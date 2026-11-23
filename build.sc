import mill._
import scalalib._
import scalafmt._
import $packages._
import $file.`rocket-chip`.common
import $file.`rocket-chip`.cde.common
import $file.`rocket-chip`.hardfloat.common

val pwd = os.Path(sys.env("MILL_WORKSPACE_ROOT"))

object v {
  val scala = "2.13.18"
  val chiselCrossVersions = Map(
    "xiangshan" -> (
      mvn"cc.xiangshan::chisel:7.16.0-xiangshan-2",
      mvn"cc.xiangshan:::chisel-plugin:7.16.0-xiangshan-2"
    ),
    "upstream" -> (
      mvn"org.chipsalliance::chisel:7.16.0",
      mvn"org.chipsalliance:::chisel-plugin:7.16.0"
    )
  )
  def chiselKeys = chiselCrossVersions.keys.toSeq
}
/* resolve firtool dependency */
import $ivy.`org.chipsalliance::chisel:7.16.0`
import $ivy.`org.chipsalliance::firtool-resolver:2.1.1`

trait HasChisel extends SbtModule with Cross.Module[String] {
  def chiselModule: Option[ScalaModule] = None

  def chiselPluginJar: T[Option[PathRef]] = None

  def chiselIvy: Option[Dep] = Some(v.chiselCrossVersions(crossValue)._1)

  def chiselPluginIvy: Option[Dep] = Some(v.chiselCrossVersions(crossValue)._2)

  override def scalaVersion = v.scala

  override def scalacOptions = super.scalacOptions() ++
    Agg("-language:reflectiveCalls", "-Ymacro-annotations", "-Ytasty-reader")

  override def ivyDeps = super.ivyDeps() ++ Agg(chiselIvy.get)

  override def scalacPluginIvyDeps = super.scalacPluginIvyDeps() ++ Agg(chiselPluginIvy.get)

  def resolveFirtoolDeps = T {
    firtoolresolver.Resolve(chisel3.BuildInfo.firtoolVersion.get, true) match {
      case Right(bin) => bin.path.getAbsolutePath
      case Left(err) => err
    }
  }
}

trait RocketChip extends $file.`rocket-chip`.common.RocketChipModule with HasChisel {
  def scalaVersion: T[String] = T(v.scala)

  override def millSourcePath = pwd / "rocket-chip"

  def macrosModule = macros(crossValue)

  def hardfloatModule = hardfloat(crossValue)

  def cdeModule = cde(crossValue)

  def mainargsIvy = mvn"com.lihaoyi::mainargs:0.7.0"

  def json4sJacksonIvy = mvn"org.json4s::json4s-jackson:4.0.7"

  trait Macros
    extends $file.`rocket-chip`.common.MacrosModule
      with HasChisel {

    def scalaVersion: T[String] = T(v.scala)

    def scalaReflectIvy = mvn"org.scala-lang:scala-reflect:${v.scala}"
  }

  object macros extends Cross[Macros](v.chiselKeys)

  trait HardFloat
    extends $file.`rocket-chip`.hardfloat.common.HardfloatModule with HasChisel {

    def scalaVersion: T[String] = T(v.scala)

    override def millSourcePath = pwd / "rocket-chip" / "hardfloat" / "hardfloat"

  }

  object hardfloat extends Cross[HardFloat](v.chiselKeys)

  trait CDE
    extends $file.`rocket-chip`.cde.common.CDEModule with Cross.Module[String] {

    def scalaVersion: T[String] = T(v.scala)

    override def millSourcePath = pwd / "rocket-chip" / "cde" / "cde"
  }

  object cde extends Cross[CDE](v.chiselKeys)
}

object rocketchip extends Cross[RocketChip](v.chiselKeys)

trait Utility extends HasChisel {

  override def millSourcePath = pwd / "utility"

  override def moduleDeps = super.moduleDeps ++ Seq(
    rocketchip(crossValue)
  )

  override def ivyDeps = super.ivyDeps() ++ Agg(
    mvn"com.lihaoyi::sourcecode:0.4.2",
  )

  object test extends SbtTests with TestModule.ScalaTest {
    override def ivyDeps = Agg(mvn"org.scalatest::scalatest:3.2.20")
  }
}

object utility extends Cross[Utility](v.chiselKeys)

trait ChiselIOPMPModule extends ScalaModule with Cross.Module[String] {

  def rocketModule: ScalaModule

  def utilityModule: ScalaModule

  override def moduleDeps = super.moduleDeps ++ Seq(rocketModule, utilityModule)

  val resourcesPATH = pwd.toString() + "/src/main/resources"
  val envPATH = sys.env("PATH") + ":" + resourcesPATH

  override def forkEnv = Map("PATH" -> envPATH)
}

trait ChiselIOPMP extends ChiselIOPMPModule with HasChisel with ScalafmtModule {

  override def millSourcePath = pwd

  def rocketModule: ScalaModule = rocketchip(crossValue)

  def utilityModule: ScalaModule = utility(crossValue)

  override def ivyDeps = super.ivyDeps() ++ Agg(
    mvn"io.circe::circe-yaml:1.15.0",
    mvn"io.circe::circe-generic-extras:0.14.4"
  )

  override def scalacOptions = super.scalacOptions() ++ Agg("-deprecation", "-feature")
}

object ChiselIOPMP extends Cross[ChiselIOPMP](v.chiselKeys)
