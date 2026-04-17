package iopmp

import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config.Parameters
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.amba.axi4._
import freechips.rocketchip.util._
import _root_.circt.stage.ChiselStage
import device._

class AXIMemory
(
  address: Seq[AddressSet]
)(implicit p: Parameters)
  extends AXI4SlaveModule(address, executable = false, beatBytes = 8)

class Demo(implicit p: Parameters) extends LazyModule {

  val masterNode = AXI4MasterNode(Seq(AXI4MasterPortParameters(
    Seq(AXI4MasterParameters(
      name = "iopmp-bridge",
      id   = IdRange(0, 14)
    ))
  )))

  val dmac = LazyModule(new AXI4DMAC(Seq(AddressSet(0x40003000L, 0xfff))))
  val iopmp = LazyModule(new IopmpLazy(1))
  val memory = LazyModule(new AXIMemory(Seq(AddressSet(0x80000000L, 0x7fffffffL)))) // fake memory, no cache

  dmac.node := masterNode
  iopmp.slaveNodes(0) := dmac.masterNode
  memory.node := iopmp.masterNodes(0)

  val io_slv = InModuleBody {
    masterNode.makeIOs()
  }

  lazy val module = new Imp
  class Imp extends LazyModuleImp(this) {

    iopmp.module.apb_s.paddr    := 0.U
    iopmp.module.apb_s.psel     := 0.U
    iopmp.module.apb_s.penable  := 0.U
    iopmp.module.apb_s.pwrite   := 0.U
    iopmp.module.apb_s.pwdata   := 0.U

  }
}
