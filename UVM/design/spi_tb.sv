module spi_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // $time is a built-in system function
  initial $display(">>>>>>>> SIM TIME START: %0t", $time);
  final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

  // Include all required files
  `include "spi_tran.sv"
  `include "spi_seq.sv"
  `include "spi_sqr.sv"
  `include "spi_drv.sv"
  `include "spi_mon.sv"
  `include "spi_agt.sv" 
  `include "spi_scb.sv"
  `include "spi_cov.sv"
  `include "spi_env.sv"
  `include "spi_test.sv"

  initial begin
    run_test("spi_test");
  end

  initial begin
    $fsdbDumpfile("spi_sim.fsdb");
    $fsdbDumpvars(0, spi_tb);
  end
endmodule
