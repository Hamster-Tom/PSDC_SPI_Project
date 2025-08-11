// File: spi_tb.sv
// Description: The top-level testbench module. It instantiates the DUT,
// the interface, and the testbench environment, and controls the simulation flow.

// Include all necessary files.
`include "spi_if.sv"
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
`include "spi.sv"

module spi_tb;
  
  parameter CLK_DIV = 4;
  
  logic clk = 0;
  logic rst_n = 0;

  // Instantiate the virtual interface.
  spi_if spi_if0 (.*);

  // Instantiate the Design Under Test (DUT).
  spi #(.CLK_DIV(CLK_DIV)) dut (
    .clk(spi_if0.clk),
    .rst_n(spi_if0.rst_n),
    .start(spi_if0.start),
    .tx_data(spi_if0.tx_data),
    .rx_data(spi_if0.rx_data),
    .busy(spi_if0.busy),
    .done(spi_if0.done),
    .sclk(spi_if0.sclk),
    .mosi(spi_if0.mosi),
    .miso(spi_if0.miso),
    .cs_n(spi_if0.cs_n)
  );

  // Test class handle.
  spi_test test_comp;

  // Clock generation.
  initial begin
    forever #5 clk = ~clk;
  end

  // Reset generation.
  initial begin
    spi_if0.clk = clk;
    spi_if0.rst_n = rst_n;
    #10 rst_n = 1;
    spi_if0.rst_n = rst_n;
  end

  // Main test flow.
  initial begin
    // Instantiate the environment.
    spi_env env = new(spi_if0);
    // Instantiate the test component.
    test_comp = new(env);
    // Run the test.
    test_comp.run();
    
    #100 $finish;
  end
endmodule

