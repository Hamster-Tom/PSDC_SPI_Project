`include "spi.sv"
`include "spi_if.sv"

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
  `include "spi_scb.sv"
  `include "spi_cov.sv"
  `include "spi_agt.sv" 
  `include "spi_env.sv"
  `include "spi_test.sv"

  	spi_if spi_if();
  
  	parameter CLK_DIV = 4;
    // Constants
    bit [7:0] SLAVE_RESET_RESPONSE = 8'hB9;
    int slave_reset_response = SLAVE_RESET_RESPONSE;

    // Simple SPI slave model for testing
    logic [7:0] slave_rx_data;
    logic [7:0] slave_tx_data = SLAVE_RESET_RESPONSE;

  spi #(.CLK_DIV(CLK_DIV)) dut (
      .clk     (spi_if.clk),
      .rst_n   (spi_if.rst_n),
      .start   (spi_if.start),
      .tx_data (spi_if.tx_data),
      .rx_data (spi_if.rx_data),
      .busy    (spi_if.busy),
      .done    (spi_if.done),
      .sclk    (spi_if.sclk),
      .mosi    (spi_if.mosi),
      .miso    (spi_if.miso),
      .cs_n    (spi_if.cs_n)
  );

  initial begin
    spi_if.clk = 0;
    forever #5 spi_if.clk = ~spi_if.clk;
  end
  
  initial begin
    spi_if.rst_n 	= 0;
    spi_if.start 	= 0;
    spi_if.tx_data 	= 0;
    spi_if.miso 	= 0;
    #20 spi_if.rst_n = 1;
  end

  initial begin
    uvm_config_db#(virtual spi_if)::set(null, "*", "vif", spi_if);
    uvm_config_db#(int)::set(null, "*", "slave_rx_data", slave_rx_data);
    run_test("spi_test");
  end

  initial begin
    $fsdbDumpfile("spi_sim.fsdb");
    $fsdbDumpSVA(0, spi_tb);
    $fsdbDumpvars(0, spi_tb);
  end

    always @(posedge spi_if.sclk or negedge spi_if.rst_n or posedge spi_if.cs_n) begin
        if (!spi_if.rst_n) begin
            slave_rx_data <= 8'h11;
            spi_if.miso <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
        else if (spi_if.cs_n) begin
            spi_if.miso <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;

            `uvm_info("SLV-RLD", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                               slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
        else begin
                // Shift in MOSI on rising edge
                slave_rx_data <= {slave_rx_data[6:0], spi_if.mosi};

                // Update MISO immediately for next bit
                spi_if.miso <= slave_tx_data[7];
                slave_tx_data <= {slave_tx_data[6:0], 1'b0};

                `uvm_info("SLV", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                           slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
    end
endmodule
