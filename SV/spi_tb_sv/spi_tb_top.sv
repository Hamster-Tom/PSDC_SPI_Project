// spi_top_tb.sv - Testbench for the spi_top module
// This testbench implements the verification plan using a scoreboard and assertions.

`timescale 1ns / 1ps

module spi_top_tb;

    // =========================================================================
    // 1. Testbench Signals & Parameters
    // =========================================================================
    // Instantiate the same parameters as the DUT
    parameter MASTER_FREQ = 100_000_000;
    parameter SLAVE_FREQ 	= 1_800_000;
    parameter SPI_MODE 		= 1;
    parameter SPI_TRF_BIT = 12; // Adjusted to match test plan

    // Testbench signals
    logic clk;
    logic rst;

    logic [1:0] req;
    logic [7:0] wait_duration;
    logic [(SPI_TRF_BIT-1):0] din_master;
    logic [(SPI_TRF_BIT-1):0] din_slave;

    logic [(SPI_TRF_BIT-1):0] dout_master;
    logic [(SPI_TRF_BIT-1):0] dout_slave;
    logic done_tx;
    logic done_rx;

    // Internal signals for monitoring and assertions
    logic sclk;
    logic sclk_en;
    logic cs;
    logic mosi;
    logic miso;

    // =========================================================================
    // 2. Clock & Reset Generator
    // =========================================================================
    // Clock generation
    always #5 clk = ~clk; // Generates a 100 MHz clock (10 ns period)

    // Reset generation
    initial begin
        clk 					= 1'b0;
        rst 					= 1'b1;
        req 					= 2'b00;
        din_master 		= '0;
        din_slave 		= '0;
        wait_duration = '0;
        #20;
        rst 					= 1'b0;
        $display("Initial reset complete. Starting test sequences.");
    end

    // =========================================================================
    // 3. Design Under Test (DUT) Instantiation
    // =========================================================================
    spi_top #(
        .MASTER_FREQ	(MASTER_FREQ),
        .SLAVE_FREQ		(SLAVE_FREQ),
        .SPI_MODE			(SPI_MODE),
        .SPI_TRF_BIT	(SPI_TRF_BIT)
    ) dut (
        .clk(clk),
        .rst(rst),
        .req(req),
        .wait_duration	(wait_duration),
        .din_master			(din_master),
        .din_slave			(din_slave),
        .dout_master		(dout_master),
        .dout_slave			(dout_slave),
        .done_tx				(done_tx),
        .done_rx				(done_rx)
    );

    // Connecting internal signals for monitoring
    assign sclk 		= dut.sclk_generator_inst.sclk;
    assign sclk_en 	= dut.spi_master_inst.sclk_en;
    assign cs 			= dut.spi_master_inst.cs;
    assign mosi 		= dut.spi_master_inst.mosi;
    assign miso 		= dut.spi_slave_inst.miso;
    
    // =========================================================================
    // 4. Scoreboard for Data Integrity Checks (Technique 3.1, 4.1, 5.1, 8.1)
    // =========================================================================
    // The scoreboard will check the received data against the sent data.
    class spi_scoreboard;
        logic [(SPI_TRF_BIT-1):0] tx_data_q [$];
        logic [(SPI_TRF_BIT-1):0] rx_data_q [$];

        function void push_tx_data(logic [(SPI_TRF_BIT-1):0] data);
            tx_data_q.push_back(data);
            $display("SCOREBOARD: Pushed TX data 0x%h to queue.", data);
        endfunction

        function void push_rx_data(logic [(SPI_TRF_BIT-1):0] data);
            rx_data_q.push_back(data);
            $display("SCOREBOARD: Pushed RX data 0x%h to queue.", data);
        endfunction

        task check_tx_data();
            logic [(SPI_TRF_BIT-1):0] expected_data, actual_data;
            if (tx_data_q.size() > 0) begin
                expected_data = tx_data_q.pop_front();
                actual_data = dout_slave;

                if (actual_data === expected_data) begin
                    $display("SCOREBOARD PASSED: TX data matched! Sent: 0x%h, Received: 0x%h", expected_data, actual_data);
                end else begin
                    $error("SCOREBOARD FAILED: TX data mismatch! Sent: 0x%h, Received: 0x%h", expected_data, actual_data);
                end
            end
        endtask

        task check_rx_data();
            logic [(SPI_TRF_BIT-1):0] expected_data, actual_data;
            if (rx_data_q.size() > 0) begin
                expected_data = rx_data_q.pop_front();
                actual_data = dout_master;

                if (actual_data === expected_data) begin
                    $display("SCOREBOARD PASSED: RX data matched! Sent: 0x%h, Received: 0x%h", expected_data, actual_data);
                end else begin
                    $error("SCOREBOARD FAILED: RX data mismatch! Sent: 0x%h, Received: 0x%h", expected_data, actual_data);
                end
            end
        endtask
    endclass

    // Instantiate the scoreboard
    spi_scoreboard scoreboard_inst;

    // =========================================================================
    // 5. Stimulus Generator
    // =========================================================================
    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars(0, spi_top_tb);
    end
    
    task reset();
		      rst = 1'b1;
		      #50;
		      rst = 1'b0;
    endtask
    
    initial begin
        scoreboard_inst = new();

        // Test 3.1
        #100;
        $display("TEST: Master TX to Slave (Test ID 3.1)");
        req 					= 2'b01;
        din_master 		= 12'hABC;
        wait_duration = 8'd0;
        scoreboard_inst.push_tx_data(12'hABC);
        
        @(posedge done_tx); // Wait for the transfer to complete
        scoreboard_inst.check_tx_data();
        
        // Test 4.1
        $display("TEST: Master RX from Slave (Test ID 4.1)");
        req 					= 2'b10;
        din_slave 		= 12'h123;
        wait_duration = 8'd0;
        scoreboard_inst.push_rx_data(12'h123);
        
        @(posedge done_rx);
        scoreboard_inst.check_rx_data();

        // Test 5.1
        $display("TEST: Full Duplex Transfer (Test ID 5.1)");
        req 				= 2'b11;
        din_master 	= 12'hA5A;
        din_slave 	= 12'h5A5;
        wait_duration = 8'd0;
        scoreboard_inst.push_tx_data(12'hA5A);
        scoreboard_inst.push_rx_data(12'h5A5);
        
        @(posedge done_tx);
        scoreboard_inst.check_tx_data();
        @(posedge done_rx);
        scoreboard_inst.check_rx_data();
        
        // Test 2.4
        $display("TEST: No Operation Check (Test ID 7.1)");
        #100;
        req = 2'b00;
        reset();
	
        // Test 6.1
        $display("TEST: Wait Duration Check (Test ID 6.1)");
        req 						= 2'b01;
        din_master 			= 12'h456;
        wait_duration 	= 8'd15; // 10 clock cycles wait
        
        @(posedge done_tx);
        scoreboard_inst.check_tx_data();

        // Finalize test and report
        #100;
        $display("TEST: All sequences completed.");
        $finish;
    end
    
    // =========================================================================
    // 6. Assertions for Specific Checks
    // =========================================================================
    
    rst_check: assert property (@(posedge clk) (rst) |->
        (dout_master == '0) && (dout_slave == '0) && (done_tx == 1'b0) && (done_rx == 1'b0)
    ) else $error("%t [rst = 1] rst=%b", $time, rst);
    
    // Assertion to check that outputs are stable and at their inactive values when req = 2'b00
    no_operation_check: assert property (@(posedge clk) disable iff (rst)
        (req == 2'b00) |->
            ($stable(dout_master)) && ($stable(dout_slave)) && (done_tx == 1'b0) && (done_rx == 1'b0)
    ) else $error("%t [req = 00] dout_master=0x%h, dout_slave=0x%h, done_tx=%b, done_rx=%b", $time, dout_master, dout_slave, done_tx, done_rx);
    
endmodule
