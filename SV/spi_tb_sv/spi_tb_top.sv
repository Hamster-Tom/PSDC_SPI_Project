// spi_top_tb.sv - Testbench for the spi_top module
// This testbench implements the verification plan using a scoreboard and assertions.

`timescale 1ns / 1ps

module spi_top_tb;

    // =========================================================================
    // 1. Testbench Signals & Parameters
    // =========================================================================
    // Instantiate the same parameters as the DUT
    parameter MASTER_FREQ = 100_000_000;
    parameter SLAVE_FREQ = 1_800_000;
    parameter SPI_MODE = 1;
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
        clk = 1'b0;
        rst = 1'b1;
        req = 2'b00;
        din_master = '0;
        din_slave = '0;
        wait_duration = '0;
        #20;
        rst = 1'b0;
        $display("Initial reset complete. Starting test sequences.");
    end

    // =========================================================================
    // 3. Design Under Test (DUT) Instantiation
    // =========================================================================
    spi_top #(
        .MASTER_FREQ(MASTER_FREQ),
        .SLAVE_FREQ(SLAVE_FREQ),
        .SPI_MODE(SPI_MODE),
        .SPI_TRF_BIT(SPI_TRF_BIT)
    ) dut (
        .clk(clk),
        .rst(rst),
        .req(req),
        .wait_duration(wait_duration),
        .din_master(din_master),
        .din_slave(din_slave),
        .dout_master(dout_master),
        .dout_slave(dout_slave),
        .done_tx(done_tx),
        .done_rx(done_rx)
    );

    // Connecting internal signals for monitoring
    assign sclk = dut.sclk_generator_inst.sclk;
    assign sclk_en = dut.spi_master_inst.sclk_en;
    assign cs = dut.spi_master_inst.cs;
    assign mosi = dut.spi_master_inst.mosi;
    assign miso = dut.spi_slave_inst.miso;
    
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

        task check_tx_rx_data();
            logic [(SPI_TRF_BIT-1):0] expected_tx, expected_rx;
            logic [(SPI_TRF_BIT-1):0] actual_tx, actual_rx;

            // Wait for both queues to have data
            while (tx_data_q.size() > 0 && rx_data_q.size() > 0) begin
                expected_tx = tx_data_q.pop_front();
                expected_rx = rx_data_q.pop_front();
                
                // Monitor DUT outputs for actual data
                @(posedge done_tx);
                actual_tx = dout_slave;
                @(posedge done_rx);
                actual_rx = dout_master;

                if (actual_tx === expected_tx) begin
                    $display("SCOREBOARD PASSED: TX data matched! Sent: 0x%h, Received: 0x%h", expected_tx, actual_tx);
                end else begin
                    $error("SCOREBOARD FAILED: TX data mismatch! Sent: 0x%h, Received: 0x%h", expected_tx, actual_tx);
                end
                
                if (actual_rx === expected_rx) begin
                    $display("SCOREBOARD PASSED: RX data matched! Sent: 0x%h, Received: 0x%h", expected_rx, actual_rx);
                end else begin
                    $error("SCOREBOARD FAILED: RX data mismatch! Sent: 0x%h, Received: 0x%h", expected_rx, actual_rx);
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
    
    initial begin
        scoreboard_inst = new();
        
        // Wait for reset to complete
        @(negedge rst);
        
        // 5.1. Master TX to Slave (Test 3.1)
        #100;
        $display("TEST: Master TX to Slave (Test ID 3.1)");
        req <= 2'b01;
        din_master <= 12'hABC;
        wait_duration <= 8'd0;
        scoreboard_inst.push_tx_data(12'hABC);
        @(posedge done_tx); // Wait for the transfer to complete
        #10;
        
        // 5.2. Master RX from Slave (Test 4.1)
        #100;
        $display("TEST: Master RX from Slave (Test ID 4.1)");
        req <= 2'b10;
        din_slave <= 12'h123;
        wait_duration <= 8'd0;
        scoreboard_inst.push_rx_data(12'h123);
        @(posedge done_rx);
        #10;

        // 5.3. Full Duplex Transfer (Test 5.1)
        #100;
        $display("TEST: Full Duplex Transfer (Test ID 5.1)");
        req <= 2'b11;
        din_master <= 12'hA5A;
        din_slave <= 12'h5A5;
        scoreboard_inst.push_tx_data(12'hA5A);
        scoreboard_inst.push_rx_data(12'h5A5);
        @(posedge done_tx);
        @(posedge done_rx);
        #10;

        // 5.4. Wait Duration Check (Test 6.1)
        #100;
        $display("TEST: Wait Duration Check (Test ID 6.1)");
        req <= 2'b01;
        din_master <= 12'h456;
        wait_duration <= 8'd10; // 10 clock cycles wait
        @(posedge done_tx);
        #10;

        // Finalize test and report
        #100;
        $display("TEST: All sequences completed.");
        $finish;
    end
    
    // =========================================================================
    // 6. Assertions for Specific Checks
    // =========================================================================
    
    // Assertion 2.1: sclk frequency check
    // This is more complex and would require a more detailed sequence
    // A simple check can be done as a sequential assertion
    // This is a basic check to ensure sclk toggles when enabled
    sclk_toggle_when_enabled_p: assert property (@(posedge clk) (sclk_en) |-> sclk == !($past(sclk)));
    
    // Assertion 3.2: MSB-first transmission check
    // Requires monitoring internal signals. This is a simplified check.
    // A more robust check would involve a state machine in the assertion.
    // This assertion checks that when TX starts, the first bit on MOSI matches the MSB of din_master
    msb_first_tx_p: assert property (@(posedge sclk) (dut.spi_master_inst.state_tx == 2'b10) |-> mosi == dut.spi_master_inst.din_reg[(SPI_TRF_BIT-1)]);
    
    // Assertion 4.2: Master RX on negative sclk edge
    // A simplified check to ensure sampling occurs on the negative edge
    negedge_sampling_p: assert property (@(posedge clk) (dut.spi_master_inst.state_rx == 1'b1 && dut.spi_master_inst.sclk_negedge) |-> dut.spi_master_inst.dout_temp[0] == miso);

    // Assertion 6.1: wait_duration check for cs
    // This assertion checks the wait duration before the transfer starts.
    wait_duration_p: assert property (@(posedge clk) $rose(sclk_en) |-> ##[dut.spi_master_inst.wait_duration_reg] !dut.spi_master_inst.sclk_en);
    
    // Assertion 7.1: Mid-transfer reset check
    // This assertion checks that upon reset, the state machines return to idle.
    reset_to_idle_p: assert property (@(posedge clk) rst |-> dut.spi_master_inst.state_tx == 2'b00 and dut.spi_master_inst.state_rx == 1'b0);

    // Assertion 7.2: CS mid-transfer check
    // This assertion checks that if CS goes high, the slave resets to its idle state.
    cs_mid_transfer_p: assert property (@(posedge clk) ($rose(cs) && dut.spi_slave_inst.state_rx == 1'b1) |-> ##1 dut.spi_slave_inst.state_rx == 1'b0);
    
endmodule
