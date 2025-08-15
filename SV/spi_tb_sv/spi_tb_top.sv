`timescale 1ns / 1ps

module spi_top_tb;

    // =========================================================================
    // 1. Testbench Signals & Parameters
    // =========================================================================
    // Instantiate the same parameters as the DUT
    parameter MASTER_FREQ 	= 100_000_000;
    parameter SLAVE_FREQ 	= 1_800_000;
    parameter SPI_MODE 		= 1;
    
    //parameter `SPI_TRF_BIT = 12;
	// Testbench signals
	`ifndef SPI_TRF_BIT
	`define SPI_TRF_BIT 12
	`endif

	localparam int DATA_WIDTH = `SPI_TRF_BIT;  // Use macro from Makefile
	//logic [DATA_WIDTH-1:0] test_data;
    logic clk;
    logic rst;

    logic [1:0] req;
    logic [7:0] wait_duration;
    logic [(`SPI_TRF_BIT-1):0] din_master;
    logic [(`SPI_TRF_BIT-1):0] din_slave;

    logic [(`SPI_TRF_BIT-1):0] dout_master;
    logic [(`SPI_TRF_BIT-1):0] dout_slave;
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
        clk 			= 1'b0;
        rst 			= 1'b1;
        req 			= 2'b00;
        din_master 		= '0;
        din_slave 		= '0;
        wait_duration 	= '0;
        #20;
        rst 			= 1'b0;
        $display("Initial reset complete. Starting test sequences.");
    end

    // =========================================================================
    // 3. Design Under Test (DUT) Instantiation
    // =========================================================================
    spi_top #(
        .MASTER_FREQ	(MASTER_FREQ),
        .SLAVE_FREQ		(SLAVE_FREQ),
        .SPI_MODE		(SPI_MODE),
        .SPI_TRF_BIT	(`SPI_TRF_BIT)
    ) dut (
        .clk(clk),
        .rst(rst),
        .req(req),
        .wait_duration	(wait_duration),
        .din_master		(din_master),
        .din_slave		(din_slave),
        .dout_master	(dout_master),
        .dout_slave		(dout_slave),
        .done_tx		(done_tx),
        .done_rx		(done_rx)
    ); 

    // Connecting internal signals for monitoring
    assign sclk 		= dut.sclk_generator_inst.sclk;
    assign sclk_en 		= dut.spi_master_inst.sclk_en;
    assign cs 			= dut.spi_master_inst.cs;
    assign mosi 		= dut.spi_master_inst.mosi;
    assign miso 		= dut.spi_slave_inst.miso;
    
    // =========================================================================
    // 4. Scoreboard for Data Integrity Checks
    // =========================================================================
    class spi_scoreboard;
		logic [(`SPI_TRF_BIT-1):0] tx_data_q [$];
		logic [(`SPI_TRF_BIT-1):0] rx_data_q [$];

		int total_checks;
		int pass_count;
		int fail_count;

		function new();
		    total_checks 	= 0;
		    pass_count   	= 0;
		    fail_count   	= 0;
		    cg 				= new();
		endfunction

		covergroup cg @(posedge clk);

			coverpoint req {
				bins no_operation = {2'b0};
				bins tx_only      = {2'b01};
				bins rx_only      = {2'b10};
				bins full_duplex  = {2'b11};
			}

			coverpoint wait_duration {
				bins zero   = {0};
				bins short  = {[1:5]};
				bins med    = {[6:15]};
				bins long   = {[16:255]};
			}

			// Full range of values
			coverpoint din_master {
				bins all_values[] = {[0 : (1<<`SPI_TRF_BIT)-1]};
			}

			coverpoint din_slave {
				bins all_values[] = {[0 : (1<<`SPI_TRF_BIT)-1]};
			}

			// Corner cases for din_master
			din_master_corner : coverpoint din_master {
				bins zero     = {0};
				bins all_ones = { (1<<`SPI_TRF_BIT) - 1 };
			}

			// Corner cases for din_slave
			din_slave_corner : coverpoint din_slave {
				bins zero     = {0};
				bins all_ones = { (1<<`SPI_TRF_BIT) - 1 };
			}

		endgroup



		function void push_tx_data(int req, logic [(`SPI_TRF_BIT-1):0] data);
		    tx_data_q.push_back(data);
		    $display("[%0t][SEQ][REQ=%0d] Pushed TX data 0x%h to queue.", $time, req, data);
		endfunction

		function void push_rx_data(int req, logic [(`SPI_TRF_BIT-1):0] data);
		    rx_data_q.push_back(data);
		    $display("[%0t][SEQ][REQ=%0d] Pushed RX data 0x%h to queue.", $time, req, data);
		endfunction

		task check_tx_data();
		    logic [(`SPI_TRF_BIT-1):0] expected_data, actual_data;
		    if (tx_data_q.size() > 0) begin
		        expected_data = tx_data_q.pop_front();
		        actual_data   = dout_slave;
		        total_checks++;
		        if (actual_data === expected_data) begin
		            pass_count++;
		            $display("[%0t][SCB][PASS] TX data matched! Sent: 0x%h, Received: 0x%h",
		                     $time, expected_data, actual_data);
		        end else begin
		            fail_count++;
		            $error("[%0t][SCB][FAIL] TX data mismatch! Sent: 0x%h, Received: 0x%h",
		                   $time, expected_data, actual_data);
		        end
		    end
		endtask

		task check_rx_data();
		    logic [(`SPI_TRF_BIT-1):0] expected_data, actual_data;
		    if (rx_data_q.size() > 0) begin
		        expected_data = rx_data_q.pop_front();
		        actual_data   = dout_master;
		        total_checks++;
		        if (actual_data === expected_data) begin
		            pass_count++;
		            $display("[%0t][SCB][PASS] RX data matched! Sent: 0x%h, Received: 0x%h",
		                     $time, expected_data, actual_data);
		        end else begin
		            fail_count++;
		            $error("[%0t][SCB][FAIL] RX data mismatch! Sent: 0x%h, Received: 0x%h",
		                   $time, expected_data, actual_data);
		        end
		    end
		endtask

		task summary();
		    $display("\n=================== SCOREBOARD SUMMARY ===================");
		    $display("Total Checks: %0d", total_checks);
		    $display("Pass Count  : %0d", pass_count);
		    $display("Fail Count  : %0d", fail_count);
		    $display("==========================================================\n");
		endtask
	endclass
    spi_scoreboard scoreboard_inst;
    
    class tx_rx_rand;

  		rand logic [(`SPI_TRF_BIT-1):0] din_master;
  		rand logic [(`SPI_TRF_BIT-1):0] din_slave;
		rand logic [1:0] req;
		rand logic [7:0] wait_duration;
  		constraint ran_range{
			din_master 		inside {[0:(2**`SPI_TRF_BIT)-1]};
        	din_slave 		inside {[0:(2**`SPI_TRF_BIT)-1]};
			req 			inside {[0:3]};	
			wait_duration 	inside {[0:256]};
			}

    endclass
    tx_rx_rand gen;

    // =========================================================================
    // 5. Stimulus Generator
    // =========================================================================
    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars(0, spi_top_tb);
    end
    
    initial begin
		#100ms;
		$error("TEST TIMEOUT: Simulation exceeded 1ms without finishing.");
		$finish;
    end
    
    task reset();
  		#50;
		rst = 1'b1;
		#50;
		rst = 1'b0;
    endtask

    initial begin
        bit cs_went_high 	= 0;
        clk					= 0;
        req					= 0;
        din_master			= 0;
        din_slave			= 0;
        wait_duration		= 0;
        
        scoreboard_inst 	= new();
        gen 				= new();
        
        $display("\n------------------------- FIXED SEQUENCE INPUT --------------------\n");
        $display("Initial reset complete. Starting test sequences.");
       	
       	// Test 2.2 TX Data MSB -> LSB  	
       	reset();
       	#100;
        $display("TEST: TX Data MSB -> LSB (Test ID 2.1)");
        assert (gen.randomize()) else $fatal ("Randomization failed!");
        req 			= 2'b01;
        din_master 		= gen.din_master;
        din_slave		= gen.din_slave;
        wait_duration 	= 8'd0;

        @(negedge sclk)
		for (int i = `SPI_TRF_BIT-1; i >= 0; i--) begin
			@(negedge sclk)
			assert (din_master[i] === dout_slave[0])
				else $error("Bit mismatch: Expected MSB = %b, Got = %b", din_master[i], dout_slave[0]);
		end

       	// Test 7.1 Reset on transfer
       	reset();
		#100;
        $display("TEST: Reset on transfer");        
        assert (gen.randomize()) else $fatal ("Randomization failed!");
        req 			= 2'b01;
        din_master 		= gen.din_master;
        din_slave		= gen.din_slave;
        wait_duration 	= 8'd0;
        #1000;
		@(posedge sclk);
		reset();

		// Test 6.5
		$display("\n------------------------- RANDOMIZED INPUT --------------------\n");
		repeat (10000) begin
			assert (gen.randomize()) else $fatal ("Randomization failed!");

			req				= gen.req;
			
			@(posedge clk);
			din_master 		<= gen.din_master;
			din_slave 		<= gen.din_slave;
			wait_duration 	<= gen.wait_duration;
			
			if (req == 2'b01) begin 
				@(posedge clk);
				scoreboard_inst.push_tx_data(req, din_master);	
		  		@(posedge done_tx);
		  		scoreboard_inst.check_tx_data();
			end else if (req == 2'b10) begin 
				@(posedge clk);
				scoreboard_inst.push_rx_data(req, din_slave);
				@(posedge done_rx);
				scoreboard_inst.check_rx_data();
			end else if (req == 2'b11) begin 
				@(posedge clk);
				scoreboard_inst.push_tx_data(req, din_master);
				scoreboard_inst.push_rx_data(req, din_slave);
			 	fork
					@(posedge done_tx);
					@(posedge done_rx);
				join
				scoreboard_inst.check_tx_data();
				scoreboard_inst.check_rx_data();
			end else if (req == 2'b0) begin
				#1000;
				reset();
				continue;
			end
		end
				    
	    // Finalize test and report
	    #100;
	    scoreboard_inst.summary();
	    $display("TEST: All sequences completed.");
	    $finish;
	end

    // =========================================================================
    // 6. Assertions for Specific Checks
    // =========================================================================

    done_rx_check: assert property (@(posedge clk)
	disable iff (rst || ($past(req) == 2'b01 || $past(req) == 2'b00))
		($rose (dut.spi_master_inst.sclk_negedge) && (din_slave === dout_master)) |=> done_rx
	) else $error("%t [FAIL][Done RX] RX did not aserrt when din_slave=%h dout_master=%h",
	          $time, din_slave, dout_master);
    
    rst_check: assert property (@(posedge clk) 
		(rst) |->
    	(dout_master == '0) && (dout_slave == '0) && (done_tx == 1'b0) && (done_rx == 1'b0)
    ) else $error("%t [FAIL][rst_check] rst=%b", $time, rst);
    
    no_operation_check: assert property (@(posedge clk) 
    disable iff (rst)
    	(req == 2'b00) |-> ##2 ($stable(dout_master)) && ($stable(dout_slave)) && (done_tx == 1'b0) && (done_rx == 1'b0)
    ) else $error("%t [FAIL][no_operation_check] dout_master=0x%h, dout_slave=0x%h, done_tx=%b, done_rx=%b", $time, dout_master, dout_slave, done_tx, done_rx);
    
	dout_miso_check: assert property (@(negedge sclk)
	disable iff (rst || (din_slave == dout_master))
		(req == 2'b10 || req == 2'b11) |=> ($past(miso) == dout_master[0])
	) else $error("%t [FAIL][dout_miso_check] dout_master LSB != miso in RX/Full-Duplex mode", $time);

	dout_mosi_check: assert property (@(negedge sclk)
	disable iff (rst || (din_master == dout_slave))
		(req == 2'b01 || req == 2'b11) |=> ($past(mosi) == dout_slave[0])
	) else $error("%t [FAIL][dout_mosi_check] dout_slave LSB != mosi in TX/Full-Duplex mode", $time);
	
	dout_master_sampled_n: assert property (@(negedge dut.spi_master_inst.sclk_negedge)
	disable iff (rst || (din_slave == dout_master))
  		((req == 2 || req ==3 ) && !cs && dout_master !== 0) |=> (dout_master !== $past(dout_master))
	) else $error("dout_master did not change at negedge sclk: Previous = %b, Current = %b", $past(dout_master), dout_master); 

	dout_slave_sampled_n: assert property (@(negedge dut.spi_master_inst.sclk_negedge)
	disable iff (rst || (din_master == dout_slave))
		((req == 1 || req == 3) && !cs && dout_slave !== 0) |=> (dout_slave !== $past(dout_slave))
	) else $error("dout_slave did not change at negedge sclk: Previous = %b, Current = %b", $past(dout_slave), dout_slave);

	// SCLK enable check on posedge main clock
	sclk_en_assert_sclk: assert property (@(posedge clk)
	disable iff (rst)
		!sclk_en |-> ##2 $stable(sclk)
	) else $error("sclk does not toggle when not en");
	
	// Test 7.2 CS Assert after TX/RX transfer	
	cs_rise_check: assert property (@(posedge clk)
    disable iff (rst || req == 2'b11)
    	(done_tx || done_rx) |-> cs
	) else $error("%t [FAIL][CS Timing] CS did not rise with done_tx(%b) or done_rx(%b)", $time, done_tx, done_rx);

endmodule

/* TO BE FIXED

duplex_cs_rise_check: assert property (@(posedge clk)
	disable iff (rst || (req == 2'b01 || req == 2'b10))
	tx_rx_done |-> cs
) else $error("%t [FAIL][CS Timing] CS did not rise after both done_tx(%b) and done_rx(%b)",
		          $time, done_tx, done_rx);

int counter;
initial begin
    counter = 0;
    forever begin
        @(negedge sclk)
        $display("At negedge sclk: counter=%0d", counter);
		if (counter >= 10) begin
			counter = 0;
        end else if (din_master === dout_slave) begin
            for (counter = 1; counter <= wait_duration; counter++) begin
                @(posedge clk);
                $display("counter=%0d", counter);
            end
        end 
    end
end

	done_tx_check: assert property (@(posedge clk)
		disable iff (rst || ($past(req) == 2'b10 || $past(req) == 2'b00))
		($rose(dut.spi_master_inst.sclk_negedge) && (counter == wait_duration)) |=> done_rx
	) else $error("%t [FAIL][Done TX] TX did not assert when din_slave=%h dout_master=%h",
		          $time, din_slave, dout_master);
*/
