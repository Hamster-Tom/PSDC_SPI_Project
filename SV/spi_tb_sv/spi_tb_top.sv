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
	function new();
	    cg = new();
	endfunction;
	 
	covergroup cg @(posedge clk);

  	 coverpoint req {
    	 bins tx_only = {2'b01};
    	 bins rx_only = {2'b10};
   	 bins full_duplex = {2'b11};
  	 }

	coverpoint wait_duration {
    	bins zero = {0};
    	bins short = {[1:5]};
    	bins med = {[6:15]};
    	bins long = {[16:255]};
  	}

	coverpoint din_master {
	bins all_values ={[0:SPI_TRF_BIT-1]};
	}

	coverpoint din_slave{
	bins all_values ={[0:SPI_TRF_BIT-1]};
	}
	din_master_corner : coverpoint din_master {
    	bins zero     = {12'h000};
    	bins all_ones = {12'hFFF};
    	bins mid      = {12'h800};
    	bins pattern1 = {12'hAAA}; // alternating 101010101010
    	bins pattern2 = {12'h555}; // alternating 010101010101
  	}

	din_slave_corner : coverpoint din_slave {
    	bins zero     = {12'h000};
    	bins all_ones = {12'hFFF};
    	bins mid      = {12'h800};
    	bins pattern1 = {12'hAAA};
    	bins pattern2 = {12'h555};
  	}
	endgroup

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
    class tx_rx_rand;

  		rand logic [(SPI_TRF_BIT-1):0] din_master;
  		rand logic [(SPI_TRF_BIT-1):0] din_slave;
		rand logic [1:0] req;
  		constraint ran_range{
			din_master inside {[0:(2**SPI_TRF_BIT)-1]};
        		din_slave inside {[0:(2**SPI_TRF_BIT)-1]};
			req inside {[0:3]};	}

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
    		#1ms;
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
        bit cs_went_high = 0;
        scoreboard_inst = new();
        gen 						= new();
        
       	// 2.1. TX Data MSB -> LSB
				#100;
        $display("TEST: TX Data MSB -> LSB (Test ID 2.1)");
        req 					= 2'b01;
        din_master 		= 12'hABC;
        wait_duration = 8'd0;
	for (int i = SPI_TRF_BIT-1; i >= 0; i--) begin
	@(posedge sclk)
	assert (din_slave[i] === dout_master[i])
	  else $error("Bit mismatch: Expected MSB = %b, Got = %b", dout_slave[i], din_master[i]);
  	end
        // Reset after test 3.1
        reset();

       	// 2.2. CS Assert after done transfer
				#100;
        $display("TEST: CS Assert after done transfer (Test ID 2.2)");
        req 					= 2'b01;
        din_master 		= 12'hABC;
        wait_duration = 8'd10;
	@(posedge clk);

  	// Wait for transaction to complete
  	wait (done_tx);
  	$display("Transaction done. Waiting for CS to go high...");
  	// Wait for CS to rise or timeout
	repeat (wait_duration) begin
  	  @(posedge clk);
  	    if (cs) begin
    	     cs_went_high = 1;
    	     break;
  	    end else cs_went_high=0;
	end
  	assert (cs_went_high)
    	$display("PASS: CS went high before %0d cycles", wait_duration);
  	else
    	$error("FAIL: CS did not rise within wait_duration (%0d cycles)", wait_duration);
        // Reset after test 3.1
        reset();

       	// 3.3. Reset on transfer
				#100;
        $display("TEST: Reset on transfer");
        req 					= 2'b01;
        din_master 		= 12'hABC;
        wait_duration = 8'd00;
	@(posedge sclk);
	reset();
        
	assert (dout_master ==0 && dout_slave ==0 && done_tx ==0 && done_rx ==0)   	
	$display("PASS: All output is 0 during reset");
	else $error("dout_master is not 0 on rst");
        
        // Reset after test 3.1
        reset();

        // Test 3.1
        #100;
        $display("TEST: Master TX to Slave (Test ID 3.1)");
        req 					= 2'b01;
        din_master 		= 12'hABC;
        din_slave 		= 12'h000;
        wait_duration = 8'd0;
        scoreboard_inst.push_tx_data(12'hABC);
        
        @(posedge done_tx); // Wait for the transfer to complete
        scoreboard_inst.check_tx_data();
        
        // Test 4.1
        $display("TEST: Master RX from Slave (Test ID 4.1)");
        req 					= 2'b10;
        din_master 		= 12'h000;
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
        wait_duration = 8'd10;
        scoreboard_inst.push_tx_data(12'hA5A);
        scoreboard_inst.push_rx_data(12'h5A5);
        
        fork
        	@(posedge done_tx);
        	@(posedge done_rx);
        join
        
        scoreboard_inst.check_tx_data();
        scoreboard_inst.check_rx_data();
        
        // Test 2.4
        $display("TEST: No Operation Check (Test ID 7.1)");
        req = 2'b00;
        #10000;
        reset();
	
        // Test 6.1
        $display("TEST: Wait Duration Check (Test ID 6.1)");
        req 						= 2'b01;
        din_master 			= 12'h456;
        din_slave 			= 12'h000;
        wait_duration 	= 8'd10; // 10 clock cycles wait
        
        @(posedge done_tx);
        scoreboard_inst.check_tx_data();

		$display("\n------------------------- RANDOMIZATION INPUT --------------------\n");
		repeat (10) begin
			assert (gen.randomize()) else $fatal ("Randomization failed!");

			din_master 	= gen.din_master;
			din_slave 	= gen.din_slave;
			req					= 	gen.req;
			
			// Push expected data into scoreboard
		  		scoreboard_inst.push_tx_data(din_master);
		  		scoreboard_inst.push_rx_data(din_slave);
			
			if (req == 2'b01) begin 	
		      		@(posedge done_tx);
		      		scoreboard_inst.check_tx_data();
			end else if (req == 2'b10) begin 
				@(posedge done_rx);
				scoreboard_inst.check_rx_data();
			end else if (req == 2'b11) begin 
			 	fork
					@(posedge done_tx);
					@(posedge done_rx);
				join
				scoreboard_inst.check_tx_data();
		          		scoreboard_inst.check_rx_data();
			end else if (req == 2'b00) begin
				#1000;
				continue;
			end
		end
        
        // Finalize test and report
        #100;
        $display("TEST: All sequences completed.");
        $finish;
    end
    
    // =========================================================================
    // 6. Assertions for Specific Checks
    // =========================================================================
    
    rst_check: assert property (@(posedge clk) 
    		(rst) |->
        (dout_master == '0) && (dout_slave == '0) && (done_tx == 1'b0) && (done_rx == 1'b0)
    ) else $error("%t [rst = 1] rst=%b", $time, rst);
    
    // Assertion to check that outputs are stable and at their inactive values when req = 2'b00
    no_operation_check: assert property (@(posedge clk) disable iff (rst)
        (req == 2'b00) |=>
        ($stable(dout_master)) && ($stable(dout_slave)) && (done_tx == 1'b0) && (done_rx == 1'b0)
    ) else $error("%t [req = 00] dout_master=0x%h, dout_slave=0x%h, done_tx=%b, done_rx=%b", $time, dout_master, dout_slave, done_tx, done_rx);
    
		dout_miso_check: assert property (@(negedge sclk)
				disable iff (rst || (din_slave == dout_master))
				(req == 2'b10 || req == 2'b11) |=> ($past(miso) == dout_master[0])
		) else $error("%t [FAIL][dout_miso_check] dout_master LSB != miso in RX/Full-Duplex mode", $time);

		dout_mosi_check: assert property (@(negedge sclk)
				disable iff (rst || (din_master == dout_slave))
				(req == 2'b01 || req == 2'b11) |=> ($past(mosi) == dout_slave[0])
		) else $error("%t [FAIL][dout_mosi_check] dout_slave LSB != mosi in TX/Full-Duplex mode", $time);
		
	property dout_master_sampled_n;
	  @(negedge sclk)
	  disable iff (rst)
	  (req == 2 | req ==3 && !cs && dout_master !== 0) |-> (dout_master !== $past(dout_master));
	endproperty

	assert property (dout_master_sampled_n)
 	 else $error("dout_master changed at posedge sclk: Previous = %b, Current = %b", 
               $past(dout_master), dout_master); 

	property dout_slave_sampled_n;
	  @(negedge sclk)
	  disable iff (rst)
	  (req == 1 | req ==3 && !cs && dout_slave !== 0) |-> (dout_slave !== $past(dout_slave));
	endproperty

	assert property (dout_slave_sampled_n)
 	 else $error("dout_slave changed at posedge sclk: Previous = %b, Current = %b", 
               $past(dout_slave), dout_slave);    

	assert property (sclk_en_assert)
 	 else $error("sclk does not toggle when not en");  
	property sclk_en_assert;
	  @(posedge clk)
  		disable iff (rst)
		(done_tx | done_rx) |-> ##[0:MASTER_FREQ / (SLAVE_FREQ * 2)](sclk_en == 1'b0);
	endproperty

	assert property (sclk_en_assert)
 	 else $error("sclk_en not deasserted after transaction");   


endmodule
