
//------------------------------------------------------------
// Event detection and wait duration latching
//------------------------------------------------------------
logic        sclk_rise, sclk_fall;
logic        rise_counting, fall_counting;
int unsigned rise_counter, fall_counter;
int unsigned rise_wait_target, fall_wait_target;

// Detect rise/fall events
always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
        sclk_rise       <= 1'b0;
        sclk_fall       <= 1'b0;
        rise_counting   <= 1'b0;
        fall_counting   <= 1'b0;
        rise_counter    <= 0;
        fall_counter    <= 0;
        rise_wait_target<= 0;
        fall_wait_target<= 0;
    end else begin
        sclk_rise <= (din_master == dout_slave) && $rose(sclk);
        sclk_fall <= (din_slave  == dout_master) && $fell(sclk);

        //------------------------------
        // TX: Rise event handling
        //------------------------------
        if (sclk_rise) begin
            rise_wait_target <= wait_duration;  // latch current wait_duration
            rise_counting    <= 1'b1;
            rise_counter     <= 0;
        end else if (rise_counting) begin
            rise_counter <= rise_counter + 1;
            if (rise_counter >= rise_wait_target)
                rise_counting <= 1'b0; // stop when reached
        end

        //------------------------------
        // RX: Fall event handling
        //------------------------------
        if (sclk_fall) begin
            fall_wait_target <= wait_duration;  // latch current wait_duration
            fall_counting    <= 1'b1;
            fall_counter     <= 0;
        end else if (fall_counting) begin
            fall_counter <= fall_counter + 1;
            if (fall_counter >= fall_wait_target)
                fall_counting <= 1'b0; // stop when reached
        end
    end
end

//------------------------------------------------------------
// Assertions with pass/fail printouts
//------------------------------------------------------------
done_tx_check: assert property (
    @(posedge clk) disable iff (rst || !(req == 2'b01 || req == 2'b11))
        ( (rise_wait_target == 0 && sclk_rise) ||
          (rise_wait_target > 0 && !rise_counting && rise_counter == rise_wait_target) )
        |-> done_tx
) begin
    $display("%t [PASS][done_tx] latched_dur=%0d counter=%0d rise_counting=%0b done_tx=%b",
             $time, rise_wait_target, rise_counter, rise_counting, done_tx);
end else begin
    $error("%t [FAIL][done_tx] latched_dur=%0d counter=%0d rise_counting=%0b done_tx=%b",
           $time, rise_wait_target, rise_counter, rise_counting, done_tx);
end

done_rx_check: assert property (
    @(posedge clk) disable iff (rst || !(req == 2'b10 || req == 2'b11))
        ( (fall_wait_target == 0 && sclk_fall) ||
          (fall_wait_target > 0 && !fall_counting && fall_counter == fall_wait_target) )
        |-> done_rx
) begin
    $display("%t [PASS][done_rx] latched_dur=%0d counter=%0d fall_counting=%0b done_rx=%b",
             $time, fall_wait_target, fall_counter, fall_counting, done_rx);
end else begin
    $error("%t [FAIL][done_rx] latched_dur=%0d counter=%0d fall_counting=%0b done_rx=%b",
           $time, fall_wait_target, fall_counter, fall_counting, done_rx);
end



