import uvm_pkg::*;
`include "uvm_macros.svh"

// Property and assertion definitions for the SPI module
module spi_sva #(
    parameter CLK_DIV = 4
)(
    input logic clk,
    input logic rst_n,
    input logic start,
    input logic [7:0] tx_data,
    output logic [7:0] rx_data,
    output logic busy,
    output logic done,
    output logic sclk,
    output logic mosi,
    input logic miso,
    output logic cs_n
);

    // Local variable to store previous values for checks
    logic [7:0] prev_tx_data;
    logic prev_busy;
    logic prev_start;
    logic prev_sclk;
    logic prev_cs_n;
    logic [7:0] prev_rx_data;

    // Store previous values on each clock edge
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            prev_tx_data <= '0;
            prev_busy <= '0;
            prev_start <= '0;
            prev_sclk <= '0;
            prev_cs_n <= '0;
            prev_rx_data <= '0;
        end else begin
            prev_tx_data <= tx_data;
            prev_busy <= busy;
            prev_start <= start;
            prev_sclk <= sclk;
            prev_cs_n <= cs_n;
            prev_rx_data <= rx_data;
        end
    end

    // Requirement: 1.1.1 Ensure start is ignored if busy=1.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (busy && start) |-> (!start)
    ) else $error("Assertion 1.1.1 Failed: Start signal was asserted while busy.");

    // Requirement: 1.1.2 Check no new transaction begins until done pulse.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (start && !prev_busy) |-> (!busy || prev_done)
    ) else $error("Assertion 1.1.2 Failed: New transaction started before done pulse.");

    // Requirement: 1.1.3 Check busy stays high for exactly 8 bits.
    // This implies busy should be high for 16 sclk cycles (8 bits * 2 sclk edges per bit).
    // And each sclk cycle takes CLK_DIV system clock cycles.
    // So, busy should be high for 16 * CLK_DIV system clock cycles.
    // A simplified check is that busy should go low one cycle after done goes high, or when done is high.
    // Or, busy stays high as long as bit_cnt is not 0 and sclk has not finished its last full cycle.
    // Given the design, 'busy' is asserted when 'start' is high, and deasserted when the state goes back to IDLE.
    // The state goes to IDLE when bit_cnt becomes 0 (after the last bit is processed).
    // We can check busy is high until `done` is asserted, and then goes low in the next cycle.

    // Busy goes high when start, and goes low after done.
    // For 1.1.3: Busy stays high for exactly 8 bits (this means the duration of the transfer).
    // busy is asserted when start, and deasserted when state goes to IDLE (bit_cnt==0 && sclk=1'b1, after miso sample).
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (start && !prev_busy) |=> busy ##[((8 * 2 * CLK_DIV) - 1) : (8 * 2 * CLK_DIV) -1] !busy
    ) else $error("Assertion 1.1.3 Failed: Busy signal did not stay high for exactly 8 bits.");

    // Requirement: 1.1.4 Verify done is exactly 1 clock cycle after the last bit.
    // 'done' is asserted when 'bit_cnt' becomes 0 (last bit), and 'state' transitions to 'IDLE'.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (busy && !bit_cnt && sclk) |=> done
    ) else $error("Assertion 1.1.4 Failed: Done signal was not asserted exactly 1 clock cycle after the last bit.");

    // Requirement: 1.1.5 Ensure busy deasserts 1 clk cycle after done.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (done && prev_busy) |-> (!busy)
    ) else $error("Assertion 1.1.5 Failed: Busy did not deassert 1 clock cycle after done.");

    // Requirement: 1.1.6 Confirm busy goes high immediately after start.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (start && !prev_busy) |-> (busy)
    ) else $error("Assertion 1.1.6 Failed: Busy did not go high immediately after start.");

    // Requirement: 1.2.1 cs_n must go low immediately after start.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (start && !prev_busy) |-> (!cs_n)
    ) else $error("Assertion 1.2.1 Failed: cs_n did not go low immediately after start.");

    // Requirement: 1.2.2 cs_n should not glitch during transfer.
    // cs_n should remain low while busy is high.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (busy) |-> (!cs_n)
    ) else $error("Assertion 1.2.2 Failed: cs_n glitched during transfer.");

    // Requirement: 1.2.3 cs_n must go high after the 8th bit (aligned with done).
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (done) |-> (cs_n)
    ) else $error("Assertion 1.2.3 Failed: cs_n did not go high after the 8th bit/done.");

    // Requirement: 1.2.4 cs_n should not deassert early (e.g., after 7 bits).
    // This is implicitly covered by 1.2.2 and 1.2.3, but we can add a specific check.
    // cs_n stays low as long as bit_cnt > 0 during TRANSFER state.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (state == TRANSFER && bit_cnt > 0) |-> (!cs_n)
    ) else $error("Assertion 1.2.4 Failed: cs_n deasserted early (before 8 bits were transferred).");


    // Requirement: 2.1.1 Verify mosi shifts out tx_data[7] first, tx_data[0] last.
    // MOSI changes on falling edge of SCLK. Data is shifted out from MSB (tx_reg[7]) to LSB (tx_reg[0]).
    // 'bit_cnt' counts down from 7 to 0, where 7 is the first bit (MSB) and 0 is the last bit (LSB).
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (state == TRANSFER && !sclk && prev_sclk) |-> (mosi == tx_reg[bit_cnt])
    ) else $error("Assertion 2.1.1 Failed: MOSI did not shift out data in correct order (MSB first).");

    // Requirement: 2.1.2 Ensure mosi only changes on falling clock edges.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (state == TRANSFER && sclk && !prev_sclk) |-> (mosi == $past(mosi))
    ) else $error("Assertion 2.1.2 Failed: MOSI changed on rising clock edge.");

    // Requirement: 2.2.1 Confirm miso is sampled only on rising sclk edge.
    // MISO is sampled on the rising edge of SCLK.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (state == TRANSFER && sclk && !prev_sclk) |-> ($rose(sclk) && rx_reg[bit_cnt] == $past(miso, 1, @(posedge clk)))
    ) else $error("Assertion 2.2.1 Failed: MISO not sampled on rising sclk edge.");

    // Requirement: 2.2.2 Compare rx_data with expected slave response.
    // This requires a testbench component (scoreboard) to predict the slave's response.
    // SVA can only check if rx_data is updated correctly at the end.
    // The comparison will be handled by the scoreboard in the testbench.
    // This assertion can verify that `rx_data` is only updated once at the end.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (state == TRANSFER && !bit_cnt && sclk) |-> (rx_data == {rx_reg[6:0], miso})
    ) else $error("Assertion 2.2.2 Failed: rx_data not updated with the final received value.");


    // Requirement: 2.2.3 Ensure rx_data updates only when done=1.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (state == TRANSFER && bit_cnt > 0) |-> (rx_data == $past(rx_data))
    ) else $error("Assertion 2.2.3 Failed: rx_data updated before transaction was done.");

    // Requirement: 3.1.1 Verify sclk period = 2 * CLK_DIV * clk period.
    // This means one full SCLK cycle (high and low) takes 2 * CLK_DIV system clock cycles.
    // We'll check the sclk period.
    // Sequence to check one full SCLK cycle.
    sequence sclk_period_check;
        sclk ##[2*CLK_DIV-1] !sclk ##[2*CLK_DIV-1] sclk;
    endsequence
    assert property (@(posedge clk)
        disable iff (!rst_n || state != TRANSFER)
        sclk_period_check
    ) else $error("Assertion 3.1.1 Failed: SCLK period is not 2 * CLK_DIV * clk period.");


    // Requirement: 3.1.2 Confirm sclk=0 when cs_n=1 (idle).
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (state == IDLE) |-> (!sclk)
    ) else $error("Assertion 3.1.2 Failed: SCLK is not 0 when in IDLE state (cs_n is high).");

    // Requirement: 3.1.3 Ensure no sclk glitches outside transfers.
    // This implies sclk should be stable (at 0) during IDLE state.
    assert property (@(posedge clk)
        disable iff (!rst_n)
        (state == IDLE) |-> ($stable(sclk))
    ) else $error("Assertion 3.1.3 Failed: SCLK glitched during IDLE state.");

    // Requirement: 4.1.1 Reset during transfer.
    // This requires a specific test case, not a general assertion.
    // It verifies how the module behaves when reset is asserted during an ongoing transfer.
    // The expected behavior is that the module should immediately go to its reset state.
    // No specific assertion can be written for this, but a coverage point can be added.
    cover property (@(posedge clk)
        (state == TRANSFER && !rst_n)
    ) $info("Coverage 4.1.1: Reset asserted during transfer.");


    // Requirement: 4.1.2 Back-to-back transfers.
    // This is a scenario for a test sequence, not an assertion for correctness.
    // It implies ensuring the module correctly handles immediate re-initiation of transfer after one completes.
    cover property (@(posedge clk)
        (done ##1 start)
    ) $info("Coverage 4.1.2: Back-to-back transfers.");

    // Requirement: 4.1.3 Start without rst_n.
    // This is an invalid scenario, usually caught by reset sequence.
    // It should be handled by testbench, not by SVA usually.
    // However, if we want to confirm the module doesn't start without reset,
    // we could assert that 'start' is only acknowledged after 'rst_n' is released.
    // Given the design, the module always starts in IDLE after reset, so this is mostly covered.

    // Requirement: 4.1.4 miso timing violations.
    // This requires checking setup and hold times, which are typically handled in gate-level simulations
    // or by checking specific timing models, not usually by functional SVA.
    // However, a basic check can be done to ensure MISO is stable around the rising edge of SCLK.
    // This might be more complex as it depends on external MISO source.
    // For functional SVA, we assume MISO is valid when sampled.

    // Requirement: 4.1.5 Long sequence of transfers.
    // This is a test scenario, not an assertion.
    // It checks the module's robustness over many continuous operations.
    cover property (@(posedge clk)
        start ##[1000] start // Example: two starts separated by 1000 cycles
    ) $info("Coverage 4.1.5: Long sequence of transfers.");

    // Requirement: 4.1.6 Synchronous reset.
    // The design uses an asynchronous reset (`negedge rst_n` in always_ff block).
    // If the requirement is for *synchronous* reset, the design needs modification.
    // Assuming the requirement meant how the module reacts to the given reset,
    // the initial block ensures proper reset values.

    // Requirement: 5.1.1 Scoreboard comparison of sent vs. received.
    // This is handled by a scoreboard in the testbench, not SVA.
    // SVA can assert that rx_data is loaded *when done*.
    assert property (@(posedge clk)
        (done) |-> (rx_data == expected_rx_data) // 'expected_rx_data' would come from the scoreboard/prediction model
    ) else $error("Assertion 5.1.1 Failed: Received data does not match expected data.");

    // Requirement: 5.1.2 Reset during active transfer. (Duplicate of 4.1.1)
    // Covered by 4.1.1.
endmodule
