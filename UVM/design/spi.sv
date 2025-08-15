module spi #(
    parameter CLK_DIV = 4  // Clock divider (sysclk/spi_clk)
)(
    input  logic        clk,      // System clock
    input  logic        rst_n,    // Active-low reset
    input  logic        start,    // Start transmission
    input  logic [7:0]  tx_data,  // Data to transmit
    output logic [7:0]  rx_data,  // Received data
    output logic        busy,     // Transmission in progress
    output logic        done,     // Transmission complete
    
    // SPI interface
    output logic        sclk,     // SPI clock
    output logic        mosi,     // Master out, slave in
    input  logic        miso,     // Master in, slave out
    output logic        cs_n      // Chip select (active low)
);

    logic [7:0] tx_reg;    // Transmit shift register
    logic [7:0] rx_reg;    // Receive shift register
    logic [2:0] bit_cnt;   // Bit counter (0-7)
    logic [CLK_DIV-1:0] clk_cnt;  // Clock divider counter
    
    typedef enum {IDLE, TRANSFER} state_t;
    state_t state;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            sclk <= 1'b0;
            cs_n <= 1'b1;
            busy <= 1'b0;
            done <= 1'b0;
            rx_data <= 8'h00;
            clk_cnt <= '0;
            bit_cnt <= 3'd7;
        end else begin
            done <= 1'b0;
            
            case (state)
                IDLE: begin
                    cs_n <= 1'b1;
                    sclk <= 1'b0;
                    busy <= 1'b0;
                    clk_cnt <= '0;
                    bit_cnt <= 3'd7;
                    
                    if (start) begin
                        state <= TRANSFER;
                        tx_reg <= tx_data;
                        cs_n <= 1'b0;
                        busy <= 1'b1;
                    end
                end
                
                TRANSFER: begin
                    if (clk_cnt == CLK_DIV-1) begin
                        clk_cnt <= '0;
                        sclk <= ~sclk;
                        
                        if (sclk) begin
                            // Rising edge - sample MISO
                            rx_reg <= {rx_reg[6:0], miso};
                            
                            if (bit_cnt == 0) begin
                                // Last bit
                                state <= IDLE;
                                rx_data <= {rx_reg[6:0], miso};
                                done <= 1'b1;
                                cs_n <= 1'b1;
                            end else begin
                                bit_cnt <= bit_cnt - 1;
                            end
                        end else begin
                            // Falling edge - change MOSI
                            mosi <= tx_reg[bit_cnt];
                        end
                    end else begin
                        clk_cnt <= clk_cnt + 1;
                    end
                end
            endcase
        end
    end

endmodule
