class spi_tran extends uvm_sequence_item;
  	// Data Types and Variables
  	rand logic [7:0]  tx_data;  // Data to transmit
  	rand logic	miso;
  	
  	logic [7:0]  rx_data;  // Received data
  	logic mosi;
  
    logic        start;    // Start transmission
    logic        busy;     // Transmission in progress
    logic        done;     // Transmission complete
    
    int seq_count;
    int seq_index;
    string seq_type;
    int delay;

	`uvm_object_utils(spi_tran)

	function new(string name = "spi_tran");
		super.new(name);
	endfunction

endclass

