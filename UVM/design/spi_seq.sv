class spi_seq extends uvm_sequence #(spi_tran);
  `uvm_object_utils(spi_seq)

  int min_delay;
  int max_delay;
  int delay;
  int seq_count;
  int seq_index;
  string seq_type;
  
  spi_tran tr;

  function new(string name = "spi_seq");
    super.new(name);
    seq_index = 0;
    seq_type = "base";
  endfunction

  function int get_random_delay();
    return $urandom_range(min_delay, max_delay);
  endfunction

  task body();
    `uvm_info(get_type_name(), "Starting Sequence", UVM_MEDIUM)
    repeat (seq_count) begin
      tr = spi_tran::type_id::create("tr");
      start_item(tr);
      
      assert(tr.randomize() with {});
      
      seq_index++;
      tr.seq_count 	= this.seq_count;
      tr.seq_index 	= this.seq_index;
      tr.seq_type 	= this.seq_type;
      
      delay 		= get_random_delay();
      tr.delay 		= this.delay;
      
	`uvm_info(get_type_name(), $sformatf("Sent %0d/%0d %s sequences: txdata=0x%h, rxdata=0x%h, start=%0b Next sequence after %0d", 
										seq_index, seq_count, seq_type, tr.tx_data, tr.rx_data, tr.start, tr.delay), 
										UVM_MEDIUM)

      #delay;
      finish_item(tr);
    end
  endtask
endclass
