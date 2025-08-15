class spi_drv extends uvm_driver #(spi_tran);
  `uvm_component_utils(spi_drv)

  uvm_analysis_port #(spi_tran) drv_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    drv_ap = new("drv_ap", this);
  endfunction

  task run_phase(uvm_phase phase);
    spi_tran tr;
    forever begin
      seq_item_port.get_next_item(tr);

      drv_ap.write(tr);
      `uvm_info("DRIVER", $sformatf("Drive %0d/%0d %s transaction to DUT: addr=0x%2h, data=0x%8h, write=%0b",//Please add the inputs outputs based on the DUT.
                                    //tr.seq_index, tr.seq_count, tr.seq_type, tr.addr, tr.data, tr.write),
                                    UVM_MEDIUM)

      seq_item_port.item_done();
    end
  endtask
endclass
