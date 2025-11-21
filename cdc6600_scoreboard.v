(** * CDC 6600 Scoreboard Formalization
    Rigorous mechanization of the CDC 6600 dynamic instruction scheduling mechanism.
    Based on Thornton's original design (1964). *)

Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import List.
Import ListNotations.

(** ** Foundational Types *)

(** X register identifiers: 8 operand registers (X0-X7), 60-bit each *)
Inductive xreg : Type :=
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7.

(** A register identifiers: 8 address registers (A0-A7), 18-bit each *)
Inductive areg : Type :=
  | A0 | A1 | A2 | A3 | A4 | A5 | A6 | A7.

(** B register identifiers: 8 increment/index registers (B0-B7), 18-bit each
    B0 is hardware-enforced to zero *)
Inductive breg : Type :=
  | B0 | B1 | B2 | B3 | B4 | B5 | B6 | B7.

(** Functional unit enumeration: 10 independent execution units *)
Inductive func_unit : Type :=
  | FU_Branch
  | FU_Boolean
  | FU_Shift
  | FU_LongAdd
  | FU_FPAdd
  | FU_FPMul1
  | FU_FPMul2
  | FU_FPDiv
  | FU_Incr1
  | FU_Incr2.

(** Functional unit equality *)
Definition func_unit_eq (fu1 fu2 : func_unit) : bool :=
  match fu1, fu2 with
  | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
  | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
  | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
  | _, _ => false
  end.

(** Functional unit equality correctness *)
Lemma func_unit_eq_spec : forall fu1 fu2, func_unit_eq fu1 fu2 = true <-> fu1 = fu2.
Proof.
  intros fu1 fu2. split.
  - intro H. destruct fu1, fu2; try reflexivity; discriminate H.
  - intro H. rewrite H. destruct fu2; reflexivity.
Qed.

(** Functional unit decidable equality *)
Lemma func_unit_eq_dec : forall fu1 fu2 : func_unit, {fu1 = fu2} + {fu1 <> fu2}.
Proof.
  intros fu1 fu2.
  destruct (func_unit_eq fu1 fu2) eqn:Heq.
  - left. apply func_unit_eq_spec. assumption.
  - right. intro Hcontra. apply func_unit_eq_spec in Hcontra. rewrite Hcontra in Heq. discriminate.
Qed.

(** Q-numbers encode result provenance:
    - QFU fu: Result pending from functional unit fu
    - QNone: No result pending
    - QDReg n: Result pending from D register n (memory buffer) *)
Inductive qnum : Type :=
  | QFU (fu : func_unit)
  | QNone
  | QDReg (n : nat).

(** Q-number equality *)
Definition qnum_eq (q1 q2 : qnum) : bool :=
  match q1, q2 with
  | QNone, QNone => true
  | QFU fu1, QFU fu2 => match fu1, fu2 with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1
      | FU_Incr2, FU_Incr2 => true
      | _, _ => false
      end
  | QDReg n1, QDReg n2 => Nat.eqb n1 n2
  | _, _ => false
  end.

(** Q-number equality correctness *)
Lemma qnum_eq_spec : forall q1 q2, qnum_eq q1 q2 = true <-> q1 = q2.
Proof.
  intros q1 q2. split.
  - intro H. destruct q1, q2; simpl in H; try discriminate; auto.
    + destruct fu, fu0; try discriminate; reflexivity.
    + apply Nat.eqb_eq in H. rewrite H. reflexivity.
  - intro H. rewrite H. destruct q2; simpl; auto.
    + destruct fu; reflexivity.
    + apply Nat.eqb_refl.
Qed.

(** Operation codes for branch unit *)
Inductive branch_op : Type :=
  | OP_BEQ | OP_BNE | OP_BLT | OP_BGE | OP_JMP.

(** Operation codes for boolean unit *)
Inductive bool_op : Type :=
  | OP_AND | OP_OR | OP_XOR | OP_NOT | OP_NAND.

(** Operation codes for shift unit *)
Inductive shift_op : Type :=
  | OP_SLL | OP_SRL | OP_SRA | OP_ROT.

(** Operation codes for long integer add unit *)
Inductive longadd_op : Type :=
  | OP_LADD | OP_LSUB.

(** Operation codes for floating point add unit *)
Inductive fpadd_op : Type :=
  | OP_FADD | OP_FSUB.

(** Operation codes for floating point multiply units *)
Inductive fpmul_op : Type :=
  | OP_FMUL.

(** Operation codes for floating point divide unit *)
Inductive fpdiv_op : Type :=
  | OP_FDIV.

(** Operation codes for increment units (18-bit integer add, memory load/store) *)
Inductive incr_op : Type :=
  | OP_INCR | OP_DECR | OP_LOAD | OP_STORE.

(** Unified operation type encoding all possible operations *)
Inductive operation : Type :=
  | Op_Branch (op : branch_op)
  | Op_Bool (op : bool_op)
  | Op_Shift (op : shift_op)
  | Op_LongAdd (op : longadd_op)
  | Op_FPAdd (op : fpadd_op)
  | Op_FPMul (op : fpmul_op)
  | Op_FPDiv (op : fpdiv_op)
  | Op_Incr (op : incr_op).

(** Execution latency in clock cycles for each operation type *)
Definition latency (op : operation) : nat :=
  match op with
  | Op_Branch _ => 3
  | Op_Bool _ => 3
  | Op_Shift _ => 3
  | Op_LongAdd _ => 3
  | Op_FPAdd _ => 4
  | Op_FPMul _ => 10
  | Op_FPDiv _ => 29
  | Op_Incr _ => 3
  end.

(** All operations have non-zero latency *)
Lemma latency_nonzero : forall op, latency op > 0.
Proof.
  intros []; simpl; auto with arith.
Qed.

(** Latency is bounded by maximum unit latency (FP divide: 29 cycles) *)
Lemma latency_bounded : forall op, latency op <= 29.
Proof.
  intros [b | b0 | s | l | f | f0 | f1 | i];
    (destruct b || destruct b0 || destruct s || destruct l ||
     destruct f || destruct f0 || destruct f1 || destruct i);
    simpl; lia.
Qed.

(** Check if operation is a load *)
Definition is_load (op : operation) : bool :=
  match op with
  | Op_Incr OP_LOAD => true
  | _ => false
  end.

(** Check if operation is a store *)
Definition is_store (op : operation) : bool :=
  match op with
  | Op_Incr OP_STORE => true
  | _ => false
  end.

(** Check if operation is a memory operation (load or store) *)
Definition is_mem_op (op : operation) : bool :=
  orb (is_load op) (is_store op).

(** ** Computational Semantics *)

(** 60-bit data value bounds *)
Definition MAX_60BIT : nat := 2^60 - 1.

(** 18-bit data value bounds *)
Definition MAX_18BIT : nat := 2^18 - 1.

(** Modular arithmetic for 60-bit values *)
Definition mod60 (n : nat) : nat := n mod (2^60).

(** Modular arithmetic for 18-bit values *)
Definition mod18 (n : nat) : nat := n mod (2^18).

(** Branch operation semantics *)
Definition eval_branch_op (op : branch_op) (v1 v2 : nat) : bool :=
  match op with
  | OP_BEQ => Nat.eqb v1 v2
  | OP_BNE => negb (Nat.eqb v1 v2)
  | OP_BLT => Nat.ltb v1 v2
  | OP_BGE => Nat.leb v2 v1
  | OP_JMP => true
  end.

(** Boolean operation semantics *)
Definition eval_bool_op (op : bool_op) (v1 v2 : nat) : nat :=
  match op with
  | OP_AND => Nat.land v1 v2
  | OP_OR => Nat.lor v1 v2
  | OP_XOR => Nat.lxor v1 v2
  | OP_NOT => Nat.lxor v1 MAX_60BIT
  | OP_NAND => Nat.lxor (Nat.land v1 v2) MAX_60BIT
  end.

(** Shift operation semantics *)
Definition eval_shift_op (op : shift_op) (v1 v2 : nat) : nat :=
  let shift_amt := v2 mod 60 in
  match op with
  | OP_SLL => mod60 (Nat.shiftl v1 shift_amt)
  | OP_SRL => Nat.shiftr v1 shift_amt
  | OP_SRA => Nat.shiftr v1 shift_amt
  | OP_ROT => mod60 ((Nat.shiftl v1 shift_amt) + (Nat.shiftr v1 (60 - shift_amt)))
  end.

(** Long add operation semantics *)
Definition eval_longadd_op (op : longadd_op) (v1 v2 : nat) : nat :=
  match op with
  | OP_LADD => mod60 (v1 + v2)
  | OP_LSUB => mod60 (v1 - v2)
  end.

(** Floating point add operation semantics (abstract) *)
Definition eval_fpadd_op (op : fpadd_op) (v1 v2 : nat) : nat :=
  match op with
  | OP_FADD => mod60 (v1 + v2)
  | OP_FSUB => mod60 (v1 - v2)
  end.

(** Floating point multiply operation semantics (abstract) *)
Definition eval_fpmul_op (op : fpmul_op) (v1 v2 : nat) : nat :=
  match op with
  | OP_FMUL => mod60 (v1 * v2)
  end.

(** Floating point divide operation semantics (abstract) *)
Definition eval_fpdiv_op (op : fpdiv_op) (v1 v2 : nat) : nat :=
  match op with
  | OP_FDIV => if Nat.eqb v2 0 then 0 else mod60 (v1 / v2)
  end.

(** Increment operation semantics *)
Definition eval_incr_op (op : incr_op) (v1 v2 : nat) : nat :=
  match op with
  | OP_INCR => mod18 (v1 + v2)
  | OP_DECR => mod18 (v1 - v2)
  | OP_LOAD => v1
  | OP_STORE => v1
  end.

(** Unified operation evaluation *)
Definition eval_operation (op : operation) (v1 v2 : nat) : option nat :=
  match op with
  | Op_Branch bop => Some (if eval_branch_op bop v1 v2 then 1 else 0)
  | Op_Bool bop => Some (eval_bool_op bop v1 v2)
  | Op_Shift sop => Some (eval_shift_op sop v1 v2)
  | Op_LongAdd lop => Some (eval_longadd_op lop v1 v2)
  | Op_FPAdd fop => Some (eval_fpadd_op fop v1 v2)
  | Op_FPMul mop => Some (eval_fpmul_op mop v1 v2)
  | Op_FPDiv dop => Some (eval_fpdiv_op dop v1 v2)
  | Op_Incr iop => Some (eval_incr_op iop v1 v2)
  end.

(** ** Register and State Structures *)

(** 60-bit data value (abstract representation) *)
Definition word60 : Type := nat.

(** 18-bit address/index value (abstract representation) *)
Definition word18 : Type := nat.

(** X register file: 8 operand registers *)
Definition xreg_file : Type := xreg -> word60.

(** A register file: 8 address registers *)
Definition areg_file : Type := areg -> word18.

(** B register file: 8 increment/index registers *)
Definition breg_file : Type := breg -> word18.

(** Generic register identifier for operands *)
Inductive reg_id : Type :=
  | Reg_X (r : xreg)
  | Reg_A (r : areg)
  | Reg_B (r : breg).

(** Functional unit descriptor: Busy, Op, Fi, Fj, Fk, Qj, Qk, Rj, Rk, operand values, result, branch target *)
Record fu_descriptor : Type := mk_fu_desc {
  fu_busy : bool;
  fu_op : option operation;
  fu_fi : option reg_id;
  fu_fj : option reg_id;
  fu_fk : option reg_id;
  fu_qj : qnum;
  fu_qk : qnum;
  fu_rj : bool;
  fu_rk : bool;
  fu_remaining_cycles : nat;
  fu_operand1 : nat;
  fu_operand2 : nat;
  fu_result : option nat;
  fu_branch_target : option nat
}.

(** Functional unit status: mapping from functional units to descriptors *)
Definition fu_status : Type := func_unit -> fu_descriptor.

(** Register result status: which functional unit will write each register *)
Record reg_result_status : Type := mk_reg_result {
  xreg_result : xreg -> qnum;
  areg_result : areg -> qnum;
  breg_result : breg -> qnum
}.

(** Instruction execution stage *)
Inductive instr_stage : Type :=
  | Stage_Issue
  | Stage_ReadOps
  | Stage_Execute
  | Stage_WriteResult.

(** Instruction descriptor *)
Record instruction : Type := mk_instr {
  instr_op : operation;
  instr_dest : reg_id;
  instr_src1 : reg_id;
  instr_src2 : reg_id;
  instr_branch_target : option nat
}.

(** Instruction memory: mapping from address to instruction *)
Definition instr_memory : Type := nat -> option instruction.

(** Program counter type: 18-bit address *)
Definition pc : Type := nat.

(** 18-bit address space size - opaque to avoid large computation *)
Definition ADDR_SPACE_SIZE : nat := 262144.  (* 2^18 = 262144 *)

(** Valid PC: within 18-bit address space *)
Definition valid_pc (p : pc) : Prop := p < ADDR_SPACE_SIZE.

(** Zero is a valid PC *)
Lemma zero_valid_pc : valid_pc 0.
Proof.
  unfold valid_pc, ADDR_SPACE_SIZE.
  apply Nat.neq_0_lt_0.
  intro H. discriminate H.
Qed.

(** ADDR_SPACE_SIZE is positive *)
Lemma addr_space_size_positive : 0 < ADDR_SPACE_SIZE.
Proof.
  unfold ADDR_SPACE_SIZE.
  apply Nat.lt_0_succ.
Qed.

(** ADDR_SPACE_SIZE is nonzero *)
Lemma addr_space_size_nonzero : ADDR_SPACE_SIZE <> 0.
Proof.
  apply Nat.neq_0_lt_0.
  apply addr_space_size_positive.
Qed.

(** Incrementing valid PC preserves validity (wraps modulo address space size) *)
Lemma pc_increment_valid : forall p, valid_pc p -> valid_pc ((p + 1) mod ADDR_SPACE_SIZE).
Proof.
  intros p Hp.
  unfold valid_pc in *.
  apply Nat.mod_upper_bound.
  apply addr_space_size_nonzero.
Qed.

Opaque ADDR_SPACE_SIZE.

(** Maximum instruction queue depth *)
Definition MAX_QUEUE_DEPTH : nat := 8.

(** ** Memory System Types *)

(** Memory address: 17-bit physical address *)
Definition mem_addr : Type := nat.

(** Memory bank identifier: 0-31 for 32-way interleaving *)
Definition bank_id : Type := nat.

(** Memory bank state: mapping from offset to 60-bit word *)
Definition bank_state : Type := nat -> nat.

(** Memory bank status *)
Record bank_status : Type := mk_bank_status {
  bank_busy : bool;
  bank_remaining_cycles : nat;
  bank_pending_addr : option mem_addr;
  bank_is_write : bool
}.

(** D-register identifier *)
Inductive dreg : Type :=
  | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7.

(** D-register status *)
Record dreg_status : Type := mk_dreg_status {
  dreg_busy : bool;
  dreg_has_data : bool;
  dreg_data : nat;
  dreg_target_xreg : option nat;
  dreg_source_addr : option mem_addr;
  dreg_remaining_cycles : nat
}.

(** Central Memory state *)
Record central_memory : Type := mk_central_memory {
  mem_banks : bank_id -> bank_state;
  mem_bank_status : bank_id -> bank_status;
  mem_cycle_count : nat
}.

(** D-register file *)
Definition dreg_file : Type := dreg -> dreg_status.

(** Complete memory subsystem *)
Record memory_subsystem : Type := mk_mem_subsystem {
  main_memory : central_memory;
  d_registers : dreg_file
}.

(** Memory bank capacity: 4K words per bank *)
Definition BANK_SIZE : nat := 4096.

(** Extract bank ID from address (lower 5 bits determine bank) *)
Definition addr_to_bank (addr : mem_addr) : bank_id :=
  addr mod 32.

(** Extract bank offset from address (upper 12 bits) *)
Definition addr_to_offset (addr : mem_addr) : nat :=
  addr / 32.

(** Scoreboard state: all components *)
Record scoreboard_state : Type := mk_sb_state {
  sb_xregs : xreg_file;
  sb_aregs : areg_file;
  sb_bregs : breg_file;
  sb_fu_status : fu_status;
  sb_reg_result : reg_result_status;
  sb_instr_queue : list instruction;
  sb_cycle_count : nat;
  sb_pc : pc;
  sb_imem : instr_memory;
  sb_mem : memory_subsystem
}.

(** ** Well-Formedness Invariants *)

(** Q-number validity: references valid functional units or sentinels *)
Definition qnum_valid (q : qnum) : Prop :=
  match q with
  | QFU _ => True
  | QNone => True
  | QDReg n => n < 7
  end.

(** Functional unit descriptor validity *)
Definition fu_desc_valid (desc : fu_descriptor) : Prop :=
  qnum_valid (fu_qj desc) /\ qnum_valid (fu_qk desc) /\
  (forall target, fu_branch_target desc = Some target -> valid_pc target).

(** B0 is always zero *)
Definition b0_zero_inv (bregs : breg_file) : Prop :=
  bregs B0 = 0.

(** When busy=false, descriptor fields are irrelevant *)
Definition busy_consistency (desc : fu_descriptor) : Prop :=
  fu_busy desc = false ->
    fu_op desc = None /\
    fu_fi desc = None /\
    fu_fj desc = None /\
    fu_fk desc = None /\
    fu_qj desc = QNone /\
    fu_qk desc = QNone.

(** Register result status consistency with FU destinations *)
Definition reg_result_consistency (fus : fu_status) (rrs : reg_result_status) : Prop :=
  forall fu,
    match fu_fi (fus fu) with
    | Some (Reg_X xr) => fu_busy (fus fu) = true -> xreg_result rrs xr = QFU fu
    | Some (Reg_A ar) => fu_busy (fus fu) = true -> areg_result rrs ar = QFU fu
    | Some (Reg_B br) => fu_busy (fus fu) = true -> breg_result rrs br = QFU fu
    | None => True
    end.

(** Rj is true iff Qj indicates operand ready *)
Definition rj_correctness (desc : fu_descriptor) : Prop :=
  fu_rj desc = true <-> fu_qj desc = QNone.

(** Rk is true iff Qk indicates operand ready *)
Definition rk_correctness (desc : fu_descriptor) : Prop :=
  fu_rk desc = true <-> fu_qk desc = QNone.

(** Register result status has valid Q-numbers *)
Definition reg_result_valid (rrs : reg_result_status) : Prop :=
  (forall xr, qnum_valid (xreg_result rrs xr)) /\
  (forall ar, qnum_valid (areg_result rrs ar)) /\
  (forall br, qnum_valid (breg_result rrs br)).

(** Instruction memory immutability *)
Definition imem_immutable (imem1 imem2 : instr_memory) : Prop :=
  forall addr, imem1 addr = imem2 addr.

(** Instruction queue depth bounded *)
Definition queue_bounded (st : scoreboard_state) : Prop :=
  length (sb_instr_queue st) <= MAX_QUEUE_DEPTH.

(** Instruction validity: branch target must be valid PC if present *)
Definition instr_valid (instr : instruction) : Prop :=
  forall target, instr_branch_target instr = Some target -> valid_pc target.

(** All instructions in queue are valid *)
Definition queue_instrs_valid (st : scoreboard_state) : Prop :=
  forall instr, In instr (sb_instr_queue st) -> instr_valid instr.

(** Memory subsystem invariants *)
Definition bank_data_valid (mem : central_memory) : Prop :=
  forall bid offset, offset < BANK_SIZE ->
    (mem_banks mem bid) offset < 2^60.

Definition bank_mutual_exclusion (mem : central_memory) : Prop :=
  forall bid, bank_busy (mem_bank_status mem bid) = true ->
    exists addr, bank_pending_addr (mem_bank_status mem bid) = Some addr
              /\ addr_to_bank addr = bid.

Definition dreg_data_valid (dregs : dreg_file) : Prop :=
  forall d, dreg_has_data (dregs d) = true ->
    dreg_data (dregs d) < 2^60.

Definition dreg_busy_has_addr (dregs : dreg_file) : Prop :=
  forall d, dreg_busy (dregs d) = true ->
    exists addr, dreg_source_addr (dregs d) = Some addr.

Definition dreg_addrs_valid (dregs : dreg_file) : Prop :=
  forall d addr, dreg_source_addr (dregs d) = Some addr -> addr < 2^17.

Definition mem_subsystem_valid (msys : memory_subsystem) : Prop :=
  bank_data_valid (main_memory msys) /\
  bank_mutual_exclusion (main_memory msys) /\
  dreg_data_valid (d_registers msys) /\
  dreg_busy_has_addr (d_registers msys) /\
  dreg_addrs_valid (d_registers msys).

(** Remaining cycles bounded by latency *)
Definition cycles_bounded (desc : fu_descriptor) : Prop :=
  fu_busy desc = true ->
  match fu_op desc with
  | Some op => fu_remaining_cycles desc <= latency op
  | None => True
  end.

(** Instruction memory contains only valid instructions *)
Definition imem_valid (imem : instr_memory) : Prop :=
  forall addr instr, imem addr = Some instr -> instr_valid instr.

(** Complete scoreboard well-formedness invariant *)
Definition scoreboard_invariant (st : scoreboard_state) : Prop :=
  b0_zero_inv (sb_bregs st) /\
  (forall fu, fu_desc_valid (sb_fu_status st fu)) /\
  (forall fu, busy_consistency (sb_fu_status st fu)) /\
  (forall fu, rj_correctness (sb_fu_status st fu)) /\
  (forall fu, rk_correctness (sb_fu_status st fu)) /\
  (forall fu, cycles_bounded (sb_fu_status st fu)) /\
  reg_result_consistency (sb_fu_status st) (sb_reg_result st) /\
  reg_result_valid (sb_reg_result st) /\
  valid_pc (sb_pc st) /\
  queue_bounded st /\
  queue_instrs_valid st /\
  mem_subsystem_valid (sb_mem st) /\
  imem_valid (sb_imem st).

(** Initial functional unit descriptor: all idle *)
Definition init_fu_desc : fu_descriptor :=
  mk_fu_desc false None None None None QNone QNone true true 0 0 0 None None.

(** Initial functional unit status: all units idle *)
Definition init_fu_status : fu_status :=
  fun _ => init_fu_desc.

(** Initial register result status: no pending results *)
Definition init_reg_result : reg_result_status :=
  mk_reg_result (fun _ => QNone) (fun _ => QNone) (fun _ => QNone).

(** Empty instruction memory *)
Definition init_imem : instr_memory := fun _ => None.

(** Initial memory bank *)
Definition init_bank : bank_state := fun offset => 0.

(** Initial bank status *)
Definition init_bank_status : bank_status :=
  mk_bank_status false 0 None false.

(** Initial central memory *)
Definition init_central_memory : central_memory :=
  mk_central_memory
    (fun bid => init_bank)
    (fun bid => init_bank_status)
    0.

(** Initial D-register status *)
Definition init_dreg_status : dreg_status :=
  mk_dreg_status false false 0 None None 0.

(** Initial D-register file *)
Definition init_dreg_file : dreg_file :=
  fun d => init_dreg_status.

(** Initial memory subsystem *)
Definition init_mem_subsystem : memory_subsystem :=
  mk_mem_subsystem init_central_memory init_dreg_file.

(** Memory timing parameters (in 100ns clock cycles) *)
Definition MEM_ACCESS_TIME : nat := 10.

(** Read word from bank *)
Definition read_bank (mem : central_memory) (addr : mem_addr) : nat :=
  let bid := addr_to_bank addr in
  let offset := addr_to_offset addr in
  (mem_banks mem bid) offset.

(** Step memory bank status *)
Definition step_bank_status (bs : bank_status) : bank_status :=
  if bank_busy bs then
    if Nat.eqb (bank_remaining_cycles bs) 1 then
      init_bank_status
    else
      mk_bank_status true (bank_remaining_cycles bs - 1)
                     (bank_pending_addr bs) (bank_is_write bs)
  else
    bs.

(** Step memory banks *)
Definition step_memory (mem : central_memory) : central_memory :=
  mk_central_memory
    (mem_banks mem)
    (fun bid => step_bank_status (mem_bank_status mem bid))
    (S (mem_cycle_count mem)).

(** Step D-register *)
Definition step_dreg_status (ds : dreg_status) (mem : central_memory) : dreg_status :=
  if dreg_busy ds then
    if Nat.eqb (dreg_remaining_cycles ds) 1 then
      match dreg_source_addr ds with
      | None => init_dreg_status
      | Some addr =>
          let data := read_bank mem addr in
          mk_dreg_status true true data (dreg_target_xreg ds) (Some addr) 0
      end
    else
      mk_dreg_status true (dreg_has_data ds) (dreg_data ds)
                     (dreg_target_xreg ds) (dreg_source_addr ds)
                     (dreg_remaining_cycles ds - 1)
  else
    ds.

(** Step entire memory subsystem *)
Definition step_mem_subsystem (msys : memory_subsystem) : memory_subsystem :=
  let new_mem := step_memory (main_memory msys) in
  let new_dregs := fun d => step_dreg_status (d_registers msys d) new_mem in
  mk_mem_subsystem new_mem new_dregs.

(** Step bank preserves bank data validity *)
Lemma step_bank_preserves_data_valid : forall mem,
  bank_data_valid mem ->
  bank_data_valid (step_memory mem).
Proof.
  intros mem Hvalid bid off.
  unfold step_memory.
  apply Hvalid.
Qed.

(** Step bank preserves mutual exclusion *)
Lemma step_bank_preserves_mutual_exclusion : forall mem,
  bank_mutual_exclusion mem ->
  bank_mutual_exclusion (step_memory mem).
Proof.
  intros mem Hexcl bid Hbusy.
  unfold step_memory in Hbusy. simpl in Hbusy.
  unfold step_bank_status in Hbusy.
  destruct (bank_busy (mem_bank_status mem bid)) eqn:Hb.
  - destruct (Nat.eqb (bank_remaining_cycles (mem_bank_status mem bid)) 1) eqn:Hcyc.
    + simpl in Hbusy. unfold init_bank_status in Hbusy. simpl in Hbusy. discriminate Hbusy.
    + simpl in Hbusy.
      specialize (Hexcl bid Hb). destruct Hexcl as [addr [Haddr Hbank]].
      exists addr. split; [|assumption].
      unfold step_memory. simpl. unfold step_bank_status.
      rewrite Hb, Hcyc. simpl. assumption.
  - simpl in Hbusy. congruence.
Qed.

(** Helper: addr_to_offset is bounded by BANK_SIZE for all addresses. *)
Lemma addr_to_offset_bounded : forall addr, addr < 2^17 -> addr_to_offset addr < BANK_SIZE.
Proof.
  intros addr Haddr.
  unfold addr_to_offset, BANK_SIZE.
  assert (H: addr < 32 * 4096).
  { change (2^17) with 131072 in Haddr. change (32 * 4096) with 131072. lia. }
  apply Nat.div_lt_upper_bound. lia. lia.
Qed.


(** Step D-register preserves data validity *)
Lemma step_dreg_preserves_data_valid : forall dregs mem,
  dreg_data_valid dregs ->
  dreg_addrs_valid dregs ->
  bank_data_valid mem ->
  dreg_data_valid (fun d => step_dreg_status (dregs d) mem).
Proof.
  intros dregs mem Hdreg Haddr_valid Hbank d Hhas_data.
  unfold step_dreg_status in Hhas_data.
  destruct (dreg_busy (dregs d)) eqn:Hbusy.
  - destruct (Nat.eqb (dreg_remaining_cycles (dregs d)) 1) eqn:Hcyc.
    + destruct (dreg_source_addr (dregs d)) eqn:Haddr.
      * unfold step_dreg_status. rewrite Hbusy, Hcyc, Haddr.
        unfold read_bank. unfold bank_data_valid in Hbank.
        apply Hbank. apply addr_to_offset_bounded.
        eapply Haddr_valid. eassumption.
      * simpl in Hhas_data. discriminate Hhas_data.
    + unfold step_dreg_status. rewrite Hbusy, Hcyc.
      destruct (dreg_has_data (dregs d)) eqn:Hhas_orig.
      * cbv zeta in Hhas_data. apply Hdreg. assumption.
      * cbv zeta in Hhas_data. discriminate Hhas_data.
  - unfold step_dreg_status. rewrite Hbusy. apply Hdreg. assumption.
Qed.

(** Step D-register preserves busy-has-addr *)
Lemma step_dreg_preserves_busy_has_addr : forall dregs mem,
  dreg_busy_has_addr dregs ->
  dreg_busy_has_addr (fun d => step_dreg_status (dregs d) mem).
Proof.
  intros dregs mem Haddr d Hbusy.
  unfold step_dreg_status in Hbusy.
  destruct (dreg_busy (dregs d)) eqn:Hbusy_orig.
  - destruct (Nat.eqb (dreg_remaining_cycles (dregs d)) 1) eqn:Hcyc.
    + destruct (dreg_source_addr (dregs d)) eqn:Hsrc.
      * unfold step_dreg_status. rewrite Hbusy_orig, Hcyc, Hsrc.
        exists m. reflexivity.
      * unfold init_dreg_status in Hbusy. simpl in Hbusy. discriminate Hbusy.
    + unfold step_dreg_status. rewrite Hbusy_orig, Hcyc. simpl in Hbusy.
      specialize (Haddr d Hbusy_orig). destruct Haddr as [addr Haddr].
      exists addr. assumption.
  - unfold step_dreg_status in Hbusy. rewrite Hbusy_orig in Hbusy. discriminate Hbusy.
Qed.

(** Step D-register preserves address validity *)
Lemma step_dreg_preserves_addrs_valid : forall dregs mem,
  dreg_addrs_valid dregs ->
  dreg_addrs_valid (fun d => step_dreg_status (dregs d) mem).
Proof.
  intros dregs mem Hvalid d addr Hsrc.
  unfold step_dreg_status in Hsrc.
  destruct (dreg_busy (dregs d)) eqn:Hbusy.
  - destruct (Nat.eqb (dreg_remaining_cycles (dregs d)) 1) eqn:Hcyc.
    + destruct (dreg_source_addr (dregs d)) eqn:Haddr.
      * simpl in Hsrc. injection Hsrc as Hsrc. subst addr.
        apply Hvalid with (d:=d). assumption.
      * unfold init_dreg_status in Hsrc. simpl in Hsrc. discriminate Hsrc.
    + simpl in Hsrc. apply Hvalid with (d:=d). assumption.
  - apply Hvalid with (d:=d). assumption.
Qed.

(** Memory subsystem stepping preserves validity *)
Lemma step_mem_subsystem_preserves_validity : forall msys,
  mem_subsystem_valid msys ->
  mem_subsystem_valid (step_mem_subsystem msys).
Proof.
  intros msys Hvalid.
  unfold mem_subsystem_valid in *.
  destruct Hvalid as [Hdata [Hmutex [Hdreg [Hdreg_has_addr Hdreg_addr]]]].
  unfold step_mem_subsystem. simpl.
  split. apply step_bank_preserves_data_valid. assumption.
  split. apply step_bank_preserves_mutual_exclusion. assumption.
  split. eapply step_dreg_preserves_data_valid; eassumption.
  split. apply step_dreg_preserves_busy_has_addr. assumption.
  apply step_dreg_preserves_addrs_valid. assumption.
Qed.

(** Initial scoreboard state *)
Definition init_scoreboard_state : scoreboard_state :=
  mk_sb_state
    (fun _ => 0)
    (fun _ => 0)
    (fun r => match r with B0 => 0 | _ => 0 end)
    init_fu_status
    init_reg_result
    nil
    0
    0
    init_imem
    init_mem_subsystem.

(** Helper: 0 < 2^60 *)
Lemma zero_lt_power_60 : 0 < 2^60.
Proof.
  assert (2^60 <> 0). { apply Nat.pow_nonzero. lia. }
  lia.
Qed.

(** Helper: initial bank data is valid *)
Lemma init_bank_data_valid : bank_data_valid init_central_memory.
Proof.
  unfold bank_data_valid, init_central_memory, init_bank.
  intros bid offset Hoff.
  change ((fun offset0 => 0) offset < 2^60).
  cbv beta. apply zero_lt_power_60.
Qed.

(** Helper: initial banks have mutual exclusion *)
Lemma init_bank_mutual_exclusion : bank_mutual_exclusion init_central_memory.
Proof.
  unfold bank_mutual_exclusion, init_central_memory, init_bank_status.
  intros bid H. simpl in H. discriminate.
Qed.

(** Helper: initial D-registers have valid data *)
Lemma init_dreg_data_valid : dreg_data_valid init_dreg_file.
Proof.
  unfold dreg_data_valid, init_dreg_file, init_dreg_status.
  intros d H. simpl in H. discriminate.
Qed.

(** Helper: initial busy D-registers have addresses *)
Lemma init_dreg_busy_has_addr : dreg_busy_has_addr init_dreg_file.
Proof.
  unfold dreg_busy_has_addr, init_dreg_file, init_dreg_status.
  intros d H. simpl in H. discriminate.
Qed.

(** Helper: initial D-register addresses are valid *)
Lemma init_dreg_addrs_valid : dreg_addrs_valid init_dreg_file.
Proof.
  unfold dreg_addrs_valid, init_dreg_file, init_dreg_status.
  intros d addr H. simpl in H. discriminate.
Qed.

(** Initial state satisfies all invariants *)
Theorem init_state_valid : scoreboard_invariant init_scoreboard_state.
Proof.
  unfold scoreboard_invariant, init_scoreboard_state. simpl.
  split. unfold b0_zero_inv. simpl. reflexivity.
  split. intros fu. unfold fu_desc_valid, init_fu_status, init_fu_desc. simpl. split. constructor. split. constructor. intros target H. discriminate.
  split. intros fu. unfold busy_consistency, init_fu_status, init_fu_desc. simpl. intros _. repeat split; reflexivity.
  split. intros fu. unfold rj_correctness, init_fu_status, init_fu_desc. simpl. split; intros; reflexivity.
  split. intros fu. unfold rk_correctness, init_fu_status, init_fu_desc. simpl. split; intros; reflexivity.
  split. intros fu. unfold cycles_bounded, init_fu_status, init_fu_desc. simpl. intros H. discriminate.
  split. unfold reg_result_consistency, init_fu_status, init_fu_desc, init_reg_result. simpl. intros fu. destruct fu; simpl; constructor.
  split. unfold reg_result_valid, init_reg_result. simpl. split. intros. constructor. split. intros. constructor. intros. constructor.
  split. unfold init_scoreboard_state. simpl sb_pc. apply zero_valid_pc.
  split. unfold queue_bounded, init_scoreboard_state. simpl. lia.
  split. unfold queue_instrs_valid, init_scoreboard_state. simpl. intros instr H. inversion H.
  split.
  unfold mem_subsystem_valid, init_scoreboard_state, init_mem_subsystem. simpl.
  repeat split.
  - apply init_bank_data_valid.
  - apply init_bank_mutual_exclusion.
  - apply init_dreg_data_valid.
  - apply init_dreg_busy_has_addr.
  - apply init_dreg_addrs_valid.
  - unfold imem_valid, init_scoreboard_state, init_imem. simpl.
    intros addr instr H. discriminate.
Qed.

(** ** Hazard Detection Predicates *)

(** Determine which functional unit type can execute an operation, with load balancing *)
Definition fu_for_op (op : operation) (fus : fu_status) : func_unit :=
  match op with
  | Op_Branch _ => FU_Branch
  | Op_Bool _ => FU_Boolean
  | Op_Shift _ => FU_Shift
  | Op_LongAdd _ => FU_LongAdd
  | Op_FPAdd _ => FU_FPAdd
  | Op_FPMul _ => if fu_busy (fus FU_FPMul1) then FU_FPMul2 else FU_FPMul1
  | Op_FPDiv _ => FU_FPDiv
  | Op_Incr _ => if fu_busy (fus FU_Incr1) then FU_Incr2 else FU_Incr1
  end.

(** fu_for_op always returns a valid functional unit *)
Lemma fu_for_op_valid : forall op fus,
  match fu_for_op op fus with
  | FU_Branch | FU_Boolean | FU_Shift | FU_LongAdd | FU_FPAdd
  | FU_FPMul1 | FU_FPMul2 | FU_FPDiv | FU_Incr1 | FU_Incr2 => True
  end.
Proof.
  intros op fus.
  destruct op; simpl; auto.
  - destruct (fu_busy (fus FU_FPMul1)); auto.
  - destruct (fu_busy (fus FU_Incr1)); auto.
Qed.

(** FU allocation for multiply operations *)
Lemma fu_for_fpmul_cases : forall fus,
  fu_for_op (Op_FPMul OP_FMUL) fus = FU_FPMul1 \/
  fu_for_op (Op_FPMul OP_FMUL) fus = FU_FPMul2.
Proof.
  intro fus. simpl.
  destruct (fu_busy (fus FU_FPMul1)); [right|left]; reflexivity.
Qed.

(** FU allocation for increment operations *)
Lemma fu_for_incr_cases : forall iop fus,
  fu_for_op (Op_Incr iop) fus = FU_Incr1 \/
  fu_for_op (Op_Incr iop) fus = FU_Incr2.
Proof.
  intros iop fus. simpl.
  destruct (fu_busy (fus FU_Incr1)); [right|left]; reflexivity.
Qed.

(** Unique FU for branch operations *)
Lemma fu_for_branch_unique : forall bop fus,
  fu_for_op (Op_Branch bop) fus = FU_Branch.
Proof.
  intros. reflexivity.
Qed.

(** Unique FU for boolean operations *)
Lemma fu_for_bool_unique : forall bop fus,
  fu_for_op (Op_Bool bop) fus = FU_Boolean.
Proof.
  intros. reflexivity.
Qed.

(** Unique FU for shift operations *)
Lemma fu_for_shift_unique : forall sop fus,
  fu_for_op (Op_Shift sop) fus = FU_Shift.
Proof.
  intros. reflexivity.
Qed.

(** Unique FU for long add operations *)
Lemma fu_for_longadd_unique : forall lop fus,
  fu_for_op (Op_LongAdd lop) fus = FU_LongAdd.
Proof.
  intros. reflexivity.
Qed.

(** Unique FU for FP add operations *)
Lemma fu_for_fpadd_unique : forall fop fus,
  fu_for_op (Op_FPAdd fop) fus = FU_FPAdd.
Proof.
  intros. reflexivity.
Qed.

(** Unique FU for FP divide operations *)
Lemma fu_for_fpdiv_unique : forall dop fus,
  fu_for_op (Op_FPDiv dop) fus = FU_FPDiv.
Proof.
  intros. reflexivity.
Qed.

(** Structural hazard: required functional unit is busy *)
Definition structural_hazard (fus : fu_status) (instr : instruction) : Prop :=
  fu_busy (fus (fu_for_op (instr_op instr) fus)) = true.

(** Structural hazard is already boolean *)
Lemma structural_hazard_bool : forall fus instr,
  structural_hazard fus instr <-> fu_busy (fus (fu_for_op (instr_op instr) fus)) = true.
Proof.
  intros. unfold structural_hazard. tauto.
Qed.

(** X register equality *)
Definition xreg_eq (x1 x2 : xreg) : bool :=
  match x1, x2 with
  | X0, X0 | X1, X1 | X2, X2 | X3, X3 | X4, X4 | X5, X5 | X6, X6 | X7, X7 => true
  | _, _ => false
  end.

(** X register equality correctness *)
Lemma xreg_eq_spec : forall x1 x2, xreg_eq x1 x2 = true <-> x1 = x2.
Proof.
  intros x1 x2. split.
  - intro H. destruct x1, x2; try reflexivity; discriminate H.
  - intro H. rewrite H. destruct x2; reflexivity.
Qed.

(** X register decidable equality *)
Lemma xreg_eq_dec : forall x1 x2 : xreg, {x1 = x2} + {x1 <> x2}.
Proof.
  intros x1 x2.
  destruct (xreg_eq x1 x2) eqn:Heq.
  - left. apply xreg_eq_spec. assumption.
  - right. intro Hcontra. apply xreg_eq_spec in Hcontra. rewrite Hcontra in Heq. discriminate.
Qed.

(** A register equality *)
Definition areg_eq (a1 a2 : areg) : bool :=
  match a1, a2 with
  | A0, A0 | A1, A1 | A2, A2 | A3, A3 | A4, A4 | A5, A5 | A6, A6 | A7, A7 => true
  | _, _ => false
  end.

(** A register equality correctness *)
Lemma areg_eq_spec : forall a1 a2, areg_eq a1 a2 = true <-> a1 = a2.
Proof.
  intros a1 a2. split.
  - intro H. destruct a1, a2; try reflexivity; discriminate H.
  - intro H. rewrite H. destruct a2; reflexivity.
Qed.

(** A register decidable equality *)
Lemma areg_eq_dec : forall a1 a2 : areg, {a1 = a2} + {a1 <> a2}.
Proof.
  intros a1 a2.
  destruct (areg_eq a1 a2) eqn:Heq.
  - left. apply areg_eq_spec. assumption.
  - right. intro Hcontra. apply areg_eq_spec in Hcontra. rewrite Hcontra in Heq. discriminate.
Qed.

(** B register equality *)
Definition breg_eq (b1 b2 : breg) : bool :=
  match b1, b2 with
  | B0, B0 | B1, B1 | B2, B2 | B3, B3 | B4, B4 | B5, B5 | B6, B6 | B7, B7 => true
  | _, _ => false
  end.

(** B register equality correctness *)
Lemma breg_eq_spec : forall b1 b2, breg_eq b1 b2 = true <-> b1 = b2.
Proof.
  intros b1 b2. split.
  - intro H. destruct b1, b2; try reflexivity; discriminate H.
  - intro H. rewrite H. destruct b2; reflexivity.
Qed.

(** B register decidable equality *)
Lemma breg_eq_dec : forall b1 b2 : breg, {b1 = b2} + {b1 <> b2}.
Proof.
  intros b1 b2.
  destruct (breg_eq b1 b2) eqn:Heq.
  - left. apply breg_eq_spec. assumption.
  - right. intro Hcontra. apply breg_eq_spec in Hcontra. rewrite Hcontra in Heq. discriminate.
Qed.

(** Register equality *)
Definition reg_eq (r1 r2 : reg_id) : bool :=
  match r1, r2 with
  | Reg_X x1, Reg_X x2 => xreg_eq x1 x2
  | Reg_A a1, Reg_A a2 => areg_eq a1 a2
  | Reg_B b1, Reg_B b2 => breg_eq b1 b2
  | _, _ => false
  end.

(** Register equality correctness *)
Lemma reg_eq_spec : forall r1 r2, reg_eq r1 r2 = true <-> r1 = r2.
Proof.
  intros r1 r2. split.
  - intro H. destruct r1, r2; try discriminate H.
    + apply xreg_eq_spec in H. rewrite H. reflexivity.
    + apply areg_eq_spec in H. rewrite H. reflexivity.
    + apply breg_eq_spec in H. rewrite H. reflexivity.
  - intro H. rewrite H. destruct r2; simpl.
    + apply xreg_eq_spec. reflexivity.
    + apply areg_eq_spec. reflexivity.
    + apply breg_eq_spec. reflexivity.
Qed.

(** Register decidable equality *)
Lemma reg_eq_dec : forall r1 r2 : reg_id, {r1 = r2} + {r1 <> r2}.
Proof.
  intros r1 r2.
  destruct (reg_eq r1 r2) eqn:Heq.
  - left. apply reg_eq_spec. assumption.
  - right. intro Hcontra. apply reg_eq_spec in Hcontra. rewrite Hcontra in Heq. discriminate.
Qed.

(** Check if any busy FU will write to a register *)
Definition reg_reserved (fus : fu_status) (r : reg_id) : bool :=
  orb (orb (orb (orb (orb (orb (orb (orb (orb
    (andb (fu_busy (fus FU_Branch)) (match fu_fi (fus FU_Branch) with Some fi => reg_eq fi r | None => false end))
    (andb (fu_busy (fus FU_Boolean)) (match fu_fi (fus FU_Boolean) with Some fi => reg_eq fi r | None => false end)))
    (andb (fu_busy (fus FU_Shift)) (match fu_fi (fus FU_Shift) with Some fi => reg_eq fi r | None => false end)))
    (andb (fu_busy (fus FU_LongAdd)) (match fu_fi (fus FU_LongAdd) with Some fi => reg_eq fi r | None => false end)))
    (andb (fu_busy (fus FU_FPAdd)) (match fu_fi (fus FU_FPAdd) with Some fi => reg_eq fi r | None => false end)))
    (andb (fu_busy (fus FU_FPMul1)) (match fu_fi (fus FU_FPMul1) with Some fi => reg_eq fi r | None => false end)))
    (andb (fu_busy (fus FU_FPMul2)) (match fu_fi (fus FU_FPMul2) with Some fi => reg_eq fi r | None => false end)))
    (andb (fu_busy (fus FU_FPDiv)) (match fu_fi (fus FU_FPDiv) with Some fi => reg_eq fi r | None => false end)))
    (andb (fu_busy (fus FU_Incr1)) (match fu_fi (fus FU_Incr1) with Some fi => reg_eq fi r | None => false end)))
    (andb (fu_busy (fus FU_Incr2)) (match fu_fi (fus FU_Incr2) with Some fi => reg_eq fi r | None => false end)).

(** WAW hazard: destination register already reserved *)
Definition waw_hazard (fus : fu_status) (instr : instruction) : Prop :=
  reg_reserved fus (instr_dest instr) = true.

(** WAW hazard is already boolean *)
Lemma waw_hazard_bool : forall fus instr,
  waw_hazard fus instr <-> reg_reserved fus (instr_dest instr) = true.
Proof.
  intros. unfold waw_hazard. tauto.
Qed.

(** First-order conflict: structural hazard or WAW hazard *)
Definition first_order_conflict (fus : fu_status) (instr : instruction) : Prop :=
  structural_hazard fus instr \/ waw_hazard fus instr.

(** Boolean version of first-order conflict for computation *)
Definition first_order_conflict_b (fus : fu_status) (instr : instruction) : bool :=
  orb (fu_busy (fus (fu_for_op (instr_op instr) fus)))
      (reg_reserved fus (instr_dest instr)).

(** Equivalence between boolean and propositional first-order conflict *)
Lemma first_order_conflict_iff : forall fus instr,
  first_order_conflict fus instr <-> first_order_conflict_b fus instr = true.
Proof.
  intros fus instr.
  unfold first_order_conflict, first_order_conflict_b.
  unfold structural_hazard, waw_hazard.
  split.
  - intros [H | H].
    + apply orb_true_intro. left. destruct (fu_busy (fus (fu_for_op (instr_op instr) fus))); auto.
    + apply orb_true_intro. right. assumption.
  - intro H. apply orb_prop in H. destruct H as [H | H].
    + left. destruct (fu_busy (fus (fu_for_op (instr_op instr) fus))) eqn:E; auto; discriminate.
    + right. assumption.
Qed.

(** RAW hazard for a source operand: operand not ready *)
Definition raw_hazard_operand (desc : fu_descriptor) (is_j : bool) : Prop :=
  if is_j then fu_qj desc <> QNone else fu_qk desc <> QNone.

(** RAW hazard: source operands not ready *)
Definition raw_hazard (desc : fu_descriptor) : Prop :=
  fu_qj desc <> QNone \/ fu_qk desc <> QNone.

(** Boolean version of RAW hazard *)
Definition raw_hazard_b (desc : fu_descriptor) : bool :=
  negb (andb (qnum_eq (fu_qj desc) QNone) (qnum_eq (fu_qk desc) QNone)).

(** RAW hazard equivalence *)
Lemma raw_hazard_iff : forall desc,
  raw_hazard desc <-> raw_hazard_b desc = true.
Proof.
  intro desc. unfold raw_hazard, raw_hazard_b.
  split.
  - intros [H | H].
    + apply negb_true_iff. apply andb_false_intro1.
      destruct (qnum_eq (fu_qj desc) QNone) eqn:E; auto.
      apply qnum_eq_spec in E. contradiction.
    + apply negb_true_iff. apply andb_false_intro2.
      destruct (qnum_eq (fu_qk desc) QNone) eqn:E; auto.
      apply qnum_eq_spec in E. contradiction.
  - intro H. apply negb_true_iff in H. apply andb_false_elim in H.
    destruct H as [H | H].
    + left. intro Hcontra. apply qnum_eq_spec in Hcontra. rewrite Hcontra in H. discriminate.
    + right. intro Hcontra. apply qnum_eq_spec in Hcontra. rewrite Hcontra in H. discriminate.
Qed.

(** Second-order conflict: RAW hazard *)
Definition second_order_conflict (desc : fu_descriptor) : Prop :=
  raw_hazard desc.

(** Check if a register will be read by any busy FU *)
Definition reg_will_be_read (fus : fu_status) (r : reg_id) : bool :=
  orb (orb (orb (orb (orb (orb (orb (orb (orb
    (andb (fu_busy (fus FU_Branch))
      (orb (match fu_fj (fus FU_Branch) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_Branch) with Some fk => reg_eq fk r | None => false end)))
    (andb (fu_busy (fus FU_Boolean))
      (orb (match fu_fj (fus FU_Boolean) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_Boolean) with Some fk => reg_eq fk r | None => false end))))
    (andb (fu_busy (fus FU_Shift))
      (orb (match fu_fj (fus FU_Shift) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_Shift) with Some fk => reg_eq fk r | None => false end))))
    (andb (fu_busy (fus FU_LongAdd))
      (orb (match fu_fj (fus FU_LongAdd) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_LongAdd) with Some fk => reg_eq fk r | None => false end))))
    (andb (fu_busy (fus FU_FPAdd))
      (orb (match fu_fj (fus FU_FPAdd) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_FPAdd) with Some fk => reg_eq fk r | None => false end))))
    (andb (fu_busy (fus FU_FPMul1))
      (orb (match fu_fj (fus FU_FPMul1) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_FPMul1) with Some fk => reg_eq fk r | None => false end))))
    (andb (fu_busy (fus FU_FPMul2))
      (orb (match fu_fj (fus FU_FPMul2) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_FPMul2) with Some fk => reg_eq fk r | None => false end))))
    (andb (fu_busy (fus FU_FPDiv))
      (orb (match fu_fj (fus FU_FPDiv) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_FPDiv) with Some fk => reg_eq fk r | None => false end))))
    (andb (fu_busy (fus FU_Incr1))
      (orb (match fu_fj (fus FU_Incr1) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_Incr1) with Some fk => reg_eq fk r | None => false end))))
    (andb (fu_busy (fus FU_Incr2))
      (orb (match fu_fj (fus FU_Incr2) with Some fj => reg_eq fj r | None => false end)
           (match fu_fk (fus FU_Incr2) with Some fk => reg_eq fk r | None => false end))).

(** WAR hazard: writing would overwrite register needed by pending instruction *)
Definition war_hazard (fus : fu_status) (dest : reg_id) : Prop :=
  reg_will_be_read fus dest = true.

(** WAR hazard is already boolean *)
Lemma war_hazard_bool : forall fus dest,
  war_hazard fus dest <-> reg_will_be_read fus dest = true.
Proof.
  intros. unfold war_hazard. tauto.
Qed.

(** Third-order conflict: WAR hazard *)
Definition third_order_conflict (fus : fu_status) (dest : reg_id) : Prop :=
  war_hazard fus dest.

(** ** Stage Transition Functions *)

(** All instructions in memory have valid branch targets - now part of invariant *)
Lemma imem_instr_valid : forall (st : scoreboard_state) (addr : pc) (instr : instruction),
  scoreboard_invariant st ->
  sb_imem st addr = Some instr ->
  instr_valid instr.
Proof.
  intros st addr instr Hinv Himem.
  unfold scoreboard_invariant in Hinv.
  destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Himem_valid]]]]]]]]]]]].
  unfold imem_valid in Himem_valid.
  apply (Himem_valid addr instr Himem).
Qed.

(** Issue precondition: no first-order conflicts and valid instruction *)
Definition issue_precond (st : scoreboard_state) (instr : instruction) : Prop :=
  ~first_order_conflict (sb_fu_status st) instr /\ instr_valid instr.

(** Get Q-number for a register from register result status *)
Definition get_qnum (rrs : reg_result_status) (r : reg_id) : qnum :=
  match r with
  | Reg_X xr => xreg_result rrs xr
  | Reg_A ar => areg_result rrs ar
  | Reg_B br => breg_result rrs br
  end.

(** Update register result status for a register *)
Definition set_qnum (rrs : reg_result_status) (r : reg_id) (q : qnum) : reg_result_status :=
  match r with
  | Reg_X xr => mk_reg_result
      (fun xr' => if match xr, xr' with X0,X0|X1,X1|X2,X2|X3,X3|X4,X4|X5,X5|X6,X6|X7,X7 => true | _,_ => false end
                  then q else xreg_result rrs xr')
      (areg_result rrs)
      (breg_result rrs)
  | Reg_A ar => mk_reg_result
      (xreg_result rrs)
      (fun ar' => if match ar, ar' with A0,A0|A1,A1|A2,A2|A3,A3|A4,A4|A5,A5|A6,A6|A7,A7 => true | _,_ => false end
                  then q else areg_result rrs ar')
      (breg_result rrs)
  | Reg_B br => mk_reg_result
      (xreg_result rrs)
      (areg_result rrs)
      (fun br' => if match br, br' with B0,B0|B1,B1|B2,B2|B3,B3|B4,B4|B5,B5|B6,B6|B7,B7 => true | _,_ => false end
                  then q else breg_result rrs br')
  end.

(** Update functional unit status for a specific FU *)
Definition update_fu (fus : fu_status) (fu : func_unit) (desc : fu_descriptor) : fu_status :=
  fun fu' => if match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end then desc else fus fu'.

(** Increment cycle counter *)
Definition increment_cycle (st : scoreboard_state) : scoreboard_state :=
  mk_sb_state
    (sb_xregs st)
    (sb_aregs st)
    (sb_bregs st)
    (sb_fu_status st)
    (sb_reg_result st)
    (sb_instr_queue st)
    (sb_cycle_count st + 1)
    (sb_pc st)
    (sb_imem st)
    (step_mem_subsystem (sb_mem st)).

(** Issue transition: reserve FU, set up descriptor, update register result status *)
Definition issue_transition (st : scoreboard_state) (instr : instruction) : scoreboard_state :=
  let fu := fu_for_op (instr_op instr) (sb_fu_status st) in
  let qj := get_qnum (sb_reg_result st) (instr_src1 instr) in
  let qk := get_qnum (sb_reg_result st) (instr_src2 instr) in
  let new_desc := mk_fu_desc
    true
    (Some (instr_op instr))
    (Some (instr_dest instr))
    (Some (instr_src1 instr))
    (Some (instr_src2 instr))
    qj
    qk
    (match qj with QNone => true | _ => false end)
    (match qk with QNone => true | _ => false end)
    (latency (instr_op instr))
    0
    0
    None
    (instr_branch_target instr)
  in
  let new_fus := update_fu (sb_fu_status st) fu new_desc in
  let new_rrs := set_qnum (sb_reg_result st) (instr_dest instr) (QFU fu) in
  increment_cycle (mk_sb_state
    (sb_xregs st)
    (sb_aregs st)
    (sb_bregs st)
    new_fus
    new_rrs
    (sb_instr_queue st)
    (sb_cycle_count st)
    (sb_pc st)
    (sb_imem st)
    (sb_mem st)).

(** Read operands precondition: no second-order conflict *)
Definition read_precond (fu : func_unit) (st : scoreboard_state) : Prop :=
  fu_busy (sb_fu_status st fu) = true /\
  ~second_order_conflict (sb_fu_status st fu).

(** Boolean version of read_precond *)
Definition read_precond_b (fu : func_unit) (st : scoreboard_state) : bool :=
  andb (fu_busy (sb_fu_status st fu)) (negb (raw_hazard_b (sb_fu_status st fu))).

(** read_precond decidability *)
Lemma read_precond_dec : forall fu st, {read_precond fu st} + {~read_precond fu st}.
Proof.
  intros fu st.
  destruct (read_precond_b fu st) eqn:Heq.
  - left. unfold read_precond, read_precond_b, second_order_conflict in *.
    apply andb_prop in Heq. destruct Heq as [Hbusy Hraw].
    split. assumption.
    apply negb_true_iff in Hraw.
    intro Hcontra.
    apply raw_hazard_iff in Hcontra.
    rewrite Hcontra in Hraw. discriminate.
  - right. unfold read_precond, read_precond_b, second_order_conflict in *.
    intro Hcontra. destruct Hcontra as [Hbusy Hnoraw].
    assert (Hraw: raw_hazard_b (sb_fu_status st fu) = false).
    { destruct (raw_hazard_b (sb_fu_status st fu)) eqn:Hrb; [|reflexivity].
      exfalso. apply Hnoraw. apply raw_hazard_iff. assumption. }
    rewrite Hbusy in Heq. rewrite Hraw in Heq. simpl in Heq. discriminate.
Qed.

(** Read value from a register *)
Definition read_reg (st : scoreboard_state) (r : reg_id) : nat :=
  match r with
  | Reg_X xr => sb_xregs st xr
  | Reg_A ar => sb_aregs st ar
  | Reg_B br => sb_bregs st br
  end.

(** Read operands transition: read operands from register files into FU *)
Definition read_transition (fu : func_unit) (st : scoreboard_state) : scoreboard_state :=
  let desc := sb_fu_status st fu in
  let v1 := match fu_fj desc with
            | Some r => read_reg st r
            | None => 0
            end in
  let v2 := match fu_fk desc with
            | Some r => read_reg st r
            | None => 0
            end in
  let new_desc := mk_fu_desc
    (fu_busy desc)
    (fu_op desc)
    (fu_fi desc)
    (fu_fj desc)
    (fu_fk desc)
    (fu_qj desc)
    (fu_qk desc)
    (fu_rj desc)
    (fu_rk desc)
    (fu_remaining_cycles desc)
    v1
    v2
    None
    (fu_branch_target desc)
  in
  increment_cycle (mk_sb_state
    (sb_xregs st)
    (sb_aregs st)
    (sb_bregs st)
    (update_fu (sb_fu_status st) fu new_desc)
    (sb_reg_result st)
    (sb_instr_queue st)
    (sb_cycle_count st)
    (sb_pc st)
    (sb_imem st)
    (sb_mem st)).

(** Execute step: decrement cycle counter, compute result when done *)
Definition execute_step (fu : func_unit) (st : scoreboard_state) : scoreboard_state :=
  let desc := sb_fu_status st fu in
  if fu_busy desc then
    if Nat.eqb (fu_remaining_cycles desc) 0 then
      st
    else
      let new_cycles := fu_remaining_cycles desc - 1 in
      let result := if Nat.eqb new_cycles 0 then
                      match fu_op desc with
                      | Some op => eval_operation op (fu_operand1 desc) (fu_operand2 desc)
                      | None => None
                      end
                    else
                      fu_result desc
      in
      let new_desc := mk_fu_desc
        (fu_busy desc)
        (fu_op desc)
        (fu_fi desc)
        (fu_fj desc)
        (fu_fk desc)
        (fu_qj desc)
        (fu_qk desc)
        (fu_rj desc)
        (fu_rk desc)
        new_cycles
        (fu_operand1 desc)
        (fu_operand2 desc)
        result
        (fu_branch_target desc)
      in
      increment_cycle (mk_sb_state
        (sb_xregs st)
        (sb_aregs st)
        (sb_bregs st)
        (update_fu (sb_fu_status st) fu new_desc)
        (sb_reg_result st)
        (sb_instr_queue st)
        (sb_cycle_count st)
        (sb_pc st)
        (sb_imem st)
        (sb_mem st))
  else
    st.

(** Writeback precondition: execution complete and no third-order conflict *)
Definition writeback_precond (fu : func_unit) (st : scoreboard_state) : Prop :=
  let desc := sb_fu_status st fu in
  fu_busy desc = true /\
  fu_remaining_cycles desc = 0 /\
  match fu_fi desc with
  | Some dest => ~third_order_conflict (sb_fu_status st) dest
  | None => False
  end.

(** Boolean version of writeback_precond *)
Definition writeback_precond_b (fu : func_unit) (st : scoreboard_state) : bool :=
  let desc := sb_fu_status st fu in
  andb (andb (fu_busy desc) (Nat.eqb (fu_remaining_cycles desc) 0))
       (match fu_fi desc with
        | Some dest => negb (reg_will_be_read (sb_fu_status st) dest)
        | None => false
        end).

(** writeback_precond decidability *)
Lemma writeback_precond_dec : forall fu st, {writeback_precond fu st} + {~writeback_precond fu st}.
Proof.
  intros fu st.
  destruct (fu_busy (sb_fu_status st fu)) eqn:Hbusy.
  - destruct (Nat.eqb (fu_remaining_cycles (sb_fu_status st fu)) 0) eqn:Hcyc.
    + destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi.
      * destruct (reg_will_be_read (sb_fu_status st) dest) eqn:Hwar.
        -- right. intro Hcontra.
           unfold writeback_precond in Hcontra.
           destruct Hcontra as [_ [_ Hnowar]].
           rewrite Hfi in Hnowar.
           apply Hnowar. unfold third_order_conflict, war_hazard. assumption.
        -- left. unfold writeback_precond.
           split. assumption.
           split. apply Nat.eqb_eq. assumption.
           rewrite Hfi. intro Hcontra.
           unfold third_order_conflict, war_hazard in Hcontra.
           rewrite Hcontra in Hwar. discriminate.
      * right. intro Hcontra.
        unfold writeback_precond in Hcontra.
        destruct Hcontra as [_ [_ Hfalse]].
        rewrite Hfi in Hfalse. exact Hfalse.
    + right. intro Hcontra.
      unfold writeback_precond in Hcontra.
      destruct Hcontra as [_ [Hcyc0 _]].
      apply Nat.eqb_eq in Hcyc0. rewrite Hcyc0 in Hcyc. discriminate.
  - right. intro Hcontra.
    unfold writeback_precond in Hcontra.
    destruct Hcontra as [Hb _].
    rewrite Hb in Hbusy. discriminate.
Qed.

(** Write value to a register *)
Definition write_reg (st : scoreboard_state) (r : reg_id) (v : nat) : scoreboard_state :=
  match r with
  | Reg_X xr => mk_sb_state
      (fun xr' => if match xr, xr' with X0,X0|X1,X1|X2,X2|X3,X3|X4,X4|X5,X5|X6,X6|X7,X7 => true | _,_ => false end
                  then v else sb_xregs st xr')
      (sb_aregs st)
      (sb_bregs st)
      (sb_fu_status st)
      (sb_reg_result st)
      (sb_instr_queue st)
      (sb_cycle_count st)
      (sb_pc st)
      (sb_imem st)
      (sb_mem st)
  | Reg_A ar => mk_sb_state
      (sb_xregs st)
      (fun ar' => if match ar, ar' with A0,A0|A1,A1|A2,A2|A3,A3|A4,A4|A5,A5|A6,A6|A7,A7 => true | _,_ => false end
                  then v else sb_aregs st ar')
      (sb_bregs st)
      (sb_fu_status st)
      (sb_reg_result st)
      (sb_instr_queue st)
      (sb_cycle_count st)
      (sb_pc st)
      (sb_imem st)
      (sb_mem st)
  | Reg_B br => mk_sb_state
      (sb_xregs st)
      (sb_aregs st)
      (fun br' => match br' with
                  | B0 => 0  (* B0 is hardware-enforced to zero, always *)
                  | _ => if match br, br' with B0,B0|B1,B1|B2,B2|B3,B3|B4,B4|B5,B5|B6,B6|B7,B7 => true | _,_ => false end
                         then v else sb_bregs st br'
                  end)
      (sb_fu_status st)
      (sb_reg_result st)
      (sb_instr_queue st)
      (sb_cycle_count st)
      (sb_pc st)
      (sb_imem st)
      (sb_mem st)
  end.

(** Broadcast writeback: when FU completes, wake up waiting FUs by clearing matching Q-numbers *)
Definition broadcast_writeback (fus : fu_status) (completed_fu : func_unit) : fu_status :=
  fun fu' =>
    let desc' := fus fu' in
    if fu_busy desc' then
      mk_fu_desc
        (fu_busy desc')
        (fu_op desc')
        (fu_fi desc')
        (fu_fj desc')
        (fu_fk desc')
        (if qnum_eq (fu_qj desc') (QFU completed_fu) then QNone else fu_qj desc')
        (if qnum_eq (fu_qk desc') (QFU completed_fu) then QNone else fu_qk desc')
        (if qnum_eq (fu_qj desc') (QFU completed_fu) then true else fu_rj desc')
        (if qnum_eq (fu_qk desc') (QFU completed_fu) then true else fu_rk desc')
        (fu_remaining_cycles desc')
        (fu_operand1 desc')
        (fu_operand2 desc')
        (fu_result desc')
        (fu_branch_target desc')
    else desc'.

(** Writeback transition: write computed result to register, free FU, clear register result status *)
Definition writeback_transition (fu : func_unit) (st : scoreboard_state) : scoreboard_state :=
  let desc := sb_fu_status st fu in
  match fu_fi desc with
  | Some dest =>
      let st_with_result := match fu_result desc with
                            | Some v => write_reg st dest v
                            | None => st
                            end in
      let new_rrs := set_qnum (sb_reg_result st_with_result) dest QNone in
      let new_pc := match fu_branch_target desc, fu_result desc with
                    | Some target, Some v => if Nat.eqb v 0 then sb_pc st_with_result else target
                    | _, _ => sb_pc st_with_result
                    end in
      let broadcasted_fus := broadcast_writeback (sb_fu_status st_with_result) fu in
      increment_cycle (mk_sb_state
        (sb_xregs st_with_result)
        (sb_aregs st_with_result)
        (sb_bregs st_with_result)
        (update_fu broadcasted_fus fu init_fu_desc)
        new_rrs
        (sb_instr_queue st_with_result)
        (sb_cycle_count st_with_result)
        new_pc
        (sb_imem st_with_result)
        (sb_mem st_with_result))
  | None => st
  end.

(** ** Instruction Fetch and Dispatch *)

(** Fetch instruction from instruction memory at PC *)
Definition fetch_instr (st : scoreboard_state) : option instruction :=
  sb_imem st (sb_pc st).

(** Increment PC with wrapping *)
Definition increment_pc (st : scoreboard_state) : scoreboard_state :=
  mk_sb_state
    (sb_xregs st)
    (sb_aregs st)
    (sb_bregs st)
    (sb_fu_status st)
    (sb_reg_result st)
    (sb_instr_queue st)
    (sb_cycle_count st)
    ((sb_pc st + 1) mod ADDR_SPACE_SIZE)
    (sb_imem st)
    (sb_mem st).

(** Enqueue instruction into instruction queue *)
Definition enqueue_instr (st : scoreboard_state) (instr : instruction) : scoreboard_state :=
  mk_sb_state
    (sb_xregs st)
    (sb_aregs st)
    (sb_bregs st)
    (sb_fu_status st)
    (sb_reg_result st)
    (sb_instr_queue st ++ [instr])
    (sb_cycle_count st)
    (sb_pc st)
    (sb_imem st)
    (sb_mem st).

(** Fetch and enqueue: fetch instruction from memory and add to queue *)
Definition fetch_and_enqueue (st : scoreboard_state) : scoreboard_state :=
  match fetch_instr st with
  | Some instr => enqueue_instr (increment_pc st) instr
  | None => st
  end.

(** Dequeue instruction from instruction queue *)
Definition dequeue_instr (st : scoreboard_state) : option (instruction * scoreboard_state) :=
  match sb_instr_queue st with
  | [] => None
  | instr :: rest => Some (instr, mk_sb_state
                                     (sb_xregs st)
                                     (sb_aregs st)
                                     (sb_bregs st)
                                     (sb_fu_status st)
                                     (sb_reg_result st)
                                     rest
                                     (sb_cycle_count st)
                                     (sb_pc st)
                                     (sb_imem st)
                                     (sb_mem st))
  end.

(** Issue from queue: attempt to issue the front instruction from the queue *)
Definition issue_from_queue (st : scoreboard_state) : scoreboard_state :=
  match dequeue_instr st with
  | None => st
  | Some (instr, st_dequeued) =>
      if negb (first_order_conflict_b (sb_fu_status st) instr)
      then issue_transition st_dequeued instr
      else st
  end.

(** Fetch precondition: queue not full and valid instruction at PC *)
Definition fetch_precond (st : scoreboard_state) : Prop :=
  length (sb_instr_queue st) < MAX_QUEUE_DEPTH /\
  exists instr, sb_imem st (sb_pc st) = Some instr.

(** Dispatch precondition: queue non-empty *)
Definition dispatch_precond (st : scoreboard_state) : Prop :=
  sb_instr_queue st <> [].

(** ** Scoreboard Step Relation *)

(** Single step of scoreboard execution *)
Inductive sb_step : scoreboard_state -> scoreboard_state -> Prop :=
  | Step_Issue : forall st instr st',
      issue_precond st instr ->
      st' = issue_transition st instr ->
      sb_step st st'
  | Step_Read : forall st fu st',
      read_precond fu st ->
      st' = read_transition fu st ->
      sb_step st st'
  | Step_Execute : forall st fu st',
      fu_busy (sb_fu_status st fu) = true ->
      st' = execute_step fu st ->
      sb_step st st'
  | Step_Writeback : forall st fu st',
      writeback_precond fu st ->
      st' = writeback_transition fu st ->
      sb_step st st'
  | Step_Fetch : forall st st',
      fetch_precond st ->
      st' = fetch_and_enqueue st ->
      sb_step st st'
  | Step_Dispatch : forall st st',
      dispatch_precond st ->
      st' = issue_from_queue st ->
      sb_step st st'.

(** Multi-step transitive closure *)
Inductive sb_steps : scoreboard_state -> scoreboard_state -> Prop :=
  | Steps_Refl : forall st,
      sb_steps st st
  | Steps_Step : forall st1 st2 st3,
      sb_step st1 st2 ->
      sb_steps st2 st3 ->
      sb_steps st1 st3.

(** Instruction has completed execution *)
Definition instr_completed (fu : func_unit) (st : scoreboard_state) : Prop :=
  fu_busy (sb_fu_status st fu) = false.

(** All instructions have completed *)
Definition all_instrs_completed (st : scoreboard_state) : Prop :=
  forall fu, instr_completed fu st.

(** ** Safety Properties *)

(** Functional unit update preserves unmodified descriptors *)
Lemma update_fu_preserves_other : forall fus fu desc fu',
  fu <> fu' ->
  update_fu fus fu desc fu' = fus fu'.
Proof.
  intros fus fu desc fu' Hneq.
  unfold update_fu.
  destruct fu, fu'; simpl; try reflexivity; try contradiction.
Qed.

(** Functional unit update with valid descriptor preserves global validity *)
Lemma update_fu_preserves_validity : forall fus fu desc,
  (forall fu', fu_desc_valid (fus fu')) ->
  fu_desc_valid desc ->
  (forall fu', fu_desc_valid (update_fu fus fu desc fu')).
Proof.
  intros fus fu desc Hvalid Hdesc_valid fu'.
  unfold update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq.
  - assumption.
  - apply Hvalid.
Qed.

(** Register file equality implies B0 zero invariant preservation *)
Lemma b0_zero_preserved : forall st st',
  b0_zero_inv (sb_bregs st) ->
  sb_bregs st' = sb_bregs st ->
  b0_zero_inv (sb_bregs st').
Proof.
  intros st st' HB0 Hbregs.
  rewrite Hbregs. assumption.
Qed.

(** Issue transition preserves busy-idle consistency *)
Lemma issue_preserves_busy_consistency : forall st instr,
  (forall fu, busy_consistency (sb_fu_status st fu)) ->
  (forall fu, busy_consistency (sb_fu_status (issue_transition st instr) fu)).
Proof.
  intros st instr Hbusy fu.
  unfold issue_transition. simpl.
  unfold update_fu.
  destruct (match fu_for_op (instr_op instr) (sb_fu_status st), fu with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq.
  - unfold busy_consistency. simpl. intro H. discriminate H.
  - apply Hbusy.
Qed.

(** ** Issue Preserves Invariants *)

Section IssueInvariantPreservation.

(** Issue preserves B0 zero invariant *)
Lemma issue_preserves_b0_zero : forall st instr,
  b0_zero_inv (sb_bregs st) ->
  b0_zero_inv (sb_bregs (issue_transition st instr)).
Proof.
  intros st instr HB0.
  unfold issue_transition. simpl.
  assumption.
Qed.

(** Issue preserves FU descriptor validity given register result status never produces invalid D-registers *)
Lemma issue_preserves_fu_desc_valid : forall st instr,
  (forall r, qnum_valid (get_qnum (sb_reg_result st) r)) ->
  (forall fu, fu_desc_valid (sb_fu_status st fu)) ->
  (forall target, instr_branch_target instr = Some target -> valid_pc target) ->
  (forall fu, fu_desc_valid (sb_fu_status (issue_transition st instr) fu)).
Proof.
  intros st instr Hqvalid Hvalid Htarget_valid.
  unfold issue_transition. simpl.
  intros fu.
  apply update_fu_preserves_validity.
  - assumption.
  - unfold fu_desc_valid. simpl.
    split. apply Hqvalid.
    split. apply Hqvalid.
    assumption.
Qed.

(** Issue preserves Rj correctness *)
Lemma issue_preserves_rj_correct : forall st instr,
  (forall fu, rj_correctness (sb_fu_status st fu)) ->
  (forall fu, rj_correctness (sb_fu_status (issue_transition st instr) fu)).
Proof.
  intros st instr Hrj fu.
  unfold issue_transition, rj_correctness. simpl.
  unfold update_fu.
  destruct (match fu_for_op (instr_op instr) (sb_fu_status st), fu with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq.
  - simpl. split; intros H; destruct (get_qnum (sb_reg_result st) (instr_src1 instr)); auto; discriminate.
  - apply Hrj.
Qed.

(** Issue preserves Rk correctness *)
Lemma issue_preserves_rk_correct : forall st instr,
  (forall fu, rk_correctness (sb_fu_status st fu)) ->
  (forall fu, rk_correctness (sb_fu_status (issue_transition st instr) fu)).
Proof.
  intros st instr Hrk fu.
  unfold issue_transition, rk_correctness. simpl.
  unfold update_fu.
  destruct (match fu_for_op (instr_op instr) (sb_fu_status st), fu with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq.
  - simpl. split; intros H; destruct (get_qnum (sb_reg_result st) (instr_src2 instr)); auto; discriminate.
  - apply Hrk.
Qed.

(** Issue preserves cycles bounded *)
Lemma issue_preserves_cycles_bounded : forall st instr,
  (forall fu, cycles_bounded (sb_fu_status st fu)) ->
  (forall fu, cycles_bounded (sb_fu_status (issue_transition st instr) fu)).
Proof.
  intros st instr Hcycles fu.
  unfold issue_transition, cycles_bounded. simpl.
  unfold update_fu.
  destruct (match fu_for_op (instr_op instr) (sb_fu_status st), fu with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq.
  - simpl. intros _. apply Nat.le_refl.
  - apply Hcycles.
Qed.

(** Register result status has valid Q-numbers from scoreboard invariant *)
Lemma reg_result_valid_qnums : forall st,
  scoreboard_invariant st ->
  forall r, qnum_valid (get_qnum (sb_reg_result st) r).
Proof.
  intros st Hinv r.
  unfold scoreboard_invariant in Hinv.
  destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [Hreg_valid _]]]]]]]].
  unfold reg_result_valid in Hreg_valid.
  destruct Hreg_valid as [Hxvalid [Havalid Hbvalid]].
  destruct r as [xr | ar | br]; unfold get_qnum; simpl.
  - apply Hxvalid.
  - apply Havalid.
  - apply Hbvalid.
Qed.

(** Helper lemma: andb with true on left *)
Lemma andb_true_l : forall b, true && b = b.
Proof. intro b. reflexivity. Qed.

(** Helper lemma: reg_eq is reflexive *)
Lemma reg_eq_refl : forall r, reg_eq r r = true.
Proof.
  intro r. apply reg_eq_spec. reflexivity.
Qed.

(** Helper lemma: if FU is busy with destination r, then reg_reserved returns true *)
Lemma busy_fu_implies_reg_reserved : forall fus fu r,
  fu_busy (fus fu) = true ->
  fu_fi (fus fu) = Some r ->
  reg_reserved fus r = true.
Proof.
  intros fus fu r Hbusy Hfi.
  unfold reg_reserved.
  destruct fu; rewrite Hbusy; rewrite Hfi; rewrite andb_true_l; rewrite reg_eq_refl;
    repeat rewrite orb_true_r; reflexivity.
Qed.

(** Helper lemma: issue_precond implies no busy FU has the same X register destination *)
Lemma issue_precond_no_waw_xreg : forall st instr fu xr,
  issue_precond st instr ->
  instr_dest instr = Reg_X xr ->
  fu_busy (sb_fu_status st fu) = true ->
  fu_fi (sb_fu_status st fu) <> Some (Reg_X xr).
Proof.
  intros st instr fu xr Hpre Hdest Hbusy.
  unfold issue_precond in Hpre. destruct Hpre as [Hno_conflict _].
  unfold first_order_conflict, waw_hazard in Hno_conflict.
  intro Hcontra.
  apply Hno_conflict. right.
  rewrite Hdest.
  eapply busy_fu_implies_reg_reserved; eassumption.
Qed.

(** Helper lemma: issue_precond implies no busy FU has the same A register destination *)
Lemma issue_precond_no_waw_areg : forall st instr fu ar,
  issue_precond st instr ->
  instr_dest instr = Reg_A ar ->
  fu_busy (sb_fu_status st fu) = true ->
  fu_fi (sb_fu_status st fu) <> Some (Reg_A ar).
Proof.
  intros st instr fu ar Hpre Hdest Hbusy.
  unfold issue_precond in Hpre. destruct Hpre as [Hno_conflict _].
  unfold first_order_conflict, waw_hazard in Hno_conflict.
  intro Hcontra.
  apply Hno_conflict. right.
  rewrite Hdest.
  eapply busy_fu_implies_reg_reserved; eassumption.
Qed.

(** Helper lemma: issue_precond implies no busy FU has the same B register destination *)
Lemma issue_precond_no_waw_breg : forall st instr fu br,
  issue_precond st instr ->
  instr_dest instr = Reg_B br ->
  fu_busy (sb_fu_status st fu) = true ->
  fu_fi (sb_fu_status st fu) <> Some (Reg_B br).
Proof.
  intros st instr fu br Hpre Hdest Hbusy.
  unfold issue_precond in Hpre. destruct Hpre as [Hno_conflict _].
  unfold first_order_conflict, waw_hazard in Hno_conflict.
  intro Hcontra.
  apply Hno_conflict. right.
  rewrite Hdest.
  eapply busy_fu_implies_reg_reserved; eassumption.
Qed.

(** Helper lemma: set_qnum for different register preserves Q-number *)
Lemma set_qnum_other_xreg : forall rrs xr xr' q,
  xr <> xr' ->
  xreg_result (set_qnum rrs (Reg_X xr) q) xr' = xreg_result rrs xr'.
Proof.
  intros rrs xr xr' q Hneq.
  unfold set_qnum. simpl.
  destruct (match xr, xr' with X0,X0|X1,X1|X2,X2|X3,X3|X4,X4|X5,X5|X6,X6|X7,X7 => true | _,_ => false end) eqn:Heq.
  - destruct xr, xr'; simpl in Heq; try discriminate Heq; contradiction Hneq; reflexivity.
  - reflexivity.
Qed.

Lemma set_qnum_other_areg : forall rrs ar ar' q,
  ar <> ar' ->
  areg_result (set_qnum rrs (Reg_A ar) q) ar' = areg_result rrs ar'.
Proof.
  intros rrs ar ar' q Hneq.
  unfold set_qnum. simpl.
  destruct (match ar, ar' with A0,A0|A1,A1|A2,A2|A3,A3|A4,A4|A5,A5|A6,A6|A7,A7 => true | _,_ => false end) eqn:Heq.
  - destruct ar, ar'; simpl in Heq; try discriminate Heq; contradiction Hneq; reflexivity.
  - reflexivity.
Qed.

Lemma set_qnum_other_breg : forall rrs br br' q,
  br <> br' ->
  breg_result (set_qnum rrs (Reg_B br) q) br' = breg_result rrs br'.
Proof.
  intros rrs br br' q Hneq.
  unfold set_qnum. simpl.
  destruct (match br, br' with B0,B0|B1,B1|B2,B2|B3,B3|B4,B4|B5,B5|B6,B6|B7,B7 => true | _,_ => false end) eqn:Heq.
  - destruct br, br'; simpl in Heq; try discriminate Heq; contradiction Hneq; reflexivity.
  - reflexivity.
Qed.

Lemma set_qnum_different_regtype_preserves_xreg : forall rrs r q xr,
  (forall xr', r <> Reg_X xr') ->
  xreg_result (set_qnum rrs r q) xr = xreg_result rrs xr.
Proof.
  intros rrs r q xr Hdiff.
  destruct r; unfold set_qnum; simpl.
  - exfalso. apply (Hdiff r). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma set_qnum_different_regtype_preserves_areg : forall rrs r q ar,
  (forall ar', r <> Reg_A ar') ->
  areg_result (set_qnum rrs r q) ar = areg_result rrs ar.
Proof.
  intros rrs r q ar Hdiff.
  destruct r; unfold set_qnum; simpl.
  - reflexivity.
  - exfalso. apply (Hdiff r). reflexivity.
  - reflexivity.
Qed.

Lemma set_qnum_different_regtype_preserves_breg : forall rrs r q br,
  (forall br', r <> Reg_B br') ->
  breg_result (set_qnum rrs r q) br = breg_result rrs br.
Proof.
  intros rrs r q br Hdiff.
  destruct r; unfold set_qnum; simpl.
  - reflexivity.
  - reflexivity.
  - exfalso. apply (Hdiff r). reflexivity.
Qed.

(** Issue preserves register result consistency *)
Lemma issue_preserves_reg_result_consistency : forall st instr,
  issue_precond st instr ->
  reg_result_consistency (sb_fu_status st) (sb_reg_result st) ->
  reg_result_consistency (sb_fu_status (issue_transition st instr))
                         (sb_reg_result (issue_transition st instr)).
Proof.
  intros st instr Hpre Hreg.
  unfold issue_transition, reg_result_consistency. simpl.
  intros fu.
  unfold update_fu.
  destruct (match fu_for_op (instr_op instr) (sb_fu_status st), fu with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq.
  - simpl.
    assert (Hfu_eq: fu = fu_for_op (instr_op instr) (sb_fu_status st)) by (destruct (fu_for_op (instr_op instr) (sb_fu_status st)), fu; auto; discriminate Heq).
    rewrite Hfu_eq.
    destruct (instr_dest instr) as [xr | ar | br]; unfold set_qnum; simpl; intro Hbusy.
    + destruct xr; simpl; reflexivity.
    + destruct ar; simpl; reflexivity.
    + destruct br; simpl; reflexivity.
  - specialize (Hreg fu).
    destruct (fu_fi (sb_fu_status st fu)) as [[xr'|ar'|br']|] eqn:Hfi; auto.
    + intro Hbusy.
      destruct (instr_dest instr) as [xr|ar|br] eqn:Hdest.
      * unfold set_qnum. simpl.
        destruct (match xr, xr' with X0,X0|X1,X1|X2,X2|X3,X3|X4,X4|X5,X5|X6,X6|X7,X7 => true | _,_ => false end) eqn:Heqxr.
        -- assert (Hxreq: xr = xr') by (destruct xr, xr'; try reflexivity; discriminate Heqxr).
           subst xr'.
           exfalso. eapply (issue_precond_no_waw_xreg st instr fu xr); try eassumption.
        -- apply Hreg; assumption.
      * apply Hreg; assumption.
      * apply Hreg; assumption.
    + intro Hbusy.
      destruct (instr_dest instr) as [xr|ar|br] eqn:Hdest.
      * apply Hreg; assumption.
      * unfold set_qnum. simpl.
        destruct (match ar, ar' with A0,A0|A1,A1|A2,A2|A3,A3|A4,A4|A5,A5|A6,A6|A7,A7 => true | _,_ => false end) eqn:Heqar.
        -- assert (Hareq: ar = ar') by (destruct ar, ar'; try reflexivity; discriminate Heqar).
           subst ar'.
           exfalso. eapply (issue_precond_no_waw_areg st instr fu ar); try eassumption.
        -- apply Hreg; assumption.
      * apply Hreg; assumption.
    + intro Hbusy.
      destruct (instr_dest instr) as [xr|ar|br] eqn:Hdest.
      * apply Hreg; assumption.
      * apply Hreg; assumption.
      * unfold set_qnum. simpl.
        destruct (match br, br' with B0,B0|B1,B1|B2,B2|B3,B3|B4,B4|B5,B5|B6,B6|B7,B7 => true | _,_ => false end) eqn:Heqbr.
        -- assert (Hbreq: br = br') by (destruct br, br'; try reflexivity; discriminate Heqbr).
           subst br'.
           exfalso. eapply (issue_precond_no_waw_breg st instr fu br); try eassumption.
        -- apply Hreg; assumption.
Qed.

(** Issue preserves register result validity *)
Lemma issue_preserves_reg_result_valid : forall st instr,
  reg_result_valid (sb_reg_result st) ->
  reg_result_valid (sb_reg_result (issue_transition st instr)).
Proof.
  intros st instr Hrvalid.
  unfold issue_transition, reg_result_valid. simpl.
  unfold set_qnum in *.
  destruct Hrvalid as [Hxvalid [Havalid Hbvalid]].
  split.
  - intros xr'. destruct (instr_dest instr) as [xr | ar | br]; simpl.
    + destruct (match xr, xr' with X0,X0|X1,X1|X2,X2|X3,X3|X4,X4|X5,X5|X6,X6|X7,X7 => true | _,_ => false end); auto; constructor.
    + apply Hxvalid.
    + apply Hxvalid.
  - split.
    + intros ar'. destruct (instr_dest instr) as [xr | ar | br]; simpl.
      * apply Havalid.
      * destruct (match ar, ar' with A0,A0|A1,A1|A2,A2|A3,A3|A4,A4|A5,A5|A6,A6|A7,A7 => true | _,_ => false end); auto; constructor.
      * apply Havalid.
    + intros br'. destruct (instr_dest instr) as [xr | ar | br]; simpl.
      * apply Hbvalid.
      * apply Hbvalid.
      * destruct (match br, br' with B0,B0|B1,B1|B2,B2|B3,B3|B4,B4|B5,B5|B6,B6|B7,B7 => true | _,_ => false end); auto; constructor.
Qed.

(** Issue preserves instruction memory *)
Lemma issue_preserves_imem : forall st instr,
  imem_immutable (sb_imem st) (sb_imem (issue_transition st instr)).
Proof.
  intros st instr. unfold imem_immutable, issue_transition, increment_cycle. simpl. reflexivity.
Qed.

(** Issue preserves PC validity *)
Lemma issue_preserves_pc : forall st instr,
  valid_pc (sb_pc st) ->
  valid_pc (sb_pc (issue_transition st instr)).
Proof.
  intros st instr Hpc.
  unfold issue_transition, increment_cycle. simpl. assumption.
Qed.

(** Issue preserves queue boundedness *)
Lemma issue_preserves_queue_bounded : forall st instr,
  queue_bounded st ->
  queue_bounded (issue_transition st instr).
Proof.
  intros st instr Hbound.
  unfold queue_bounded, issue_transition, increment_cycle. simpl.
  assumption.
Qed.

(** Issue preserves queue instructions validity *)
Lemma issue_preserves_queue_instrs_valid : forall st instr,
  queue_instrs_valid st ->
  queue_instrs_valid (issue_transition st instr).
Proof.
  intros st instr Hvalid.
  unfold queue_instrs_valid, issue_transition, increment_cycle. simpl.
  assumption.
Qed.

(** Main theorem: Issue preserves complete scoreboard invariant *)
Theorem issue_preserves_invariant : forall st instr,
  scoreboard_invariant st ->
  issue_precond st instr ->
  scoreboard_invariant (issue_transition st instr).
Proof.
  intros st instr Hinv Hpre.
  unfold scoreboard_invariant in *.
  destruct Hinv as [HB0 [Hfu_valid [Hbusy [Hrj [Hrk [Hcycles [Hreg [Hrvalid [Hpc [Hqueue [Hqvalid [Hmem Himem]]]]]]]]]]]].
  unfold issue_precond in Hpre. destruct Hpre as [Hno_conflict Hinstr_valid].
  split. eapply issue_preserves_b0_zero. apply HB0.
  split. eapply issue_preserves_fu_desc_valid. eapply reg_result_valid_qnums. apply (conj HB0 (conj Hfu_valid (conj Hbusy (conj Hrj (conj Hrk (conj Hcycles (conj Hreg (conj Hrvalid (conj Hpc (conj Hqueue (conj Hqvalid (conj Hmem Himem)))))))))))). apply Hfu_valid. unfold instr_valid in Hinstr_valid. apply Hinstr_valid.
  split. eapply issue_preserves_busy_consistency. apply Hbusy.
  split. eapply issue_preserves_rj_correct. apply Hrj.
  split. eapply issue_preserves_rk_correct. apply Hrk.
  split. eapply issue_preserves_cycles_bounded. apply Hcycles.
  split. eapply issue_preserves_reg_result_consistency. unfold issue_precond. split; assumption. apply Hreg.
  split. eapply issue_preserves_reg_result_valid. apply Hrvalid.
  split. eapply issue_preserves_pc. apply Hpc.
  split. eapply issue_preserves_queue_bounded. apply Hqueue.
  split. eapply issue_preserves_queue_instrs_valid. apply Hqvalid.
  split. unfold issue_transition. unfold increment_cycle. simpl.
    apply step_mem_subsystem_preserves_validity. assumption.
  unfold imem_valid. unfold issue_transition, increment_cycle. simpl. assumption.
Qed.

End IssueInvariantPreservation.

(** Read preserves B0 zero invariant *)
Lemma read_preserves_b0_zero : forall st fu,
  b0_zero_inv (sb_bregs st) ->
  b0_zero_inv (sb_bregs (read_transition fu st)).
Proof.
  intros st fu HB0.
  unfold read_transition. simpl.
  assumption.
Qed.

(** Read preserves FU descriptor validity *)
Lemma read_preserves_fu_desc_valid : forall st fu,
  (forall fu', fu_desc_valid (sb_fu_status st fu')) ->
  (forall fu', fu_desc_valid (sb_fu_status (read_transition fu st) fu')).
Proof.
  intros st fu Hvalid fu'.
  unfold read_transition.
  apply update_fu_preserves_validity.
  - assumption.
  - unfold fu_desc_valid. simpl. split; apply (Hvalid fu).
Qed.

(** Read preserves busy consistency *)
Lemma read_preserves_busy_consistency : forall st fu,
  (forall fu', busy_consistency (sb_fu_status st fu')) ->
  (forall fu', busy_consistency (sb_fu_status (read_transition fu st) fu')).
Proof.
  intros st fu Hbusy fu'.
  unfold read_transition. simpl.
  unfold busy_consistency, update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl; apply Hbusy.
Qed.

(** Read preserves Rj correctness *)
Lemma read_preserves_rj_correct : forall st fu,
  (forall fu', rj_correctness (sb_fu_status st fu')) ->
  (forall fu', rj_correctness (sb_fu_status (read_transition fu st) fu')).
Proof.
  intros st fu Hrj fu'.
  unfold read_transition. simpl.
  unfold rj_correctness, update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl; apply Hrj.
Qed.

(** Read preserves Rk correctness *)
Lemma read_preserves_rk_correct : forall st fu,
  (forall fu', rk_correctness (sb_fu_status st fu')) ->
  (forall fu', rk_correctness (sb_fu_status (read_transition fu st) fu')).
Proof.
  intros st fu Hrk fu'.
  unfold read_transition. simpl.
  unfold rk_correctness, update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl; apply Hrk.
Qed.

(** Read preserves cycles bounded *)
Lemma read_preserves_cycles_bounded : forall st fu,
  (forall fu', cycles_bounded (sb_fu_status st fu')) ->
  (forall fu', cycles_bounded (sb_fu_status (read_transition fu st) fu')).
Proof.
  intros st fu Hcycles fu'.
  unfold read_transition, cycles_bounded. simpl.
  unfold update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl; apply Hcycles.
Qed.

(** Read preserves register result consistency *)
Lemma read_preserves_reg_result_consistency : forall st fu,
  reg_result_consistency (sb_fu_status st) (sb_reg_result st) ->
  reg_result_consistency (sb_fu_status (read_transition fu st))
                         (sb_reg_result (read_transition fu st)).
Proof.
  intros st fu Hreg fu'.
  unfold read_transition. simpl.
  unfold reg_result_consistency in Hreg.
  specialize (Hreg fu').
  unfold update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl.
  - assert (Hfu_eq: fu = fu') by (destruct fu, fu'; auto; discriminate Heq).
    subst fu'. exact Hreg.
  - exact Hreg.
Qed.

(** Read preserves register result validity *)
Lemma read_preserves_reg_result_valid : forall st fu,
  reg_result_valid (sb_reg_result st) ->
  reg_result_valid (sb_reg_result (read_transition fu st)).
Proof.
  intros st fu Hrvalid.
  unfold read_transition. simpl.
  assumption.
Qed.

(** Read preserves instruction memory *)
Lemma read_preserves_imem : forall st fu,
  imem_immutable (sb_imem st) (sb_imem (read_transition fu st)).
Proof.
  intros st fu. unfold imem_immutable, read_transition, increment_cycle. simpl. reflexivity.
Qed.

(** Read preserves PC validity *)
Lemma read_preserves_pc : forall st fu,
  valid_pc (sb_pc st) ->
  valid_pc (sb_pc (read_transition fu st)).
Proof.
  intros st fu Hpc.
  unfold read_transition, increment_cycle. simpl. assumption.
Qed.

(** Read preserves queue boundedness *)
Lemma read_preserves_queue_bounded : forall st fu,
  queue_bounded st ->
  queue_bounded (read_transition fu st).
Proof.
  intros st fu Hbound.
  unfold queue_bounded, read_transition, increment_cycle. simpl.
  assumption.
Qed.

(** Read preserves queue instructions validity *)
Lemma read_preserves_queue_instrs_valid : forall st fu,
  queue_instrs_valid st ->
  queue_instrs_valid (read_transition fu st).
Proof.
  intros st fu Hvalid.
  unfold queue_instrs_valid, read_transition, increment_cycle. simpl.
  assumption.
Qed.

Theorem read_preserves_invariant : forall st fu,
  scoreboard_invariant st ->
  read_precond fu st ->
  scoreboard_invariant (read_transition fu st).
Proof.
  intros st fu Hinv Hpre.
  unfold scoreboard_invariant in *.
  destruct Hinv as [HB0 [Hfu_valid [Hbusy [Hrj [Hrk [Hcycles [Hreg [Hrvalid [Hpc [Hqueue [Hqvalid [Hmem Himem]]]]]]]]]]]].
  split. eapply read_preserves_b0_zero. apply HB0.
  split. eapply read_preserves_fu_desc_valid. apply Hfu_valid.
  split. eapply read_preserves_busy_consistency. apply Hbusy.
  split. eapply read_preserves_rj_correct. apply Hrj.
  split. eapply read_preserves_rk_correct. apply Hrk.
  split. eapply read_preserves_cycles_bounded. apply Hcycles.
  split. eapply read_preserves_reg_result_consistency. apply Hreg.
  split. eapply read_preserves_reg_result_valid. apply Hrvalid.
  split. eapply read_preserves_pc. apply Hpc.
  split. eapply read_preserves_queue_bounded. apply Hqueue.
  split. eapply read_preserves_queue_instrs_valid. apply Hqvalid.
  split. unfold read_transition. unfold increment_cycle. simpl.
    apply step_mem_subsystem_preserves_validity. assumption.
  unfold imem_valid. unfold read_transition, increment_cycle. simpl. assumption.
Qed.

(** Execute preserves B0 zero invariant *)
Lemma execute_preserves_b0_zero : forall st fu,
  b0_zero_inv (sb_bregs st) ->
  b0_zero_inv (sb_bregs (execute_step fu st)).
Proof.
  intros st fu HB0.
  unfold execute_step.
  destruct (fu_busy (sb_fu_status st fu)); simpl; try assumption.
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0); simpl; assumption.
Qed.

(** Execute preserves FU descriptor validity *)
Lemma execute_preserves_fu_desc_valid : forall st fu,
  (forall fu', fu_desc_valid (sb_fu_status st fu')) ->
  (forall fu', fu_desc_valid (sb_fu_status (execute_step fu st) fu')).
Proof.
  intros st fu Hvalid fu'.
  unfold execute_step.
  destruct (fu_busy (sb_fu_status st fu)) eqn:Hbusy; simpl; try apply Hvalid.
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0) eqn:Hcyc; simpl; try apply Hvalid.
  apply update_fu_preserves_validity.
  - assumption.
  - unfold fu_desc_valid. simpl. split; apply (Hvalid fu).
Qed.

(** Execute preserves busy consistency *)
Lemma execute_preserves_busy_consistency : forall st fu,
  (forall fu', busy_consistency (sb_fu_status st fu')) ->
  (forall fu', busy_consistency (sb_fu_status (execute_step fu st) fu')).
Proof.
  intros st fu Hbusy fu'.
  unfold execute_step.
  destruct (fu_busy (sb_fu_status st fu)) eqn:Hfubusy; simpl; try apply Hbusy.
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0) eqn:Hcyc; simpl; try apply Hbusy.
  unfold busy_consistency, update_fu.
  specialize (Hbusy fu').
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl.
  - assert (Hfu_eq: fu = fu') by (destruct fu, fu'; auto; discriminate Heq).
    subst fu'. unfold busy_consistency in Hbusy. rewrite Hfubusy in Hbusy. intro. discriminate.
  - apply Hbusy.
Qed.

(** Execute preserves Rj correctness *)
Lemma execute_preserves_rj_correct : forall st fu,
  (forall fu', rj_correctness (sb_fu_status st fu')) ->
  (forall fu', rj_correctness (sb_fu_status (execute_step fu st) fu')).
Proof.
  intros st fu Hrj fu'.
  unfold execute_step.
  destruct (fu_busy (sb_fu_status st fu)) eqn:Hfubusy; simpl; try apply Hrj.
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0) eqn:Hcyc; simpl; try apply Hrj.
  unfold rj_correctness, update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl; apply Hrj.
Qed.

(** Execute preserves Rk correctness *)
Lemma execute_preserves_rk_correct : forall st fu,
  (forall fu', rk_correctness (sb_fu_status st fu')) ->
  (forall fu', rk_correctness (sb_fu_status (execute_step fu st) fu')).
Proof.
  intros st fu Hrk fu'.
  unfold execute_step.
  destruct (fu_busy (sb_fu_status st fu)) eqn:Hfubusy; simpl; try apply Hrk.
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0) eqn:Hcyc; simpl; try apply Hrk.
  unfold rk_correctness, update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl; apply Hrk.
Qed.

(** Execute preserves cycles bounded *)
Lemma execute_preserves_cycles_bounded : forall st fu,
  (forall fu', cycles_bounded (sb_fu_status st fu')) ->
  (forall fu', cycles_bounded (sb_fu_status (execute_step fu st) fu')).
Proof.
  intros st fu Hcycles fu'.
  unfold execute_step, cycles_bounded.
  destruct (fu_busy (sb_fu_status st fu)) eqn:Hbusy; simpl; try apply Hcycles.
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0) eqn:Hcyc; simpl; try apply Hcycles.
  unfold update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl.
  - assert (Hfu_eq: fu = fu') by (destruct fu, fu'; auto; discriminate Heq).
    subst fu'.
    intros _. unfold cycles_bounded in Hcycles. specialize (Hcycles fu).
    rewrite Hbusy in Hcycles. specialize (Hcycles eq_refl).
    destruct (fu_op (sb_fu_status st fu)) as [op|]; simpl in *; auto.
    apply Nat.eqb_neq in Hcyc. lia.
  - apply Hcycles.
Qed.

(** Execute preserves register result consistency *)
Lemma execute_preserves_reg_result_consistency : forall st fu,
  reg_result_consistency (sb_fu_status st) (sb_reg_result st) ->
  reg_result_consistency (sb_fu_status (execute_step fu st))
                         (sb_reg_result (execute_step fu st)).
Proof.
  intros st fu Hreg fu'.
  unfold execute_step.
  destruct (fu_busy (sb_fu_status st fu)) eqn:Hfubusy; simpl; try apply Hreg.
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0) eqn:Hcyc; simpl; try apply Hreg.
  unfold reg_result_consistency in Hreg.
  specialize (Hreg fu').
  unfold update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl.
  - assert (Hfu_eq: fu = fu') by (destruct fu, fu'; auto; discriminate Heq).
    subst fu'. rewrite Hfubusy in Hreg. exact Hreg.
  - exact Hreg.
Qed.

(** Execute preserves register result validity *)
Lemma execute_preserves_reg_result_valid : forall st fu,
  reg_result_valid (sb_reg_result st) ->
  reg_result_valid (sb_reg_result (execute_step fu st)).
Proof.
  intros st fu Hrvalid.
  unfold execute_step.
  destruct (fu_busy (sb_fu_status st fu)); simpl; try assumption.
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0); simpl; assumption.
Qed.

(** Execute preserves instruction memory *)
Lemma execute_preserves_imem : forall st fu,
  imem_immutable (sb_imem st) (sb_imem (execute_step fu st)).
Proof.
  intros st fu. unfold imem_immutable, execute_step.
  destruct (fu_busy (sb_fu_status st fu)); [|reflexivity].
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0); [reflexivity|].
  unfold increment_cycle. simpl. reflexivity.
Qed.

(** Execute preserves PC validity *)
Lemma execute_preserves_pc : forall st fu,
  valid_pc (sb_pc st) ->
  valid_pc (sb_pc (execute_step fu st)).
Proof.
  intros st fu Hpc.
  unfold execute_step.
  destruct (fu_busy (sb_fu_status st fu)); [|assumption].
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0); [assumption|].
  unfold increment_cycle. simpl. assumption.
Qed.

(** Execute preserves queue boundedness *)
Lemma execute_preserves_queue_bounded : forall st fu,
  queue_bounded st ->
  queue_bounded (execute_step fu st).
Proof.
  intros st fu Hbound.
  unfold queue_bounded, execute_step.
  destruct (fu_busy (sb_fu_status st fu)); [|assumption].
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0); [assumption|].
  unfold increment_cycle. simpl. assumption.
Qed.

(** Execute preserves queue instructions validity *)
Lemma execute_preserves_queue_instrs_valid : forall st fu,
  queue_instrs_valid st ->
  queue_instrs_valid (execute_step fu st).
Proof.
  intros st fu Hvalid.
  unfold queue_instrs_valid, execute_step.
  destruct (fu_busy (sb_fu_status st fu)); [|assumption].
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0); [assumption|].
  unfold increment_cycle. simpl. assumption.
Qed.

Theorem execute_preserves_invariant : forall st fu,
  scoreboard_invariant st ->
  scoreboard_invariant (execute_step fu st).
Proof.
  intros st fu Hinv.
  unfold scoreboard_invariant in *.
  destruct Hinv as [HB0 [Hfu_valid [Hbusy [Hrj [Hrk [Hcycles [Hreg [Hrvalid [Hpc [Hqueue [Hqvalid [Hmem Himem]]]]]]]]]]]].
  split. eapply execute_preserves_b0_zero. apply HB0.
  split. eapply execute_preserves_fu_desc_valid. apply Hfu_valid.
  split. eapply execute_preserves_busy_consistency. apply Hbusy.
  split. eapply execute_preserves_rj_correct. apply Hrj.
  split. eapply execute_preserves_rk_correct. apply Hrk.
  split. eapply execute_preserves_cycles_bounded. apply Hcycles.
  split. eapply execute_preserves_reg_result_consistency. apply Hreg.
  split. eapply execute_preserves_reg_result_valid. apply Hrvalid.
  split. eapply execute_preserves_pc. apply Hpc.
  split. eapply execute_preserves_queue_bounded. apply Hqueue.
  split. eapply execute_preserves_queue_instrs_valid. apply Hqvalid.
  split.
  - unfold execute_step. destruct (fu_busy (sb_fu_status st fu)).
    + destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0).
      * assumption.
      * unfold increment_cycle. simpl. apply step_mem_subsystem_preserves_validity. assumption.
    + assumption.
  - unfold imem_valid, execute_step. destruct (fu_busy (sb_fu_status st fu)); [|assumption].
    destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0); [assumption|].
    unfold increment_cycle. simpl. assumption.
Qed.

(** Helper: write_reg preserves B0 zero for X and A registers *)
Lemma write_reg_preserves_b0_xreg : forall st xr v,
  b0_zero_inv (sb_bregs st) ->
  b0_zero_inv (sb_bregs (write_reg st (Reg_X xr) v)).
Proof.
  intros st xr v HB0.
  unfold write_reg, b0_zero_inv. simpl. assumption.
Qed.

Lemma write_reg_preserves_b0_areg : forall st ar v,
  b0_zero_inv (sb_bregs st) ->
  b0_zero_inv (sb_bregs (write_reg st (Reg_A ar) v)).
Proof.
  intros st ar v HB0.
  unfold write_reg, b0_zero_inv. simpl. assumption.
Qed.

(** Helper: write_reg to B register preserves B0=0 due to hardware enforcement *)
Lemma write_reg_preserves_b0_breg : forall st br v,
  b0_zero_inv (sb_bregs st) ->
  b0_zero_inv (sb_bregs (write_reg st (Reg_B br) v)).
Proof.
  intros st br v HB0.
  unfold write_reg, b0_zero_inv. simpl. reflexivity.
Qed.

(** Writeback preserves B0 zero invariant *)
Lemma writeback_preserves_b0_zero : forall st fu,
  b0_zero_inv (sb_bregs st) ->
  b0_zero_inv (sb_bregs (writeback_transition fu st)).
Proof.
  intros st fu HB0.
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi.
  - destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
    + destruct dest as [xr|ar|br].
      * apply write_reg_preserves_b0_xreg. assumption.
      * apply write_reg_preserves_b0_areg. assumption.
      * apply write_reg_preserves_b0_breg. assumption.
    + unfold b0_zero_inv in *. simpl. assumption.
  - unfold b0_zero_inv in *. simpl. assumption.
Qed.

(** Broadcast preserves FU descriptor validity *)
Lemma broadcast_preserves_fu_desc_valid : forall fus fu,
  (forall fu', fu_desc_valid (fus fu')) ->
  (forall fu', fu_desc_valid (broadcast_writeback fus fu fu')).
Proof.
  intros fus fu Hvalid fu'.
  unfold broadcast_writeback.
  destruct (fu_busy (fus fu')) eqn:Hbusy; [|apply Hvalid].
  unfold fu_desc_valid. simpl.
  destruct (Hvalid fu') as [Hqj [Hqk Hbranch]].
  split. destruct (qnum_eq (fu_qj (fus fu')) (QFU fu)); [constructor | assumption].
  split. destruct (qnum_eq (fu_qk (fus fu')) (QFU fu)); [constructor | assumption].
  assumption.
Qed.

(** Writeback preserves FU descriptor validity *)
Lemma writeback_preserves_fu_desc_valid : forall st fu,
  (forall fu', fu_desc_valid (sb_fu_status st fu')) ->
  (forall fu', fu_desc_valid (sb_fu_status (writeback_transition fu st) fu')).
Proof.
  intros st fu Hvalid fu'.
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi; try apply Hvalid.
  destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
  - unfold write_reg. destruct dest as [xr|ar|br]; simpl.
    + apply update_fu_preserves_validity.
      * apply broadcast_preserves_fu_desc_valid. assumption.
      * unfold fu_desc_valid, init_fu_desc; simpl; split; [constructor | split; [constructor | intros target H; discriminate]].
    + apply update_fu_preserves_validity.
      * apply broadcast_preserves_fu_desc_valid. assumption.
      * unfold fu_desc_valid, init_fu_desc; simpl; split; [constructor | split; [constructor | intros target H; discriminate]].
    + apply update_fu_preserves_validity.
      * apply broadcast_preserves_fu_desc_valid. assumption.
      * unfold fu_desc_valid, init_fu_desc; simpl; split; [constructor | split; [constructor | intros target H; discriminate]].
  - simpl. apply update_fu_preserves_validity.
    + apply broadcast_preserves_fu_desc_valid. assumption.
    + unfold fu_desc_valid, init_fu_desc; simpl; split; [constructor | split; [constructor | intros target H; discriminate]].
Qed.

(** Broadcast preserves busy consistency *)
Lemma broadcast_preserves_busy_consistency : forall fus fu,
  (forall fu', busy_consistency (fus fu')) ->
  (forall fu', busy_consistency (broadcast_writeback fus fu fu')).
Proof.
  intros fus fu Hbusy fu'.
  unfold broadcast_writeback.
  destruct (fu_busy (fus fu')) eqn:Hfubusy; [|apply Hbusy].
  unfold busy_consistency. simpl. intro H. discriminate.
Qed.

(** Writeback preserves busy consistency *)
Lemma writeback_preserves_busy_consistency : forall st fu,
  (forall fu', busy_consistency (sb_fu_status st fu')) ->
  (forall fu', busy_consistency (sb_fu_status (writeback_transition fu st) fu')).
Proof.
  intros st fu Hbusy fu'.
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi; try apply Hbusy.
  destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
  - unfold write_reg. destruct dest as [xr|ar|br]; simpl;
    unfold busy_consistency, update_fu;
    destruct (match fu, fu' with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
      | _, _ => false
    end) eqn:Heq; simpl; try (apply broadcast_preserves_busy_consistency; assumption);
    unfold busy_consistency, init_fu_desc; simpl; intros _; repeat split; reflexivity.
  - simpl. unfold busy_consistency, update_fu.
    destruct (match fu, fu' with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
      | _, _ => false
    end) eqn:Heq; simpl; try (apply broadcast_preserves_busy_consistency; assumption);
    unfold busy_consistency, init_fu_desc; simpl; intros _; repeat split; reflexivity.
Qed.

(** Broadcast preserves Rj correctness *)
Lemma broadcast_preserves_rj_correct : forall fus fu,
  (forall fu', rj_correctness (fus fu')) ->
  (forall fu', rj_correctness (broadcast_writeback fus fu fu')).
Proof.
  intros fus fu Hrj fu'.
  unfold broadcast_writeback.
  destruct (fu_busy (fus fu')) eqn:Hbusy; [|apply Hrj].
  unfold rj_correctness. simpl.
  destruct (qnum_eq (fu_qj (fus fu')) (QFU fu)) eqn:Hqj.
  - split; intros; reflexivity.
  - apply Hrj.
Qed.

(** Writeback preserves Rj correctness *)
Lemma writeback_preserves_rj_correct : forall st fu,
  (forall fu', rj_correctness (sb_fu_status st fu')) ->
  (forall fu', rj_correctness (sb_fu_status (writeback_transition fu st) fu')).
Proof.
  intros st fu Hrj fu'.
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi; try apply Hrj.
  destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
  - unfold write_reg. destruct dest as [xr|ar|br]; simpl;
    unfold rj_correctness, update_fu;
    destruct (match fu, fu' with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
      | _, _ => false
    end) eqn:Heq; simpl; try (apply broadcast_preserves_rj_correct; assumption);
    unfold rj_correctness, init_fu_desc; simpl; split; intros; reflexivity.
  - simpl. unfold rj_correctness, update_fu.
    destruct (match fu, fu' with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
      | _, _ => false
    end) eqn:Heq; simpl; try (apply broadcast_preserves_rj_correct; assumption);
    unfold rj_correctness, init_fu_desc; simpl; split; intros; reflexivity.
Qed.

(** Broadcast preserves Rk correctness *)
Lemma broadcast_preserves_rk_correct : forall fus fu,
  (forall fu', rk_correctness (fus fu')) ->
  (forall fu', rk_correctness (broadcast_writeback fus fu fu')).
Proof.
  intros fus fu Hrk fu'.
  unfold broadcast_writeback.
  destruct (fu_busy (fus fu')) eqn:Hbusy; [|apply Hrk].
  unfold rk_correctness. simpl.
  destruct (qnum_eq (fu_qk (fus fu')) (QFU fu)) eqn:Hqk.
  - split; intros; reflexivity.
  - apply Hrk.
Qed.

(** Writeback preserves Rk correctness *)
Lemma writeback_preserves_rk_correct : forall st fu,
  (forall fu', rk_correctness (sb_fu_status st fu')) ->
  (forall fu', rk_correctness (sb_fu_status (writeback_transition fu st) fu')).
Proof.
  intros st fu Hrk fu'.
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi; try apply Hrk.
  destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
  - unfold write_reg. destruct dest as [xr|ar|br]; simpl;
    unfold rk_correctness, update_fu;
    destruct (match fu, fu' with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
      | _, _ => false
    end) eqn:Heq; simpl; try (apply broadcast_preserves_rk_correct; assumption);
    unfold rk_correctness, init_fu_desc; simpl; split; intros; reflexivity.
  - simpl. unfold rk_correctness, update_fu.
    destruct (match fu, fu' with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
      | _, _ => false
    end) eqn:Heq; simpl; try (apply broadcast_preserves_rk_correct; assumption);
    unfold rk_correctness, init_fu_desc; simpl; split; intros; reflexivity.
Qed.

(** Broadcast preserves cycles bounded *)
Lemma broadcast_preserves_cycles_bounded : forall fus fu,
  (forall fu', cycles_bounded (fus fu')) ->
  (forall fu', cycles_bounded (broadcast_writeback fus fu fu')).
Proof.
  intros fus fu Hcycles fu'.
  unfold broadcast_writeback.
  destruct (fu_busy (fus fu')) eqn:Hbusy; [|apply Hcycles].
  unfold cycles_bounded. simpl. intro H. specialize (Hcycles fu').
  unfold cycles_bounded in Hcycles. apply Hcycles. assumption.
Qed.

(** Writeback preserves cycles bounded *)
Lemma writeback_preserves_cycles_bounded : forall st fu,
  (forall fu', cycles_bounded (sb_fu_status st fu')) ->
  (forall fu', cycles_bounded (sb_fu_status (writeback_transition fu st) fu')).
Proof.
  intros st fu Hcycles fu'.
  unfold writeback_transition, cycles_bounded.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi; try apply Hcycles.
  destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
  - unfold write_reg. destruct dest as [xr|ar|br]; simpl;
    unfold update_fu;
    destruct (match fu, fu' with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
      | _, _ => false
    end) eqn:Heq; simpl; try (apply broadcast_preserves_cycles_bounded; assumption);
    unfold cycles_bounded, init_fu_desc; simpl; intros H; discriminate.
  - simpl. unfold update_fu.
    destruct (match fu, fu' with
      | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
      | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
      | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
      | _, _ => false
    end) eqn:Heq; simpl; try (apply broadcast_preserves_cycles_bounded; assumption);
    unfold cycles_bounded, init_fu_desc; simpl; intros H; discriminate.
Qed.

(** Helper: setting a register to QNone preserves validity for other registers *)
Lemma set_qnum_none_preserves_validity_xreg : forall rrs xr xr',
  qnum_valid (xreg_result rrs xr') ->
  qnum_valid (xreg_result (set_qnum rrs (Reg_X xr) QNone) xr').
Proof.
  intros rrs xr xr' Hvalid.
  unfold set_qnum. simpl.
  destruct (match xr, xr' with X0,X0|X1,X1|X2,X2|X3,X3|X4,X4|X5,X5|X6,X6|X7,X7 => true | _,_ => false end).
  - constructor.
  - assumption.
Qed.

Lemma set_qnum_none_preserves_validity_areg : forall rrs ar ar',
  qnum_valid (areg_result rrs ar') ->
  qnum_valid (areg_result (set_qnum rrs (Reg_A ar) QNone) ar').
Proof.
  intros rrs ar ar' Hvalid.
  unfold set_qnum. simpl.
  destruct (match ar, ar' with A0,A0|A1,A1|A2,A2|A3,A3|A4,A4|A5,A5|A6,A6|A7,A7 => true | _,_ => false end).
  - constructor.
  - assumption.
Qed.

Lemma set_qnum_none_preserves_validity_breg : forall rrs br br',
  qnum_valid (breg_result rrs br') ->
  qnum_valid (breg_result (set_qnum rrs (Reg_B br) QNone) br').
Proof.
  intros rrs br br' Hvalid.
  unfold set_qnum. simpl.
  destruct (match br, br' with B0,B0|B1,B1|B2,B2|B3,B3|B4,B4|B5,B5|B6,B6|B7,B7 => true | _,_ => false end).
  - constructor.
  - assumption.
Qed.

(** Helper: write_reg does not change fu_status *)
Lemma write_reg_preserves_fu_status : forall st r v,
  sb_fu_status (write_reg st r v) = sb_fu_status st.
Proof.
  intros st r v.
  destruct r; unfold write_reg; simpl; reflexivity.
Qed.

(** Helper: write_reg does not change reg_result *)
Lemma write_reg_preserves_reg_result : forall st r v,
  sb_reg_result (write_reg st r v) = sb_reg_result st.
Proof.
  intros st r v.
  destruct r; unfold write_reg; simpl; reflexivity.
Qed.

(** Helper: After setting qnum to QNone and resetting FU, reg_result_consistency holds
    Key insight: When fu ≠ fu' (Heq = false), the destination of fu' doesn't overlap with dest
    because reg_result_consistency ensures each register is claimed by at most one FU. *)
Lemma reset_fu_preserves_reg_result_consistency : forall fus rrs fu dest,
  reg_result_consistency fus rrs ->
  fu_fi (fus fu) = Some dest ->
  fu_busy (fus fu) = true ->
  reg_result_consistency
    (update_fu fus fu init_fu_desc)
    (set_qnum rrs dest QNone).
Proof.
  intros fus rrs fu dest Hreg Hfi Hbusy fu'.
  unfold update_fu.
  destruct (match fu, fu' with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq.
  - unfold init_fu_desc. simpl. auto.
  - unfold reg_result_consistency in *.
    assert (Hreg_fu: match dest with
                     | Reg_X xr => xreg_result rrs xr = QFU fu
                     | Reg_A ar => areg_result rrs ar = QFU fu
                     | Reg_B br => breg_result rrs br = QFU fu
                     end).
    { destruct dest as [xr|ar|br]; specialize (Hreg fu); rewrite Hfi in Hreg; apply Hreg; assumption. }
    clear Hfi.
    specialize (Hreg fu').
    destruct (fu_fi (fus fu')) as [[xr'|ar'|br']|] eqn:Hfi'; auto.
    + intro Hbusy'.
      assert (Hreg_fu': xreg_result rrs xr' = QFU fu') by (apply Hreg; assumption).
      destruct dest as [xr|ar|br]; unfold set_qnum; simpl.
      * destruct (match xr, xr' with X0,X0|X1,X1|X2,X2|X3,X3|X4,X4|X5,X5|X6,X6|X7,X7 => true | _,_ => false end) eqn:Hxeq.
        -- assert (xr = xr') by (destruct xr, xr'; try reflexivity; discriminate Hxeq).
           subst xr'.
           rewrite Hreg_fu in Hreg_fu'.
           assert (fu = fu') by congruence.
           subst fu'.
           destruct fu; discriminate Heq.
        -- assumption.
      * assumption.
      * assumption.
    + intro Hbusy'.
      assert (Hreg_fu': areg_result rrs ar' = QFU fu') by (apply Hreg; assumption).
      destruct dest as [xr|ar|br]; unfold set_qnum; simpl.
      * assumption.
      * destruct (match ar, ar' with A0,A0|A1,A1|A2,A2|A3,A3|A4,A4|A5,A5|A6,A6|A7,A7 => true | _,_ => false end) eqn:Haeq.
        -- assert (ar = ar') by (destruct ar, ar'; try reflexivity; discriminate Haeq).
           subst ar'.
           rewrite Hreg_fu in Hreg_fu'.
           assert (fu = fu') by congruence.
           subst fu'.
           destruct fu; discriminate Heq.
        -- assumption.
      * assumption.
    + intro Hbusy'.
      assert (Hreg_fu': breg_result rrs br' = QFU fu') by (apply Hreg; assumption).
      destruct dest as [xr|ar|br]; unfold set_qnum; simpl.
      * assumption.
      * assumption.
      * destruct (match br, br' with B0,B0|B1,B1|B2,B2|B3,B3|B4,B4|B5,B5|B6,B6|B7,B7 => true | _,_ => false end) eqn:Hbeq.
        -- assert (br = br') by (destruct br, br'; try reflexivity; discriminate Hbeq).
           subst br'.
           rewrite Hreg_fu in Hreg_fu'.
           assert (fu = fu') by congruence.
           subst fu'.
           destruct fu; discriminate Heq.
        -- assumption.
Qed.

(** Broadcast preserves fu_fi for the completing FU *)
Lemma broadcast_preserves_fi : forall fus fu,
  fu_fi (broadcast_writeback fus fu fu) = fu_fi (fus fu).
Proof.
  intros. unfold broadcast_writeback.
  destruct (fu_busy (fus fu)) eqn:H; reflexivity.
Qed.

(** Broadcast preserves fu_busy for the completing FU *)
Lemma broadcast_preserves_busy_self : forall fus fu,
  fu_busy (broadcast_writeback fus fu fu) = fu_busy (fus fu).
Proof.
  intros. unfold broadcast_writeback. simpl.
  destruct (fu_busy (fus fu)) eqn:H.
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

(** Broadcast preserves register result consistency *)
Lemma broadcast_preserves_reg_result_consistency : forall fus rrs fu,
  reg_result_consistency fus rrs ->
  reg_result_consistency (broadcast_writeback fus fu) rrs.
Proof.
  intros fus rrs fu Hreg fu'.
  specialize (Hreg fu').
  unfold broadcast_writeback.
  destruct (fu_busy (fus fu')) eqn:Hbusy.
  - exact Hreg.
  - destruct (fu_fi (fus fu')) as [[xr|ar|br]|] eqn:Hfi; auto.
    + intro H. rewrite Hbusy in H. discriminate.
    + intro H. rewrite Hbusy in H. discriminate.
    + intro H. rewrite Hbusy in H. discriminate.
Qed.

(** Writeback preserves register result consistency *)
Lemma writeback_preserves_reg_result_consistency : forall st fu,
  writeback_precond fu st ->
  reg_result_consistency (sb_fu_status st) (sb_reg_result st) ->
  reg_result_consistency (sb_fu_status (writeback_transition fu st))
                         (sb_reg_result (writeback_transition fu st)).
Proof.
  intros st fu Hpre Hreg.
  unfold writeback_precond in Hpre.
  destruct Hpre as [Hbusy [Hcyc Hdest]].
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi.
  - destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
    + rewrite write_reg_preserves_fu_status.
      rewrite write_reg_preserves_reg_result.
      apply reset_fu_preserves_reg_result_consistency.
      * apply broadcast_preserves_reg_result_consistency. assumption.
      * rewrite broadcast_preserves_fi. assumption.
      * rewrite broadcast_preserves_busy_self. assumption.
    + apply reset_fu_preserves_reg_result_consistency.
      * apply broadcast_preserves_reg_result_consistency. assumption.
      * rewrite broadcast_preserves_fi. assumption.
      * rewrite broadcast_preserves_busy_self. assumption.
  - exfalso. exact Hdest.
Qed.

(** Writeback preserves register result validity *)
Lemma writeback_preserves_reg_result_valid : forall st fu,
  reg_result_valid (sb_reg_result st) ->
  reg_result_valid (sb_reg_result (writeback_transition fu st)).
Proof.
  intros st fu Hrvalid.
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi; try assumption.
  destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
  - unfold write_reg, reg_result_valid in *.
    destruct Hrvalid as [Hxvalid [Havalid Hbvalid]].
    destruct dest as [xr|ar|br]; simpl; split.
    + intros xr'. apply set_qnum_none_preserves_validity_xreg. apply Hxvalid.
    + split.
      * intros ar'. apply Havalid.
      * intros br'. apply Hbvalid.
    + intros xr'. apply Hxvalid.
    + split.
      * intros ar'. apply set_qnum_none_preserves_validity_areg. apply Havalid.
      * intros br'. apply Hbvalid.
    + intros xr'. apply Hxvalid.
    + split.
      * intros ar'. apply Havalid.
      * intros br'. apply set_qnum_none_preserves_validity_breg. apply Hbvalid.
  - simpl. unfold reg_result_valid in *.
    destruct Hrvalid as [Hxvalid [Havalid Hbvalid]].
    destruct dest as [xr|ar|br]; split.
    + intros xr'. apply set_qnum_none_preserves_validity_xreg. apply Hxvalid.
    + split.
      * intros ar'. apply Havalid.
      * intros br'. apply Hbvalid.
    + intros xr'. apply Hxvalid.
    + split.
      * intros ar'. apply set_qnum_none_preserves_validity_areg. apply Havalid.
      * intros br'. apply Hbvalid.
    + intros xr'. apply Hxvalid.
    + split.
      * intros ar'. apply Havalid.
      * intros br'. apply set_qnum_none_preserves_validity_breg. apply Hbvalid.
Qed.

(** write_reg preserves instruction memory *)
Lemma write_reg_preserves_imem : forall st r v,
  imem_immutable (sb_imem st) (sb_imem (write_reg st r v)).
Proof.
  intros st r v. unfold imem_immutable, write_reg. destruct r; simpl; reflexivity.
Qed.

(** write_reg preserves PC *)
Lemma write_reg_preserves_pc : forall st r v,
  valid_pc (sb_pc st) ->
  valid_pc (sb_pc (write_reg st r v)).
Proof.
  intros st r v Hpc.
  unfold write_reg. destruct r; simpl; assumption.
Qed.

(** Writeback preserves instruction memory *)
Lemma writeback_preserves_imem : forall st fu,
  imem_immutable (sb_imem st) (sb_imem (writeback_transition fu st)).
Proof.
  intros st fu. unfold imem_immutable, writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)); [|reflexivity].
  destruct (fu_result (sb_fu_status st fu)).
  - unfold increment_cycle. simpl. apply write_reg_preserves_imem.
  - unfold increment_cycle. simpl. reflexivity.
Qed.

(** Writeback preserves PC validity *)
Lemma writeback_preserves_pc : forall st fu,
  fu_desc_valid (sb_fu_status st fu) ->
  valid_pc (sb_pc st) ->
  valid_pc (sb_pc (writeback_transition fu st)).
Proof.
  intros st fu Hvalid Hpc.
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [r|] eqn:Hfi; [|assumption].
  assert (Hwr_pc: forall v, sb_pc (write_reg st r v) = sb_pc st) by (intro; unfold write_reg; destruct r; reflexivity).
  destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
  - unfold increment_cycle, fu_desc_valid in *. destruct Hvalid as [_ [_ Hbranch_valid]]. simpl.
    destruct (fu_branch_target (sb_fu_status st fu)) as [target|] eqn:Htarget; simpl; rewrite Hwr_pc.
    + destruct (v =? 0); assumption || (apply Hbranch_valid; reflexivity).
    + assumption.
  - unfold increment_cycle. simpl.
    destruct (fu_branch_target (sb_fu_status st fu)); simpl; assumption.
Qed.

(** Writeback preserves queue boundedness *)
Lemma writeback_preserves_queue_bounded : forall st fu,
  queue_bounded st ->
  queue_bounded (writeback_transition fu st).
Proof.
  intros st fu Hbound.
  unfold queue_bounded, writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)); [|assumption].
  destruct (fu_result (sb_fu_status st fu)).
  - unfold increment_cycle, write_reg. destruct r; simpl; assumption.
  - unfold increment_cycle. simpl. assumption.
Qed.

(** Writeback preserves queue instructions validity *)
Lemma writeback_preserves_queue_instrs_valid : forall st fu,
  queue_instrs_valid st ->
  queue_instrs_valid (writeback_transition fu st).
Proof.
  intros st fu Hvalid.
  unfold queue_instrs_valid, writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)); [|assumption].
  destruct (fu_result (sb_fu_status st fu)).
  - unfold increment_cycle, write_reg. destruct r; simpl; assumption.
  - unfold increment_cycle. simpl. assumption.
Qed.

(** Main theorem: Writeback preserves complete scoreboard invariant *)
Theorem writeback_preserves_invariant : forall st fu,
  scoreboard_invariant st ->
  writeback_precond fu st ->
  scoreboard_invariant (writeback_transition fu st).
Proof.
  intros st fu Hinv Hpre.
  unfold scoreboard_invariant in *.
  destruct Hinv as [HB0 [Hfu_valid [Hbusy [Hrj [Hrk [Hcycles [Hreg [Hrvalid [Hpc [Hqueue [Hqvalid [Hmem Himem]]]]]]]]]]]].
  split. eapply writeback_preserves_b0_zero. apply HB0.
  split. eapply writeback_preserves_fu_desc_valid. apply Hfu_valid.
  split. eapply writeback_preserves_busy_consistency. apply Hbusy.
  split. eapply writeback_preserves_rj_correct. apply Hrj.
  split. eapply writeback_preserves_rk_correct. apply Hrk.
  split. eapply writeback_preserves_cycles_bounded. apply Hcycles.
  split. eapply writeback_preserves_reg_result_consistency. apply Hpre. apply Hreg.
  split. eapply writeback_preserves_reg_result_valid. apply Hrvalid.
  split. eapply writeback_preserves_pc. apply Hfu_valid. apply Hpc.
  split. eapply writeback_preserves_queue_bounded. apply Hqueue.
  split. eapply writeback_preserves_queue_instrs_valid. apply Hqvalid.
  split.
  - unfold writeback_transition. destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi.
    + destruct (fu_result (sb_fu_status st fu)).
      * unfold write_reg. destruct dest; unfold increment_cycle; simpl; apply step_mem_subsystem_preserves_validity; assumption.
      * unfold increment_cycle. simpl. apply step_mem_subsystem_preserves_validity. assumption.
    + assumption.
  - unfold imem_valid, writeback_transition. destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi; [|assumption].
    destruct (fu_result (sb_fu_status st fu)).
    + unfold write_reg. destruct dest; unfold increment_cycle; simpl; assumption.
    + unfold increment_cycle. simpl. assumption.
Qed.

(** Fetch preserves B0 zero invariant *)
Lemma fetch_preserves_b0_zero : forall st,
  b0_zero_inv (sb_bregs st) ->
  b0_zero_inv (sb_bregs (fetch_and_enqueue st)).
Proof.
  intros st HB0.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|assumption].
  unfold enqueue_instr, increment_pc. simpl. assumption.
Qed.

(** Fetch preserves FU descriptor validity *)
Lemma fetch_preserves_fu_desc_valid : forall st,
  (forall fu, fu_desc_valid (sb_fu_status st fu)) ->
  (forall fu, fu_desc_valid (sb_fu_status (fetch_and_enqueue st) fu)).
Proof.
  intros st Hvalid fu.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|apply Hvalid].
  unfold enqueue_instr, increment_pc. simpl. apply Hvalid.
Qed.

(** Fetch preserves busy consistency *)
Lemma fetch_preserves_busy_consistency : forall st,
  (forall fu, busy_consistency (sb_fu_status st fu)) ->
  (forall fu, busy_consistency (sb_fu_status (fetch_and_enqueue st) fu)).
Proof.
  intros st Hbusy fu.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|apply Hbusy].
  unfold enqueue_instr, increment_pc. simpl. apply Hbusy.
Qed.

(** Fetch preserves Rj correctness *)
Lemma fetch_preserves_rj_correct : forall st,
  (forall fu, rj_correctness (sb_fu_status st fu)) ->
  (forall fu, rj_correctness (sb_fu_status (fetch_and_enqueue st) fu)).
Proof.
  intros st Hrj fu.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|apply Hrj].
  unfold enqueue_instr, increment_pc. simpl. apply Hrj.
Qed.

(** Fetch preserves Rk correctness *)
Lemma fetch_preserves_rk_correct : forall st,
  (forall fu, rk_correctness (sb_fu_status st fu)) ->
  (forall fu, rk_correctness (sb_fu_status (fetch_and_enqueue st) fu)).
Proof.
  intros st Hrk fu.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|apply Hrk].
  unfold enqueue_instr, increment_pc. simpl. apply Hrk.
Qed.

(** Fetch preserves cycles bounded *)
Lemma fetch_preserves_cycles_bounded : forall st,
  (forall fu, cycles_bounded (sb_fu_status st fu)) ->
  (forall fu, cycles_bounded (sb_fu_status (fetch_and_enqueue st) fu)).
Proof.
  intros st Hcycles fu.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|apply Hcycles].
  unfold enqueue_instr, increment_pc. simpl. apply Hcycles.
Qed.

(** Fetch preserves register result consistency *)
Lemma fetch_preserves_reg_result_consistency : forall st,
  reg_result_consistency (sb_fu_status st) (sb_reg_result st) ->
  reg_result_consistency (sb_fu_status (fetch_and_enqueue st))
                         (sb_reg_result (fetch_and_enqueue st)).
Proof.
  intros st Hreg fu.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|apply Hreg].
  unfold enqueue_instr, increment_pc. simpl. apply Hreg.
Qed.

(** Fetch preserves register result validity *)
Lemma fetch_preserves_reg_result_valid : forall st,
  reg_result_valid (sb_reg_result st) ->
  reg_result_valid (sb_reg_result (fetch_and_enqueue st)).
Proof.
  intros st Hrvalid.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|assumption].
  unfold enqueue_instr, increment_pc. simpl. assumption.
Qed.

(** Fetch preserves PC validity *)
Lemma fetch_preserves_pc : forall st,
  valid_pc (sb_pc st) ->
  valid_pc (sb_pc (fetch_and_enqueue st)).
Proof.
  intros st Hpc.
  unfold fetch_and_enqueue.
  destruct (fetch_instr st); [|assumption].
  unfold enqueue_instr, increment_pc. simpl.
  apply pc_increment_valid. assumption.
Qed.

(** Fetch preserves queue boundedness when precondition holds *)
Lemma fetch_preserves_queue_bounded : forall st,
  fetch_precond st ->
  queue_bounded st ->
  queue_bounded (fetch_and_enqueue st).
Proof.
  intros st Hpre Hbound.
  unfold fetch_precond in Hpre. destruct Hpre as [Hlen [instr Hinstr]].
  unfold fetch_and_enqueue, fetch_instr. rewrite Hinstr.
  unfold enqueue_instr, increment_pc, queue_bounded. simpl.
  rewrite app_length. simpl. lia.
Qed.

(** Fetch preserves queue instructions validity when fetched instruction is valid *)
Lemma fetch_preserves_queue_instrs_valid : forall st,
  scoreboard_invariant st ->
  fetch_precond st ->
  queue_instrs_valid st ->
  queue_instrs_valid (fetch_and_enqueue st).
Proof.
  intros st Hinv Hpre Hvalid.
  unfold fetch_precond in Hpre. destruct Hpre as [Hlen [instr Hinstr]].
  unfold fetch_and_enqueue, fetch_instr. rewrite Hinstr.
  unfold enqueue_instr, increment_pc, queue_instrs_valid. simpl.
  intros instr' Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply Hvalid. assumption.
  - simpl in Hin. destruct Hin as [Heq|Hin]; [|inversion Hin].
    subst instr'. eapply imem_instr_valid; eassumption.
Qed.

(** Main theorem: Fetch preserves complete scoreboard invariant *)
Theorem fetch_preserves_invariant : forall st,
  scoreboard_invariant st ->
  fetch_precond st ->
  scoreboard_invariant (fetch_and_enqueue st).
Proof.
  intros st Hinv Hpre.
  unfold scoreboard_invariant in *.
  destruct Hinv as [HB0 [Hfu_valid [Hbusy [Hrj [Hrk [Hcycles [Hreg [Hrvalid [Hpc [Hqueue [Hqvalid [Hmem Himem]]]]]]]]]]]].
  split. eapply fetch_preserves_b0_zero. apply HB0.
  split. eapply fetch_preserves_fu_desc_valid. apply Hfu_valid.
  split. eapply fetch_preserves_busy_consistency. apply Hbusy.
  split. eapply fetch_preserves_rj_correct. apply Hrj.
  split. eapply fetch_preserves_rk_correct. apply Hrk.
  split. eapply fetch_preserves_cycles_bounded. apply Hcycles.
  split. eapply fetch_preserves_reg_result_consistency. apply Hreg.
  split. eapply fetch_preserves_reg_result_valid. apply Hrvalid.
  split. eapply fetch_preserves_pc. apply Hpc.
  split. eapply fetch_preserves_queue_bounded; assumption.
  split.
  - apply (fetch_preserves_queue_instrs_valid st); try assumption.
    + split. exact HB0.
      split. exact Hfu_valid.
      split. exact Hbusy.
      split. exact Hrj.
      split. exact Hrk.
      split. exact Hcycles.
      split. exact Hreg.
      split. exact Hrvalid.
      split. exact Hpc.
      split. exact Hqueue.
      split. exact Hqvalid.
      split. exact Hmem.
      exact Himem.
  - split.
    + unfold fetch_and_enqueue. destruct (fetch_instr st); simpl; assumption.
    + unfold imem_valid, fetch_and_enqueue. destruct (fetch_instr st); simpl; assumption.
Qed.

(** Dispatch preserves invariants (complex due to conditional issue) *)
Theorem dispatch_preserves_invariant : forall st,
  scoreboard_invariant st ->
  dispatch_precond st ->
  scoreboard_invariant (issue_from_queue st).
Proof.
  intros st Hinv Hpre.
  unfold issue_from_queue.
  destruct (dequeue_instr st) as [[instr st_deq]|] eqn:Hdeq; [|assumption].
  destruct (negb (first_order_conflict_b (sb_fu_status st) instr)) eqn:Hconf.
  - unfold scoreboard_invariant in Hinv.
    destruct Hinv as [HB0 [Hfu_valid [Hbusy [Hrj [Hrk [Hcycles [Hreg [Hrvalid [Hpc [Hqueue [Hqvalid [Hmem Himem]]]]]]]]]]]].
    assert (Hdeq_inv: scoreboard_invariant st_deq).
    { unfold scoreboard_invariant, dequeue_instr in *.
      destruct (sb_instr_queue st) as [|i q] eqn:Hq; [discriminate|].
      injection Hdeq as Heq1 Heq2. subst instr st_deq. simpl.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      split. unfold queue_bounded. simpl. unfold queue_bounded in Hqueue. rewrite Hq in Hqueue. simpl in Hqueue. lia.
      split. unfold queue_instrs_valid. simpl. unfold queue_instrs_valid in Hqvalid. intros instr' Hin. apply Hqvalid. rewrite Hq. simpl. right. assumption.
      split. assumption.
      assumption.
    }
    apply negb_true_iff in Hconf.
    assert (Hno_conflict: ~first_order_conflict (sb_fu_status st) instr).
    { intro Hcontra. apply first_order_conflict_iff in Hcontra. rewrite Hcontra in Hconf. discriminate. }
    assert (Hno_conflict_deq: ~first_order_conflict (sb_fu_status st_deq) instr).
    { unfold dequeue_instr in Hdeq.
      destruct (sb_instr_queue st) as [|i q] eqn:Hq; [discriminate|].
      injection Hdeq as _ Heq2. subst st_deq. simpl in *. assumption. }
    assert (Hinstr_valid: instr_valid instr).
    { unfold dequeue_instr in Hdeq.
      destruct (sb_instr_queue st) as [|i q] eqn:Hq; [discriminate|].
      injection Hdeq as Heq1 _. subst instr.
      apply Hqvalid. rewrite Hq. simpl. left. reflexivity.
    }
    apply issue_preserves_invariant; [assumption|unfold issue_precond; split; assumption].
  - assumption.
Qed.

(** Invariants preserved by single step *)
Theorem step_preserves_invariant : forall st st',
  scoreboard_invariant st ->
  sb_step st st' ->
  scoreboard_invariant st'.
Proof.
  intros st st' Hinv Hstep.
  destruct Hstep.
  - subst. apply issue_preserves_invariant; assumption.
  - subst. apply read_preserves_invariant; assumption.
  - subst. apply execute_preserves_invariant; assumption.
  - subst. apply writeback_preserves_invariant; assumption.
  - subst. apply fetch_preserves_invariant; assumption.
  - subst. apply dispatch_preserves_invariant; assumption.
Qed.

(** Invariants preserved by multi-step *)
Theorem steps_preserve_invariant : forall st st',
  scoreboard_invariant st ->
  sb_steps st st' ->
  scoreboard_invariant st'.
Proof.
  intros st st' Hinv Hsteps.
  induction Hsteps.
  - assumption.
  - apply IHHsteps. eapply step_preserves_invariant; eassumption.
Qed.

(** ** Memory System Operations and Invariants *)

(** Valid memory address predicate *)
Definition valid_mem_addr (addr : mem_addr) : Prop :=
  addr < 2^17.

(** Valid bank identifier *)
Definition valid_bank_id (bid : bank_id) : Prop :=
  bid < 32.

(** Reconstruct address from bank and offset *)
Definition bank_offset_to_addr (bid : bank_id) (offset : nat) : mem_addr :=
  offset * 32 + bid.

Lemma addr_bank_offset_inv : forall addr,
  valid_mem_addr addr ->
  bank_offset_to_addr (addr_to_bank addr) (addr_to_offset addr) = addr.
Proof.
  intros addr Hvalid.
  unfold bank_offset_to_addr, addr_to_bank, addr_to_offset.
  rewrite Nat.mul_comm.
  rewrite <- Nat.div_mod; try lia.
Qed.

(** Write word to bank *)
Definition write_bank (mem : central_memory) (addr : mem_addr) (value : nat) : central_memory :=
  let bid := addr_to_bank addr in
  let offset := addr_to_offset addr in
  let new_bank := fun off => if Nat.eqb off offset then value else (mem_banks mem bid) off in
  mk_central_memory
    (fun b => if Nat.eqb b bid then new_bank else mem_banks mem b)
    (mem_bank_status mem)
    (mem_cycle_count mem).

(** Check if bank is available for access *)
Definition bank_available (mem : central_memory) (bid : bank_id) : bool :=
  negb (bank_busy (mem_bank_status mem bid)).

(** Check for bank conflict *)
Definition bank_conflict (mem : central_memory) (addr : mem_addr) : bool :=
  let bid := addr_to_bank addr in
  bank_busy (mem_bank_status mem bid).

(** Initiate memory read *)
Definition start_mem_read (mem : central_memory) (addr : mem_addr) : central_memory :=
  let bid := addr_to_bank addr in
  let new_status := mk_bank_status true MEM_ACCESS_TIME (Some addr) false in
  mk_central_memory
    (mem_banks mem)
    (fun b => if Nat.eqb b bid then new_status else mem_bank_status mem b)
    (mem_cycle_count mem).

(** Initiate memory write *)
Definition start_mem_write (mem : central_memory) (addr : mem_addr) : central_memory :=
  let bid := addr_to_bank addr in
  let new_status := mk_bank_status true MEM_ACCESS_TIME (Some addr) true in
  mk_central_memory
    (mem_banks mem)
    (fun b => if Nat.eqb b bid then new_status else mem_bank_status mem b)
    (mem_cycle_count mem).

(** Allocate free D-register for load operation *)
Definition alloc_dreg (dregs : dreg_file) : option dreg :=
  if negb (dreg_busy (dregs D1)) then Some D1
  else if negb (dreg_busy (dregs D2)) then Some D2
  else if negb (dreg_busy (dregs D3)) then Some D3
  else if negb (dreg_busy (dregs D4)) then Some D4
  else if negb (dreg_busy (dregs D5)) then Some D5
  else if negb (dreg_busy (dregs D6)) then Some D6
  else if negb (dreg_busy (dregs D7)) then Some D7
  else None.

(** Start load operation *)
Definition start_load (msys : memory_subsystem) (addr : mem_addr) (target_xreg : nat)
  : option memory_subsystem :=
  match alloc_dreg (d_registers msys) with
  | None => None
  | Some dreg =>
      if bank_conflict (main_memory msys) addr then
        None
      else
        let new_mem := start_mem_read (main_memory msys) addr in
        let new_dreg_status := mk_dreg_status true false 0
                                (Some target_xreg) (Some addr) MEM_ACCESS_TIME in
        let new_dregs := fun d => if match d, dreg with
                                     | D1, D1 => true | D2, D2 => true | D3, D3 => true
                                     | D4, D4 => true | D5, D5 => true | D6, D6 => true
                                     | D7, D7 => true | _, _ => false
                                     end
                                  then new_dreg_status
                                  else d_registers msys d in
        Some (mk_mem_subsystem new_mem new_dregs)
  end.

(** Start store operation *)
Definition start_store (msys : memory_subsystem) (addr : mem_addr) (value : nat)
  : option memory_subsystem :=
  if bank_conflict (main_memory msys) addr then
    None
  else
    let new_mem := start_mem_write (main_memory msys) addr in
    let final_mem := write_bank new_mem addr value in
    Some (mk_mem_subsystem final_mem (d_registers msys)).

(** Memory subsystem lemmas *)

Lemma valid_bank_from_addr : forall addr,
  valid_mem_addr addr ->
  valid_bank_id (addr_to_bank addr).
Proof.
  intros addr Hvalid.
  unfold valid_bank_id, addr_to_bank.
  apply Nat.mod_upper_bound.
  lia.
Qed.

(** Helper: initial memory subsystem is valid *)
Lemma init_mem_valid : mem_subsystem_valid init_mem_subsystem.
Proof.
  unfold mem_subsystem_valid, init_mem_subsystem. simpl.
  repeat split.
  - apply init_bank_data_valid.
  - apply init_bank_mutual_exclusion.
  - apply init_dreg_data_valid.
  - apply init_dreg_busy_has_addr.
  - apply init_dreg_addrs_valid.
Qed.

(** ** High-Level Correctness Properties *)

(** A state is quiescent if all functional units are idle *)
Definition quiescent (st : scoreboard_state) : Prop :=
  forall fu, fu_busy (sb_fu_status st fu) = false.

(** A state has work available if there are instructions in the queue or FUs executing *)
Definition has_work (st : scoreboard_state) : Prop :=
  sb_instr_queue st <> [] \/ ~quiescent st.

(** Progress: if the invariant holds and there is work, a step is possible *)
Definition progress_property : Prop :=
  forall st, scoreboard_invariant st -> has_work st ->
    exists st', sb_step st st'.

(** Determinism: steps are deterministic given same state and same transition type *)
Definition deterministic_step : Prop :=
  forall st st1 st2, sb_step st st1 -> sb_step st st2 -> st1 = st2.

(** Note: The scoreboard allows multiple concurrent steps (e.g., Execute on FU1
    while Read on FU2), so full determinism doesn't hold. Instead, we prove
    determinism conditioned on the same transition being chosen. *)

(** Same-transition determinism for Issue *)
Lemma issue_deterministic : forall st instr1 instr2 st1 st2,
  st1 = issue_transition st instr1 ->
  st2 = issue_transition st instr2 ->
  instr1 = instr2 ->
  st1 = st2.
Proof.
  intros st instr1 instr2 st1 st2 H1 H2 Heq.
  subst. reflexivity.
Qed.

(** Same-FU determinism for Read *)
Lemma read_deterministic : forall st fu st1 st2,
  st1 = read_transition fu st ->
  st2 = read_transition fu st ->
  st1 = st2.
Proof.
  intros st fu st1 st2 H1 H2.
  subst. reflexivity.
Qed.

(** Same-FU determinism for Execute *)
Lemma execute_deterministic : forall st fu st1 st2,
  st1 = execute_step fu st ->
  st2 = execute_step fu st ->
  st1 = st2.
Proof.
  intros st fu st1 st2 H1 H2.
  subst. reflexivity.
Qed.

(** Same-FU determinism for Writeback *)
Lemma writeback_deterministic : forall st fu st1 st2,
  st1 = writeback_transition fu st ->
  st2 = writeback_transition fu st ->
  st1 = st2.
Proof.
  intros st fu st1 st2 H1 H2.
  subst. reflexivity.
Qed.

(** Fetch determinism *)
Lemma fetch_deterministic : forall st st1 st2,
  st1 = fetch_and_enqueue st ->
  st2 = fetch_and_enqueue st ->
  st1 = st2.
Proof.
  intros st st1 st2 H1 H2.
  subst. reflexivity.
Qed.

(** Dispatch determinism *)
Lemma dispatch_deterministic : forall st st1 st2,
  st1 = issue_from_queue st ->
  st2 = issue_from_queue st ->
  st1 = st2.
Proof.
  intros st st1 st2 H1 H2.
  subst. reflexivity.
Qed.

(** Observation: sb_step is NOT fully deterministic because multiple
    transitions can fire simultaneously (e.g., execute on different FUs).
    This is inherent to the concurrent nature of the scoreboard.
    Each individual transition type IS deterministic given its parameters. *)

(** Safety: all reachable states satisfy the invariant *)
Definition safety_property : Prop :=
  forall st st',
    scoreboard_invariant st ->
    sb_steps st st' ->
    scoreboard_invariant st'.

(** The safety property holds by our invariant preservation theorem *)
Theorem safety_holds : safety_property.
Proof.
  unfold safety_property.
  intros st st' Hinv Hsteps.
  eapply steps_preserve_invariant; eassumption.
Qed.

(** Helper: enqueuing preserves queue length increase by one *)
Lemma enqueue_increases_length : forall st instr,
  length (sb_instr_queue (enqueue_instr st instr)) = length (sb_instr_queue st) + 1.
Proof.
  intros st instr.
  unfold enqueue_instr. simpl.
  rewrite app_length. simpl. lia.
Qed.

(** Helper: empty queue has length 0 *)
Lemma empty_queue_length : forall st,
  sb_instr_queue st = [] ->
  length (sb_instr_queue st) = 0.
Proof.
  intros st Hempty.
  rewrite Hempty. simpl. reflexivity.
Qed.

(** Helper: executing a busy FU with non-zero cycles decreases remaining cycles *)
Lemma execute_decreases_cycles : forall st fu,
  fu_busy (sb_fu_status st fu) = true ->
  fu_remaining_cycles (sb_fu_status st fu) > 0 ->
  fu_remaining_cycles (sb_fu_status (execute_step fu st) fu) =
    fu_remaining_cycles (sb_fu_status st fu) - 1.
Proof.
  intros st fu Hbusy Hgt.
  unfold execute_step.
  rewrite Hbusy.
  assert (Hneq: fu_remaining_cycles (sb_fu_status st fu) =? 0 = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hneq.
  unfold update_fu. simpl.
  destruct (match fu, fu with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl; try reflexivity.
  destruct fu; discriminate Heq.
Qed.

(** Helper: not quiescent means some FU is busy *)
Lemma not_quiescent_exists_busy : forall st,
  ~quiescent st ->
  exists fu, fu_busy (sb_fu_status st fu) = true.
Proof.
  intros st Hnq.
  unfold quiescent in Hnq.
  destruct (fu_busy (sb_fu_status st FU_Branch)) eqn:HB; [exists FU_Branch; auto|].
  destruct (fu_busy (sb_fu_status st FU_Boolean)) eqn:HBO; [exists FU_Boolean; auto|].
  destruct (fu_busy (sb_fu_status st FU_Shift)) eqn:HS; [exists FU_Shift; auto|].
  destruct (fu_busy (sb_fu_status st FU_LongAdd)) eqn:HL; [exists FU_LongAdd; auto|].
  destruct (fu_busy (sb_fu_status st FU_FPAdd)) eqn:HFA; [exists FU_FPAdd; auto|].
  destruct (fu_busy (sb_fu_status st FU_FPMul1)) eqn:HM1; [exists FU_FPMul1; auto|].
  destruct (fu_busy (sb_fu_status st FU_FPMul2)) eqn:HM2; [exists FU_FPMul2; auto|].
  destruct (fu_busy (sb_fu_status st FU_FPDiv)) eqn:HD; [exists FU_FPDiv; auto|].
  destruct (fu_busy (sb_fu_status st FU_Incr1)) eqn:HI1; [exists FU_Incr1; auto|].
  destruct (fu_busy (sb_fu_status st FU_Incr2)) eqn:HI2; [exists FU_Incr2; auto|].
  exfalso. apply Hnq. intros fu. destruct fu; assumption.
Qed.

(** Helper: busy FU can always execute *)
Lemma busy_fu_can_execute : forall st fu,
  fu_busy (sb_fu_status st fu) = true ->
  exists st', st' = execute_step fu st.
Proof.
  intros st fu Hbusy.
  exists (execute_step fu st). reflexivity.
Qed.

(** Helper: non-empty queue enables dispatch *)
Lemma nonempty_queue_enables_dispatch : forall st,
  sb_instr_queue st <> [] ->
  dispatch_precond st.
Proof.
  intros st Hne.
  unfold dispatch_precond. assumption.
Qed.

(** Theorem: Progress holds - if there is work, a step is possible *)
Theorem progress_holds : progress_property.
Proof.
  unfold progress_property, has_work.
  intros st Hinv [Hqueue | Hnq].
  - exists (issue_from_queue st).
    apply Step_Dispatch.
    apply nonempty_queue_enables_dispatch. assumption.
    reflexivity.
  - apply not_quiescent_exists_busy in Hnq.
    destruct Hnq as [fu Hbusy].
    exists (execute_step fu st).
    apply (Step_Execute st fu). assumption. reflexivity.
Qed.

(** Helper: if fetch precondition holds, we can fetch *)
Lemma fetch_enables_step : forall st,
  fetch_precond st ->
  exists st', sb_step st st'.
Proof.
  intros st Hpre.
  exists (fetch_and_enqueue st).
  apply Step_Fetch with (st := st); auto.
Qed.

(** Helper: execute preserves busy status when cycles remain *)
Lemma execute_preserves_busy : forall st fu,
  fu_busy (sb_fu_status st fu) = true ->
  fu_remaining_cycles (sb_fu_status st fu) > 0 ->
  fu_busy (sb_fu_status (execute_step fu st) fu) = true.
Proof.
  intros st fu Hbusy Hcyc.
  unfold execute_step.
  rewrite Hbusy.
  assert (Hneq: fu_remaining_cycles (sb_fu_status st fu) =? 0 = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hneq.
  unfold update_fu. simpl.
  destruct (match fu, fu with
    | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
    | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
    | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
    | _, _ => false
  end) eqn:Heq; simpl; try reflexivity.
  destruct fu; discriminate Heq.
Qed.

(** Helper: writeback clears busy flag *)
Lemma writeback_clears_busy : forall st fu,
  writeback_precond fu st ->
  fu_busy (sb_fu_status (writeback_transition fu st) fu) = false.
Proof.
  intros st fu Hpre.
  unfold writeback_precond in Hpre.
  destruct Hpre as [Hbusy [Hcyc Hdest]].
  unfold writeback_transition.
  destruct (fu_fi (sb_fu_status st fu)) as [dest|] eqn:Hfi.
  - destruct (fu_result (sb_fu_status st fu)) as [v|] eqn:Hres.
    + unfold write_reg. destruct dest; unfold update_fu; simpl;
      destruct (match fu, fu with
        | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
        | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
        | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
        | _, _ => false
      end) eqn:Heq; simpl; try reflexivity;
      destruct fu; discriminate Heq.
    + unfold update_fu; simpl;
      destruct (match fu, fu with
        | FU_Branch, FU_Branch | FU_Boolean, FU_Boolean | FU_Shift, FU_Shift
        | FU_LongAdd, FU_LongAdd | FU_FPAdd, FU_FPAdd | FU_FPMul1, FU_FPMul1
        | FU_FPMul2, FU_FPMul2 | FU_FPDiv, FU_FPDiv | FU_Incr1, FU_Incr1 | FU_Incr2, FU_Incr2 => true
        | _, _ => false
      end) eqn:Heq; simpl; try reflexivity;
      destruct fu; discriminate Heq.
  - exfalso. destruct Hdest.
Qed.

(** No deadlock: a quiescent state with an empty queue can always make progress if given instructions *)
Definition no_deadlock : Prop :=
  forall st,
    scoreboard_invariant st ->
    quiescent st ->
    sb_instr_queue st = [] ->
    forall instr,
      instr_valid instr ->
      length (sb_instr_queue st) < MAX_QUEUE_DEPTH ->
      exists st', sb_step st st'.

(** Helper: if imem contains an instruction at PC, we can construct fetch_precond *)
Lemma imem_has_instr_enables_fetch : forall st instr,
  sb_imem st (sb_pc st) = Some instr ->
  length (sb_instr_queue st) < MAX_QUEUE_DEPTH ->
  fetch_precond st.
Proof.
  intros st instr Hinstr Hlen.
  unfold fetch_precond.
  split; [assumption | exists instr; assumption].
Qed.

(** Theorem: no_deadlock holds under assumption that imem always has instructions *)
Theorem no_deadlock_holds_with_imem : forall st,
  scoreboard_invariant st ->
  quiescent st ->
  sb_instr_queue st = [] ->
  forall instr,
    instr_valid instr ->
    sb_imem st (sb_pc st) = Some instr ->
    length (sb_instr_queue st) < MAX_QUEUE_DEPTH ->
    exists st', sb_step st st'.
Proof.
  intros st Hinv Hquiet Hempty instr Hvalid Himem Hlen.
  apply fetch_enables_step.
  apply (imem_has_instr_enables_fetch st instr); assumption.
Qed.

(** Stronger no_deadlock using invariant's imem_valid *)
Theorem no_deadlock_from_invariant : forall st,
  scoreboard_invariant st ->
  quiescent st ->
  sb_instr_queue st = [] ->
  length (sb_instr_queue st) < MAX_QUEUE_DEPTH ->
  (exists instr, sb_imem st (sb_pc st) = Some instr) ->
  exists st', sb_step st st'.
Proof.
  intros st Hinv Hquiet Hempty Hlen [instr Himem].
  apply fetch_enables_step.
  apply (imem_has_instr_enables_fetch st instr); assumption.
Qed.

(** Note: Full no_deadlock without assuming imem contains instruction at PC
    requires either totality of imem (all addresses map to instructions) or
    modeling a halt state. The current formulation correctly captures that
    progress is possible when imem has an instruction at the current PC. *)

(** Functional units eventually complete: any busy FU will eventually become idle *)
Definition eventual_completion : Prop :=
  forall st fu,
    scoreboard_invariant st ->
    fu_busy (sb_fu_status st fu) = true ->
    exists st' n,
      sb_steps st st' /\
      fu_busy (sb_fu_status st' fu) = false /\
      sb_cycle_count st' = sb_cycle_count st + n.

(** Note on eventual_completion proof:
    To prove this property would require:
    1. Well-founded induction on fu_remaining_cycles
    2. Show that repeated execution decreases cycles (execute_decreases_cycles)
    3. Show that execute preserves busy when cycles > 0 (execute_preserves_busy)
    4. Show that when cycles = 0, writeback can clear the FU (writeback_clears_busy)
    5. Handle WAR hazards: show third_order_conflict eventually clears

    The key helpers are already proven:
    - execute_decreases_cycles: executing with cycles > 0 decreases by 1
    - execute_preserves_busy: FU stays busy while cycles > 0
    - writeback_clears_busy: writeback sets busy = false

    The remaining challenge is proving WAR hazards eventually resolve,
    which requires reasoning about the dynamic behavior of read operations. *)

Require Import Coq.Arith.Wf_nat.

Definition fu_measure (st : scoreboard_state) (fu : func_unit) : nat :=
  if fu_busy (sb_fu_status st fu)
  then S (fu_remaining_cycles (sb_fu_status st fu))
  else 0.

Definition total_fu_cycles (st : scoreboard_state) : nat :=
  fu_measure st FU_Branch + fu_measure st FU_Boolean + fu_measure st FU_Shift +
  fu_measure st FU_LongAdd + fu_measure st FU_FPAdd + fu_measure st FU_FPMul1 +
  fu_measure st FU_FPMul2 + fu_measure st FU_FPDiv + fu_measure st FU_Incr1 + fu_measure st FU_Incr2.

Lemma execute_decreases_measure_for_fu : forall st fu,
  fu_busy (sb_fu_status st fu) = true ->
  fu_remaining_cycles (sb_fu_status st fu) > 0 ->
  fu_measure (execute_step fu st) fu < fu_measure st fu.
Proof.
  intros st fu Hbusy Hcyc.
  unfold fu_measure.
  assert (Hdec := execute_decreases_cycles st fu Hbusy Hcyc).
  assert (Hpres := execute_preserves_busy st fu Hbusy Hcyc).
  rewrite Hpres. rewrite Hbusy. lia.
Qed.

Lemma execute_preserves_other_fu_measure : forall st fu fu',
  fu <> fu' ->
  fu_measure (execute_step fu st) fu' = fu_measure st fu'.
Proof.
  intros st fu fu' Hneq.
  unfold fu_measure, execute_step.
  destruct (fu_busy (sb_fu_status st fu)) eqn:Hb; [|reflexivity].
  destruct (fu_remaining_cycles (sb_fu_status st fu) =? 0) eqn:Hc; [reflexivity|].
  unfold increment_cycle, update_fu. simpl.
  destruct (match fu, fu' with FU_Branch,FU_Branch|FU_Boolean,FU_Boolean|FU_Shift,FU_Shift
           |FU_LongAdd,FU_LongAdd|FU_FPAdd,FU_FPAdd|FU_FPMul1,FU_FPMul1|FU_FPMul2,FU_FPMul2
           |FU_FPDiv,FU_FPDiv|FU_Incr1,FU_Incr1|FU_Incr2,FU_Incr2 => true |_,_ => false end) eqn:Heq;
  [exfalso; apply Hneq; destruct fu, fu'; try reflexivity; discriminate Heq|reflexivity].
Qed.

(** Helper: execute step can be taken for busy FU *)
Lemma busy_fu_enables_execute_step : forall st fu,
  fu_busy (sb_fu_status st fu) = true ->
  sb_step st (execute_step fu st).
Proof.
  intros st fu Hbusy.
  apply (Step_Execute st fu). assumption. reflexivity.
Qed.

(** Helper: single execute step relates states *)
Lemma execute_single_step : forall st fu,
  fu_busy (sb_fu_status st fu) = true ->
  sb_steps st (execute_step fu st).
Proof.
  intros st fu Hbusy.
  apply (Steps_Step st (execute_step fu st) (execute_step fu st)).
  - apply busy_fu_enables_execute_step. assumption.
  - apply Steps_Refl.
Qed.

(** Simplified eventual_completion under no-WAR-hazard assumption *)
Theorem eventual_completion_no_war : forall st fu dest,
  scoreboard_invariant st ->
  fu_busy (sb_fu_status st fu) = true ->
  fu_remaining_cycles (sb_fu_status st fu) = 0 ->
  fu_fi (sb_fu_status st fu) = Some dest ->
  ~third_order_conflict (sb_fu_status st) dest ->
  exists st',
    sb_step st st' /\
    fu_busy (sb_fu_status st' fu) = false.
Proof.
  intros st fu dest Hinv Hbusy Hcyc Hfi Hnowar.
  exists (writeback_transition fu st).
  split.
  - apply Step_Writeback with (fu := fu).
    + unfold writeback_precond.
      split; [assumption | split; [assumption |]].
      rewrite Hfi. assumption.
    + reflexivity.
  - apply writeback_clears_busy.
    unfold writeback_precond.
    split; [assumption | split; [assumption |]].
    rewrite Hfi. assumption.
Qed.

(** Note: Full eventual_completion requires proving that WAR hazards
    (third_order_conflict) eventually resolve through read operations
    completing and clearing their Rj/Rk flags. This requires additional
    machinery to track read operation progress and a more complex
    well-founded measure combining remaining cycles across all FUs. *)

(** Bounded execution: functional units complete within their latency bound *)
Definition bounded_execution : Prop :=
  forall st fu op,
    scoreboard_invariant st ->
    fu_busy (sb_fu_status st fu) = true ->
    fu_op (sb_fu_status st fu) = Some op ->
    fu_remaining_cycles (sb_fu_status st fu) <= latency op.

(** Theorem: Bounded execution holds *)
Theorem bounded_execution_holds : bounded_execution.
Proof.
  unfold bounded_execution.
  intros st fu op Hinv Hbusy Hop.
  unfold scoreboard_invariant in Hinv.
  destruct Hinv as [_ [_ [_ [_ [_ [Hcycles _]]]]]].
  unfold cycles_bounded in Hcycles.
  specialize (Hcycles fu).
  rewrite Hbusy in Hcycles.
  specialize (Hcycles eq_refl).
  rewrite Hop in Hcycles.
  exact Hcycles.
Qed.

(** Memory subsystem stays valid during execution *)
Definition mem_subsystem_stays_valid : Prop :=
  forall st st',
    scoreboard_invariant st ->
    mem_subsystem_valid (sb_mem st) ->
    sb_step st st' ->
    mem_subsystem_valid (sb_mem st').

(** Theorem: Memory subsystem stays valid *)
Theorem mem_subsystem_stays_valid_holds : mem_subsystem_stays_valid.
Proof.
  unfold mem_subsystem_stays_valid.
  intros st st' Hinv Hmem Hstep.
  apply step_preserves_invariant in Hstep; [|assumption].
  unfold scoreboard_invariant in Hstep.
  destruct Hstep as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hmem' _]]]]]]]]]]]].
  exact Hmem'.
Qed.

(** PC stays valid during execution (already proven via invariant preservation) *)
Theorem pc_stays_valid : forall st st',
  scoreboard_invariant st ->
  sb_step st st' ->
  valid_pc (sb_pc st').
Proof.
  intros st st' Hinv Hstep.
  apply step_preserves_invariant in Hstep; [|assumption].
  unfold scoreboard_invariant in Hstep.
  destruct Hstep as [_ [_ [_ [_ [_ [_ [_ [_ [Hpc _]]]]]]]]].
  assumption.
Qed.

(** Queue stays bounded during execution (already proven via invariant preservation) *)
Theorem queue_stays_bounded : forall st st',
  scoreboard_invariant st ->
  sb_step st st' ->
  queue_bounded st'.
Proof.
  intros st st' Hinv Hstep.
  apply step_preserves_invariant in Hstep; [|assumption].
  unfold scoreboard_invariant in Hstep.
  destruct Hstep as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hbound _]]]]]]]]]].
  assumption.
Qed.
