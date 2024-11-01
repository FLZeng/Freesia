From iris.heap_lang Require Import proofmode notation.

Definition N : namespace := nroot .@ "N".
Definition lockN : namespace := nroot .@ "lock".
Definition mutexN : namespace := nroot .@ "mutex".


Definition wait_queue_elem : Type := prod
  bool (* done *)
  bool (* wait_read *).

Notation wait_queue := (list wait_queue_elem).


Definition mk_wait_queue_elem : val := λ: <>,
  let: "done" := #false in
  let: "wait_read" := #false in
  ref ("done", "wait_read").

Structure wait_queue_elem1 : Type := {
  done : bool;
  wait_read : bool;
}.

Structure mutex1 := mk_mutex {
  spin_lock : val;  (* used when operating on this struct *)
  state : Z;  (* -1: write, 0: unlocked, > 0: readers *)
  wq : (list wait_queue_elem1);
}.

Record Mutex := mkMutex {
  m_lk : loc;
  m_state : loc;
  m_wq : loc;
}.

Record System_State := mkState {
  g_fd : loc;
  (* g_mutex : (loc * loc * loc); *)
  g_mutex : Mutex;
}.

Notation TEEC_UUID := nat.

Inductive TEEC_Result : Type :=
  | TEEC_SUCCESS
  | TEEC_ERROR_GENERIC
  | TEEC_ERROR_ACCESS_DENIED
  | TEEC_ERROR_CANCEL
  | TEEC_ERROR_ACCESS_CONFLICT
  | TEEC_ERROR_EXCESS_DATA
  | TEEC_ERROR_BAD_FORMAT
  | TEEC_ERROR_BAD_PARAMETERS
  | TEEC_ERROR_BAD_STATE
  | TEEC_ERROR_ITEM_NOT_FOUND
  | TEEC_ERROR_NOT_IMPLEMENTED
  | TEEC_ERROR_NOT_SUPPORTED
  | TEEC_ERROR_NO_DATA
  | TEEC_ERROR_OUT_OF_MEMORY
  | TEEC_ERROR_BUSY
  | TEEC_ERROR_COMMUNICATION
  | TEEC_ERROR_SECURITY
  | TEEC_ERROR_SHORT_BUFFER
  | TEEC_ERROR_TARGET_DEAD
  | TEE_ERROR_EXTERNAL_CANCEL
  | TEE_ERROR_OVERFLOW
  | TEE_ERROR_TARGET_DEAD
  | TEE_ERROR_STORAGE_NO_SPACE
  | TEE_ERROR_MAC_INVALID
  | TEE_ERROR_SIGNATURE_INVALID
  | TEE_ERROR_TIME_NOT_SET
  | TEE_ERROR_TIME_NEEDS_RESET.

Inductive TEEC_Parameter_Type : Type :=
  | TEEC_NONE
  | TEEC_VALUE_INPUT
  | TEEC_VALUE_OUTPUT
  | TEEC_VALUE_INOUT
  | TEEC_MEMREF_TEMP_INPUT
  | TEEC_MEMREF_TEMP_OUTPUT
  | TEEC_MEMREF_TEMP_INOUT
  | TEEC_MEMREF_WHOLE
  | TEEC_MEMREF_PARTIAL_INPUT
  | TEEC_MEMREF_PARTIAL_OUTPUT
  | TEEC_MEMREF_PARTIAL_INOUT.

Inductive TEEC_Shm_Flag : Type :=
  | TEEC_MEM_INPUT
  | TEEC_MEM_OUTPUT
  | TEEC_MEM_INOUT.

Inductive TEEC_ErrorOrigin : Type :=
  | TEEC_ORIGIN_API
  | TEEC_ORIGIN_COMMS
  | TEEC_ORIGIN_TEE
  | TEEC_ORIGIN_TRUSTED_APP.

Record TEEC_Context_imp := mkCtxImp {
  ctx_fd : loc;
  is_initialized : loc;
  reg_mem : bool;
  memref_null : bool;
}.

Record TEEC_Context := mkCtx {
  ctx_imp : TEEC_Context_imp;
}.

Record TEEC_SharedMemory_imp := mkShmImp {
  shm_id : Z;
  shm_allocated_size : nat;
  shm_shadow_buffer : loc;
  shm_registred_fd : Z;
  shm_imp_flags : TEEC_Shm_Flag;
}.

Record TEEC_SharedMemory := mkShm {
  shm_buffer : loc;
  shm_size : nat;
  shm_flags : TEEC_Shm_Flag;
  shm_imp : TEEC_SharedMemory_imp;
}.

Record TEEC_TempMemoryReference := mkTempMemRef {
  tmp_buffer : loc;
  tmp_size : nat;
}.

Record TEEC_RegisteredMemoryReference := mkRegMemRef {
  reg_parent : TEEC_SharedMemory;
  reg_size : nat;
  reg_offset : nat;
}.

Record TEEC_Value := mkValue {
  val_a : nat;
  val_b : nat;
}.

Inductive TEEC_Parameter : Type :=
  | tmpref (buf : TEEC_TempMemoryReference)
  | memref (buf : TEEC_RegisteredMemoryReference)
  | value  (val : TEEC_Value).

Record TEEC_Session_imp := mkSessImp {
  sess_ctx : loc;
  sess_id : nat;
}.

Record TEEC_Session := mkSession {
  sess_imp : TEEC_Session_imp;
}.

Record TEEC_Operation_imp := mkOpImp {
  op_sess : loc;
}.

Record TEEC_Operation := mkOp {
  op_started : bool;
  op_param_type : TEEC_Parameter_Type;
  op_param: TEEC_Parameter;
  op_imp : TEEC_Operation_imp;
}.

Definition pointer_update : val :=
  λ: "l" "v", "l" <- "v".