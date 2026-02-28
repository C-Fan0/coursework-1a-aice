(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x ->
  match x with
  | Eq  -> fz
  | Neq -> not fz
  | Gt  -> (fs = fo) && not fz
  | Ge  -> (fs = fo)
  | Lt  -> (fs <> fo)
  | Le  -> (fs <> fo) || fz

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if addr >= mem_bot && addr < mem_top then
    Some (Int64.to_int (Int64.sub addr mem_bot))
  else
    None


let read_mem (m:mach) (addr:int64) : int64 =
  match map_addr addr with
  | None -> raise X86lite_segfault
  | Some i ->
    let bytes = [m.mem.(i); m.mem.(i+1); m.mem.(i+2); m.mem.(i+3);
                 m.mem.(i+4); m.mem.(i+5); m.mem.(i+6); m.mem.(i+7)] in
    int64_of_sbytes bytes

let write_mem (m:mach) (addr:int64) (v:int64) : unit =
  match map_addr addr with
  | None -> raise X86lite_segfault
  | Some i ->
    let bytes = sbytes_of_int64 v in
    List.iteri (fun j b -> m.mem.(i+j) <- b) bytes

let read_operand (m:mach) (op:operand) : int64 =
  match op with
  | Imm (Lit i)-> i                    
  | Reg r-> m.regs.(rind r)            
  | Ind1 (Lit i)-> read_mem m i        
  | Ind2 r-> read_mem m m.regs.(rind r)
  | Ind3 (Lit i, r)-> read_mem m (Int64.add i m.regs.(rind r))  
  | _ -> failwith "invalid operand"

let write_operand (m:mach) (op:operand) (v:int64) : unit =
  match op with
  | Reg r -> m.regs.(rind r) <- v
  | Ind1 (Lit i)-> write_mem m i v
  | Ind2 r -> write_mem m m.regs.(rind r) v
  | Ind3 (Lit i, r)-> write_mem m (Int64.add i m.regs.(rind r)) v
  | _ -> failwith "cannot write to this operand"


(*Abdullah + Juan Helper Functions*)
let interp_negq (v:int64) : int64 = Int64.neg v

let interp_incq (v:int64) : int64 = Int64.add v 1L

let interp_decq (v:int64) : int64 = Int64.sub v 1L

let interp_addq (src:int64) (dest:int64) : int64 = Int64.add dest src

let interp_subq (src:int64) (dest:int64) : int64 = Int64.sub dest src

let interp_leaq (m:mach) (op:operand) : int64 =
  match op with
  | Ind1 (Lit i) -> i
  | Ind2 r -> m.regs.(rind r)
  | Ind3 (Lit i, r) -> Int64.add i m.regs.(rind r)
  | _ -> failwith "leaq: invalid operand"

let interp_pushq (m:mach) (v:int64) : unit =
  let new_rsp = Int64.sub m.regs.(rind Rsp) 8L in
  m.regs.(rind Rsp) <- new_rsp;
  write_mem m new_rsp v

let interp_movq (v:int64) : int64 = v

(*Flag Functions Juan*)

let set_flags_add (m:mach) (src:int64) (dest:int64) (result:int64) : unit =
  m.flags.fz <- result = 0L;
  m.flags.fs <- result < 0L;
  m.flags.fo <- ((Int64.compare src 0L >= 0) = (Int64.compare dest 0L >= 0))
             && ((Int64.compare src 0L >= 0) <> (Int64.compare result 0L >= 0))

let set_flags_sub (m:mach) (src:int64) (dest:int64) (result:int64) : unit =
  m.flags.fz <- result = 0L;
  m.flags.fs <- result < 0L;
  m.flags.fo <- ((Int64.compare dest 0L >= 0) <> (Int64.compare src 0L >= 0))
             && ((Int64.compare dest 0L >= 0) <> (Int64.compare result 0L >= 0))

let set_flags_neg (m:mach) (src:int64) (result:int64) : unit =
  m.flags.fz <- result = 0L;
  m.flags.fs <- result < 0L;
  m.flags.fo <- src = Int64.min_int








let interp_imulq (s:int64) (d:int64) : int64 = Int64.mul s d

let interp_shlq (amt:int64) (d:int64) : int64 =
  let shift = Int64.to_int amt in
  if shift = 0 then d
  else Int64.shift_left d shift

let interp_xorq (s:int64) (d:int64) : int64 = Int64.logxor s d

let interp_orq (s:int64) (d:int64) : int64 = Int64.logor s d

let interp_andq (s:int64) (d:int64) : int64 = Int64.logand s d

let interp_popq (m:mach) : int64 =
  let rsp = m.regs.(rind Rsp) in
  let v = read_mem m rsp in
  m.regs.(rind Rsp) <- Int64.add rsp 8L;
  v

(*Flag Functions Abdullah*)

let set_flags_imul (m:mach) (s:int64) (d:int64) (result:int64) : unit =
  let of_flag =
    let a = Int64.to_float s in
    let b = Int64.to_float d in
    let exact = a *. b in
    let back = Int64.to_float result in
    exact <> back
  in
  m.flags.fo <- of_flag;
  m.flags.fs <- result < 0L;
  m.flags.fz <- result = 0L

let set_flags_shlq (m:mach) (amt:int64) (d:int64) (result:int64) : unit =
  let shift = Int64.to_int amt in
  if shift <> 0 then begin
    m.flags.fs <- result < 0L;
    m.flags.fz <- result = 0L;
    if shift = 1 then
      m.flags.fo <- (result < 0L) <> (d < 0L)
  end

let set_flags_logic (m:mach) (result:int64) : unit =
  m.flags.fo <- false;
  m.flags.fs <- result < 0L;
  m.flags.fz <- result = 0L

(*Step Function*)

let step (m:mach) : unit =
  let rip = m.regs.(rind Rip) in
  let ins = match map_addr rip with
    | None -> raise X86lite_segfault
    | Some i -> match m.mem.(i) with
      | InsB0 ins -> ins
      | _ -> failwith "step: expected instruction"
  in
  m.regs.(rind Rip) <- Int64.add rip ins_size;
  match ins with

  | (Movq, [src; dest]) ->
    let result = interp_movq (read_operand m src) in
    write_operand m dest result


  | (Negq, [dest]) ->
    let s = read_operand m dest in
    let result = interp_negq s in
    write_operand m dest result;
    set_flags_neg m s result


  | (Incq, [dest]) ->
    let d = read_operand m dest in
    let result = interp_incq d in
    write_operand m dest result;
    set_flags_add m 1L d result


  | (Decq, [dest]) ->
    let d = read_operand m dest in
    let result = interp_decq d in
    write_operand m dest result;
    set_flags_sub m 1L d result


  | (Addq, [src; dest]) ->
    let s = read_operand m src in
    let d = read_operand m dest in
    let result = interp_addq s d in
    write_operand m dest result;
    set_flags_add m s d result


  | (Subq, [src; dest]) ->
    let s = read_operand m src in
    let d = read_operand m dest in
    let result = interp_subq s d in
    write_operand m dest result;
    set_flags_sub m s d result


  | (Leaq, [src; dest]) ->
    let result = interp_leaq m src in
    write_operand m dest result


  | (Pushq, [src]) ->
    interp_pushq m (read_operand m src)


  | (Imulq, [src; dest]) ->
    let s = read_operand m src in
    let d = read_operand m dest in
    let result = interp_imulq s d in
    write_operand m dest result;
    set_flags_imul m s d result


  | (Shlq, [amt; dest]) ->
    let a = read_operand m amt in
    let d = read_operand m dest in
    let result = interp_shlq a d in
    write_operand m dest result;
    set_flags_shlq m a d result


  | (Xorq, [src; dest]) ->
    let s = read_operand m src in
    let d = read_operand m dest in
    let result = interp_xorq s d in
    write_operand m dest result;
    set_flags_logic m result


  | (Orq, [src; dest]) ->
    let s = read_operand m src in
    let d = read_operand m dest in
    let result = interp_orq s d in
    write_operand m dest result;
    set_flags_logic m result


  | (Andq, [src; dest]) ->
    let s = read_operand m src in
    let d = read_operand m dest in
    let result = interp_andq s d in
    write_operand m dest result;
    set_flags_logic m result


  | (Popq, [dest]) ->
    let v = interp_popq m in
    write_operand m dest v
  | _ -> failwith "step: unimplemented instruction"


  
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (p:prog) : exec =
failwith "assemble unimplemented"

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
failwith "load unimplemented"