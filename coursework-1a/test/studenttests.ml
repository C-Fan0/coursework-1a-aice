open Util.Assert
open X86
open Simulator
open Gradedtests
open Asm
(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)
(* NOTE: Your "submitted public test case" for Part III belongs over in the
   shared git submodule.
*)

let mov_ri =
  test_machine
  [
    InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
  ]

(*GCD using Euclidean algorithm with repeated subtraction for mod
   gcd(a, b):
     if b == 0 return a
     else return gcd(b, a mod b)
   mod(a, b) computed by repeated subtraction:
     while a >= b: a = a - b
     return a
   Arguments: a in %rdi, b in %rsi
   Result: in %rax
*)
let gcd_prog =
  [ text "mod_loop"
      [ Cmpq,  [~%Rsi; ~%Rdi]
      ; J Lt,  [~$$"mod_done"]
      ; Subq,  [~%Rsi; ~%Rdi]
      ; Jmp,   [~$$"mod_loop"]
      ]
  ; text "mod_done"
      [ Movq,  [~%Rdi; ~%Rax]
      ; Retq,  []
      ]
  ; text "gcd"
      [ Subq,  [~$8; ~%Rsp]
      ; Cmpq,  [~$0; ~%Rsi]
      ; J Eq,  [~$$"gcd_base"]
      ; Movq,  [~%Rsi; Ind2 Rsp]
      ; Callq, [~$$"mod_loop"]
      ; Movq,  [Ind2 Rsp; ~%Rdi]
      ; Movq,  [~%Rax; ~%Rsi]
      ; Addq,  [~$8; ~%Rsp]
      ; Callq, [~$$"gcd"]
      ; Retq,  []
      ]
  ; text "gcd_base"
      [ Movq,  [~%Rdi; ~%Rax]
      ; Addq,  [~$8; ~%Rsp]
      ; Retq,  []
      ]
  ; gtext "main"
      [ Movq,  [~$12; ~%Rdi]
      ; Movq,  [~$8;  ~%Rsi]
      ; Callq, [~$$"gcd"]
      ; Retq,  []
      ]
  ]

let gcd_with_inputs (a:int) (b:int) =
  [ text "mod_loop"
      [ Cmpq,  [~%Rsi; ~%Rdi]
      ; J Lt,  [~$$"mod_done"]
      ; Subq,  [~%Rsi; ~%Rdi]
      ; Jmp,   [~$$"mod_loop"]
      ]
  ; text "mod_done"
      [ Movq,  [~%Rdi; ~%Rax]
      ; Retq,  []
      ]
  ; text "gcd"
      [ Subq,  [~$8; ~%Rsp]
      ; Cmpq,  [~$0; ~%Rsi]
      ; J Eq,  [~$$"gcd_base"]
      ; Movq,  [~%Rsi; Ind2 Rsp]
      ; Callq, [~$$"mod_loop"]
      ; Movq,  [Ind2 Rsp; ~%Rdi]
      ; Movq,  [~%Rax; ~%Rsi]
      ; Addq,  [~$8; ~%Rsp]
      ; Callq, [~$$"gcd"]
      ; Retq,  []
      ]
  ; text "gcd_base"
      [ Movq,  [~%Rdi; ~%Rax]
      ; Addq,  [~$8; ~%Rsp]
      ; Retq,  []
      ]
  ; gtext "main"
      [ Movq,  [Imm (Lit (Int64.of_int a)); ~%Rdi]
      ; Movq,  [Imm (Lit (Int64.of_int b)); ~%Rsi]
      ; Callq, [~$$"gcd"]
      ; Retq,  []
      ]
  ]


let provided_tests : suite = [
  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
    (* gcd(12, 8) = 4 *)
    ("gcd_12_8",  program_test gcd_prog 4L);
    (* gcd(27, 9) = 9 — one is a multiple of the other *)
    ("gcd_27_9",  program_test (gcd_with_inputs 27 9) 9L);
    (* gcd(48, 18) = 6 *)make
    ("gcd_48_18", program_test (gcd_with_inputs 48 18) 6L);
  ]);

 
]
