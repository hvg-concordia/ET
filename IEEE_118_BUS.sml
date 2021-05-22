(* ========================================================================= *)
(* File Name: IEEE_118_BUS.sml	                                 	     *)
(*---------------------------------------------------------------------------*)
(*          Description: Reliability Analysis of a Standard IEEE 118-Bus     *)
(*                       Tranmission Network in a Smart Power Grid           *)
(*                                                                           *)
(*          HOL4-Kananaskis 13 		 			     	     *)
(*									     *)
(*	    Author : Mohamed Wagdy Abdelghany             		     *)
(*                                              			     *)
(* 	    Department of Electrical and Computer Engineering (ECE)          *)
(*	    Concordia University                                             *)
(*          Montreal, Quebec, Canada, 2021                                   *)
(*                                                                           *)
(* ========================================================================= *)

(*app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "real_probabilityTheory",
	  "numTheory", "dep_rewrite", "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "real_measureTheory","real_sigmaTheory",
	  "indexedListsTheory", "listLib", "bossLib", "metisLib", "realLib", "numLib", "combinTheory",
          "arithmeticTheory","boolTheory", " ETreeTheory", "listSyntax"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory indexedListsTheory
     listLib satTheory numTheory bossLib metisLib realLib numLib combinTheory arithmeticTheory
     boolTheory ETreeTheory listSyntax;
     
val _ = new_theory "IEEE_118_BUS";
(*--------------------------------------------------------------------------------------------------*)

    (*-----------------------------------------------------------------------------------------*)  
    (*   SYSTEM-LEVEL RELIABILITY ANALYSIS OF 118-BUS ELECTRICAL POWER TRANSMISSION  NETWORK   *)
    (*-----------------------------------------------------------------------------------------*)

(*--------------------------------------------------------------------------------------*)  
(*  Complete ET Models of Loads A, B and C (2048, 1024, 4096 Test Cases, Respectively)  *)
(*--------------------------------------------------------------------------------------*)

val IEEE_118_BUS_COMPLETE_ET_LOAD_A_DEF = Define
`IEEE_118_BUS_COMPLETE_ET_LOAD_A [TL1;TL2;TL3;TL4;TL5;TL6;TL7;TL8;TL9;TL10] [TL11] t p =
 ETREE (NODE (⊗Ν𝑳 (EVENT_TREE_LIST [↑ p TL11 t; ↓ p TL11 t]) (↑↓ p [TL1;TL2;TL3;TL4;TL5;TL6;TL7;TL8;TL9;TL10] t)))`;

val IEEE_118_BUS_COMPLETE_ET_LOAD_B_DEF = Define
`IEEE_118_BUS_COMPLETE_ET_LOAD_B [TL12;TL13;TL14;TL15;TL6;TL7;TL8;TL9;T20] [TL21] t p =
 ETREE (NODE (⊗Ν𝑳 (EVENT_TREE_LIST [↑ p TL21 t; ↓ p TL21 t]) (↑↓ p [TL12;TL13;TL14;TL15;TL6;TL7;TL8;TL9;T20] t)))`;

val IEEE_118_BUS_COMPLETE_ET_LOAD_C_DEF = Define
`IEEE_118_BUS_COMPLETE_ET_LOAD_C [TL22;TL23;TL24;TL25;TL26;TL27;TL28;TL29;TL30;TL31] [TL32] t p =
 ETREE (NODE (⊗Ν𝑳 (EVENT_TREE_LIST [↑ p TL32 t; ↓ p TL32 t]) (↑↓ p [TL22;TL23;TL24;TL25;TL26;TL27;TL28;TL29;TL30;TL31] t)))`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------*)  
(*  Load A Reliability Analysis   *)
(*--------------------------------*)

val IEEE_118_BUS_REDUCED_ET_LOAD_A_LOAD_SHEDDING_DEF = Define
`IEEE_118_BUS_REDUCED_ET_LOAD_A_LOAD_SHEDDING [TL1;TL2;TL3;TL4;TL5;TL6;TL7;TL8;TL9;TL10;TL11] t p =
 ETREE (NODE (EVENT_TREE_LIST (MAP (\a. ET_PATH p a)
([[↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↓  p TL10 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL6 t; ↓ p TL7 t; ↓ p TL8 t; ↑ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL6 t; ↓ p TL7 t; ↓ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↓ p TL7 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↓ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL6 t; ↓ p TL7 t];
  [↑ p TL1 t; ↑ p TL2 t; ↓ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↑ p TL7 t;  ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL8 t; ↑ p TL9 t; ↓ p TL11 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL8 t; ↓ p TL9 t; ↓ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↓  p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↓ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↓ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↓ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↓ p TL10 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↓ p TL10 t]]))))`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val IEEE_118_BUS_REDUCED_ET_LOAD_A_COMPLETE_FAILURE_DEF = Define
`IEEE_118_BUS_REDUCED_ET_LOAD_A_COMPLETE_FAILURE [TL1;TL2;TL3;TL4;TL5;TL6;TL7;TL8;TL9;TL10;TL11] t p =
 ETREE (NODE (EVENT_TREE_LIST (MAP (\a. ET_PATH p a)
([[↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↑ p TL6 t; ↓ p TL7 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t; ↓ p TL6 t; ↓ p TL7 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↓ p TL10 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↑ p TL6 t; ↓ p TL7 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↓ p TL10 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t];
  [↑ p TL1 t; ↑ p TL2 t; ↑ p TL3 t; ↓ p TL4 t; ↓ p TL6 t; ↓ p TL7 t];
  [↑ p TL1 t; ↑ p TL2 t; ↓ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL6 t; ↑ p TL7 t];
  [↑ p TL1 t; ↑ p TL2 t; ↓ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↑ p TL7 t;  ↑ p TL10 t; ↑ p TL11 t];
  [↑ p TL1 t; ↑ p TL2 t; ↓ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↑ p TL7 t;  ↓ p TL10 t];
  [↑ p TL1 t; ↑ p TL2 t; ↓ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL6 t; ↓ p TL7 t];
  [↑ p TL1 t; ↑ p TL2 t; ↓ p TL3 t; ↑ p TL4 t; ↓ p TL5 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL11 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↑ p TL8 t; ↓ p TL9 t; ↓ p TL10 t; ↑ p TL11 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↑ p TL5 t; ↓ p TL8 t; ↓ p TL9 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↑ p TL4 t; ↓ p TL5 t];
  [↑ p TL1 t; ↓ p TL2 t; ↑ p TL3 t; ↓ p TL4 t];
  [↑ p TL1 t; ↓ p TL2 t; ↓ p TL3 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↓ p TL10 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↓ p TL9 t; ↓ p TL10 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↓ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↓ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↓ p TL7 t; ↑ p TL8 t; ↓ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↑ p TL6 t; ↓ p TL7 t; ↓ p TL8 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↑ p TL7 t; ↑ p TL8 t; ↓ p TL9 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↑ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↑ p TL10 t; ↓ p TL11 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↑ p TL9 t; ↓ p TL10 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↑ p TL7 t; ↓ p TL8 t; ↓ p TL9 t];
  [↓ p TL1 t; ↑ p TL2 t; ↑ p TL3 t;  ↓ p TL6 t; ↓ p TL7 t];
  [↓ p TL1 t; ↑ p TL2 t; ↓ p TL3 t];
  [↓ p TL1 t; ↓ p TL2 t]]))))`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------*)   
(* Probability of Load Shedding 15 % of Load A    *)
(*------------------------------------------------*)

PROBABILITY ``IEEE_118_BUS_LOAD_SHEDDING_OF_LOAD_A``
``exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           (exp (-FR_TL5 * t) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) *
               ((1 − exp (-FR_TL9 * t)) *
                (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            (exp (-FR_TL5 * t) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               (exp (-FR_TL8 * t) *
                ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t)))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             (exp (-FR_TL5 * t) *
              (exp (-FR_TL6 * t) *
               (exp (-FR_TL7 * t) *
                ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              (exp (-FR_TL5 * t) *
               (exp (-FR_TL6 * t) *
                ((1 − exp (-FR_TL7 * t)) *
                 ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               (exp (-FR_TL5 * t) *
                (exp (-FR_TL6 * t) *
                 ((1 − exp (-FR_TL7 * t)) *
                  ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                (exp (-FR_TL5 * t) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 (exp (-FR_TL5 * t) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  (exp (-FR_TL5 * t) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   (exp (-FR_TL5 * t) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    (exp (-FR_TL5 * t) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    (exp (-FR_TL4 * t) *
                     ((1 − exp (-FR_TL5 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) * exp (-FR_TL9 * t)))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     (exp (-FR_TL4 * t) *
                      ((1 − exp (-FR_TL5 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         (exp (-FR_TL8 * t) * exp (-FR_TL9 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) *
                         (exp (-FR_TL7 * t) *
                          (exp (-FR_TL8 * t) *
                           ((1 − exp (-FR_TL9 * t)) *
                            (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             ((1 − exp (-FR_TL9 * t)) *
                              (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         ((1 − exp (-FR_TL3 * t)) *
                          (exp (-FR_TL4 * t) *
                           (exp (-FR_TL5 * t) *
                            (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          ((1 − exp (-FR_TL3 * t)) *
                           (exp (-FR_TL4 * t) *
                            (exp (-FR_TL5 * t) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          ((1 − exp (-FR_TL2 * t)) *
                           (exp (-FR_TL3 * t) *
                            (exp (-FR_TL4 * t) *
                             (exp (-FR_TL5 * t) *
                              (exp (-FR_TL8 * t) *
                               (exp (-FR_TL9 * t) * (1 − exp (-FR_TL11 * t)))))))) +
                          (exp (-FR_TL1 * t) *
                           ((1 − exp (-FR_TL2 * t)) *
                            (exp (-FR_TL3 * t) *
                             (exp (-FR_TL4 * t) *
                              (exp (-FR_TL5 * t) *
                               (exp (-FR_TL8 * t) *
                                ((1 − exp (-FR_TL9 * t)) *
                                 (exp (-FR_TL10 * t) *
                                  (1 − exp (-FR_TL11 * t))))))))) +
                           (exp (-FR_TL1 * t) *
                            ((1 − exp (-FR_TL2 * t)) *
                             (exp (-FR_TL3 * t) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL8 * t) *
                                 ((1 − exp (-FR_TL9 * t)) *
                                  ((1 − exp (-FR_TL10 * t)) *
                                   (1 − exp (-FR_TL11 * t))))))))) +
                            (exp (-FR_TL1 * t) *
                             ((1 − exp (-FR_TL2 * t)) *
                              (exp (-FR_TL3 * t) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL8 * t)) *
                                  (exp (-FR_TL9 * t) *
                                   (exp (-FR_TL10 * t) *
                                    (1 − exp (-FR_TL11 * t))))))))) +
                             ((1 − exp (-FR_TL1 * t)) *
                              (exp (-FR_TL2 * t) *
                               (exp (-FR_TL3 * t) *
                                (exp (-FR_TL6 * t) *
                                 (exp (-FR_TL7 * t) *
                                  (exp (-FR_TL8 * t) *
                                   (exp (-FR_TL9 * t) *
                                    (exp (-FR_TL10 * t) *
                                     (1 − exp (-FR_TL11 * t))))))))) +
                              ((1 − exp (-FR_TL1 * t)) *
                               (exp (-FR_TL2 * t) *
                                (exp (-FR_TL3 * t) *
                                 (exp (-FR_TL6 * t) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL8 * t) *
                                    ((1 − exp (-FR_TL9 * t)) *
                                     (exp (-FR_TL10 * t) *
                                      (1 − exp (-FR_TL11 * t))))))))) +
                               ((1 − exp (-FR_TL1 * t)) *
                                (exp (-FR_TL2 * t) *
                                 (exp (-FR_TL3 * t) *
                                  (exp (-FR_TL6 * t) *
                                   (exp (-FR_TL7 * t) *
                                    ((1 − exp (-FR_TL8 * t)) *
                                     (exp (-FR_TL9 * t) *
                                      (exp (-FR_TL10 * t) *
                                       (1 − exp (-FR_TL11 * t))))))))) +
                                ((1 − exp (-FR_TL1 * t)) *
                                 (exp (-FR_TL2 * t) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL6 * t) *
                                    (exp (-FR_TL7 * t) *
                                     ((1 − exp (-FR_TL8 * t)) *
                                      ((1 − exp (-FR_TL9 * t)) *
                                       (exp (-FR_TL10 * t) *
                                        (1 − exp (-FR_TL11 * t))))))))) +
                                 ((1 − exp (-FR_TL1 * t)) *
                                  (exp (-FR_TL2 * t) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL6 * t) *
                                     ((1 − exp (-FR_TL7 * t)) *
                                      (exp (-FR_TL8 * t) *
                                       (exp (-FR_TL9 * t) *
                                        (exp (-FR_TL10 * t) *
                                         (1 − exp (-FR_TL11 * t))))))))) +
                                  ((1 − exp (-FR_TL1 * t)) *
                                   (exp (-FR_TL2 * t) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL6 * t) *
                                      ((1 − exp (-FR_TL7 * t)) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         (exp (-FR_TL10 * t) *
                                          exp (-FR_TL11 * t)))))))) +
                                   ((1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL6 * t) *
                                       ((1 − exp (-FR_TL7 * t)) *
                                        (exp (-FR_TL8 * t) *
                                         ((1 − exp (-FR_TL9 * t)) *
                                          (1 − exp (-FR_TL10 * t)))))))) +
                                    (1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      ((1 − exp (-FR_TL6 * t)) *
                                       (exp (-FR_TL7 * t) *
                                        (exp (-FR_TL8 * t) *
                                         (exp (-FR_TL9 * t) *
                                          (1 − exp (-FR_TL10 * t)))))))))))))))))))))))))))))))))))) ``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)   
(* Probability of Load A Complete Failure    *)
(*-------------------------------------------*)

PROBABILITY ``IEEE_118_BUS_LOAD_A_COMPLETE_FAILURE``
    ``exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           ((1 − exp (-FR_TL5 * t)) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            ((1 − exp (-FR_TL5 * t)) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             ((1 − exp (-FR_TL5 * t)) *
              (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              ((1 − exp (-FR_TL5 * t)) *
               ((1 − exp (-FR_TL6 * t)) *
                (exp (-FR_TL7 * t) *
                 (exp (-FR_TL8 * t) *
                  (exp (-FR_TL9 * t) *
                   (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               ((1 − exp (-FR_TL5 * t)) *
                ((1 − exp (-FR_TL6 * t)) *
                 (exp (-FR_TL7 * t) *
                  (exp (-FR_TL8 * t) *
                   (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                ((1 − exp (-FR_TL5 * t)) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 ((1 − exp (-FR_TL5 * t)) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  ((1 − exp (-FR_TL5 * t)) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   ((1 − exp (-FR_TL5 * t)) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    ((1 − exp (-FR_TL5 * t)) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    ((1 − exp (-FR_TL4 * t)) *
                     (exp (-FR_TL6 * t) *
                      (exp (-FR_TL7 * t) *
                       (exp (-FR_TL8 * t) *
                        ((1 − exp (-FR_TL9 * t)) *
                         (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     ((1 − exp (-FR_TL4 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) *
                         ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t))))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t)))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         (exp (-FR_TL3 * t) *
                          ((1 − exp (-FR_TL4 * t)) *
                           ((1 − exp (-FR_TL6 * t)) *
                            (exp (-FR_TL7 * t) *
                             (exp (-FR_TL8 * t) *
                              ((1 − exp (-FR_TL9 * t)) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t)))))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          (exp (-FR_TL3 * t) *
                           ((1 − exp (-FR_TL4 * t)) *
                            ((1 − exp (-FR_TL6 * t)) *
                             (exp (-FR_TL7 * t) *
                              (exp (-FR_TL8 * t) *
                               ((1 − exp (-FR_TL9 * t)) *
                                (1 − exp (-FR_TL10 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          (exp (-FR_TL2 * t) *
                           (exp (-FR_TL3 * t) *
                            ((1 − exp (-FR_TL4 * t)) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                          (exp (-FR_TL1 * t) *
                           (exp (-FR_TL2 * t) *
                            (exp (-FR_TL3 * t) *
                             ((1 − exp (-FR_TL4 * t)) *
                              ((1 − exp (-FR_TL6 * t)) *
                               (1 − exp (-FR_TL7 * t)))))) +
                           (exp (-FR_TL1 * t) *
                            (exp (-FR_TL2 * t) *
                             ((1 − exp (-FR_TL3 * t)) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL6 * t) * exp (-FR_TL7 * t)))))) +
                            (exp (-FR_TL1 * t) *
                             (exp (-FR_TL2 * t) *
                              ((1 − exp (-FR_TL3 * t)) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL6 * t)) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL10 * t) * exp (-FR_TL11 * t)))))))) +
                             (exp (-FR_TL1 * t) *
                              (exp (-FR_TL2 * t) *
                               ((1 − exp (-FR_TL3 * t)) *
                                (exp (-FR_TL4 * t) *
                                 (exp (-FR_TL5 * t) *
                                  ((1 − exp (-FR_TL6 * t)) *
                                   (exp (-FR_TL7 * t) *
                                    (1 − exp (-FR_TL10 * t)))))))) +
                              (exp (-FR_TL1 * t) *
                               (exp (-FR_TL2 * t) *
                                ((1 − exp (-FR_TL3 * t)) *
                                 (exp (-FR_TL4 * t) *
                                  (exp (-FR_TL5 * t) *
                                   ((1 − exp (-FR_TL6 * t)) *
                                    (1 − exp (-FR_TL7 * t))))))) +
                               (exp (-FR_TL1 * t) *
                                (exp (-FR_TL2 * t) *
                                 ((1 − exp (-FR_TL3 * t)) *
                                  (exp (-FR_TL4 * t) *
                                   (1 − exp (-FR_TL5 * t))))) +
                                (exp (-FR_TL1 * t) *
                                 ((1 − exp (-FR_TL2 * t)) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL4 * t) *
                                    (exp (-FR_TL5 * t) *
                                     (exp (-FR_TL8 * t) *
                                      (exp (-FR_TL9 * t) *
                                       exp (-FR_TL11 * t))))))) +
                                 (exp (-FR_TL1 * t) *
                                  ((1 − exp (-FR_TL2 * t)) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL4 * t) *
                                     (exp (-FR_TL5 * t) *
                                      (exp (-FR_TL8 * t) *
                                       ((1 − exp (-FR_TL9 * t)) *
                                        (exp (-FR_TL10 * t) *
                                         exp (-FR_TL11 * t)))))))) +
                                  (exp (-FR_TL1 * t) *
                                   ((1 − exp (-FR_TL2 * t)) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL4 * t) *
                                      (exp (-FR_TL5 * t) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         ((1 − exp (-FR_TL10 * t)) *
                                          exp (-FR_TL11 * t)))))))) +
                                   (exp (-FR_TL1 * t) *
                                    ((1 − exp (-FR_TL2 * t)) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL4 * t) *
                                       (exp (-FR_TL5 * t) *
                                        ((1 − exp (-FR_TL8 * t)) *
                                         (exp (-FR_TL9 * t) *
                                          (exp (-FR_TL10 * t) *
                                           exp (-FR_TL11 * t)))))))) +
                                    (exp (-FR_TL1 * t) *
                                     ((1 − exp (-FR_TL2 * t)) *
                                      (exp (-FR_TL3 * t) *
                                       (exp (-FR_TL4 * t) *
                                        (exp (-FR_TL5 * t) *
                                         ((1 − exp (-FR_TL8 * t)) *
                                          (exp (-FR_TL9 * t) *
                                           (1 − exp (-FR_TL10 * t)))))))) +
                                     (exp (-FR_TL1 * t) *
                                      ((1 − exp (-FR_TL2 * t)) *
                                       (exp (-FR_TL3 * t) *
                                        (exp (-FR_TL4 * t) *
                                         (exp (-FR_TL5 * t) *
                                          ((1 − exp (-FR_TL8 * t)) *
                                           (1 − exp (-FR_TL9 * t))))))) +
                                      (exp (-FR_TL1 * t) *
                                       ((1 − exp (-FR_TL2 * t)) *
                                        (exp (-FR_TL3 * t) *
                                         (exp (-FR_TL4 * t) *
                                          (1 − exp (-FR_TL5 * t))))) +
                                       (exp (-FR_TL1 * t) *
                                        ((1 − exp (-FR_TL2 * t)) *
                                         (exp (-FR_TL3 * t) *
                                          (1 − exp (-FR_TL4 * t)))) +
                                        (exp (-FR_TL1 * t) *
                                         ((1 − exp (-FR_TL2 * t)) *
                                          (1 − exp (-FR_TL3 * t))) +
                                         ((1 − exp (-FR_TL1 * t)) *
                                          (exp (-FR_TL2 * t) *
                                           (exp (-FR_TL3 * t) *
                                            (exp (-FR_TL6 * t) *
                                             (exp (-FR_TL7 * t) *
                                              (exp (-FR_TL8 * t) *
                                               (exp (-FR_TL9 * t) *
                                                (exp (-FR_TL10 * t) *
                                                 exp (-FR_TL11 * t)))))))) +
                                          ((1 − exp (-FR_TL1 * t)) *
                                           (exp (-FR_TL2 * t) *
                                            (exp (-FR_TL3 * t) *
                                             (exp (-FR_TL6 * t) *
                                              (exp (-FR_TL7 * t) *
                                               (exp (-FR_TL8 * t) *
                                                (exp (-FR_TL9 * t) *
                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                           ((1 − exp (-FR_TL1 * t)) *
                                            (exp (-FR_TL2 * t) *
                                             (exp (-FR_TL3 * t) *
                                              (exp (-FR_TL6 * t) *
                                               (exp (-FR_TL7 * t) *
                                                (exp (-FR_TL8 * t) *
                                                 ((1 − exp (-FR_TL9 * t)) *
                                                  (exp (-FR_TL10 * t) *
                                                   exp (-FR_TL11 * t)))))))) +
                                            ((1 − exp (-FR_TL1 * t)) *
                                             (exp (-FR_TL2 * t) *
                                              (exp (-FR_TL3 * t) *
                                               (exp (-FR_TL6 * t) *
                                                (exp (-FR_TL7 * t) *
                                                 (exp (-FR_TL8 * t) *
                                                  ((1 − exp (-FR_TL9 * t)) *
                                                   (1 − exp (-FR_TL10 * t)))))))) +
                                             ((1 − exp (-FR_TL1 * t)) *
                                              (exp (-FR_TL2 * t) *
                                               (exp (-FR_TL3 * t) *
                                                (exp (-FR_TL6 * t) *
                                                 (exp (-FR_TL7 * t) *
                                                  ((1 − exp (-FR_TL8 * t)) *
                                                   (exp (-FR_TL9 * t) *
                                                    (exp (-FR_TL10 * t) *
                                                     exp (-FR_TL11 * t)))))))) +
                                              ((1 − exp (-FR_TL1 * t)) *
                                               (exp (-FR_TL2 * t) *
                                                (exp (-FR_TL3 * t) *
                                                 (exp (-FR_TL6 * t) *
                                                  (exp (-FR_TL7 * t) *
                                                   ((1 − exp (-FR_TL8 * t)) *
                                                    (exp (-FR_TL9 * t) *
                                                     (1 − exp (-FR_TL10 * t)))))))) +
                                               ((1 − exp (-FR_TL1 * t)) *
                                                (exp (-FR_TL2 * t) *
                                                 (exp (-FR_TL3 * t) *
                                                  (exp (-FR_TL6 * t) *
                                                   (exp (-FR_TL7 * t) *
                                                    ((1 − exp (-FR_TL8 * t)) *
                                                     ((1 − exp (-FR_TL9 * t)) *
                                                      (exp (-FR_TL10 * t) *
                                                       exp (-FR_TL11 * t)))))))) +
                                                ((1 − exp (-FR_TL1 * t)) *
                                                 (exp (-FR_TL2 * t) *
                                                  (exp (-FR_TL3 * t) *
                                                   (exp (-FR_TL6 * t) *
                                                    (exp (-FR_TL7 * t) *
                                                     ((1 − exp (-FR_TL8 * t)) *
                                                      ((1 − exp (-FR_TL9 * t)) *
                                                       (1 −
                                                        exp (-FR_TL10 * t)))))))) +
                                                 ((1 − exp (-FR_TL1 * t)) *
                                                  (exp (-FR_TL2 * t) *
                                                   (exp (-FR_TL3 * t) *
                                                    (exp (-FR_TL6 * t) *
                                                     ((1 − exp (-FR_TL7 * t)) *
                                                      (exp (-FR_TL8 * t) *
                                                       (exp (-FR_TL9 * t) *
                                                        (exp (-FR_TL10 * t) *
                                                         exp (-FR_TL11 * t)))))))) +
                                                  ((1 − exp (-FR_TL1 * t)) *
                                                   (exp (-FR_TL2 * t) *
                                                    (exp (-FR_TL3 * t) *
                                                     (exp (-FR_TL6 * t) *
                                                      ((1 − exp (-FR_TL7 * t)) *
                                                       (exp (-FR_TL8 * t) *
                                                        (exp (-FR_TL9 * t) *
                                                         (1 −  exp (-FR_TL10 * t)))))))) +
                                                   ((1 − exp (-FR_TL1 * t)) *
                                                    (exp (-FR_TL2 * t) *
                                                     (exp (-FR_TL3 * t) *
                                                      (exp (-FR_TL6 * t) *
                                                       ((1 − exp (-FR_TL7 * t)) *
                                                        (exp (-FR_TL8 * t) *
                                                         ((1 − exp (-FR_TL9 * t)) *
                                                          (exp (-FR_TL10 * t) *
                                                           (1 − exp (-FR_TL11 * t))))))))) +
                                                    ((1 − exp (-FR_TL1 * t)) *
                                                     (exp (-FR_TL2 * t) *
                                                      (exp (-FR_TL3 * t) *
                                                       (exp (-FR_TL6 * t) *
                                                        ((1 − exp (-FR_TL7 * t)) *
                                                         (1 − exp (-FR_TL8 * t)))))) +
                                                     ((1 − exp (-FR_TL1 * t)) *
                                                      (exp (-FR_TL2 * t) *
                                                       (exp (-FR_TL3 * t) *
                                                        ((1 − exp (-FR_TL6 * t)) *
                                                         (exp (-FR_TL7 * t) *
                                                          (exp (-FR_TL8 * t) *
                                                           (exp (-FR_TL9 * t) *
                                                            (exp (-FR_TL10 * t) *
                                                             exp (-FR_TL11 * t)))))))) +
                                                      ((1 − exp (-FR_TL1 * t)) *
                                                       (exp (-FR_TL2 * t) *
                                                        (exp (-FR_TL3 * t) *
                                                         ((1 − exp (-FR_TL6 * t)) *
                                                          (exp (-FR_TL7 * t) *
                                                           (exp (-FR_TL8 * t) *
                                                            (exp(-FR_TL9 * t) *
                                                             (exp (-FR_TL10 * t) *
                                                              (1 − exp (-FR_TL11 * t))))))))) +
                                                       ((1 − exp (-FR_TL1 * t)) *
                                                        (exp (-FR_TL2 * t) *
                                                         (exp (-FR_TL3 * t) *
                                                          ((1 − exp (-FR_TL6 * t)) *
                                                           (exp (-FR_TL7 * t) *
                                                            (exp (-FR_TL8 * t) *
                                                             (1 − exp (-FR_TL9 * t))))))) +
                                                        ((1 −  exp (-FR_TL1 * t)) *
                                                         (exp (-FR_TL2 * t) *
                                                          (exp (-FR_TL3 * t) *
                                                           ((1 − exp (-FR_TL6 * t)) *
                                                            (exp (-FR_TL7 * t) *
                                                             ((1 − exp (-FR_TL8 * t)) *
                                                              (exp (-FR_TL9 * t) *
                                                               (exp (-FR_TL10 * t) *
                                                                exp (-FR_TL11 * t)))))))) +
                                                         ((1 − exp (-FR_TL1 * t)) *
                                                          (exp (-FR_TL2 * t) *
                                                           (exp (-FR_TL3 * t) *
                                                            ((1 − exp (-FR_TL6 * t)) *
                                                             (exp (-FR_TL7 * t) *
                                                              ((1 − exp (-FR_TL8 * t)) *
                                                               (exp (-FR_TL9 * t) *
                                                                (exp (-FR_TL10 * t) *
                                                                 (1 −  exp (-FR_TL11 * t))))))))) +
                                                          ((1 − exp (-FR_TL1 * t)) *
                                                           (exp (-FR_TL2 * t) *
                                                            (exp (-FR_TL3 * t) *
                                                             ((1 − exp (-FR_TL6 * t)) *
                                                              (exp (-FR_TL7 * t) *
                                                               ((1 − exp (-FR_TL8 * t)) *
                                                                (exp (-FR_TL9 * t) *
                                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                                           ((1 − exp  (-FR_TL1 * t)) *
                                                            (exp (-FR_TL2 * t) *
                                                             (exp (-FR_TL3 * t) *
                                                              ((1 − exp (-FR_TL6 * t)) *
                                                               (exp (-FR_TL7 * t) *
                                                                ((1 − exp (-FR_TL8 * t)) *
                                                                 (1 − exp (-FR_TL9 * t))))))) +
                                                            ((1 − exp (-FR_TL1 * t)) *
                                                             (exp (-FR_TL2 * t) *
                                                              (exp (-FR_TL3 * t) *
                                                               ((1 − exp (-FR_TL6 * t)) *
                                                                (1 − exp  (-FR_TL7 * t))))) +
                                                             ((1 − exp (-FR_TL1 * t)) *
                                                              (exp (-FR_TL2 * t) *
                                                               (1 −  exp  (-FR_TL3 * t))) +
                                                              (1 − exp (-FR_TL1 * t)) *
                                                              (1 − exp (-FR_TL2 * t))))))))))))))))))))))))))))))))))))))))))))))))))))))))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------*)  
(*  Load B Reliability Analysis   *)
(*--------------------------------*)

val IEEE_118_BUS_REDUCED_ET_LOAD_B_LOAD_SHEDDING_DEF = Define
`IEEE_118_BUS_REDUCED_ET_LOAD_B_LOAD_SHEDDING [TL12; TL13; TL14; TL15; TL18; TL19; TL20; TL21; TL16; TL17] t p =
 ETREE (NODE (EVENT_TREE_LIST (MAP (\a. ET_PATH p a)
([[↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↑ p TL17 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↑ p TL17 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↑ p TL21 t; ↓ p TL16 t; ↓ p TL17 t]]))))`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val IEEE_118_BUS_REDUCED_ET_LOAD_B_COMPLETE_FAILURE_DEF = Define
`IEEE_118_BUS_REDUCED_ET_LOAD_B_COMPLETE_FAILURE [TL12; TL13; TL14; TL15; TL18; TL19; TL20; TL21; TL16; TL17] t p =
 ETREE (NODE (EVENT_TREE_LIST (MAP (\a. ET_PATH p a)
([[↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↓ p TL16 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↓ p TL20 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↓ p TL19 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↓ p TL16 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↑ p TL19 t; ↓ p TL20 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t; ↓ p TL19 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↓ p TL16 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↑ p TL19 t; ↓ p TL20 t];
  [↑ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t; ↓ p TL19 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↑ p TL16 t; ↓ p TL17 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t; ↓ p TL16 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↓ p TL20 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↓ p TL19 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↑ p TL15 t; ↓ p TL18 t];
  [↑ p TL12 t; ↑ p TL13 t; ↓ p TL14 t; ↓ p TL15 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↓ p TL20 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↓ p TL19 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t];
  [↑ p TL12 t; ↓ p TL13 t; ↑ p TL14 t; ↓ p TL15 t];
  [↑ p TL12 t; ↓ p TL13 t; ↓ p TL14 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↑ p TL20 t; ↓ p TL21 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↑ p TL19 t; ↓ p TL20 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↑ p TL18 t; ↓ p TL19 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↑ p TL15 t; ↓ p TL18 t];
  [↓ p TL12 t; ↑ p TL13 t; ↑ p TL14 t; ↓ p TL15 t];
  [↓ p TL12 t; ↑ p TL13 t; ↓ p TL14 t];
  [↓ p TL12 t; ↓ p TL13 t]]))))`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------*)   
(* Probability of Load Shedding 15 % of Load B    *)
(*------------------------------------------------*)

PROBABILITY ``IEEE_118_BUS_LOAD_SHEDDING_OF_LOAD_B``
``  exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              (exp (-FR_TL21 * t) *
               ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) *
                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             ((1 − exp (-FR_TL18 * t)) *
              (exp (-FR_TL19 * t) *
               (exp (-FR_TL20 * t) *
                (exp (-FR_TL21 * t) *
                 (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              ((1 − exp (-FR_TL18 * t)) *
               (exp (-FR_TL19 * t) *
                (exp (-FR_TL20 * t) *
                 (exp (-FR_TL21 * t) *
                  (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  (exp (-FR_TL21 * t) *
                   ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   (exp (-FR_TL21 * t) *
                    ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    ((1 − exp (-FR_TL21 * t)) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 ((1 − exp (-FR_TL15 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    (exp (-FR_TL21 * t) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     (exp (-FR_TL21 * t) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      (exp (-FR_TL21 * t) *
                       ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) *
                      (exp (-FR_TL20 * t) *
                       (exp (-FR_TL21 * t) *
                        ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t))))))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) *
                      (exp (-FR_TL19 * t) *
                       (exp (-FR_TL20 * t) *
                        ((1 − exp (-FR_TL21 * t)) *
                         (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          (exp (-FR_TL21 * t) *
                           (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           (exp (-FR_TL21 * t) *
                            (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) *
                           (exp (-FR_TL20 * t) *
                            (exp (-FR_TL21 * t) *
                             ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) *
                           (exp (-FR_TL19 * t) *
                            (exp (-FR_TL20 * t) *
                             (exp (-FR_TL21 * t) *
                              ((1 − exp (-FR_TL16 * t)) *
                               (1 − exp (-FR_TL17 * t)))))))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) *
                           (exp (-FR_TL18 * t) *
                            (exp (-FR_TL19 * t) *
                             (exp (-FR_TL20 * t) *
                              ((1 − exp (-FR_TL21 * t)) *
                               (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                        (exp (-FR_L12 * t) *
                         ((1 − exp (-FR_TL13 * t)) *
                          (exp (-FR_TL14 * t) *
                           (exp (-FR_TL15 * t) *
                            (exp (-FR_TL18 * t) *
                             (exp (-FR_TL19 * t) *
                              (exp (-FR_TL20 * t) *
                               (exp (-FR_TL21 * t) *
                                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (exp (-FR_TL21 * t) *
                                 (exp (-FR_TL16 * t) *
                                  (1 − exp (-FR_TL17 * t)))))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (exp (-FR_TL20 * t) *
                                 (exp (-FR_TL21 * t) *
                                  (exp (-FR_TL16 * t) *
                                   (1 − exp (-FR_TL17 * t)))))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (exp (-FR_TL19 * t) *
                                 (exp (-FR_TL20 * t) *
                                  (exp (-FR_TL21 * t) *
                                   (exp (-FR_TL16 * t) *
                                    (1 − exp (-FR_TL17 * t)))))))))) +
                            ((1 − exp (-FR_L12 * t)) *
                             (exp (-FR_TL13 * t) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (exp (-FR_TL18 * t) *
                                 (exp (-FR_TL19 * t) *
                                  (exp (-FR_TL20 * t) *
                                   (exp (-FR_TL21 * t) *
                                    (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                             ((1 − exp (-FR_L12 * t)) *
                              (exp (-FR_TL13 * t) *
                               (exp (-FR_TL14 * t) *
                                (exp (-FR_TL15 * t) *
                                 (exp (-FR_TL18 * t) *
                                  (exp (-FR_TL19 * t) *
                                   (exp (-FR_TL20 * t) *
                                    (exp (-FR_TL21 * t) *
                                     (exp (-FR_TL16 * t) *
                                      (1 − exp (-FR_TL17 * t)))))))))) +
                              ((1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       exp (-FR_TL17 * t))))))))) +
                               (1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       (1 − exp (-FR_TL17 * t)))))))))))))))))))))))))))))))))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)   
(* Probability of Load B Complete Failure    *)
(*-------------------------------------------*)

PROBABILITY ``IEEE_118_BUS_LOAD_B_COMPLETE_FAILURE``
``  exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              ((1 − exp (-FR_TL21 * t)) *
               (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             (exp (-FR_TL18 * t) *
              (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  ((1 − exp (-FR_TL21 * t)) *
                   (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 (exp (-FR_TL15 * t) *
                  ((1 − exp (-FR_TL18 * t)) * (1 − exp (-FR_TL19 * t)))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     ((1 − exp (-FR_TL21 * t)) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t)))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) * (1 − exp (-FR_TL19 * t))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          ((1 − exp (-FR_TL21 * t)) *
                           (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           ((1 − exp (-FR_TL21 * t)) *
                            (1 − exp (-FR_TL16 * t))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) * (1 − exp (-FR_TL18 * t))))) +
                        (exp (-FR_L12 * t) *
                         (exp (-FR_TL13 * t) *
                          ((1 − exp (-FR_TL14 * t)) *
                           (1 − exp (-FR_TL15 * t)))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (1 − exp (-FR_TL21 * t)))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (1 − exp (-FR_TL20 * t))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (1 − exp (-FR_TL19 * t)))))) +
                            (exp (-FR_L12 * t) *
                             ((1 − exp (-FR_TL13 * t)) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (1 − exp (-FR_TL18 * t))))) +
                             (exp (-FR_L12 * t) *
                              ((1 − exp (-FR_TL13 * t)) *
                               (exp (-FR_TL14 * t) *
                                (1 − exp (-FR_TL15 * t)))) +
                              (exp (-FR_L12 * t) *
                               ((1 − exp (-FR_TL13 * t)) *
                                (1 − exp (-FR_TL14 * t))) +
                               ((1 − exp (-FR_L12 * t)) *
                                (exp (-FR_TL13 * t) *
                                 (exp (-FR_TL14 * t) *
                                  (exp (-FR_TL15 * t) *
                                   (exp (-FR_TL18 * t) *
                                    (exp (-FR_TL19 * t) *
                                     (exp (-FR_TL20 * t) *
                                      (1 − exp (-FR_TL21 * t)))))))) +
                                ((1 − exp (-FR_L12 * t)) *
                                 (exp (-FR_TL13 * t) *
                                  (exp (-FR_TL14 * t) *
                                   (exp (-FR_TL15 * t) *
                                    (exp (-FR_TL18 * t) *
                                     (exp (-FR_TL19 * t) *
                                      (1 − exp (-FR_TL20 * t))))))) +
                                 ((1 − exp (-FR_L12 * t)) *
                                  (exp (-FR_TL13 * t) *
                                   (exp (-FR_TL14 * t) *
                                    (exp (-FR_TL15 * t) *
                                     (exp (-FR_TL18 * t) *
                                      (1 − exp (-FR_TL19 * t)))))) +
                                  ((1 − exp (-FR_L12 * t)) *
                                   (exp (-FR_TL13 * t) *
                                    (exp (-FR_TL14 * t) *
                                     (exp (-FR_TL15 * t) *
                                      (1 − exp (-FR_TL18 * t))))) +
                                   ((1 − exp (-FR_L12 * t)) *
                                    (exp (-FR_TL13 * t) *
                                     (exp (-FR_TL14 * t) *
                                      (1 − exp (-FR_TL15 * t)))) +
                                    ((1 − exp (-FR_L12 * t)) *
                                     (exp (-FR_TL13 * t) *
                                      (1 − exp (-FR_TL14 * t))) +
                                     (1 − exp (-FR_L12 * t)) *
                                     (1 − exp (-FR_TL13 * t)))))))))))))))))))))))))))))))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------*)  
(*  Load C Reliability Analysis   *)
(*--------------------------------*)

val IEEE_118_BUS_REDUCED_ET_LOAD_C_LOAD_SHEDDING_DEF = Define
`IEEE_118_BUS_REDUCED_ET_LOAD_C_LOAD_SHEDDING [TL22; TL23; TL24; TL25; TL26; TL27; TL28; TL29; TL30; TL31; TL32; TL33] t p =
 ETREE (NODE (EVENT_TREE_LIST (MAP (\a. ET_PATH p a)
([[↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓  p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓  p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↓ p TL31 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↓ p TL31 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↓ p TL30 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↓ p TL26 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↓ p TL25 t];
  [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
  [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
  [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t; ↑ p TL33 t]]))))`;    
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val IEEE_118_BUS_REDUCED_ET_LOAD_C_COMPLETE_FAILURE_DEF = Define
`IEEE_118_BUS_REDUCED_ET_LOAD_C_COMPLETE_FAILURE [TL22; TL23; TL24; TL25; TL26; TL27; TL28; TL29; TL30; TL31; TL32; TL33] t p =
 ETREE (NODE (EVENT_TREE_LIST (MAP (\a. ET_PATH p a)
([[↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t; ↑ p TL29 t; ↓ p TL30 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t; ↓ p TL29 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t; ↑ p TL29 t; ↓ p TL30 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t; ↓ p TL29 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↓ p TL26 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↓ p TL26 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↓ p TL26 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↓ p TL26 t; ↑ p TL29 t; ↓ p TL30 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↓ p TL26 t; ↓ p TL29 t];
  [↑ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↓ p TL25 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t];
  [↑ p TL22 t; ↑ p TL23 t; ↓ p TL24 t; ↑ p TL25 t; ↓ p TL26 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t; ↑ p TL32 t; ↑ p TL33 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t; ↓ p TL32 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↓ p TL31 t; ↓ p TL32 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↓ p TL31 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↓ p TL30 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↓ p TL26 t];
 [↑ p TL22 t; ↓ p TL23 t; ↑ p TL24 t; ↓ p TL25 t];
 [↑ p TL22 t; ↓ p TL23 t; ↓ p TL24 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↑ p TL30 t; ↓ p TL31 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↑ p TL31 t; ↓ p TL32 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↑ p TL29 t; ↓ p TL30 t; ↓ p TL31 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↑ p TL32 t; ↓ p TL33 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↑ p TL31 t; ↓ p TL32 t; ↓ p TL33 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↑ p TL30 t; ↓  p TL31 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↑ p TL28 t; ↓ p TL29 t; ↓ p TL30 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↑ p TL27 t; ↓ p TL28 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↑ p TL26 t; ↓ p TL27 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↑ p TL25 t; ↓ p TL26 t];
 [↓ p TL22 t; ↑ p TL23 t; ↑ p TL24 t; ↓ p TL25 t];
 [↓ p TL22 t; ↑ p TL23 t; ↓ p TL24 t];
 [↓ p TL22 t; ↓ p TL23 t]]))))`;    
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------*)   
(* Probability of Load Shedding 15 % of Load C    *)
(*------------------------------------------------*)

PROBABILITY ``IEEE_118_BUS_LOAD_SHEDDING_OF_LOAD_C``
``  exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             (exp (-FR_TL28 * t) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              (exp (-FR_TL28 * t) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               (exp (-FR_TL28 * t) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                (exp (-FR_TL28 * t) *
                 (exp (-FR_TL29 * t) *
                  ((1 − exp (-FR_TL30 * t)) *
                   (exp (-FR_TL31 * t) *
                    (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 (exp (-FR_TL28 * t) *
                  (exp (-FR_TL29 * t) *
                   ((1 − exp (-FR_TL30 * t)) *
                    (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 (exp (-FR_TL27 * t) *
                  (exp (-FR_TL28 * t) *
                   (exp (-FR_TL29 * t) *
                    ((1 − exp (-FR_TL30 * t)) * (1 − exp (-FR_TL31 * t)))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  (exp (-FR_TL27 * t) *
                   (exp (-FR_TL28 * t) *
                    ((1 − exp (-FR_TL29 * t)) *
                     (exp (-FR_TL30 * t) *
                      (exp (-FR_TL31 * t) *
                       (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   (exp (-FR_TL27 * t) *
                    (exp (-FR_TL28 * t) *
                     ((1 − exp (-FR_TL29 * t)) *
                      (exp (-FR_TL30 * t) *
                       (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    (exp (-FR_TL27 * t) *
                     (exp (-FR_TL28 * t) *
                      ((1 − exp (-FR_TL29 * t)) *
                       (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     (exp (-FR_TL27 * t) *
                      (exp (-FR_TL28 * t) *
                       ((1 − exp (-FR_TL29 * t)) * (1 − exp (-FR_TL30 * t))))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     (exp (-FR_TL26 * t) *
                      (exp (-FR_TL27 * t) *
                       ((1 − exp (-FR_TL28 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      (exp (-FR_TL26 * t) *
                       ((1 − exp (-FR_TL27 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t)))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      ((1 − exp (-FR_TL24 * t)) *
                       (exp (-FR_TL25 * t) *
                        (exp (-FR_TL26 * t) *
                         (exp (-FR_TL27 * t) *
                          (exp (-FR_TL28 * t) *
                           (exp (-FR_TL29 * t) *
                            (exp (-FR_TL30 * t) *
                             (exp (-FR_TL31 * t) *
                              (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       ((1 − exp (-FR_TL24 * t)) * (1 − exp (-FR_TL25 * t)))) +
                      (exp (-FR_TL22 * t) *
                       ((1 − exp (-FR_TL23 * t)) *
                        (exp (-FR_TL24 * t) *
                         (exp (-FR_TL25 * t) *
                          (exp (-FR_TL26 * t) *
                           (exp (-FR_TL27 * t) *
                            (exp (-FR_TL28 * t) *
                             (exp (-FR_TL29 * t) *
                              (exp (-FR_TL30 * t) *
                               (exp (-FR_TL31 * t) *
                                (1 − exp (-FR_TL32 * t))))))))))) +
                       (exp (-FR_TL22 * t) *
                        ((1 − exp (-FR_TL23 * t)) *
                         (exp (-FR_TL24 * t) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               ((1 − exp (-FR_TL30 * t)) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                        (exp (-FR_TL22 * t) *
                         ((1 − exp (-FR_TL23 * t)) *
                          (exp (-FR_TL24 * t) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               ((1 − exp (-FR_TL29 * t)) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                         ((1 − exp (-FR_TL22 * t)) *
                          (exp (-FR_TL23 * t) *
                           (exp (-FR_TL24 * t) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (exp (-FR_TL31 * t) *
                                   (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                          ((1 − exp (-FR_TL22 * t)) *
                           (exp (-FR_TL23 * t) *
                            (exp (-FR_TL24 * t) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  ((1 − exp (-FR_TL30 * t)) *
                                   (exp (-FR_TL31 * t) *
                                    (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                           ((1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     (exp (-FR_TL32 * t) *
                                      exp (-FR_TL33 * t))))))))))) +
                            (1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     ((1 − exp (-FR_TL32 * t)) *
                                      exp (-FR_TL33 * t))))))))))))))))))))))))))))))) ``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)   
(* Probability of Load C Complete Failure    *)
(*-------------------------------------------*)

PROBABILITY ``IEEE_118_BUS_LOAD_C_COMPLETE_FAILURE``
`` exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             ((1 − exp (-FR_TL28 * t)) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              ((1 − exp (-FR_TL28 * t)) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               ((1 − exp (-FR_TL28 * t)) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                ((1 − exp (-FR_TL28 * t)) *
                 (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 ((1 − exp (-FR_TL28 * t)) * (1 − exp (-FR_TL29 * t)))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 ((1 − exp (-FR_TL27 * t)) *
                  (exp (-FR_TL29 * t) *
                   (exp (-FR_TL30 * t) *
                    (exp (-FR_TL31 * t) *
                     (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t))))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  ((1 − exp (-FR_TL27 * t)) *
                   (exp (-FR_TL29 * t) *
                    (exp (-FR_TL30 * t) *
                     (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t)))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   ((1 − exp (-FR_TL27 * t)) *
                    (exp (-FR_TL29 * t) *
                     (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    ((1 − exp (-FR_TL27 * t)) *
                     (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t)))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     ((1 − exp (-FR_TL27 * t)) * (1 − exp (-FR_TL29 * t))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     ((1 − exp (-FR_TL26 * t)) *
                      (exp (-FR_TL29 * t) *
                       (exp (-FR_TL30 * t) *
                        (exp (-FR_TL31 * t) *
                         (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      ((1 − exp (-FR_TL26 * t)) *
                       (exp (-FR_TL29 * t) *
                        (exp (-FR_TL30 * t) *
                         (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      (exp (-FR_TL24 * t) *
                       (exp (-FR_TL25 * t) *
                        ((1 − exp (-FR_TL26 * t)) *
                         (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       (exp (-FR_TL24 * t) *
                        (exp (-FR_TL25 * t) *
                         ((1 − exp (-FR_TL26 * t)) *
                          (1 − exp (-FR_TL29 * t)))))) +
                      (exp (-FR_TL22 * t) *
                       (exp (-FR_TL23 * t) *
                        (exp (-FR_TL24 * t) * (1 − exp (-FR_TL25 * t)))) +
                       (exp (-FR_TL22 * t) *
                        (exp (-FR_TL23 * t) *
                         ((1 − exp (-FR_TL24 * t)) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               (exp (-FR_TL30 * t) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) *
                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                        (exp (-FR_TL22 * t) *
                         (exp (-FR_TL23 * t) *
                          ((1 − exp (-FR_TL24 * t)) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               (exp (-FR_TL29 * t) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (1 − exp (-FR_TL32 * t))))))))))) +
                         (exp (-FR_TL22 * t) *
                          (exp (-FR_TL23 * t) *
                           ((1 − exp (-FR_TL24 * t)) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (1 − exp (-FR_TL31 * t)))))))))) +
                          (exp (-FR_TL22 * t) *
                           (exp (-FR_TL23 * t) *
                            ((1 − exp (-FR_TL24 * t)) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  (1 − exp (-FR_TL30 * t))))))))) +
                           (exp (-FR_TL22 * t) *
                            (exp (-FR_TL23 * t) *
                             ((1 − exp (-FR_TL24 * t)) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  (1 − exp (-FR_TL29 * t)))))))) +
                            (exp (-FR_TL22 * t) *
                             (exp (-FR_TL23 * t) *
                              ((1 − exp (-FR_TL24 * t)) *
                               (exp (-FR_TL25 * t) *
                                (exp (-FR_TL26 * t) *
                                 (exp (-FR_TL27 * t) *
                                  (1 − exp (-FR_TL28 * t))))))) +
                             (exp (-FR_TL22 * t) *
                              (exp (-FR_TL23 * t) *
                               ((1 − exp (-FR_TL24 * t)) *
                                (exp (-FR_TL25 * t) *
                                 (exp (-FR_TL26 * t) *
                                  (1 − exp (-FR_TL27 * t)))))) +
                              (exp (-FR_TL22 * t) *
                               (exp (-FR_TL23 * t) *
                                ((1 − exp (-FR_TL24 * t)) *
                                 (exp (-FR_TL25 * t) *
                                  (1 − exp (-FR_TL26 * t))))) +
                               (exp (-FR_TL22 * t) *
                                ((1 − exp (-FR_TL23 * t)) *
                                 (exp (-FR_TL24 * t) *
                                  (exp (-FR_TL25 * t) *
                                   (exp (-FR_TL26 * t) *
                                    (exp (-FR_TL27 * t) *
                                     (exp (-FR_TL28 * t) *
                                      (exp (-FR_TL29 * t) *
                                       (exp (-FR_TL30 * t) *
                                        (exp (-FR_TL31 * t) *
                                         (exp (-FR_TL32 * t) *
                                          exp (-FR_TL33 * t))))))))))) +
                                (exp (-FR_TL22 * t) *
                                 ((1 − exp (-FR_TL23 * t)) *
                                  (exp (-FR_TL24 * t) *
                                   (exp (-FR_TL25 * t) *
                                    (exp (-FR_TL26 * t) *
                                     (exp (-FR_TL27 * t) *
                                      (exp (-FR_TL28 * t) *
                                       (exp (-FR_TL29 * t) *
                                        (exp (-FR_TL30 * t) *
                                         (exp (-FR_TL31 * t) *
                                          (exp (-FR_TL32 * t) *
                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                 (exp (-FR_TL22 * t) *
                                  ((1 − exp (-FR_TL23 * t)) *
                                   (exp (-FR_TL24 * t) *
                                    (exp (-FR_TL25 * t) *
                                     (exp (-FR_TL26 * t) *
                                      (exp (-FR_TL27 * t) *
                                       (exp (-FR_TL28 * t) *
                                        (exp (-FR_TL29 * t) *
                                         (exp (-FR_TL30 * t) *
                                          ((1 − exp (-FR_TL31 * t)) *
                                           (exp (-FR_TL32 * t) *
                                            exp (-FR_TL33 * t))))))))))) +
                                  (exp (-FR_TL22 * t) *
                                   ((1 − exp (-FR_TL23 * t)) *
                                    (exp (-FR_TL24 * t) *
                                     (exp (-FR_TL25 * t) *
                                      (exp (-FR_TL26 * t) *
                                       (exp (-FR_TL27 * t) *
                                        (exp (-FR_TL28 * t) *
                                         (exp (-FR_TL29 * t) *
                                          (exp (-FR_TL30 * t) *
                                           ((1 − exp (-FR_TL31 * t)) *
                                            (exp (-FR_TL32 * t) *
                                             (1 − exp (-FR_TL33 * t)))))))))))) +
                                   (exp (-FR_TL22 * t) *
                                    ((1 − exp (-FR_TL23 * t)) *
                                     (exp (-FR_TL24 * t) *
                                      (exp (-FR_TL25 * t) *
                                       (exp (-FR_TL26 * t) *
                                        (exp (-FR_TL27 * t) *
                                         (exp (-FR_TL28 * t) *
                                          (exp (-FR_TL29 * t) *
                                           (exp (-FR_TL30 * t) *
                                            ((1 − exp (-FR_TL31 * t)) *
                                             (1 − exp (-FR_TL32 * t))))))))))) +
                                    (exp (-FR_TL22 * t) *
                                     ((1 − exp (-FR_TL23 * t)) *
                                      (exp (-FR_TL24 * t) *
                                       (exp (-FR_TL25 * t) *
                                        (exp (-FR_TL26 * t) *
                                         (exp (-FR_TL27 * t) *
                                          (exp (-FR_TL28 * t) *
                                           (exp (-FR_TL29 * t) *
                                            ((1 − exp (-FR_TL30 * t)) *
                                             (exp (-FR_TL31 * t) *
                                              (exp (-FR_TL32 * t) *
                                               (1 − exp (-FR_TL33 * t)))))))))))) +
                                     (exp (-FR_TL22 * t) *
                                      ((1 − exp (-FR_TL23 * t)) *
                                       (exp (-FR_TL24 * t) *
                                        (exp (-FR_TL25 * t) *
                                         (exp (-FR_TL26 * t) *
                                          (exp (-FR_TL27 * t) *
                                           (exp (-FR_TL28 * t) *
                                            (exp (-FR_TL29 * t) *
                                             ((1 − exp (-FR_TL30 * t)) *
                                              (exp (-FR_TL31 * t) *
                                               (1 − exp (-FR_TL32 * t))))))))))) +
                                      (exp (-FR_TL22 * t) *
                                       ((1 − exp (-FR_TL23 * t)) *
                                        (exp (-FR_TL24 * t) *
                                         (exp (-FR_TL25 * t) *
                                          (exp (-FR_TL26 * t) *
                                           (exp (-FR_TL27 * t) *
                                            (exp (-FR_TL28 * t) *
                                             (exp (-FR_TL29 * t) *
                                              ((1 − exp (-FR_TL30 * t)) *
                                               ((1 − exp (-FR_TL31 * t)) *
                                                (1 − exp (-FR_TL32 * t))))))))))) +
                                       (exp (-FR_TL22 * t) *
                                        ((1 − exp (-FR_TL23 * t)) *
                                         (exp (-FR_TL24 * t) *
                                          (exp (-FR_TL25 * t) *
                                           (exp (-FR_TL26 * t) *
                                            (exp (-FR_TL27 * t) *
                                             (exp (-FR_TL28 * t) *
                                              ((1 − exp (-FR_TL29 * t)) *
                                               (exp (-FR_TL30 * t) *
                                                (exp (-FR_TL31 * t) *
                                                 (exp (-FR_TL32 * t) *
                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                        (exp (-FR_TL22 * t) *
                                         ((1 − exp (-FR_TL23 * t)) *
                                          (exp (-FR_TL24 * t) *
                                           (exp (-FR_TL25 * t) *
                                            (exp (-FR_TL26 * t) *
                                             (exp (-FR_TL27 * t) *
                                              (exp (-FR_TL28 * t) *
                                               ((1 − exp (-FR_TL29 * t)) *
                                                (exp (-FR_TL30 * t) *
                                                 (exp (-FR_TL31 * t) *
                                                  (1 − exp (-FR_TL32 * t))))))))))) +
                                         (exp (-FR_TL22 * t) *
                                          ((1 − exp (-FR_TL23 * t)) *
                                           (exp (-FR_TL24 * t) *
                                            (exp (-FR_TL25 * t) *
                                             (exp (-FR_TL26 * t) *
                                              (exp (-FR_TL27 * t) *
                                               (exp (-FR_TL28 * t) *
                                                ((1 − exp (-FR_TL29 * t)) *
                                                 (exp (-FR_TL30 * t) *
                                                  (1 − exp (-FR_TL31 * t)))))))))) +
                                          (exp (-FR_TL22 * t) *
                                           ((1 − exp (-FR_TL23 * t)) *
                                            (exp (-FR_TL24 * t) *
                                             (exp (-FR_TL25 * t) *
                                              (exp (-FR_TL26 * t) *
                                               (exp (-FR_TL27 * t) *
                                                (exp (-FR_TL28 * t) *
                                                 ((1 − exp (-FR_TL29 * t)) *
                                                  (1 − exp (-FR_TL30 * t))))))))) +
                                           (exp (-FR_TL22 * t) *
                                            ((1 − exp (-FR_TL23 * t)) *
                                             (exp (-FR_TL24 * t) *
                                              (exp (-FR_TL25 * t) *
                                               (exp (-FR_TL26 * t) *
                                                (exp (-FR_TL27 * t) *
                                                 (1 − exp (-FR_TL28 * t))))))) +
                                            (exp (-FR_TL22 * t) *
                                             ((1 − exp (-FR_TL23 * t)) *
                                              (exp (-FR_TL24 * t) *
                                               (exp (-FR_TL25 * t) *
                                                (exp (-FR_TL26 * t) *
                                                 (1 − exp (-FR_TL27 * t)))))) +
                                             (exp (-FR_TL22 * t) *
                                              ((1 − exp (-FR_TL23 * t)) *
                                               (exp (-FR_TL24 * t) *
                                                (exp (-FR_TL25 * t) *
                                                 (1 − exp (-FR_TL26 * t))))) +
                                              (exp (-FR_TL22 * t) *
                                               ((1 − exp (-FR_TL23 * t)) *
                                                (exp (-FR_TL24 * t) *
                                                 (1 − exp (-FR_TL25 * t)))) +
                                               (exp (-FR_TL22 * t) *
                                                ((1 − exp (-FR_TL23 * t)) *
                                                 (1 − exp (-FR_TL24 * t))) +
                                                ((1 − exp (-FR_TL22 * t)) *
                                                 (exp (-FR_TL23 * t) *
                                                  (exp (-FR_TL24 * t) *
                                                   (exp (-FR_TL25 * t) *
                                                    (exp (-FR_TL26 * t) *
                                                     (exp (-FR_TL27 * t) *
                                                      (exp (-FR_TL28 * t) *
                                                       (exp (-FR_TL29 * t) *
                                                        (exp (-FR_TL30 * t) *
                                                         (exp (-FR_TL31 * t) *
                                                          (exp (-FR_TL32 * t) *
                                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                                 ((1 − exp (-FR_TL22 * t)) *
                                                  (exp (-FR_TL23 * t) *
                                                   (exp (-FR_TL24 * t) *
                                                    (exp (-FR_TL25 * t) *
                                                     (exp (-FR_TL26 * t) *
                                                      (exp (-FR_TL27 * t) *
                                                       (exp (-FR_TL28 * t) *
                                                        (exp (-FR_TL29 * t) *
                                                         (exp (-FR_TL30 * t) *
                                                          (exp (-FR_TL31 * t) *
                                                           (1 − exp (-FR_TL32 * t))))))))))) +
                                                  ((1 − exp (-FR_TL22 * t)) *
                                                   (exp (-FR_TL23 * t) *
                                                    (exp (-FR_TL24 * t) *
                                                     (exp (-FR_TL25 * t) *
                                                      (exp (-FR_TL26 * t) *
                                                       (exp (-FR_TL27 * t) *
                                                        (exp (-FR_TL28 * t) *
                                                         (exp (-FR_TL29 * t) *
                                                          (exp (-FR_TL30 * t) *
                                                           (1 − exp (-FR_TL31 * t)))))))))) +
                                                   ((1 − exp (-FR_TL22 * t)) *
                                                    (exp (-FR_TL23 * t) *
                                                     (exp (-FR_TL24 * t) *
                                                      (exp (-FR_TL25 * t) *
                                                       (exp (-FR_TL26 * t) *
                                                        (exp (-FR_TL27 * t) *
                                                         (exp (-FR_TL28 * t) *
                                                          (exp (-FR_TL29 * t) *
                                                           ((1 − exp (-FR_TL30 * t)) *
                                                            (exp (-FR_TL31 * t) *
                                                             (exp (-FR_TL32 * t) *
                                                              (1 − exp (-FR_TL33 * t)))))))))))) +
                                                    ((1 − exp (-FR_TL22 * t)) *
                                                     (exp (-FR_TL23 * t) *
                                                      (exp (-FR_TL24 * t) *
                                                       (exp (-FR_TL25 * t) *
                                                        (exp (-FR_TL26 * t) *
                                                         (exp (-FR_TL27 * t) *
                                                          (exp (-FR_TL28 * t) *
                                                           (exp  (-FR_TL29 * t) *
                                                            ((1 − exp (-FR_TL30 * t)) *
                                                             (exp (-FR_TL31 * t) *
                                                              (1 −  exp (-FR_TL32 * t))))))))))) +
                                                     ((1 − exp (-FR_TL22 * t)) *
                                                      (exp (-FR_TL23 * t) *
                                                       (exp (-FR_TL24 * t) *
                                                        (exp (-FR_TL25 * t) *
                                                         (exp (-FR_TL26 * t) *
                                                          (exp (-FR_TL27 * t) *
                                                           (exp (-FR_TL28 * t) *
                                                            (exp (-FR_TL29 * t) *
                                                             ((1 −  exp (-FR_TL30 * t)) *
                                                              (1 − exp (-FR_TL31 * t)))))))))) +
                                                      ((1 − exp (-FR_TL22 * t)) *
                                                       (exp (-FR_TL23 * t) *
                                                        (exp (-FR_TL24 * t) *
                                                         (exp (-FR_TL25 * t) *
                                                          (exp (-FR_TL26 * t) *
                                                           (exp (-FR_TL27 * t) *
                                                            (exp  (-FR_TL28 * t) *
                                                             ((1 − exp (-FR_TL29 * t)) *
                                                              (exp (-FR_TL30 * t) *
                                                               (exp (-FR_TL31 * t) *
                                                                (exp (-FR_TL32 * t) *
                                                                 (1 − exp (-FR_TL33 * t)))))))))))) +
                                                       ((1 − exp (-FR_TL22 * t)) *
                                                        (exp (-FR_TL23 * t) *
                                                         (exp (-FR_TL24 * t) *
                                                          (exp (-FR_TL25 * t) *
                                                           (exp (-FR_TL26 * t) *
                                                            (exp  (-FR_TL27 * t) *
                                                             (exp (-FR_TL28 * t) *
                                                              ((1 −  exp (-FR_TL29 * t)) *
                                                               (exp (-FR_TL30 * t) *
                                                                (exp (-FR_TL31 * t) *
                                                                 ((1 − exp (-FR_TL32 * t)) *
                                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                                        ((1 − exp (-FR_TL22 * t)) *
                                                         (exp (-FR_TL23 * t) *
                                                          (exp (-FR_TL24 * t) *
                                                           (exp (-FR_TL25 * t) *
                                                            (exp (-FR_TL26 * t) *
                                                             (exp (-FR_TL27 * t) *
                                                              (exp (-FR_TL28 * t) *
                                                               ((1 − exp (-FR_TL29 * t)) *
                                                                (exp (-FR_TL30 * t) *
                                                                 (1 − exp (-FR_TL31 * t)))))))))) +
                                                         ((1 − exp (-FR_TL22 * t)) *
                                                          (exp (-FR_TL23 * t) *
                                                           (exp (-FR_TL24 * t) *
                                                            (exp (-FR_TL25 * t) *
                                                             (exp (-FR_TL26 * t) *
                                                              (exp (-FR_TL27 * t) *
                                                               (exp (-FR_TL28 * t) *
                                                                ((1 − exp (-FR_TL29 * t)) *
                                                                 (1 −  exp (-FR_TL30 * t))))))))) +
                                                          ((1 − exp (-FR_TL22 * t)) *
                                                           (exp (-FR_TL23 * t) *
                                                            (exp (-FR_TL24 * t) *
                                                             (exp (-FR_TL25 * t) *
                                                              (exp (-FR_TL26 * t) *
                                                               (exp (-FR_TL27 * t) *
                                                                (1 − exp (-FR_TL28 * t))))))) +
                                                           ((1 − exp (-FR_TL22 * t)) *
                                                            (exp (-FR_TL23 * t) *
                                                             (exp (-FR_TL24 * t) *
                                                              (exp (-FR_TL25 * t) *
                                                               (exp (-FR_TL26 * t) *
                                                                (1 −  exp (-FR_TL27 * t)))))) +
                                                            ((1 − exp (-FR_TL22 * t)) *
                                                             (exp (-FR_TL23 * t) *
                                                              (exp (-FR_TL24 * t) *
                                                               (exp (-FR_TL25 * t) *
                                                                (1 − exp (-FR_TL26 * t))))) +
                                                             ((1 − exp (-FR_TL22 * t)) *
                                                              (exp (-FR_TL23 * t) *
                                                               (exp  (-FR_TL24 * t) *
                                                                (1 −exp (-FR_TL25 * t)))) +
                                                              ((1 − exp (-FR_TL22 * t)) *
                                                               (exp (-FR_TL23 * t) *
                                                                (1 −  exp (-FR_TL24 * t))) +
                                                               (1 − exp (-FR_TL22 * t)) *
                                                               (1 − exp (-FR_TL23 * t))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------*)  
(*    SAIFI Reliability Index     *)
(*--------------------------------*)

SAIFI
``((exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           (exp (-FR_TL5 * t) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) *
               ((1 − exp (-FR_TL9 * t)) *
                (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            (exp (-FR_TL5 * t) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               (exp (-FR_TL8 * t) *
                ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t)))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             (exp (-FR_TL5 * t) *
              (exp (-FR_TL6 * t) *
               (exp (-FR_TL7 * t) *
                ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              (exp (-FR_TL5 * t) *
               (exp (-FR_TL6 * t) *
                ((1 − exp (-FR_TL7 * t)) *
                 ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               (exp (-FR_TL5 * t) *
                (exp (-FR_TL6 * t) *
                 ((1 − exp (-FR_TL7 * t)) *
                  ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                (exp (-FR_TL5 * t) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 (exp (-FR_TL5 * t) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  (exp (-FR_TL5 * t) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   (exp (-FR_TL5 * t) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    (exp (-FR_TL5 * t) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    (exp (-FR_TL4 * t) *
                     ((1 − exp (-FR_TL5 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) * exp (-FR_TL9 * t)))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     (exp (-FR_TL4 * t) *
                      ((1 − exp (-FR_TL5 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         (exp (-FR_TL8 * t) * exp (-FR_TL9 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) *
                         (exp (-FR_TL7 * t) *
                          (exp (-FR_TL8 * t) *
                           ((1 − exp (-FR_TL9 * t)) *
                            (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             ((1 − exp (-FR_TL9 * t)) *
                              (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         ((1 − exp (-FR_TL3 * t)) *
                          (exp (-FR_TL4 * t) *
                           (exp (-FR_TL5 * t) *
                            (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          ((1 − exp (-FR_TL3 * t)) *
                           (exp (-FR_TL4 * t) *
                            (exp (-FR_TL5 * t) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          ((1 − exp (-FR_TL2 * t)) *
                           (exp (-FR_TL3 * t) *
                            (exp (-FR_TL4 * t) *
                             (exp (-FR_TL5 * t) *
                              (exp (-FR_TL8 * t) *
                               (exp (-FR_TL9 * t) * (1 − exp (-FR_TL11 * t)))))))) +
                          (exp (-FR_TL1 * t) *
                           ((1 − exp (-FR_TL2 * t)) *
                            (exp (-FR_TL3 * t) *
                             (exp (-FR_TL4 * t) *
                              (exp (-FR_TL5 * t) *
                               (exp (-FR_TL8 * t) *
                                ((1 − exp (-FR_TL9 * t)) *
                                 (exp (-FR_TL10 * t) *
                                  (1 − exp (-FR_TL11 * t))))))))) +
                           (exp (-FR_TL1 * t) *
                            ((1 − exp (-FR_TL2 * t)) *
                             (exp (-FR_TL3 * t) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL8 * t) *
                                 ((1 − exp (-FR_TL9 * t)) *
                                  ((1 − exp (-FR_TL10 * t)) *
                                   (1 − exp (-FR_TL11 * t))))))))) +
                            (exp (-FR_TL1 * t) *
                             ((1 − exp (-FR_TL2 * t)) *
                              (exp (-FR_TL3 * t) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL8 * t)) *
                                  (exp (-FR_TL9 * t) *
                                   (exp (-FR_TL10 * t) *
                                    (1 − exp (-FR_TL11 * t))))))))) +
                             ((1 − exp (-FR_TL1 * t)) *
                              (exp (-FR_TL2 * t) *
                               (exp (-FR_TL3 * t) *
                                (exp (-FR_TL6 * t) *
                                 (exp (-FR_TL7 * t) *
                                  (exp (-FR_TL8 * t) *
                                   (exp (-FR_TL9 * t) *
                                    (exp (-FR_TL10 * t) *
                                     (1 − exp (-FR_TL11 * t))))))))) +
                              ((1 − exp (-FR_TL1 * t)) *
                               (exp (-FR_TL2 * t) *
                                (exp (-FR_TL3 * t) *
                                 (exp (-FR_TL6 * t) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL8 * t) *
                                    ((1 − exp (-FR_TL9 * t)) *
                                     (exp (-FR_TL10 * t) *
                                      (1 − exp (-FR_TL11 * t))))))))) +
                               ((1 − exp (-FR_TL1 * t)) *
                                (exp (-FR_TL2 * t) *
                                 (exp (-FR_TL3 * t) *
                                  (exp (-FR_TL6 * t) *
                                   (exp (-FR_TL7 * t) *
                                    ((1 − exp (-FR_TL8 * t)) *
                                     (exp (-FR_TL9 * t) *
                                      (exp (-FR_TL10 * t) *
                                       (1 − exp (-FR_TL11 * t))))))))) +
                                ((1 − exp (-FR_TL1 * t)) *
                                 (exp (-FR_TL2 * t) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL6 * t) *
                                    (exp (-FR_TL7 * t) *
                                     ((1 − exp (-FR_TL8 * t)) *
                                      ((1 − exp (-FR_TL9 * t)) *
                                       (exp (-FR_TL10 * t) *
                                        (1 − exp (-FR_TL11 * t))))))))) +
                                 ((1 − exp (-FR_TL1 * t)) *
                                  (exp (-FR_TL2 * t) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL6 * t) *
                                     ((1 − exp (-FR_TL7 * t)) *
                                      (exp (-FR_TL8 * t) *
                                       (exp (-FR_TL9 * t) *
                                        (exp (-FR_TL10 * t) *
                                         (1 − exp (-FR_TL11 * t))))))))) +
                                  ((1 − exp (-FR_TL1 * t)) *
                                   (exp (-FR_TL2 * t) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL6 * t) *
                                      ((1 − exp (-FR_TL7 * t)) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         (exp (-FR_TL10 * t) *
                                          exp (-FR_TL11 * t)))))))) +
                                   ((1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL6 * t) *
                                       ((1 − exp (-FR_TL7 * t)) *
                                        (exp (-FR_TL8 * t) *
                                         ((1 − exp (-FR_TL9 * t)) *
                                          (1 − exp (-FR_TL10 * t)))))))) +
                                    (1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      ((1 − exp (-FR_TL6 * t)) *
                                       (exp (-FR_TL7 * t) *
                                        (exp (-FR_TL8 * t) *
                                         (exp (-FR_TL9 * t) *
                                          (1 − exp (-FR_TL10 * t))))))))))))))))))))))))))))))))))))) * 0.15 * CN_A +
        (exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           ((1 − exp (-FR_TL5 * t)) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            ((1 − exp (-FR_TL5 * t)) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             ((1 − exp (-FR_TL5 * t)) *
              (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              ((1 − exp (-FR_TL5 * t)) *
               ((1 − exp (-FR_TL6 * t)) *
                (exp (-FR_TL7 * t) *
                 (exp (-FR_TL8 * t) *
                  (exp (-FR_TL9 * t) *
                   (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               ((1 − exp (-FR_TL5 * t)) *
                ((1 − exp (-FR_TL6 * t)) *
                 (exp (-FR_TL7 * t) *
                  (exp (-FR_TL8 * t) *
                   (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                ((1 − exp (-FR_TL5 * t)) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 ((1 − exp (-FR_TL5 * t)) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  ((1 − exp (-FR_TL5 * t)) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   ((1 − exp (-FR_TL5 * t)) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    ((1 − exp (-FR_TL5 * t)) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    ((1 − exp (-FR_TL4 * t)) *
                     (exp (-FR_TL6 * t) *
                      (exp (-FR_TL7 * t) *
                       (exp (-FR_TL8 * t) *
                        ((1 − exp (-FR_TL9 * t)) *
                         (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     ((1 − exp (-FR_TL4 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) *
                         ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t))))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t)))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         (exp (-FR_TL3 * t) *
                          ((1 − exp (-FR_TL4 * t)) *
                           ((1 − exp (-FR_TL6 * t)) *
                            (exp (-FR_TL7 * t) *
                             (exp (-FR_TL8 * t) *
                              ((1 − exp (-FR_TL9 * t)) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t)))))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          (exp (-FR_TL3 * t) *
                           ((1 − exp (-FR_TL4 * t)) *
                            ((1 − exp (-FR_TL6 * t)) *
                             (exp (-FR_TL7 * t) *
                              (exp (-FR_TL8 * t) *
                               ((1 − exp (-FR_TL9 * t)) *
                                (1 − exp (-FR_TL10 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          (exp (-FR_TL2 * t) *
                           (exp (-FR_TL3 * t) *
                            ((1 − exp (-FR_TL4 * t)) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                          (exp (-FR_TL1 * t) *
                           (exp (-FR_TL2 * t) *
                            (exp (-FR_TL3 * t) *
                             ((1 − exp (-FR_TL4 * t)) *
                              ((1 − exp (-FR_TL6 * t)) *
                               (1 − exp (-FR_TL7 * t)))))) +
                           (exp (-FR_TL1 * t) *
                            (exp (-FR_TL2 * t) *
                             ((1 − exp (-FR_TL3 * t)) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL6 * t) * exp (-FR_TL7 * t)))))) +
                            (exp (-FR_TL1 * t) *
                             (exp (-FR_TL2 * t) *
                              ((1 − exp (-FR_TL3 * t)) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL6 * t)) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL10 * t) * exp (-FR_TL11 * t)))))))) +
                             (exp (-FR_TL1 * t) *
                              (exp (-FR_TL2 * t) *
                               ((1 − exp (-FR_TL3 * t)) *
                                (exp (-FR_TL4 * t) *
                                 (exp (-FR_TL5 * t) *
                                  ((1 − exp (-FR_TL6 * t)) *
                                   (exp (-FR_TL7 * t) *
                                    (1 − exp (-FR_TL10 * t)))))))) +
                              (exp (-FR_TL1 * t) *
                               (exp (-FR_TL2 * t) *
                                ((1 − exp (-FR_TL3 * t)) *
                                 (exp (-FR_TL4 * t) *
                                  (exp (-FR_TL5 * t) *
                                   ((1 − exp (-FR_TL6 * t)) *
                                    (1 − exp (-FR_TL7 * t))))))) +
                               (exp (-FR_TL1 * t) *
                                (exp (-FR_TL2 * t) *
                                 ((1 − exp (-FR_TL3 * t)) *
                                  (exp (-FR_TL4 * t) *
                                   (1 − exp (-FR_TL5 * t))))) +
                                (exp (-FR_TL1 * t) *
                                 ((1 − exp (-FR_TL2 * t)) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL4 * t) *
                                    (exp (-FR_TL5 * t) *
                                     (exp (-FR_TL8 * t) *
                                      (exp (-FR_TL9 * t) *
                                       exp (-FR_TL11 * t))))))) +
                                 (exp (-FR_TL1 * t) *
                                  ((1 − exp (-FR_TL2 * t)) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL4 * t) *
                                     (exp (-FR_TL5 * t) *
                                      (exp (-FR_TL8 * t) *
                                       ((1 − exp (-FR_TL9 * t)) *
                                        (exp (-FR_TL10 * t) *
                                         exp (-FR_TL11 * t)))))))) +
                                  (exp (-FR_TL1 * t) *
                                   ((1 − exp (-FR_TL2 * t)) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL4 * t) *
                                      (exp (-FR_TL5 * t) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         ((1 − exp (-FR_TL10 * t)) *
                                          exp (-FR_TL11 * t)))))))) +
                                   (exp (-FR_TL1 * t) *
                                    ((1 − exp (-FR_TL2 * t)) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL4 * t) *
                                       (exp (-FR_TL5 * t) *
                                        ((1 − exp (-FR_TL8 * t)) *
                                         (exp (-FR_TL9 * t) *
                                          (exp (-FR_TL10 * t) *
                                           exp (-FR_TL11 * t)))))))) +
                                    (exp (-FR_TL1 * t) *
                                     ((1 − exp (-FR_TL2 * t)) *
                                      (exp (-FR_TL3 * t) *
                                       (exp (-FR_TL4 * t) *
                                        (exp (-FR_TL5 * t) *
                                         ((1 − exp (-FR_TL8 * t)) *
                                          (exp (-FR_TL9 * t) *
                                           (1 − exp (-FR_TL10 * t)))))))) +
                                     (exp (-FR_TL1 * t) *
                                      ((1 − exp (-FR_TL2 * t)) *
                                       (exp (-FR_TL3 * t) *
                                        (exp (-FR_TL4 * t) *
                                         (exp (-FR_TL5 * t) *
                                          ((1 − exp (-FR_TL8 * t)) *
                                           (1 − exp (-FR_TL9 * t))))))) +
                                      (exp (-FR_TL1 * t) *
                                       ((1 − exp (-FR_TL2 * t)) *
                                        (exp (-FR_TL3 * t) *
                                         (exp (-FR_TL4 * t) *
                                          (1 − exp (-FR_TL5 * t))))) +
                                       (exp (-FR_TL1 * t) *
                                        ((1 − exp (-FR_TL2 * t)) *
                                         (exp (-FR_TL3 * t) *
                                          (1 − exp (-FR_TL4 * t)))) +
                                        (exp (-FR_TL1 * t) *
                                         ((1 − exp (-FR_TL2 * t)) *
                                          (1 − exp (-FR_TL3 * t))) +
                                         ((1 − exp (-FR_TL1 * t)) *
                                          (exp (-FR_TL2 * t) *
                                           (exp (-FR_TL3 * t) *
                                            (exp (-FR_TL6 * t) *
                                             (exp (-FR_TL7 * t) *
                                              (exp (-FR_TL8 * t) *
                                               (exp (-FR_TL9 * t) *
                                                (exp (-FR_TL10 * t) *
                                                 exp (-FR_TL11 * t)))))))) +
                                          ((1 − exp (-FR_TL1 * t)) *
                                           (exp (-FR_TL2 * t) *
                                            (exp (-FR_TL3 * t) *
                                             (exp (-FR_TL6 * t) *
                                              (exp (-FR_TL7 * t) *
                                               (exp (-FR_TL8 * t) *
                                                (exp (-FR_TL9 * t) *
                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                           ((1 − exp (-FR_TL1 * t)) *
                                            (exp (-FR_TL2 * t) *
                                             (exp (-FR_TL3 * t) *
                                              (exp (-FR_TL6 * t) *
                                               (exp (-FR_TL7 * t) *
                                                (exp (-FR_TL8 * t) *
                                                 ((1 − exp (-FR_TL9 * t)) *
                                                  (exp (-FR_TL10 * t) *
                                                   exp (-FR_TL11 * t)))))))) +
                                            ((1 − exp (-FR_TL1 * t)) *
                                             (exp (-FR_TL2 * t) *
                                              (exp (-FR_TL3 * t) *
                                               (exp (-FR_TL6 * t) *
                                                (exp (-FR_TL7 * t) *
                                                 (exp (-FR_TL8 * t) *
                                                  ((1 − exp (-FR_TL9 * t)) *
                                                   (1 − exp (-FR_TL10 * t)))))))) +
                                             ((1 − exp (-FR_TL1 * t)) *
                                              (exp (-FR_TL2 * t) *
                                               (exp (-FR_TL3 * t) *
                                                (exp (-FR_TL6 * t) *
                                                 (exp (-FR_TL7 * t) *
                                                  ((1 − exp (-FR_TL8 * t)) *
                                                   (exp (-FR_TL9 * t) *
                                                    (exp (-FR_TL10 * t) *
                                                     exp (-FR_TL11 * t)))))))) +
                                              ((1 − exp (-FR_TL1 * t)) *
                                               (exp (-FR_TL2 * t) *
                                                (exp (-FR_TL3 * t) *
                                                 (exp (-FR_TL6 * t) *
                                                  (exp (-FR_TL7 * t) *
                                                   ((1 − exp (-FR_TL8 * t)) *
                                                    (exp (-FR_TL9 * t) *
                                                     (1 − exp (-FR_TL10 * t)))))))) +
                                               ((1 − exp (-FR_TL1 * t)) *
                                                (exp (-FR_TL2 * t) *
                                                 (exp (-FR_TL3 * t) *
                                                  (exp (-FR_TL6 * t) *
                                                   (exp (-FR_TL7 * t) *
                                                    ((1 − exp (-FR_TL8 * t)) *
                                                     ((1 − exp (-FR_TL9 * t)) *
                                                      (exp (-FR_TL10 * t) *
                                                       exp (-FR_TL11 * t)))))))) +
                                                ((1 − exp (-FR_TL1 * t)) *
                                                 (exp (-FR_TL2 * t) *
                                                  (exp (-FR_TL3 * t) *
                                                   (exp (-FR_TL6 * t) *
                                                    (exp (-FR_TL7 * t) *
                                                     ((1 − exp (-FR_TL8 * t)) *
                                                      ((1 − exp (-FR_TL9 * t)) *
                                                       (1 −
                                                        exp (-FR_TL10 * t)))))))) +
                                                 ((1 − exp (-FR_TL1 * t)) *
                                                  (exp (-FR_TL2 * t) *
                                                   (exp (-FR_TL3 * t) *
                                                    (exp (-FR_TL6 * t) *
                                                     ((1 − exp (-FR_TL7 * t)) *
                                                      (exp (-FR_TL8 * t) *
                                                       (exp (-FR_TL9 * t) *
                                                        (exp (-FR_TL10 * t) *
                                                         exp (-FR_TL11 * t)))))))) +
                                                  ((1 − exp (-FR_TL1 * t)) *
                                                   (exp (-FR_TL2 * t) *
                                                    (exp (-FR_TL3 * t) *
                                                     (exp (-FR_TL6 * t) *
                                                      ((1 − exp (-FR_TL7 * t)) *
                                                       (exp (-FR_TL8 * t) *
                                                        (exp (-FR_TL9 * t) *
                                                         (1 −  exp (-FR_TL10 * t)))))))) +
                                                   ((1 − exp (-FR_TL1 * t)) *
                                                    (exp (-FR_TL2 * t) *
                                                     (exp (-FR_TL3 * t) *
                                                      (exp (-FR_TL6 * t) *
                                                       ((1 − exp (-FR_TL7 * t)) *
                                                        (exp (-FR_TL8 * t) *
                                                         ((1 − exp (-FR_TL9 * t)) *
                                                          (exp (-FR_TL10 * t) *
                                                           (1 − exp (-FR_TL11 * t))))))))) +
                                                    ((1 − exp (-FR_TL1 * t)) *
                                                     (exp (-FR_TL2 * t) *
                                                      (exp (-FR_TL3 * t) *
                                                       (exp (-FR_TL6 * t) *
                                                        ((1 − exp (-FR_TL7 * t)) *
                                                         (1 − exp (-FR_TL8 * t)))))) +
                                                     ((1 − exp (-FR_TL1 * t)) *
                                                      (exp (-FR_TL2 * t) *
                                                       (exp (-FR_TL3 * t) *
                                                        ((1 − exp (-FR_TL6 * t)) *
                                                         (exp (-FR_TL7 * t) *
                                                          (exp (-FR_TL8 * t) *
                                                           (exp (-FR_TL9 * t) *
                                                            (exp (-FR_TL10 * t) *
                                                             exp (-FR_TL11 * t)))))))) +
                                                      ((1 − exp (-FR_TL1 * t)) *
                                                       (exp (-FR_TL2 * t) *
                                                        (exp (-FR_TL3 * t) *
                                                         ((1 − exp (-FR_TL6 * t)) *
                                                          (exp (-FR_TL7 * t) *
                                                           (exp (-FR_TL8 * t) *
                                                            (exp(-FR_TL9 * t) *
                                                             (exp (-FR_TL10 * t) *
                                                              (1 − exp (-FR_TL11 * t))))))))) +
                                                       ((1 − exp (-FR_TL1 * t)) *
                                                        (exp (-FR_TL2 * t) *
                                                         (exp (-FR_TL3 * t) *
                                                          ((1 − exp (-FR_TL6 * t)) *
                                                           (exp (-FR_TL7 * t) *
                                                            (exp (-FR_TL8 * t) *
                                                             (1 − exp (-FR_TL9 * t))))))) +
                                                        ((1 −  exp (-FR_TL1 * t)) *
                                                         (exp (-FR_TL2 * t) *
                                                          (exp (-FR_TL3 * t) *
                                                           ((1 − exp (-FR_TL6 * t)) *
                                                            (exp (-FR_TL7 * t) *
                                                             ((1 − exp (-FR_TL8 * t)) *
                                                              (exp (-FR_TL9 * t) *
                                                               (exp (-FR_TL10 * t) *
                                                                exp (-FR_TL11 * t)))))))) +
                                                         ((1 − exp (-FR_TL1 * t)) *
                                                          (exp (-FR_TL2 * t) *
                                                           (exp (-FR_TL3 * t) *
                                                            ((1 − exp (-FR_TL6 * t)) *
                                                             (exp (-FR_TL7 * t) *
                                                              ((1 − exp (-FR_TL8 * t)) *
                                                               (exp (-FR_TL9 * t) *
                                                                (exp (-FR_TL10 * t) *
                                                                 (1 −  exp (-FR_TL11 * t))))))))) +
                                                          ((1 − exp (-FR_TL1 * t)) *
                                                           (exp (-FR_TL2 * t) *
                                                            (exp (-FR_TL3 * t) *
                                                             ((1 − exp (-FR_TL6 * t)) *
                                                              (exp (-FR_TL7 * t) *
                                                               ((1 − exp (-FR_TL8 * t)) *
                                                                (exp (-FR_TL9 * t) *
                                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                                           ((1 − exp  (-FR_TL1 * t)) *
                                                            (exp (-FR_TL2 * t) *
                                                             (exp (-FR_TL3 * t) *
                                                              ((1 − exp (-FR_TL6 * t)) *
                                                               (exp (-FR_TL7 * t) *
                                                                ((1 − exp (-FR_TL8 * t)) *
                                                                 (1 − exp (-FR_TL9 * t))))))) +
                                                            ((1 − exp (-FR_TL1 * t)) *
                                                             (exp (-FR_TL2 * t) *
                                                              (exp (-FR_TL3 * t) *
                                                               ((1 − exp (-FR_TL6 * t)) *
                                                                (1 − exp  (-FR_TL7 * t))))) +
                                                             ((1 − exp (-FR_TL1 * t)) *
                                                              (exp (-FR_TL2 * t) *
                                                               (1 −  exp  (-FR_TL3 * t))) +
                                                              (1 − exp (-FR_TL1 * t)) *
                                                              (1 − exp (-FR_TL2 * t))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * CN_A +
	(exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              (exp (-FR_TL21 * t) *
               ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) *
                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             ((1 − exp (-FR_TL18 * t)) *
              (exp (-FR_TL19 * t) *
               (exp (-FR_TL20 * t) *
                (exp (-FR_TL21 * t) *
                 (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              ((1 − exp (-FR_TL18 * t)) *
               (exp (-FR_TL19 * t) *
                (exp (-FR_TL20 * t) *
                 (exp (-FR_TL21 * t) *
                  (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  (exp (-FR_TL21 * t) *
                   ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   (exp (-FR_TL21 * t) *
                    ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    ((1 − exp (-FR_TL21 * t)) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 ((1 − exp (-FR_TL15 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    (exp (-FR_TL21 * t) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     (exp (-FR_TL21 * t) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      (exp (-FR_TL21 * t) *
                       ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) *
                      (exp (-FR_TL20 * t) *
                       (exp (-FR_TL21 * t) *
                        ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t))))))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) *
                      (exp (-FR_TL19 * t) *
                       (exp (-FR_TL20 * t) *
                        ((1 − exp (-FR_TL21 * t)) *
                         (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          (exp (-FR_TL21 * t) *
                           (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           (exp (-FR_TL21 * t) *
                            (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) *
                           (exp (-FR_TL20 * t) *
                            (exp (-FR_TL21 * t) *
                             ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) *
                           (exp (-FR_TL19 * t) *
                            (exp (-FR_TL20 * t) *
                             (exp (-FR_TL21 * t) *
                              ((1 − exp (-FR_TL16 * t)) *
                               (1 − exp (-FR_TL17 * t)))))))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) *
                           (exp (-FR_TL18 * t) *
                            (exp (-FR_TL19 * t) *
                             (exp (-FR_TL20 * t) *
                              ((1 − exp (-FR_TL21 * t)) *
                               (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                        (exp (-FR_L12 * t) *
                         ((1 − exp (-FR_TL13 * t)) *
                          (exp (-FR_TL14 * t) *
                           (exp (-FR_TL15 * t) *
                            (exp (-FR_TL18 * t) *
                             (exp (-FR_TL19 * t) *
                              (exp (-FR_TL20 * t) *
                               (exp (-FR_TL21 * t) *
                                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (exp (-FR_TL21 * t) *
                                 (exp (-FR_TL16 * t) *
                                  (1 − exp (-FR_TL17 * t)))))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (exp (-FR_TL20 * t) *
                                 (exp (-FR_TL21 * t) *
                                  (exp (-FR_TL16 * t) *
                                   (1 − exp (-FR_TL17 * t)))))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (exp (-FR_TL19 * t) *
                                 (exp (-FR_TL20 * t) *
                                  (exp (-FR_TL21 * t) *
                                   (exp (-FR_TL16 * t) *
                                    (1 − exp (-FR_TL17 * t)))))))))) +
                            ((1 − exp (-FR_L12 * t)) *
                             (exp (-FR_TL13 * t) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (exp (-FR_TL18 * t) *
                                 (exp (-FR_TL19 * t) *
                                  (exp (-FR_TL20 * t) *
                                   (exp (-FR_TL21 * t) *
                                    (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                             ((1 − exp (-FR_L12 * t)) *
                              (exp (-FR_TL13 * t) *
                               (exp (-FR_TL14 * t) *
                                (exp (-FR_TL15 * t) *
                                 (exp (-FR_TL18 * t) *
                                  (exp (-FR_TL19 * t) *
                                   (exp (-FR_TL20 * t) *
                                    (exp (-FR_TL21 * t) *
                                     (exp (-FR_TL16 * t) *
                                      (1 − exp (-FR_TL17 * t)))))))))) +
                              ((1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       exp (-FR_TL17 * t))))))))) +
                               (1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       (1 − exp (-FR_TL17 * t)))))))))))))))))))))))))))))))))) * 0.15 * CN_B +
        (exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              ((1 − exp (-FR_TL21 * t)) *
               (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             (exp (-FR_TL18 * t) *
              (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  ((1 − exp (-FR_TL21 * t)) *
                   (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 (exp (-FR_TL15 * t) *
                  ((1 − exp (-FR_TL18 * t)) * (1 − exp (-FR_TL19 * t)))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     ((1 − exp (-FR_TL21 * t)) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t)))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) * (1 − exp (-FR_TL19 * t))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          ((1 − exp (-FR_TL21 * t)) *
                           (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           ((1 − exp (-FR_TL21 * t)) *
                            (1 − exp (-FR_TL16 * t))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) * (1 − exp (-FR_TL18 * t))))) +
                        (exp (-FR_L12 * t) *
                         (exp (-FR_TL13 * t) *
                          ((1 − exp (-FR_TL14 * t)) *
                           (1 − exp (-FR_TL15 * t)))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (1 − exp (-FR_TL21 * t)))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (1 − exp (-FR_TL20 * t))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (1 − exp (-FR_TL19 * t)))))) +
                            (exp (-FR_L12 * t) *
                             ((1 − exp (-FR_TL13 * t)) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (1 − exp (-FR_TL18 * t))))) +
                             (exp (-FR_L12 * t) *
                              ((1 − exp (-FR_TL13 * t)) *
                               (exp (-FR_TL14 * t) *
                                (1 − exp (-FR_TL15 * t)))) +
                              (exp (-FR_L12 * t) *
                               ((1 − exp (-FR_TL13 * t)) *
                                (1 − exp (-FR_TL14 * t))) +
                               ((1 − exp (-FR_L12 * t)) *
                                (exp (-FR_TL13 * t) *
                                 (exp (-FR_TL14 * t) *
                                  (exp (-FR_TL15 * t) *
                                   (exp (-FR_TL18 * t) *
                                    (exp (-FR_TL19 * t) *
                                     (exp (-FR_TL20 * t) *
                                      (1 − exp (-FR_TL21 * t)))))))) +
                                ((1 − exp (-FR_L12 * t)) *
                                 (exp (-FR_TL13 * t) *
                                  (exp (-FR_TL14 * t) *
                                   (exp (-FR_TL15 * t) *
                                    (exp (-FR_TL18 * t) *
                                     (exp (-FR_TL19 * t) *
                                      (1 − exp (-FR_TL20 * t))))))) +
                                 ((1 − exp (-FR_L12 * t)) *
                                  (exp (-FR_TL13 * t) *
                                   (exp (-FR_TL14 * t) *
                                    (exp (-FR_TL15 * t) *
                                     (exp (-FR_TL18 * t) *
                                      (1 − exp (-FR_TL19 * t)))))) +
                                  ((1 − exp (-FR_L12 * t)) *
                                   (exp (-FR_TL13 * t) *
                                    (exp (-FR_TL14 * t) *
                                     (exp (-FR_TL15 * t) *
                                      (1 − exp (-FR_TL18 * t))))) +
                                   ((1 − exp (-FR_L12 * t)) *
                                    (exp (-FR_TL13 * t) *
                                     (exp (-FR_TL14 * t) *
                                      (1 − exp (-FR_TL15 * t)))) +
                                    ((1 − exp (-FR_L12 * t)) *
                                     (exp (-FR_TL13 * t) *
                                      (1 − exp (-FR_TL14 * t))) +
                                     (1 − exp (-FR_L12 * t)) *
                                     (1 − exp (-FR_TL13 * t)))))))))))))))))))))))))))))))) * CN_B +
	( exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             (exp (-FR_TL28 * t) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              (exp (-FR_TL28 * t) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               (exp (-FR_TL28 * t) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                (exp (-FR_TL28 * t) *
                 (exp (-FR_TL29 * t) *
                  ((1 − exp (-FR_TL30 * t)) *
                   (exp (-FR_TL31 * t) *
                    (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 (exp (-FR_TL28 * t) *
                  (exp (-FR_TL29 * t) *
                   ((1 − exp (-FR_TL30 * t)) *
                    (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 (exp (-FR_TL27 * t) *
                  (exp (-FR_TL28 * t) *
                   (exp (-FR_TL29 * t) *
                    ((1 − exp (-FR_TL30 * t)) * (1 − exp (-FR_TL31 * t)))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  (exp (-FR_TL27 * t) *
                   (exp (-FR_TL28 * t) *
                    ((1 − exp (-FR_TL29 * t)) *
                     (exp (-FR_TL30 * t) *
                      (exp (-FR_TL31 * t) *
                       (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   (exp (-FR_TL27 * t) *
                    (exp (-FR_TL28 * t) *
                     ((1 − exp (-FR_TL29 * t)) *
                      (exp (-FR_TL30 * t) *
                       (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    (exp (-FR_TL27 * t) *
                     (exp (-FR_TL28 * t) *
                      ((1 − exp (-FR_TL29 * t)) *
                       (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     (exp (-FR_TL27 * t) *
                      (exp (-FR_TL28 * t) *
                       ((1 − exp (-FR_TL29 * t)) * (1 − exp (-FR_TL30 * t))))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     (exp (-FR_TL26 * t) *
                      (exp (-FR_TL27 * t) *
                       ((1 − exp (-FR_TL28 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      (exp (-FR_TL26 * t) *
                       ((1 − exp (-FR_TL27 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t)))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      ((1 − exp (-FR_TL24 * t)) *
                       (exp (-FR_TL25 * t) *
                        (exp (-FR_TL26 * t) *
                         (exp (-FR_TL27 * t) *
                          (exp (-FR_TL28 * t) *
                           (exp (-FR_TL29 * t) *
                            (exp (-FR_TL30 * t) *
                             (exp (-FR_TL31 * t) *
                              (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       ((1 − exp (-FR_TL24 * t)) * (1 − exp (-FR_TL25 * t)))) +
                      (exp (-FR_TL22 * t) *
                       ((1 − exp (-FR_TL23 * t)) *
                        (exp (-FR_TL24 * t) *
                         (exp (-FR_TL25 * t) *
                          (exp (-FR_TL26 * t) *
                           (exp (-FR_TL27 * t) *
                            (exp (-FR_TL28 * t) *
                             (exp (-FR_TL29 * t) *
                              (exp (-FR_TL30 * t) *
                               (exp (-FR_TL31 * t) *
                                (1 − exp (-FR_TL32 * t))))))))))) +
                       (exp (-FR_TL22 * t) *
                        ((1 − exp (-FR_TL23 * t)) *
                         (exp (-FR_TL24 * t) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               ((1 − exp (-FR_TL30 * t)) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                        (exp (-FR_TL22 * t) *
                         ((1 − exp (-FR_TL23 * t)) *
                          (exp (-FR_TL24 * t) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               ((1 − exp (-FR_TL29 * t)) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                         ((1 − exp (-FR_TL22 * t)) *
                          (exp (-FR_TL23 * t) *
                           (exp (-FR_TL24 * t) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (exp (-FR_TL31 * t) *
                                   (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                          ((1 − exp (-FR_TL22 * t)) *
                           (exp (-FR_TL23 * t) *
                            (exp (-FR_TL24 * t) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  ((1 − exp (-FR_TL30 * t)) *
                                   (exp (-FR_TL31 * t) *
                                    (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                           ((1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     (exp (-FR_TL32 * t) *
                                      exp (-FR_TL33 * t))))))))))) +
                            (1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     ((1 − exp (-FR_TL32 * t)) *
                                      exp (-FR_TL33 * t)))))))))))))))))))))))))))))))) * 0.15 * CN_C +
        (exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             ((1 − exp (-FR_TL28 * t)) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              ((1 − exp (-FR_TL28 * t)) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               ((1 − exp (-FR_TL28 * t)) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                ((1 − exp (-FR_TL28 * t)) *
                 (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 ((1 − exp (-FR_TL28 * t)) * (1 − exp (-FR_TL29 * t)))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 ((1 − exp (-FR_TL27 * t)) *
                  (exp (-FR_TL29 * t) *
                   (exp (-FR_TL30 * t) *
                    (exp (-FR_TL31 * t) *
                     (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t))))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  ((1 − exp (-FR_TL27 * t)) *
                   (exp (-FR_TL29 * t) *
                    (exp (-FR_TL30 * t) *
                     (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t)))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   ((1 − exp (-FR_TL27 * t)) *
                    (exp (-FR_TL29 * t) *
                     (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    ((1 − exp (-FR_TL27 * t)) *
                     (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t)))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     ((1 − exp (-FR_TL27 * t)) * (1 − exp (-FR_TL29 * t))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     ((1 − exp (-FR_TL26 * t)) *
                      (exp (-FR_TL29 * t) *
                       (exp (-FR_TL30 * t) *
                        (exp (-FR_TL31 * t) *
                         (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      ((1 − exp (-FR_TL26 * t)) *
                       (exp (-FR_TL29 * t) *
                        (exp (-FR_TL30 * t) *
                         (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      (exp (-FR_TL24 * t) *
                       (exp (-FR_TL25 * t) *
                        ((1 − exp (-FR_TL26 * t)) *
                         (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       (exp (-FR_TL24 * t) *
                        (exp (-FR_TL25 * t) *
                         ((1 − exp (-FR_TL26 * t)) *
                          (1 − exp (-FR_TL29 * t)))))) +
                      (exp (-FR_TL22 * t) *
                       (exp (-FR_TL23 * t) *
                        (exp (-FR_TL24 * t) * (1 − exp (-FR_TL25 * t)))) +
                       (exp (-FR_TL22 * t) *
                        (exp (-FR_TL23 * t) *
                         ((1 − exp (-FR_TL24 * t)) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               (exp (-FR_TL30 * t) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) *
                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                        (exp (-FR_TL22 * t) *
                         (exp (-FR_TL23 * t) *
                          ((1 − exp (-FR_TL24 * t)) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               (exp (-FR_TL29 * t) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (1 − exp (-FR_TL32 * t))))))))))) +
                         (exp (-FR_TL22 * t) *
                          (exp (-FR_TL23 * t) *
                           ((1 − exp (-FR_TL24 * t)) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (1 − exp (-FR_TL31 * t)))))))))) +
                          (exp (-FR_TL22 * t) *
                           (exp (-FR_TL23 * t) *
                            ((1 − exp (-FR_TL24 * t)) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  (1 − exp (-FR_TL30 * t))))))))) +
                           (exp (-FR_TL22 * t) *
                            (exp (-FR_TL23 * t) *
                             ((1 − exp (-FR_TL24 * t)) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  (1 − exp (-FR_TL29 * t)))))))) +
                            (exp (-FR_TL22 * t) *
                             (exp (-FR_TL23 * t) *
                              ((1 − exp (-FR_TL24 * t)) *
                               (exp (-FR_TL25 * t) *
                                (exp (-FR_TL26 * t) *
                                 (exp (-FR_TL27 * t) *
                                  (1 − exp (-FR_TL28 * t))))))) +
                             (exp (-FR_TL22 * t) *
                              (exp (-FR_TL23 * t) *
                               ((1 − exp (-FR_TL24 * t)) *
                                (exp (-FR_TL25 * t) *
                                 (exp (-FR_TL26 * t) *
                                  (1 − exp (-FR_TL27 * t)))))) +
                              (exp (-FR_TL22 * t) *
                               (exp (-FR_TL23 * t) *
                                ((1 − exp (-FR_TL24 * t)) *
                                 (exp (-FR_TL25 * t) *
                                  (1 − exp (-FR_TL26 * t))))) +
                               (exp (-FR_TL22 * t) *
                                ((1 − exp (-FR_TL23 * t)) *
                                 (exp (-FR_TL24 * t) *
                                  (exp (-FR_TL25 * t) *
                                   (exp (-FR_TL26 * t) *
                                    (exp (-FR_TL27 * t) *
                                     (exp (-FR_TL28 * t) *
                                      (exp (-FR_TL29 * t) *
                                       (exp (-FR_TL30 * t) *
                                        (exp (-FR_TL31 * t) *
                                         (exp (-FR_TL32 * t) *
                                          exp (-FR_TL33 * t))))))))))) +
                                (exp (-FR_TL22 * t) *
                                 ((1 − exp (-FR_TL23 * t)) *
                                  (exp (-FR_TL24 * t) *
                                   (exp (-FR_TL25 * t) *
                                    (exp (-FR_TL26 * t) *
                                     (exp (-FR_TL27 * t) *
                                      (exp (-FR_TL28 * t) *
                                       (exp (-FR_TL29 * t) *
                                        (exp (-FR_TL30 * t) *
                                         (exp (-FR_TL31 * t) *
                                          (exp (-FR_TL32 * t) *
                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                 (exp (-FR_TL22 * t) *
                                  ((1 − exp (-FR_TL23 * t)) *
                                   (exp (-FR_TL24 * t) *
                                    (exp (-FR_TL25 * t) *
                                     (exp (-FR_TL26 * t) *
                                      (exp (-FR_TL27 * t) *
                                       (exp (-FR_TL28 * t) *
                                        (exp (-FR_TL29 * t) *
                                         (exp (-FR_TL30 * t) *
                                          ((1 − exp (-FR_TL31 * t)) *
                                           (exp (-FR_TL32 * t) *
                                            exp (-FR_TL33 * t))))))))))) +
                                  (exp (-FR_TL22 * t) *
                                   ((1 − exp (-FR_TL23 * t)) *
                                    (exp (-FR_TL24 * t) *
                                     (exp (-FR_TL25 * t) *
                                      (exp (-FR_TL26 * t) *
                                       (exp (-FR_TL27 * t) *
                                        (exp (-FR_TL28 * t) *
                                         (exp (-FR_TL29 * t) *
                                          (exp (-FR_TL30 * t) *
                                           ((1 − exp (-FR_TL31 * t)) *
                                            (exp (-FR_TL32 * t) *
                                             (1 − exp (-FR_TL33 * t)))))))))))) +
                                   (exp (-FR_TL22 * t) *
                                    ((1 − exp (-FR_TL23 * t)) *
                                     (exp (-FR_TL24 * t) *
                                      (exp (-FR_TL25 * t) *
                                       (exp (-FR_TL26 * t) *
                                        (exp (-FR_TL27 * t) *
                                         (exp (-FR_TL28 * t) *
                                          (exp (-FR_TL29 * t) *
                                           (exp (-FR_TL30 * t) *
                                            ((1 − exp (-FR_TL31 * t)) *
                                             (1 − exp (-FR_TL32 * t))))))))))) +
                                    (exp (-FR_TL22 * t) *
                                     ((1 − exp (-FR_TL23 * t)) *
                                      (exp (-FR_TL24 * t) *
                                       (exp (-FR_TL25 * t) *
                                        (exp (-FR_TL26 * t) *
                                         (exp (-FR_TL27 * t) *
                                          (exp (-FR_TL28 * t) *
                                           (exp (-FR_TL29 * t) *
                                            ((1 − exp (-FR_TL30 * t)) *
                                             (exp (-FR_TL31 * t) *
                                              (exp (-FR_TL32 * t) *
                                               (1 − exp (-FR_TL33 * t)))))))))))) +
                                     (exp (-FR_TL22 * t) *
                                      ((1 − exp (-FR_TL23 * t)) *
                                       (exp (-FR_TL24 * t) *
                                        (exp (-FR_TL25 * t) *
                                         (exp (-FR_TL26 * t) *
                                          (exp (-FR_TL27 * t) *
                                           (exp (-FR_TL28 * t) *
                                            (exp (-FR_TL29 * t) *
                                             ((1 − exp (-FR_TL30 * t)) *
                                              (exp (-FR_TL31 * t) *
                                               (1 − exp (-FR_TL32 * t))))))))))) +
                                      (exp (-FR_TL22 * t) *
                                       ((1 − exp (-FR_TL23 * t)) *
                                        (exp (-FR_TL24 * t) *
                                         (exp (-FR_TL25 * t) *
                                          (exp (-FR_TL26 * t) *
                                           (exp (-FR_TL27 * t) *
                                            (exp (-FR_TL28 * t) *
                                             (exp (-FR_TL29 * t) *
                                              ((1 − exp (-FR_TL30 * t)) *
                                               ((1 − exp (-FR_TL31 * t)) *
                                                (1 − exp (-FR_TL32 * t))))))))))) +
                                       (exp (-FR_TL22 * t) *
                                        ((1 − exp (-FR_TL23 * t)) *
                                         (exp (-FR_TL24 * t) *
                                          (exp (-FR_TL25 * t) *
                                           (exp (-FR_TL26 * t) *
                                            (exp (-FR_TL27 * t) *
                                             (exp (-FR_TL28 * t) *
                                              ((1 − exp (-FR_TL29 * t)) *
                                               (exp (-FR_TL30 * t) *
                                                (exp (-FR_TL31 * t) *
                                                 (exp (-FR_TL32 * t) *
                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                        (exp (-FR_TL22 * t) *
                                         ((1 − exp (-FR_TL23 * t)) *
                                          (exp (-FR_TL24 * t) *
                                           (exp (-FR_TL25 * t) *
                                            (exp (-FR_TL26 * t) *
                                             (exp (-FR_TL27 * t) *
                                              (exp (-FR_TL28 * t) *
                                               ((1 − exp (-FR_TL29 * t)) *
                                                (exp (-FR_TL30 * t) *
                                                 (exp (-FR_TL31 * t) *
                                                  (1 − exp (-FR_TL32 * t))))))))))) +
                                         (exp (-FR_TL22 * t) *
                                          ((1 − exp (-FR_TL23 * t)) *
                                           (exp (-FR_TL24 * t) *
                                            (exp (-FR_TL25 * t) *
                                             (exp (-FR_TL26 * t) *
                                              (exp (-FR_TL27 * t) *
                                               (exp (-FR_TL28 * t) *
                                                ((1 − exp (-FR_TL29 * t)) *
                                                 (exp (-FR_TL30 * t) *
                                                  (1 − exp (-FR_TL31 * t)))))))))) +
                                          (exp (-FR_TL22 * t) *
                                           ((1 − exp (-FR_TL23 * t)) *
                                            (exp (-FR_TL24 * t) *
                                             (exp (-FR_TL25 * t) *
                                              (exp (-FR_TL26 * t) *
                                               (exp (-FR_TL27 * t) *
                                                (exp (-FR_TL28 * t) *
                                                 ((1 − exp (-FR_TL29 * t)) *
                                                  (1 − exp (-FR_TL30 * t))))))))) +
                                           (exp (-FR_TL22 * t) *
                                            ((1 − exp (-FR_TL23 * t)) *
                                             (exp (-FR_TL24 * t) *
                                              (exp (-FR_TL25 * t) *
                                               (exp (-FR_TL26 * t) *
                                                (exp (-FR_TL27 * t) *
                                                 (1 − exp (-FR_TL28 * t))))))) +
                                            (exp (-FR_TL22 * t) *
                                             ((1 − exp (-FR_TL23 * t)) *
                                              (exp (-FR_TL24 * t) *
                                               (exp (-FR_TL25 * t) *
                                                (exp (-FR_TL26 * t) *
                                                 (1 − exp (-FR_TL27 * t)))))) +
                                             (exp (-FR_TL22 * t) *
                                              ((1 − exp (-FR_TL23 * t)) *
                                               (exp (-FR_TL24 * t) *
                                                (exp (-FR_TL25 * t) *
                                                 (1 − exp (-FR_TL26 * t))))) +
                                              (exp (-FR_TL22 * t) *
                                               ((1 − exp (-FR_TL23 * t)) *
                                                (exp (-FR_TL24 * t) *
                                                 (1 − exp (-FR_TL25 * t)))) +
                                               (exp (-FR_TL22 * t) *
                                                ((1 − exp (-FR_TL23 * t)) *
                                                 (1 − exp (-FR_TL24 * t))) +
                                                ((1 − exp (-FR_TL22 * t)) *
                                                 (exp (-FR_TL23 * t) *
                                                  (exp (-FR_TL24 * t) *
                                                   (exp (-FR_TL25 * t) *
                                                    (exp (-FR_TL26 * t) *
                                                     (exp (-FR_TL27 * t) *
                                                      (exp (-FR_TL28 * t) *
                                                       (exp (-FR_TL29 * t) *
                                                        (exp (-FR_TL30 * t) *
                                                         (exp (-FR_TL31 * t) *
                                                          (exp (-FR_TL32 * t) *
                                                           (1 −exp (-FR_TL33 * t)))))))))))) +
                                                 ((1 − exp (-FR_TL22 * t)) *
                                                  (exp (-FR_TL23 * t) *
                                                   (exp (-FR_TL24 * t) *
                                                    (exp (-FR_TL25 * t) *
                                                     (exp (-FR_TL26 * t) *
                                                      (exp (-FR_TL27 * t) *
                                                       (exp (-FR_TL28 * t) *
                                                        (exp (-FR_TL29 * t) *
                                                         (exp (-FR_TL30 * t) *
                                                          (exp (-FR_TL31 * t) *
                                                           (1 − exp (-FR_TL32 * t))))))))))) +
                                                  ((1 − exp (-FR_TL22 * t)) *
                                                   (exp (-FR_TL23 * t) *
                                                    (exp (-FR_TL24 * t) *
                                                     (exp (-FR_TL25 * t) *
                                                      (exp (-FR_TL26 * t) *
                                                       (exp (-FR_TL27 * t) *
                                                        (exp (-FR_TL28 * t) *
                                                         (exp (-FR_TL29 * t) *
                                                          (exp (-FR_TL30 * t) *
                                                           (1 − exp (-FR_TL31 * t)))))))))) +
                                                   ((1 − exp (-FR_TL22 * t)) *
                                                    (exp (-FR_TL23 * t) *
                                                     (exp (-FR_TL24 * t) *
                                                      (exp (-FR_TL25 * t) *
                                                       (exp (-FR_TL26 * t) *
                                                        (exp (-FR_TL27 * t) *
                                                         (exp (-FR_TL28 * t) *
                                                          (exp (-FR_TL29 * t) *
                                                           ((1 − exp (-FR_TL30 * t)) *
                                                            (exp (-FR_TL31 * t) *
                                                             (exp (-FR_TL32 * t) *
                                                              (1 − exp (-FR_TL33 * t)))))))))))) +
                                                    ((1 − exp (-FR_TL22 * t)) *
                                                     (exp (-FR_TL23 * t) *
                                                      (exp (-FR_TL24 * t) *
                                                       (exp (-FR_TL25 * t) *
                                                        (exp (-FR_TL26 * t) *
                                                         (exp (-FR_TL27 * t) *
                                                          (exp (-FR_TL28 * t) *
                                                           (exp  (-FR_TL29 * t) *
                                                            ((1 − exp (-FR_TL30 * t)) *
                                                             (exp (-FR_TL31 * t) *
                                                              (1 −  exp (-FR_TL32 * t))))))))))) +
                                                     ((1 − exp (-FR_TL22 * t)) *
                                                      (exp (-FR_TL23 * t) *
                                                       (exp (-FR_TL24 * t) *
                                                        (exp (-FR_TL25 * t) *
                                                         (exp (-FR_TL26 * t) *
                                                          (exp (-FR_TL27 * t) *
                                                           (exp (-FR_TL28 * t) *
                                                            (exp (-FR_TL29 * t) *
                                                             ((1 −  exp (-FR_TL30 * t)) *
                                                              (1 − exp (-FR_TL31 * t)))))))))) +
                                                      ((1 − exp (-FR_TL22 * t)) *
                                                       (exp (-FR_TL23 * t) *
                                                        (exp (-FR_TL24 * t) *
                                                         (exp (-FR_TL25 * t) *
                                                          (exp (-FR_TL26 * t) *
                                                           (exp (-FR_TL27 * t) *
                                                            (exp  (-FR_TL28 * t) *
                                                             ((1 − exp (-FR_TL29 * t)) *
                                                              (exp (-FR_TL30 * t) *
                                                               (exp (-FR_TL31 * t) *
                                                                (exp (-FR_TL32 * t) *
                                                                 (1 − exp (-FR_TL33 * t)))))))))))) +
                                                       ((1 − exp (-FR_TL22 * t)) *
                                                        (exp (-FR_TL23 * t) *
                                                         (exp (-FR_TL24 * t) *
                                                          (exp (-FR_TL25 * t) *
                                                           (exp (-FR_TL26 * t) *
                                                            (exp  (-FR_TL27 * t) *
                                                             (exp (-FR_TL28 * t) *
                                                              ((1 −  exp (-FR_TL29 * t)) *
                                                               (exp (-FR_TL30 * t) *
                                                                (exp (-FR_TL31 * t) *
                                                                 ((1 − exp (-FR_TL32 * t)) *
                                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                                        ((1 − exp (-FR_TL22 * t)) *
                                                         (exp (-FR_TL23 * t) *
                                                          (exp (-FR_TL24 * t) *
                                                           (exp (-FR_TL25 * t) *
                                                            (exp (-FR_TL26 * t) *
                                                             (exp (-FR_TL27 * t) *
                                                              (exp (-FR_TL28 * t) *
                                                               ((1 − exp (-FR_TL29 * t)) *
                                                                (exp (-FR_TL30 * t) *
                                                                 (1 − exp (-FR_TL31 * t)))))))))) +
                                                         ((1 − exp (-FR_TL22 * t)) *
                                                          (exp (-FR_TL23 * t) *
                                                           (exp (-FR_TL24 * t) *
                                                            (exp (-FR_TL25 * t) *
                                                             (exp (-FR_TL26 * t) *
                                                              (exp (-FR_TL27 * t) *
                                                               (exp (-FR_TL28 * t) *
                                                                ((1 − exp (-FR_TL29 * t)) *
                                                                 (1 −  exp (-FR_TL30 * t))))))))) +
                                                          ((1 − exp (-FR_TL22 * t)) *
                                                           (exp (-FR_TL23 * t) *
                                                            (exp (-FR_TL24 * t) *
                                                             (exp (-FR_TL25 * t) *
                                                              (exp (-FR_TL26 * t) *
                                                               (exp (-FR_TL27 * t) *
                                                                (1 − exp (-FR_TL28 * t))))))) +
                                                           ((1 − exp (-FR_TL22 * t)) *
                                                            (exp (-FR_TL23 * t) *
                                                             (exp (-FR_TL24 * t) *
                                                              (exp (-FR_TL25 * t) *
                                                               (exp (-FR_TL26 * t) *
                                                                (1 −  exp (-FR_TL27 * t)))))) +
                                                            ((1 − exp (-FR_TL22 * t)) *
                                                             (exp (-FR_TL23 * t) *
                                                              (exp (-FR_TL24 * t) *
                                                               (exp (-FR_TL25 * t) *
                                                                (1 − exp (-FR_TL26 * t))))) +
                                                             ((1 − exp (-FR_TL22 * t)) *
                                                              (exp (-FR_TL23 * t) *
                                                               (exp  (-FR_TL24 * t) *
                                                                (1 −exp (-FR_TL25 * t)))) +
                                                              ((1 − exp (-FR_TL22 * t)) *
                                                               (exp (-FR_TL23 * t) *
                                                                (1 −  exp (-FR_TL24 * t))) +
                                                               (1 − exp (-FR_TL22 * t)) *
                                                               (1 − exp (-FR_TL23 * t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * CN_C) / (CN_A + CN_B + CN_C)``
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------*)  
(*    SAIDI Reliability Index     *)
(*--------------------------------*)

SAIDI
``((exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           (exp (-FR_TL5 * t) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) *
               ((1 − exp (-FR_TL9 * t)) *
                (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            (exp (-FR_TL5 * t) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               (exp (-FR_TL8 * t) *
                ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t)))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             (exp (-FR_TL5 * t) *
              (exp (-FR_TL6 * t) *
               (exp (-FR_TL7 * t) *
                ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              (exp (-FR_TL5 * t) *
               (exp (-FR_TL6 * t) *
                ((1 − exp (-FR_TL7 * t)) *
                 ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               (exp (-FR_TL5 * t) *
                (exp (-FR_TL6 * t) *
                 ((1 − exp (-FR_TL7 * t)) *
                  ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                (exp (-FR_TL5 * t) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 (exp (-FR_TL5 * t) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  (exp (-FR_TL5 * t) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   (exp (-FR_TL5 * t) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    (exp (-FR_TL5 * t) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    (exp (-FR_TL4 * t) *
                     ((1 − exp (-FR_TL5 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) * exp (-FR_TL9 * t)))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     (exp (-FR_TL4 * t) *
                      ((1 − exp (-FR_TL5 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         (exp (-FR_TL8 * t) * exp (-FR_TL9 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) *
                         (exp (-FR_TL7 * t) *
                          (exp (-FR_TL8 * t) *
                           ((1 − exp (-FR_TL9 * t)) *
                            (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             ((1 − exp (-FR_TL9 * t)) *
                              (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         ((1 − exp (-FR_TL3 * t)) *
                          (exp (-FR_TL4 * t) *
                           (exp (-FR_TL5 * t) *
                            (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          ((1 − exp (-FR_TL3 * t)) *
                           (exp (-FR_TL4 * t) *
                            (exp (-FR_TL5 * t) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          ((1 − exp (-FR_TL2 * t)) *
                           (exp (-FR_TL3 * t) *
                            (exp (-FR_TL4 * t) *
                             (exp (-FR_TL5 * t) *
                              (exp (-FR_TL8 * t) *
                               (exp (-FR_TL9 * t) * (1 − exp (-FR_TL11 * t)))))))) +
                          (exp (-FR_TL1 * t) *
                           ((1 − exp (-FR_TL2 * t)) *
                            (exp (-FR_TL3 * t) *
                             (exp (-FR_TL4 * t) *
                              (exp (-FR_TL5 * t) *
                               (exp (-FR_TL8 * t) *
                                ((1 − exp (-FR_TL9 * t)) *
                                 (exp (-FR_TL10 * t) *
                                  (1 − exp (-FR_TL11 * t))))))))) +
                           (exp (-FR_TL1 * t) *
                            ((1 − exp (-FR_TL2 * t)) *
                             (exp (-FR_TL3 * t) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL8 * t) *
                                 ((1 − exp (-FR_TL9 * t)) *
                                  ((1 − exp (-FR_TL10 * t)) *
                                   (1 − exp (-FR_TL11 * t))))))))) +
                            (exp (-FR_TL1 * t) *
                             ((1 − exp (-FR_TL2 * t)) *
                              (exp (-FR_TL3 * t) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL8 * t)) *
                                  (exp (-FR_TL9 * t) *
                                   (exp (-FR_TL10 * t) *
                                    (1 − exp (-FR_TL11 * t))))))))) +
                             ((1 − exp (-FR_TL1 * t)) *
                              (exp (-FR_TL2 * t) *
                               (exp (-FR_TL3 * t) *
                                (exp (-FR_TL6 * t) *
                                 (exp (-FR_TL7 * t) *
                                  (exp (-FR_TL8 * t) *
                                   (exp (-FR_TL9 * t) *
                                    (exp (-FR_TL10 * t) *
                                     (1 − exp (-FR_TL11 * t))))))))) +
                              ((1 − exp (-FR_TL1 * t)) *
                               (exp (-FR_TL2 * t) *
                                (exp (-FR_TL3 * t) *
                                 (exp (-FR_TL6 * t) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL8 * t) *
                                    ((1 − exp (-FR_TL9 * t)) *
                                     (exp (-FR_TL10 * t) *
                                      (1 − exp (-FR_TL11 * t))))))))) +
                               ((1 − exp (-FR_TL1 * t)) *
                                (exp (-FR_TL2 * t) *
                                 (exp (-FR_TL3 * t) *
                                  (exp (-FR_TL6 * t) *
                                   (exp (-FR_TL7 * t) *
                                    ((1 − exp (-FR_TL8 * t)) *
                                     (exp (-FR_TL9 * t) *
                                      (exp (-FR_TL10 * t) *
                                       (1 − exp (-FR_TL11 * t))))))))) +
                                ((1 − exp (-FR_TL1 * t)) *
                                 (exp (-FR_TL2 * t) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL6 * t) *
                                    (exp (-FR_TL7 * t) *
                                     ((1 − exp (-FR_TL8 * t)) *
                                      ((1 − exp (-FR_TL9 * t)) *
                                       (exp (-FR_TL10 * t) *
                                        (1 − exp (-FR_TL11 * t))))))))) +
                                 ((1 − exp (-FR_TL1 * t)) *
                                  (exp (-FR_TL2 * t) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL6 * t) *
                                     ((1 − exp (-FR_TL7 * t)) *
                                      (exp (-FR_TL8 * t) *
                                       (exp (-FR_TL9 * t) *
                                        (exp (-FR_TL10 * t) *
                                         (1 − exp (-FR_TL11 * t))))))))) +
                                  ((1 − exp (-FR_TL1 * t)) *
                                   (exp (-FR_TL2 * t) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL6 * t) *
                                      ((1 − exp (-FR_TL7 * t)) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         (exp (-FR_TL10 * t) *
                                          exp (-FR_TL11 * t)))))))) +
                                   ((1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL6 * t) *
                                       ((1 − exp (-FR_TL7 * t)) *
                                        (exp (-FR_TL8 * t) *
                                         ((1 − exp (-FR_TL9 * t)) *
                                          (1 − exp (-FR_TL10 * t)))))))) +
                                    (1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      ((1 − exp (-FR_TL6 * t)) *
                                       (exp (-FR_TL7 * t) *
                                        (exp (-FR_TL8 * t) *
                                         (exp (-FR_TL9 * t) *
                                          (1 − exp (-FR_TL10 * t))))))))))))))))))))))))))))))))))))) * MTTR_A * 0.15 * CN_A +
        (exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           ((1 − exp (-FR_TL5 * t)) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            ((1 − exp (-FR_TL5 * t)) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             ((1 − exp (-FR_TL5 * t)) *
              (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              ((1 − exp (-FR_TL5 * t)) *
               ((1 − exp (-FR_TL6 * t)) *
                (exp (-FR_TL7 * t) *
                 (exp (-FR_TL8 * t) *
                  (exp (-FR_TL9 * t) *
                   (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               ((1 − exp (-FR_TL5 * t)) *
                ((1 − exp (-FR_TL6 * t)) *
                 (exp (-FR_TL7 * t) *
                  (exp (-FR_TL8 * t) *
                   (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                ((1 − exp (-FR_TL5 * t)) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 ((1 − exp (-FR_TL5 * t)) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  ((1 − exp (-FR_TL5 * t)) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   ((1 − exp (-FR_TL5 * t)) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    ((1 − exp (-FR_TL5 * t)) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    ((1 − exp (-FR_TL4 * t)) *
                     (exp (-FR_TL6 * t) *
                      (exp (-FR_TL7 * t) *
                       (exp (-FR_TL8 * t) *
                        ((1 − exp (-FR_TL9 * t)) *
                         (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     ((1 − exp (-FR_TL4 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) *
                         ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t))))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t)))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         (exp (-FR_TL3 * t) *
                          ((1 − exp (-FR_TL4 * t)) *
                           ((1 − exp (-FR_TL6 * t)) *
                            (exp (-FR_TL7 * t) *
                             (exp (-FR_TL8 * t) *
                              ((1 − exp (-FR_TL9 * t)) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t)))))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          (exp (-FR_TL3 * t) *
                           ((1 − exp (-FR_TL4 * t)) *
                            ((1 − exp (-FR_TL6 * t)) *
                             (exp (-FR_TL7 * t) *
                              (exp (-FR_TL8 * t) *
                               ((1 − exp (-FR_TL9 * t)) *
                                (1 − exp (-FR_TL10 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          (exp (-FR_TL2 * t) *
                           (exp (-FR_TL3 * t) *
                            ((1 − exp (-FR_TL4 * t)) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                          (exp (-FR_TL1 * t) *
                           (exp (-FR_TL2 * t) *
                            (exp (-FR_TL3 * t) *
                             ((1 − exp (-FR_TL4 * t)) *
                              ((1 − exp (-FR_TL6 * t)) *
                               (1 − exp (-FR_TL7 * t)))))) +
                           (exp (-FR_TL1 * t) *
                            (exp (-FR_TL2 * t) *
                             ((1 − exp (-FR_TL3 * t)) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL6 * t) * exp (-FR_TL7 * t)))))) +
                            (exp (-FR_TL1 * t) *
                             (exp (-FR_TL2 * t) *
                              ((1 − exp (-FR_TL3 * t)) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL6 * t)) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL10 * t) * exp (-FR_TL11 * t)))))))) +
                             (exp (-FR_TL1 * t) *
                              (exp (-FR_TL2 * t) *
                               ((1 − exp (-FR_TL3 * t)) *
                                (exp (-FR_TL4 * t) *
                                 (exp (-FR_TL5 * t) *
                                  ((1 − exp (-FR_TL6 * t)) *
                                   (exp (-FR_TL7 * t) *
                                    (1 − exp (-FR_TL10 * t)))))))) +
                              (exp (-FR_TL1 * t) *
                               (exp (-FR_TL2 * t) *
                                ((1 − exp (-FR_TL3 * t)) *
                                 (exp (-FR_TL4 * t) *
                                  (exp (-FR_TL5 * t) *
                                   ((1 − exp (-FR_TL6 * t)) *
                                    (1 − exp (-FR_TL7 * t))))))) +
                               (exp (-FR_TL1 * t) *
                                (exp (-FR_TL2 * t) *
                                 ((1 − exp (-FR_TL3 * t)) *
                                  (exp (-FR_TL4 * t) *
                                   (1 − exp (-FR_TL5 * t))))) +
                                (exp (-FR_TL1 * t) *
                                 ((1 − exp (-FR_TL2 * t)) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL4 * t) *
                                    (exp (-FR_TL5 * t) *
                                     (exp (-FR_TL8 * t) *
                                      (exp (-FR_TL9 * t) *
                                       exp (-FR_TL11 * t))))))) +
                                 (exp (-FR_TL1 * t) *
                                  ((1 − exp (-FR_TL2 * t)) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL4 * t) *
                                     (exp (-FR_TL5 * t) *
                                      (exp (-FR_TL8 * t) *
                                       ((1 − exp (-FR_TL9 * t)) *
                                        (exp (-FR_TL10 * t) *
                                         exp (-FR_TL11 * t)))))))) +
                                  (exp (-FR_TL1 * t) *
                                   ((1 − exp (-FR_TL2 * t)) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL4 * t) *
                                      (exp (-FR_TL5 * t) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         ((1 − exp (-FR_TL10 * t)) *
                                          exp (-FR_TL11 * t)))))))) +
                                   (exp (-FR_TL1 * t) *
                                    ((1 − exp (-FR_TL2 * t)) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL4 * t) *
                                       (exp (-FR_TL5 * t) *
                                        ((1 − exp (-FR_TL8 * t)) *
                                         (exp (-FR_TL9 * t) *
                                          (exp (-FR_TL10 * t) *
                                           exp (-FR_TL11 * t)))))))) +
                                    (exp (-FR_TL1 * t) *
                                     ((1 − exp (-FR_TL2 * t)) *
                                      (exp (-FR_TL3 * t) *
                                       (exp (-FR_TL4 * t) *
                                        (exp (-FR_TL5 * t) *
                                         ((1 − exp (-FR_TL8 * t)) *
                                          (exp (-FR_TL9 * t) *
                                           (1 − exp (-FR_TL10 * t)))))))) +
                                     (exp (-FR_TL1 * t) *
                                      ((1 − exp (-FR_TL2 * t)) *
                                       (exp (-FR_TL3 * t) *
                                        (exp (-FR_TL4 * t) *
                                         (exp (-FR_TL5 * t) *
                                          ((1 − exp (-FR_TL8 * t)) *
                                           (1 − exp (-FR_TL9 * t))))))) +
                                      (exp (-FR_TL1 * t) *
                                       ((1 − exp (-FR_TL2 * t)) *
                                        (exp (-FR_TL3 * t) *
                                         (exp (-FR_TL4 * t) *
                                          (1 − exp (-FR_TL5 * t))))) +
                                       (exp (-FR_TL1 * t) *
                                        ((1 − exp (-FR_TL2 * t)) *
                                         (exp (-FR_TL3 * t) *
                                          (1 − exp (-FR_TL4 * t)))) +
                                        (exp (-FR_TL1 * t) *
                                         ((1 − exp (-FR_TL2 * t)) *
                                          (1 − exp (-FR_TL3 * t))) +
                                         ((1 − exp (-FR_TL1 * t)) *
                                          (exp (-FR_TL2 * t) *
                                           (exp (-FR_TL3 * t) *
                                            (exp (-FR_TL6 * t) *
                                             (exp (-FR_TL7 * t) *
                                              (exp (-FR_TL8 * t) *
                                               (exp (-FR_TL9 * t) *
                                                (exp (-FR_TL10 * t) *
                                                 exp (-FR_TL11 * t)))))))) +
                                          ((1 − exp (-FR_TL1 * t)) *
                                           (exp (-FR_TL2 * t) *
                                            (exp (-FR_TL3 * t) *
                                             (exp (-FR_TL6 * t) *
                                              (exp (-FR_TL7 * t) *
                                               (exp (-FR_TL8 * t) *
                                                (exp (-FR_TL9 * t) *
                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                           ((1 − exp (-FR_TL1 * t)) *
                                            (exp (-FR_TL2 * t) *
                                             (exp (-FR_TL3 * t) *
                                              (exp (-FR_TL6 * t) *
                                               (exp (-FR_TL7 * t) *
                                                (exp (-FR_TL8 * t) *
                                                 ((1 − exp (-FR_TL9 * t)) *
                                                  (exp (-FR_TL10 * t) *
                                                   exp (-FR_TL11 * t)))))))) +
                                            ((1 − exp (-FR_TL1 * t)) *
                                             (exp (-FR_TL2 * t) *
                                              (exp (-FR_TL3 * t) *
                                               (exp (-FR_TL6 * t) *
                                                (exp (-FR_TL7 * t) *
                                                 (exp (-FR_TL8 * t) *
                                                  ((1 − exp (-FR_TL9 * t)) *
                                                   (1 − exp (-FR_TL10 * t)))))))) +
                                             ((1 − exp (-FR_TL1 * t)) *
                                              (exp (-FR_TL2 * t) *
                                               (exp (-FR_TL3 * t) *
                                                (exp (-FR_TL6 * t) *
                                                 (exp (-FR_TL7 * t) *
                                                  ((1 − exp (-FR_TL8 * t)) *
                                                   (exp (-FR_TL9 * t) *
                                                    (exp (-FR_TL10 * t) *
                                                     exp (-FR_TL11 * t)))))))) +
                                              ((1 − exp (-FR_TL1 * t)) *
                                               (exp (-FR_TL2 * t) *
                                                (exp (-FR_TL3 * t) *
                                                 (exp (-FR_TL6 * t) *
                                                  (exp (-FR_TL7 * t) *
                                                   ((1 − exp (-FR_TL8 * t)) *
                                                    (exp (-FR_TL9 * t) *
                                                     (1 − exp (-FR_TL10 * t)))))))) +
                                               ((1 − exp (-FR_TL1 * t)) *
                                                (exp (-FR_TL2 * t) *
                                                 (exp (-FR_TL3 * t) *
                                                  (exp (-FR_TL6 * t) *
                                                   (exp (-FR_TL7 * t) *
                                                    ((1 − exp (-FR_TL8 * t)) *
                                                     ((1 − exp (-FR_TL9 * t)) *
                                                      (exp (-FR_TL10 * t) *
                                                       exp (-FR_TL11 * t)))))))) +
                                                ((1 − exp (-FR_TL1 * t)) *
                                                 (exp (-FR_TL2 * t) *
                                                  (exp (-FR_TL3 * t) *
                                                   (exp (-FR_TL6 * t) *
                                                    (exp (-FR_TL7 * t) *
                                                     ((1 − exp (-FR_TL8 * t)) *
                                                      ((1 − exp (-FR_TL9 * t)) *
                                                       (1 −
                                                        exp (-FR_TL10 * t)))))))) +
                                                 ((1 − exp (-FR_TL1 * t)) *
                                                  (exp (-FR_TL2 * t) *
                                                   (exp (-FR_TL3 * t) *
                                                    (exp (-FR_TL6 * t) *
                                                     ((1 − exp (-FR_TL7 * t)) *
                                                      (exp (-FR_TL8 * t) *
                                                       (exp (-FR_TL9 * t) *
                                                        (exp (-FR_TL10 * t) *
                                                         exp (-FR_TL11 * t)))))))) +
                                                  ((1 − exp (-FR_TL1 * t)) *
                                                   (exp (-FR_TL2 * t) *
                                                    (exp (-FR_TL3 * t) *
                                                     (exp (-FR_TL6 * t) *
                                                      ((1 − exp (-FR_TL7 * t)) *
                                                       (exp (-FR_TL8 * t) *
                                                        (exp (-FR_TL9 * t) *
                                                         (1 −  exp (-FR_TL10 * t)))))))) +
                                                   ((1 − exp (-FR_TL1 * t)) *
                                                    (exp (-FR_TL2 * t) *
                                                     (exp (-FR_TL3 * t) *
                                                      (exp (-FR_TL6 * t) *
                                                       ((1 − exp (-FR_TL7 * t)) *
                                                        (exp (-FR_TL8 * t) *
                                                         ((1 − exp (-FR_TL9 * t)) *
                                                          (exp (-FR_TL10 * t) *
                                                           (1 − exp (-FR_TL11 * t))))))))) +
                                                    ((1 − exp (-FR_TL1 * t)) *
                                                     (exp (-FR_TL2 * t) *
                                                      (exp (-FR_TL3 * t) *
                                                       (exp (-FR_TL6 * t) *
                                                        ((1 − exp (-FR_TL7 * t)) *
                                                         (1 − exp (-FR_TL8 * t)))))) +
                                                     ((1 − exp (-FR_TL1 * t)) *
                                                      (exp (-FR_TL2 * t) *
                                                       (exp (-FR_TL3 * t) *
                                                        ((1 − exp (-FR_TL6 * t)) *
                                                         (exp (-FR_TL7 * t) *
                                                          (exp (-FR_TL8 * t) *
                                                           (exp (-FR_TL9 * t) *
                                                            (exp (-FR_TL10 * t) *
                                                             exp (-FR_TL11 * t)))))))) +
                                                      ((1 − exp (-FR_TL1 * t)) *
                                                       (exp (-FR_TL2 * t) *
                                                        (exp (-FR_TL3 * t) *
                                                         ((1 − exp (-FR_TL6 * t)) *
                                                          (exp (-FR_TL7 * t) *
                                                           (exp (-FR_TL8 * t) *
                                                            (exp(-FR_TL9 * t) *
                                                             (exp (-FR_TL10 * t) *
                                                              (1 − exp (-FR_TL11 * t))))))))) +
                                                       ((1 − exp (-FR_TL1 * t)) *
                                                        (exp (-FR_TL2 * t) *
                                                         (exp (-FR_TL3 * t) *
                                                          ((1 − exp (-FR_TL6 * t)) *
                                                           (exp (-FR_TL7 * t) *
                                                            (exp (-FR_TL8 * t) *
                                                             (1 − exp (-FR_TL9 * t))))))) +
                                                        ((1 −  exp (-FR_TL1 * t)) *
                                                         (exp (-FR_TL2 * t) *
                                                          (exp (-FR_TL3 * t) *
                                                           ((1 − exp (-FR_TL6 * t)) *
                                                            (exp (-FR_TL7 * t) *
                                                             ((1 − exp (-FR_TL8 * t)) *
                                                              (exp (-FR_TL9 * t) *
                                                               (exp (-FR_TL10 * t) *
                                                                exp (-FR_TL11 * t)))))))) +
                                                         ((1 − exp (-FR_TL1 * t)) *
                                                          (exp (-FR_TL2 * t) *
                                                           (exp (-FR_TL3 * t) *
                                                            ((1 − exp (-FR_TL6 * t)) *
                                                             (exp (-FR_TL7 * t) *
                                                              ((1 − exp (-FR_TL8 * t)) *
                                                               (exp (-FR_TL9 * t) *
                                                                (exp (-FR_TL10 * t) *
                                                                 (1 −  exp (-FR_TL11 * t))))))))) +
                                                          ((1 − exp (-FR_TL1 * t)) *
                                                           (exp (-FR_TL2 * t) *
                                                            (exp (-FR_TL3 * t) *
                                                             ((1 − exp (-FR_TL6 * t)) *
                                                              (exp (-FR_TL7 * t) *
                                                               ((1 − exp (-FR_TL8 * t)) *
                                                                (exp (-FR_TL9 * t) *
                                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                                           ((1 − exp  (-FR_TL1 * t)) *
                                                            (exp (-FR_TL2 * t) *
                                                             (exp (-FR_TL3 * t) *
                                                              ((1 − exp (-FR_TL6 * t)) *
                                                               (exp (-FR_TL7 * t) *
                                                                ((1 − exp (-FR_TL8 * t)) *
                                                                 (1 − exp (-FR_TL9 * t))))))) +
                                                            ((1 − exp (-FR_TL1 * t)) *
                                                             (exp (-FR_TL2 * t) *
                                                              (exp (-FR_TL3 * t) *
                                                               ((1 − exp (-FR_TL6 * t)) *
                                                                (1 − exp  (-FR_TL7 * t))))) +
                                                             ((1 − exp (-FR_TL1 * t)) *
                                                              (exp (-FR_TL2 * t) *
                                                               (1 −  exp  (-FR_TL3 * t))) +
                                                              (1 − exp (-FR_TL1 * t)) *
                                                              (1 − exp (-FR_TL2 * t))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * MTTR_A * CN_A +
	(exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              (exp (-FR_TL21 * t) *
               ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) *
                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             ((1 − exp (-FR_TL18 * t)) *
              (exp (-FR_TL19 * t) *
               (exp (-FR_TL20 * t) *
                (exp (-FR_TL21 * t) *
                 (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              ((1 − exp (-FR_TL18 * t)) *
               (exp (-FR_TL19 * t) *
                (exp (-FR_TL20 * t) *
                 (exp (-FR_TL21 * t) *
                  (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  (exp (-FR_TL21 * t) *
                   ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   (exp (-FR_TL21 * t) *
                    ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    ((1 − exp (-FR_TL21 * t)) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 ((1 − exp (-FR_TL15 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    (exp (-FR_TL21 * t) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     (exp (-FR_TL21 * t) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      (exp (-FR_TL21 * t) *
                       ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) *
                      (exp (-FR_TL20 * t) *
                       (exp (-FR_TL21 * t) *
                        ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t))))))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) *
                      (exp (-FR_TL19 * t) *
                       (exp (-FR_TL20 * t) *
                        ((1 − exp (-FR_TL21 * t)) *
                         (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          (exp (-FR_TL21 * t) *
                           (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           (exp (-FR_TL21 * t) *
                            (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) *
                           (exp (-FR_TL20 * t) *
                            (exp (-FR_TL21 * t) *
                             ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) *
                           (exp (-FR_TL19 * t) *
                            (exp (-FR_TL20 * t) *
                             (exp (-FR_TL21 * t) *
                              ((1 − exp (-FR_TL16 * t)) *
                               (1 − exp (-FR_TL17 * t)))))))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) *
                           (exp (-FR_TL18 * t) *
                            (exp (-FR_TL19 * t) *
                             (exp (-FR_TL20 * t) *
                              ((1 − exp (-FR_TL21 * t)) *
                               (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                        (exp (-FR_L12 * t) *
                         ((1 − exp (-FR_TL13 * t)) *
                          (exp (-FR_TL14 * t) *
                           (exp (-FR_TL15 * t) *
                            (exp (-FR_TL18 * t) *
                             (exp (-FR_TL19 * t) *
                              (exp (-FR_TL20 * t) *
                               (exp (-FR_TL21 * t) *
                                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (exp (-FR_TL21 * t) *
                                 (exp (-FR_TL16 * t) *
                                  (1 − exp (-FR_TL17 * t)))))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (exp (-FR_TL20 * t) *
                                 (exp (-FR_TL21 * t) *
                                  (exp (-FR_TL16 * t) *
                                   (1 − exp (-FR_TL17 * t)))))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (exp (-FR_TL19 * t) *
                                 (exp (-FR_TL20 * t) *
                                  (exp (-FR_TL21 * t) *
                                   (exp (-FR_TL16 * t) *
                                    (1 − exp (-FR_TL17 * t)))))))))) +
                            ((1 − exp (-FR_L12 * t)) *
                             (exp (-FR_TL13 * t) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (exp (-FR_TL18 * t) *
                                 (exp (-FR_TL19 * t) *
                                  (exp (-FR_TL20 * t) *
                                   (exp (-FR_TL21 * t) *
                                    (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                             ((1 − exp (-FR_L12 * t)) *
                              (exp (-FR_TL13 * t) *
                               (exp (-FR_TL14 * t) *
                                (exp (-FR_TL15 * t) *
                                 (exp (-FR_TL18 * t) *
                                  (exp (-FR_TL19 * t) *
                                   (exp (-FR_TL20 * t) *
                                    (exp (-FR_TL21 * t) *
                                     (exp (-FR_TL16 * t) *
                                      (1 − exp (-FR_TL17 * t)))))))))) +
                              ((1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       exp (-FR_TL17 * t))))))))) +
                               (1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       (1 − exp (-FR_TL17 * t)))))))))))))))))))))))))))))))))) * MTTR_B * 0.15 * CN_B +
        (exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              ((1 − exp (-FR_TL21 * t)) *
               (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             (exp (-FR_TL18 * t) *
              (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  ((1 − exp (-FR_TL21 * t)) *
                   (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 (exp (-FR_TL15 * t) *
                  ((1 − exp (-FR_TL18 * t)) * (1 − exp (-FR_TL19 * t)))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     ((1 − exp (-FR_TL21 * t)) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t)))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) * (1 − exp (-FR_TL19 * t))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          ((1 − exp (-FR_TL21 * t)) *
                           (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           ((1 − exp (-FR_TL21 * t)) *
                            (1 − exp (-FR_TL16 * t))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) * (1 − exp (-FR_TL18 * t))))) +
                        (exp (-FR_L12 * t) *
                         (exp (-FR_TL13 * t) *
                          ((1 − exp (-FR_TL14 * t)) *
                           (1 − exp (-FR_TL15 * t)))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (1 − exp (-FR_TL21 * t)))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (1 − exp (-FR_TL20 * t))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (1 − exp (-FR_TL19 * t)))))) +
                            (exp (-FR_L12 * t) *
                             ((1 − exp (-FR_TL13 * t)) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (1 − exp (-FR_TL18 * t))))) +
                             (exp (-FR_L12 * t) *
                              ((1 − exp (-FR_TL13 * t)) *
                               (exp (-FR_TL14 * t) *
                                (1 − exp (-FR_TL15 * t)))) +
                              (exp (-FR_L12 * t) *
                               ((1 − exp (-FR_TL13 * t)) *
                                (1 − exp (-FR_TL14 * t))) +
                               ((1 − exp (-FR_L12 * t)) *
                                (exp (-FR_TL13 * t) *
                                 (exp (-FR_TL14 * t) *
                                  (exp (-FR_TL15 * t) *
                                   (exp (-FR_TL18 * t) *
                                    (exp (-FR_TL19 * t) *
                                     (exp (-FR_TL20 * t) *
                                      (1 − exp (-FR_TL21 * t)))))))) +
                                ((1 − exp (-FR_L12 * t)) *
                                 (exp (-FR_TL13 * t) *
                                  (exp (-FR_TL14 * t) *
                                   (exp (-FR_TL15 * t) *
                                    (exp (-FR_TL18 * t) *
                                     (exp (-FR_TL19 * t) *
                                      (1 − exp (-FR_TL20 * t))))))) +
                                 ((1 − exp (-FR_L12 * t)) *
                                  (exp (-FR_TL13 * t) *
                                   (exp (-FR_TL14 * t) *
                                    (exp (-FR_TL15 * t) *
                                     (exp (-FR_TL18 * t) *
                                      (1 − exp (-FR_TL19 * t)))))) +
                                  ((1 − exp (-FR_L12 * t)) *
                                   (exp (-FR_TL13 * t) *
                                    (exp (-FR_TL14 * t) *
                                     (exp (-FR_TL15 * t) *
                                      (1 − exp (-FR_TL18 * t))))) +
                                   ((1 − exp (-FR_L12 * t)) *
                                    (exp (-FR_TL13 * t) *
                                     (exp (-FR_TL14 * t) *
                                      (1 − exp (-FR_TL15 * t)))) +
                                    ((1 − exp (-FR_L12 * t)) *
                                     (exp (-FR_TL13 * t) *
                                      (1 − exp (-FR_TL14 * t))) +
                                     (1 − exp (-FR_L12 * t)) *
                                     (1 − exp (-FR_TL13 * t)))))))))))))))))))))))))))))))) * MTTR_B * CN_B +
	( exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             (exp (-FR_TL28 * t) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              (exp (-FR_TL28 * t) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               (exp (-FR_TL28 * t) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                (exp (-FR_TL28 * t) *
                 (exp (-FR_TL29 * t) *
                  ((1 − exp (-FR_TL30 * t)) *
                   (exp (-FR_TL31 * t) *
                    (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 (exp (-FR_TL28 * t) *
                  (exp (-FR_TL29 * t) *
                   ((1 − exp (-FR_TL30 * t)) *
                    (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 (exp (-FR_TL27 * t) *
                  (exp (-FR_TL28 * t) *
                   (exp (-FR_TL29 * t) *
                    ((1 − exp (-FR_TL30 * t)) * (1 − exp (-FR_TL31 * t)))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  (exp (-FR_TL27 * t) *
                   (exp (-FR_TL28 * t) *
                    ((1 − exp (-FR_TL29 * t)) *
                     (exp (-FR_TL30 * t) *
                      (exp (-FR_TL31 * t) *
                       (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   (exp (-FR_TL27 * t) *
                    (exp (-FR_TL28 * t) *
                     ((1 − exp (-FR_TL29 * t)) *
                      (exp (-FR_TL30 * t) *
                       (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    (exp (-FR_TL27 * t) *
                     (exp (-FR_TL28 * t) *
                      ((1 − exp (-FR_TL29 * t)) *
                       (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     (exp (-FR_TL27 * t) *
                      (exp (-FR_TL28 * t) *
                       ((1 − exp (-FR_TL29 * t)) * (1 − exp (-FR_TL30 * t))))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     (exp (-FR_TL26 * t) *
                      (exp (-FR_TL27 * t) *
                       ((1 − exp (-FR_TL28 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      (exp (-FR_TL26 * t) *
                       ((1 − exp (-FR_TL27 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t)))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      ((1 − exp (-FR_TL24 * t)) *
                       (exp (-FR_TL25 * t) *
                        (exp (-FR_TL26 * t) *
                         (exp (-FR_TL27 * t) *
                          (exp (-FR_TL28 * t) *
                           (exp (-FR_TL29 * t) *
                            (exp (-FR_TL30 * t) *
                             (exp (-FR_TL31 * t) *
                              (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       ((1 − exp (-FR_TL24 * t)) * (1 − exp (-FR_TL25 * t)))) +
                      (exp (-FR_TL22 * t) *
                       ((1 − exp (-FR_TL23 * t)) *
                        (exp (-FR_TL24 * t) *
                         (exp (-FR_TL25 * t) *
                          (exp (-FR_TL26 * t) *
                           (exp (-FR_TL27 * t) *
                            (exp (-FR_TL28 * t) *
                             (exp (-FR_TL29 * t) *
                              (exp (-FR_TL30 * t) *
                               (exp (-FR_TL31 * t) *
                                (1 − exp (-FR_TL32 * t))))))))))) +
                       (exp (-FR_TL22 * t) *
                        ((1 − exp (-FR_TL23 * t)) *
                         (exp (-FR_TL24 * t) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               ((1 − exp (-FR_TL30 * t)) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                        (exp (-FR_TL22 * t) *
                         ((1 − exp (-FR_TL23 * t)) *
                          (exp (-FR_TL24 * t) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               ((1 − exp (-FR_TL29 * t)) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                         ((1 − exp (-FR_TL22 * t)) *
                          (exp (-FR_TL23 * t) *
                           (exp (-FR_TL24 * t) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (exp (-FR_TL31 * t) *
                                   (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                          ((1 − exp (-FR_TL22 * t)) *
                           (exp (-FR_TL23 * t) *
                            (exp (-FR_TL24 * t) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  ((1 − exp (-FR_TL30 * t)) *
                                   (exp (-FR_TL31 * t) *
                                    (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                           ((1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     (exp (-FR_TL32 * t) *
                                      exp (-FR_TL33 * t))))))))))) +
                            (1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     ((1 − exp (-FR_TL32 * t)) *
                                      exp (-FR_TL33 * t)))))))))))))))))))))))))))))))) * MTTR_C  * 0.15 * CN_C +
        (exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             ((1 − exp (-FR_TL28 * t)) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              ((1 − exp (-FR_TL28 * t)) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               ((1 − exp (-FR_TL28 * t)) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                ((1 − exp (-FR_TL28 * t)) *
                 (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 ((1 − exp (-FR_TL28 * t)) * (1 − exp (-FR_TL29 * t)))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 ((1 − exp (-FR_TL27 * t)) *
                  (exp (-FR_TL29 * t) *
                   (exp (-FR_TL30 * t) *
                    (exp (-FR_TL31 * t) *
                     (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t))))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  ((1 − exp (-FR_TL27 * t)) *
                   (exp (-FR_TL29 * t) *
                    (exp (-FR_TL30 * t) *
                     (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t)))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   ((1 − exp (-FR_TL27 * t)) *
                    (exp (-FR_TL29 * t) *
                     (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    ((1 − exp (-FR_TL27 * t)) *
                     (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t)))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     ((1 − exp (-FR_TL27 * t)) * (1 − exp (-FR_TL29 * t))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     ((1 − exp (-FR_TL26 * t)) *
                      (exp (-FR_TL29 * t) *
                       (exp (-FR_TL30 * t) *
                        (exp (-FR_TL31 * t) *
                         (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      ((1 − exp (-FR_TL26 * t)) *
                       (exp (-FR_TL29 * t) *
                        (exp (-FR_TL30 * t) *
                         (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      (exp (-FR_TL24 * t) *
                       (exp (-FR_TL25 * t) *
                        ((1 − exp (-FR_TL26 * t)) *
                         (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       (exp (-FR_TL24 * t) *
                        (exp (-FR_TL25 * t) *
                         ((1 − exp (-FR_TL26 * t)) *
                          (1 − exp (-FR_TL29 * t)))))) +
                      (exp (-FR_TL22 * t) *
                       (exp (-FR_TL23 * t) *
                        (exp (-FR_TL24 * t) * (1 − exp (-FR_TL25 * t)))) +
                       (exp (-FR_TL22 * t) *
                        (exp (-FR_TL23 * t) *
                         ((1 − exp (-FR_TL24 * t)) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               (exp (-FR_TL30 * t) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) *
                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                        (exp (-FR_TL22 * t) *
                         (exp (-FR_TL23 * t) *
                          ((1 − exp (-FR_TL24 * t)) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               (exp (-FR_TL29 * t) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (1 − exp (-FR_TL32 * t))))))))))) +
                         (exp (-FR_TL22 * t) *
                          (exp (-FR_TL23 * t) *
                           ((1 − exp (-FR_TL24 * t)) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (1 − exp (-FR_TL31 * t)))))))))) +
                          (exp (-FR_TL22 * t) *
                           (exp (-FR_TL23 * t) *
                            ((1 − exp (-FR_TL24 * t)) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  (1 − exp (-FR_TL30 * t))))))))) +
                           (exp (-FR_TL22 * t) *
                            (exp (-FR_TL23 * t) *
                             ((1 − exp (-FR_TL24 * t)) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  (1 − exp (-FR_TL29 * t)))))))) +
                            (exp (-FR_TL22 * t) *
                             (exp (-FR_TL23 * t) *
                              ((1 − exp (-FR_TL24 * t)) *
                               (exp (-FR_TL25 * t) *
                                (exp (-FR_TL26 * t) *
                                 (exp (-FR_TL27 * t) *
                                  (1 − exp (-FR_TL28 * t))))))) +
                             (exp (-FR_TL22 * t) *
                              (exp (-FR_TL23 * t) *
                               ((1 − exp (-FR_TL24 * t)) *
                                (exp (-FR_TL25 * t) *
                                 (exp (-FR_TL26 * t) *
                                  (1 − exp (-FR_TL27 * t)))))) +
                              (exp (-FR_TL22 * t) *
                               (exp (-FR_TL23 * t) *
                                ((1 − exp (-FR_TL24 * t)) *
                                 (exp (-FR_TL25 * t) *
                                  (1 − exp (-FR_TL26 * t))))) +
                               (exp (-FR_TL22 * t) *
                                ((1 − exp (-FR_TL23 * t)) *
                                 (exp (-FR_TL24 * t) *
                                  (exp (-FR_TL25 * t) *
                                   (exp (-FR_TL26 * t) *
                                    (exp (-FR_TL27 * t) *
                                     (exp (-FR_TL28 * t) *
                                      (exp (-FR_TL29 * t) *
                                       (exp (-FR_TL30 * t) *
                                        (exp (-FR_TL31 * t) *
                                         (exp (-FR_TL32 * t) *
                                          exp (-FR_TL33 * t))))))))))) +
                                (exp (-FR_TL22 * t) *
                                 ((1 − exp (-FR_TL23 * t)) *
                                  (exp (-FR_TL24 * t) *
                                   (exp (-FR_TL25 * t) *
                                    (exp (-FR_TL26 * t) *
                                     (exp (-FR_TL27 * t) *
                                      (exp (-FR_TL28 * t) *
                                       (exp (-FR_TL29 * t) *
                                        (exp (-FR_TL30 * t) *
                                         (exp (-FR_TL31 * t) *
                                          (exp (-FR_TL32 * t) *
                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                 (exp (-FR_TL22 * t) *
                                  ((1 − exp (-FR_TL23 * t)) *
                                   (exp (-FR_TL24 * t) *
                                    (exp (-FR_TL25 * t) *
                                     (exp (-FR_TL26 * t) *
                                      (exp (-FR_TL27 * t) *
                                       (exp (-FR_TL28 * t) *
                                        (exp (-FR_TL29 * t) *
                                         (exp (-FR_TL30 * t) *
                                          ((1 − exp (-FR_TL31 * t)) *
                                           (exp (-FR_TL32 * t) *
                                            exp (-FR_TL33 * t))))))))))) +
                                  (exp (-FR_TL22 * t) *
                                   ((1 − exp (-FR_TL23 * t)) *
                                    (exp (-FR_TL24 * t) *
                                     (exp (-FR_TL25 * t) *
                                      (exp (-FR_TL26 * t) *
                                       (exp (-FR_TL27 * t) *
                                        (exp (-FR_TL28 * t) *
                                         (exp (-FR_TL29 * t) *
                                          (exp (-FR_TL30 * t) *
                                           ((1 − exp (-FR_TL31 * t)) *
                                            (exp (-FR_TL32 * t) *
                                             (1 − exp (-FR_TL33 * t)))))))))))) +
                                   (exp (-FR_TL22 * t) *
                                    ((1 − exp (-FR_TL23 * t)) *
                                     (exp (-FR_TL24 * t) *
                                      (exp (-FR_TL25 * t) *
                                       (exp (-FR_TL26 * t) *
                                        (exp (-FR_TL27 * t) *
                                         (exp (-FR_TL28 * t) *
                                          (exp (-FR_TL29 * t) *
                                           (exp (-FR_TL30 * t) *
                                            ((1 − exp (-FR_TL31 * t)) *
                                             (1 − exp (-FR_TL32 * t))))))))))) +
                                    (exp (-FR_TL22 * t) *
                                     ((1 − exp (-FR_TL23 * t)) *
                                      (exp (-FR_TL24 * t) *
                                       (exp (-FR_TL25 * t) *
                                        (exp (-FR_TL26 * t) *
                                         (exp (-FR_TL27 * t) *
                                          (exp (-FR_TL28 * t) *
                                           (exp (-FR_TL29 * t) *
                                            ((1 − exp (-FR_TL30 * t)) *
                                             (exp (-FR_TL31 * t) *
                                              (exp (-FR_TL32 * t) *
                                               (1 − exp (-FR_TL33 * t)))))))))))) +
                                     (exp (-FR_TL22 * t) *
                                      ((1 − exp (-FR_TL23 * t)) *
                                       (exp (-FR_TL24 * t) *
                                        (exp (-FR_TL25 * t) *
                                         (exp (-FR_TL26 * t) *
                                          (exp (-FR_TL27 * t) *
                                           (exp (-FR_TL28 * t) *
                                            (exp (-FR_TL29 * t) *
                                             ((1 − exp (-FR_TL30 * t)) *
                                              (exp (-FR_TL31 * t) *
                                               (1 − exp (-FR_TL32 * t))))))))))) +
                                      (exp (-FR_TL22 * t) *
                                       ((1 − exp (-FR_TL23 * t)) *
                                        (exp (-FR_TL24 * t) *
                                         (exp (-FR_TL25 * t) *
                                          (exp (-FR_TL26 * t) *
                                           (exp (-FR_TL27 * t) *
                                            (exp (-FR_TL28 * t) *
                                             (exp (-FR_TL29 * t) *
                                              ((1 − exp (-FR_TL30 * t)) *
                                               ((1 − exp (-FR_TL31 * t)) *
                                                (1 − exp (-FR_TL32 * t))))))))))) +
                                       (exp (-FR_TL22 * t) *
                                        ((1 − exp (-FR_TL23 * t)) *
                                         (exp (-FR_TL24 * t) *
                                          (exp (-FR_TL25 * t) *
                                           (exp (-FR_TL26 * t) *
                                            (exp (-FR_TL27 * t) *
                                             (exp (-FR_TL28 * t) *
                                              ((1 − exp (-FR_TL29 * t)) *
                                               (exp (-FR_TL30 * t) *
                                                (exp (-FR_TL31 * t) *
                                                 (exp (-FR_TL32 * t) *
                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                        (exp (-FR_TL22 * t) *
                                         ((1 − exp (-FR_TL23 * t)) *
                                          (exp (-FR_TL24 * t) *
                                           (exp (-FR_TL25 * t) *
                                            (exp (-FR_TL26 * t) *
                                             (exp (-FR_TL27 * t) *
                                              (exp (-FR_TL28 * t) *
                                               ((1 − exp (-FR_TL29 * t)) *
                                                (exp (-FR_TL30 * t) *
                                                 (exp (-FR_TL31 * t) *
                                                  (1 − exp (-FR_TL32 * t))))))))))) +
                                         (exp (-FR_TL22 * t) *
                                          ((1 − exp (-FR_TL23 * t)) *
                                           (exp (-FR_TL24 * t) *
                                            (exp (-FR_TL25 * t) *
                                             (exp (-FR_TL26 * t) *
                                              (exp (-FR_TL27 * t) *
                                               (exp (-FR_TL28 * t) *
                                                ((1 − exp (-FR_TL29 * t)) *
                                                 (exp (-FR_TL30 * t) *
                                                  (1 − exp (-FR_TL31 * t)))))))))) +
                                          (exp (-FR_TL22 * t) *
                                           ((1 − exp (-FR_TL23 * t)) *
                                            (exp (-FR_TL24 * t) *
                                             (exp (-FR_TL25 * t) *
                                              (exp (-FR_TL26 * t) *
                                               (exp (-FR_TL27 * t) *
                                                (exp (-FR_TL28 * t) *
                                                 ((1 − exp (-FR_TL29 * t)) *
                                                  (1 − exp (-FR_TL30 * t))))))))) +
                                           (exp (-FR_TL22 * t) *
                                            ((1 − exp (-FR_TL23 * t)) *
                                             (exp (-FR_TL24 * t) *
                                              (exp (-FR_TL25 * t) *
                                               (exp (-FR_TL26 * t) *
                                                (exp (-FR_TL27 * t) *
                                                 (1 − exp (-FR_TL28 * t))))))) +
                                            (exp (-FR_TL22 * t) *
                                             ((1 − exp (-FR_TL23 * t)) *
                                              (exp (-FR_TL24 * t) *
                                               (exp (-FR_TL25 * t) *
                                                (exp (-FR_TL26 * t) *
                                                 (1 − exp (-FR_TL27 * t)))))) +
                                             (exp (-FR_TL22 * t) *
                                              ((1 − exp (-FR_TL23 * t)) *
                                               (exp (-FR_TL24 * t) *
                                                (exp (-FR_TL25 * t) *
                                                 (1 − exp (-FR_TL26 * t))))) +
                                              (exp (-FR_TL22 * t) *
                                               ((1 − exp (-FR_TL23 * t)) *
                                                (exp (-FR_TL24 * t) *
                                                 (1 − exp (-FR_TL25 * t)))) +
                                               (exp (-FR_TL22 * t) *
                                                ((1 − exp (-FR_TL23 * t)) *
                                                 (1 − exp (-FR_TL24 * t))) +
                                                ((1 − exp (-FR_TL22 * t)) *
                                                 (exp (-FR_TL23 * t) *
                                                  (exp (-FR_TL24 * t) *
                                                   (exp (-FR_TL25 * t) *
                                                    (exp (-FR_TL26 * t) *
                                                     (exp (-FR_TL27 * t) *
                                                      (exp (-FR_TL28 * t) *
                                                       (exp (-FR_TL29 * t) *
                                                        (exp (-FR_TL30 * t) *
                                                         (exp (-FR_TL31 * t) *
                                                          (exp (-FR_TL32 * t) *
                                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                                 ((1 − exp (-FR_TL22 * t)) *
                                                  (exp (-FR_TL23 * t) *
                                                   (exp (-FR_TL24 * t) *
                                                    (exp (-FR_TL25 * t) *
                                                     (exp (-FR_TL26 * t) *
                                                      (exp (-FR_TL27 * t) *
                                                       (exp (-FR_TL28 * t) *
                                                        (exp (-FR_TL29 * t) *
                                                         (exp (-FR_TL30 * t) *
                                                          (exp (-FR_TL31 * t) *
                                                           (1 − exp (-FR_TL32 * t))))))))))) +
                                                  ((1 − exp (-FR_TL22 * t)) *
                                                   (exp (-FR_TL23 * t) *
                                                    (exp (-FR_TL24 * t) *
                                                     (exp (-FR_TL25 * t) *
                                                      (exp (-FR_TL26 * t) *
                                                       (exp (-FR_TL27 * t) *
                                                        (exp (-FR_TL28 * t) *
                                                         (exp (-FR_TL29 * t) *
                                                          (exp (-FR_TL30 * t) *
                                                           (1 − exp (-FR_TL31 * t)))))))))) +
                                                   ((1 − exp (-FR_TL22 * t)) *
                                                    (exp (-FR_TL23 * t) *
                                                     (exp (-FR_TL24 * t) *
                                                      (exp (-FR_TL25 * t) *
                                                       (exp (-FR_TL26 * t) *
                                                        (exp (-FR_TL27 * t) *
                                                         (exp (-FR_TL28 * t) *
                                                          (exp (-FR_TL29 * t) *
                                                           ((1 − exp (-FR_TL30 * t)) *
                                                            (exp (-FR_TL31 * t) *
                                                             (exp (-FR_TL32 * t) *
                                                              (1 − exp (-FR_TL33 * t)))))))))))) +
                                                    ((1 − exp (-FR_TL22 * t)) *
                                                     (exp (-FR_TL23 * t) *
                                                      (exp (-FR_TL24 * t) *
                                                       (exp (-FR_TL25 * t) *
                                                        (exp (-FR_TL26 * t) *
                                                         (exp (-FR_TL27 * t) *
                                                          (exp (-FR_TL28 * t) *
                                                           (exp  (-FR_TL29 * t) *
                                                            ((1 − exp (-FR_TL30 * t)) *
                                                             (exp (-FR_TL31 * t) *
                                                              (1 −  exp (-FR_TL32 * t))))))))))) +
                                                     ((1 − exp (-FR_TL22 * t)) *
                                                      (exp (-FR_TL23 * t) *
                                                       (exp (-FR_TL24 * t) *
                                                        (exp (-FR_TL25 * t) *
                                                         (exp (-FR_TL26 * t) *
                                                          (exp (-FR_TL27 * t) *
                                                           (exp (-FR_TL28 * t) *
                                                            (exp (-FR_TL29 * t) *
                                                             ((1 −  exp (-FR_TL30 * t)) *
                                                              (1 − exp (-FR_TL31 * t)))))))))) +
                                                      ((1 − exp (-FR_TL22 * t)) *
                                                       (exp (-FR_TL23 * t) *
                                                        (exp (-FR_TL24 * t) *
                                                         (exp (-FR_TL25 * t) *
                                                          (exp (-FR_TL26 * t) *
                                                           (exp (-FR_TL27 * t) *
                                                            (exp  (-FR_TL28 * t) *
                                                             ((1 − exp (-FR_TL29 * t)) *
                                                              (exp (-FR_TL30 * t) *
                                                               (exp (-FR_TL31 * t) *
                                                                (exp (-FR_TL32 * t) *
                                                                 (1 − exp (-FR_TL33 * t)))))))))))) +
                                                       ((1 − exp (-FR_TL22 * t)) *
                                                        (exp (-FR_TL23 * t) *
                                                         (exp (-FR_TL24 * t) *
                                                          (exp (-FR_TL25 * t) *
                                                           (exp (-FR_TL26 * t) *
                                                            (exp  (-FR_TL27 * t) *
                                                             (exp (-FR_TL28 * t) *
                                                              ((1 −  exp (-FR_TL29 * t)) *
                                                               (exp (-FR_TL30 * t) *
                                                                (exp (-FR_TL31 * t) *
                                                                 ((1 − exp (-FR_TL32 * t)) *
                                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                                        ((1 − exp (-FR_TL22 * t)) *
                                                         (exp (-FR_TL23 * t) *
                                                          (exp (-FR_TL24 * t) *
                                                           (exp (-FR_TL25 * t) *
                                                            (exp (-FR_TL26 * t) *
                                                             (exp (-FR_TL27 * t) *
                                                              (exp (-FR_TL28 * t) *
                                                               ((1 − exp (-FR_TL29 * t)) *
                                                                (exp (-FR_TL30 * t) *
                                                                 (1 − exp (-FR_TL31 * t)))))))))) +
                                                         ((1 − exp (-FR_TL22 * t)) *
                                                          (exp (-FR_TL23 * t) *
                                                           (exp (-FR_TL24 * t) *
                                                            (exp (-FR_TL25 * t) *
                                                             (exp (-FR_TL26 * t) *
                                                              (exp (-FR_TL27 * t) *
                                                               (exp (-FR_TL28 * t) *
                                                                ((1 − exp (-FR_TL29 * t)) *
                                                                 (1 −  exp (-FR_TL30 * t))))))))) +
                                                          ((1 − exp (-FR_TL22 * t)) *
                                                           (exp (-FR_TL23 * t) *
                                                            (exp (-FR_TL24 * t) *
                                                             (exp (-FR_TL25 * t) *
                                                              (exp (-FR_TL26 * t) *
                                                               (exp (-FR_TL27 * t) *
                                                                (1 − exp (-FR_TL28 * t))))))) +
                                                           ((1 − exp (-FR_TL22 * t)) *
                                                            (exp (-FR_TL23 * t) *
                                                             (exp (-FR_TL24 * t) *
                                                              (exp (-FR_TL25 * t) *
                                                               (exp (-FR_TL26 * t) *
                                                                (1 −  exp (-FR_TL27 * t)))))) +
                                                            ((1 − exp (-FR_TL22 * t)) *
                                                             (exp (-FR_TL23 * t) *
                                                              (exp (-FR_TL24 * t) *
                                                               (exp (-FR_TL25 * t) *
                                                                (1 − exp (-FR_TL26 * t))))) +
                                                             ((1 − exp (-FR_TL22 * t)) *
                                                              (exp (-FR_TL23 * t) *
                                                               (exp  (-FR_TL24 * t) *
                                                                (1 −exp (-FR_TL25 * t)))) +
                                                              ((1 − exp (-FR_TL22 * t)) *
                                                               (exp (-FR_TL23 * t) *
                                                                (1 −  exp (-FR_TL24 * t))) +
                                                               (1 − exp (-FR_TL22 * t)) *
                                                               (1 − exp (-FR_TL23 * t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * MTTR_C * CN_C) / (CN_A + CN_B + CN_C)``
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------*)  
(*    CAIDI Reliability Index     *)
(*--------------------------------*)

CAIDI
``((exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           (exp (-FR_TL5 * t) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) *
               ((1 − exp (-FR_TL9 * t)) *
                (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            (exp (-FR_TL5 * t) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               (exp (-FR_TL8 * t) *
                ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t)))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             (exp (-FR_TL5 * t) *
              (exp (-FR_TL6 * t) *
               (exp (-FR_TL7 * t) *
                ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              (exp (-FR_TL5 * t) *
               (exp (-FR_TL6 * t) *
                ((1 − exp (-FR_TL7 * t)) *
                 ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               (exp (-FR_TL5 * t) *
                (exp (-FR_TL6 * t) *
                 ((1 − exp (-FR_TL7 * t)) *
                  ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                (exp (-FR_TL5 * t) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 (exp (-FR_TL5 * t) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  (exp (-FR_TL5 * t) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   (exp (-FR_TL5 * t) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    (exp (-FR_TL5 * t) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    (exp (-FR_TL4 * t) *
                     ((1 − exp (-FR_TL5 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) * exp (-FR_TL9 * t)))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     (exp (-FR_TL4 * t) *
                      ((1 − exp (-FR_TL5 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         (exp (-FR_TL8 * t) * exp (-FR_TL9 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) *
                         (exp (-FR_TL7 * t) *
                          (exp (-FR_TL8 * t) *
                           ((1 − exp (-FR_TL9 * t)) *
                            (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             ((1 − exp (-FR_TL9 * t)) *
                              (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         ((1 − exp (-FR_TL3 * t)) *
                          (exp (-FR_TL4 * t) *
                           (exp (-FR_TL5 * t) *
                            (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          ((1 − exp (-FR_TL3 * t)) *
                           (exp (-FR_TL4 * t) *
                            (exp (-FR_TL5 * t) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          ((1 − exp (-FR_TL2 * t)) *
                           (exp (-FR_TL3 * t) *
                            (exp (-FR_TL4 * t) *
                             (exp (-FR_TL5 * t) *
                              (exp (-FR_TL8 * t) *
                               (exp (-FR_TL9 * t) * (1 − exp (-FR_TL11 * t)))))))) +
                          (exp (-FR_TL1 * t) *
                           ((1 − exp (-FR_TL2 * t)) *
                            (exp (-FR_TL3 * t) *
                             (exp (-FR_TL4 * t) *
                              (exp (-FR_TL5 * t) *
                               (exp (-FR_TL8 * t) *
                                ((1 − exp (-FR_TL9 * t)) *
                                 (exp (-FR_TL10 * t) *
                                  (1 − exp (-FR_TL11 * t))))))))) +
                           (exp (-FR_TL1 * t) *
                            ((1 − exp (-FR_TL2 * t)) *
                             (exp (-FR_TL3 * t) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL8 * t) *
                                 ((1 − exp (-FR_TL9 * t)) *
                                  ((1 − exp (-FR_TL10 * t)) *
                                   (1 − exp (-FR_TL11 * t))))))))) +
                            (exp (-FR_TL1 * t) *
                             ((1 − exp (-FR_TL2 * t)) *
                              (exp (-FR_TL3 * t) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL8 * t)) *
                                  (exp (-FR_TL9 * t) *
                                   (exp (-FR_TL10 * t) *
                                    (1 − exp (-FR_TL11 * t))))))))) +
                             ((1 − exp (-FR_TL1 * t)) *
                              (exp (-FR_TL2 * t) *
                               (exp (-FR_TL3 * t) *
                                (exp (-FR_TL6 * t) *
                                 (exp (-FR_TL7 * t) *
                                  (exp (-FR_TL8 * t) *
                                   (exp (-FR_TL9 * t) *
                                    (exp (-FR_TL10 * t) *
                                     (1 − exp (-FR_TL11 * t))))))))) +
                              ((1 − exp (-FR_TL1 * t)) *
                               (exp (-FR_TL2 * t) *
                                (exp (-FR_TL3 * t) *
                                 (exp (-FR_TL6 * t) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL8 * t) *
                                    ((1 − exp (-FR_TL9 * t)) *
                                     (exp (-FR_TL10 * t) *
                                      (1 − exp (-FR_TL11 * t))))))))) +
                               ((1 − exp (-FR_TL1 * t)) *
                                (exp (-FR_TL2 * t) *
                                 (exp (-FR_TL3 * t) *
                                  (exp (-FR_TL6 * t) *
                                   (exp (-FR_TL7 * t) *
                                    ((1 − exp (-FR_TL8 * t)) *
                                     (exp (-FR_TL9 * t) *
                                      (exp (-FR_TL10 * t) *
                                       (1 − exp (-FR_TL11 * t))))))))) +
                                ((1 − exp (-FR_TL1 * t)) *
                                 (exp (-FR_TL2 * t) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL6 * t) *
                                    (exp (-FR_TL7 * t) *
                                     ((1 − exp (-FR_TL8 * t)) *
                                      ((1 − exp (-FR_TL9 * t)) *
                                       (exp (-FR_TL10 * t) *
                                        (1 − exp (-FR_TL11 * t))))))))) +
                                 ((1 − exp (-FR_TL1 * t)) *
                                  (exp (-FR_TL2 * t) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL6 * t) *
                                     ((1 − exp (-FR_TL7 * t)) *
                                      (exp (-FR_TL8 * t) *
                                       (exp (-FR_TL9 * t) *
                                        (exp (-FR_TL10 * t) *
                                         (1 − exp (-FR_TL11 * t))))))))) +
                                  ((1 − exp (-FR_TL1 * t)) *
                                   (exp (-FR_TL2 * t) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL6 * t) *
                                      ((1 − exp (-FR_TL7 * t)) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         (exp (-FR_TL10 * t) *
                                          exp (-FR_TL11 * t)))))))) +
                                   ((1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL6 * t) *
                                       ((1 − exp (-FR_TL7 * t)) *
                                        (exp (-FR_TL8 * t) *
                                         ((1 − exp (-FR_TL9 * t)) *
                                          (1 − exp (-FR_TL10 * t)))))))) +
                                    (1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      ((1 − exp (-FR_TL6 * t)) *
                                       (exp (-FR_TL7 * t) *
                                        (exp (-FR_TL8 * t) *
                                         (exp (-FR_TL9 * t) *
                                          (1 − exp (-FR_TL10 * t))))))))))))))))))))))))))))))))))))) * MTTR_A * 0.15 * CN_A +
        (exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           ((1 − exp (-FR_TL5 * t)) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            ((1 − exp (-FR_TL5 * t)) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             ((1 − exp (-FR_TL5 * t)) *
              (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              ((1 − exp (-FR_TL5 * t)) *
               ((1 − exp (-FR_TL6 * t)) *
                (exp (-FR_TL7 * t) *
                 (exp (-FR_TL8 * t) *
                  (exp (-FR_TL9 * t) *
                   (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               ((1 − exp (-FR_TL5 * t)) *
                ((1 − exp (-FR_TL6 * t)) *
                 (exp (-FR_TL7 * t) *
                  (exp (-FR_TL8 * t) *
                   (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                ((1 − exp (-FR_TL5 * t)) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 ((1 − exp (-FR_TL5 * t)) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  ((1 − exp (-FR_TL5 * t)) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   ((1 − exp (-FR_TL5 * t)) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    ((1 − exp (-FR_TL5 * t)) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    ((1 − exp (-FR_TL4 * t)) *
                     (exp (-FR_TL6 * t) *
                      (exp (-FR_TL7 * t) *
                       (exp (-FR_TL8 * t) *
                        ((1 − exp (-FR_TL9 * t)) *
                         (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     ((1 − exp (-FR_TL4 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) *
                         ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t))))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t)))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         (exp (-FR_TL3 * t) *
                          ((1 − exp (-FR_TL4 * t)) *
                           ((1 − exp (-FR_TL6 * t)) *
                            (exp (-FR_TL7 * t) *
                             (exp (-FR_TL8 * t) *
                              ((1 − exp (-FR_TL9 * t)) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t)))))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          (exp (-FR_TL3 * t) *
                           ((1 − exp (-FR_TL4 * t)) *
                            ((1 − exp (-FR_TL6 * t)) *
                             (exp (-FR_TL7 * t) *
                              (exp (-FR_TL8 * t) *
                               ((1 − exp (-FR_TL9 * t)) *
                                (1 − exp (-FR_TL10 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          (exp (-FR_TL2 * t) *
                           (exp (-FR_TL3 * t) *
                            ((1 − exp (-FR_TL4 * t)) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                          (exp (-FR_TL1 * t) *
                           (exp (-FR_TL2 * t) *
                            (exp (-FR_TL3 * t) *
                             ((1 − exp (-FR_TL4 * t)) *
                              ((1 − exp (-FR_TL6 * t)) *
                               (1 − exp (-FR_TL7 * t)))))) +
                           (exp (-FR_TL1 * t) *
                            (exp (-FR_TL2 * t) *
                             ((1 − exp (-FR_TL3 * t)) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL6 * t) * exp (-FR_TL7 * t)))))) +
                            (exp (-FR_TL1 * t) *
                             (exp (-FR_TL2 * t) *
                              ((1 − exp (-FR_TL3 * t)) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL6 * t)) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL10 * t) * exp (-FR_TL11 * t)))))))) +
                             (exp (-FR_TL1 * t) *
                              (exp (-FR_TL2 * t) *
                               ((1 − exp (-FR_TL3 * t)) *
                                (exp (-FR_TL4 * t) *
                                 (exp (-FR_TL5 * t) *
                                  ((1 − exp (-FR_TL6 * t)) *
                                   (exp (-FR_TL7 * t) *
                                    (1 − exp (-FR_TL10 * t)))))))) +
                              (exp (-FR_TL1 * t) *
                               (exp (-FR_TL2 * t) *
                                ((1 − exp (-FR_TL3 * t)) *
                                 (exp (-FR_TL4 * t) *
                                  (exp (-FR_TL5 * t) *
                                   ((1 − exp (-FR_TL6 * t)) *
                                    (1 − exp (-FR_TL7 * t))))))) +
                               (exp (-FR_TL1 * t) *
                                (exp (-FR_TL2 * t) *
                                 ((1 − exp (-FR_TL3 * t)) *
                                  (exp (-FR_TL4 * t) *
                                   (1 − exp (-FR_TL5 * t))))) +
                                (exp (-FR_TL1 * t) *
                                 ((1 − exp (-FR_TL2 * t)) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL4 * t) *
                                    (exp (-FR_TL5 * t) *
                                     (exp (-FR_TL8 * t) *
                                      (exp (-FR_TL9 * t) *
                                       exp (-FR_TL11 * t))))))) +
                                 (exp (-FR_TL1 * t) *
                                  ((1 − exp (-FR_TL2 * t)) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL4 * t) *
                                     (exp (-FR_TL5 * t) *
                                      (exp (-FR_TL8 * t) *
                                       ((1 − exp (-FR_TL9 * t)) *
                                        (exp (-FR_TL10 * t) *
                                         exp (-FR_TL11 * t)))))))) +
                                  (exp (-FR_TL1 * t) *
                                   ((1 − exp (-FR_TL2 * t)) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL4 * t) *
                                      (exp (-FR_TL5 * t) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         ((1 − exp (-FR_TL10 * t)) *
                                          exp (-FR_TL11 * t)))))))) +
                                   (exp (-FR_TL1 * t) *
                                    ((1 − exp (-FR_TL2 * t)) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL4 * t) *
                                       (exp (-FR_TL5 * t) *
                                        ((1 − exp (-FR_TL8 * t)) *
                                         (exp (-FR_TL9 * t) *
                                          (exp (-FR_TL10 * t) *
                                           exp (-FR_TL11 * t)))))))) +
                                    (exp (-FR_TL1 * t) *
                                     ((1 − exp (-FR_TL2 * t)) *
                                      (exp (-FR_TL3 * t) *
                                       (exp (-FR_TL4 * t) *
                                        (exp (-FR_TL5 * t) *
                                         ((1 − exp (-FR_TL8 * t)) *
                                          (exp (-FR_TL9 * t) *
                                           (1 − exp (-FR_TL10 * t)))))))) +
                                     (exp (-FR_TL1 * t) *
                                      ((1 − exp (-FR_TL2 * t)) *
                                       (exp (-FR_TL3 * t) *
                                        (exp (-FR_TL4 * t) *
                                         (exp (-FR_TL5 * t) *
                                          ((1 − exp (-FR_TL8 * t)) *
                                           (1 − exp (-FR_TL9 * t))))))) +
                                      (exp (-FR_TL1 * t) *
                                       ((1 − exp (-FR_TL2 * t)) *
                                        (exp (-FR_TL3 * t) *
                                         (exp (-FR_TL4 * t) *
                                          (1 − exp (-FR_TL5 * t))))) +
                                       (exp (-FR_TL1 * t) *
                                        ((1 − exp (-FR_TL2 * t)) *
                                         (exp (-FR_TL3 * t) *
                                          (1 − exp (-FR_TL4 * t)))) +
                                        (exp (-FR_TL1 * t) *
                                         ((1 − exp (-FR_TL2 * t)) *
                                          (1 − exp (-FR_TL3 * t))) +
                                         ((1 − exp (-FR_TL1 * t)) *
                                          (exp (-FR_TL2 * t) *
                                           (exp (-FR_TL3 * t) *
                                            (exp (-FR_TL6 * t) *
                                             (exp (-FR_TL7 * t) *
                                              (exp (-FR_TL8 * t) *
                                               (exp (-FR_TL9 * t) *
                                                (exp (-FR_TL10 * t) *
                                                 exp (-FR_TL11 * t)))))))) +
                                          ((1 − exp (-FR_TL1 * t)) *
                                           (exp (-FR_TL2 * t) *
                                            (exp (-FR_TL3 * t) *
                                             (exp (-FR_TL6 * t) *
                                              (exp (-FR_TL7 * t) *
                                               (exp (-FR_TL8 * t) *
                                                (exp (-FR_TL9 * t) *
                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                           ((1 − exp (-FR_TL1 * t)) *
                                            (exp (-FR_TL2 * t) *
                                             (exp (-FR_TL3 * t) *
                                              (exp (-FR_TL6 * t) *
                                               (exp (-FR_TL7 * t) *
                                                (exp (-FR_TL8 * t) *
                                                 ((1 − exp (-FR_TL9 * t)) *
                                                  (exp (-FR_TL10 * t) *
                                                   exp (-FR_TL11 * t)))))))) +
                                            ((1 − exp (-FR_TL1 * t)) *
                                             (exp (-FR_TL2 * t) *
                                              (exp (-FR_TL3 * t) *
                                               (exp (-FR_TL6 * t) *
                                                (exp (-FR_TL7 * t) *
                                                 (exp (-FR_TL8 * t) *
                                                  ((1 − exp (-FR_TL9 * t)) *
                                                   (1 − exp (-FR_TL10 * t)))))))) +
                                             ((1 − exp (-FR_TL1 * t)) *
                                              (exp (-FR_TL2 * t) *
                                               (exp (-FR_TL3 * t) *
                                                (exp (-FR_TL6 * t) *
                                                 (exp (-FR_TL7 * t) *
                                                  ((1 − exp (-FR_TL8 * t)) *
                                                   (exp (-FR_TL9 * t) *
                                                    (exp (-FR_TL10 * t) *
                                                     exp (-FR_TL11 * t)))))))) +
                                              ((1 − exp (-FR_TL1 * t)) *
                                               (exp (-FR_TL2 * t) *
                                                (exp (-FR_TL3 * t) *
                                                 (exp (-FR_TL6 * t) *
                                                  (exp (-FR_TL7 * t) *
                                                   ((1 − exp (-FR_TL8 * t)) *
                                                    (exp (-FR_TL9 * t) *
                                                     (1 − exp (-FR_TL10 * t)))))))) +
                                               ((1 − exp (-FR_TL1 * t)) *
                                                (exp (-FR_TL2 * t) *
                                                 (exp (-FR_TL3 * t) *
                                                  (exp (-FR_TL6 * t) *
                                                   (exp (-FR_TL7 * t) *
                                                    ((1 − exp (-FR_TL8 * t)) *
                                                     ((1 − exp (-FR_TL9 * t)) *
                                                      (exp (-FR_TL10 * t) *
                                                       exp (-FR_TL11 * t)))))))) +
                                                ((1 − exp (-FR_TL1 * t)) *
                                                 (exp (-FR_TL2 * t) *
                                                  (exp (-FR_TL3 * t) *
                                                   (exp (-FR_TL6 * t) *
                                                    (exp (-FR_TL7 * t) *
                                                     ((1 − exp (-FR_TL8 * t)) *
                                                      ((1 − exp (-FR_TL9 * t)) *
                                                       (1 −
                                                        exp (-FR_TL10 * t)))))))) +
                                                 ((1 − exp (-FR_TL1 * t)) *
                                                  (exp (-FR_TL2 * t) *
                                                   (exp (-FR_TL3 * t) *
                                                    (exp (-FR_TL6 * t) *
                                                     ((1 − exp (-FR_TL7 * t)) *
                                                      (exp (-FR_TL8 * t) *
                                                       (exp (-FR_TL9 * t) *
                                                        (exp (-FR_TL10 * t) *
                                                         exp (-FR_TL11 * t)))))))) +
                                                  ((1 − exp (-FR_TL1 * t)) *
                                                   (exp (-FR_TL2 * t) *
                                                    (exp (-FR_TL3 * t) *
                                                     (exp (-FR_TL6 * t) *
                                                      ((1 − exp (-FR_TL7 * t)) *
                                                       (exp (-FR_TL8 * t) *
                                                        (exp (-FR_TL9 * t) *
                                                         (1 −  exp (-FR_TL10 * t)))))))) +
                                                   ((1 − exp (-FR_TL1 * t)) *
                                                    (exp (-FR_TL2 * t) *
                                                     (exp (-FR_TL3 * t) *
                                                      (exp (-FR_TL6 * t) *
                                                       ((1 − exp (-FR_TL7 * t)) *
                                                        (exp (-FR_TL8 * t) *
                                                         ((1 − exp (-FR_TL9 * t)) *
                                                          (exp (-FR_TL10 * t) *
                                                           (1 − exp (-FR_TL11 * t))))))))) +
                                                    ((1 − exp (-FR_TL1 * t)) *
                                                     (exp (-FR_TL2 * t) *
                                                      (exp (-FR_TL3 * t) *
                                                       (exp (-FR_TL6 * t) *
                                                        ((1 − exp (-FR_TL7 * t)) *
                                                         (1 − exp (-FR_TL8 * t)))))) +
                                                     ((1 − exp (-FR_TL1 * t)) *
                                                      (exp (-FR_TL2 * t) *
                                                       (exp (-FR_TL3 * t) *
                                                        ((1 − exp (-FR_TL6 * t)) *
                                                         (exp (-FR_TL7 * t) *
                                                          (exp (-FR_TL8 * t) *
                                                           (exp (-FR_TL9 * t) *
                                                            (exp (-FR_TL10 * t) *
                                                             exp (-FR_TL11 * t)))))))) +
                                                      ((1 − exp (-FR_TL1 * t)) *
                                                       (exp (-FR_TL2 * t) *
                                                        (exp (-FR_TL3 * t) *
                                                         ((1 − exp (-FR_TL6 * t)) *
                                                          (exp (-FR_TL7 * t) *
                                                           (exp (-FR_TL8 * t) *
                                                            (exp(-FR_TL9 * t) *
                                                             (exp (-FR_TL10 * t) *
                                                              (1 − exp (-FR_TL11 * t))))))))) +
                                                       ((1 − exp (-FR_TL1 * t)) *
                                                        (exp (-FR_TL2 * t) *
                                                         (exp (-FR_TL3 * t) *
                                                          ((1 − exp (-FR_TL6 * t)) *
                                                           (exp (-FR_TL7 * t) *
                                                            (exp (-FR_TL8 * t) *
                                                             (1 − exp (-FR_TL9 * t))))))) +
                                                        ((1 −  exp (-FR_TL1 * t)) *
                                                         (exp (-FR_TL2 * t) *
                                                          (exp (-FR_TL3 * t) *
                                                           ((1 − exp (-FR_TL6 * t)) *
                                                            (exp (-FR_TL7 * t) *
                                                             ((1 − exp (-FR_TL8 * t)) *
                                                              (exp (-FR_TL9 * t) *
                                                               (exp (-FR_TL10 * t) *
                                                                exp (-FR_TL11 * t)))))))) +
                                                         ((1 − exp (-FR_TL1 * t)) *
                                                          (exp (-FR_TL2 * t) *
                                                           (exp (-FR_TL3 * t) *
                                                            ((1 − exp (-FR_TL6 * t)) *
                                                             (exp (-FR_TL7 * t) *
                                                              ((1 − exp (-FR_TL8 * t)) *
                                                               (exp (-FR_TL9 * t) *
                                                                (exp (-FR_TL10 * t) *
                                                                 (1 −  exp (-FR_TL11 * t))))))))) +
                                                          ((1 − exp (-FR_TL1 * t)) *
                                                           (exp (-FR_TL2 * t) *
                                                            (exp (-FR_TL3 * t) *
                                                             ((1 − exp (-FR_TL6 * t)) *
                                                              (exp (-FR_TL7 * t) *
                                                               ((1 − exp (-FR_TL8 * t)) *
                                                                (exp (-FR_TL9 * t) *
                                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                                           ((1 − exp  (-FR_TL1 * t)) *
                                                            (exp (-FR_TL2 * t) *
                                                             (exp (-FR_TL3 * t) *
                                                              ((1 − exp (-FR_TL6 * t)) *
                                                               (exp (-FR_TL7 * t) *
                                                                ((1 − exp (-FR_TL8 * t)) *
                                                                 (1 − exp (-FR_TL9 * t))))))) +
                                                            ((1 − exp (-FR_TL1 * t)) *
                                                             (exp (-FR_TL2 * t) *
                                                              (exp (-FR_TL3 * t) *
                                                               ((1 − exp (-FR_TL6 * t)) *
                                                                (1 − exp  (-FR_TL7 * t))))) +
                                                             ((1 − exp (-FR_TL1 * t)) *
                                                              (exp (-FR_TL2 * t) *
                                                               (1 −  exp  (-FR_TL3 * t))) +
                                                              (1 − exp (-FR_TL1 * t)) *
                                                              (1 − exp (-FR_TL2 * t))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * MTTR_A * CN_A +
	(exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              (exp (-FR_TL21 * t) *
               ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) *
                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             ((1 − exp (-FR_TL18 * t)) *
              (exp (-FR_TL19 * t) *
               (exp (-FR_TL20 * t) *
                (exp (-FR_TL21 * t) *
                 (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              ((1 − exp (-FR_TL18 * t)) *
               (exp (-FR_TL19 * t) *
                (exp (-FR_TL20 * t) *
                 (exp (-FR_TL21 * t) *
                  (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  (exp (-FR_TL21 * t) *
                   ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   (exp (-FR_TL21 * t) *
                    ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    ((1 − exp (-FR_TL21 * t)) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 ((1 − exp (-FR_TL15 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    (exp (-FR_TL21 * t) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     (exp (-FR_TL21 * t) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      (exp (-FR_TL21 * t) *
                       ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) *
                      (exp (-FR_TL20 * t) *
                       (exp (-FR_TL21 * t) *
                        ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t))))))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) *
                      (exp (-FR_TL19 * t) *
                       (exp (-FR_TL20 * t) *
                        ((1 − exp (-FR_TL21 * t)) *
                         (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          (exp (-FR_TL21 * t) *
                           (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           (exp (-FR_TL21 * t) *
                            (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) *
                           (exp (-FR_TL20 * t) *
                            (exp (-FR_TL21 * t) *
                             ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) *
                           (exp (-FR_TL19 * t) *
                            (exp (-FR_TL20 * t) *
                             (exp (-FR_TL21 * t) *
                              ((1 − exp (-FR_TL16 * t)) *
                               (1 − exp (-FR_TL17 * t)))))))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) *
                           (exp (-FR_TL18 * t) *
                            (exp (-FR_TL19 * t) *
                             (exp (-FR_TL20 * t) *
                              ((1 − exp (-FR_TL21 * t)) *
                               (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                        (exp (-FR_L12 * t) *
                         ((1 − exp (-FR_TL13 * t)) *
                          (exp (-FR_TL14 * t) *
                           (exp (-FR_TL15 * t) *
                            (exp (-FR_TL18 * t) *
                             (exp (-FR_TL19 * t) *
                              (exp (-FR_TL20 * t) *
                               (exp (-FR_TL21 * t) *
                                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (exp (-FR_TL21 * t) *
                                 (exp (-FR_TL16 * t) *
                                  (1 − exp (-FR_TL17 * t)))))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (exp (-FR_TL20 * t) *
                                 (exp (-FR_TL21 * t) *
                                  (exp (-FR_TL16 * t) *
                                   (1 − exp (-FR_TL17 * t)))))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (exp (-FR_TL19 * t) *
                                 (exp (-FR_TL20 * t) *
                                  (exp (-FR_TL21 * t) *
                                   (exp (-FR_TL16 * t) *
                                    (1 − exp (-FR_TL17 * t)))))))))) +
                            ((1 − exp (-FR_L12 * t)) *
                             (exp (-FR_TL13 * t) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (exp (-FR_TL18 * t) *
                                 (exp (-FR_TL19 * t) *
                                  (exp (-FR_TL20 * t) *
                                   (exp (-FR_TL21 * t) *
                                    (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                             ((1 − exp (-FR_L12 * t)) *
                              (exp (-FR_TL13 * t) *
                               (exp (-FR_TL14 * t) *
                                (exp (-FR_TL15 * t) *
                                 (exp (-FR_TL18 * t) *
                                  (exp (-FR_TL19 * t) *
                                   (exp (-FR_TL20 * t) *
                                    (exp (-FR_TL21 * t) *
                                     (exp (-FR_TL16 * t) *
                                      (1 − exp (-FR_TL17 * t)))))))))) +
                              ((1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       exp (-FR_TL17 * t))))))))) +
                               (1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       (1 − exp (-FR_TL17 * t)))))))))))))))))))))))))))))))))) * MTTR_B * 0.15 * CN_B +
        (exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              ((1 − exp (-FR_TL21 * t)) *
               (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             (exp (-FR_TL18 * t) *
              (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  ((1 − exp (-FR_TL21 * t)) *
                   (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 (exp (-FR_TL15 * t) *
                  ((1 − exp (-FR_TL18 * t)) * (1 − exp (-FR_TL19 * t)))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     ((1 − exp (-FR_TL21 * t)) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t)))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) * (1 − exp (-FR_TL19 * t))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          ((1 − exp (-FR_TL21 * t)) *
                           (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           ((1 − exp (-FR_TL21 * t)) *
                            (1 − exp (-FR_TL16 * t))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) * (1 − exp (-FR_TL18 * t))))) +
                        (exp (-FR_L12 * t) *
                         (exp (-FR_TL13 * t) *
                          ((1 − exp (-FR_TL14 * t)) *
                           (1 − exp (-FR_TL15 * t)))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (1 − exp (-FR_TL21 * t)))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (1 − exp (-FR_TL20 * t))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (1 − exp (-FR_TL19 * t)))))) +
                            (exp (-FR_L12 * t) *
                             ((1 − exp (-FR_TL13 * t)) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (1 − exp (-FR_TL18 * t))))) +
                             (exp (-FR_L12 * t) *
                              ((1 − exp (-FR_TL13 * t)) *
                               (exp (-FR_TL14 * t) *
                                (1 − exp (-FR_TL15 * t)))) +
                              (exp (-FR_L12 * t) *
                               ((1 − exp (-FR_TL13 * t)) *
                                (1 − exp (-FR_TL14 * t))) +
                               ((1 − exp (-FR_L12 * t)) *
                                (exp (-FR_TL13 * t) *
                                 (exp (-FR_TL14 * t) *
                                  (exp (-FR_TL15 * t) *
                                   (exp (-FR_TL18 * t) *
                                    (exp (-FR_TL19 * t) *
                                     (exp (-FR_TL20 * t) *
                                      (1 − exp (-FR_TL21 * t)))))))) +
                                ((1 − exp (-FR_L12 * t)) *
                                 (exp (-FR_TL13 * t) *
                                  (exp (-FR_TL14 * t) *
                                   (exp (-FR_TL15 * t) *
                                    (exp (-FR_TL18 * t) *
                                     (exp (-FR_TL19 * t) *
                                      (1 − exp (-FR_TL20 * t))))))) +
                                 ((1 − exp (-FR_L12 * t)) *
                                  (exp (-FR_TL13 * t) *
                                   (exp (-FR_TL14 * t) *
                                    (exp (-FR_TL15 * t) *
                                     (exp (-FR_TL18 * t) *
                                      (1 − exp (-FR_TL19 * t)))))) +
                                  ((1 − exp (-FR_L12 * t)) *
                                   (exp (-FR_TL13 * t) *
                                    (exp (-FR_TL14 * t) *
                                     (exp (-FR_TL15 * t) *
                                      (1 − exp (-FR_TL18 * t))))) +
                                   ((1 − exp (-FR_L12 * t)) *
                                    (exp (-FR_TL13 * t) *
                                     (exp (-FR_TL14 * t) *
                                      (1 − exp (-FR_TL15 * t)))) +
                                    ((1 − exp (-FR_L12 * t)) *
                                     (exp (-FR_TL13 * t) *
                                      (1 − exp (-FR_TL14 * t))) +
                                     (1 − exp (-FR_L12 * t)) *
                                     (1 − exp (-FR_TL13 * t)))))))))))))))))))))))))))))))) * MTTR_B * CN_B +
	( exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             (exp (-FR_TL28 * t) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              (exp (-FR_TL28 * t) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               (exp (-FR_TL28 * t) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                (exp (-FR_TL28 * t) *
                 (exp (-FR_TL29 * t) *
                  ((1 − exp (-FR_TL30 * t)) *
                   (exp (-FR_TL31 * t) *
                    (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 (exp (-FR_TL28 * t) *
                  (exp (-FR_TL29 * t) *
                   ((1 − exp (-FR_TL30 * t)) *
                    (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 (exp (-FR_TL27 * t) *
                  (exp (-FR_TL28 * t) *
                   (exp (-FR_TL29 * t) *
                    ((1 − exp (-FR_TL30 * t)) * (1 − exp (-FR_TL31 * t)))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  (exp (-FR_TL27 * t) *
                   (exp (-FR_TL28 * t) *
                    ((1 − exp (-FR_TL29 * t)) *
                     (exp (-FR_TL30 * t) *
                      (exp (-FR_TL31 * t) *
                       (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   (exp (-FR_TL27 * t) *
                    (exp (-FR_TL28 * t) *
                     ((1 − exp (-FR_TL29 * t)) *
                      (exp (-FR_TL30 * t) *
                       (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    (exp (-FR_TL27 * t) *
                     (exp (-FR_TL28 * t) *
                      ((1 − exp (-FR_TL29 * t)) *
                       (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     (exp (-FR_TL27 * t) *
                      (exp (-FR_TL28 * t) *
                       ((1 − exp (-FR_TL29 * t)) * (1 − exp (-FR_TL30 * t))))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     (exp (-FR_TL26 * t) *
                      (exp (-FR_TL27 * t) *
                       ((1 − exp (-FR_TL28 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      (exp (-FR_TL26 * t) *
                       ((1 − exp (-FR_TL27 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t)))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      ((1 − exp (-FR_TL24 * t)) *
                       (exp (-FR_TL25 * t) *
                        (exp (-FR_TL26 * t) *
                         (exp (-FR_TL27 * t) *
                          (exp (-FR_TL28 * t) *
                           (exp (-FR_TL29 * t) *
                            (exp (-FR_TL30 * t) *
                             (exp (-FR_TL31 * t) *
                              (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       ((1 − exp (-FR_TL24 * t)) * (1 − exp (-FR_TL25 * t)))) +
                      (exp (-FR_TL22 * t) *
                       ((1 − exp (-FR_TL23 * t)) *
                        (exp (-FR_TL24 * t) *
                         (exp (-FR_TL25 * t) *
                          (exp (-FR_TL26 * t) *
                           (exp (-FR_TL27 * t) *
                            (exp (-FR_TL28 * t) *
                             (exp (-FR_TL29 * t) *
                              (exp (-FR_TL30 * t) *
                               (exp (-FR_TL31 * t) *
                                (1 − exp (-FR_TL32 * t))))))))))) +
                       (exp (-FR_TL22 * t) *
                        ((1 − exp (-FR_TL23 * t)) *
                         (exp (-FR_TL24 * t) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               ((1 − exp (-FR_TL30 * t)) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                        (exp (-FR_TL22 * t) *
                         ((1 − exp (-FR_TL23 * t)) *
                          (exp (-FR_TL24 * t) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               ((1 − exp (-FR_TL29 * t)) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                         ((1 − exp (-FR_TL22 * t)) *
                          (exp (-FR_TL23 * t) *
                           (exp (-FR_TL24 * t) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (exp (-FR_TL31 * t) *
                                   (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                          ((1 − exp (-FR_TL22 * t)) *
                           (exp (-FR_TL23 * t) *
                            (exp (-FR_TL24 * t) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  ((1 − exp (-FR_TL30 * t)) *
                                   (exp (-FR_TL31 * t) *
                                    (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                           ((1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     (exp (-FR_TL32 * t) *
                                      exp (-FR_TL33 * t))))))))))) +
                            (1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     ((1 − exp (-FR_TL32 * t)) *
                                      exp (-FR_TL33 * t)))))))))))))))))))))))))))))))) * MTTR_C  * 0.15 * CN_C +
        (exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             ((1 − exp (-FR_TL28 * t)) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              ((1 − exp (-FR_TL28 * t)) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               ((1 − exp (-FR_TL28 * t)) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                ((1 − exp (-FR_TL28 * t)) *
                 (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 ((1 − exp (-FR_TL28 * t)) * (1 − exp (-FR_TL29 * t)))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 ((1 − exp (-FR_TL27 * t)) *
                  (exp (-FR_TL29 * t) *
                   (exp (-FR_TL30 * t) *
                    (exp (-FR_TL31 * t) *
                     (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t))))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  ((1 − exp (-FR_TL27 * t)) *
                   (exp (-FR_TL29 * t) *
                    (exp (-FR_TL30 * t) *
                     (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t)))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   ((1 − exp (-FR_TL27 * t)) *
                    (exp (-FR_TL29 * t) *
                     (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    ((1 − exp (-FR_TL27 * t)) *
                     (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t)))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     ((1 − exp (-FR_TL27 * t)) * (1 − exp (-FR_TL29 * t))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     ((1 − exp (-FR_TL26 * t)) *
                      (exp (-FR_TL29 * t) *
                       (exp (-FR_TL30 * t) *
                        (exp (-FR_TL31 * t) *
                         (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      ((1 − exp (-FR_TL26 * t)) *
                       (exp (-FR_TL29 * t) *
                        (exp (-FR_TL30 * t) *
                         (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      (exp (-FR_TL24 * t) *
                       (exp (-FR_TL25 * t) *
                        ((1 − exp (-FR_TL26 * t)) *
                         (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       (exp (-FR_TL24 * t) *
                        (exp (-FR_TL25 * t) *
                         ((1 − exp (-FR_TL26 * t)) *
                          (1 − exp (-FR_TL29 * t)))))) +
                      (exp (-FR_TL22 * t) *
                       (exp (-FR_TL23 * t) *
                        (exp (-FR_TL24 * t) * (1 − exp (-FR_TL25 * t)))) +
                       (exp (-FR_TL22 * t) *
                        (exp (-FR_TL23 * t) *
                         ((1 − exp (-FR_TL24 * t)) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               (exp (-FR_TL30 * t) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) *
                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                        (exp (-FR_TL22 * t) *
                         (exp (-FR_TL23 * t) *
                          ((1 − exp (-FR_TL24 * t)) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               (exp (-FR_TL29 * t) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (1 − exp (-FR_TL32 * t))))))))))) +
                         (exp (-FR_TL22 * t) *
                          (exp (-FR_TL23 * t) *
                           ((1 − exp (-FR_TL24 * t)) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (1 − exp (-FR_TL31 * t)))))))))) +
                          (exp (-FR_TL22 * t) *
                           (exp (-FR_TL23 * t) *
                            ((1 − exp (-FR_TL24 * t)) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  (1 − exp (-FR_TL30 * t))))))))) +
                           (exp (-FR_TL22 * t) *
                            (exp (-FR_TL23 * t) *
                             ((1 − exp (-FR_TL24 * t)) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  (1 − exp (-FR_TL29 * t)))))))) +
                            (exp (-FR_TL22 * t) *
                             (exp (-FR_TL23 * t) *
                              ((1 − exp (-FR_TL24 * t)) *
                               (exp (-FR_TL25 * t) *
                                (exp (-FR_TL26 * t) *
                                 (exp (-FR_TL27 * t) *
                                  (1 − exp (-FR_TL28 * t))))))) +
                             (exp (-FR_TL22 * t) *
                              (exp (-FR_TL23 * t) *
                               ((1 − exp (-FR_TL24 * t)) *
                                (exp (-FR_TL25 * t) *
                                 (exp (-FR_TL26 * t) *
                                  (1 − exp (-FR_TL27 * t)))))) +
                              (exp (-FR_TL22 * t) *
                               (exp (-FR_TL23 * t) *
                                ((1 − exp (-FR_TL24 * t)) *
                                 (exp (-FR_TL25 * t) *
                                  (1 − exp (-FR_TL26 * t))))) +
                               (exp (-FR_TL22 * t) *
                                ((1 − exp (-FR_TL23 * t)) *
                                 (exp (-FR_TL24 * t) *
                                  (exp (-FR_TL25 * t) *
                                   (exp (-FR_TL26 * t) *
                                    (exp (-FR_TL27 * t) *
                                     (exp (-FR_TL28 * t) *
                                      (exp (-FR_TL29 * t) *
                                       (exp (-FR_TL30 * t) *
                                        (exp (-FR_TL31 * t) *
                                         (exp (-FR_TL32 * t) *
                                          exp (-FR_TL33 * t))))))))))) +
                                (exp (-FR_TL22 * t) *
                                 ((1 − exp (-FR_TL23 * t)) *
                                  (exp (-FR_TL24 * t) *
                                   (exp (-FR_TL25 * t) *
                                    (exp (-FR_TL26 * t) *
                                     (exp (-FR_TL27 * t) *
                                      (exp (-FR_TL28 * t) *
                                       (exp (-FR_TL29 * t) *
                                        (exp (-FR_TL30 * t) *
                                         (exp (-FR_TL31 * t) *
                                          (exp (-FR_TL32 * t) *
                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                 (exp (-FR_TL22 * t) *
                                  ((1 − exp (-FR_TL23 * t)) *
                                   (exp (-FR_TL24 * t) *
                                    (exp (-FR_TL25 * t) *
                                     (exp (-FR_TL26 * t) *
                                      (exp (-FR_TL27 * t) *
                                       (exp (-FR_TL28 * t) *
                                        (exp (-FR_TL29 * t) *
                                         (exp (-FR_TL30 * t) *
                                          ((1 − exp (-FR_TL31 * t)) *
                                           (exp (-FR_TL32 * t) *
                                            exp (-FR_TL33 * t))))))))))) +
                                  (exp (-FR_TL22 * t) *
                                   ((1 − exp (-FR_TL23 * t)) *
                                    (exp (-FR_TL24 * t) *
                                     (exp (-FR_TL25 * t) *
                                      (exp (-FR_TL26 * t) *
                                       (exp (-FR_TL27 * t) *
                                        (exp (-FR_TL28 * t) *
                                         (exp (-FR_TL29 * t) *
                                          (exp (-FR_TL30 * t) *
                                           ((1 − exp (-FR_TL31 * t)) *
                                            (exp (-FR_TL32 * t) *
                                             (1 − exp (-FR_TL33 * t)))))))))))) +
                                   (exp (-FR_TL22 * t) *
                                    ((1 − exp (-FR_TL23 * t)) *
                                     (exp (-FR_TL24 * t) *
                                      (exp (-FR_TL25 * t) *
                                       (exp (-FR_TL26 * t) *
                                        (exp (-FR_TL27 * t) *
                                         (exp (-FR_TL28 * t) *
                                          (exp (-FR_TL29 * t) *
                                           (exp (-FR_TL30 * t) *
                                            ((1 − exp (-FR_TL31 * t)) *
                                             (1 − exp (-FR_TL32 * t))))))))))) +
                                    (exp (-FR_TL22 * t) *
                                     ((1 − exp (-FR_TL23 * t)) *
                                      (exp (-FR_TL24 * t) *
                                       (exp (-FR_TL25 * t) *
                                        (exp (-FR_TL26 * t) *
                                         (exp (-FR_TL27 * t) *
                                          (exp (-FR_TL28 * t) *
                                           (exp (-FR_TL29 * t) *
                                            ((1 − exp (-FR_TL30 * t)) *
                                             (exp (-FR_TL31 * t) *
                                              (exp (-FR_TL32 * t) *
                                               (1 − exp (-FR_TL33 * t)))))))))))) +
                                     (exp (-FR_TL22 * t) *
                                      ((1 − exp (-FR_TL23 * t)) *
                                       (exp (-FR_TL24 * t) *
                                        (exp (-FR_TL25 * t) *
                                         (exp (-FR_TL26 * t) *
                                          (exp (-FR_TL27 * t) *
                                           (exp (-FR_TL28 * t) *
                                            (exp (-FR_TL29 * t) *
                                             ((1 − exp (-FR_TL30 * t)) *
                                              (exp (-FR_TL31 * t) *
                                               (1 − exp (-FR_TL32 * t))))))))))) +
                                      (exp (-FR_TL22 * t) *
                                       ((1 − exp (-FR_TL23 * t)) *
                                        (exp (-FR_TL24 * t) *
                                         (exp (-FR_TL25 * t) *
                                          (exp (-FR_TL26 * t) *
                                           (exp (-FR_TL27 * t) *
                                            (exp (-FR_TL28 * t) *
                                             (exp (-FR_TL29 * t) *
                                              ((1 − exp (-FR_TL30 * t)) *
                                               ((1 − exp (-FR_TL31 * t)) *
                                                (1 − exp (-FR_TL32 * t))))))))))) +
                                       (exp (-FR_TL22 * t) *
                                        ((1 − exp (-FR_TL23 * t)) *
                                         (exp (-FR_TL24 * t) *
                                          (exp (-FR_TL25 * t) *
                                           (exp (-FR_TL26 * t) *
                                            (exp (-FR_TL27 * t) *
                                             (exp (-FR_TL28 * t) *
                                              ((1 − exp (-FR_TL29 * t)) *
                                               (exp (-FR_TL30 * t) *
                                                (exp (-FR_TL31 * t) *
                                                 (exp (-FR_TL32 * t) *
                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                        (exp (-FR_TL22 * t) *
                                         ((1 − exp (-FR_TL23 * t)) *
                                          (exp (-FR_TL24 * t) *
                                           (exp (-FR_TL25 * t) *
                                            (exp (-FR_TL26 * t) *
                                             (exp (-FR_TL27 * t) *
                                              (exp (-FR_TL28 * t) *
                                               ((1 − exp (-FR_TL29 * t)) *
                                                (exp (-FR_TL30 * t) *
                                                 (exp (-FR_TL31 * t) *
                                                  (1 − exp (-FR_TL32 * t))))))))))) +
                                         (exp (-FR_TL22 * t) *
                                          ((1 − exp (-FR_TL23 * t)) *
                                           (exp (-FR_TL24 * t) *
                                            (exp (-FR_TL25 * t) *
                                             (exp (-FR_TL26 * t) *
                                              (exp (-FR_TL27 * t) *
                                               (exp (-FR_TL28 * t) *
                                                ((1 − exp (-FR_TL29 * t)) *
                                                 (exp (-FR_TL30 * t) *
                                                  (1 − exp (-FR_TL31 * t)))))))))) +
                                          (exp (-FR_TL22 * t) *
                                           ((1 − exp (-FR_TL23 * t)) *
                                            (exp (-FR_TL24 * t) *
                                             (exp (-FR_TL25 * t) *
                                              (exp (-FR_TL26 * t) *
                                               (exp (-FR_TL27 * t) *
                                                (exp (-FR_TL28 * t) *
                                                 ((1 − exp (-FR_TL29 * t)) *
                                                  (1 − exp (-FR_TL30 * t))))))))) +
                                           (exp (-FR_TL22 * t) *
                                            ((1 − exp (-FR_TL23 * t)) *
                                             (exp (-FR_TL24 * t) *
                                              (exp (-FR_TL25 * t) *
                                               (exp (-FR_TL26 * t) *
                                                (exp (-FR_TL27 * t) *
                                                 (1 − exp (-FR_TL28 * t))))))) +
                                            (exp (-FR_TL22 * t) *
                                             ((1 − exp (-FR_TL23 * t)) *
                                              (exp (-FR_TL24 * t) *
                                               (exp (-FR_TL25 * t) *
                                                (exp (-FR_TL26 * t) *
                                                 (1 − exp (-FR_TL27 * t)))))) +
                                             (exp (-FR_TL22 * t) *
                                              ((1 − exp (-FR_TL23 * t)) *
                                               (exp (-FR_TL24 * t) *
                                                (exp (-FR_TL25 * t) *
                                                 (1 − exp (-FR_TL26 * t))))) +
                                              (exp (-FR_TL22 * t) *
                                               ((1 − exp (-FR_TL23 * t)) *
                                                (exp (-FR_TL24 * t) *
                                                 (1 − exp (-FR_TL25 * t)))) +
                                               (exp (-FR_TL22 * t) *
                                                ((1 − exp (-FR_TL23 * t)) *
                                                 (1 − exp (-FR_TL24 * t))) +
                                                ((1 − exp (-FR_TL22 * t)) *
                                                 (exp (-FR_TL23 * t) *
                                                  (exp (-FR_TL24 * t) *
                                                   (exp (-FR_TL25 * t) *
                                                    (exp (-FR_TL26 * t) *
                                                     (exp (-FR_TL27 * t) *
                                                      (exp (-FR_TL28 * t) *
                                                       (exp (-FR_TL29 * t) *
                                                        (exp (-FR_TL30 * t) *
                                                         (exp (-FR_TL31 * t) *
                                                          (exp (-FR_TL32 * t) *
                                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                                 ((1 − exp (-FR_TL22 * t)) *
                                                  (exp (-FR_TL23 * t) *
                                                   (exp (-FR_TL24 * t) *
                                                    (exp (-FR_TL25 * t) *
                                                     (exp (-FR_TL26 * t) *
                                                      (exp (-FR_TL27 * t) *
                                                       (exp (-FR_TL28 * t) *
                                                        (exp (-FR_TL29 * t) *
                                                         (exp (-FR_TL30 * t) *
                                                          (exp (-FR_TL31 * t) *
                                                           (1 − exp (-FR_TL32 * t))))))))))) +
                                                  ((1 − exp (-FR_TL22 * t)) *
                                                   (exp (-FR_TL23 * t) *
                                                    (exp (-FR_TL24 * t) *
                                                     (exp (-FR_TL25 * t) *
                                                      (exp (-FR_TL26 * t) *
                                                       (exp (-FR_TL27 * t) *
                                                        (exp (-FR_TL28 * t) *
                                                         (exp (-FR_TL29 * t) *
                                                          (exp (-FR_TL30 * t) *
                                                           (1 − exp (-FR_TL31 * t)))))))))) +
                                                   ((1 − exp (-FR_TL22 * t)) *
                                                    (exp (-FR_TL23 * t) *
                                                     (exp (-FR_TL24 * t) *
                                                      (exp (-FR_TL25 * t) *
                                                       (exp (-FR_TL26 * t) *
                                                        (exp (-FR_TL27 * t) *
                                                         (exp (-FR_TL28 * t) *
                                                          (exp (-FR_TL29 * t) *
                                                           ((1 − exp (-FR_TL30 * t)) *
                                                            (exp (-FR_TL31 * t) *
                                                             (exp (-FR_TL32 * t) *
                                                              (1 − exp (-FR_TL33 * t)))))))))))) +
                                                    ((1 − exp (-FR_TL22 * t)) *
                                                     (exp (-FR_TL23 * t) *
                                                      (exp (-FR_TL24 * t) *
                                                       (exp (-FR_TL25 * t) *
                                                        (exp (-FR_TL26 * t) *
                                                         (exp (-FR_TL27 * t) *
                                                          (exp (-FR_TL28 * t) *
                                                           (exp  (-FR_TL29 * t) *
                                                            ((1 − exp (-FR_TL30 * t)) *
                                                             (exp (-FR_TL31 * t) *
                                                              (1 −  exp (-FR_TL32 * t))))))))))) +
                                                     ((1 − exp (-FR_TL22 * t)) *
                                                      (exp (-FR_TL23 * t) *
                                                       (exp (-FR_TL24 * t) *
                                                        (exp (-FR_TL25 * t) *
                                                         (exp (-FR_TL26 * t) *
                                                          (exp (-FR_TL27 * t) *
                                                           (exp (-FR_TL28 * t) *
                                                            (exp (-FR_TL29 * t) *
                                                             ((1 −  exp (-FR_TL30 * t)) *
                                                              (1 − exp (-FR_TL31 * t)))))))))) +
                                                      ((1 − exp (-FR_TL22 * t)) *
                                                       (exp (-FR_TL23 * t) *
                                                        (exp (-FR_TL24 * t) *
                                                         (exp (-FR_TL25 * t) *
                                                          (exp (-FR_TL26 * t) *
                                                           (exp (-FR_TL27 * t) *
                                                            (exp  (-FR_TL28 * t) *
                                                             ((1 − exp (-FR_TL29 * t)) *
                                                              (exp (-FR_TL30 * t) *
                                                               (exp (-FR_TL31 * t) *
                                                                (exp (-FR_TL32 * t) *
                                                                 (1 − exp (-FR_TL33 * t)))))))))))) +
                                                       ((1 − exp (-FR_TL22 * t)) *
                                                        (exp (-FR_TL23 * t) *
                                                         (exp (-FR_TL24 * t) *
                                                          (exp (-FR_TL25 * t) *
                                                           (exp (-FR_TL26 * t) *
                                                            (exp  (-FR_TL27 * t) *
                                                             (exp (-FR_TL28 * t) *
                                                              ((1 −  exp (-FR_TL29 * t)) *
                                                               (exp (-FR_TL30 * t) *
                                                                (exp (-FR_TL31 * t) *
                                                                 ((1 − exp (-FR_TL32 * t)) *
                                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                                        ((1 − exp (-FR_TL22 * t)) *
                                                         (exp (-FR_TL23 * t) *
                                                          (exp (-FR_TL24 * t) *
                                                           (exp (-FR_TL25 * t) *
                                                            (exp (-FR_TL26 * t) *
                                                             (exp (-FR_TL27 * t) *
                                                              (exp (-FR_TL28 * t) *
                                                               ((1 − exp (-FR_TL29 * t)) *
                                                                (exp (-FR_TL30 * t) *
                                                                 (1 − exp (-FR_TL31 * t)))))))))) +
                                                         ((1 − exp (-FR_TL22 * t)) *
                                                          (exp (-FR_TL23 * t) *
                                                           (exp (-FR_TL24 * t) *
                                                            (exp (-FR_TL25 * t) *
                                                             (exp (-FR_TL26 * t) *
                                                              (exp (-FR_TL27 * t) *
                                                               (exp (-FR_TL28 * t) *
                                                                ((1 − exp (-FR_TL29 * t)) *
                                                                 (1 −  exp (-FR_TL30 * t))))))))) +
                                                          ((1 − exp (-FR_TL22 * t)) *
                                                           (exp (-FR_TL23 * t) *
                                                            (exp (-FR_TL24 * t) *
                                                             (exp (-FR_TL25 * t) *
                                                              (exp (-FR_TL26 * t) *
                                                               (exp (-FR_TL27 * t) *
                                                                (1 − exp (-FR_TL28 * t))))))) +
                                                           ((1 − exp (-FR_TL22 * t)) *
                                                            (exp (-FR_TL23 * t) *
                                                             (exp (-FR_TL24 * t) *
                                                              (exp (-FR_TL25 * t) *
                                                               (exp (-FR_TL26 * t) *
                                                                (1 −  exp (-FR_TL27 * t)))))) +
                                                            ((1 − exp (-FR_TL22 * t)) *
                                                             (exp (-FR_TL23 * t) *
                                                              (exp (-FR_TL24 * t) *
                                                               (exp (-FR_TL25 * t) *
                                                                (1 − exp (-FR_TL26 * t))))) +
                                                             ((1 − exp (-FR_TL22 * t)) *
                                                              (exp (-FR_TL23 * t) *
                                                               (exp  (-FR_TL24 * t) *
                                                                (1 −exp (-FR_TL25 * t)))) +
                                                              ((1 − exp (-FR_TL22 * t)) *
                                                               (exp (-FR_TL23 * t) *
                                                                (1 −  exp (-FR_TL24 * t))) +
                                                               (1 − exp (-FR_TL22 * t)) *
                                                               (1 − exp (-FR_TL23 * t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * MTTR_C * CN_C) /
((exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           (exp (-FR_TL5 * t) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) *
               ((1 − exp (-FR_TL9 * t)) *
                (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            (exp (-FR_TL5 * t) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               (exp (-FR_TL8 * t) *
                ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t)))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             (exp (-FR_TL5 * t) *
              (exp (-FR_TL6 * t) *
               (exp (-FR_TL7 * t) *
                ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              (exp (-FR_TL5 * t) *
               (exp (-FR_TL6 * t) *
                ((1 − exp (-FR_TL7 * t)) *
                 ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               (exp (-FR_TL5 * t) *
                (exp (-FR_TL6 * t) *
                 ((1 − exp (-FR_TL7 * t)) *
                  ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                (exp (-FR_TL5 * t) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 (exp (-FR_TL5 * t) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  (exp (-FR_TL5 * t) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   (exp (-FR_TL5 * t) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    (exp (-FR_TL5 * t) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    (exp (-FR_TL4 * t) *
                     ((1 − exp (-FR_TL5 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) * exp (-FR_TL9 * t)))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     (exp (-FR_TL4 * t) *
                      ((1 − exp (-FR_TL5 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         ((1 − exp (-FR_TL8 * t)) * exp (-FR_TL9 * t)))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) *
                         (exp (-FR_TL8 * t) * exp (-FR_TL9 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) *
                         (exp (-FR_TL7 * t) *
                          (exp (-FR_TL8 * t) *
                           ((1 − exp (-FR_TL9 * t)) *
                            (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             ((1 − exp (-FR_TL9 * t)) *
                              (exp (-FR_TL10 * t) * exp (-FR_TL11 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         ((1 − exp (-FR_TL3 * t)) *
                          (exp (-FR_TL4 * t) *
                           (exp (-FR_TL5 * t) *
                            (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          ((1 − exp (-FR_TL3 * t)) *
                           (exp (-FR_TL4 * t) *
                            (exp (-FR_TL5 * t) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          ((1 − exp (-FR_TL2 * t)) *
                           (exp (-FR_TL3 * t) *
                            (exp (-FR_TL4 * t) *
                             (exp (-FR_TL5 * t) *
                              (exp (-FR_TL8 * t) *
                               (exp (-FR_TL9 * t) * (1 − exp (-FR_TL11 * t)))))))) +
                          (exp (-FR_TL1 * t) *
                           ((1 − exp (-FR_TL2 * t)) *
                            (exp (-FR_TL3 * t) *
                             (exp (-FR_TL4 * t) *
                              (exp (-FR_TL5 * t) *
                               (exp (-FR_TL8 * t) *
                                ((1 − exp (-FR_TL9 * t)) *
                                 (exp (-FR_TL10 * t) *
                                  (1 − exp (-FR_TL11 * t))))))))) +
                           (exp (-FR_TL1 * t) *
                            ((1 − exp (-FR_TL2 * t)) *
                             (exp (-FR_TL3 * t) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL8 * t) *
                                 ((1 − exp (-FR_TL9 * t)) *
                                  ((1 − exp (-FR_TL10 * t)) *
                                   (1 − exp (-FR_TL11 * t))))))))) +
                            (exp (-FR_TL1 * t) *
                             ((1 − exp (-FR_TL2 * t)) *
                              (exp (-FR_TL3 * t) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL8 * t)) *
                                  (exp (-FR_TL9 * t) *
                                   (exp (-FR_TL10 * t) *
                                    (1 − exp (-FR_TL11 * t))))))))) +
                             ((1 − exp (-FR_TL1 * t)) *
                              (exp (-FR_TL2 * t) *
                               (exp (-FR_TL3 * t) *
                                (exp (-FR_TL6 * t) *
                                 (exp (-FR_TL7 * t) *
                                  (exp (-FR_TL8 * t) *
                                   (exp (-FR_TL9 * t) *
                                    (exp (-FR_TL10 * t) *
                                     (1 − exp (-FR_TL11 * t))))))))) +
                              ((1 − exp (-FR_TL1 * t)) *
                               (exp (-FR_TL2 * t) *
                                (exp (-FR_TL3 * t) *
                                 (exp (-FR_TL6 * t) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL8 * t) *
                                    ((1 − exp (-FR_TL9 * t)) *
                                     (exp (-FR_TL10 * t) *
                                      (1 − exp (-FR_TL11 * t))))))))) +
                               ((1 − exp (-FR_TL1 * t)) *
                                (exp (-FR_TL2 * t) *
                                 (exp (-FR_TL3 * t) *
                                  (exp (-FR_TL6 * t) *
                                   (exp (-FR_TL7 * t) *
                                    ((1 − exp (-FR_TL8 * t)) *
                                     (exp (-FR_TL9 * t) *
                                      (exp (-FR_TL10 * t) *
                                       (1 − exp (-FR_TL11 * t))))))))) +
                                ((1 − exp (-FR_TL1 * t)) *
                                 (exp (-FR_TL2 * t) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL6 * t) *
                                    (exp (-FR_TL7 * t) *
                                     ((1 − exp (-FR_TL8 * t)) *
                                      ((1 − exp (-FR_TL9 * t)) *
                                       (exp (-FR_TL10 * t) *
                                        (1 − exp (-FR_TL11 * t))))))))) +
                                 ((1 − exp (-FR_TL1 * t)) *
                                  (exp (-FR_TL2 * t) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL6 * t) *
                                     ((1 − exp (-FR_TL7 * t)) *
                                      (exp (-FR_TL8 * t) *
                                       (exp (-FR_TL9 * t) *
                                        (exp (-FR_TL10 * t) *
                                         (1 − exp (-FR_TL11 * t))))))))) +
                                  ((1 − exp (-FR_TL1 * t)) *
                                   (exp (-FR_TL2 * t) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL6 * t) *
                                      ((1 − exp (-FR_TL7 * t)) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         (exp (-FR_TL10 * t) *
                                          exp (-FR_TL11 * t)))))))) +
                                   ((1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL6 * t) *
                                       ((1 − exp (-FR_TL7 * t)) *
                                        (exp (-FR_TL8 * t) *
                                         ((1 − exp (-FR_TL9 * t)) *
                                          (1 − exp (-FR_TL10 * t)))))))) +
                                    (1 − exp (-FR_TL1 * t)) *
                                    (exp (-FR_TL2 * t) *
                                     (exp (-FR_TL3 * t) *
                                      ((1 − exp (-FR_TL6 * t)) *
                                       (exp (-FR_TL7 * t) *
                                        (exp (-FR_TL8 * t) *
                                         (exp (-FR_TL9 * t) *
                                          (1 − exp (-FR_TL10 * t))))))))))))))))))))))))))))))))))))) * 0.15 * CN_A +
        (exp (-FR_TL1 * t) *
        (exp (-FR_TL2 * t) *
         (exp (-FR_TL3 * t) *
          (exp (-FR_TL4 * t) *
           ((1 − exp (-FR_TL5 * t)) *
            (exp (-FR_TL6 * t) *
             (exp (-FR_TL7 * t) *
              (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
        (exp (-FR_TL1 * t) *
         (exp (-FR_TL2 * t) *
          (exp (-FR_TL3 * t) *
           (exp (-FR_TL4 * t) *
            ((1 − exp (-FR_TL5 * t)) *
             (exp (-FR_TL6 * t) *
              (exp (-FR_TL7 * t) *
               ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
         (exp (-FR_TL1 * t) *
          (exp (-FR_TL2 * t) *
           (exp (-FR_TL3 * t) *
            (exp (-FR_TL4 * t) *
             ((1 − exp (-FR_TL5 * t)) *
              (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t))))))) +
          (exp (-FR_TL1 * t) *
           (exp (-FR_TL2 * t) *
            (exp (-FR_TL3 * t) *
             (exp (-FR_TL4 * t) *
              ((1 − exp (-FR_TL5 * t)) *
               ((1 − exp (-FR_TL6 * t)) *
                (exp (-FR_TL7 * t) *
                 (exp (-FR_TL8 * t) *
                  (exp (-FR_TL9 * t) *
                   (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
           (exp (-FR_TL1 * t) *
            (exp (-FR_TL2 * t) *
             (exp (-FR_TL3 * t) *
              (exp (-FR_TL4 * t) *
               ((1 − exp (-FR_TL5 * t)) *
                ((1 − exp (-FR_TL6 * t)) *
                 (exp (-FR_TL7 * t) *
                  (exp (-FR_TL8 * t) *
                   (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
            (exp (-FR_TL1 * t) *
             (exp (-FR_TL2 * t) *
              (exp (-FR_TL3 * t) *
               (exp (-FR_TL4 * t) *
                ((1 − exp (-FR_TL5 * t)) *
                 ((1 − exp (-FR_TL6 * t)) *
                  (exp (-FR_TL7 * t) *
                   (exp (-FR_TL8 * t) * (1 − exp (-FR_TL9 * t))))))))) +
             (exp (-FR_TL1 * t) *
              (exp (-FR_TL2 * t) *
               (exp (-FR_TL3 * t) *
                (exp (-FR_TL4 * t) *
                 ((1 − exp (-FR_TL5 * t)) *
                  ((1 − exp (-FR_TL6 * t)) *
                   (exp (-FR_TL7 * t) *
                    ((1 − exp (-FR_TL8 * t)) *
                     (exp (-FR_TL9 * t) *
                      (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t))))))))))) +
              (exp (-FR_TL1 * t) *
               (exp (-FR_TL2 * t) *
                (exp (-FR_TL3 * t) *
                 (exp (-FR_TL4 * t) *
                  ((1 − exp (-FR_TL5 * t)) *
                   ((1 − exp (-FR_TL6 * t)) *
                    (exp (-FR_TL7 * t) *
                     ((1 − exp (-FR_TL8 * t)) *
                      (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t)))))))))) +
               (exp (-FR_TL1 * t) *
                (exp (-FR_TL2 * t) *
                 (exp (-FR_TL3 * t) *
                  (exp (-FR_TL4 * t) *
                   ((1 − exp (-FR_TL5 * t)) *
                    ((1 − exp (-FR_TL6 * t)) *
                     (exp (-FR_TL7 * t) *
                      ((1 − exp (-FR_TL8 * t)) * (1 − exp (-FR_TL9 * t))))))))) +
                (exp (-FR_TL1 * t) *
                 (exp (-FR_TL2 * t) *
                  (exp (-FR_TL3 * t) *
                   (exp (-FR_TL4 * t) *
                    ((1 − exp (-FR_TL5 * t)) *
                     ((1 − exp (-FR_TL6 * t)) * (1 − exp (-FR_TL7 * t))))))) +
                 (exp (-FR_TL1 * t) *
                  (exp (-FR_TL2 * t) *
                   (exp (-FR_TL3 * t) *
                    ((1 − exp (-FR_TL4 * t)) *
                     (exp (-FR_TL6 * t) *
                      (exp (-FR_TL7 * t) *
                       (exp (-FR_TL8 * t) *
                        ((1 − exp (-FR_TL9 * t)) *
                         (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                  (exp (-FR_TL1 * t) *
                   (exp (-FR_TL2 * t) *
                    (exp (-FR_TL3 * t) *
                     ((1 − exp (-FR_TL4 * t)) *
                      (exp (-FR_TL6 * t) *
                       (exp (-FR_TL7 * t) *
                        (exp (-FR_TL8 * t) *
                         ((1 − exp (-FR_TL9 * t)) * (1 − exp (-FR_TL10 * t))))))))) +
                   (exp (-FR_TL1 * t) *
                    (exp (-FR_TL2 * t) *
                     (exp (-FR_TL3 * t) *
                      ((1 − exp (-FR_TL4 * t)) *
                       (exp (-FR_TL6 * t) *
                        (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                    (exp (-FR_TL1 * t) *
                     (exp (-FR_TL2 * t) *
                      (exp (-FR_TL3 * t) *
                       ((1 − exp (-FR_TL4 * t)) *
                        (exp (-FR_TL6 * t) * (1 − exp (-FR_TL7 * t)))))) +
                     (exp (-FR_TL1 * t) *
                      (exp (-FR_TL2 * t) *
                       (exp (-FR_TL3 * t) *
                        ((1 − exp (-FR_TL4 * t)) *
                         ((1 − exp (-FR_TL6 * t)) *
                          (exp (-FR_TL7 * t) *
                           (exp (-FR_TL8 * t) *
                            (exp (-FR_TL9 * t) *
                             (exp (-FR_TL10 * t) * (1 − exp (-FR_TL11 * t)))))))))) +
                      (exp (-FR_TL1 * t) *
                       (exp (-FR_TL2 * t) *
                        (exp (-FR_TL3 * t) *
                         ((1 − exp (-FR_TL4 * t)) *
                          ((1 − exp (-FR_TL6 * t)) *
                           (exp (-FR_TL7 * t) *
                            (exp (-FR_TL8 * t) *
                             (exp (-FR_TL9 * t) * (1 − exp (-FR_TL10 * t))))))))) +
                       (exp (-FR_TL1 * t) *
                        (exp (-FR_TL2 * t) *
                         (exp (-FR_TL3 * t) *
                          ((1 − exp (-FR_TL4 * t)) *
                           ((1 − exp (-FR_TL6 * t)) *
                            (exp (-FR_TL7 * t) *
                             (exp (-FR_TL8 * t) *
                              ((1 − exp (-FR_TL9 * t)) *
                               (exp (-FR_TL10 * t) *
                                (1 − exp (-FR_TL11 * t)))))))))) +
                        (exp (-FR_TL1 * t) *
                         (exp (-FR_TL2 * t) *
                          (exp (-FR_TL3 * t) *
                           ((1 − exp (-FR_TL4 * t)) *
                            ((1 − exp (-FR_TL6 * t)) *
                             (exp (-FR_TL7 * t) *
                              (exp (-FR_TL8 * t) *
                               ((1 − exp (-FR_TL9 * t)) *
                                (1 − exp (-FR_TL10 * t))))))))) +
                         (exp (-FR_TL1 * t) *
                          (exp (-FR_TL2 * t) *
                           (exp (-FR_TL3 * t) *
                            ((1 − exp (-FR_TL4 * t)) *
                             ((1 − exp (-FR_TL6 * t)) *
                              (exp (-FR_TL7 * t) * (1 − exp (-FR_TL8 * t))))))) +
                          (exp (-FR_TL1 * t) *
                           (exp (-FR_TL2 * t) *
                            (exp (-FR_TL3 * t) *
                             ((1 − exp (-FR_TL4 * t)) *
                              ((1 − exp (-FR_TL6 * t)) *
                               (1 − exp (-FR_TL7 * t)))))) +
                           (exp (-FR_TL1 * t) *
                            (exp (-FR_TL2 * t) *
                             ((1 − exp (-FR_TL3 * t)) *
                              (exp (-FR_TL4 * t) *
                               (exp (-FR_TL5 * t) *
                                (exp (-FR_TL6 * t) * exp (-FR_TL7 * t)))))) +
                            (exp (-FR_TL1 * t) *
                             (exp (-FR_TL2 * t) *
                              ((1 − exp (-FR_TL3 * t)) *
                               (exp (-FR_TL4 * t) *
                                (exp (-FR_TL5 * t) *
                                 ((1 − exp (-FR_TL6 * t)) *
                                  (exp (-FR_TL7 * t) *
                                   (exp (-FR_TL10 * t) * exp (-FR_TL11 * t)))))))) +
                             (exp (-FR_TL1 * t) *
                              (exp (-FR_TL2 * t) *
                               ((1 − exp (-FR_TL3 * t)) *
                                (exp (-FR_TL4 * t) *
                                 (exp (-FR_TL5 * t) *
                                  ((1 − exp (-FR_TL6 * t)) *
                                   (exp (-FR_TL7 * t) *
                                    (1 − exp (-FR_TL10 * t)))))))) +
                              (exp (-FR_TL1 * t) *
                               (exp (-FR_TL2 * t) *
                                ((1 − exp (-FR_TL3 * t)) *
                                 (exp (-FR_TL4 * t) *
                                  (exp (-FR_TL5 * t) *
                                   ((1 − exp (-FR_TL6 * t)) *
                                    (1 − exp (-FR_TL7 * t))))))) +
                               (exp (-FR_TL1 * t) *
                                (exp (-FR_TL2 * t) *
                                 ((1 − exp (-FR_TL3 * t)) *
                                  (exp (-FR_TL4 * t) *
                                   (1 − exp (-FR_TL5 * t))))) +
                                (exp (-FR_TL1 * t) *
                                 ((1 − exp (-FR_TL2 * t)) *
                                  (exp (-FR_TL3 * t) *
                                   (exp (-FR_TL4 * t) *
                                    (exp (-FR_TL5 * t) *
                                     (exp (-FR_TL8 * t) *
                                      (exp (-FR_TL9 * t) *
                                       exp (-FR_TL11 * t))))))) +
                                 (exp (-FR_TL1 * t) *
                                  ((1 − exp (-FR_TL2 * t)) *
                                   (exp (-FR_TL3 * t) *
                                    (exp (-FR_TL4 * t) *
                                     (exp (-FR_TL5 * t) *
                                      (exp (-FR_TL8 * t) *
                                       ((1 − exp (-FR_TL9 * t)) *
                                        (exp (-FR_TL10 * t) *
                                         exp (-FR_TL11 * t)))))))) +
                                  (exp (-FR_TL1 * t) *
                                   ((1 − exp (-FR_TL2 * t)) *
                                    (exp (-FR_TL3 * t) *
                                     (exp (-FR_TL4 * t) *
                                      (exp (-FR_TL5 * t) *
                                       (exp (-FR_TL8 * t) *
                                        ((1 − exp (-FR_TL9 * t)) *
                                         ((1 − exp (-FR_TL10 * t)) *
                                          exp (-FR_TL11 * t)))))))) +
                                   (exp (-FR_TL1 * t) *
                                    ((1 − exp (-FR_TL2 * t)) *
                                     (exp (-FR_TL3 * t) *
                                      (exp (-FR_TL4 * t) *
                                       (exp (-FR_TL5 * t) *
                                        ((1 − exp (-FR_TL8 * t)) *
                                         (exp (-FR_TL9 * t) *
                                          (exp (-FR_TL10 * t) *
                                           exp (-FR_TL11 * t)))))))) +
                                    (exp (-FR_TL1 * t) *
                                     ((1 − exp (-FR_TL2 * t)) *
                                      (exp (-FR_TL3 * t) *
                                       (exp (-FR_TL4 * t) *
                                        (exp (-FR_TL5 * t) *
                                         ((1 − exp (-FR_TL8 * t)) *
                                          (exp (-FR_TL9 * t) *
                                           (1 − exp (-FR_TL10 * t)))))))) +
                                     (exp (-FR_TL1 * t) *
                                      ((1 − exp (-FR_TL2 * t)) *
                                       (exp (-FR_TL3 * t) *
                                        (exp (-FR_TL4 * t) *
                                         (exp (-FR_TL5 * t) *
                                          ((1 − exp (-FR_TL8 * t)) *
                                           (1 − exp (-FR_TL9 * t))))))) +
                                      (exp (-FR_TL1 * t) *
                                       ((1 − exp (-FR_TL2 * t)) *
                                        (exp (-FR_TL3 * t) *
                                         (exp (-FR_TL4 * t) *
                                          (1 − exp (-FR_TL5 * t))))) +
                                       (exp (-FR_TL1 * t) *
                                        ((1 − exp (-FR_TL2 * t)) *
                                         (exp (-FR_TL3 * t) *
                                          (1 − exp (-FR_TL4 * t)))) +
                                        (exp (-FR_TL1 * t) *
                                         ((1 − exp (-FR_TL2 * t)) *
                                          (1 − exp (-FR_TL3 * t))) +
                                         ((1 − exp (-FR_TL1 * t)) *
                                          (exp (-FR_TL2 * t) *
                                           (exp (-FR_TL3 * t) *
                                            (exp (-FR_TL6 * t) *
                                             (exp (-FR_TL7 * t) *
                                              (exp (-FR_TL8 * t) *
                                               (exp (-FR_TL9 * t) *
                                                (exp (-FR_TL10 * t) *
                                                 exp (-FR_TL11 * t)))))))) +
                                          ((1 − exp (-FR_TL1 * t)) *
                                           (exp (-FR_TL2 * t) *
                                            (exp (-FR_TL3 * t) *
                                             (exp (-FR_TL6 * t) *
                                              (exp (-FR_TL7 * t) *
                                               (exp (-FR_TL8 * t) *
                                                (exp (-FR_TL9 * t) *
                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                           ((1 − exp (-FR_TL1 * t)) *
                                            (exp (-FR_TL2 * t) *
                                             (exp (-FR_TL3 * t) *
                                              (exp (-FR_TL6 * t) *
                                               (exp (-FR_TL7 * t) *
                                                (exp (-FR_TL8 * t) *
                                                 ((1 − exp (-FR_TL9 * t)) *
                                                  (exp (-FR_TL10 * t) *
                                                   exp (-FR_TL11 * t)))))))) +
                                            ((1 − exp (-FR_TL1 * t)) *
                                             (exp (-FR_TL2 * t) *
                                              (exp (-FR_TL3 * t) *
                                               (exp (-FR_TL6 * t) *
                                                (exp (-FR_TL7 * t) *
                                                 (exp (-FR_TL8 * t) *
                                                  ((1 − exp (-FR_TL9 * t)) *
                                                   (1 − exp (-FR_TL10 * t)))))))) +
                                             ((1 − exp (-FR_TL1 * t)) *
                                              (exp (-FR_TL2 * t) *
                                               (exp (-FR_TL3 * t) *
                                                (exp (-FR_TL6 * t) *
                                                 (exp (-FR_TL7 * t) *
                                                  ((1 − exp (-FR_TL8 * t)) *
                                                   (exp (-FR_TL9 * t) *
                                                    (exp (-FR_TL10 * t) *
                                                     exp (-FR_TL11 * t)))))))) +
                                              ((1 − exp (-FR_TL1 * t)) *
                                               (exp (-FR_TL2 * t) *
                                                (exp (-FR_TL3 * t) *
                                                 (exp (-FR_TL6 * t) *
                                                  (exp (-FR_TL7 * t) *
                                                   ((1 − exp (-FR_TL8 * t)) *
                                                    (exp (-FR_TL9 * t) *
                                                     (1 − exp (-FR_TL10 * t)))))))) +
                                               ((1 − exp (-FR_TL1 * t)) *
                                                (exp (-FR_TL2 * t) *
                                                 (exp (-FR_TL3 * t) *
                                                  (exp (-FR_TL6 * t) *
                                                   (exp (-FR_TL7 * t) *
                                                    ((1 − exp (-FR_TL8 * t)) *
                                                     ((1 − exp (-FR_TL9 * t)) *
                                                      (exp (-FR_TL10 * t) *
                                                       exp (-FR_TL11 * t)))))))) +
                                                ((1 − exp (-FR_TL1 * t)) *
                                                 (exp (-FR_TL2 * t) *
                                                  (exp (-FR_TL3 * t) *
                                                   (exp (-FR_TL6 * t) *
                                                    (exp (-FR_TL7 * t) *
                                                     ((1 − exp (-FR_TL8 * t)) *
                                                      ((1 − exp (-FR_TL9 * t)) *
                                                       (1 −
                                                        exp (-FR_TL10 * t)))))))) +
                                                 ((1 − exp (-FR_TL1 * t)) *
                                                  (exp (-FR_TL2 * t) *
                                                   (exp (-FR_TL3 * t) *
                                                    (exp (-FR_TL6 * t) *
                                                     ((1 − exp (-FR_TL7 * t)) *
                                                      (exp (-FR_TL8 * t) *
                                                       (exp (-FR_TL9 * t) *
                                                        (exp (-FR_TL10 * t) *
                                                         exp (-FR_TL11 * t)))))))) +
                                                  ((1 − exp (-FR_TL1 * t)) *
                                                   (exp (-FR_TL2 * t) *
                                                    (exp (-FR_TL3 * t) *
                                                     (exp (-FR_TL6 * t) *
                                                      ((1 − exp (-FR_TL7 * t)) *
                                                       (exp (-FR_TL8 * t) *
                                                        (exp (-FR_TL9 * t) *
                                                         (1 −  exp (-FR_TL10 * t)))))))) +
                                                   ((1 − exp (-FR_TL1 * t)) *
                                                    (exp (-FR_TL2 * t) *
                                                     (exp (-FR_TL3 * t) *
                                                      (exp (-FR_TL6 * t) *
                                                       ((1 − exp (-FR_TL7 * t)) *
                                                        (exp (-FR_TL8 * t) *
                                                         ((1 − exp (-FR_TL9 * t)) *
                                                          (exp (-FR_TL10 * t) *
                                                           (1 − exp (-FR_TL11 * t))))))))) +
                                                    ((1 − exp (-FR_TL1 * t)) *
                                                     (exp (-FR_TL2 * t) *
                                                      (exp (-FR_TL3 * t) *
                                                       (exp (-FR_TL6 * t) *
                                                        ((1 − exp (-FR_TL7 * t)) *
                                                         (1 − exp (-FR_TL8 * t)))))) +
                                                     ((1 − exp (-FR_TL1 * t)) *
                                                      (exp (-FR_TL2 * t) *
                                                       (exp (-FR_TL3 * t) *
                                                        ((1 − exp (-FR_TL6 * t)) *
                                                         (exp (-FR_TL7 * t) *
                                                          (exp (-FR_TL8 * t) *
                                                           (exp (-FR_TL9 * t) *
                                                            (exp (-FR_TL10 * t) *
                                                             exp (-FR_TL11 * t)))))))) +
                                                      ((1 − exp (-FR_TL1 * t)) *
                                                       (exp (-FR_TL2 * t) *
                                                        (exp (-FR_TL3 * t) *
                                                         ((1 − exp (-FR_TL6 * t)) *
                                                          (exp (-FR_TL7 * t) *
                                                           (exp (-FR_TL8 * t) *
                                                            (exp(-FR_TL9 * t) *
                                                             (exp (-FR_TL10 * t) *
                                                              (1 − exp (-FR_TL11 * t))))))))) +
                                                       ((1 − exp (-FR_TL1 * t)) *
                                                        (exp (-FR_TL2 * t) *
                                                         (exp (-FR_TL3 * t) *
                                                          ((1 − exp (-FR_TL6 * t)) *
                                                           (exp (-FR_TL7 * t) *
                                                            (exp (-FR_TL8 * t) *
                                                             (1 − exp (-FR_TL9 * t))))))) +
                                                        ((1 −  exp (-FR_TL1 * t)) *
                                                         (exp (-FR_TL2 * t) *
                                                          (exp (-FR_TL3 * t) *
                                                           ((1 − exp (-FR_TL6 * t)) *
                                                            (exp (-FR_TL7 * t) *
                                                             ((1 − exp (-FR_TL8 * t)) *
                                                              (exp (-FR_TL9 * t) *
                                                               (exp (-FR_TL10 * t) *
                                                                exp (-FR_TL11 * t)))))))) +
                                                         ((1 − exp (-FR_TL1 * t)) *
                                                          (exp (-FR_TL2 * t) *
                                                           (exp (-FR_TL3 * t) *
                                                            ((1 − exp (-FR_TL6 * t)) *
                                                             (exp (-FR_TL7 * t) *
                                                              ((1 − exp (-FR_TL8 * t)) *
                                                               (exp (-FR_TL9 * t) *
                                                                (exp (-FR_TL10 * t) *
                                                                 (1 −  exp (-FR_TL11 * t))))))))) +
                                                          ((1 − exp (-FR_TL1 * t)) *
                                                           (exp (-FR_TL2 * t) *
                                                            (exp (-FR_TL3 * t) *
                                                             ((1 − exp (-FR_TL6 * t)) *
                                                              (exp (-FR_TL7 * t) *
                                                               ((1 − exp (-FR_TL8 * t)) *
                                                                (exp (-FR_TL9 * t) *
                                                                 (1 − exp (-FR_TL10 * t)))))))) +
                                                           ((1 − exp  (-FR_TL1 * t)) *
                                                            (exp (-FR_TL2 * t) *
                                                             (exp (-FR_TL3 * t) *
                                                              ((1 − exp (-FR_TL6 * t)) *
                                                               (exp (-FR_TL7 * t) *
                                                                ((1 − exp (-FR_TL8 * t)) *
                                                                 (1 − exp (-FR_TL9 * t))))))) +
                                                            ((1 − exp (-FR_TL1 * t)) *
                                                             (exp (-FR_TL2 * t) *
                                                              (exp (-FR_TL3 * t) *
                                                               ((1 − exp (-FR_TL6 * t)) *
                                                                (1 − exp  (-FR_TL7 * t))))) +
                                                             ((1 − exp (-FR_TL1 * t)) *
                                                              (exp (-FR_TL2 * t) *
                                                               (1 −  exp  (-FR_TL3 * t))) +
                                                              (1 − exp (-FR_TL1 * t)) *
                                                              (1 − exp (-FR_TL2 * t))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * CN_A +
	(exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              (exp (-FR_TL21 * t) *
               ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) *
                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             ((1 − exp (-FR_TL18 * t)) *
              (exp (-FR_TL19 * t) *
               (exp (-FR_TL20 * t) *
                (exp (-FR_TL21 * t) *
                 (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              ((1 − exp (-FR_TL18 * t)) *
               (exp (-FR_TL19 * t) *
                (exp (-FR_TL20 * t) *
                 (exp (-FR_TL21 * t) *
                  (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  (exp (-FR_TL21 * t) *
                   ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   (exp (-FR_TL21 * t) *
                    ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t)))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    ((1 − exp (-FR_TL21 * t)) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 ((1 − exp (-FR_TL15 * t)) *
                  (exp (-FR_TL19 * t) *
                   (exp (-FR_TL20 * t) *
                    (exp (-FR_TL21 * t) *
                     (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     (exp (-FR_TL21 * t) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      (exp (-FR_TL21 * t) *
                       ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) *
                      (exp (-FR_TL20 * t) *
                       (exp (-FR_TL21 * t) *
                        ((1 − exp (-FR_TL16 * t)) * (1 − exp (-FR_TL17 * t))))))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) *
                      (exp (-FR_TL19 * t) *
                       (exp (-FR_TL20 * t) *
                        ((1 − exp (-FR_TL21 * t)) *
                         (exp (-FR_TL16 * t) * exp (-FR_TL17 * t)))))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          (exp (-FR_TL21 * t) *
                           (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           (exp (-FR_TL21 * t) *
                            (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) *
                           (exp (-FR_TL20 * t) *
                            (exp (-FR_TL21 * t) *
                             ((1 − exp (-FR_TL16 * t)) * exp (-FR_TL17 * t))))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) *
                           (exp (-FR_TL19 * t) *
                            (exp (-FR_TL20 * t) *
                             (exp (-FR_TL21 * t) *
                              ((1 − exp (-FR_TL16 * t)) *
                               (1 − exp (-FR_TL17 * t)))))))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) *
                           (exp (-FR_TL18 * t) *
                            (exp (-FR_TL19 * t) *
                             (exp (-FR_TL20 * t) *
                              ((1 − exp (-FR_TL21 * t)) *
                               (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                        (exp (-FR_L12 * t) *
                         ((1 − exp (-FR_TL13 * t)) *
                          (exp (-FR_TL14 * t) *
                           (exp (-FR_TL15 * t) *
                            (exp (-FR_TL18 * t) *
                             (exp (-FR_TL19 * t) *
                              (exp (-FR_TL20 * t) *
                               (exp (-FR_TL21 * t) *
                                (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (exp (-FR_TL21 * t) *
                                 (exp (-FR_TL16 * t) *
                                  (1 − exp (-FR_TL17 * t)))))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (exp (-FR_TL20 * t) *
                                 (exp (-FR_TL21 * t) *
                                  (exp (-FR_TL16 * t) *
                                   (1 − exp (-FR_TL17 * t)))))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (exp (-FR_TL19 * t) *
                                 (exp (-FR_TL20 * t) *
                                  (exp (-FR_TL21 * t) *
                                   (exp (-FR_TL16 * t) *
                                    (1 − exp (-FR_TL17 * t)))))))))) +
                            ((1 − exp (-FR_L12 * t)) *
                             (exp (-FR_TL13 * t) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (exp (-FR_TL18 * t) *
                                 (exp (-FR_TL19 * t) *
                                  (exp (-FR_TL20 * t) *
                                   (exp (-FR_TL21 * t) *
                                    (exp (-FR_TL16 * t) * exp (-FR_TL17 * t))))))))) +
                             ((1 − exp (-FR_L12 * t)) *
                              (exp (-FR_TL13 * t) *
                               (exp (-FR_TL14 * t) *
                                (exp (-FR_TL15 * t) *
                                 (exp (-FR_TL18 * t) *
                                  (exp (-FR_TL19 * t) *
                                   (exp (-FR_TL20 * t) *
                                    (exp (-FR_TL21 * t) *
                                     (exp (-FR_TL16 * t) *
                                      (1 − exp (-FR_TL17 * t)))))))))) +
                              ((1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       exp (-FR_TL17 * t))))))))) +
                               (1 − exp (-FR_L12 * t)) *
                               (exp (-FR_TL13 * t) *
                                (exp (-FR_TL14 * t) *
                                 (exp (-FR_TL15 * t) *
                                  (exp (-FR_TL18 * t) *
                                   (exp (-FR_TL19 * t) *
                                    (exp (-FR_TL20 * t) *
                                     (exp (-FR_TL21 * t) *
                                      ((1 − exp (-FR_TL16 * t)) *
                                       (1 − exp (-FR_TL17 * t)))))))))))))))))))))))))))))))))) * 0.15 * CN_B +
        (exp (-FR_L12 * t) *
        (exp (-FR_TL13 * t) *
         (exp (-FR_TL14 * t) *
          (exp (-FR_TL15 * t) *
           (exp (-FR_TL18 * t) *
            (exp (-FR_TL19 * t) *
             (exp (-FR_TL20 * t) *
              ((1 − exp (-FR_TL21 * t)) *
               (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
        (exp (-FR_L12 * t) *
         (exp (-FR_TL13 * t) *
          (exp (-FR_TL14 * t) *
           (exp (-FR_TL15 * t) *
            (exp (-FR_TL18 * t) *
             (exp (-FR_TL19 * t) *
              (exp (-FR_TL20 * t) *
               ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
         (exp (-FR_L12 * t) *
          (exp (-FR_TL13 * t) *
           (exp (-FR_TL14 * t) *
            (exp (-FR_TL15 * t) *
             (exp (-FR_TL18 * t) *
              (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
          (exp (-FR_L12 * t) *
           (exp (-FR_TL13 * t) *
            (exp (-FR_TL14 * t) *
             (exp (-FR_TL15 * t) *
              (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
           (exp (-FR_L12 * t) *
            (exp (-FR_TL13 * t) *
             (exp (-FR_TL14 * t) *
              (exp (-FR_TL15 * t) *
               ((1 − exp (-FR_TL18 * t)) *
                (exp (-FR_TL19 * t) *
                 (exp (-FR_TL20 * t) *
                  ((1 − exp (-FR_TL21 * t)) *
                   (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
            (exp (-FR_L12 * t) *
             (exp (-FR_TL13 * t) *
              (exp (-FR_TL14 * t) *
               (exp (-FR_TL15 * t) *
                ((1 − exp (-FR_TL18 * t)) *
                 (exp (-FR_TL19 * t) *
                  (exp (-FR_TL20 * t) *
                   ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t))))))))) +
             (exp (-FR_L12 * t) *
              (exp (-FR_TL13 * t) *
               (exp (-FR_TL14 * t) *
                (exp (-FR_TL15 * t) *
                 ((1 − exp (-FR_TL18 * t)) *
                  (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
              (exp (-FR_L12 * t) *
               (exp (-FR_TL13 * t) *
                (exp (-FR_TL14 * t) *
                 (exp (-FR_TL15 * t) *
                  ((1 − exp (-FR_TL18 * t)) * (1 − exp (-FR_TL19 * t)))))) +
               (exp (-FR_L12 * t) *
                (exp (-FR_TL13 * t) *
                 (exp (-FR_TL14 * t) *
                  ((1 − exp (-FR_TL15 * t)) *
                   (exp (-FR_TL19 * t) *
                    (exp (-FR_TL20 * t) *
                     ((1 − exp (-FR_TL21 * t)) *
                      (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t))))))))) +
                (exp (-FR_L12 * t) *
                 (exp (-FR_TL13 * t) *
                  (exp (-FR_TL14 * t) *
                   ((1 − exp (-FR_TL15 * t)) *
                    (exp (-FR_TL19 * t) *
                     (exp (-FR_TL20 * t) *
                      ((1 − exp (-FR_TL21 * t)) * (1 − exp (-FR_TL16 * t)))))))) +
                 (exp (-FR_L12 * t) *
                  (exp (-FR_TL13 * t) *
                   (exp (-FR_TL14 * t) *
                    ((1 − exp (-FR_TL15 * t)) *
                     (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t)))))) +
                  (exp (-FR_L12 * t) *
                   (exp (-FR_TL13 * t) *
                    (exp (-FR_TL14 * t) *
                     ((1 − exp (-FR_TL15 * t)) * (1 − exp (-FR_TL19 * t))))) +
                   (exp (-FR_L12 * t) *
                    (exp (-FR_TL13 * t) *
                     ((1 − exp (-FR_TL14 * t)) *
                      (exp (-FR_TL15 * t) *
                       (exp (-FR_TL18 * t) *
                        (exp (-FR_TL19 * t) *
                         (exp (-FR_TL20 * t) *
                          ((1 − exp (-FR_TL21 * t)) *
                           (exp (-FR_TL16 * t) * (1 − exp (-FR_TL17 * t)))))))))) +
                    (exp (-FR_L12 * t) *
                     (exp (-FR_TL13 * t) *
                      ((1 − exp (-FR_TL14 * t)) *
                       (exp (-FR_TL15 * t) *
                        (exp (-FR_TL18 * t) *
                         (exp (-FR_TL19 * t) *
                          (exp (-FR_TL20 * t) *
                           ((1 − exp (-FR_TL21 * t)) *
                            (1 − exp (-FR_TL16 * t))))))))) +
                     (exp (-FR_L12 * t) *
                      (exp (-FR_TL13 * t) *
                       ((1 − exp (-FR_TL14 * t)) *
                        (exp (-FR_TL15 * t) *
                         (exp (-FR_TL18 * t) *
                          (exp (-FR_TL19 * t) * (1 − exp (-FR_TL20 * t))))))) +
                      (exp (-FR_L12 * t) *
                       (exp (-FR_TL13 * t) *
                        ((1 − exp (-FR_TL14 * t)) *
                         (exp (-FR_TL15 * t) *
                          (exp (-FR_TL18 * t) * (1 − exp (-FR_TL19 * t)))))) +
                       (exp (-FR_L12 * t) *
                        (exp (-FR_TL13 * t) *
                         ((1 − exp (-FR_TL14 * t)) *
                          (exp (-FR_TL15 * t) * (1 − exp (-FR_TL18 * t))))) +
                        (exp (-FR_L12 * t) *
                         (exp (-FR_TL13 * t) *
                          ((1 − exp (-FR_TL14 * t)) *
                           (1 − exp (-FR_TL15 * t)))) +
                         (exp (-FR_L12 * t) *
                          ((1 − exp (-FR_TL13 * t)) *
                           (exp (-FR_TL14 * t) *
                            (exp (-FR_TL15 * t) *
                             (exp (-FR_TL18 * t) *
                              (exp (-FR_TL19 * t) *
                               (exp (-FR_TL20 * t) *
                                (1 − exp (-FR_TL21 * t)))))))) +
                          (exp (-FR_L12 * t) *
                           ((1 − exp (-FR_TL13 * t)) *
                            (exp (-FR_TL14 * t) *
                             (exp (-FR_TL15 * t) *
                              (exp (-FR_TL18 * t) *
                               (exp (-FR_TL19 * t) *
                                (1 − exp (-FR_TL20 * t))))))) +
                           (exp (-FR_L12 * t) *
                            ((1 − exp (-FR_TL13 * t)) *
                             (exp (-FR_TL14 * t) *
                              (exp (-FR_TL15 * t) *
                               (exp (-FR_TL18 * t) *
                                (1 − exp (-FR_TL19 * t)))))) +
                            (exp (-FR_L12 * t) *
                             ((1 − exp (-FR_TL13 * t)) *
                              (exp (-FR_TL14 * t) *
                               (exp (-FR_TL15 * t) *
                                (1 − exp (-FR_TL18 * t))))) +
                             (exp (-FR_L12 * t) *
                              ((1 − exp (-FR_TL13 * t)) *
                               (exp (-FR_TL14 * t) *
                                (1 − exp (-FR_TL15 * t)))) +
                              (exp (-FR_L12 * t) *
                               ((1 − exp (-FR_TL13 * t)) *
                                (1 − exp (-FR_TL14 * t))) +
                               ((1 − exp (-FR_L12 * t)) *
                                (exp (-FR_TL13 * t) *
                                 (exp (-FR_TL14 * t) *
                                  (exp (-FR_TL15 * t) *
                                   (exp (-FR_TL18 * t) *
                                    (exp (-FR_TL19 * t) *
                                     (exp (-FR_TL20 * t) *
                                      (1 − exp (-FR_TL21 * t)))))))) +
                                ((1 − exp (-FR_L12 * t)) *
                                 (exp (-FR_TL13 * t) *
                                  (exp (-FR_TL14 * t) *
                                   (exp (-FR_TL15 * t) *
                                    (exp (-FR_TL18 * t) *
                                     (exp (-FR_TL19 * t) *
                                      (1 − exp (-FR_TL20 * t))))))) +
                                 ((1 − exp (-FR_L12 * t)) *
                                  (exp (-FR_TL13 * t) *
                                   (exp (-FR_TL14 * t) *
                                    (exp (-FR_TL15 * t) *
                                     (exp (-FR_TL18 * t) *
                                      (1 − exp (-FR_TL19 * t)))))) +
                                  ((1 − exp (-FR_L12 * t)) *
                                   (exp (-FR_TL13 * t) *
                                    (exp (-FR_TL14 * t) *
                                     (exp (-FR_TL15 * t) *
                                      (1 − exp (-FR_TL18 * t))))) +
                                   ((1 − exp (-FR_L12 * t)) *
                                    (exp (-FR_TL13 * t) *
                                     (exp (-FR_TL14 * t) *
                                      (1 − exp (-FR_TL15 * t)))) +
                                    ((1 − exp (-FR_L12 * t)) *
                                     (exp (-FR_TL13 * t) *
                                      (1 − exp (-FR_TL14 * t))) +
                                     (1 − exp (-FR_L12 * t)) *
                                     (1 − exp (-FR_TL13 * t)))))))))))))))))))))))))))))))) * CN_B +
	( exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             (exp (-FR_TL28 * t) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              (exp (-FR_TL28 * t) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               (exp (-FR_TL28 * t) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                (exp (-FR_TL28 * t) *
                 (exp (-FR_TL29 * t) *
                  ((1 − exp (-FR_TL30 * t)) *
                   (exp (-FR_TL31 * t) *
                    (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 (exp (-FR_TL28 * t) *
                  (exp (-FR_TL29 * t) *
                   ((1 − exp (-FR_TL30 * t)) *
                    (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 (exp (-FR_TL27 * t) *
                  (exp (-FR_TL28 * t) *
                   (exp (-FR_TL29 * t) *
                    ((1 − exp (-FR_TL30 * t)) * (1 − exp (-FR_TL31 * t)))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  (exp (-FR_TL27 * t) *
                   (exp (-FR_TL28 * t) *
                    ((1 − exp (-FR_TL29 * t)) *
                     (exp (-FR_TL30 * t) *
                      (exp (-FR_TL31 * t) *
                       (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   (exp (-FR_TL27 * t) *
                    (exp (-FR_TL28 * t) *
                     ((1 − exp (-FR_TL29 * t)) *
                      (exp (-FR_TL30 * t) *
                       (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    (exp (-FR_TL27 * t) *
                     (exp (-FR_TL28 * t) *
                      ((1 − exp (-FR_TL29 * t)) *
                       (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     (exp (-FR_TL27 * t) *
                      (exp (-FR_TL28 * t) *
                       ((1 − exp (-FR_TL29 * t)) * (1 − exp (-FR_TL30 * t))))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     (exp (-FR_TL26 * t) *
                      (exp (-FR_TL27 * t) *
                       ((1 − exp (-FR_TL28 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      (exp (-FR_TL26 * t) *
                       ((1 − exp (-FR_TL27 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t)))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) *
                          (exp (-FR_TL31 * t) *
                           (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      ((1 − exp (-FR_TL24 * t)) *
                       (exp (-FR_TL25 * t) *
                        (exp (-FR_TL26 * t) *
                         (exp (-FR_TL27 * t) *
                          (exp (-FR_TL28 * t) *
                           (exp (-FR_TL29 * t) *
                            (exp (-FR_TL30 * t) *
                             (exp (-FR_TL31 * t) *
                              (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       ((1 − exp (-FR_TL24 * t)) * (1 − exp (-FR_TL25 * t)))) +
                      (exp (-FR_TL22 * t) *
                       ((1 − exp (-FR_TL23 * t)) *
                        (exp (-FR_TL24 * t) *
                         (exp (-FR_TL25 * t) *
                          (exp (-FR_TL26 * t) *
                           (exp (-FR_TL27 * t) *
                            (exp (-FR_TL28 * t) *
                             (exp (-FR_TL29 * t) *
                              (exp (-FR_TL30 * t) *
                               (exp (-FR_TL31 * t) *
                                (1 − exp (-FR_TL32 * t))))))))))) +
                       (exp (-FR_TL22 * t) *
                        ((1 − exp (-FR_TL23 * t)) *
                         (exp (-FR_TL24 * t) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               ((1 − exp (-FR_TL30 * t)) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                        (exp (-FR_TL22 * t) *
                         ((1 − exp (-FR_TL23 * t)) *
                          (exp (-FR_TL24 * t) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               ((1 − exp (-FR_TL29 * t)) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                         ((1 − exp (-FR_TL22 * t)) *
                          (exp (-FR_TL23 * t) *
                           (exp (-FR_TL24 * t) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (exp (-FR_TL31 * t) *
                                   (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                          ((1 − exp (-FR_TL22 * t)) *
                           (exp (-FR_TL23 * t) *
                            (exp (-FR_TL24 * t) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  ((1 − exp (-FR_TL30 * t)) *
                                   (exp (-FR_TL31 * t) *
                                    (exp (-FR_TL32 * t) * exp (-FR_TL33 * t))))))))))) +
                           ((1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     (exp (-FR_TL32 * t) *
                                      exp (-FR_TL33 * t))))))))))) +
                            (1 − exp (-FR_TL22 * t)) *
                            (exp (-FR_TL23 * t) *
                             (exp (-FR_TL24 * t) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  ((1 − exp (-FR_TL29 * t)) *
                                   (exp (-FR_TL30 * t) *
                                    (exp (-FR_TL31 * t) *
                                     ((1 − exp (-FR_TL32 * t)) *
                                      exp (-FR_TL33 * t))))))))))))))))))))))))))))))))  * 0.15 * CN_C +
        (exp (-FR_TL22 * t) *
        (exp (-FR_TL23 * t) *
         (exp (-FR_TL24 * t) *
          (exp (-FR_TL25 * t) *
           (exp (-FR_TL26 * t) *
            (exp (-FR_TL27 * t) *
             ((1 − exp (-FR_TL28 * t)) *
              (exp (-FR_TL29 * t) *
               (exp (-FR_TL30 * t) *
                (exp (-FR_TL31 * t) *
                 (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))))) +
        (exp (-FR_TL22 * t) *
         (exp (-FR_TL23 * t) *
          (exp (-FR_TL24 * t) *
           (exp (-FR_TL25 * t) *
            (exp (-FR_TL26 * t) *
             (exp (-FR_TL27 * t) *
              ((1 − exp (-FR_TL28 * t)) *
               (exp (-FR_TL29 * t) *
                (exp (-FR_TL30 * t) *
                 (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))))) +
         (exp (-FR_TL22 * t) *
          (exp (-FR_TL23 * t) *
           (exp (-FR_TL24 * t) *
            (exp (-FR_TL25 * t) *
             (exp (-FR_TL26 * t) *
              (exp (-FR_TL27 * t) *
               ((1 − exp (-FR_TL28 * t)) *
                (exp (-FR_TL29 * t) *
                 (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))))) +
          (exp (-FR_TL22 * t) *
           (exp (-FR_TL23 * t) *
            (exp (-FR_TL24 * t) *
             (exp (-FR_TL25 * t) *
              (exp (-FR_TL26 * t) *
               (exp (-FR_TL27 * t) *
                ((1 − exp (-FR_TL28 * t)) *
                 (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))))) +
           (exp (-FR_TL22 * t) *
            (exp (-FR_TL23 * t) *
             (exp (-FR_TL24 * t) *
              (exp (-FR_TL25 * t) *
               (exp (-FR_TL26 * t) *
                (exp (-FR_TL27 * t) *
                 ((1 − exp (-FR_TL28 * t)) * (1 − exp (-FR_TL29 * t)))))))) +
            (exp (-FR_TL22 * t) *
             (exp (-FR_TL23 * t) *
              (exp (-FR_TL24 * t) *
               (exp (-FR_TL25 * t) *
                (exp (-FR_TL26 * t) *
                 ((1 − exp (-FR_TL27 * t)) *
                  (exp (-FR_TL29 * t) *
                   (exp (-FR_TL30 * t) *
                    (exp (-FR_TL31 * t) *
                     (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t))))))))))) +
             (exp (-FR_TL22 * t) *
              (exp (-FR_TL23 * t) *
               (exp (-FR_TL24 * t) *
                (exp (-FR_TL25 * t) *
                 (exp (-FR_TL26 * t) *
                  ((1 − exp (-FR_TL27 * t)) *
                   (exp (-FR_TL29 * t) *
                    (exp (-FR_TL30 * t) *
                     (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t)))))))))) +
              (exp (-FR_TL22 * t) *
               (exp (-FR_TL23 * t) *
                (exp (-FR_TL24 * t) *
                 (exp (-FR_TL25 * t) *
                  (exp (-FR_TL26 * t) *
                   ((1 − exp (-FR_TL27 * t)) *
                    (exp (-FR_TL29 * t) *
                     (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t))))))))) +
               (exp (-FR_TL22 * t) *
                (exp (-FR_TL23 * t) *
                 (exp (-FR_TL24 * t) *
                  (exp (-FR_TL25 * t) *
                   (exp (-FR_TL26 * t) *
                    ((1 − exp (-FR_TL27 * t)) *
                     (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t)))))))) +
                (exp (-FR_TL22 * t) *
                 (exp (-FR_TL23 * t) *
                  (exp (-FR_TL24 * t) *
                   (exp (-FR_TL25 * t) *
                    (exp (-FR_TL26 * t) *
                     ((1 − exp (-FR_TL27 * t)) * (1 − exp (-FR_TL29 * t))))))) +
                 (exp (-FR_TL22 * t) *
                  (exp (-FR_TL23 * t) *
                   (exp (-FR_TL24 * t) *
                    (exp (-FR_TL25 * t) *
                     ((1 − exp (-FR_TL26 * t)) *
                      (exp (-FR_TL29 * t) *
                       (exp (-FR_TL30 * t) *
                        (exp (-FR_TL31 * t) *
                         (exp (-FR_TL32 * t) * (1 − exp (-FR_TL33 * t)))))))))) +
                  (exp (-FR_TL22 * t) *
                   (exp (-FR_TL23 * t) *
                    (exp (-FR_TL24 * t) *
                     (exp (-FR_TL25 * t) *
                      ((1 − exp (-FR_TL26 * t)) *
                       (exp (-FR_TL29 * t) *
                        (exp (-FR_TL30 * t) *
                         (exp (-FR_TL31 * t) * (1 − exp (-FR_TL32 * t))))))))) +
                   (exp (-FR_TL22 * t) *
                    (exp (-FR_TL23 * t) *
                     (exp (-FR_TL24 * t) *
                      (exp (-FR_TL25 * t) *
                       ((1 − exp (-FR_TL26 * t)) *
                        (exp (-FR_TL29 * t) *
                         (exp (-FR_TL30 * t) * (1 − exp (-FR_TL31 * t)))))))) +
                    (exp (-FR_TL22 * t) *
                     (exp (-FR_TL23 * t) *
                      (exp (-FR_TL24 * t) *
                       (exp (-FR_TL25 * t) *
                        ((1 − exp (-FR_TL26 * t)) *
                         (exp (-FR_TL29 * t) * (1 − exp (-FR_TL30 * t))))))) +
                     (exp (-FR_TL22 * t) *
                      (exp (-FR_TL23 * t) *
                       (exp (-FR_TL24 * t) *
                        (exp (-FR_TL25 * t) *
                         ((1 − exp (-FR_TL26 * t)) *
                          (1 − exp (-FR_TL29 * t)))))) +
                      (exp (-FR_TL22 * t) *
                       (exp (-FR_TL23 * t) *
                        (exp (-FR_TL24 * t) * (1 − exp (-FR_TL25 * t)))) +
                       (exp (-FR_TL22 * t) *
                        (exp (-FR_TL23 * t) *
                         ((1 − exp (-FR_TL24 * t)) *
                          (exp (-FR_TL25 * t) *
                           (exp (-FR_TL26 * t) *
                            (exp (-FR_TL27 * t) *
                             (exp (-FR_TL28 * t) *
                              (exp (-FR_TL29 * t) *
                               (exp (-FR_TL30 * t) *
                                (exp (-FR_TL31 * t) *
                                 (exp (-FR_TL32 * t) *
                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                        (exp (-FR_TL22 * t) *
                         (exp (-FR_TL23 * t) *
                          ((1 − exp (-FR_TL24 * t)) *
                           (exp (-FR_TL25 * t) *
                            (exp (-FR_TL26 * t) *
                             (exp (-FR_TL27 * t) *
                              (exp (-FR_TL28 * t) *
                               (exp (-FR_TL29 * t) *
                                (exp (-FR_TL30 * t) *
                                 (exp (-FR_TL31 * t) *
                                  (1 − exp (-FR_TL32 * t))))))))))) +
                         (exp (-FR_TL22 * t) *
                          (exp (-FR_TL23 * t) *
                           ((1 − exp (-FR_TL24 * t)) *
                            (exp (-FR_TL25 * t) *
                             (exp (-FR_TL26 * t) *
                              (exp (-FR_TL27 * t) *
                               (exp (-FR_TL28 * t) *
                                (exp (-FR_TL29 * t) *
                                 (exp (-FR_TL30 * t) *
                                  (1 − exp (-FR_TL31 * t)))))))))) +
                          (exp (-FR_TL22 * t) *
                           (exp (-FR_TL23 * t) *
                            ((1 − exp (-FR_TL24 * t)) *
                             (exp (-FR_TL25 * t) *
                              (exp (-FR_TL26 * t) *
                               (exp (-FR_TL27 * t) *
                                (exp (-FR_TL28 * t) *
                                 (exp (-FR_TL29 * t) *
                                  (1 − exp (-FR_TL30 * t))))))))) +
                           (exp (-FR_TL22 * t) *
                            (exp (-FR_TL23 * t) *
                             ((1 − exp (-FR_TL24 * t)) *
                              (exp (-FR_TL25 * t) *
                               (exp (-FR_TL26 * t) *
                                (exp (-FR_TL27 * t) *
                                 (exp (-FR_TL28 * t) *
                                  (1 − exp (-FR_TL29 * t)))))))) +
                            (exp (-FR_TL22 * t) *
                             (exp (-FR_TL23 * t) *
                              ((1 − exp (-FR_TL24 * t)) *
                               (exp (-FR_TL25 * t) *
                                (exp (-FR_TL26 * t) *
                                 (exp (-FR_TL27 * t) *
                                  (1 − exp (-FR_TL28 * t))))))) +
                             (exp (-FR_TL22 * t) *
                              (exp (-FR_TL23 * t) *
                               ((1 − exp (-FR_TL24 * t)) *
                                (exp (-FR_TL25 * t) *
                                 (exp (-FR_TL26 * t) *
                                  (1 − exp (-FR_TL27 * t)))))) +
                              (exp (-FR_TL22 * t) *
                               (exp (-FR_TL23 * t) *
                                ((1 − exp (-FR_TL24 * t)) *
                                 (exp (-FR_TL25 * t) *
                                  (1 − exp (-FR_TL26 * t))))) +
                               (exp (-FR_TL22 * t) *
                                ((1 − exp (-FR_TL23 * t)) *
                                 (exp (-FR_TL24 * t) *
                                  (exp (-FR_TL25 * t) *
                                   (exp (-FR_TL26 * t) *
                                    (exp (-FR_TL27 * t) *
                                     (exp (-FR_TL28 * t) *
                                      (exp (-FR_TL29 * t) *
                                       (exp (-FR_TL30 * t) *
                                        (exp (-FR_TL31 * t) *
                                         (exp (-FR_TL32 * t) *
                                          exp (-FR_TL33 * t))))))))))) +
                                (exp (-FR_TL22 * t) *
                                 ((1 − exp (-FR_TL23 * t)) *
                                  (exp (-FR_TL24 * t) *
                                   (exp (-FR_TL25 * t) *
                                    (exp (-FR_TL26 * t) *
                                     (exp (-FR_TL27 * t) *
                                      (exp (-FR_TL28 * t) *
                                       (exp (-FR_TL29 * t) *
                                        (exp (-FR_TL30 * t) *
                                         (exp (-FR_TL31 * t) *
                                          (exp (-FR_TL32 * t) *
                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                 (exp (-FR_TL22 * t) *
                                  ((1 − exp (-FR_TL23 * t)) *
                                   (exp (-FR_TL24 * t) *
                                    (exp (-FR_TL25 * t) *
                                     (exp (-FR_TL26 * t) *
                                      (exp (-FR_TL27 * t) *
                                       (exp (-FR_TL28 * t) *
                                        (exp (-FR_TL29 * t) *
                                         (exp (-FR_TL30 * t) *
                                          ((1 − exp (-FR_TL31 * t)) *
                                           (exp (-FR_TL32 * t) *
                                            exp (-FR_TL33 * t))))))))))) +
                                  (exp (-FR_TL22 * t) *
                                   ((1 − exp (-FR_TL23 * t)) *
                                    (exp (-FR_TL24 * t) *
                                     (exp (-FR_TL25 * t) *
                                      (exp (-FR_TL26 * t) *
                                       (exp (-FR_TL27 * t) *
                                        (exp (-FR_TL28 * t) *
                                         (exp (-FR_TL29 * t) *
                                          (exp (-FR_TL30 * t) *
                                           ((1 − exp (-FR_TL31 * t)) *
                                            (exp (-FR_TL32 * t) *
                                             (1 − exp (-FR_TL33 * t)))))))))))) +
                                   (exp (-FR_TL22 * t) *
                                    ((1 − exp (-FR_TL23 * t)) *
                                     (exp (-FR_TL24 * t) *
                                      (exp (-FR_TL25 * t) *
                                       (exp (-FR_TL26 * t) *
                                        (exp (-FR_TL27 * t) *
                                         (exp (-FR_TL28 * t) *
                                          (exp (-FR_TL29 * t) *
                                           (exp (-FR_TL30 * t) *
                                            ((1 − exp (-FR_TL31 * t)) *
                                             (1 − exp (-FR_TL32 * t))))))))))) +
                                    (exp (-FR_TL22 * t) *
                                     ((1 − exp (-FR_TL23 * t)) *
                                      (exp (-FR_TL24 * t) *
                                       (exp (-FR_TL25 * t) *
                                        (exp (-FR_TL26 * t) *
                                         (exp (-FR_TL27 * t) *
                                          (exp (-FR_TL28 * t) *
                                           (exp (-FR_TL29 * t) *
                                            ((1 − exp (-FR_TL30 * t)) *
                                             (exp (-FR_TL31 * t) *
                                              (exp (-FR_TL32 * t) *
                                               (1 − exp (-FR_TL33 * t)))))))))))) +
                                     (exp (-FR_TL22 * t) *
                                      ((1 − exp (-FR_TL23 * t)) *
                                       (exp (-FR_TL24 * t) *
                                        (exp (-FR_TL25 * t) *
                                         (exp (-FR_TL26 * t) *
                                          (exp (-FR_TL27 * t) *
                                           (exp (-FR_TL28 * t) *
                                            (exp (-FR_TL29 * t) *
                                             ((1 − exp (-FR_TL30 * t)) *
                                              (exp (-FR_TL31 * t) *
                                               (1 − exp (-FR_TL32 * t))))))))))) +
                                      (exp (-FR_TL22 * t) *
                                       ((1 − exp (-FR_TL23 * t)) *
                                        (exp (-FR_TL24 * t) *
                                         (exp (-FR_TL25 * t) *
                                          (exp (-FR_TL26 * t) *
                                           (exp (-FR_TL27 * t) *
                                            (exp (-FR_TL28 * t) *
                                             (exp (-FR_TL29 * t) *
                                              ((1 − exp (-FR_TL30 * t)) *
                                               ((1 − exp (-FR_TL31 * t)) *
                                                (1 − exp (-FR_TL32 * t))))))))))) +
                                       (exp (-FR_TL22 * t) *
                                        ((1 − exp (-FR_TL23 * t)) *
                                         (exp (-FR_TL24 * t) *
                                          (exp (-FR_TL25 * t) *
                                           (exp (-FR_TL26 * t) *
                                            (exp (-FR_TL27 * t) *
                                             (exp (-FR_TL28 * t) *
                                              ((1 − exp (-FR_TL29 * t)) *
                                               (exp (-FR_TL30 * t) *
                                                (exp (-FR_TL31 * t) *
                                                 (exp (-FR_TL32 * t) *
                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                        (exp (-FR_TL22 * t) *
                                         ((1 − exp (-FR_TL23 * t)) *
                                          (exp (-FR_TL24 * t) *
                                           (exp (-FR_TL25 * t) *
                                            (exp (-FR_TL26 * t) *
                                             (exp (-FR_TL27 * t) *
                                              (exp (-FR_TL28 * t) *
                                               ((1 − exp (-FR_TL29 * t)) *
                                                (exp (-FR_TL30 * t) *
                                                 (exp (-FR_TL31 * t) *
                                                  (1 − exp (-FR_TL32 * t))))))))))) +
                                         (exp (-FR_TL22 * t) *
                                          ((1 − exp (-FR_TL23 * t)) *
                                           (exp (-FR_TL24 * t) *
                                            (exp (-FR_TL25 * t) *
                                             (exp (-FR_TL26 * t) *
                                              (exp (-FR_TL27 * t) *
                                               (exp (-FR_TL28 * t) *
                                                ((1 − exp (-FR_TL29 * t)) *
                                                 (exp (-FR_TL30 * t) *
                                                  (1 − exp (-FR_TL31 * t)))))))))) +
                                          (exp (-FR_TL22 * t) *
                                           ((1 − exp (-FR_TL23 * t)) *
                                            (exp (-FR_TL24 * t) *
                                             (exp (-FR_TL25 * t) *
                                              (exp (-FR_TL26 * t) *
                                               (exp (-FR_TL27 * t) *
                                                (exp (-FR_TL28 * t) *
                                                 ((1 − exp (-FR_TL29 * t)) *
                                                  (1 − exp (-FR_TL30 * t))))))))) +
                                           (exp (-FR_TL22 * t) *
                                            ((1 − exp (-FR_TL23 * t)) *
                                             (exp (-FR_TL24 * t) *
                                              (exp (-FR_TL25 * t) *
                                               (exp (-FR_TL26 * t) *
                                                (exp (-FR_TL27 * t) *
                                                 (1 − exp (-FR_TL28 * t))))))) +
                                            (exp (-FR_TL22 * t) *
                                             ((1 − exp (-FR_TL23 * t)) *
                                              (exp (-FR_TL24 * t) *
                                               (exp (-FR_TL25 * t) *
                                                (exp (-FR_TL26 * t) *
                                                 (1 − exp (-FR_TL27 * t)))))) +
                                             (exp (-FR_TL22 * t) *
                                              ((1 − exp (-FR_TL23 * t)) *
                                               (exp (-FR_TL24 * t) *
                                                (exp (-FR_TL25 * t) *
                                                 (1 − exp (-FR_TL26 * t))))) +
                                              (exp (-FR_TL22 * t) *
                                               ((1 − exp (-FR_TL23 * t)) *
                                                (exp (-FR_TL24 * t) *
                                                 (1 − exp (-FR_TL25 * t)))) +
                                               (exp (-FR_TL22 * t) *
                                                ((1 − exp (-FR_TL23 * t)) *
                                                 (1 − exp (-FR_TL24 * t))) +
                                                ((1 − exp (-FR_TL22 * t)) *
                                                 (exp (-FR_TL23 * t) *
                                                  (exp (-FR_TL24 * t) *
                                                   (exp (-FR_TL25 * t) *
                                                    (exp (-FR_TL26 * t) *
                                                     (exp (-FR_TL27 * t) *
                                                      (exp (-FR_TL28 * t) *
                                                       (exp (-FR_TL29 * t) *
                                                        (exp (-FR_TL30 * t) *
                                                         (exp (-FR_TL31 * t) *
                                                          (exp (-FR_TL32 * t) *
                                                           (1 − exp (-FR_TL33 * t)))))))))))) +
                                                 ((1 − exp (-FR_TL22 * t)) *
                                                  (exp (-FR_TL23 * t) *
                                                   (exp (-FR_TL24 * t) *
                                                    (exp (-FR_TL25 * t) *
                                                     (exp (-FR_TL26 * t) *
                                                      (exp (-FR_TL27 * t) *
                                                       (exp (-FR_TL28 * t) *
                                                        (exp (-FR_TL29 * t) *
                                                         (exp (-FR_TL30 * t) *
                                                          (exp (-FR_TL31 * t) *
                                                           (1 − exp (-FR_TL32 * t))))))))))) +
                                                  ((1 − exp (-FR_TL22 * t)) *
                                                   (exp (-FR_TL23 * t) *
                                                    (exp (-FR_TL24 * t) *
                                                     (exp (-FR_TL25 * t) *
                                                      (exp (-FR_TL26 * t) *
                                                       (exp (-FR_TL27 * t) *
                                                        (exp (-FR_TL28 * t) *
                                                         (exp (-FR_TL29 * t) *
                                                          (exp (-FR_TL30 * t) *
                                                           (1 − exp (-FR_TL31 * t)))))))))) +
                                                   ((1 − exp (-FR_TL22 * t)) *
                                                    (exp (-FR_TL23 * t) *
                                                     (exp (-FR_TL24 * t) *
                                                      (exp (-FR_TL25 * t) *
                                                       (exp (-FR_TL26 * t) *
                                                        (exp (-FR_TL27 * t) *
                                                         (exp (-FR_TL28 * t) *
                                                          (exp (-FR_TL29 * t) *
                                                           ((1 − exp (-FR_TL30 * t)) *
                                                            (exp (-FR_TL31 * t) *
                                                             (exp (-FR_TL32 * t) *
                                                              (1 − exp (-FR_TL33 * t)))))))))))) +
                                                    ((1 − exp (-FR_TL22 * t)) *
                                                     (exp (-FR_TL23 * t) *
                                                      (exp (-FR_TL24 * t) *
                                                       (exp (-FR_TL25 * t) *
                                                        (exp (-FR_TL26 * t) *
                                                         (exp (-FR_TL27 * t) *
                                                          (exp (-FR_TL28 * t) *
                                                           (exp  (-FR_TL29 * t) *
                                                            ((1 − exp (-FR_TL30 * t)) *
                                                             (exp (-FR_TL31 * t) *
                                                              (1 −  exp (-FR_TL32 * t))))))))))) +
                                                     ((1 − exp (-FR_TL22 * t)) *
                                                      (exp (-FR_TL23 * t) *
                                                       (exp (-FR_TL24 * t) *
                                                        (exp (-FR_TL25 * t) *
                                                         (exp (-FR_TL26 * t) *
                                                          (exp (-FR_TL27 * t) *
                                                           (exp (-FR_TL28 * t) *
                                                            (exp (-FR_TL29 * t) *
                                                             ((1 −  exp (-FR_TL30 * t)) *
                                                              (1 − exp (-FR_TL31 * t)))))))))) +
                                                      ((1 − exp (-FR_TL22 * t)) *
                                                       (exp (-FR_TL23 * t) *
                                                        (exp (-FR_TL24 * t) *
                                                         (exp (-FR_TL25 * t) *
                                                          (exp (-FR_TL26 * t) *
                                                           (exp (-FR_TL27 * t) *
                                                            (exp  (-FR_TL28 * t) *
                                                             ((1 − exp (-FR_TL29 * t)) *
                                                              (exp (-FR_TL30 * t) *
                                                               (exp (-FR_TL31 * t) *
                                                                (exp (-FR_TL32 * t) *
                                                                 (1 − exp (-FR_TL33 * t)))))))))))) +
                                                       ((1 − exp (-FR_TL22 * t)) *
                                                        (exp (-FR_TL23 * t) *
                                                         (exp (-FR_TL24 * t) *
                                                          (exp (-FR_TL25 * t) *
                                                           (exp (-FR_TL26 * t) *
                                                            (exp  (-FR_TL27 * t) *
                                                             (exp (-FR_TL28 * t) *
                                                              ((1 −  exp (-FR_TL29 * t)) *
                                                               (exp (-FR_TL30 * t) *
                                                                (exp (-FR_TL31 * t) *
                                                                 ((1 − exp (-FR_TL32 * t)) *
                                                                  (1 − exp (-FR_TL33 * t)))))))))))) +
                                                        ((1 − exp (-FR_TL22 * t)) *
                                                         (exp (-FR_TL23 * t) *
                                                          (exp (-FR_TL24 * t) *
                                                           (exp (-FR_TL25 * t) *
                                                            (exp (-FR_TL26 * t) *
                                                             (exp (-FR_TL27 * t) *
                                                              (exp (-FR_TL28 * t) *
                                                               ((1 − exp (-FR_TL29 * t)) *
                                                                (exp (-FR_TL30 * t) *
                                                                 (1 − exp (-FR_TL31 * t)))))))))) +
                                                         ((1 − exp (-FR_TL22 * t)) *
                                                          (exp (-FR_TL23 * t) *
                                                           (exp (-FR_TL24 * t) *
                                                            (exp (-FR_TL25 * t) *
                                                             (exp (-FR_TL26 * t) *
                                                              (exp (-FR_TL27 * t) *
                                                               (exp (-FR_TL28 * t) *
                                                                ((1 − exp (-FR_TL29 * t)) *
                                                                 (1 −  exp (-FR_TL30 * t))))))))) +
                                                          ((1 − exp (-FR_TL22 * t)) *
                                                           (exp (-FR_TL23 * t) *
                                                            (exp (-FR_TL24 * t) *
                                                             (exp (-FR_TL25 * t) *
                                                              (exp (-FR_TL26 * t) *
                                                               (exp (-FR_TL27 * t) *
                                                                (1 − exp (-FR_TL28 * t))))))) +
                                                           ((1 − exp (-FR_TL22 * t)) *
                                                            (exp (-FR_TL23 * t) *
                                                             (exp (-FR_TL24 * t) *
                                                              (exp (-FR_TL25 * t) *
                                                               (exp (-FR_TL26 * t) *
                                                                (1 −  exp (-FR_TL27 * t)))))) +
                                                            ((1 − exp (-FR_TL22 * t)) *
                                                             (exp (-FR_TL23 * t) *
                                                              (exp (-FR_TL24 * t) *
                                                               (exp (-FR_TL25 * t) *
                                                                (1 − exp (-FR_TL26 * t))))) +
                                                             ((1 − exp (-FR_TL22 * t)) *
                                                              (exp (-FR_TL23 * t) *
                                                               (exp  (-FR_TL24 * t) *
                                                                (1 −exp (-FR_TL25 * t)))) +
                                                              ((1 − exp (-FR_TL22 * t)) *
                                                               (exp (-FR_TL23 * t) *
                                                                (1 −  exp (-FR_TL24 * t))) +
                                                               (1 − exp (-FR_TL22 * t)) *
                                                               (1 − exp (-FR_TL23 * t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * CN_C)``

val _ = export_theory();
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
	(*------------------------------------------------------------------------------*)
		       (*--------------------------------------------------*)
			         (*--------------------------------*)
					  (*---------------*)
