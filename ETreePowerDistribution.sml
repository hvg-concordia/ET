(* ========================================================================= *)
(* File Name: ETreePowerDistribution.sml	                 	     *)
(*---------------------------------------------------------------------------*)
(*          Description: Formalization of Event Trees using                  *)
(*                       Higher-order Logic Theorem Proving                  *)
(*                                                                           *)
(*          HOL4-Kananaskis 13 		 			     	     *)
(*									     *)
(*	    Author : Mohamed Abdelghany             		     	     *)
(*                                              			     *)
(* 	    Department of Electrical and Computer Engineering (ECE)          *)
(*	    Concordia University                                             *)
(*          Montreal, Quebec, Canada, 2020                                   *)
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
     
val _ = new_theory "ETreePowerDistribution";
(*--------------------------------------------------------------------------------------------------*)
			    (*-------------------------------------*)  
			    (*            CASE STUDY               *)
			    (*-------------------------------------*)

(*-----------------------------------------*)  
(*   Lemma 1 Power grid All Paths Proof    *)
(*-----------------------------------------*)

val POWER_GRID = store_thm("POWER_GRID",
``!M1 M2 M3 L1 L2 t p.
ETREE (NODE
  (ETREE_N_STAIR (EVENT_TREE_LIST [SUCCESS p L2 t; FAIL p L2 t])
                                 [[SUCCESS p M1 t; FAIL p M1 t];
                                  [SUCCESS p M2 t; FAIL p M2 t];
		            	  [SUCCESS p M3 t; FAIL p M3 t];
				  [SUCCESS p L1 t; FAIL p L1 t];
		 	    	  [SUCCESS p L2 t; FAIL p L2 t]])) = 
 ETREE (NODE
[BRANCH (SUCCESS p M1 t) [BRANCH (SUCCESS p M2 t) [BRANCH (SUCCESS p M3 t)
[BRANCH (SUCCESS p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)]);
 BRANCH (FAIL p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)])];
 BRANCH (FAIL p M3 t)
[BRANCH (SUCCESS p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)]);
 BRANCH (FAIL p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)])]];
 BRANCH (FAIL p M2 t) [BRANCH (SUCCESS p M3 t)
[BRANCH (SUCCESS p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)]);
 BRANCH (FAIL p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)])];
 BRANCH (FAIL p M3 t)
[BRANCH (SUCCESS p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)]);
 BRANCH (FAIL p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)])]]];
 BRANCH (FAIL p M1 t) [BRANCH (SUCCESS p M2 t) [BRANCH (SUCCESS p M3 t)
[BRANCH (SUCCESS p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)]);
 BRANCH (FAIL p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)])];
 BRANCH (FAIL p M3 t)
[BRANCH (SUCCESS p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)]);
 BRANCH (FAIL p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)])]];
 BRANCH (FAIL p M2 t) [BRANCH (SUCCESS p M3 t)
[BRANCH (SUCCESS p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)]);
 BRANCH (FAIL p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)])];
 BRANCH (FAIL p M3 t)
[BRANCH (SUCCESS p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)]);
 BRANCH (FAIL p L1 t) (EVENT_TREE_LIST[(SUCCESS p L2 t);(FAIL p L2 t)])]]]])``,
rw [ETREE_N_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, ETREE_TWO_STAIR_DEF]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [UNION_ASSOC]
\\ rw [EXTENSION]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------*)  
(*    ETree Power Distribution Definition   *)
(*------------------------------------------*)

val ETREE_POWER_DISTRIBUTION_DEF = Define
`ETREE_POWER_DISTRIBUTION [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F] =

ETREE (NODE
       [BRANCH M1_S
       	   [BRANCH M2_S
	        [ATOMIC L1_S;
		 BRANCH L1_F [ATOMIC L2_S; ATOMIC L2_F]];		      
	    BRANCH M2_F 
	        [BRANCH M3_S
	            [ATOMIC L1_S;
		     BRANCH L1_F [ATOMIC L2_S; ATOMIC L2_F]];
		 BRANCH M3_F [ATOMIC L1_S; ATOMIC L1_F]]];
        BRANCH M1_F
       	   [BRANCH M2_S
	       [BRANCH M3_S
	       	   [ATOMIC L1_S;
		    BRANCH L1_F [ATOMIC L2_S; ATOMIC L2_F]];
	        BRANCH M3_F [ATOMIC L2_S; ATOMIC L2_F]];		
	    ATOMIC M2_F]])`; 
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------*)   
(*        LEMMA 2 (Model Proof)             *)
(*------------------------------------------*)

val ETREE_POWER_DISTRIBUTION_PROOF = store_thm("ETREE_POWER_DISTRIBUTION_PROOF",
``!M1_S M1_F M2_S M2_F M3_S M3_F L1_S L1_F L2_S L2_F.
ETREE (NODE(EVENT_TREE_LIST
      (NESTED_COMPLETE_CYLINDER
	(ETREE_N_STAIR_ALL_PATHS[L2_S;L2_F][[M1_S; M1_F];[M2_S; M2_F];[M3_S; M3_F];[L1_S; L1_F]])
        [[31;30;29;28;27;26;25;24];[23;22];[21;20];[17;16];[15;14];[13;12];[9;8];[7;6];[5;4];[3;2;1;0]]
	[[M1_F; M2_F];[M1_F; M2_S; M3_F; L2_F];[M1_F; M2_S; M3_F; L2_S];[M1_F; M2_S; M3_S; L1_S];
         [M1_S; M2_F; M3_F; L1_F];[M1_S; M2_F; M3_F; L1_S];[M1_S; M2_F; M3_S; L1_S];
	 [M1_S; M2_S; L1_F; L2_F];[M1_S; M2_S; L1_F; L2_S];[M1_S; M2_S; L1_S]]))) =

ETREE_POWER_DISTRIBUTION [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F]``,

rw [ETREE_POWER_DISTRIBUTION_DEF]
\\ rw [ETREE_DEF]
\\ EVAL_TAC
\\ DEP_REWRITE_TAC [EQ_SUBSET_SUBSET]
\\ rw [UNION_OVER_INTER, INTER_ASSOC, UNION_ASSOC]
\\ rw [EXTENSION]
\\ EQ_TAC
   >-(metis_tac [INTER_IDEMPOT])
\\ metis_tac [INTER_IDEMPOT]);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(* LEMMA 3  (ETree Power Distribution Paths)  *)
(*--------------------------------------------*)

val ETREE_POWER_DISTRIBUTION_PATHS_PROOF = store_thm("ETREE_POWER_DISTRIBUTION_PATHS_PROOF",
  ``!M1_S M1_F M2_S M2_F M3_S M3_F L1_S L1_F L2_S L2_F.
ETREE_POWER_DISTRIBUTION [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F] =
(M1_S ∩ M2_S ∩ L1_S) ∪
(M1_S ∩ M2_S ∩ L1_F ∩ L2_S) ∪
(M1_S ∩ M2_S ∩ L1_F ∩ L2_F) ∪
(M1_S ∩ M2_F ∩ M3_S ∩ L1_S) ∪
(M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_S) ∪
(M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F) ∪
(M1_S ∩ M2_F ∩ M3_F ∩ L1_S) ∪
(M1_S ∩ M2_F ∩ M3_F ∩ L1_F) ∪
(M1_F ∩ M2_S ∩ M3_S ∩ L1_S) ∪
(M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_S) ∪
(M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F) ∪
(M1_F ∩ M2_S ∩ M3_F ∩ L2_S) ∪
(M1_F ∩ M2_S ∩ M3_F ∩ L2_F) ∪
(M1_F ∩ M2_F) ``, 
rw [ETREE_POWER_DISTRIBUTION_DEF, ETREE_DEF]
\\ rw[UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [UNION_ASSOC]
\\ rw [EXTENSION]
\\ EQ_TAC
   >-(metis_tac [INTER_IDEMPOT])
\\ metis_tac [INTER_IDEMPOT]);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------*)  
(*     Load A Failure (Definition)     *)
(*-------------------------------------*)
val LOAD_A_FAILURE_DEF  = Define
`LOAD_A_FAILURE [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F] =
ETREE (NODE (EVENT_TREE_LIST (PARTITIONING [11;12;13]
      (NESTED_COMPLETE_CYLINDER
          (ETREE_N_STAIR_ALL_PATHS [L2_S;L2_F][[M1_S; M1_F];[M2_S; M2_F];[M3_S; M3_F];[L1_S; L1_F]])
	  [[31;30;29;28;27;26;25;24];[23;22];[21;20];[17;16];[15;14];[13;12];[9;8];[7;6];[5;4];[3;2;1;0]]
	  [[M1_F; M2_F];[M1_F; M2_S; M3_F; L2_F];[M1_F; M2_S; M3_F; L2_S];[M1_F; M2_S; M3_S; L1_S];
 	  [M1_S; M2_F; M3_F; L1_F];[M1_S; M2_F; M3_F; L1_S];[M1_S; M2_F; M3_S; L1_S];
 	  [M1_S; M2_S; L1_F; L2_F];[M1_S; M2_S; L1_F; L2_S];[M1_S; M2_S; L1_S]])))) `;
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------*)   
(*   LEMMA 4 (Load A Failure Paths Proof)   *)
(*------------------------------------------*)

val ETREE_LOAD_A_FAILURE_PATHS = store_thm("ETREE_LOAD_A_FAILURE_PATHS",
  ``!M1_S M1_F M2_S M2_F M3_S M3_F L1_S L1_F L2_S L2_F.
LOAD_A_FAILURE [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F] =
(M1_F ∩ M2_S ∩ M3_F ∩ L2_S) ∪
(M1_F ∩ M2_S ∩ M3_F ∩ L2_F) ∪
(M1_F ∩ M2_F)``,
rw []
\\ EVAL_TAC
\\ rw []
   >-( rw [INTER_ASSOC]
       \\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ rw [UNION_ASSOC]
       \\ sg `! a b c.  a UNION b UNION c = b UNION a UNION c`
       	  >-( rw [EXTENSION]
	      \\ metis_tac [])
       \\ fs []
       \\ rw [GSYM UNION_ASSOC])
   >-(rw [INTER_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ sg ` M1_F ∩ M2_S ∩ M3_F ∩ L2_S ∪ (M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F) =
               M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ (M1_F ∩ M2_S ∩ M3_F ∩ L2_S ∪ M1_F ∩ M2_F)`
  	  >-( rw [EXTENSION]
              \\ metis_tac [])
       \\ fs [])
\\ rw [INTER_ASSOC]
\\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_S ∪ (M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F) =
       M1_F ∩ M2_F  ∪ ( M1_F ∩ M2_S ∩ M3_F ∩ L2_S ∪ M1_F ∩ M2_S ∩ M3_F ∩ L2_F) `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ fs []);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------*)  
(*     Load B Failure (Definition)     *)
(*-------------------------------------*)

val LOAD_B_FAILURE_DEF  = Define
`LOAD_B_FAILURE [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F] =
ETREE (NODE (EVENT_TREE_LIST (PARTITIONING [6;7;13]
      (NESTED_COMPLETE_CYLINDER
        (ETREE_N_STAIR_ALL_PATHS [L2_S;L2_F][[M1_S; M1_F];[M2_S; M2_F];[M3_S; M3_F];[L1_S; L1_F]])
        [[31;30;29;28;27;26;25;24];[23;22];[21;20];[17;16];[15;14];[13;12];[9;8];[7;6];[5;4];[3;2;1;0]]
	[[M1_F; M2_F];[M1_F; M2_S; M3_F; L2_F];[M1_F; M2_S; M3_F; L2_S];[M1_F; M2_S; M3_S; L1_S];
         [M1_S; M2_F; M3_F; L1_F];[M1_S; M2_F; M3_F; L1_S];[M1_S; M2_F; M3_S; L1_S];
	 [M1_S; M2_S; L1_F; L2_F];[M1_S; M2_S; L1_F; L2_S];[M1_S; M2_S; L1_S]])))) `;
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------*)   
(*   LEMMA 5 (Load B Failure Paths Proof)   *)
(*------------------------------------------*)

val ETREE_LOAD_B_FAILURE_PATHS = store_thm("ETREE_LOAD_B_FAILURE_PATHS",
  ``!M1_S M1_F M2_S M2_F M3_S M3_F L1_S L1_F L2_S L2_F.
LOAD_B_FAILURE [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F] =
M1_F ∩ M2_F ∪
M1_S ∩ M2_F ∩ M3_F ∩ L1_F  ∪
M1_S ∩ M2_F ∩ M3_F ∩ L1_S``,
rw []
\\ EVAL_TAC
\\ rw []
   >-( rw [INTER_ASSOC]
       \\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ sg `M1_F ∩ M2_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_S =
   	     M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ (M1_F ∩ M2_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_S)`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs [])
   >-(rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ rw [UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ rw [UNION_ASSOC]
       \\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_S ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_F =
	      M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ (M1_S ∩ M2_F ∩ M3_F ∩ L1_S ∪ M1_F ∩ M2_F)`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs [])
\\ rw [INTER_ASSOC]
\\ rw [UNION_ASSOC]);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------*)  
(*     Load C Failure (Definition)     *)
(*-------------------------------------*)

val LOAD_C_FAILURE_DEF  = Define
`LOAD_C_FAILURE [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F] =
ETREE (NODE (EVENT_TREE_LIST (PARTITIONING [2;5;7;10;12;13]
      (NESTED_COMPLETE_CYLINDER
        (ETREE_N_STAIR_ALL_PATHS [L2_S;L2_F][[M1_S; M1_F];[M2_S; M2_F];[M3_S; M3_F];[L1_S; L1_F]])
        [[31;30;29;28;27;26;25;24];[23;22];[21;20];[17;16];[15;14];[13;12];[9;8];[7;6];[5;4];[3;2;1;0]]
	[[M1_F; M2_F];[M1_F; M2_S; M3_F; L2_F];[M1_F; M2_S; M3_F; L2_S];[M1_F; M2_S; M3_S; L1_S];
         [M1_S; M2_F; M3_F; L1_F];[M1_S; M2_F; M3_F; L1_S];[M1_S; M2_F; M3_S; L1_S];
	 [M1_S; M2_S; L1_F; L2_F];[M1_S; M2_S; L1_F; L2_S];[M1_S; M2_S; L1_S]])))) `;
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------*)   
(*   LEMMA 6 (Load C Failure Paths Proof)   *)
(*------------------------------------------*)

val ETREE_LOAD_C_FAILURE_PATHS = store_thm("ETREE_LOAD_B_FAILURE_PATHS",
  ``!M1_S M1_F M2_S M2_F M3_S M3_F L1_S L1_F L2_S L2_F.
LOAD_C_FAILURE [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_S; L1_F; L2_S; L2_F] =
M1_S ∩ M2_S ∩ L1_F ∩ L2_F  ∪
M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪
M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪
M1_F ∩ M2_F``,

rw []
\\ EVAL_TAC
\\ rw []
   >-( rw [GSYM UNION_ASSOC]
       \\ rw [INTER_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ sg ` M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
               M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
	       M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ 
   	       M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs []
	\\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ sg ` M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
               M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
	       M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪
	       M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs []
	\\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ sg ` M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
               M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
	       M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪
	       M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ 
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs []
	\\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ sg ` M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
               M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
	       M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
	       M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_F`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs []
	\\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ rw [UNION_ASSOC]
       \\ sg ` M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
               M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
	       M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪ M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪
	       M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ 
	       M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_F`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs []
	\\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ rw [UNION_ASSOC]
       \\ sg ` M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
               M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
	       M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
	       M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_F ∩ M2_F`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs []
	\\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ rw [UNION_ASSOC]
       \\ sg ` M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
               M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
	       M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪
	       M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪ M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ 
	       M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_F ∩ M2_F`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs []
	\\ rw [GSYM UNION_ASSOC])
   >-( rw [INTER_ASSOC]
       \\ rw [UNION_ASSOC]
       \\ sg ` M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
               M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
   	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
	       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
	       M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪ 
	       M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_F ∩ M2_F`
 	  >-( rw [EXTENSION]
	      \\ metis_tac [])
	\\ fs []
	\\ rw [GSYM UNION_ASSOC])
\\ rw [INTER_ASSOC]
\\ rw [UNION_ASSOC]);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------*)   
(*         Print All Path Numbers           *)
(*------------------------------------------*)

PRINT_ALL_PATH_NUMBERS
   ``[M1_S ∩ (M2_S ∩ (M3_S ∩ (L1_S ∩ L2_S)));
      M1_S ∩ (M2_S ∩ (M3_S ∩ (L1_S ∩ L2_F)));
      M1_S ∩ (M2_S ∩ (M3_S ∩ (L1_F ∩ L2_S)));
      M1_S ∩ (M2_S ∩ (M3_S ∩ (L1_F ∩ L2_F)));
      M1_S ∩ (M2_S ∩ (M3_F ∩ (L1_S ∩ L2_S)));
      M1_S ∩ (M2_S ∩ (M3_F ∩ (L1_S ∩ L2_F)));
      M1_S ∩ (M2_S ∩ (M3_F ∩ (L1_F ∩ L2_S)));
      M1_S ∩ (M2_S ∩ (M3_F ∩ (L1_F ∩ L2_F)));
      M1_S ∩ (M2_F ∩ (M3_S ∩ (L1_S ∩ L2_S)));
      M1_S ∩ (M2_F ∩ (M3_S ∩ (L1_S ∩ L2_F)));
      M1_S ∩ (M2_F ∩ (M3_S ∩ (L1_F ∩ L2_S)));
      M1_S ∩ (M2_F ∩ (M3_S ∩ (L1_F ∩ L2_F)));
      M1_S ∩ (M2_F ∩ (M3_F ∩ (L1_S ∩ L2_S)));
      M1_S ∩ (M2_F ∩ (M3_F ∩ (L1_S ∩ L2_F)));
      M1_S ∩ (M2_F ∩ (M3_F ∩ (L1_F ∩ L2_S)));
      M1_S ∩ (M2_F ∩ (M3_F ∩ (L1_F ∩ L2_F)));
      M1_F ∩ (M2_S ∩ (M3_S ∩ (L1_S ∩ L2_S)));
      M1_F ∩ (M2_S ∩ (M3_S ∩ (L1_S ∩ L2_F)));
      M1_F ∩ (M2_S ∩ (M3_S ∩ (L1_F ∩ L2_S)));
      M1_F ∩ (M2_S ∩ (M3_S ∩ (L1_F ∩ L2_F)));
      M1_F ∩ (M2_S ∩ (M3_F ∩ (L1_S ∩ L2_S)));
      M1_F ∩ (M2_S ∩ (M3_F ∩ (L1_S ∩ L2_F)));
      M1_F ∩ (M2_S ∩ (M3_F ∩ (L1_F ∩ L2_S)));
      M1_F ∩ (M2_S ∩ (M3_F ∩ (L1_F ∩ L2_F)));
      M1_F ∩ (M2_F ∩ (M3_S ∩ (L1_S ∩ L2_S)));
      M1_F ∩ (M2_F ∩ (M3_S ∩ (L1_S ∩ L2_F)));
      M1_F ∩ (M2_F ∩ (M3_S ∩ (L1_F ∩ L2_S)));
      M1_F ∩ (M2_F ∩ (M3_S ∩ (L1_F ∩ L2_F)));
      M1_F ∩ (M2_F ∩ (M3_F ∩ (L1_S ∩ L2_S)));
      M1_F ∩ (M2_F ∩ (M3_F ∩ (L1_S ∩ L2_F)));
      M1_F ∩ (M2_F ∩ (M3_F ∩ (L1_F ∩ L2_S)));
      M1_F ∩ (M2_F ∩ (M3_F ∩ (L1_F ∩ L2_F)))]``;
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(*    LEMMA 7 (Probability of Path 2 )        *)
(*--------------------------------------------*)

val PROB_PATH2_C = store_thm("PROB_PATH2_C",
``prob_space p /\  MUTUAL_INDEP p [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] /\
  (!x'. MEM x' [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] ==> x'  IN  events p) ==>
  (prob p (M1_S ∩ M2_S ∩ L1_F ∩ L2_F) = prob p M1_S * (prob p M2_S * (prob p L1_F * prob p L2_F)))``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_S; M2_S; L1_F; L2_F]`
>- ( once_rewrite_tac[(prove(``!a b c. a::d = [a]++d``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M1_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::c = [a;b;d]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M2_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::f::e = [a;b;d;f]++e``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M3_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1  
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::f::e::g = [a;b;d;f;e]++g``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M3_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1  
     \\ rw[])
\\ sg `M1_S ∩ M2_S ∩ L1_F ∩ L2_F =
   PATH p [M1_S; M2_S; L1_F; L2_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_S ∩ M2_S ∩ L1_F ∩ L2_F IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∩ p_space p =
              p_space p ∩ M1_S ∩ M2_S ∩ L1_F ∩ L2_F`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(*    LEMMA 8 (Probability of Path 5 )        *)
(*--------------------------------------------*)

val PROB_PATH5_C = store_thm("PROB_PATH5_C",
``prob_space p /\  MUTUAL_INDEP p [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] /\
  (!x'. MEM x' [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] ==> x'  IN  events p) ==>
  (prob p (M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F) =
   prob p M1_S * (prob p M2_F * (prob p M3_S * (prob p L1_F * prob p L2_F))))``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_S; M2_F; M3_S;L1_F;L2_F]`
>- ( once_rewrite_tac[(prove(``!a b c. a::d = [a]++d``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M1_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a;b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M2_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::f::e::g = [a;b;d;f;e]++g``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M3_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1  
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c f g h I. a::b::d::f::e::g::h =
                                                 [a;b;d;f;e;g]++h``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[L1_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c f g h I. a::b::d::f::e::i::x::g::h =
                                                 [a;b;d;f;e;i;x;g]++h``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[L2_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[])
\\ sg `M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F =
   PATH p [M1_S; M2_F; M3_S; L1_F; L2_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∩ p_space p =
              p_space p ∩ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F `
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(*    LEMMA 9 (Probability of Path 6 )        *)
(*--------------------------------------------*)

val PROB_PATH6_C = store_thm("PROB_PATH6_C",
``prob_space p /\  MUTUAL_INDEP p [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] /\
  (!x'. MEM x' [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] ==> x'  IN  events p) ==>
  (prob p (M1_S ∩ M2_F ∩ M3_F ∩ L1_F) = prob p M1_S * (prob p M2_F * (prob p M3_F * prob p L1_F)))``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_S; M2_F; M3_F; L1_F]`
>- ( once_rewrite_tac[(prove(``!a b c. a::d = [a]++d``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M1_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a;b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M2_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::f::g = [a;b;d;f]++g``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M3_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1  
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L2_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[])
\\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_F =
   PATH p [M1_S; M2_F; M3_F; L1_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_F IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∩ p_space p =
              p_space p ∩ M1_S ∩ M2_F ∩ M3_F ∩ L1_F`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val PROB_PATH6_B = store_thm("PROB_PATH6_B",
``prob_space p /\ MUTUAL_INDEP p [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] /\ 
  (!x'. MEM x' [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] ==> x'  IN  events p ) ==>
  (prob p (M1_S ∩ M2_F ∩ M3_F ∩ L1_F) = prob p M1_S * (prob p M2_F * (prob p M3_F * prob p L1_F)))``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_S; M2_F; M3_F; L1_F]`
>- ( once_rewrite_tac[(prove(``!a b c. a::d = [a]++d``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M1_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]   
     \\ once_rewrite_tac[(prove(``!a b c f g h I. a::b::d::f::h = [a;b;d;f]++h``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[L1_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[])
\\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_F =
   PATH p [M1_S; M2_F; M3_F; L1_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_F IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∩ p_space p =
              p_space p ∩ M1_S ∩ M2_F ∩ M3_F ∩ L1_F`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(*   LEMMA 10 (Probability of Path 7 )        *)
(*--------------------------------------------*)

val PROB_PATH7_B = store_thm("PROB_PATH7_B",
``prob_space p /\ MUTUAL_INDEP p [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] /\ 
  (!x'. MEM x' [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] ==> x'  IN  events p ) ==>
  (prob p (M1_S ∩ M2_F ∩ M3_F ∩ L1_S) = prob p M1_S * (prob p M2_F * (prob p M3_F * prob p L1_S)))``,
rw []
\\ sg ` MUTUAL_INDEP p [M1_S; M2_F; M3_F; L1_S]`
>- ( once_rewrite_tac[(prove(``!a b c. a::d = [a]++d``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M1_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]    
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L1_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[])
\\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_S =
   PATH p [M1_S; M2_F; M3_F; L1_S]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_S IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_S ∩ M2_F ∩ M3_F ∩ L1_S ∩ p_space p =
              p_space p ∩ M1_S ∩ M2_F ∩ M3_F ∩ L1_S`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(*  LEMMA 11 (Probability of Path 10 )        *)
(*--------------------------------------------*)

val PROB_PATH10_C = store_thm("PROB_PATH10_C",
 ``prob_space p /\ (!x'. MEM x' [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] ==> x' IN  events p ) /\
 (MUTUAL_INDEP p [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F])  ==>
  (prob p (M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F) =
   prob p M1_F * (prob p M2_S * (prob p M3_S * (prob p L1_F * prob p L2_F))))``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_F; M2_S; M3_S;L1_F;L2_F]`
>- ( irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `M1_S`
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::c = [a;b;d]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M2_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::f::e::g = [a;b;d;f;e]++g``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[M3_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1  
     \\ rw[])
\\ sg `M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F =
   PATH p [M1_F; M2_S; M3_S; L1_F; L2_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∩ p_space p =
              p_space p ∩ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F `
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(*   LEMMA 12 (Probability of Path 11)        *)
(*--------------------------------------------*)

val PROB_PATH11_A = store_thm("PROB_PATH11_A",
``MUTUAL_INDEP p [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] /\ prob_space p /\
  (!x'. MEM x' [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] ==> x'  IN  events p ) ==>
  (prob p (M1_F ∩ M2_S ∩ M3_F ∩ L2_S) = prob p M1_F * (prob p M2_S * (prob p M3_F * prob p L2_S)))``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_F; M2_S; M3_F; L2_S]`
>- ( rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L2_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a;b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M2_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[])
\\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_S =
   PATH p [M1_F; M2_S; M3_F; L2_S]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_S IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_S ∩ p_space p =
              p_space p ∩ M1_F ∩ M2_S ∩ M3_F ∩ L2_S`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(*   LEMMA 13 (Probability of Path 12)        *)
(*--------------------------------------------*)

val PROB_PATH12_C = store_thm("PROB_PATH12_C",
``prob_space p /\ (!x'. MEM x' [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] ==> x' IN  events p ) /\
 (MUTUAL_INDEP p [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F])  ==>
 (prob p (M1_F ∩ M2_S ∩ M3_F ∩ L2_F) = prob p M1_F * (prob p M2_S * (prob p M3_F * prob p L2_F)))``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_F; M2_S; M3_F; L2_F]`
>- (  irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `M1_S` 
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::e = [a;b;d]++e``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M2_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::e::f = [a;b;d;e]++f``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M3_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]    
     \\ once_rewrite_tac[(prove(``!a b c f g h I J. a::b::d::f::e::g::h = [a;b;d;f;e;g]++h``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[L1_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[])
\\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_F =
   PATH p [M1_F; M2_S; M3_F; L2_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg ` M1_F ∩ M2_S ∩ M3_F ∩ L2_F IN  events p `
       	  >-( metis_tac [EVENTS_INTER])
       \\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∩ p_space p =
              p_space p ∩ M1_F ∩ M2_S ∩ M3_F ∩ L2_F`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val PROB_PATH12_A = store_thm("PROB_PATH12_A",
``MUTUAL_INDEP p [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] /\ prob_space p /\
  (!x'. MEM x' [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] ==> x'  IN  events p ) ==>
  (prob p (M1_F ∩ M2_S ∩ M3_F ∩ L2_F) = prob p M1_F * (prob p M2_S * (prob p M3_F * prob p L2_F)))``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_F; M2_S; M3_F; L2_F]`
>- ( rw[]    
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d = [a;b]++d``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M2_F]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]    
     \\ once_rewrite_tac[(prove(``!a b c f g h I J. a::b::d::f::e = [a;b;d;f]++e``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND 
     \\ Q.EXISTS_TAC `[L2_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[])
\\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_F =
   PATH p [M1_F; M2_S; M3_F; L2_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg ` M1_F ∩ M2_S ∩ M3_F ∩ L2_F IN  events p `
       	  >-( metis_tac [EVENTS_INTER])
       \\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∩ p_space p =
              p_space p ∩ M1_F ∩ M2_S ∩ M3_F ∩ L2_F`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(*   LEMMA 14 (Probability of Path 13)        *)
(*--------------------------------------------*)

val PROB_PATH13_C = store_thm("PROB_PATH13_C",
``prob_space p /\ (!x'. MEM x' [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] ==> x' IN  events p ) /\
 (MUTUAL_INDEP p [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F])  ==>
  (prob p (M1_F ∩ M2_F) = prob p M1_F * prob p M2_F )``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_F; M2_F]`
>- ( once_rewrite_tac[(prove(``!a b c. a::c = [a]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M1_S]`
     \\ rw []
     \\ once_rewrite_tac[(prove(``!a b c. a::b::e = [a;b]++e``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M2_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::d::e::f = [a;b;d;e]++f``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M3_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]    
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `M3_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L1_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L2_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[])
\\ sg `M1_F ∩ M2_F=
   PATH p [M1_F; M2_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_F ∩ M2_F IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_F ∩ M2_F ∩ p_space p =
              p_space p ∩ M1_F ∩ M2_F`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val PROB_PATH13_B = store_thm("PROB_PATH13_B",
``prob_space p /\ MUTUAL_INDEP p [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] /\ 
  (!x'. MEM x' [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] ==> x'  IN  events p ) ==>
  (prob p (M1_F ∩ M2_F) = prob p M1_F * prob p M2_F )``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_F; M2_F]`
>- ( once_rewrite_tac[(prove(``!a b c. a::c = [a]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M1_S]`
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `M3_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L1_S`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L1_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[])
\\ sg `M1_F ∩ M2_F=
   PATH p [M1_F; M2_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_F ∩ M2_F IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_F ∩ M2_F ∩ p_space p =
              p_space p ∩ M1_F ∩ M2_F`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val PROB_PATH13_A = store_thm("PROB_PATH13_A",
``MUTUAL_INDEP p [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] /\ prob_space p /\
  (!x'. MEM x' [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] ==> x'  IN  events p ) ==>
  (prob p (M1_F ∩ M2_F) = prob p M1_F * prob p M2_F )``,

rw []
\\ sg ` MUTUAL_INDEP p [M1_F; M2_F]`
>- ( once_rewrite_tac[(prove(``!a b c. a::c = [a]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[M2_S]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `M3_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L2_S`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[]
     \\ irule MUTUAL_INDEP_CONS
     \\ Q.EXISTS_TAC `L2_F`
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_APPEND_SYM 
     \\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
     \\ rw[])
\\ sg `M1_F ∩ M2_F=
   PATH p [M1_F; M2_F]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `M1_F ∩ M2_F IN events p `
       	  >-(metis_tac[EVENTS_INTER])
       \\ sg `M1_F ∩ M2_F ∩ p_space p =
              p_space p ∩ M1_F ∩ M2_F`
          >-( rw [EXTENSION]
	      \\ EQ_TAC
	         >-(metis_tac [])
	      \\ metis_tac [])
       \\ fs []
       \\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ fs []
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------------*)   
(*   LEMMA 15 (Customer Interruption Expression Proof)  *)
(*------------------------------------------------------*)

val CUSTOMER_INTERRUPTIONS_EXPRESSSION = store_thm("CUSTOMER_INTERRUPTIONS_EXPRESSSION",
  ``!M1_S M1_F M2_S M2_F M3_S M3_F L1_S L1_F L2_S L2_F p X Y Z.
  CUSTOMER_INTERRUPTIONS
        [L2_S;L2_F][[M1_S; M1_F];[M2_S; M2_F];[M3_S; M3_F];[L1_S; L1_F]]
        [[31;30;29;28;27;26;25;24];[23;22];[21;20];[17;16];[15;14];[13;12];[9;8];[7;6];[5;4];[3;2;1;0]]
	[[M1_F; M2_F];[M1_F; M2_S; M3_F; L2_F];[M1_F; M2_S; M3_F; L2_S];[M1_F; M2_S; M3_S; L1_S];
         [M1_S; M2_F; M3_F; L1_F];[M1_S; M2_F; M3_F; L1_S];[M1_S; M2_F; M3_S; L1_S];
	 [M1_S; M2_S; L1_F; L2_F];[M1_S; M2_S; L1_F; L2_S];[M1_S; M2_S; L1_S]]
	[[11;12;13]; [6;7;13]; [2;5;7;10;12;13]] [X;Y;Z] p = 
prob p ( (M1_F ∩ M2_S ∩ M3_F ∩ L2_S) ∪
       	 (M1_F ∩ M2_S ∩ M3_F ∩ L2_F) ∪
	 (M1_F ∩ M2_F)) * (&X) +
prob p ( M1_S ∩ M2_F ∩ M3_F ∩ L1_S ∪
       	 M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪
  	 M1_F ∩ M2_F) * (&Y) +
prob p ( M1_S ∩ M2_S ∩ L1_F ∩ L2_F  ∪
       	 M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
	 M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪
	 M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
	 M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪
	 M1_F ∩ M2_F) * (&Z)``,
EVAL_TAC
\\ rw [INTER_ASSOC]
\\ rw [UNION_ASSOC]
\\ rw [GSYM REAL_ADD_ASSOC]);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------------*)   
(*   LEMMA 16 (SAIFI Expression Proof)                   *)
(*------------------------------------------------------*)

val SAIFI_EXPRESSSION = store_thm("SAIFI_EXPRESSSION",
  ``!M1_S M1_F M2_S M2_F M3_S M3_F L1_S L1_F L2_S L2_F p X Y Z.
  SAIFI
        [L2_S;L2_F][[M1_S; M1_F];[M2_S; M2_F];[M3_S; M3_F];[L1_S; L1_F]]
        [[31;30;29;28;27;26;25;24];[23;22];[21;20];[17;16];[15;14];[13;12];[9;8];[7;6];[5;4];[3;2;1;0]]
	[[M1_F; M2_F];[M1_F; M2_S; M3_F; L2_F];[M1_F; M2_S; M3_F; L2_S];[M1_F; M2_S; M3_S; L1_S];
         [M1_S; M2_F; M3_F; L1_F];[M1_S; M2_F; M3_F; L1_S];[M1_S; M2_F; M3_S; L1_S];
	 [M1_S; M2_S; L1_F; L2_F];[M1_S; M2_S; L1_F; L2_S];[M1_S; M2_S; L1_S]]
	[[11;12;13]; [6;7;13]; [2;5;7;10;12;13]] [X;Y;Z] p = 
(prob p ( M1_F ∩ M2_S ∩ M3_F ∩ L2_S ∪
       	  M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪
	  M1_F ∩ M2_F) * (&X) +
 prob p ( M1_S ∩ M2_F ∩ M3_F ∩ L1_S ∪
       	  M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪
  	  M1_F ∩ M2_F) * (&Y) +
 prob p ( M1_S ∩ M2_S ∩ L1_F ∩ L2_F  ∪
       	  M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
	  M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪
	  M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
	  M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪
	  M1_F ∩ M2_F) * (&Z))/ (&(X+Y+Z))``,
EVAL_TAC
\\ rw [INTER_ASSOC]
\\ rw [UNION_ASSOC]
\\ rw [GSYM REAL_ADD_ASSOC]);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(* LEMMA 14 Disjont of Load A Failure Paths  *)
(*-------------------------------------------*)

val DISJOINT_LOAD_A_FAILURE_PATHS1 = store_thm("DISJOINT_LOAD_A_FAILURE_PATHS1",
``ALL_DISTINCT [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] /\  
  disjoint {M2_S; M2_F} /\ disjoint {L2_S; L2_F} ==>
  (disjoint { M1_F ∩ M2_S ∩ M3_F ∩ L2_S;
              M1_F ∩ M2_S ∩ M3_F ∩ L2_F;
	      M1_F ∩ M2_F})``,
once_rewrite_tac [disjoint, ALL_DISTINCT]
\\ fs[EXTENSION] \\ metis_tac[]);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(* LEMMA 17 Disjont of Load B Failure Paths  *)
(*-------------------------------------------*)

val DISJOINT_LOAD_B_FAILURE_PATHS1 = store_thm("DISJOINT_LOAD_B_FAILURE_PATHS1",
``ALL_DISTINCT [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] /\
  disjoint {M1_S; M1_F}  /\ disjoint {L1_S; L1_F}  ==>
  (disjoint { M1_F ∩ M2_F;
  	      M1_S ∩ M2_F ∩ M3_F ∩ L1_F;
	      M1_S ∩ M2_F ∩ M3_F ∩ L1_S})``,
once_rewrite_tac [disjoint, ALL_DISTINCT]
\\ fs[EXTENSION] \\ metis_tac[]);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(* LEMMA 18 Disjont of Load C Failure Paths  *)
(*-------------------------------------------*)

val DISJOINT_LOAD_C_FAILURE_PATHS2 = store_thm("DISJOINT_LOAD_C_FAILURE_PATHS2",
``ALL_DISTINCT [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] /\  
  disjoint {M1_S; M1_F} /\ disjoint {M2_S; M2_F} /\ disjoint {M3_S; M3_F} ==>
  (disjoint { M1_S ∩ M2_S ∩ L1_F ∩ L2_F;
              M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F;
              M1_S ∩ M2_F ∩ M3_F ∩ L1_F;
	      M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F;
	      M1_F ∩ M2_S ∩ M3_F ∩ L2_F;
	      M1_F ∩ M2_F})``,
once_rewrite_tac [disjoint, ALL_DISTINCT]
\\ fs[EXTENSION] \\ metis_tac[]);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(* LEMMA 19  (Probability of Load A Failure)  *)
(*--------------------------------------------*)

val PROB_LOAD_A_FAILURE  = store_thm("PROB_LOAD_A_FAILURE",
``!M1_F M2_S M2_F M3_F L2_S L2_F  p.
  (prob_space p)  /\ ALL_DISTINCT [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] /\
  ALL_DISTINCT [ M1_F ∩ M2_S ∩ M3_F ∩ L2_S;  M1_F ∩ M2_S ∩ M3_F ∩ L2_F; M1_F ∩ M2_F] /\
  disjoint {M2_S; M2_F} /\ disjoint {L2_S; L2_F} /\
  (!x'. MEM x' [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F] ==> x'  IN  events p ) /\
  (MUTUAL_INDEP p [M1_F; M2_S; M2_F; M3_F; L2_S; L2_F]) ==>

 (prob p ( M1_F ∩ M2_S ∩ M3_F ∩ L2_S ∪ M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F) =
 (prob p M1_F) * ((prob p M2_S) * ((prob p M3_F) * (prob p L2_S))) +
 (prob p M1_F) * ((prob p M2_S) * ((prob p M3_F) * (prob p L2_F))) +
 (prob p M1_F) * (prob p M2_F))``,

rw []
\\ sg `M1_F ∩ M2_S ∩ M3_F ∩ L2_S ∪ M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F =
       ETREE (NODE (EVENT_TREE_LIST [M1_F ∩ M2_S ∩ M3_F ∩ L2_S;M1_F ∩ M2_S ∩ M3_F ∩ L2_F;M1_F ∩ M2_F])) `
   >-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])   
   >-( DEP_REWRITE_TAC [DISJOINT_LOAD_A_FAILURE_PATHS1]
       \\ fs [])
\\ rw [PROB_SUM_DEF]
\\ sg`prob p (M1_F ∩ M2_S ∩ M3_F ∩ L2_S) = prob p M1_F * (prob p M2_S * (prob p M3_F * prob p L2_S))`
   >-( DEP_REWRITE_TAC [PROB_PATH11_A]
       \\ rw []
       \\ metis_tac [])
\\ sg`prob p (M1_F ∩ M2_S ∩ M3_F ∩ L2_F) =
      prob p M1_F * (prob p M2_S * (prob p M3_F * prob p L2_F))`
   >-( DEP_REWRITE_TAC [PROB_PATH12_A]
       \\ rw []
       \\ metis_tac [])
\\ sg`prob p (M1_F ∩ M2_F) = prob p M1_F * prob p M2_F`      
   >-( DEP_REWRITE_TAC [PROB_PATH13_A]
       \\ rw []
       \\ metis_tac [])
\\ fs []
\\ rw []
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(* LEMMA 20  (Probability of Load B Failure)  *)
(*--------------------------------------------*)

val PROB_LOAD_B_FAILURE  = store_thm("PROB_LOAD_B_FAILURE",
``!M1_S M1_F M2_F M3_F L1_S L1_F p.
  (prob_space p)  /\ ALL_DISTINCT [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] /\  
  ALL_DISTINCT [M1_F ∩ M2_F; M1_S ∩ M2_F ∩ M3_F ∩ L1_F; M1_S ∩ M2_F ∩ M3_F ∩ L1_S] /\
  disjoint {M1_S ; M1_F}  /\ disjoint {L1_S; L1_F} /\
  (!x'. MEM x' [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F] ==> x'  IN  events p ) /\
  (MUTUAL_INDEP p [M1_S; M1_F; M2_F; M3_F; L1_S; L1_F]) ==>
 
 (prob p (M1_F ∩ M2_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_S) =
 (prob p M1_S) * ((prob p M2_F) * ((prob p M3_F) * (prob p L1_S))) +
 (prob p M1_S) * ((prob p M2_F) * ((prob p M3_F) * (prob p L1_F))) +
 (prob p M1_F) * (prob p M2_F))``,


rw []
\\ sg `M1_F ∩ M2_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_S ∩ M2_F ∩ M3_F ∩ L1_S  =
       ETREE (NODE (EVENT_TREE_LIST [M1_F ∩ M2_F; M1_S ∩ M2_F ∩ M3_F ∩ L1_F; M1_S ∩ M2_F ∩ M3_F ∩ L1_S])) `
   >-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])
   >-( DEP_REWRITE_TAC [DISJOINT_LOAD_B_FAILURE_PATHS1]
       \\ fs [])
\\ rw [PROB_SUM_DEF]
\\ sg`prob p (M1_S ∩ M2_F ∩ M3_F ∩ L1_S) = prob p M1_S * (prob p M2_F * (prob p M3_F * prob p L1_S))`
   >-( DEP_REWRITE_TAC [PROB_PATH7_B]
       \\ rw []
       \\ metis_tac [])
\\ sg`prob p (M1_S ∩ M2_F ∩ M3_F ∩ L1_F) =
      prob p M1_S * (prob p M2_F * (prob p M3_F * prob p L1_F))`
   >-( DEP_REWRITE_TAC [PROB_PATH6_B]
       \\ rw []
       \\ metis_tac [])
\\ sg`prob p (M1_F ∩ M2_F) = prob p M1_F * prob p M2_F`      
   >-( DEP_REWRITE_TAC [PROB_PATH13_B]
       \\ rw []
       \\ metis_tac [])
\\ fs []
\\ rw []
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)   
(* LEMMA 21  (Probability of Load C Failure)  *)
(*--------------------------------------------*)

val PROB_LOAD_C_FAILURE  = store_thm("PROB_LOAD_C_FAILURE",
``!M1_S M1_F M2_S M2_F M3_S M3_F L1_F L2_F p.
  (prob_space p)  /\ ALL_DISTINCT [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] /\  
  ALL_DISTINCT [ M1_S ∩ M2_S ∩ L1_F ∩ L2_F; M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F;
           	 M1_S ∩ M2_F ∩ M3_F ∩ L1_F; M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F;
           	 M1_F ∩ M2_S ∩ M3_F ∩ L2_F; M1_F ∩ M2_F] /\
  disjoint {M1_S ; M1_F} /\ disjoint {M2_S ; M2_F} /\ disjoint {M3_S; M3_F} /\
 (!x'. MEM x' [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F] ==> x' IN  events p ) /\
 (MUTUAL_INDEP p [M1_S; M1_F; M2_S; M2_F; M3_S; M3_F; L1_F; L2_F]) ==>
 
 (prob p ( M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪
       	   M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
           M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪
	   M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
           M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪
	   M1_F ∩ M2_F) =
 (prob p M1_S) * ((prob p M2_S) * ((prob p L1_F) * (prob p L2_F))) +
 (prob p M1_S) * ((prob p M2_F) * ((prob p M3_S) * ((prob p L1_F) * (prob p L2_F)))) +
 (prob p M1_S) * ((prob p M2_F) * ((prob p M3_F) * (prob p L1_F))) +
 (prob p M1_F) * ((prob p M2_S) * ((prob p M3_S) * ((prob p L1_F) * (prob p L2_F)))) +
 (prob p M1_F) * ((prob p M2_S) * ((prob p M3_F) * (prob p L2_F))) +
 (prob p M1_F) * (prob p M2_F))``,

rw []
\\ sg `M1_S ∩ M2_S ∩ L1_F ∩ L2_F ∪ M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F ∪
       M1_S ∩ M2_F ∩ M3_F ∩ L1_F ∪ M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F ∪
       M1_F ∩ M2_S ∩ M3_F ∩ L2_F ∪ M1_F ∩ M2_F  =
       ETREE (NODE (EVENT_TREE_LIST [M1_S ∩ M2_S ∩ L1_F ∩ L2_F; M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F;
           	    		     M1_S ∩ M2_F ∩ M3_F ∩ L1_F; M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F;
           	    		     M1_F ∩ M2_S ∩ M3_F ∩ L2_F; M1_F ∩ M2_F])) `
   >-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF] 
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])
   >-(metis_tac [EVENTS_INTER])
   >-( DEP_REWRITE_TAC [DISJOINT_LOAD_C_FAILURE_PATHS2]
       \\ fs [])
\\ rw [PROB_SUM_DEF]
\\ sg`prob p (M1_S ∩ M2_S ∩ L1_F ∩ L2_F) = (prob p M1_S) * ((prob p M2_S) * ((prob p L1_F) * (prob p L2_F)))`
   >-( DEP_REWRITE_TAC [PROB_PATH2_C]
       \\ rw []
       \\ metis_tac [])
\\ sg`prob p (M1_S ∩ M2_F ∩ M3_S ∩ L1_F ∩ L2_F) = (prob p M1_S) * ((prob p M2_F) * ((prob p M3_S) * ((prob p L1_F) * (prob p L2_F))))`
   >-( DEP_REWRITE_TAC [PROB_PATH5_C]
       \\ rw []
       \\ metis_tac [])       
\\ sg`prob p (M1_S ∩ M2_F ∩ M3_F ∩ L1_F) = (prob p M1_S) * ((prob p M2_F) * ((prob p M3_F) * (prob p L1_F)))`
   >-( DEP_REWRITE_TAC [PROB_PATH6_C]
       \\ rw []
       \\ metis_tac [])
\\ sg`prob p (M1_F ∩ M2_S ∩ M3_S ∩ L1_F ∩ L2_F) = (prob p M1_F) * ((prob p M2_S) * ((prob p M3_S) * ((prob p L1_F) * (prob p L2_F))))`
   >-( DEP_REWRITE_TAC [PROB_PATH10_C]
       \\ rw []
       \\ metis_tac [])
\\ sg`prob p (M1_F ∩ M2_S ∩ M3_F ∩ L2_F) = (prob p M1_F) * ((prob p M2_S) * ((prob p M3_F) * (prob p L2_F)))`
   >-( DEP_REWRITE_TAC [PROB_PATH12_C]
       \\ rw []
       \\ metis_tac [])       
\\ sg`prob p (M1_F ∩ M2_F) = (prob p M1_F) * (prob p M2_F)`
   >-( DEP_REWRITE_TAC [PROB_PATH13_C]
       \\ rw []
       \\ metis_tac [])
\\ fs []
\\ rw []
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------------------------*)   
(* LEMMA 22  (Probability of Load A Failure Exponential Distribution)  *)
(*---------------------------------------------------------------------*)

val PROB_LOAD_A_FAILURE_EXP_DISTRIBUTION  = store_thm("PROB_LOAD_A_FAILURE_EXP_DISTRIBUTION",
``! M1 M2 M3 L2 p t FR_M1 FR_M2 FR_M3 FR_L2.

  (prob_space p)  /\ 0 <= t /\  
  ALL_DISTINCT [FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t; FAIL p M3 t;
	        SUCCESS p L2 t; FAIL p L2 t] /\
  ALL_DISTINCT [(FAIL p M1 t ∩ SUCCESS p M2 t ∩ FAIL p M3 t ∩ SUCCESS p L2 t);
	      	(FAIL p M1 t ∩ SUCCESS p M2 t ∩ FAIL p M3 t ∩ FAIL p L2 t);
	        (FAIL p M1 t ∩ FAIL p M2 t)] /\
  disjoint {SUCCESS p M2 t; FAIL p M2 t} /\ disjoint {SUCCESS p L2 t; FAIL p L2 t} /\
  (!x'. MEM x' [FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t; FAIL p M3 t;
	        SUCCESS p L2 t; FAIL p L2 t] ==> x' IN events p ) /\
  (MUTUAL_INDEP p [FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t; FAIL p M3 t; SUCCESS p L2 t; FAIL p L2 t]) /\
  EXP_ET_DISTRIB p M1 FR_M1 /\ EXP_ET_DISTRIB p M2 FR_M2 /\
  EXP_ET_DISTRIB p M3 FR_M3 /\ EXP_ET_DISTRIB p L2 FR_L2  ==>
 
   (prob p (FAIL p M1 t ∩ SUCCESS p M2 t ∩ FAIL p M3 t ∩ SUCCESS p L2 t ∪
       	    FAIL p M1 t ∩ SUCCESS p M2 t ∩ FAIL p M3 t ∩ FAIL p L2 t ∪
	    FAIL p M1 t ∩ FAIL p M2 t) =
   (1 - exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ( (1 - exp (-FR_M3 * t)) * (exp (-FR_L2 * t)))) +
   (1 - exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ( (1 - exp (-FR_M3 * t)) * (1- exp (-FR_L2 * t)))) +
   (1 - exp (-FR_M1 * t)) * (1- exp (-FR_M2 * t)))``,

rw []
\\ DEP_REWRITE_TAC [PROB_LOAD_A_FAILURE]
\\ fs []
\\ CONJ_TAC
   >-(metis_tac [])
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ sg `!X. prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]
\\ fs [EXP_ET_DISTRIB_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------------------------*)   
(* LEMMA 23  (Probability of Load B Failure Exponential Distribution)  *)
(*---------------------------------------------------------------------*)

val PROB_LOAD_B_FAILURE_EXP_DISTRIBUTION  = store_thm("PROB_LOAD_B_FAILURE_EXP_DISTRIBUTION",
``! M1 M2 M3 L1 p t FR_M1 FR_M2 FR_M3 FR_L1.

  (prob_space p)  /\ 0 <= t /\
  ALL_DISTINCT [SUCCESS p M1 t ; FAIL p M1 t ; FAIL p M2 t; FAIL p M3 t; SUCCESS p L1 t; FAIL p L1 t] /\
  ALL_DISTINCT [(SUCCESS p M1 t ∩ FAIL p M2 t ∩ FAIL p M3 t ∩  SUCCESS p L1 t);
	       	(SUCCESS p M1 t ∩ FAIL p M2 t ∩ FAIL p M3 t ∩ FAIL p L1 t);	       
	        (FAIL p M1 t ∩ FAIL p M2 t)] /\
  disjoint {SUCCESS p M1 t; FAIL p M1 t} /\ disjoint {SUCCESS p L1 t; FAIL p L1 t} /\
  (!x'. MEM x' [SUCCESS p M1 t ; FAIL p M1 t ; FAIL p M2 t;
                FAIL p M3 t; SUCCESS p L1 t; FAIL p L1 t] ==> x' IN events p ) /\
  (MUTUAL_INDEP p [SUCCESS p M1 t ; FAIL p M1 t ; FAIL p M2 t; FAIL p M3 t; SUCCESS p L1 t; FAIL p L1 t]) /\
  EXP_ET_DISTRIB p M1 FR_M1   /\ EXP_ET_DISTRIB p M2 FR_M2 /\
  EXP_ET_DISTRIB p M3 FR_M3 /\ EXP_ET_DISTRIB p L1 FR_L1 ==>
 
   (prob p (FAIL p M1 t ∩ FAIL p M2 t ∪ SUCCESS p M1 t ∩ FAIL p M2 t ∩ FAIL p M3 t ∩ FAIL p L1 t ∪
            SUCCESS p M1 t ∩ FAIL p M2 t ∩  FAIL p M3 t ∩  SUCCESS p L1 t) =
   (exp (-FR_M1 * t)) * ((1 - exp (-FR_M2 * t)) * ((1 - exp (-FR_M3 * t)) * (exp (-FR_L1 * t)))) +
   (exp (-FR_M1 * t)) * ((1 - exp (-FR_M2 * t)) * ((1 - exp (-FR_M3 * t)) * (1 - exp (-FR_L1 * t)))) +
   (1 - exp (-FR_M1 * t)) * (1- exp (-FR_M2 * t)))``,

rw []
\\ DEP_REWRITE_TAC [PROB_LOAD_B_FAILURE]
\\ fs []
\\ CONJ_TAC
   >-(metis_tac [])
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ sg `!X. prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]
\\ fs [EXP_ET_DISTRIB_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------------------------*)   
(* LEMMA 24  (Probability of Load C Failure Exponential Distribution)  *)
(*---------------------------------------------------------------------*)

val PROB_LOAD_C_FAILURE_EXP_DISTRIBUTION  = store_thm("PROB_LOAD_C_FAILURE_EXP_DISTRIBUTION",
``! M1 M2 M3 L1 L2 p t FR_M1 FR_M2 FR_M3 FR_L1 FR_L2.

  (prob_space p)  /\ 0 <= t /\
  ALL_DISTINCT [SUCCESS p M1 t ; FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t;
		SUCCESS p M3 t; FAIL p M3 t;  FAIL p L1 t; FAIL p L2 t] /\
  ALL_DISTINCT [(SUCCESS p M1 t ∩ SUCCESS p M2 t ∩ FAIL p L1 t ∩ FAIL p L2 t);
	        (SUCCESS p M1 t ∩ FAIL p M2 t ∩ SUCCESS p M3 t ∩ FAIL p L1 t ∩ FAIL p L2 t);
	       	(SUCCESS p M1 t ∩ FAIL p M2 t ∩ FAIL p M3 t ∩ FAIL p L1 t);
		(FAIL p M1 t ∩ SUCCESS p M2 t ∩ SUCCESS p M3 t ∩ FAIL p L1 t ∩ FAIL p L2 t);
	      	(FAIL p M1 t ∩ SUCCESS p M2 t ∩ FAIL p M3 t ∩ FAIL p L2 t);
	        (FAIL p M1 t ∩ FAIL p M2 t)] /\
  disjoint {SUCCESS p M1 t; FAIL p M1 t} /\ disjoint {SUCCESS p M2 t; FAIL p M2 t} /\
  disjoint {SUCCESS p M3 t; FAIL p M3 t} /\
  (!x'. MEM x' [SUCCESS p M1 t ; FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t;
		SUCCESS p M3 t; FAIL p M3 t;  FAIL p L1 t; FAIL p L2 t] ==> x' IN events p ) /\
  (MUTUAL_INDEP p [SUCCESS p M1 t ; FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t;
		   SUCCESS p M3 t; FAIL p M3 t;  FAIL p L1 t; FAIL p L2 t]) /\
  EXP_ET_DISTRIB p M1 FR_M1   /\ EXP_ET_DISTRIB p M2 FR_M2 /\
  EXP_ET_DISTRIB p M3 FR_M3 /\ EXP_ET_DISTRIB p L1 FR_L1 /\ EXP_ET_DISTRIB p L2 FR_L2 ==>
 
   (prob p ( SUCCESS p M1 t ∩ SUCCESS p M2 t ∩ FAIL p L1 t ∩ FAIL p L2 t ∪
   	     SUCCESS p M1 t ∩ FAIL p M2 t ∩ SUCCESS p M3 t ∩ FAIL p L1 t ∩ FAIL p L2 t  ∪
             SUCCESS p M1 t ∩ FAIL p M2 t ∩ FAIL p M3 t ∩ FAIL p L1 t ∪
	     FAIL p M1 t ∩ SUCCESS p M2 t ∩ SUCCESS p M3 t ∩ FAIL p L1 t ∩ FAIL p L2 t  ∪
             FAIL p M1 t ∩ SUCCESS p M2 t ∩ FAIL p M3 t ∩ FAIL p L2 t ∪
	     FAIL p M1 t ∩ FAIL p M2 t) =

   (exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ( (1 - exp (-FR_L1 * t)) * (1 - exp (-FR_L2 * t)))) +
   (exp (-FR_M1 * t)) * ((1 - exp (-FR_M2 * t)) * ((exp (-FR_M3 * t)) * ((1 - exp (-FR_L1 * t)) * (1 - exp (-FR_L2 * t))))) +
   (exp (-FR_M1 * t)) * ((1 - exp (-FR_M2 * t)) * ((1 - exp (-FR_M3 * t)) * (1 - exp (-FR_L1 * t)))) +
   (1 - exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ((exp (-FR_M3 * t)) * ((1 - exp (-FR_L1 * t)) * (1 - exp (-FR_L2 * t))))) +
   (1 - exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ((1 - exp (-FR_M3 * t)) * (1 - exp (-FR_L2 * t)))) +
   (1 - exp (-FR_M1 * t)) * (1- exp (-FR_M2 * t)))``,

rw []
\\ DEP_REWRITE_TAC [PROB_LOAD_C_FAILURE]
\\ fs []
\\ CONJ_TAC
   >-(metis_tac [])
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ sg `!X. prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]
\\ fs [EXP_ET_DISTRIB_DEF]
\\ rw [REAL_SUB_SUB2]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_LEM1  = store_thm("MUTUAL_INDEP_LEM1",
`` MUTUAL_INDEP p [SUCCESS p M1 t ; FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t;
		   SUCCESS p M3 t; FAIL p M3 t; SUCCESS p L1 t; FAIL p L1 t;
		   SUCCESS p L2 t; FAIL p L2 t] ==>
((MUTUAL_INDEP p [FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t; FAIL p M3 t; SUCCESS p L2 t; FAIL p L2 t]) /\
(MUTUAL_INDEP p [SUCCESS p M1 t ; FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t; SUCCESS p M3 t; FAIL p M3 t;  FAIL p L1 t; FAIL p L2 t]) /\
(MUTUAL_INDEP p [SUCCESS p M1 t ; FAIL p M1 t ; FAIL p M2 t; FAIL p M3 t; SUCCESS p L1 t; FAIL p L1 t]))``,

rw []
>-( once_rewrite_tac[(prove(``!a b c. a::c = [a]++c``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[SUCCESS p M1 t]`
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::e::f::g = [a;b;e;f]++g``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[SUCCESS p M3 t]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::e::f::h::k::g = [a;b;e;f;h;k]++g``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[SUCCESS p L1 t]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]
     \\ once_rewrite_tac[(prove(``!a b c. a::b::e::f::h::k::d::g = [a;b;e;f;h;k;d]++g``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[FAIL p L1 t]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[])
>-( once_rewrite_tac[(prove(``!a b c. a::b::e::f::h::k::g = [a;b;e;f;h;k]++g``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[SUCCESS p L1 t]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[]    
     \\ once_rewrite_tac[(prove(``!a b c. a::b::e::f::h::k::d::g::s = [a;b;e;f;h;k;d;g]++s``,rw[]))]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `[SUCCESS p L2 t]`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1 
     \\ rw[])
\\ once_rewrite_tac[(prove(``!a b c. a::b::g = [a;b]++g``,rw[]))]
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `[SUCCESS p M2 t]`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_APPEND1 
\\ rw[]
\\ once_rewrite_tac[(prove(``!a b c. a::b::e::f::g = [a;b;e;f]++g``,rw[]))]
\\ irule MUTUAL_INDEP_FRONT_APPEND
\\ Q.EXISTS_TAC `[SUCCESS p M3 t]`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_APPEND1 
\\ rw[]
\\ irule MUTUAL_INDEP_CONS
\\ Q.EXISTS_TAC `SUCCESS p L2 t`
\\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
\\ irule MUTUAL_INDEP_APPEND_SYM 
\\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
\\ rw[]
\\ irule MUTUAL_INDEP_CONS
\\ Q.EXISTS_TAC `FAIL p L2 t`
\\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
\\ irule MUTUAL_INDEP_APPEND_SYM 
\\ once_rewrite_tac[(prove(``!a b. b::c = [b]++c``,rw[]))]
\\ rw[]);

(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------*)   
(* LEMMA 25  (SAIFI Exponential Distribution)  *)
(*---------------------------------------------*)

val SAIFI_EXP_DISTRIBUTION  = store_thm("SAIFI_EXP_DISTRIBUTION",
``! M1 M2 M3 L1 L2 p t FR_M1 FR_M2 FR_M3 FR_L1 FR_L2 X Y Z.

  (prob_space p)  /\ 0 <= t /\
  ALL_DISTINCT [SUCCESS p M1 t ; FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t;
		SUCCESS p M3 t; FAIL p M3 t; SUCCESS p L1 t; FAIL p L1 t;
		SUCCESS p L2 t; FAIL p L2 t] /\
  ALL_DISTINCT [(SUCCESS p M1 t ∩ SUCCESS p M2 t ∩  SUCCESS p L1 t);
  	        (SUCCESS p M1 t ∩ SUCCESS p M2 t ∩ FAIL p L1 t ∩ SUCCESS p L2 t);
	        (SUCCESS p M1 t ∩ SUCCESS p M2 t ∩ FAIL p L1 t ∩ FAIL p L2 t);
	        (SUCCESS p M1 t ∩ FAIL p M2 t ∩ SUCCESS p M3 t ∩  SUCCESS p L1 t);
	        (SUCCESS p M1 t ∩ FAIL p M2 t ∩ SUCCESS p M3 t ∩ FAIL p L1 t ∩ SUCCESS p L2 t);
	       	(SUCCESS p M1 t ∩ FAIL p M2 t ∩ SUCCESS p M3 t ∩ FAIL p L1 t ∩ FAIL p L2 t);
	       	(SUCCESS p M1 t ∩ FAIL p M2 t ∩ FAIL p M3 t ∩  SUCCESS p L1 t);
	       	(SUCCESS p M1 t ∩ FAIL p M2 t ∩ FAIL p M3 t ∩ FAIL p L1 t);
	       	(FAIL p M1 t ∩ SUCCESS p M2 t ∩ SUCCESS p M3 t ∩  SUCCESS p L1 t);
	       	(FAIL p M1 t ∩ SUCCESS p M2 t ∩ SUCCESS p M3 t ∩ FAIL p L1 t ∩ SUCCESS p L2 t);
	      	(FAIL p M1 t ∩ SUCCESS p M2 t ∩ SUCCESS p M3 t ∩ FAIL p L1 t ∩ FAIL p L2 t);
	      	(FAIL p M1 t ∩ SUCCESS p M2 t ∩ FAIL p M3 t ∩ SUCCESS p L2 t);
	      	(FAIL p M1 t ∩ SUCCESS p M2 t ∩ FAIL p M3 t ∩ FAIL p L2 t);
	        (FAIL p M1 t ∩ FAIL p M2 t)] /\
  disjoint {SUCCESS p M1 t; FAIL p M1 t} /\ disjoint {SUCCESS p M2 t; FAIL p M2 t} /\
  disjoint {SUCCESS p M3 t; FAIL p M3 t} /\ disjoint {SUCCESS p L1 t; FAIL p L1 t} /\
  disjoint {SUCCESS p L2 t; FAIL p L2 t} /\
  (!x'. MEM x' [SUCCESS p M1 t ; FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t;
	        SUCCESS p M3 t; FAIL p M3 t; SUCCESS p L1 t; FAIL p L1 t;
	        SUCCESS p L2 t; FAIL p L2 t] ==> x' IN events p ) /\
  (MUTUAL_INDEP p [SUCCESS p M1 t ; FAIL p M1 t ; SUCCESS p M2 t; FAIL p M2 t;
		   SUCCESS p M3 t; FAIL p M3 t; SUCCESS p L1 t; FAIL p L1 t;
		   SUCCESS p L2 t; FAIL p L2 t]) /\

  EXP_ET_DISTRIB p M1 FR_M1   /\ EXP_ET_DISTRIB p M2 FR_M2 /\
  EXP_ET_DISTRIB p M3 FR_M3 /\ EXP_ET_DISTRIB p L1 FR_L1 /\ EXP_ET_DISTRIB p L2 FR_L2 ==>
  
(SAIFI  [SUCCESS p L2 t;FAIL p L2 t][[SUCCESS p M1 t; FAIL p M1 t];[SUCCESS p M2 t; FAIL p M2 t];
	[SUCCESS p M3 t; FAIL p M3 t];[SUCCESS p L1 t; FAIL p L1 t]]
        [[31;30;29;28;27;26;25;24];[23;22];[21;20];[17;16];[15;14];[13;12];[9;8];[7;6];[5;4];[3;2;1;0]]
	[[FAIL p M1 t; FAIL p M2 t];[FAIL p M1 t; SUCCESS p M2 t; FAIL p M3 t; FAIL p L2 t];
	[FAIL p M1 t; SUCCESS p M2 t; FAIL p M3 t; SUCCESS p L2 t];[FAIL p M1 t; SUCCESS p M2 t; SUCCESS p M3 t; SUCCESS p L1 t];
        [SUCCESS p M1 t; FAIL p M2 t; FAIL p M3 t; FAIL p L1 t];[SUCCESS p M1 t; FAIL p M2 t; FAIL p M3 t; SUCCESS p L1 t];
	[SUCCESS p M1 t; FAIL p M2 t; SUCCESS p M3 t; SUCCESS p L1 t];
	[SUCCESS p M1 t; SUCCESS p M2 t; FAIL p L1 t; FAIL p L2 t];
	[SUCCESS p M1 t; SUCCESS p M2 t; FAIL p L1 t; SUCCESS p L2 t];[SUCCESS p M1 t; SUCCESS p M2 t; SUCCESS p L1 t]]
	[[11;12;13]; [6;7;13]; [2;5;7;10;12;13]] [X;Y;Z] p = 
(((1 - exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ( (1 - exp (-FR_M3 * t)) * (exp (-FR_L2 * t)))) +
   (1 - exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ( (1 - exp (-FR_M3 * t)) * (1- exp (-FR_L2 * t)))) +
   (1 - exp (-FR_M1 * t)) * (1- exp (-FR_M2 * t))) * (&X) +
 ((exp (-FR_M1 * t)) * ((1 - exp (-FR_M2 * t)) * ((1 - exp (-FR_M3 * t)) * (exp (-FR_L1 * t)))) +
   (exp (-FR_M1 * t)) * ((1 - exp (-FR_M2 * t)) * ((1 - exp (-FR_M3 * t)) * (1 - exp (-FR_L1 * t)))) +
   (1 - exp (-FR_M1 * t)) * (1- exp (-FR_M2 * t))) * (&Y) +
 ((exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ( (1 - exp (-FR_L1 * t)) * (1 - exp (-FR_L2 * t)))) +
   (exp (-FR_M1 * t)) * ((1 - exp (-FR_M2 * t)) * ((exp (-FR_M3 * t)) * ((1 - exp (-FR_L1 * t)) * (1 - exp (-FR_L2 * t))))) +
   (exp (-FR_M1 * t)) * ((1 - exp (-FR_M2 * t)) * ((1 - exp (-FR_M3 * t)) * (1 - exp (-FR_L1 * t)))) +
   (1 - exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ((exp (-FR_M3 * t)) * ((1 - exp (-FR_L1 * t)) * (1 - exp (-FR_L2 * t))))) +
   (1 - exp (-FR_M1 * t)) * (exp (-FR_M2 * t) * ((1 - exp (-FR_M3 * t)) * (1 - exp (-FR_L2 * t)))) +
   (1 - exp (-FR_M1 * t)) * (1- exp (-FR_M2 * t))) * (&Z))/ (&(X+Y+Z)))``,
DEP_REWRITE_TAC [SAIFI_EXPRESSSION]
\\ rw[]
\\ DEP_REWRITE_TAC [PROB_LOAD_A_FAILURE_EXP_DISTRIBUTION]
\\ rw[]
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [MUTUAL_INDEP_LEM1])
\\ sg `↑ p M1 t ∩ ↓ p M2 t ∩ ↓ p M3 t ∩ ↑ p L1 t ∪
       ↑ p M1 t ∩ ↓ p M2 t ∩ ↓ p M3 t ∩ ↓ p L1 t ∪ ↓ p M1 t ∩ ↓ p M2 t =
       ↓ p M1 t ∩ ↓ p M2 t ∪ ↑ p M1 t ∩ ↓ p M2 t ∩ ↓ p M3 t ∩ ↓ p L1 t ∪
       ↑ p M1 t ∩ ↓ p M2 t ∩ ↓ p M3 t ∩ ↑ p L1 t`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_LOAD_B_FAILURE_EXP_DISTRIBUTION]
\\ rw[]
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [MUTUAL_INDEP_LEM1])
\\ DEP_REWRITE_TAC [PROB_LOAD_C_FAILURE_EXP_DISTRIBUTION]
\\ rw[]
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])   
\\ metis_tac [MUTUAL_INDEP_LEM1]);
(*--------------------------------------------------------------------------------------------------*)

				(*----------------------------*)  
				(*    ML Evaluation Results   *)
				(*----------------------------*)

(*---------------------------------*)   
(* Assume  FR_M1 =  3 per year     *)
(* Assume  FR_M2 =  2 per year     *)
(* Assume  FR_M3 =  1 per year     *)
(* Assume  FR_L1 =  4 per year     *)
(* Assume  FR_L2 =  5 per year     *)
(*---------------------------------*)

(*-------------------------------------------------*)   
(* Evaluation 1  (Probability of Load A Failure)   *)
(*-------------------------------------------------*)

PROBABILITY ``Load_A_Failure``
``(1 - exp (-3:real)) * (exp (-2:real))  * (1 - exp (-1:real)) * (exp (-5:real)) +
  (1 - exp (-3:real)) * (exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-5:real)) +
  (1 - exp (-3:real)) * (1 - exp (-2:real))``;
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------------*)   
(* Evaluation 2  (Probability of Load B Failure)   *)
(*-------------------------------------------------*)

PROBABILITY ``Load_B_Failure``
``(1 - exp (-3:real)) * (1 - exp (-2:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) *  (1- exp (-4:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) * (exp (-4:real)) ``;
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------------*)   
(* Evaluation 3  (Probability of Load C Failure)   *)
(*-------------------------------------------------*)

PROBABILITY ``Load_C_Failure``
``(exp (-3:real)) * (exp (-2:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (exp (-1:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-4:real)) +
(1 - exp (-3:real)) * (exp (-2:real)) * (exp (-1:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(1 - exp (-3:real)) * (exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-5:real)) +
(1 - exp (-3:real)) * (1 - exp (-2:real)) ``;
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------------------*)   
(* Evaluation 4   (Total Annual Customer interruptions)  *)
(*-------------------------------------------------------*)

CUSTOMER_INTERRUPTIONS
``((1 - exp (-3:real)) * (exp (-2:real))  * (1 - exp (-1:real)) * (exp (-5:real)) +
  (1 - exp (-3:real)) * (exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-5:real)) +
  (1 - exp (-3:real)) * (1 - exp (-2:real))) * 250 + 
  ((1 - exp (-3:real)) * (1 - exp (-2:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) *  (1- exp (-4:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) * (exp (-4:real))) * 100 +
  ((exp (-3:real)) * (exp (-2:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (exp (-1:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-4:real)) +
(1 - exp (-3:real)) * (exp (-2:real)) * (exp (-1:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(1 - exp (-3:real)) * (exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-5:real)) +
(1 - exp (-3:real)) * (1 - exp (-2:real))) * 50``;
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------*)   
(* Evaluation 5   (System Average Interruption Frequency Index (SAIFI))  *)
(*-----------------------------------------------------------------------*)

SAIFI
``(((1 - exp (-3:real)) * (exp (-2:real))  * (1 - exp (-1:real)) * (exp (-5:real)) +
  (1 - exp (-3:real)) * (exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-5:real)) +
  (1 - exp (-3:real)) * (1 - exp (-2:real))) * 250 + 
  ((1 - exp (-3:real)) * (1 - exp (-2:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) *  (1- exp (-4:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) * (exp (-4:real))) * 100 +
  ((exp (-3:real)) * (exp (-2:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (exp (-1:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(exp (-3:real)) * (1 - exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-4:real)) +
(1 - exp (-3:real)) * (exp (-2:real)) * (exp (-1:real)) * (1- exp (-4:real)) * (1- exp (-5:real)) +
(1 - exp (-3:real)) * (exp (-2:real)) * (1 - exp (-1:real)) * (1- exp (-5:real)) +
(1 - exp (-3:real)) * (1 - exp (-2:real))) * 50)/400``;

val _ = export_theory();

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
	(*------------------------------------------------------------------------------*)
		       (*--------------------------------------------------*)
			         (*--------------------------------*)
					  (*---------------*)
						(*-----*)
