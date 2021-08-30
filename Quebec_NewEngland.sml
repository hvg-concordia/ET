(* ========================================================================= *)
(* File Name: IEEE_118_BUS.sml	                                 	     *)
(*---------------------------------------------------------------------------*)
(*          Description: Reliability Analysis of a Quebec - New England      *)
(*                       Tranmission Coupling Between Canada and US          *)
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
     
val _ = new_theory "Quebec";
(*--------------------------------------------------------------------------------------------------*)

    (*-----------------------------------------------------------------------------------------*)  
    (*   SYSTEM-LEVEL RELIABILITY ANALYSIS QUEBEC - NEW ENGLAND TRANSMISSION  COUPLING SYSTEM  *)
    (*-----------------------------------------------------------------------------------------*)

val HVDC_TYPE_A_COMPLETE_ET_MODEL_DEF = Define
`HVDC_TYPE_A_COMPLETE_ET_MODEL
		   [TR5_S;TR5_F;TR5_PF]
                   [[TR1_S;TR1_F;TR1_PF];[TR2_S;TR2_F;TR2_PF];
		    [TR3_S;TR3_F;TR3_PF];[B1_S;B1_F];[B2_S;B2_F];
		    [TL1_S;TL1_F;TL1_HR;TL1_CR;TL1_FTL];
		    [TL2_S;TL2_F;TL2_HR;TL2_CR;TL2_FTL];
		    [B3_S; B3_F];[B4_S;B4_F];[TR4_S;TR4_F;TR4_PF]] t p =
 ETREE (NODE (EVENT_TREE_LIST
             (⊗Ν𝑳 ([↑ p TR5_S t; ↓ p TR5_F t; ↓ p TR5_PF t])
                   [[↑ p TR1_S t; ↓ p TR1_F t; ↓ p TR1_PF t];
		    [↑ p TR2_S t; ↓ p TR2_F t; ↓ p TR2_PF t];
		    [↑ p TR3_S t; ↓ p TR3_F t; ↓ p TR3_PF t];
		    [↑ p B1_S t; ↓ p B1_F t];
		    [↑ p B2_S t; ↓ p B2_F t];
		    [↑ p TL1_S t; ↓ p TL1_F t; ↓ p TL1_HR t; ↓ p TL1_CR t; ↓ p TL1_FTL t];
		    [↑ p TL2_S t; ↓ p TL2_F t; ↓ p TL2_HR t; ↓ p TL2_CR t; ↓ p TL2_FTL t];
		    [↑ p B3_S t; ↓ p B3_F t];
		    [↑ p B4_S t; ↓ p B4_F t];
		    [↑ p TR4_S t; ↓ p TR4_F t; ↓ p TR4_PF t]])))`;

val HVDC_TYPE_B_COMPLETE_ET_MODEL_DEF = Define
`HVDC_TYPE_B_COMPLETE_ET_MODEL
		   [TR5_S;TR5_F;TR5_PF]
                   [[TR1_S;TR1_F;TR1_PF];[TR2_S;TR2_F;TR2_PF];
		    [TR3_S;TR3_F;TR3_PF];[B1_S;B1_F];[B2_S;B2_F];
		    [TL1_S;TL1_F;TL1_HR;TL1_CR;TL1_FTL];
		    [TL2_S;TL2_F;TL2_HR;TL2_CR;TL2_FTL];
		    [B3_S; B3_F];[B4_S;B4_F];[TR4_S;TR4_F;TR4_PF]] t p =
 ETREE (NODE (EVENT_TREE_LIST
             (⊗Ν𝑳 ([↑ p TR10_S t; ↓ p TR10_F t; ↓ p TR10_PF t])
                   [[↑ p TR1_S t; ↓ p TR1_F t; ↓ p TR1_PF t];
		    [↑ p TR2_S t; ↓ p TR2_F t; ↓ p TR2_PF t];
		    [↑ p TR3_S t; ↓ p TR3_F t; ↓ p TR3_PF t];
		    [↑ p TR4_S t; ↓ p TR4_F t; ↓ p TR4_PF t];
		    [↑ p TR5_S t; ↓ p TR5_F t; ↓ p TR5_PF t];
		    [↑ p TR6_S t; ↓ p TR6_F t; ↓ p TR6_PF t];		    
		    [↑ p B1_S t; ↓ p B1_F t];
		    [↑ p B2_S t; ↓ p B2_F t];
		    [↑ p B3_S t; ↓ p B3_F t];
		    [↑ p B4_S t; ↓ p B4_F t];
		    [↑ p TL1_S t; ↓ p TL1_F t; ↓ p TL1_HR t; ↓ p TL1_CR t; ↓ p TL1_FTL t];
		    [↑ p TL2_S t; ↓ p TL2_F t; ↓ p TL2_HR t; ↓ p TL2_CR t; ↓ p TL2_FTL t];
		    [↑ p B5_S t; ↓ p B5_F t];
		    [↑ p B6_S t; ↓ p B6_F t];
		    [↑ p B7_S t; ↓ p B7_F t];
		    [↑ p B8_S t; ↓ p B8_F t];		    
		    [↑ p TR7_S t; ↓ p TR7_F t; ↓ p TR7_PF t];
		    [↑ p TR8_S t; ↓ p TR8_F t; ↓ p TR8_PF t];
		    [↑ p TR9_S t; ↓ p TR9_F t; ↓ p TR9_PF t]])))`;

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_1345_MW``
``exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_F * t)) * exp (-FR_TR5_S * t)))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * exp (-FR_TR5_S * t)))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * exp (-FR_TR4_S * t))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              ((1 − exp (-FR_B3_F * t)) *
               (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              ((1 − exp (-FR_TL2_F * t)) *
               (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               ((1 − exp (-FR_TL2_HR * t)) *
                (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                ((1 − exp (-FR_TL2_CR * t)) *
                 (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_FTL * t)) *
                  (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (exp (-FR_B1_S * t) *
                (exp (-FR_B2_S * t) *
                 ((1 − exp (-FR_TL1_F * t)) *
                  (exp (-FR_TL2_S * t) *
                   (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  ((1 − exp (-FR_TL1_HR * t)) *
                   (exp (-FR_TL2_S * t) *
                    (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   ((1 − exp (-FR_TL1_CR * t)) *
                    (exp (-FR_TL2_S * t) *
                     (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    ((1 − exp (-FR_TL1_FTL * t)) *
                     (exp (-FR_TL2_S * t) *
                      (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    ((1 − exp (-FR_B2_F * t)) *
                     (exp (-FR_TL1_S * t) *
                      (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    ((1 − exp (-FR_B1_F * t)) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL2_S * t) *
                       (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    ((1 − exp (-FR_TR3_F * t)) *
                     (exp (-FR_B1_S * t) * exp (-FR_TL1_S * t)))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     ((1 − exp (-FR_TR3_F * t)) * (1 − exp (-FR_B1_F * t)))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      ((1 − exp (-FR_TR3_PF * t)) * (1 − exp (-FR_B1_F * t)))) +
                     exp (-FR_TR1_S * t) *
                     ((1 − exp (-FR_TR2_F * t)) * (1 − exp (-FR_TR3_PF * t)))))))))))))))))))))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_2690_MW``
``   exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_F * t)))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              (exp (-FR_B3_S * t) *
               ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_PF * t)))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              (exp (-FR_TL2_S * t) *
               ((1 − exp (-FR_B3_F * t)) *
                (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_F * t)))))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               (exp (-FR_TL2_S * t) *
                ((1 − exp (-FR_B3_F * t)) *
                 (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_PF * t)))))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                (exp (-FR_TL2_S * t) *
                 ((1 − exp (-FR_B3_F * t)) * (1 − exp (-FR_B4_F * t))))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_F * t)) *
                  (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (RELIABILITY p B1 t *
                (RELIABILITY p B2 t *
                 (exp (-FR_TL1_S * t) *
                  ((1 − exp (-FR_TL2_F * t)) *
                   (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  (exp (-FR_TL1_S * t) *
                   ((1 − exp (-FR_TL2_F * t)) * (1 − exp (-FR_B3_F * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   (exp (-FR_TL1_S * t) *
                    ((1 − exp (-FR_TL2_HR * t)) *
                     (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    (exp (-FR_TL1_S * t) *
                     ((1 − exp (-FR_TL2_HR * t)) *
                      (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    (exp (-FR_B2_S * t) *
                     (exp (-FR_TL1_S * t) *
                      ((1 − exp (-FR_TL2_HR * t)) * (1 − exp (-FR_B3_F * t)))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    (exp (-FR_B1_S * t) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL1_S * t) *
                       ((1 − exp (-FR_TL2_CR * t)) *
                        (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    (exp (-FR_TR3_S * t) *
                     (exp (-FR_B1_S * t) *
                      (exp (-FR_B2_S * t) *
                       (exp (-FR_TL1_S * t) *
                        ((1 − exp (-FR_TL2_CR * t)) *
                         (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     (exp (-FR_TR3_S * t) *
                      (exp (-FR_B1_S * t) *
                       (exp (-FR_B2_S * t) *
                        (exp (-FR_TL1_S * t) *
                         ((1 − exp (-FR_TL2_CR * t)) *
                          (1 − exp (-FR_B3_F * t)))))))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      (exp (-FR_TR3_S * t) *
                       (exp (-FR_B1_S * t) *
                        (exp (-FR_B2_S * t) *
                         (exp (-FR_TL1_S * t) *
                          ((1 − exp (-FR_TL2_FTL * t)) *
                           (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                     (exp (-FR_TR1_S * t) *
                      (exp (-FR_TR2_S * t) *
                       (exp (-FR_TR3_S * t) *
                        (exp (-FR_B1_S * t) *
                         (exp (-FR_B2_S * t) *
                          (exp (-FR_TL1_S * t) *
                           ((1 − exp (-FR_TL2_FTL * t)) *
                            (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                      (exp (-FR_TR1_S * t) *
                       (exp (-FR_TR2_S * t) *
                        (exp (-FR_TR3_S * t) *
                         (exp (-FR_B1_S * t) *
                          (exp (-FR_B2_S * t) *
                           (exp (-FR_TL1_S * t) *
                            ((1 − exp (-FR_TL2_FTL * t)) *
                             (1 − exp (-FR_B3_F * t)))))))) +
                       (exp (-FR_TR1_S * t) *
                        (exp (-FR_TR2_S * t) *
                         (exp (-FR_TR3_S * t) *
                          (exp (-FR_B1_S * t) *
                           (exp (-FR_B2_S * t) *
                            ((1 − exp (-FR_TL1_F * t)) *
                             (exp (-FR_TL2_S * t) *
                              (exp (-FR_B4_S * t) *
                               (1 − exp (-FR_TR5_F * t))))))))) +
                        (exp (-FR_TR1_S * t) *
                         (exp (-FR_TR2_S * t) *
                          (exp (-FR_TR3_S * t) *
                           (exp (-FR_B1_S * t) *
                            (exp (-FR_B2_S * t) *
                             ((1 − exp (-FR_TL1_F * t)) *
                              (exp (-FR_TL2_S * t) *
                               (exp (-FR_B4_S * t) *
                                (1 − exp (-FR_TR5_PF * t))))))))) +
                         (exp (-FR_TR1_S * t) *
                          (exp (-FR_TR2_S * t) *
                           (exp (-FR_TR3_S * t) *
                            (exp (-FR_B1_S * t) *
                             (exp (-FR_B2_S * t) *
                              ((1 − exp (-FR_TL1_F * t)) *
                               (exp (-FR_TL2_S * t) *
                                (1 − exp (-FR_B4_F * t)))))))) +
                          (exp (-FR_TR1_S * t) *
                           (exp (-FR_TR2_S * t) *
                            (exp (-FR_TR3_S * t) *
                             (exp (-FR_B1_S * t) *
                              (exp (-FR_B2_S * t) *
                               ((1 − exp (-FR_TL1_F * t)) *
                                (1 − exp (-FR_TL2_F * t))))))) +
                           (exp (-FR_TR1_S * t) *
                            (exp (-FR_TR2_S * t) *
                             (exp (-FR_TR3_S * t) *
                              (exp (-FR_B1_S * t) *
                               (exp (-FR_B2_S * t) *
                                ((1 − exp (-FR_TL1_F * t)) *
                                 (1 − exp (-FR_TL2_HR * t))))))) +
                            (exp (-FR_TR1_S * t) *
                             (exp (-FR_TR2_S * t) *
                              (exp (-FR_TR3_S * t) *
                               (exp (-FR_B1_S * t) *
                                (exp (-FR_B2_S * t) *
                                 ((1 − exp (-FR_TL1_F * t)) *
                                  (1 − exp (-FR_TL2_CR * t))))))) +
                             (exp (-FR_TR1_S * t) *
                              (exp (-FR_TR2_S * t) *
                               (exp (-FR_TR3_S * t) *
                                (exp (-FR_B1_S * t) *
                                 (exp (-FR_B2_S * t) *
                                  ((1 − exp (-FR_TL1_F * t)) *
                                   (1 − exp (-FR_TL2_FTL * t))))))) +
                              (exp (-FR_TR1_S * t) *
                               (exp (-FR_TR2_S * t) *
                                (exp (-FR_TR3_S * t) *
                                 (exp (-FR_B1_S * t) *
                                  (exp (-FR_B2_S * t) *
                                   ((1 − exp (-FR_TL1_HR * t)) *
                                    (exp (-FR_TL2_S * t) *
                                     (exp (-FR_B4_S * t) *
                                      (1 − exp (-FR_TR5_F * t))))))))) +
                               (exp (-FR_TR1_S * t) *
                                (exp (-FR_TR2_S * t) *
                                 (exp (-FR_TR3_S * t) *
                                  (exp (-FR_B1_S * t) *
                                   (exp (-FR_B2_S * t) *
                                    ((1 − exp (-FR_TL1_HR * t)) *
                                     (exp (-FR_TL2_S * t) *
                                      (exp (-FR_B4_S * t) *
                                       (1 − exp (-FR_TR5_PF * t))))))))) +
                                (exp (-FR_TR1_S * t) *
                                 (exp (-FR_TR2_S * t) *
                                  (exp (-FR_TR3_S * t) *
                                   (exp (-FR_B1_S * t) *
                                    (exp (-FR_B2_S * t) *
                                     ((1 − exp (-FR_TL1_HR * t)) *
                                      (exp (-FR_TL2_S * t) *
                                       (1 − exp (-FR_B4_F * t)))))))) +
                                 (exp (-FR_TR1_S * t) *
                                  (exp (-FR_TR2_S * t) *
                                   (exp (-FR_TR3_S * t) *
                                    (exp (-FR_B1_S * t) *
                                     (exp (-FR_B2_S * t) *
                                      ((1 − exp (-FR_TL1_HR * t)) *
                                       (1 − exp (-FR_TL2_F * t))))))) +
                                  (exp (-FR_TR1_S * t) *
                                   (exp (-FR_TR2_S * t) *
                                    (exp (-FR_TR3_S * t) *
                                     (exp (-FR_B1_S * t) *
                                      (exp (-FR_B2_S * t) *
                                       ((1 − exp (-FR_TL1_HR * t)) *
                                        (1 − exp (-FR_TL2_HR * t))))))) +
                                   (exp (-FR_TR1_S * t) *
                                    (exp (-FR_TR2_S * t) *
                                     (exp (-FR_TR3_S * t) *
                                      (exp (-FR_B1_S * t) *
                                       (exp (-FR_B2_S * t) *
                                        ((1 − exp (-FR_TL1_HR * t)) *
                                         (1 − exp (-FR_TL2_CR * t))))))) +
                                    (exp (-FR_TR1_S * t) *
                                     (exp (-FR_TR2_S * t) *
                                      (exp (-FR_TR3_S * t) *
                                       (exp (-FR_B1_S * t) *
                                        (exp (-FR_B2_S * t) *
                                         ((1 − exp (-FR_TL1_HR * t)) *
                                          (1 − exp (-FR_TL2_FTL * t))))))) +
                                     (exp (-FR_TR1_S * t) *
                                      (exp (-FR_TR2_S * t) *
                                       (exp (-FR_TR3_S * t) *
                                        (exp (-FR_B1_S * t) *
                                         (exp (-FR_B2_S * t) *
                                          ((1 − exp (-FR_TL1_CR * t)) *
                                           (exp (-FR_TL2_S * t) *
                                            (exp (-FR_B4_S * t) *
                                             (1 − exp (-FR_TR5_F * t))))))))) +
                                      (exp (-FR_TR1_S * t) *
                                       (exp (-FR_TR2_S * t) *
                                        (exp (-FR_TR3_S * t) *
                                         (exp (-FR_B1_S * t) *
                                          (exp (-FR_B2_S * t) *
                                           ((1 − exp (-FR_TL1_CR * t)) *
                                            (exp (-FR_TL2_S * t) *
                                             (exp (-FR_B4_S * t) *
                                              (1 − exp (-FR_TR5_PF * t))))))))) +
                                       (exp (-FR_TR1_S * t) *
                                        (exp (-FR_TR2_S * t) *
                                         (exp (-FR_TR3_S * t) *
                                          (exp (-FR_B1_S * t) *
                                           (exp (-FR_B2_S * t) *
                                            ((1 − exp (-FR_TL1_CR * t)) *
                                             (exp (-FR_TL2_S * t) *
                                              (1 − exp (-FR_B4_F * t)))))))) +
                                        (exp (-FR_TR1_S * t) *
                                         (exp (-FR_TR2_S * t) *
                                          (exp (-FR_TR3_S * t) *
                                           (exp (-FR_B1_S * t) *
                                            (exp (-FR_B2_S * t) *
                                             ((1 − exp (-FR_TL1_CR * t)) *
                                              (1 − exp (-FR_TL2_F * t))))))) +
                                         (exp (-FR_TR1_S * t) *
                                          (exp (-FR_TR2_S * t) *
                                           (exp (-FR_TR3_S * t) *
                                            (exp (-FR_B1_S * t) *
                                             (exp (-FR_B2_S * t) *
                                              ((1 − exp (-FR_TL1_CR * t)) *
                                               (1 − exp (-FR_TL2_HR * t))))))) +
                                          (exp (-FR_TR1_S * t) *
                                           (exp (-FR_TR2_S * t) *
                                            (exp (-FR_TR3_S * t) *
                                             (exp (-FR_B1_S * t) *
                                              (exp (-FR_B2_S * t) *
                                               ((1 − exp (-FR_TL1_CR * t)) *
                                                (1 − exp (-FR_TL2_CR * t))))))) +
                                           (exp (-FR_TR1_S * t) *
                                            (exp (-FR_TR2_S * t) *
                                             (exp (-FR_TR3_S * t) *
                                              (exp (-FR_B1_S * t) *
                                               (exp (-FR_B2_S * t) *
                                                ((1 − exp (-FR_TL1_CR * t)) *
                                                 (1 − exp (-FR_TL2_FTL * t))))))) +
                                            (exp (-FR_TR1_S * t) *
                                             (exp (-FR_TR2_S * t) *
                                              (exp (-FR_TR3_S * t) *
                                               (exp (-FR_B1_S * t) *
                                                (exp (-FR_B2_S * t) *
                                                 ((1 − exp (-FR_TL1_FTL * t)) *
                                                  (exp (-FR_TL2_S * t) *
                                                   (exp (-FR_B4_S * t) *
                                                    (1 − exp (-FR_TR5_F * t))))))))) +
                                             (exp (-FR_TR1_S * t) *
                                              (exp (-FR_TR2_S * t) *
                                               (exp (-FR_TR3_S * t) *
                                                (exp (-FR_B1_S * t) *
                                                 (exp (-FR_B2_S * t) *
                                                  ((1 − exp (-FR_TL1_FTL * t)) *
                                                   (exp (-FR_TL2_S * t) *
                                                    (exp (-FR_B4_S * t) *
                                                     (1 −
                                                      exp (-FR_TR5_PF * t))))))))) +
                                              (exp (-FR_TR1_S * t) *
                                               (exp (-FR_TR2_S * t) *
                                                (exp (-FR_TR3_S * t) *
                                                 (exp (-FR_B1_S * t) *
                                                  (exp (-FR_B2_S * t) *
                                                   ((1 −
                                                     exp (-FR_TL1_FTL * t)) *
                                                    (exp (-FR_TL2_S * t) *
                                                     (1 − exp (-FR_B4_F * t)))))))) +
                                               (exp (-FR_TR1_S * t) *
                                                (exp (-FR_TR2_S * t) *
                                                 (exp (-FR_TR3_S * t) *
                                                  (exp (-FR_B1_S * t) *
                                                   (exp (-FR_B2_S * t) *
                                                    ((1 −
                                                      exp (-FR_TL1_FTL * t)) *
                                                     (1 − exp (-FR_TL2_F * t))))))) +
                                                (exp (-FR_TR1_S * t) *
                                                 (exp (-FR_TR2_S * t) *
                                                  (exp (-FR_TR3_S * t) *
                                                   (exp (-FR_B1_S * t) *
                                                    (exp (-FR_B2_S * t) *
                                                     ((1 −
                                                       exp (-FR_TL1_FTL * t)) *
                                                      (1 −
                                                       exp (-FR_TL2_HR * t))))))) +
                                                 (exp (-FR_TR1_S * t) *
                                                  (exp (-FR_TR2_S * t) *
                                                   (exp (-FR_TR3_S * t) *
                                                    (exp (-FR_B1_S * t) *
                                                     (exp (-FR_B2_S * t) *
                                                      ((1 −
                                                        exp (-FR_TL1_FTL * t)) *
                                                       (1 −
                                                        exp (-FR_TL2_CR * t))))))) +
                                                  (exp (-FR_TR1_S * t) *
                                                   (exp (-FR_TR2_S * t) *
                                                    (exp (-FR_TR3_S * t) *
                                                     (exp (-FR_B1_S * t) *
                                                      (exp (-FR_B2_S * t) *
                                                       ((1 −
                                                         exp
                                                           (-FR_TL1_FTL * t)) *
                                                        (1 −
                                                         exp
                                                           (-FR_TL2_FTL * t))))))) +
                                                   (exp (-FR_TR1_S * t) *
                                                    (exp (-FR_TR2_S * t) *
                                                     (exp (-FR_TR3_S * t) *
                                                      (exp (-FR_B1_S * t) *
                                                       ((1 −
                                                         exp (-FR_B2_F * t)) *
                                                        (exp (-FR_TL1_S * t) *
                                                         (exp (-FR_B3_S * t) *
                                                          (1 −
                                                           exp
                                                             (-FR_TR4_F * t)))))))) +
                                                    (exp (-FR_TR1_S * t) *
                                                     (exp (-FR_TR2_S * t) *
                                                      (exp (-FR_TR3_S * t) *
                                                       (exp (-FR_B1_S * t) *
                                                        ((1 −
                                                          exp (-FR_B2_F * t)) *
                                                         (exp (-FR_TL1_S * t) *
                                                          (exp (-FR_B3_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_TR4_PF * t)))))))) +
                                                     (exp (-FR_TR1_S * t) *
                                                      (exp (-FR_TR2_S * t) *
                                                       (exp (-FR_TR3_S * t) *
                                                        (exp (-FR_B1_S * t) *
                                                         ((1 −
                                                           exp (-FR_B2_F * t)) *
                                                          (exp
                                                             (-FR_TL1_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_B3_F * t))))))) +
                                                      (exp (-FR_TR1_S * t) *
                                                       (exp (-FR_TR2_S * t) *
                                                        (exp (-FR_TR3_S * t) *
                                                         (exp (-FR_B1_S * t) *
                                                          ((1 −
                                                            exp
                                                              (-FR_B2_F * t)) *
                                                           (1 −
                                                            exp
                                                              (-FR_TL1_F * t)))))) +
                                                       (exp (-FR_TR1_S * t) *
                                                        (exp (-FR_TR2_S * t) *
                                                         (exp (-FR_TR3_S * t) *
                                                          (exp (-FR_B1_S * t) *
                                                           ((1 −
                                                             exp
                                                               (-FR_B2_F * t)) *
                                                            (1 −
                                                             exp
                                                               (-FR_TL1_HR *
                                                                t)))))) +
                                                        (exp (-FR_TR1_S * t) *
                                                         (exp (-FR_TR2_S * t) *
                                                          (exp
                                                             (-FR_TR3_S * t) *
                                                           (exp
                                                              (-FR_B1_S * t) *
                                                            ((1 −
                                                              exp
                                                                (-FR_B2_F * t)) *
                                                             (1 −
                                                              exp
                                                                (-FR_TL1_CR *
                                                                 t)))))) +
                                                         (exp (-FR_TR1_S * t) *
                                                          (exp
                                                             (-FR_TR2_S * t) *
                                                           (exp
                                                              (-FR_TR3_S * t) *
                                                            (exp
                                                               (-FR_B1_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B2_F *
                                                                  t)) *
                                                              (1 −
                                                               exp
                                                                 (-FR_TL1_FTL *
                                                                  t)))))) +
                                                          (exp
                                                             (-FR_TR1_S * t) *
                                                           (exp
                                                              (-FR_TR2_S * t) *
                                                            (exp
                                                               (-FR_TR3_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B1_F *
                                                                  t)) *
                                                              (exp
                                                                 (-FR_B2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TL2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_B4_S *
                                                                    t) *
                                                                 (1 −
                                                                  exp
                                                                    (-FR_TR5_F *
                                                                     t)))))))) +
                                                           (exp
                                                              (-FR_TR1_S * t) *
                                                            (exp
                                                               (-FR_TR2_S * t) *
                                                             (exp
                                                                (-FR_TR3_S *
                                                                 t) *
                                                              ((1 −
                                                                exp
                                                                  (-FR_B1_F *
                                                                   t)) *
                                                               (exp
                                                                  (-FR_B2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TL2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_B4_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TR5_PF *
                                                                      t)))))))) +
                                                            (exp
                                                               (-FR_TR1_S * t) *
                                                             (exp
                                                                (-FR_TR2_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR3_S *
                                                                  t) *
                                                               ((1 −
                                                                 exp
                                                                   (-FR_B1_F *
                                                                    t)) *
                                                                (exp
                                                                   (-FR_B2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TL2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_B4_F *
                                                                      t))))))) +
                                                             (exp
                                                                (-FR_TR1_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR3_S *
                                                                   t) *
                                                                ((1 −
                                                                  exp
                                                                    (-FR_B1_F *
                                                                     t)) *
                                                                 (exp
                                                                    (-FR_B2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TL2_F *
                                                                      t)))))) +
                                                              (exp
                                                                 (-FR_TR1_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR3_S *
                                                                    t) *
                                                                 ((1 −
                                                                   exp
                                                                     (-FR_B1_F *
                                                                      t)) *
                                                                  (exp
                                                                     (-FR_B2_S *
                                                                      t) *
                                                                   (1 −
                                                                    exp
                                                                      (-FR_TL2_HR *
                                                                       t)))))) +
                                                               (exp
                                                                  (-FR_TR1_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR3_S *
                                                                     t) *
                                                                  ((1 −
                                                                    exp
                                                                      (-FR_B1_F *
                                                                       t)) *
                                                                   (exp
                                                                      (-FR_B2_S *
                                                                       t) *
                                                                    (1 −
                                                                     exp
                                                                       (-FR_TL2_CR *
                                                                        t)))))) +
                                                                (exp
                                                                   (-FR_TR1_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR2_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR3_S *
                                                                      t) *
                                                                   ((1 −
                                                                     exp
                                                                       (-FR_B1_F *
                                                                        t)) *
                                                                    (exp
                                                                       (-FR_B2_S *
                                                                        t) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_TL2_FTL *
                                                                         t)))))) +
                                                                 (exp
                                                                    (-FR_TR1_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR2_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR3_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_B1_F *
                                                                         t)) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_B2_F *
                                                                         t))))) +
                                                                  (exp
                                                                     (-FR_TR1_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR2_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_TR3_F *
                                                                         t)) *
                                                                     (exp
                                                                        (-FR_B1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TL1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_B3_S *
                                                                           t) *
                                                                        (1 −
                                                                         exp
                                                                           (-FR_TR4_F *
                                                                            t))))))) +
                                                                   (exp
                                                                      (-FR_TR1_S *
                                                                       t) *
                                                                    (exp
                                                                       (-FR_TR2_S *
                                                                        t) *
                                                                     ((1 −
                                                                       exp
                                                                         (-FR_TR3_F *
                                                                          t)) *
                                                                      (exp
                                                                         (-FR_B1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TL1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_B3_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TR4_PF *
                                                                             t))))))) +
                                                                    (exp
                                                                       (-FR_TR1_S *
                                                                        t) *
                                                                     (exp
                                                                        (-FR_TR2_S *
                                                                         t) *
                                                                      ((1 −
                                                                        exp
                                                                          (-FR_TR3_F *
                                                                           t)) *
                                                                       (exp
                                                                          (-FR_B1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TL1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_B3_F *
                                                                             t)))))) +
                                                                     (exp
                                                                        (-FR_TR1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TR2_S *
                                                                          t) *
                                                                       ((1 −
                                                                         exp
                                                                           (-FR_TR3_F *
                                                                            t)) *
                                                                        (exp
                                                                           (-FR_B1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TL1_F *
                                                                             t))))) +
                                                                      (exp
                                                                         (-FR_TR1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TR2_S *
                                                                           t) *
                                                                        ((1 −
                                                                          exp
                                                                            (-FR_TR3_F *
                                                                             t)) *
                                                                         (exp
                                                                            (-FR_B1_S *
                                                                             t) *
                                                                          (1 −
                                                                           exp
                                                                             (-FR_TL1_HR *
                                                                              t))))) +
                                                                       (exp
                                                                          (-FR_TR1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TR2_S *
                                                                            t) *
                                                                         ((1 −
                                                                           exp
                                                                             (-FR_TR3_F *
                                                                              t)) *
                                                                          (exp
                                                                             (-FR_B1_S *
                                                                              t) *
                                                                           (1 −
                                                                            exp
                                                                              (-FR_TL1_CR *
                                                                               t))))) +
                                                                        (exp
                                                                           (-FR_TR1_S *
                                                                            t) *
                                                                         (exp
                                                                            (-FR_TR2_S *
                                                                             t) *
                                                                          ((1 −
                                                                            exp
                                                                              (-FR_TR3_F *
                                                                               t)) *
                                                                           (exp
                                                                              (-FR_B1_S *
                                                                               t) *
                                                                            (1 −
                                                                             exp
                                                                               (-FR_TL1_FTL *
                                                                                t))))) +
                                                                         (exp
                                                                            (-FR_TR1_S *
                                                                             t) *
                                                                          (exp
                                                                             (-FR_TR2_S *
                                                                              t) *
                                                                           ((1 −
                                                                             exp
                                                                               (-FR_TR3_PF *
                                                                                t)) *
                                                                            (exp
                                                                               (-FR_B1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TL1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_B3_S *
                                                                                  t) *
                                                                               exp
                                                                                 (-FR_TR4_S *
                                                                                  t)))))) +
                                                                          (exp
                                                                             (-FR_TR1_S *
                                                                              t) *
                                                                           (exp
                                                                              (-FR_TR2_S *
                                                                               t) *
                                                                            ((1 −
                                                                              exp
                                                                                (-FR_TR3_PF *
                                                                                 t)) *
                                                                             (exp
                                                                                (-FR_B1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TL1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_B3_S *
                                                                                   t) *
                                                                                (1 −
                                                                                 exp
                                                                                   (-FR_TR4_F *
                                                                                    t))))))) +
                                                                           (exp
                                                                              (-FR_TR1_S *
                                                                               t) *
                                                                            (exp
                                                                               (-FR_TR2_S *
                                                                                t) *
                                                                             ((1 −
                                                                               exp
                                                                                 (-FR_TR3_PF *
                                                                                  t)) *
                                                                              (exp
                                                                                 (-FR_B1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TL1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_B3_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TR4_PF *
                                                                                     t))))))) +
                                                                            (exp
                                                                               (-FR_TR1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TR2_S *
                                                                                 t) *
                                                                              ((1 −
                                                                                exp
                                                                                  (-FR_TR3_PF *
                                                                                   t)) *
                                                                               (exp
                                                                                  (-FR_B1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TL1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_B3_F *
                                                                                     t)))))) +
                                                                             (exp
                                                                                (-FR_TR1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TR2_S *
                                                                                  t) *
                                                                               ((1 −
                                                                                 exp
                                                                                   (-FR_TR3_PF *
                                                                                    t)) *
                                                                                (exp
                                                                                   (-FR_B1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TL1_F *
                                                                                     t))))) +
                                                                              (exp
                                                                                 (-FR_TR1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TR2_S *
                                                                                   t) *
                                                                                ((1 −
                                                                                  exp
                                                                                    (-FR_TR3_PF *
                                                                                     t)) *
                                                                                 (exp
                                                                                    (-FR_B1_S *
                                                                                     t) *
                                                                                  (1 −
                                                                                   exp
                                                                                     (-FR_TL1_HR *
                                                                                      t))))) +
                                                                               (exp
                                                                                  (-FR_TR1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TR2_S *
                                                                                    t) *
                                                                                 ((1 −
                                                                                   exp
                                                                                     (-FR_TR3_PF *
                                                                                      t)) *
                                                                                  (exp
                                                                                     (-FR_B1_S *
                                                                                      t) *
                                                                                   (1 −
                                                                                    exp
                                                                                      (-FR_TL1_CR *
                                                                                       t))))) +
                                                                                (exp
                                                                                   (-FR_TR1_S *
                                                                                    t) *
                                                                                 (exp
                                                                                    (-FR_TR2_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR3_PF *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_B1_S *
                                                                                       t) *
                                                                                    (1 −
                                                                                     exp
                                                                                       (-FR_TL1_FTL *
                                                                                        t))))) +
                                                                                 (exp
                                                                                    (-FR_TR1_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR2_F *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_TR3_S *
                                                                                       t) *
                                                                                    (exp
                                                                                       (-FR_B2_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_TL2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B4_S *
                                                                                          t) *
                                                                                       exp
                                                                                         (-FR_TR5_S *
                                                                                          t)))))) +
                                                                                  (exp
                                                                                     (-FR_TR1_S *
                                                                                      t) *
                                                                                   ((1 −
                                                                                     exp
                                                                                       (-FR_TR2_F *
                                                                                        t)) *
                                                                                    (exp
                                                                                       (-FR_TR3_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_B2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_TL2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B4_S *
                                                                                           t) *
                                                                                        (1 −
                                                                                         exp
                                                                                           (-FR_TR5_F *
                                                                                            t))))))) +
                                                                                   (exp
                                                                                      (-FR_TR1_S *
                                                                                       t) *
                                                                                    ((1 −
                                                                                      exp
                                                                                        (-FR_TR2_F *
                                                                                         t)) *
                                                                                     (exp
                                                                                        (-FR_TR3_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_TL2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B4_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TR5_PF *
                                                                                             t))))))) +
                                                                                    (exp
                                                                                       (-FR_TR1_S *
                                                                                        t) *
                                                                                     ((1 −
                                                                                       exp
                                                                                         (-FR_TR2_F *
                                                                                          t)) *
                                                                                      (exp
                                                                                         (-FR_TR3_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_TL2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_B4_F *
                                                                                             t)))))) +
                                                                                     (exp
                                                                                        (-FR_TR1_S *
                                                                                         t) *
                                                                                      ((1 −
                                                                                        exp
                                                                                          (-FR_TR2_F *
                                                                                           t)) *
                                                                                       (exp
                                                                                          (-FR_TR3_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TL2_F *
                                                                                             t))))) +
                                                                                      (exp
                                                                                         (-FR_TR1_S *
                                                                                          t) *
                                                                                       ((1 −
                                                                                         exp
                                                                                           (-FR_TR2_F *
                                                                                            t)) *
                                                                                        (exp
                                                                                           (-FR_TR3_S *
                                                                                            t) *
                                                                                         (exp
                                                                                            (-FR_B2_S *
                                                                                             t) *
                                                                                          (1 −
                                                                                           exp
                                                                                             (-FR_TL2_HR *
                                                                                              t))))) +
                                                                                       (exp
                                                                                          (-FR_TR1_S *
                                                                                           t) *
                                                                                        ((1 −
                                                                                          exp
                                                                                            (-FR_TR2_F *
                                                                                             t)) *
                                                                                         (exp
                                                                                            (-FR_TR3_S *
                                                                                             t) *
                                                                                          (exp
                                                                                             (-FR_B2_S *
                                                                                              t) *
                                                                                           (1 −
                                                                                            exp
                                                                                              (-FR_TL2_CR *
                                                                                               t))))) +
                                                                                        (exp
                                                                                           (-FR_TR1_S *
                                                                                            t) *
                                                                                         ((1 −
                                                                                           exp
                                                                                             (-FR_TR2_F *
                                                                                              t)) *
                                                                                          (exp
                                                                                             (-FR_TR3_S *
                                                                                              t) *
                                                                                           (exp
                                                                                              (-FR_B2_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TL2_FTL *
                                                                                                t))))) +
                                                                                         (exp
                                                                                            (-FR_TR1_S *
                                                                                             t) *
                                                                                          ((1 −
                                                                                            exp
                                                                                              (-FR_TR2_F *
                                                                                               t)) *
                                                                                           (exp
                                                                                              (-FR_TR3_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_B2_F *
                                                                                                t)))) +
                                                                                          (exp
                                                                                             (-FR_TR1_S *
                                                                                              t) *
                                                                                           ((1 −
                                                                                             exp
                                                                                               (-FR_TR2_F *
                                                                                                t)) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TR3_F *
                                                                                                t))) +
                                                                                           (exp
                                                                                              (-FR_TR1_S *
                                                                                               t) *
                                                                                            ((1 −
                                                                                              exp
                                                                                                (-FR_TR2_PF *
                                                                                                 t)) *
                                                                                             (exp
                                                                                                (-FR_TR3_S *
                                                                                                 t) *
                                                                                              (exp
                                                                                                 (-FR_B2_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_TL2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B4_S *
                                                                                                    t) *
                                                                                                 exp
                                                                                                   (-FR_TR5_S *
                                                                                                    t)))))) +
                                                                                            (exp
                                                                                               (-FR_TR1_S *
                                                                                                t) *
                                                                                             ((1 −
                                                                                               exp
                                                                                                 (-FR_TR2_PF *
                                                                                                  t)) *
                                                                                              (exp
                                                                                                 (-FR_TR3_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_B2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_TL2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B4_S *
                                                                                                     t) *
                                                                                                  (1 −
                                                                                                   exp
                                                                                                     (-FR_TR5_F *
                                                                                                      t))))))) +
                                                                                             (exp
                                                                                                (-FR_TR1_S *
                                                                                                 t) *
                                                                                              ((1 −
                                                                                                exp
                                                                                                  (-FR_TR2_PF *
                                                                                                   t)) *
                                                                                               (exp
                                                                                                  (-FR_TR3_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_TL2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B4_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TR5_PF *
                                                                                                       t))))))) +
                                                                                              (exp
                                                                                                 (-FR_TR1_S *
                                                                                                  t) *
                                                                                               ((1 −
                                                                                                 exp
                                                                                                   (-FR_TR2_PF *
                                                                                                    t)) *
                                                                                                (exp
                                                                                                   (-FR_TR3_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_TL2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_B4_F *
                                                                                                       t)))))) +
                                                                                               (exp
                                                                                                  (-FR_TR1_S *
                                                                                                   t) *
                                                                                                ((1 −
                                                                                                  exp
                                                                                                    (-FR_TR2_PF *
                                                                                                     t)) *
                                                                                                 (exp
                                                                                                    (-FR_TR3_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TL2_F *
                                                                                                       t))))) +
                                                                                                (exp
                                                                                                   (-FR_TR1_S *
                                                                                                    t) *
                                                                                                 ((1 −
                                                                                                   exp
                                                                                                     (-FR_TR2_PF *
                                                                                                      t)) *
                                                                                                  (exp
                                                                                                     (-FR_TR3_S *
                                                                                                      t) *
                                                                                                   (exp
                                                                                                      (-FR_B2_S *
                                                                                                       t) *
                                                                                                    (1 −
                                                                                                     exp
                                                                                                       (-FR_TL2_HR *
                                                                                                        t))))) +
                                                                                                 (exp
                                                                                                    (-FR_TR1_S *
                                                                                                     t) *
                                                                                                  ((1 −
                                                                                                    exp
                                                                                                      (-FR_TR2_PF *
                                                                                                       t)) *
                                                                                                   (exp
                                                                                                      (-FR_TR3_S *
                                                                                                       t) *
                                                                                                    (exp
                                                                                                       (-FR_B2_S *
                                                                                                        t) *
                                                                                                     (1 −
                                                                                                      exp
                                                                                                        (-FR_TL2_CR *
                                                                                                         t))))) +
                                                                                                  (exp
                                                                                                     (-FR_TR1_S *
                                                                                                      t) *
                                                                                                   ((1 −
                                                                                                     exp
                                                                                                       (-FR_TR2_PF *
                                                                                                        t)) *
                                                                                                    (exp
                                                                                                       (-FR_TR3_S *
                                                                                                        t) *
                                                                                                     (exp
                                                                                                        (-FR_B2_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TL2_FTL *
                                                                                                          t))))) +
                                                                                                   (exp
                                                                                                      (-FR_TR1_S *
                                                                                                       t) *
                                                                                                    ((1 −
                                                                                                      exp
                                                                                                        (-FR_TR2_PF *
                                                                                                         t)) *
                                                                                                     (exp
                                                                                                        (-FR_TR3_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_B2_F *
                                                                                                          t)))) +
                                                                                                    (exp
                                                                                                       (-FR_TR1_S *
                                                                                                        t) *
                                                                                                     ((1 −
                                                                                                       exp
                                                                                                         (-FR_TR2_PF *
                                                                                                          t)) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR3_F *
                                                                                                          t))) +
                                                                                                     (exp
                                                                                                        (-FR_TR1_S *
                                                                                                         t) *
                                                                                                      ((1 −
                                                                                                        exp
                                                                                                          (-FR_TR2_PF *
                                                                                                           t)) *
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR3_PF *
                                                                                                           t))) +
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR1_F *
                                                                                                          t) +
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR1_PF *
                                                                                                           t))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))``;

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``ASUI``
``(exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_F * t)) * exp (-FR_TR5_S * t)))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * exp (-FR_TR5_S * t)))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * exp (-FR_TR4_S * t))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              ((1 − exp (-FR_B3_F * t)) *
               (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              ((1 − exp (-FR_TL2_F * t)) *
               (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               ((1 − exp (-FR_TL2_HR * t)) *
                (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                ((1 − exp (-FR_TL2_CR * t)) *
                 (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_FTL * t)) *
                  (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (exp (-FR_B1_S * t) *
                (exp (-FR_B2_S * t) *
                 ((1 − exp (-FR_TL1_F * t)) *
                  (exp (-FR_TL2_S * t) *
                   (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  ((1 − exp (-FR_TL1_HR * t)) *
                   (exp (-FR_TL2_S * t) *
                    (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   ((1 − exp (-FR_TL1_CR * t)) *
                    (exp (-FR_TL2_S * t) *
                     (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    ((1 − exp (-FR_TL1_FTL * t)) *
                     (exp (-FR_TL2_S * t) *
                      (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    ((1 − exp (-FR_B2_F * t)) *
                     (exp (-FR_TL1_S * t) *
                      (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    ((1 − exp (-FR_B1_F * t)) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL2_S * t) *
                       (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    ((1 − exp (-FR_TR3_F * t)) *
                     (exp (-FR_B1_S * t) * exp (-FR_TL1_S * t)))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     ((1 − exp (-FR_TR3_F * t)) * (1 − exp (-FR_B1_F * t)))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      ((1 − exp (-FR_TR3_PF * t)) * (1 − exp (-FR_B1_F * t)))) +
                     exp (-FR_TR1_S * t) *
                     ((1 − exp (-FR_TR2_F * t)) * (1 − exp (-FR_TR3_PF * t)))))))))))))))))))) * 40 * 55,000 +
  exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_F * t)))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              (exp (-FR_B3_S * t) *
               ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_PF * t)))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              (exp (-FR_TL2_S * t) *
               ((1 − exp (-FR_B3_F * t)) *
                (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_F * t)))))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               (exp (-FR_TL2_S * t) *
                ((1 − exp (-FR_B3_F * t)) *
                 (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_PF * t)))))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                (exp (-FR_TL2_S * t) *
                 ((1 − exp (-FR_B3_F * t)) * (1 − exp (-FR_B4_F * t))))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_F * t)) *
                  (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (RELIABILITY p B1 t *
                (RELIABILITY p B2 t *
                 (exp (-FR_TL1_S * t) *
                  ((1 − exp (-FR_TL2_F * t)) *
                   (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  (exp (-FR_TL1_S * t) *
                   ((1 − exp (-FR_TL2_F * t)) * (1 − exp (-FR_B3_F * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   (exp (-FR_TL1_S * t) *
                    ((1 − exp (-FR_TL2_HR * t)) *
                     (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    (exp (-FR_TL1_S * t) *
                     ((1 − exp (-FR_TL2_HR * t)) *
                      (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    (exp (-FR_B2_S * t) *
                     (exp (-FR_TL1_S * t) *
                      ((1 − exp (-FR_TL2_HR * t)) * (1 − exp (-FR_B3_F * t)))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    (exp (-FR_B1_S * t) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL1_S * t) *
                       ((1 − exp (-FR_TL2_CR * t)) *
                        (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    (exp (-FR_TR3_S * t) *
                     (exp (-FR_B1_S * t) *
                      (exp (-FR_B2_S * t) *
                       (exp (-FR_TL1_S * t) *
                        ((1 − exp (-FR_TL2_CR * t)) *
                         (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     (exp (-FR_TR3_S * t) *
                      (exp (-FR_B1_S * t) *
                       (exp (-FR_B2_S * t) *
                        (exp (-FR_TL1_S * t) *
                         ((1 − exp (-FR_TL2_CR * t)) *
                          (1 − exp (-FR_B3_F * t)))))))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      (exp (-FR_TR3_S * t) *
                       (exp (-FR_B1_S * t) *
                        (exp (-FR_B2_S * t) *
                         (exp (-FR_TL1_S * t) *
                          ((1 − exp (-FR_TL2_FTL * t)) *
                           (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                     (exp (-FR_TR1_S * t) *
                      (exp (-FR_TR2_S * t) *
                       (exp (-FR_TR3_S * t) *
                        (exp (-FR_B1_S * t) *
                         (exp (-FR_B2_S * t) *
                          (exp (-FR_TL1_S * t) *
                           ((1 − exp (-FR_TL2_FTL * t)) *
                            (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                      (exp (-FR_TR1_S * t) *
                       (exp (-FR_TR2_S * t) *
                        (exp (-FR_TR3_S * t) *
                         (exp (-FR_B1_S * t) *
                          (exp (-FR_B2_S * t) *
                           (exp (-FR_TL1_S * t) *
                            ((1 − exp (-FR_TL2_FTL * t)) *
                             (1 − exp (-FR_B3_F * t)))))))) +
                       (exp (-FR_TR1_S * t) *
                        (exp (-FR_TR2_S * t) *
                         (exp (-FR_TR3_S * t) *
                          (exp (-FR_B1_S * t) *
                           (exp (-FR_B2_S * t) *
                            ((1 − exp (-FR_TL1_F * t)) *
                             (exp (-FR_TL2_S * t) *
                              (exp (-FR_B4_S * t) *
                               (1 − exp (-FR_TR5_F * t))))))))) +
                        (exp (-FR_TR1_S * t) *
                         (exp (-FR_TR2_S * t) *
                          (exp (-FR_TR3_S * t) *
                           (exp (-FR_B1_S * t) *
                            (exp (-FR_B2_S * t) *
                             ((1 − exp (-FR_TL1_F * t)) *
                              (exp (-FR_TL2_S * t) *
                               (exp (-FR_B4_S * t) *
                                (1 − exp (-FR_TR5_PF * t))))))))) +
                         (exp (-FR_TR1_S * t) *
                          (exp (-FR_TR2_S * t) *
                           (exp (-FR_TR3_S * t) *
                            (exp (-FR_B1_S * t) *
                             (exp (-FR_B2_S * t) *
                              ((1 − exp (-FR_TL1_F * t)) *
                               (exp (-FR_TL2_S * t) *
                                (1 − exp (-FR_B4_F * t)))))))) +
                          (exp (-FR_TR1_S * t) *
                           (exp (-FR_TR2_S * t) *
                            (exp (-FR_TR3_S * t) *
                             (exp (-FR_B1_S * t) *
                              (exp (-FR_B2_S * t) *
                               ((1 − exp (-FR_TL1_F * t)) *
                                (1 − exp (-FR_TL2_F * t))))))) +
                           (exp (-FR_TR1_S * t) *
                            (exp (-FR_TR2_S * t) *
                             (exp (-FR_TR3_S * t) *
                              (exp (-FR_B1_S * t) *
                               (exp (-FR_B2_S * t) *
                                ((1 − exp (-FR_TL1_F * t)) *
                                 (1 − exp (-FR_TL2_HR * t))))))) +
                            (exp (-FR_TR1_S * t) *
                             (exp (-FR_TR2_S * t) *
                              (exp (-FR_TR3_S * t) *
                               (exp (-FR_B1_S * t) *
                                (exp (-FR_B2_S * t) *
                                 ((1 − exp (-FR_TL1_F * t)) *
                                  (1 − exp (-FR_TL2_CR * t))))))) +
                             (exp (-FR_TR1_S * t) *
                              (exp (-FR_TR2_S * t) *
                               (exp (-FR_TR3_S * t) *
                                (exp (-FR_B1_S * t) *
                                 (exp (-FR_B2_S * t) *
                                  ((1 − exp (-FR_TL1_F * t)) *
                                   (1 − exp (-FR_TL2_FTL * t))))))) +
                              (exp (-FR_TR1_S * t) *
                               (exp (-FR_TR2_S * t) *
                                (exp (-FR_TR3_S * t) *
                                 (exp (-FR_B1_S * t) *
                                  (exp (-FR_B2_S * t) *
                                   ((1 − exp (-FR_TL1_HR * t)) *
                                    (exp (-FR_TL2_S * t) *
                                     (exp (-FR_B4_S * t) *
                                      (1 − exp (-FR_TR5_F * t))))))))) +
                               (exp (-FR_TR1_S * t) *
                                (exp (-FR_TR2_S * t) *
                                 (exp (-FR_TR3_S * t) *
                                  (exp (-FR_B1_S * t) *
                                   (exp (-FR_B2_S * t) *
                                    ((1 − exp (-FR_TL1_HR * t)) *
                                     (exp (-FR_TL2_S * t) *
                                      (exp (-FR_B4_S * t) *
                                       (1 − exp (-FR_TR5_PF * t))))))))) +
                                (exp (-FR_TR1_S * t) *
                                 (exp (-FR_TR2_S * t) *
                                  (exp (-FR_TR3_S * t) *
                                   (exp (-FR_B1_S * t) *
                                    (exp (-FR_B2_S * t) *
                                     ((1 − exp (-FR_TL1_HR * t)) *
                                      (exp (-FR_TL2_S * t) *
                                       (1 − exp (-FR_B4_F * t)))))))) +
                                 (exp (-FR_TR1_S * t) *
                                  (exp (-FR_TR2_S * t) *
                                   (exp (-FR_TR3_S * t) *
                                    (exp (-FR_B1_S * t) *
                                     (exp (-FR_B2_S * t) *
                                      ((1 − exp (-FR_TL1_HR * t)) *
                                       (1 − exp (-FR_TL2_F * t))))))) +
                                  (exp (-FR_TR1_S * t) *
                                   (exp (-FR_TR2_S * t) *
                                    (exp (-FR_TR3_S * t) *
                                     (exp (-FR_B1_S * t) *
                                      (exp (-FR_B2_S * t) *
                                       ((1 − exp (-FR_TL1_HR * t)) *
                                        (1 − exp (-FR_TL2_HR * t))))))) +
                                   (exp (-FR_TR1_S * t) *
                                    (exp (-FR_TR2_S * t) *
                                     (exp (-FR_TR3_S * t) *
                                      (exp (-FR_B1_S * t) *
                                       (exp (-FR_B2_S * t) *
                                        ((1 − exp (-FR_TL1_HR * t)) *
                                         (1 − exp (-FR_TL2_CR * t))))))) +
                                    (exp (-FR_TR1_S * t) *
                                     (exp (-FR_TR2_S * t) *
                                      (exp (-FR_TR3_S * t) *
                                       (exp (-FR_B1_S * t) *
                                        (exp (-FR_B2_S * t) *
                                         ((1 − exp (-FR_TL1_HR * t)) *
                                          (1 − exp (-FR_TL2_FTL * t))))))) +
                                     (exp (-FR_TR1_S * t) *
                                      (exp (-FR_TR2_S * t) *
                                       (exp (-FR_TR3_S * t) *
                                        (exp (-FR_B1_S * t) *
                                         (exp (-FR_B2_S * t) *
                                          ((1 − exp (-FR_TL1_CR * t)) *
                                           (exp (-FR_TL2_S * t) *
                                            (exp (-FR_B4_S * t) *
                                             (1 − exp (-FR_TR5_F * t))))))))) +
                                      (exp (-FR_TR1_S * t) *
                                       (exp (-FR_TR2_S * t) *
                                        (exp (-FR_TR3_S * t) *
                                         (exp (-FR_B1_S * t) *
                                          (exp (-FR_B2_S * t) *
                                           ((1 − exp (-FR_TL1_CR * t)) *
                                            (exp (-FR_TL2_S * t) *
                                             (exp (-FR_B4_S * t) *
                                              (1 − exp (-FR_TR5_PF * t))))))))) +
                                       (exp (-FR_TR1_S * t) *
                                        (exp (-FR_TR2_S * t) *
                                         (exp (-FR_TR3_S * t) *
                                          (exp (-FR_B1_S * t) *
                                           (exp (-FR_B2_S * t) *
                                            ((1 − exp (-FR_TL1_CR * t)) *
                                             (exp (-FR_TL2_S * t) *
                                              (1 − exp (-FR_B4_F * t)))))))) +
                                        (exp (-FR_TR1_S * t) *
                                         (exp (-FR_TR2_S * t) *
                                          (exp (-FR_TR3_S * t) *
                                           (exp (-FR_B1_S * t) *
                                            (exp (-FR_B2_S * t) *
                                             ((1 − exp (-FR_TL1_CR * t)) *
                                              (1 − exp (-FR_TL2_F * t))))))) +
                                         (exp (-FR_TR1_S * t) *
                                          (exp (-FR_TR2_S * t) *
                                           (exp (-FR_TR3_S * t) *
                                            (exp (-FR_B1_S * t) *
                                             (exp (-FR_B2_S * t) *
                                              ((1 − exp (-FR_TL1_CR * t)) *
                                               (1 − exp (-FR_TL2_HR * t))))))) +
                                          (exp (-FR_TR1_S * t) *
                                           (exp (-FR_TR2_S * t) *
                                            (exp (-FR_TR3_S * t) *
                                             (exp (-FR_B1_S * t) *
                                              (exp (-FR_B2_S * t) *
                                               ((1 − exp (-FR_TL1_CR * t)) *
                                                (1 − exp (-FR_TL2_CR * t))))))) +
                                           (exp (-FR_TR1_S * t) *
                                            (exp (-FR_TR2_S * t) *
                                             (exp (-FR_TR3_S * t) *
                                              (exp (-FR_B1_S * t) *
                                               (exp (-FR_B2_S * t) *
                                                ((1 − exp (-FR_TL1_CR * t)) *
                                                 (1 − exp (-FR_TL2_FTL * t))))))) +
                                            (exp (-FR_TR1_S * t) *
                                             (exp (-FR_TR2_S * t) *
                                              (exp (-FR_TR3_S * t) *
                                               (exp (-FR_B1_S * t) *
                                                (exp (-FR_B2_S * t) *
                                                 ((1 − exp (-FR_TL1_FTL * t)) *
                                                  (exp (-FR_TL2_S * t) *
                                                   (exp (-FR_B4_S * t) *
                                                    (1 − exp (-FR_TR5_F * t))))))))) +
                                             (exp (-FR_TR1_S * t) *
                                              (exp (-FR_TR2_S * t) *
                                               (exp (-FR_TR3_S * t) *
                                                (exp (-FR_B1_S * t) *
                                                 (exp (-FR_B2_S * t) *
                                                  ((1 − exp (-FR_TL1_FTL * t)) *
                                                   (exp (-FR_TL2_S * t) *
                                                    (exp (-FR_B4_S * t) *
                                                     (1 −
                                                      exp (-FR_TR5_PF * t))))))))) +
                                              (exp (-FR_TR1_S * t) *
                                               (exp (-FR_TR2_S * t) *
                                                (exp (-FR_TR3_S * t) *
                                                 (exp (-FR_B1_S * t) *
                                                  (exp (-FR_B2_S * t) *
                                                   ((1 −
                                                     exp (-FR_TL1_FTL * t)) *
                                                    (exp (-FR_TL2_S * t) *
                                                     (1 − exp (-FR_B4_F * t)))))))) +
                                               (exp (-FR_TR1_S * t) *
                                                (exp (-FR_TR2_S * t) *
                                                 (exp (-FR_TR3_S * t) *
                                                  (exp (-FR_B1_S * t) *
                                                   (exp (-FR_B2_S * t) *
                                                    ((1 −
                                                      exp (-FR_TL1_FTL * t)) *
                                                     (1 − exp (-FR_TL2_F * t))))))) +
                                                (exp (-FR_TR1_S * t) *
                                                 (exp (-FR_TR2_S * t) *
                                                  (exp (-FR_TR3_S * t) *
                                                   (exp (-FR_B1_S * t) *
                                                    (exp (-FR_B2_S * t) *
                                                     ((1 −
                                                       exp (-FR_TL1_FTL * t)) *
                                                      (1 −
                                                       exp (-FR_TL2_HR * t))))))) +
                                                 (exp (-FR_TR1_S * t) *
                                                  (exp (-FR_TR2_S * t) *
                                                   (exp (-FR_TR3_S * t) *
                                                    (exp (-FR_B1_S * t) *
                                                     (exp (-FR_B2_S * t) *
                                                      ((1 −
                                                        exp (-FR_TL1_FTL * t)) *
                                                       (1 −
                                                        exp (-FR_TL2_CR * t))))))) +
                                                  (exp (-FR_TR1_S * t) *
                                                   (exp (-FR_TR2_S * t) *
                                                    (exp (-FR_TR3_S * t) *
                                                     (exp (-FR_B1_S * t) *
                                                      (exp (-FR_B2_S * t) *
                                                       ((1 −
                                                         exp
                                                           (-FR_TL1_FTL * t)) *
                                                        (1 −
                                                         exp
                                                           (-FR_TL2_FTL * t))))))) +
                                                   (exp (-FR_TR1_S * t) *
                                                    (exp (-FR_TR2_S * t) *
                                                     (exp (-FR_TR3_S * t) *
                                                      (exp (-FR_B1_S * t) *
                                                       ((1 −
                                                         exp (-FR_B2_F * t)) *
                                                        (exp (-FR_TL1_S * t) *
                                                         (exp (-FR_B3_S * t) *
                                                          (1 −
                                                           exp
                                                             (-FR_TR4_F * t)))))))) +
                                                    (exp (-FR_TR1_S * t) *
                                                     (exp (-FR_TR2_S * t) *
                                                      (exp (-FR_TR3_S * t) *
                                                       (exp (-FR_B1_S * t) *
                                                        ((1 −
                                                          exp (-FR_B2_F * t)) *
                                                         (exp (-FR_TL1_S * t) *
                                                          (exp (-FR_B3_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_TR4_PF * t)))))))) +
                                                     (exp (-FR_TR1_S * t) *
                                                      (exp (-FR_TR2_S * t) *
                                                       (exp (-FR_TR3_S * t) *
                                                        (exp (-FR_B1_S * t) *
                                                         ((1 −
                                                           exp (-FR_B2_F * t)) *
                                                          (exp
                                                             (-FR_TL1_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_B3_F * t))))))) +
                                                      (exp (-FR_TR1_S * t) *
                                                       (exp (-FR_TR2_S * t) *
                                                        (exp (-FR_TR3_S * t) *
                                                         (exp (-FR_B1_S * t) *
                                                          ((1 −
                                                            exp
                                                              (-FR_B2_F * t)) *
                                                           (1 −
                                                            exp
                                                              (-FR_TL1_F * t)))))) +
                                                       (exp (-FR_TR1_S * t) *
                                                        (exp (-FR_TR2_S * t) *
                                                         (exp (-FR_TR3_S * t) *
                                                          (exp (-FR_B1_S * t) *
                                                           ((1 −
                                                             exp
                                                               (-FR_B2_F * t)) *
                                                            (1 −
                                                             exp
                                                               (-FR_TL1_HR *
                                                                t)))))) +
                                                        (exp (-FR_TR1_S * t) *
                                                         (exp (-FR_TR2_S * t) *
                                                          (exp
                                                             (-FR_TR3_S * t) *
                                                           (exp
                                                              (-FR_B1_S * t) *
                                                            ((1 −
                                                              exp
                                                                (-FR_B2_F * t)) *
                                                             (1 −
                                                              exp
                                                                (-FR_TL1_CR *
                                                                 t)))))) +
                                                         (exp (-FR_TR1_S * t) *
                                                          (exp
                                                             (-FR_TR2_S * t) *
                                                           (exp
                                                              (-FR_TR3_S * t) *
                                                            (exp
                                                               (-FR_B1_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B2_F *
                                                                  t)) *
                                                              (1 −
                                                               exp
                                                                 (-FR_TL1_FTL *
                                                                  t)))))) +
                                                          (exp
                                                             (-FR_TR1_S * t) *
                                                           (exp
                                                              (-FR_TR2_S * t) *
                                                            (exp
                                                               (-FR_TR3_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B1_F *
                                                                  t)) *
                                                              (exp
                                                                 (-FR_B2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TL2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_B4_S *
                                                                    t) *
                                                                 (1 −
                                                                  exp
                                                                    (-FR_TR5_F *
                                                                     t)))))))) +
                                                           (exp
                                                              (-FR_TR1_S * t) *
                                                            (exp
                                                               (-FR_TR2_S * t) *
                                                             (exp
                                                                (-FR_TR3_S *
                                                                 t) *
                                                              ((1 −
                                                                exp
                                                                  (-FR_B1_F *
                                                                   t)) *
                                                               (exp
                                                                  (-FR_B2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TL2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_B4_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TR5_PF *
                                                                      t)))))))) +
                                                            (exp
                                                               (-FR_TR1_S * t) *
                                                             (exp
                                                                (-FR_TR2_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR3_S *
                                                                  t) *
                                                               ((1 −
                                                                 exp
                                                                   (-FR_B1_F *
                                                                    t)) *
                                                                (exp
                                                                   (-FR_B2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TL2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_B4_F *
                                                                      t))))))) +
                                                             (exp
                                                                (-FR_TR1_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR3_S *
                                                                   t) *
                                                                ((1 −
                                                                  exp
                                                                    (-FR_B1_F *
                                                                     t)) *
                                                                 (exp
                                                                    (-FR_B2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TL2_F *
                                                                      t)))))) +
                                                              (exp
                                                                 (-FR_TR1_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR3_S *
                                                                    t) *
                                                                 ((1 −
                                                                   exp
                                                                     (-FR_B1_F *
                                                                      t)) *
                                                                  (exp
                                                                     (-FR_B2_S *
                                                                      t) *
                                                                   (1 −
                                                                    exp
                                                                      (-FR_TL2_HR *
                                                                       t)))))) +
                                                               (exp
                                                                  (-FR_TR1_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR3_S *
                                                                     t) *
                                                                  ((1 −
                                                                    exp
                                                                      (-FR_B1_F *
                                                                       t)) *
                                                                   (exp
                                                                      (-FR_B2_S *
                                                                       t) *
                                                                    (1 −
                                                                     exp
                                                                       (-FR_TL2_CR *
                                                                        t)))))) +
                                                                (exp
                                                                   (-FR_TR1_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR2_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR3_S *
                                                                      t) *
                                                                   ((1 −
                                                                     exp
                                                                       (-FR_B1_F *
                                                                        t)) *
                                                                    (exp
                                                                       (-FR_B2_S *
                                                                        t) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_TL2_FTL *
                                                                         t)))))) +
                                                                 (exp
                                                                    (-FR_TR1_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR2_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR3_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_B1_F *
                                                                         t)) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_B2_F *
                                                                         t))))) +
                                                                  (exp
                                                                     (-FR_TR1_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR2_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_TR3_F *
                                                                         t)) *
                                                                     (exp
                                                                        (-FR_B1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TL1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_B3_S *
                                                                           t) *
                                                                        (1 −
                                                                         exp
                                                                           (-FR_TR4_F *
                                                                            t))))))) +
                                                                   (exp
                                                                      (-FR_TR1_S *
                                                                       t) *
                                                                    (exp
                                                                       (-FR_TR2_S *
                                                                        t) *
                                                                     ((1 −
                                                                       exp
                                                                         (-FR_TR3_F *
                                                                          t)) *
                                                                      (exp
                                                                         (-FR_B1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TL1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_B3_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TR4_PF *
                                                                             t))))))) +
                                                                    (exp
                                                                       (-FR_TR1_S *
                                                                        t) *
                                                                     (exp
                                                                        (-FR_TR2_S *
                                                                         t) *
                                                                      ((1 −
                                                                        exp
                                                                          (-FR_TR3_F *
                                                                           t)) *
                                                                       (exp
                                                                          (-FR_B1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TL1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_B3_F *
                                                                             t)))))) +
                                                                     (exp
                                                                        (-FR_TR1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TR2_S *
                                                                          t) *
                                                                       ((1 −
                                                                         exp
                                                                           (-FR_TR3_F *
                                                                            t)) *
                                                                        (exp
                                                                           (-FR_B1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TL1_F *
                                                                             t))))) +
                                                                      (exp
                                                                         (-FR_TR1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TR2_S *
                                                                           t) *
                                                                        ((1 −
                                                                          exp
                                                                            (-FR_TR3_F *
                                                                             t)) *
                                                                         (exp
                                                                            (-FR_B1_S *
                                                                             t) *
                                                                          (1 −
                                                                           exp
                                                                             (-FR_TL1_HR *
                                                                              t))))) +
                                                                       (exp
                                                                          (-FR_TR1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TR2_S *
                                                                            t) *
                                                                         ((1 −
                                                                           exp
                                                                             (-FR_TR3_F *
                                                                              t)) *
                                                                          (exp
                                                                             (-FR_B1_S *
                                                                              t) *
                                                                           (1 −
                                                                            exp
                                                                              (-FR_TL1_CR *
                                                                               t))))) +
                                                                        (exp
                                                                           (-FR_TR1_S *
                                                                            t) *
                                                                         (exp
                                                                            (-FR_TR2_S *
                                                                             t) *
                                                                          ((1 −
                                                                            exp
                                                                              (-FR_TR3_F *
                                                                               t)) *
                                                                           (exp
                                                                              (-FR_B1_S *
                                                                               t) *
                                                                            (1 −
                                                                             exp
                                                                               (-FR_TL1_FTL *
                                                                                t))))) +
                                                                         (exp
                                                                            (-FR_TR1_S *
                                                                             t) *
                                                                          (exp
                                                                             (-FR_TR2_S *
                                                                              t) *
                                                                           ((1 −
                                                                             exp
                                                                               (-FR_TR3_PF *
                                                                                t)) *
                                                                            (exp
                                                                               (-FR_B1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TL1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_B3_S *
                                                                                  t) *
                                                                               exp
                                                                                 (-FR_TR4_S *
                                                                                  t)))))) +
                                                                          (exp
                                                                             (-FR_TR1_S *
                                                                              t) *
                                                                           (exp
                                                                              (-FR_TR2_S *
                                                                               t) *
                                                                            ((1 −
                                                                              exp
                                                                                (-FR_TR3_PF *
                                                                                 t)) *
                                                                             (exp
                                                                                (-FR_B1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TL1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_B3_S *
                                                                                   t) *
                                                                                (1 −
                                                                                 exp
                                                                                   (-FR_TR4_F *
                                                                                    t))))))) +
                                                                           (exp
                                                                              (-FR_TR1_S *
                                                                               t) *
                                                                            (exp
                                                                               (-FR_TR2_S *
                                                                                t) *
                                                                             ((1 −
                                                                               exp
                                                                                 (-FR_TR3_PF *
                                                                                  t)) *
                                                                              (exp
                                                                                 (-FR_B1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TL1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_B3_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TR4_PF *
                                                                                     t))))))) +
                                                                            (exp
                                                                               (-FR_TR1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TR2_S *
                                                                                 t) *
                                                                              ((1 −
                                                                                exp
                                                                                  (-FR_TR3_PF *
                                                                                   t)) *
                                                                               (exp
                                                                                  (-FR_B1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TL1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_B3_F *
                                                                                     t)))))) +
                                                                             (exp
                                                                                (-FR_TR1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TR2_S *
                                                                                  t) *
                                                                               ((1 −
                                                                                 exp
                                                                                   (-FR_TR3_PF *
                                                                                    t)) *
                                                                                (exp
                                                                                   (-FR_B1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TL1_F *
                                                                                     t))))) +
                                                                              (exp
                                                                                 (-FR_TR1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TR2_S *
                                                                                   t) *
                                                                                ((1 −
                                                                                  exp
                                                                                    (-FR_TR3_PF *
                                                                                     t)) *
                                                                                 (exp
                                                                                    (-FR_B1_S *
                                                                                     t) *
                                                                                  (1 −
                                                                                   exp
                                                                                     (-FR_TL1_HR *
                                                                                      t))))) +
                                                                               (exp
                                                                                  (-FR_TR1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TR2_S *
                                                                                    t) *
                                                                                 ((1 −
                                                                                   exp
                                                                                     (-FR_TR3_PF *
                                                                                      t)) *
                                                                                  (exp
                                                                                     (-FR_B1_S *
                                                                                      t) *
                                                                                   (1 −
                                                                                    exp
                                                                                      (-FR_TL1_CR *
                                                                                       t))))) +
                                                                                (exp
                                                                                   (-FR_TR1_S *
                                                                                    t) *
                                                                                 (exp
                                                                                    (-FR_TR2_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR3_PF *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_B1_S *
                                                                                       t) *
                                                                                    (1 −
                                                                                     exp
                                                                                       (-FR_TL1_FTL *
                                                                                        t))))) +
                                                                                 (exp
                                                                                    (-FR_TR1_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR2_F *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_TR3_S *
                                                                                       t) *
                                                                                    (exp
                                                                                       (-FR_B2_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_TL2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B4_S *
                                                                                          t) *
                                                                                       exp
                                                                                         (-FR_TR5_S *
                                                                                          t)))))) +
                                                                                  (exp
                                                                                     (-FR_TR1_S *
                                                                                      t) *
                                                                                   ((1 −
                                                                                     exp
                                                                                       (-FR_TR2_F *
                                                                                        t)) *
                                                                                    (exp
                                                                                       (-FR_TR3_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_B2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_TL2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B4_S *
                                                                                           t) *
                                                                                        (1 −
                                                                                         exp
                                                                                           (-FR_TR5_F *
                                                                                            t))))))) +
                                                                                   (exp
                                                                                      (-FR_TR1_S *
                                                                                       t) *
                                                                                    ((1 −
                                                                                      exp
                                                                                        (-FR_TR2_F *
                                                                                         t)) *
                                                                                     (exp
                                                                                        (-FR_TR3_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_TL2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B4_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TR5_PF *
                                                                                             t))))))) +
                                                                                    (exp
                                                                                       (-FR_TR1_S *
                                                                                        t) *
                                                                                     ((1 −
                                                                                       exp
                                                                                         (-FR_TR2_F *
                                                                                          t)) *
                                                                                      (exp
                                                                                         (-FR_TR3_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_TL2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_B4_F *
                                                                                             t)))))) +
                                                                                     (exp
                                                                                        (-FR_TR1_S *
                                                                                         t) *
                                                                                      ((1 −
                                                                                        exp
                                                                                          (-FR_TR2_F *
                                                                                           t)) *
                                                                                       (exp
                                                                                          (-FR_TR3_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TL2_F *
                                                                                             t))))) +
                                                                                      (exp
                                                                                         (-FR_TR1_S *
                                                                                          t) *
                                                                                       ((1 −
                                                                                         exp
                                                                                           (-FR_TR2_F *
                                                                                            t)) *
                                                                                        (exp
                                                                                           (-FR_TR3_S *
                                                                                            t) *
                                                                                         (exp
                                                                                            (-FR_B2_S *
                                                                                             t) *
                                                                                          (1 −
                                                                                           exp
                                                                                             (-FR_TL2_HR *
                                                                                              t))))) +
                                                                                       (exp
                                                                                          (-FR_TR1_S *
                                                                                           t) *
                                                                                        ((1 −
                                                                                          exp
                                                                                            (-FR_TR2_F *
                                                                                             t)) *
                                                                                         (exp
                                                                                            (-FR_TR3_S *
                                                                                             t) *
                                                                                          (exp
                                                                                             (-FR_B2_S *
                                                                                              t) *
                                                                                           (1 −
                                                                                            exp
                                                                                              (-FR_TL2_CR *
                                                                                               t))))) +
                                                                                        (exp
                                                                                           (-FR_TR1_S *
                                                                                            t) *
                                                                                         ((1 −
                                                                                           exp
                                                                                             (-FR_TR2_F *
                                                                                              t)) *
                                                                                          (exp
                                                                                             (-FR_TR3_S *
                                                                                              t) *
                                                                                           (exp
                                                                                              (-FR_B2_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TL2_FTL *
                                                                                                t))))) +
                                                                                         (exp
                                                                                            (-FR_TR1_S *
                                                                                             t) *
                                                                                          ((1 −
                                                                                            exp
                                                                                              (-FR_TR2_F *
                                                                                               t)) *
                                                                                           (exp
                                                                                              (-FR_TR3_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_B2_F *
                                                                                                t)))) +
                                                                                          (exp
                                                                                             (-FR_TR1_S *
                                                                                              t) *
                                                                                           ((1 −
                                                                                             exp
                                                                                               (-FR_TR2_F *
                                                                                                t)) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TR3_F *
                                                                                                t))) +
                                                                                           (exp
                                                                                              (-FR_TR1_S *
                                                                                               t) *
                                                                                            ((1 −
                                                                                              exp
                                                                                                (-FR_TR2_PF *
                                                                                                 t)) *
                                                                                             (exp
                                                                                                (-FR_TR3_S *
                                                                                                 t) *
                                                                                              (exp
                                                                                                 (-FR_B2_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_TL2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B4_S *
                                                                                                    t) *
                                                                                                 exp
                                                                                                   (-FR_TR5_S *
                                                                                                    t)))))) +
                                                                                            (exp
                                                                                               (-FR_TR1_S *
                                                                                                t) *
                                                                                             ((1 −
                                                                                               exp
                                                                                                 (-FR_TR2_PF *
                                                                                                  t)) *
                                                                                              (exp
                                                                                                 (-FR_TR3_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_B2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_TL2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B4_S *
                                                                                                     t) *
                                                                                                  (1 −
                                                                                                   exp
                                                                                                     (-FR_TR5_F *
                                                                                                      t))))))) +
                                                                                             (exp
                                                                                                (-FR_TR1_S *
                                                                                                 t) *
                                                                                              ((1 −
                                                                                                exp
                                                                                                  (-FR_TR2_PF *
                                                                                                   t)) *
                                                                                               (exp
                                                                                                  (-FR_TR3_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_TL2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B4_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TR5_PF *
                                                                                                       t))))))) +
                                                                                              (exp
                                                                                                 (-FR_TR1_S *
                                                                                                  t) *
                                                                                               ((1 −
                                                                                                 exp
                                                                                                   (-FR_TR2_PF *
                                                                                                    t)) *
                                                                                                (exp
                                                                                                   (-FR_TR3_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_TL2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_B4_F *
                                                                                                       t)))))) +
                                                                                               (exp
                                                                                                  (-FR_TR1_S *
                                                                                                   t) *
                                                                                                ((1 −
                                                                                                  exp
                                                                                                    (-FR_TR2_PF *
                                                                                                     t)) *
                                                                                                 (exp
                                                                                                    (-FR_TR3_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TL2_F *
                                                                                                       t))))) +
                                                                                                (exp
                                                                                                   (-FR_TR1_S *
                                                                                                    t) *
                                                                                                 ((1 −
                                                                                                   exp
                                                                                                     (-FR_TR2_PF *
                                                                                                      t)) *
                                                                                                  (exp
                                                                                                     (-FR_TR3_S *
                                                                                                      t) *
                                                                                                   (exp
                                                                                                      (-FR_B2_S *
                                                                                                       t) *
                                                                                                    (1 −
                                                                                                     exp
                                                                                                       (-FR_TL2_HR *
                                                                                                        t))))) +
                                                                                                 (exp
                                                                                                    (-FR_TR1_S *
                                                                                                     t) *
                                                                                                  ((1 −
                                                                                                    exp
                                                                                                      (-FR_TR2_PF *
                                                                                                       t)) *
                                                                                                   (exp
                                                                                                      (-FR_TR3_S *
                                                                                                       t) *
                                                                                                    (exp
                                                                                                       (-FR_B2_S *
                                                                                                        t) *
                                                                                                     (1 −
                                                                                                      exp
                                                                                                        (-FR_TL2_CR *
                                                                                                         t))))) +
                                                                                                  (exp
                                                                                                     (-FR_TR1_S *
                                                                                                      t) *
                                                                                                   ((1 −
                                                                                                     exp
                                                                                                       (-FR_TR2_PF *
                                                                                                        t)) *
                                                                                                    (exp
                                                                                                       (-FR_TR3_S *
                                                                                                        t) *
                                                                                                     (exp
                                                                                                        (-FR_B2_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TL2_FTL *
                                                                                                          t))))) +
                                                                                                   (exp
                                                                                                      (-FR_TR1_S *
                                                                                                       t) *
                                                                                                    ((1 −
                                                                                                      exp
                                                                                                        (-FR_TR2_PF *
                                                                                                         t)) *
                                                                                                     (exp
                                                                                                        (-FR_TR3_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_B2_F *
                                                                                                          t)))) +
                                                                                                    (exp
                                                                                                       (-FR_TR1_S *
                                                                                                        t) *
                                                                                                     ((1 −
                                                                                                       exp
                                                                                                         (-FR_TR2_PF *
                                                                                                          t)) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR3_F *
                                                                                                          t))) +
                                                                                                     (exp
                                                                                                        (-FR_TR1_S *
                                                                                                         t) *
                                                                                                      ((1 −
                                                                                                        exp
                                                                                                          (-FR_TR2_PF *
                                                                                                           t)) *
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR3_PF *
                                                                                                           t))) +
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR1_F *
                                                                                                          t) +
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR1_PF *
                                                                                                           t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * 80 * 115,000)/115,000 * 8760``;

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``ASAI``
``115,000 * 8760 - (exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_F * t)) * exp (-FR_TR5_S * t)))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * exp (-FR_TR5_S * t)))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * exp (-FR_TR4_S * t))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              ((1 − exp (-FR_B3_F * t)) *
               (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              ((1 − exp (-FR_TL2_F * t)) *
               (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               ((1 − exp (-FR_TL2_HR * t)) *
                (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                ((1 − exp (-FR_TL2_CR * t)) *
                 (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_FTL * t)) *
                  (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (exp (-FR_B1_S * t) *
                (exp (-FR_B2_S * t) *
                 ((1 − exp (-FR_TL1_F * t)) *
                  (exp (-FR_TL2_S * t) *
                   (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  ((1 − exp (-FR_TL1_HR * t)) *
                   (exp (-FR_TL2_S * t) *
                    (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   ((1 − exp (-FR_TL1_CR * t)) *
                    (exp (-FR_TL2_S * t) *
                     (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    ((1 − exp (-FR_TL1_FTL * t)) *
                     (exp (-FR_TL2_S * t) *
                      (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    ((1 − exp (-FR_B2_F * t)) *
                     (exp (-FR_TL1_S * t) *
                      (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    ((1 − exp (-FR_B1_F * t)) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL2_S * t) *
                       (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    ((1 − exp (-FR_TR3_F * t)) *
                     (exp (-FR_B1_S * t) * exp (-FR_TL1_S * t)))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     ((1 − exp (-FR_TR3_F * t)) * (1 − exp (-FR_B1_F * t)))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      ((1 − exp (-FR_TR3_PF * t)) * (1 − exp (-FR_B1_F * t)))) +
                     exp (-FR_TR1_S * t) *
                     ((1 − exp (-FR_TR2_F * t)) * (1 − exp (-FR_TR3_PF * t)))))))))))))))))))) * 40 * 55,000 +
  exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_F * t)))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              (exp (-FR_B3_S * t) *
               ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_PF * t)))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              (exp (-FR_TL2_S * t) *
               ((1 − exp (-FR_B3_F * t)) *
                (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_F * t)))))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               (exp (-FR_TL2_S * t) *
                ((1 − exp (-FR_B3_F * t)) *
                 (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_PF * t)))))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                (exp (-FR_TL2_S * t) *
                 ((1 − exp (-FR_B3_F * t)) * (1 − exp (-FR_B4_F * t))))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_F * t)) *
                  (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (RELIABILITY p B1 t *
                (RELIABILITY p B2 t *
                 (exp (-FR_TL1_S * t) *
                  ((1 − exp (-FR_TL2_F * t)) *
                   (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  (exp (-FR_TL1_S * t) *
                   ((1 − exp (-FR_TL2_F * t)) * (1 − exp (-FR_B3_F * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   (exp (-FR_TL1_S * t) *
                    ((1 − exp (-FR_TL2_HR * t)) *
                     (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    (exp (-FR_TL1_S * t) *
                     ((1 − exp (-FR_TL2_HR * t)) *
                      (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    (exp (-FR_B2_S * t) *
                     (exp (-FR_TL1_S * t) *
                      ((1 − exp (-FR_TL2_HR * t)) * (1 − exp (-FR_B3_F * t)))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    (exp (-FR_B1_S * t) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL1_S * t) *
                       ((1 − exp (-FR_TL2_CR * t)) *
                        (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    (exp (-FR_TR3_S * t) *
                     (exp (-FR_B1_S * t) *
                      (exp (-FR_B2_S * t) *
                       (exp (-FR_TL1_S * t) *
                        ((1 − exp (-FR_TL2_CR * t)) *
                         (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     (exp (-FR_TR3_S * t) *
                      (exp (-FR_B1_S * t) *
                       (exp (-FR_B2_S * t) *
                        (exp (-FR_TL1_S * t) *
                         ((1 − exp (-FR_TL2_CR * t)) *
                          (1 − exp (-FR_B3_F * t)))))))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      (exp (-FR_TR3_S * t) *
                       (exp (-FR_B1_S * t) *
                        (exp (-FR_B2_S * t) *
                         (exp (-FR_TL1_S * t) *
                          ((1 − exp (-FR_TL2_FTL * t)) *
                           (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                     (exp (-FR_TR1_S * t) *
                      (exp (-FR_TR2_S * t) *
                       (exp (-FR_TR3_S * t) *
                        (exp (-FR_B1_S * t) *
                         (exp (-FR_B2_S * t) *
                          (exp (-FR_TL1_S * t) *
                           ((1 − exp (-FR_TL2_FTL * t)) *
                            (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                      (exp (-FR_TR1_S * t) *
                       (exp (-FR_TR2_S * t) *
                        (exp (-FR_TR3_S * t) *
                         (exp (-FR_B1_S * t) *
                          (exp (-FR_B2_S * t) *
                           (exp (-FR_TL1_S * t) *
                            ((1 − exp (-FR_TL2_FTL * t)) *
                             (1 − exp (-FR_B3_F * t)))))))) +
                       (exp (-FR_TR1_S * t) *
                        (exp (-FR_TR2_S * t) *
                         (exp (-FR_TR3_S * t) *
                          (exp (-FR_B1_S * t) *
                           (exp (-FR_B2_S * t) *
                            ((1 − exp (-FR_TL1_F * t)) *
                             (exp (-FR_TL2_S * t) *
                              (exp (-FR_B4_S * t) *
                               (1 − exp (-FR_TR5_F * t))))))))) +
                        (exp (-FR_TR1_S * t) *
                         (exp (-FR_TR2_S * t) *
                          (exp (-FR_TR3_S * t) *
                           (exp (-FR_B1_S * t) *
                            (exp (-FR_B2_S * t) *
                             ((1 − exp (-FR_TL1_F * t)) *
                              (exp (-FR_TL2_S * t) *
                               (exp (-FR_B4_S * t) *
                                (1 − exp (-FR_TR5_PF * t))))))))) +
                         (exp (-FR_TR1_S * t) *
                          (exp (-FR_TR2_S * t) *
                           (exp (-FR_TR3_S * t) *
                            (exp (-FR_B1_S * t) *
                             (exp (-FR_B2_S * t) *
                              ((1 − exp (-FR_TL1_F * t)) *
                               (exp (-FR_TL2_S * t) *
                                (1 − exp (-FR_B4_F * t)))))))) +
                          (exp (-FR_TR1_S * t) *
                           (exp (-FR_TR2_S * t) *
                            (exp (-FR_TR3_S * t) *
                             (exp (-FR_B1_S * t) *
                              (exp (-FR_B2_S * t) *
                               ((1 − exp (-FR_TL1_F * t)) *
                                (1 − exp (-FR_TL2_F * t))))))) +
                           (exp (-FR_TR1_S * t) *
                            (exp (-FR_TR2_S * t) *
                             (exp (-FR_TR3_S * t) *
                              (exp (-FR_B1_S * t) *
                               (exp (-FR_B2_S * t) *
                                ((1 − exp (-FR_TL1_F * t)) *
                                 (1 − exp (-FR_TL2_HR * t))))))) +
                            (exp (-FR_TR1_S * t) *
                             (exp (-FR_TR2_S * t) *
                              (exp (-FR_TR3_S * t) *
                               (exp (-FR_B1_S * t) *
                                (exp (-FR_B2_S * t) *
                                 ((1 − exp (-FR_TL1_F * t)) *
                                  (1 − exp (-FR_TL2_CR * t))))))) +
                             (exp (-FR_TR1_S * t) *
                              (exp (-FR_TR2_S * t) *
                               (exp (-FR_TR3_S * t) *
                                (exp (-FR_B1_S * t) *
                                 (exp (-FR_B2_S * t) *
                                  ((1 − exp (-FR_TL1_F * t)) *
                                   (1 − exp (-FR_TL2_FTL * t))))))) +
                              (exp (-FR_TR1_S * t) *
                               (exp (-FR_TR2_S * t) *
                                (exp (-FR_TR3_S * t) *
                                 (exp (-FR_B1_S * t) *
                                  (exp (-FR_B2_S * t) *
                                   ((1 − exp (-FR_TL1_HR * t)) *
                                    (exp (-FR_TL2_S * t) *
                                     (exp (-FR_B4_S * t) *
                                      (1 − exp (-FR_TR5_F * t))))))))) +
                               (exp (-FR_TR1_S * t) *
                                (exp (-FR_TR2_S * t) *
                                 (exp (-FR_TR3_S * t) *
                                  (exp (-FR_B1_S * t) *
                                   (exp (-FR_B2_S * t) *
                                    ((1 − exp (-FR_TL1_HR * t)) *
                                     (exp (-FR_TL2_S * t) *
                                      (exp (-FR_B4_S * t) *
                                       (1 − exp (-FR_TR5_PF * t))))))))) +
                                (exp (-FR_TR1_S * t) *
                                 (exp (-FR_TR2_S * t) *
                                  (exp (-FR_TR3_S * t) *
                                   (exp (-FR_B1_S * t) *
                                    (exp (-FR_B2_S * t) *
                                     ((1 − exp (-FR_TL1_HR * t)) *
                                      (exp (-FR_TL2_S * t) *
                                       (1 − exp (-FR_B4_F * t)))))))) +
                                 (exp (-FR_TR1_S * t) *
                                  (exp (-FR_TR2_S * t) *
                                   (exp (-FR_TR3_S * t) *
                                    (exp (-FR_B1_S * t) *
                                     (exp (-FR_B2_S * t) *
                                      ((1 − exp (-FR_TL1_HR * t)) *
                                       (1 − exp (-FR_TL2_F * t))))))) +
                                  (exp (-FR_TR1_S * t) *
                                   (exp (-FR_TR2_S * t) *
                                    (exp (-FR_TR3_S * t) *
                                     (exp (-FR_B1_S * t) *
                                      (exp (-FR_B2_S * t) *
                                       ((1 − exp (-FR_TL1_HR * t)) *
                                        (1 − exp (-FR_TL2_HR * t))))))) +
                                   (exp (-FR_TR1_S * t) *
                                    (exp (-FR_TR2_S * t) *
                                     (exp (-FR_TR3_S * t) *
                                      (exp (-FR_B1_S * t) *
                                       (exp (-FR_B2_S * t) *
                                        ((1 − exp (-FR_TL1_HR * t)) *
                                         (1 − exp (-FR_TL2_CR * t))))))) +
                                    (exp (-FR_TR1_S * t) *
                                     (exp (-FR_TR2_S * t) *
                                      (exp (-FR_TR3_S * t) *
                                       (exp (-FR_B1_S * t) *
                                        (exp (-FR_B2_S * t) *
                                         ((1 − exp (-FR_TL1_HR * t)) *
                                          (1 − exp (-FR_TL2_FTL * t))))))) +
                                     (exp (-FR_TR1_S * t) *
                                      (exp (-FR_TR2_S * t) *
                                       (exp (-FR_TR3_S * t) *
                                        (exp (-FR_B1_S * t) *
                                         (exp (-FR_B2_S * t) *
                                          ((1 − exp (-FR_TL1_CR * t)) *
                                           (exp (-FR_TL2_S * t) *
                                            (exp (-FR_B4_S * t) *
                                             (1 − exp (-FR_TR5_F * t))))))))) +
                                      (exp (-FR_TR1_S * t) *
                                       (exp (-FR_TR2_S * t) *
                                        (exp (-FR_TR3_S * t) *
                                         (exp (-FR_B1_S * t) *
                                          (exp (-FR_B2_S * t) *
                                           ((1 − exp (-FR_TL1_CR * t)) *
                                            (exp (-FR_TL2_S * t) *
                                             (exp (-FR_B4_S * t) *
                                              (1 − exp (-FR_TR5_PF * t))))))))) +
                                       (exp (-FR_TR1_S * t) *
                                        (exp (-FR_TR2_S * t) *
                                         (exp (-FR_TR3_S * t) *
                                          (exp (-FR_B1_S * t) *
                                           (exp (-FR_B2_S * t) *
                                            ((1 − exp (-FR_TL1_CR * t)) *
                                             (exp (-FR_TL2_S * t) *
                                              (1 − exp (-FR_B4_F * t)))))))) +
                                        (exp (-FR_TR1_S * t) *
                                         (exp (-FR_TR2_S * t) *
                                          (exp (-FR_TR3_S * t) *
                                           (exp (-FR_B1_S * t) *
                                            (exp (-FR_B2_S * t) *
                                             ((1 − exp (-FR_TL1_CR * t)) *
                                              (1 − exp (-FR_TL2_F * t))))))) +
                                         (exp (-FR_TR1_S * t) *
                                          (exp (-FR_TR2_S * t) *
                                           (exp (-FR_TR3_S * t) *
                                            (exp (-FR_B1_S * t) *
                                             (exp (-FR_B2_S * t) *
                                              ((1 − exp (-FR_TL1_CR * t)) *
                                               (1 − exp (-FR_TL2_HR * t))))))) +
                                          (exp (-FR_TR1_S * t) *
                                           (exp (-FR_TR2_S * t) *
                                            (exp (-FR_TR3_S * t) *
                                             (exp (-FR_B1_S * t) *
                                              (exp (-FR_B2_S * t) *
                                               ((1 − exp (-FR_TL1_CR * t)) *
                                                (1 − exp (-FR_TL2_CR * t))))))) +
                                           (exp (-FR_TR1_S * t) *
                                            (exp (-FR_TR2_S * t) *
                                             (exp (-FR_TR3_S * t) *
                                              (exp (-FR_B1_S * t) *
                                               (exp (-FR_B2_S * t) *
                                                ((1 − exp (-FR_TL1_CR * t)) *
                                                 (1 − exp (-FR_TL2_FTL * t))))))) +
                                            (exp (-FR_TR1_S * t) *
                                             (exp (-FR_TR2_S * t) *
                                              (exp (-FR_TR3_S * t) *
                                               (exp (-FR_B1_S * t) *
                                                (exp (-FR_B2_S * t) *
                                                 ((1 − exp (-FR_TL1_FTL * t)) *
                                                  (exp (-FR_TL2_S * t) *
                                                   (exp (-FR_B4_S * t) *
                                                    (1 − exp (-FR_TR5_F * t))))))))) +
                                             (exp (-FR_TR1_S * t) *
                                              (exp (-FR_TR2_S * t) *
                                               (exp (-FR_TR3_S * t) *
                                                (exp (-FR_B1_S * t) *
                                                 (exp (-FR_B2_S * t) *
                                                  ((1 − exp (-FR_TL1_FTL * t)) *
                                                   (exp (-FR_TL2_S * t) *
                                                    (exp (-FR_B4_S * t) *
                                                     (1 −
                                                      exp (-FR_TR5_PF * t))))))))) +
                                              (exp (-FR_TR1_S * t) *
                                               (exp (-FR_TR2_S * t) *
                                                (exp (-FR_TR3_S * t) *
                                                 (exp (-FR_B1_S * t) *
                                                  (exp (-FR_B2_S * t) *
                                                   ((1 −
                                                     exp (-FR_TL1_FTL * t)) *
                                                    (exp (-FR_TL2_S * t) *
                                                     (1 − exp (-FR_B4_F * t)))))))) +
                                               (exp (-FR_TR1_S * t) *
                                                (exp (-FR_TR2_S * t) *
                                                 (exp (-FR_TR3_S * t) *
                                                  (exp (-FR_B1_S * t) *
                                                   (exp (-FR_B2_S * t) *
                                                    ((1 −
                                                      exp (-FR_TL1_FTL * t)) *
                                                     (1 − exp (-FR_TL2_F * t))))))) +
                                                (exp (-FR_TR1_S * t) *
                                                 (exp (-FR_TR2_S * t) *
                                                  (exp (-FR_TR3_S * t) *
                                                   (exp (-FR_B1_S * t) *
                                                    (exp (-FR_B2_S * t) *
                                                     ((1 −
                                                       exp (-FR_TL1_FTL * t)) *
                                                      (1 −
                                                       exp (-FR_TL2_HR * t))))))) +
                                                 (exp (-FR_TR1_S * t) *
                                                  (exp (-FR_TR2_S * t) *
                                                   (exp (-FR_TR3_S * t) *
                                                    (exp (-FR_B1_S * t) *
                                                     (exp (-FR_B2_S * t) *
                                                      ((1 −
                                                        exp (-FR_TL1_FTL * t)) *
                                                       (1 −
                                                        exp (-FR_TL2_CR * t))))))) +
                                                  (exp (-FR_TR1_S * t) *
                                                   (exp (-FR_TR2_S * t) *
                                                    (exp (-FR_TR3_S * t) *
                                                     (exp (-FR_B1_S * t) *
                                                      (exp (-FR_B2_S * t) *
                                                       ((1 −
                                                         exp
                                                           (-FR_TL1_FTL * t)) *
                                                        (1 −
                                                         exp
                                                           (-FR_TL2_FTL * t))))))) +
                                                   (exp (-FR_TR1_S * t) *
                                                    (exp (-FR_TR2_S * t) *
                                                     (exp (-FR_TR3_S * t) *
                                                      (exp (-FR_B1_S * t) *
                                                       ((1 −
                                                         exp (-FR_B2_F * t)) *
                                                        (exp (-FR_TL1_S * t) *
                                                         (exp (-FR_B3_S * t) *
                                                          (1 −
                                                           exp
                                                             (-FR_TR4_F * t)))))))) +
                                                    (exp (-FR_TR1_S * t) *
                                                     (exp (-FR_TR2_S * t) *
                                                      (exp (-FR_TR3_S * t) *
                                                       (exp (-FR_B1_S * t) *
                                                        ((1 −
                                                          exp (-FR_B2_F * t)) *
                                                         (exp (-FR_TL1_S * t) *
                                                          (exp (-FR_B3_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_TR4_PF * t)))))))) +
                                                     (exp (-FR_TR1_S * t) *
                                                      (exp (-FR_TR2_S * t) *
                                                       (exp (-FR_TR3_S * t) *
                                                        (exp (-FR_B1_S * t) *
                                                         ((1 −
                                                           exp (-FR_B2_F * t)) *
                                                          (exp
                                                             (-FR_TL1_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_B3_F * t))))))) +
                                                      (exp (-FR_TR1_S * t) *
                                                       (exp (-FR_TR2_S * t) *
                                                        (exp (-FR_TR3_S * t) *
                                                         (exp (-FR_B1_S * t) *
                                                          ((1 −
                                                            exp
                                                              (-FR_B2_F * t)) *
                                                           (1 −
                                                            exp
                                                              (-FR_TL1_F * t)))))) +
                                                       (exp (-FR_TR1_S * t) *
                                                        (exp (-FR_TR2_S * t) *
                                                         (exp (-FR_TR3_S * t) *
                                                          (exp (-FR_B1_S * t) *
                                                           ((1 −
                                                             exp
                                                               (-FR_B2_F * t)) *
                                                            (1 −
                                                             exp
                                                               (-FR_TL1_HR *
                                                                t)))))) +
                                                        (exp (-FR_TR1_S * t) *
                                                         (exp (-FR_TR2_S * t) *
                                                          (exp
                                                             (-FR_TR3_S * t) *
                                                           (exp
                                                              (-FR_B1_S * t) *
                                                            ((1 −
                                                              exp
                                                                (-FR_B2_F * t)) *
                                                             (1 −
                                                              exp
                                                                (-FR_TL1_CR *
                                                                 t)))))) +
                                                         (exp (-FR_TR1_S * t) *
                                                          (exp
                                                             (-FR_TR2_S * t) *
                                                           (exp
                                                              (-FR_TR3_S * t) *
                                                            (exp
                                                               (-FR_B1_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B2_F *
                                                                  t)) *
                                                              (1 −
                                                               exp
                                                                 (-FR_TL1_FTL *
                                                                  t)))))) +
                                                          (exp
                                                             (-FR_TR1_S * t) *
                                                           (exp
                                                              (-FR_TR2_S * t) *
                                                            (exp
                                                               (-FR_TR3_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B1_F *
                                                                  t)) *
                                                              (exp
                                                                 (-FR_B2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TL2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_B4_S *
                                                                    t) *
                                                                 (1 −
                                                                  exp
                                                                    (-FR_TR5_F *
                                                                     t)))))))) +
                                                           (exp
                                                              (-FR_TR1_S * t) *
                                                            (exp
                                                               (-FR_TR2_S * t) *
                                                             (exp
                                                                (-FR_TR3_S *
                                                                 t) *
                                                              ((1 −
                                                                exp
                                                                  (-FR_B1_F *
                                                                   t)) *
                                                               (exp
                                                                  (-FR_B2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TL2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_B4_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TR5_PF *
                                                                      t)))))))) +
                                                            (exp
                                                               (-FR_TR1_S * t) *
                                                             (exp
                                                                (-FR_TR2_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR3_S *
                                                                  t) *
                                                               ((1 −
                                                                 exp
                                                                   (-FR_B1_F *
                                                                    t)) *
                                                                (exp
                                                                   (-FR_B2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TL2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_B4_F *
                                                                      t))))))) +
                                                             (exp
                                                                (-FR_TR1_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR3_S *
                                                                   t) *
                                                                ((1 −
                                                                  exp
                                                                    (-FR_B1_F *
                                                                     t)) *
                                                                 (exp
                                                                    (-FR_B2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TL2_F *
                                                                      t)))))) +
                                                              (exp
                                                                 (-FR_TR1_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR3_S *
                                                                    t) *
                                                                 ((1 −
                                                                   exp
                                                                     (-FR_B1_F *
                                                                      t)) *
                                                                  (exp
                                                                     (-FR_B2_S *
                                                                      t) *
                                                                   (1 −
                                                                    exp
                                                                      (-FR_TL2_HR *
                                                                       t)))))) +
                                                               (exp
                                                                  (-FR_TR1_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR3_S *
                                                                     t) *
                                                                  ((1 −
                                                                    exp
                                                                      (-FR_B1_F *
                                                                       t)) *
                                                                   (exp
                                                                      (-FR_B2_S *
                                                                       t) *
                                                                    (1 −
                                                                     exp
                                                                       (-FR_TL2_CR *
                                                                        t)))))) +
                                                                (exp
                                                                   (-FR_TR1_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR2_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR3_S *
                                                                      t) *
                                                                   ((1 −
                                                                     exp
                                                                       (-FR_B1_F *
                                                                        t)) *
                                                                    (exp
                                                                       (-FR_B2_S *
                                                                        t) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_TL2_FTL *
                                                                         t)))))) +
                                                                 (exp
                                                                    (-FR_TR1_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR2_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR3_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_B1_F *
                                                                         t)) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_B2_F *
                                                                         t))))) +
                                                                  (exp
                                                                     (-FR_TR1_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR2_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_TR3_F *
                                                                         t)) *
                                                                     (exp
                                                                        (-FR_B1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TL1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_B3_S *
                                                                           t) *
                                                                        (1 −
                                                                         exp
                                                                           (-FR_TR4_F *
                                                                            t))))))) +
                                                                   (exp
                                                                      (-FR_TR1_S *
                                                                       t) *
                                                                    (exp
                                                                       (-FR_TR2_S *
                                                                        t) *
                                                                     ((1 −
                                                                       exp
                                                                         (-FR_TR3_F *
                                                                          t)) *
                                                                      (exp
                                                                         (-FR_B1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TL1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_B3_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TR4_PF *
                                                                             t))))))) +
                                                                    (exp
                                                                       (-FR_TR1_S *
                                                                        t) *
                                                                     (exp
                                                                        (-FR_TR2_S *
                                                                         t) *
                                                                      ((1 −
                                                                        exp
                                                                          (-FR_TR3_F *
                                                                           t)) *
                                                                       (exp
                                                                          (-FR_B1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TL1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_B3_F *
                                                                             t)))))) +
                                                                     (exp
                                                                        (-FR_TR1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TR2_S *
                                                                          t) *
                                                                       ((1 −
                                                                         exp
                                                                           (-FR_TR3_F *
                                                                            t)) *
                                                                        (exp
                                                                           (-FR_B1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TL1_F *
                                                                             t))))) +
                                                                      (exp
                                                                         (-FR_TR1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TR2_S *
                                                                           t) *
                                                                        ((1 −
                                                                          exp
                                                                            (-FR_TR3_F *
                                                                             t)) *
                                                                         (exp
                                                                            (-FR_B1_S *
                                                                             t) *
                                                                          (1 −
                                                                           exp
                                                                             (-FR_TL1_HR *
                                                                              t))))) +
                                                                       (exp
                                                                          (-FR_TR1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TR2_S *
                                                                            t) *
                                                                         ((1 −
                                                                           exp
                                                                             (-FR_TR3_F *
                                                                              t)) *
                                                                          (exp
                                                                             (-FR_B1_S *
                                                                              t) *
                                                                           (1 −
                                                                            exp
                                                                              (-FR_TL1_CR *
                                                                               t))))) +
                                                                        (exp
                                                                           (-FR_TR1_S *
                                                                            t) *
                                                                         (exp
                                                                            (-FR_TR2_S *
                                                                             t) *
                                                                          ((1 −
                                                                            exp
                                                                              (-FR_TR3_F *
                                                                               t)) *
                                                                           (exp
                                                                              (-FR_B1_S *
                                                                               t) *
                                                                            (1 −
                                                                             exp
                                                                               (-FR_TL1_FTL *
                                                                                t))))) +
                                                                         (exp
                                                                            (-FR_TR1_S *
                                                                             t) *
                                                                          (exp
                                                                             (-FR_TR2_S *
                                                                              t) *
                                                                           ((1 −
                                                                             exp
                                                                               (-FR_TR3_PF *
                                                                                t)) *
                                                                            (exp
                                                                               (-FR_B1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TL1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_B3_S *
                                                                                  t) *
                                                                               exp
                                                                                 (-FR_TR4_S *
                                                                                  t)))))) +
                                                                          (exp
                                                                             (-FR_TR1_S *
                                                                              t) *
                                                                           (exp
                                                                              (-FR_TR2_S *
                                                                               t) *
                                                                            ((1 −
                                                                              exp
                                                                                (-FR_TR3_PF *
                                                                                 t)) *
                                                                             (exp
                                                                                (-FR_B1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TL1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_B3_S *
                                                                                   t) *
                                                                                (1 −
                                                                                 exp
                                                                                   (-FR_TR4_F *
                                                                                    t))))))) +
                                                                           (exp
                                                                              (-FR_TR1_S *
                                                                               t) *
                                                                            (exp
                                                                               (-FR_TR2_S *
                                                                                t) *
                                                                             ((1 −
                                                                               exp
                                                                                 (-FR_TR3_PF *
                                                                                  t)) *
                                                                              (exp
                                                                                 (-FR_B1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TL1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_B3_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TR4_PF *
                                                                                     t))))))) +
                                                                            (exp
                                                                               (-FR_TR1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TR2_S *
                                                                                 t) *
                                                                              ((1 −
                                                                                exp
                                                                                  (-FR_TR3_PF *
                                                                                   t)) *
                                                                               (exp
                                                                                  (-FR_B1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TL1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_B3_F *
                                                                                     t)))))) +
                                                                             (exp
                                                                                (-FR_TR1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TR2_S *
                                                                                  t) *
                                                                               ((1 −
                                                                                 exp
                                                                                   (-FR_TR3_PF *
                                                                                    t)) *
                                                                                (exp
                                                                                   (-FR_B1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TL1_F *
                                                                                     t))))) +
                                                                              (exp
                                                                                 (-FR_TR1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TR2_S *
                                                                                   t) *
                                                                                ((1 −
                                                                                  exp
                                                                                    (-FR_TR3_PF *
                                                                                     t)) *
                                                                                 (exp
                                                                                    (-FR_B1_S *
                                                                                     t) *
                                                                                  (1 −
                                                                                   exp
                                                                                     (-FR_TL1_HR *
                                                                                      t))))) +
                                                                               (exp
                                                                                  (-FR_TR1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TR2_S *
                                                                                    t) *
                                                                                 ((1 −
                                                                                   exp
                                                                                     (-FR_TR3_PF *
                                                                                      t)) *
                                                                                  (exp
                                                                                     (-FR_B1_S *
                                                                                      t) *
                                                                                   (1 −
                                                                                    exp
                                                                                      (-FR_TL1_CR *
                                                                                       t))))) +
                                                                                (exp
                                                                                   (-FR_TR1_S *
                                                                                    t) *
                                                                                 (exp
                                                                                    (-FR_TR2_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR3_PF *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_B1_S *
                                                                                       t) *
                                                                                    (1 −
                                                                                     exp
                                                                                       (-FR_TL1_FTL *
                                                                                        t))))) +
                                                                                 (exp
                                                                                    (-FR_TR1_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR2_F *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_TR3_S *
                                                                                       t) *
                                                                                    (exp
                                                                                       (-FR_B2_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_TL2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B4_S *
                                                                                          t) *
                                                                                       exp
                                                                                         (-FR_TR5_S *
                                                                                          t)))))) +
                                                                                  (exp
                                                                                     (-FR_TR1_S *
                                                                                      t) *
                                                                                   ((1 −
                                                                                     exp
                                                                                       (-FR_TR2_F *
                                                                                        t)) *
                                                                                    (exp
                                                                                       (-FR_TR3_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_B2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_TL2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B4_S *
                                                                                           t) *
                                                                                        (1 −
                                                                                         exp
                                                                                           (-FR_TR5_F *
                                                                                            t))))))) +
                                                                                   (exp
                                                                                      (-FR_TR1_S *
                                                                                       t) *
                                                                                    ((1 −
                                                                                      exp
                                                                                        (-FR_TR2_F *
                                                                                         t)) *
                                                                                     (exp
                                                                                        (-FR_TR3_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_TL2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B4_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TR5_PF *
                                                                                             t))))))) +
                                                                                    (exp
                                                                                       (-FR_TR1_S *
                                                                                        t) *
                                                                                     ((1 −
                                                                                       exp
                                                                                         (-FR_TR2_F *
                                                                                          t)) *
                                                                                      (exp
                                                                                         (-FR_TR3_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_TL2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_B4_F *
                                                                                             t)))))) +
                                                                                     (exp
                                                                                        (-FR_TR1_S *
                                                                                         t) *
                                                                                      ((1 −
                                                                                        exp
                                                                                          (-FR_TR2_F *
                                                                                           t)) *
                                                                                       (exp
                                                                                          (-FR_TR3_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TL2_F *
                                                                                             t))))) +
                                                                                      (exp
                                                                                         (-FR_TR1_S *
                                                                                          t) *
                                                                                       ((1 −
                                                                                         exp
                                                                                           (-FR_TR2_F *
                                                                                            t)) *
                                                                                        (exp
                                                                                           (-FR_TR3_S *
                                                                                            t) *
                                                                                         (exp
                                                                                            (-FR_B2_S *
                                                                                             t) *
                                                                                          (1 −
                                                                                           exp
                                                                                             (-FR_TL2_HR *
                                                                                              t))))) +
                                                                                       (exp
                                                                                          (-FR_TR1_S *
                                                                                           t) *
                                                                                        ((1 −
                                                                                          exp
                                                                                            (-FR_TR2_F *
                                                                                             t)) *
                                                                                         (exp
                                                                                            (-FR_TR3_S *
                                                                                             t) *
                                                                                          (exp
                                                                                             (-FR_B2_S *
                                                                                              t) *
                                                                                           (1 −
                                                                                            exp
                                                                                              (-FR_TL2_CR *
                                                                                               t))))) +
                                                                                        (exp
                                                                                           (-FR_TR1_S *
                                                                                            t) *
                                                                                         ((1 −
                                                                                           exp
                                                                                             (-FR_TR2_F *
                                                                                              t)) *
                                                                                          (exp
                                                                                             (-FR_TR3_S *
                                                                                              t) *
                                                                                           (exp
                                                                                              (-FR_B2_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TL2_FTL *
                                                                                                t))))) +
                                                                                         (exp
                                                                                            (-FR_TR1_S *
                                                                                             t) *
                                                                                          ((1 −
                                                                                            exp
                                                                                              (-FR_TR2_F *
                                                                                               t)) *
                                                                                           (exp
                                                                                              (-FR_TR3_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_B2_F *
                                                                                                t)))) +
                                                                                          (exp
                                                                                             (-FR_TR1_S *
                                                                                              t) *
                                                                                           ((1 −
                                                                                             exp
                                                                                               (-FR_TR2_F *
                                                                                                t)) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TR3_F *
                                                                                                t))) +
                                                                                           (exp
                                                                                              (-FR_TR1_S *
                                                                                               t) *
                                                                                            ((1 −
                                                                                              exp
                                                                                                (-FR_TR2_PF *
                                                                                                 t)) *
                                                                                             (exp
                                                                                                (-FR_TR3_S *
                                                                                                 t) *
                                                                                              (exp
                                                                                                 (-FR_B2_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_TL2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B4_S *
                                                                                                    t) *
                                                                                                 exp
                                                                                                   (-FR_TR5_S *
                                                                                                    t)))))) +
                                                                                            (exp
                                                                                               (-FR_TR1_S *
                                                                                                t) *
                                                                                             ((1 −
                                                                                               exp
                                                                                                 (-FR_TR2_PF *
                                                                                                  t)) *
                                                                                              (exp
                                                                                                 (-FR_TR3_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_B2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_TL2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B4_S *
                                                                                                     t) *
                                                                                                  (1 −
                                                                                                   exp
                                                                                                     (-FR_TR5_F *
                                                                                                      t))))))) +
                                                                                             (exp
                                                                                                (-FR_TR1_S *
                                                                                                 t) *
                                                                                              ((1 −
                                                                                                exp
                                                                                                  (-FR_TR2_PF *
                                                                                                   t)) *
                                                                                               (exp
                                                                                                  (-FR_TR3_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_TL2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B4_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TR5_PF *
                                                                                                       t))))))) +
                                                                                              (exp
                                                                                                 (-FR_TR1_S *
                                                                                                  t) *
                                                                                               ((1 −
                                                                                                 exp
                                                                                                   (-FR_TR2_PF *
                                                                                                    t)) *
                                                                                                (exp
                                                                                                   (-FR_TR3_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_TL2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_B4_F *
                                                                                                       t)))))) +
                                                                                               (exp
                                                                                                  (-FR_TR1_S *
                                                                                                   t) *
                                                                                                ((1 −
                                                                                                  exp
                                                                                                    (-FR_TR2_PF *
                                                                                                     t)) *
                                                                                                 (exp
                                                                                                    (-FR_TR3_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TL2_F *
                                                                                                       t))))) +
                                                                                                (exp
                                                                                                   (-FR_TR1_S *
                                                                                                    t) *
                                                                                                 ((1 −
                                                                                                   exp
                                                                                                     (-FR_TR2_PF *
                                                                                                      t)) *
                                                                                                  (exp
                                                                                                     (-FR_TR3_S *
                                                                                                      t) *
                                                                                                   (exp
                                                                                                      (-FR_B2_S *
                                                                                                       t) *
                                                                                                    (1 −
                                                                                                     exp
                                                                                                       (-FR_TL2_HR *
                                                                                                        t))))) +
                                                                                                 (exp
                                                                                                    (-FR_TR1_S *
                                                                                                     t) *
                                                                                                  ((1 −
                                                                                                    exp
                                                                                                      (-FR_TR2_PF *
                                                                                                       t)) *
                                                                                                   (exp
                                                                                                      (-FR_TR3_S *
                                                                                                       t) *
                                                                                                    (exp
                                                                                                       (-FR_B2_S *
                                                                                                        t) *
                                                                                                     (1 −
                                                                                                      exp
                                                                                                        (-FR_TL2_CR *
                                                                                                         t))))) +
                                                                                                  (exp
                                                                                                     (-FR_TR1_S *
                                                                                                      t) *
                                                                                                   ((1 −
                                                                                                     exp
                                                                                                       (-FR_TR2_PF *
                                                                                                        t)) *
                                                                                                    (exp
                                                                                                       (-FR_TR3_S *
                                                                                                        t) *
                                                                                                     (exp
                                                                                                        (-FR_B2_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TL2_FTL *
                                                                                                          t))))) +
                                                                                                   (exp
                                                                                                      (-FR_TR1_S *
                                                                                                       t) *
                                                                                                    ((1 −
                                                                                                      exp
                                                                                                        (-FR_TR2_PF *
                                                                                                         t)) *
                                                                                                     (exp
                                                                                                        (-FR_TR3_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_B2_F *
                                                                                                          t)))) +
                                                                                                    (exp
                                                                                                       (-FR_TR1_S *
                                                                                                        t) *
                                                                                                     ((1 −
                                                                                                       exp
                                                                                                         (-FR_TR2_PF *
                                                                                                          t)) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR3_F *
                                                                                                          t))) +
                                                                                                     (exp
                                                                                                        (-FR_TR1_S *
                                                                                                         t) *
                                                                                                      ((1 −
                                                                                                        exp
                                                                                                          (-FR_TR2_PF *
                                                                                                           t)) *
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR3_PF *
                                                                                                           t))) +
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR1_F *
                                                                                                          t) +
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR1_PF *
                                                                                                           t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * 80 * 115,000)/115,000 * 8760``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``ENS``
``1345 * (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_F * t)) * exp (-FR_TR5_S * t)))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * exp (-FR_TR5_S * t)))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * exp (-FR_TR4_S * t))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              ((1 − exp (-FR_B3_F * t)) *
               (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              ((1 − exp (-FR_TL2_F * t)) *
               (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               ((1 − exp (-FR_TL2_HR * t)) *
                (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                ((1 − exp (-FR_TL2_CR * t)) *
                 (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_FTL * t)) *
                  (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (exp (-FR_B1_S * t) *
                (exp (-FR_B2_S * t) *
                 ((1 − exp (-FR_TL1_F * t)) *
                  (exp (-FR_TL2_S * t) *
                   (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  ((1 − exp (-FR_TL1_HR * t)) *
                   (exp (-FR_TL2_S * t) *
                    (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   ((1 − exp (-FR_TL1_CR * t)) *
                    (exp (-FR_TL2_S * t) *
                     (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    ((1 − exp (-FR_TL1_FTL * t)) *
                     (exp (-FR_TL2_S * t) *
                      (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    ((1 − exp (-FR_B2_F * t)) *
                     (exp (-FR_TL1_S * t) *
                      (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    ((1 − exp (-FR_B1_F * t)) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL2_S * t) *
                       (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    ((1 − exp (-FR_TR3_F * t)) *
                     (exp (-FR_B1_S * t) * exp (-FR_TL1_S * t)))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     ((1 − exp (-FR_TR3_F * t)) * (1 − exp (-FR_B1_F * t)))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      ((1 − exp (-FR_TR3_PF * t)) * (1 − exp (-FR_B1_F * t)))) +
                     exp (-FR_TR1_S * t) *
                     ((1 − exp (-FR_TR2_F * t)) * (1 − exp (-FR_TR3_PF * t)))))))))))))))))))) * 40 +
  2690 * exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_F * t)))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              (exp (-FR_B3_S * t) *
               ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_PF * t)))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              (exp (-FR_TL2_S * t) *
               ((1 − exp (-FR_B3_F * t)) *
                (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_F * t)))))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               (exp (-FR_TL2_S * t) *
                ((1 − exp (-FR_B3_F * t)) *
                 (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_PF * t)))))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                (exp (-FR_TL2_S * t) *
                 ((1 − exp (-FR_B3_F * t)) * (1 − exp (-FR_B4_F * t))))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_F * t)) *
                  (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (RELIABILITY p B1 t *
                (RELIABILITY p B2 t *
                 (exp (-FR_TL1_S * t) *
                  ((1 − exp (-FR_TL2_F * t)) *
                   (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  (exp (-FR_TL1_S * t) *
                   ((1 − exp (-FR_TL2_F * t)) * (1 − exp (-FR_B3_F * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   (exp (-FR_TL1_S * t) *
                    ((1 − exp (-FR_TL2_HR * t)) *
                     (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    (exp (-FR_TL1_S * t) *
                     ((1 − exp (-FR_TL2_HR * t)) *
                      (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    (exp (-FR_B2_S * t) *
                     (exp (-FR_TL1_S * t) *
                      ((1 − exp (-FR_TL2_HR * t)) * (1 − exp (-FR_B3_F * t)))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    (exp (-FR_B1_S * t) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL1_S * t) *
                       ((1 − exp (-FR_TL2_CR * t)) *
                        (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    (exp (-FR_TR3_S * t) *
                     (exp (-FR_B1_S * t) *
                      (exp (-FR_B2_S * t) *
                       (exp (-FR_TL1_S * t) *
                        ((1 − exp (-FR_TL2_CR * t)) *
                         (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     (exp (-FR_TR3_S * t) *
                      (exp (-FR_B1_S * t) *
                       (exp (-FR_B2_S * t) *
                        (exp (-FR_TL1_S * t) *
                         ((1 − exp (-FR_TL2_CR * t)) *
                          (1 − exp (-FR_B3_F * t)))))))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      (exp (-FR_TR3_S * t) *
                       (exp (-FR_B1_S * t) *
                        (exp (-FR_B2_S * t) *
                         (exp (-FR_TL1_S * t) *
                          ((1 − exp (-FR_TL2_FTL * t)) *
                           (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                     (exp (-FR_TR1_S * t) *
                      (exp (-FR_TR2_S * t) *
                       (exp (-FR_TR3_S * t) *
                        (exp (-FR_B1_S * t) *
                         (exp (-FR_B2_S * t) *
                          (exp (-FR_TL1_S * t) *
                           ((1 − exp (-FR_TL2_FTL * t)) *
                            (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                      (exp (-FR_TR1_S * t) *
                       (exp (-FR_TR2_S * t) *
                        (exp (-FR_TR3_S * t) *
                         (exp (-FR_B1_S * t) *
                          (exp (-FR_B2_S * t) *
                           (exp (-FR_TL1_S * t) *
                            ((1 − exp (-FR_TL2_FTL * t)) *
                             (1 − exp (-FR_B3_F * t)))))))) +
                       (exp (-FR_TR1_S * t) *
                        (exp (-FR_TR2_S * t) *
                         (exp (-FR_TR3_S * t) *
                          (exp (-FR_B1_S * t) *
                           (exp (-FR_B2_S * t) *
                            ((1 − exp (-FR_TL1_F * t)) *
                             (exp (-FR_TL2_S * t) *
                              (exp (-FR_B4_S * t) *
                               (1 − exp (-FR_TR5_F * t))))))))) +
                        (exp (-FR_TR1_S * t) *
                         (exp (-FR_TR2_S * t) *
                          (exp (-FR_TR3_S * t) *
                           (exp (-FR_B1_S * t) *
                            (exp (-FR_B2_S * t) *
                             ((1 − exp (-FR_TL1_F * t)) *
                              (exp (-FR_TL2_S * t) *
                               (exp (-FR_B4_S * t) *
                                (1 − exp (-FR_TR5_PF * t))))))))) +
                         (exp (-FR_TR1_S * t) *
                          (exp (-FR_TR2_S * t) *
                           (exp (-FR_TR3_S * t) *
                            (exp (-FR_B1_S * t) *
                             (exp (-FR_B2_S * t) *
                              ((1 − exp (-FR_TL1_F * t)) *
                               (exp (-FR_TL2_S * t) *
                                (1 − exp (-FR_B4_F * t)))))))) +
                          (exp (-FR_TR1_S * t) *
                           (exp (-FR_TR2_S * t) *
                            (exp (-FR_TR3_S * t) *
                             (exp (-FR_B1_S * t) *
                              (exp (-FR_B2_S * t) *
                               ((1 − exp (-FR_TL1_F * t)) *
                                (1 − exp (-FR_TL2_F * t))))))) +
                           (exp (-FR_TR1_S * t) *
                            (exp (-FR_TR2_S * t) *
                             (exp (-FR_TR3_S * t) *
                              (exp (-FR_B1_S * t) *
                               (exp (-FR_B2_S * t) *
                                ((1 − exp (-FR_TL1_F * t)) *
                                 (1 − exp (-FR_TL2_HR * t))))))) +
                            (exp (-FR_TR1_S * t) *
                             (exp (-FR_TR2_S * t) *
                              (exp (-FR_TR3_S * t) *
                               (exp (-FR_B1_S * t) *
                                (exp (-FR_B2_S * t) *
                                 ((1 − exp (-FR_TL1_F * t)) *
                                  (1 − exp (-FR_TL2_CR * t))))))) +
                             (exp (-FR_TR1_S * t) *
                              (exp (-FR_TR2_S * t) *
                               (exp (-FR_TR3_S * t) *
                                (exp (-FR_B1_S * t) *
                                 (exp (-FR_B2_S * t) *
                                  ((1 − exp (-FR_TL1_F * t)) *
                                   (1 − exp (-FR_TL2_FTL * t))))))) +
                              (exp (-FR_TR1_S * t) *
                               (exp (-FR_TR2_S * t) *
                                (exp (-FR_TR3_S * t) *
                                 (exp (-FR_B1_S * t) *
                                  (exp (-FR_B2_S * t) *
                                   ((1 − exp (-FR_TL1_HR * t)) *
                                    (exp (-FR_TL2_S * t) *
                                     (exp (-FR_B4_S * t) *
                                      (1 − exp (-FR_TR5_F * t))))))))) +
                               (exp (-FR_TR1_S * t) *
                                (exp (-FR_TR2_S * t) *
                                 (exp (-FR_TR3_S * t) *
                                  (exp (-FR_B1_S * t) *
                                   (exp (-FR_B2_S * t) *
                                    ((1 − exp (-FR_TL1_HR * t)) *
                                     (exp (-FR_TL2_S * t) *
                                      (exp (-FR_B4_S * t) *
                                       (1 − exp (-FR_TR5_PF * t))))))))) +
                                (exp (-FR_TR1_S * t) *
                                 (exp (-FR_TR2_S * t) *
                                  (exp (-FR_TR3_S * t) *
                                   (exp (-FR_B1_S * t) *
                                    (exp (-FR_B2_S * t) *
                                     ((1 − exp (-FR_TL1_HR * t)) *
                                      (exp (-FR_TL2_S * t) *
                                       (1 − exp (-FR_B4_F * t)))))))) +
                                 (exp (-FR_TR1_S * t) *
                                  (exp (-FR_TR2_S * t) *
                                   (exp (-FR_TR3_S * t) *
                                    (exp (-FR_B1_S * t) *
                                     (exp (-FR_B2_S * t) *
                                      ((1 − exp (-FR_TL1_HR * t)) *
                                       (1 − exp (-FR_TL2_F * t))))))) +
                                  (exp (-FR_TR1_S * t) *
                                   (exp (-FR_TR2_S * t) *
                                    (exp (-FR_TR3_S * t) *
                                     (exp (-FR_B1_S * t) *
                                      (exp (-FR_B2_S * t) *
                                       ((1 − exp (-FR_TL1_HR * t)) *
                                        (1 − exp (-FR_TL2_HR * t))))))) +
                                   (exp (-FR_TR1_S * t) *
                                    (exp (-FR_TR2_S * t) *
                                     (exp (-FR_TR3_S * t) *
                                      (exp (-FR_B1_S * t) *
                                       (exp (-FR_B2_S * t) *
                                        ((1 − exp (-FR_TL1_HR * t)) *
                                         (1 − exp (-FR_TL2_CR * t))))))) +
                                    (exp (-FR_TR1_S * t) *
                                     (exp (-FR_TR2_S * t) *
                                      (exp (-FR_TR3_S * t) *
                                       (exp (-FR_B1_S * t) *
                                        (exp (-FR_B2_S * t) *
                                         ((1 − exp (-FR_TL1_HR * t)) *
                                          (1 − exp (-FR_TL2_FTL * t))))))) +
                                     (exp (-FR_TR1_S * t) *
                                      (exp (-FR_TR2_S * t) *
                                       (exp (-FR_TR3_S * t) *
                                        (exp (-FR_B1_S * t) *
                                         (exp (-FR_B2_S * t) *
                                          ((1 − exp (-FR_TL1_CR * t)) *
                                           (exp (-FR_TL2_S * t) *
                                            (exp (-FR_B4_S * t) *
                                             (1 − exp (-FR_TR5_F * t))))))))) +
                                      (exp (-FR_TR1_S * t) *
                                       (exp (-FR_TR2_S * t) *
                                        (exp (-FR_TR3_S * t) *
                                         (exp (-FR_B1_S * t) *
                                          (exp (-FR_B2_S * t) *
                                           ((1 − exp (-FR_TL1_CR * t)) *
                                            (exp (-FR_TL2_S * t) *
                                             (exp (-FR_B4_S * t) *
                                              (1 − exp (-FR_TR5_PF * t))))))))) +
                                       (exp (-FR_TR1_S * t) *
                                        (exp (-FR_TR2_S * t) *
                                         (exp (-FR_TR3_S * t) *
                                          (exp (-FR_B1_S * t) *
                                           (exp (-FR_B2_S * t) *
                                            ((1 − exp (-FR_TL1_CR * t)) *
                                             (exp (-FR_TL2_S * t) *
                                              (1 − exp (-FR_B4_F * t)))))))) +
                                        (exp (-FR_TR1_S * t) *
                                         (exp (-FR_TR2_S * t) *
                                          (exp (-FR_TR3_S * t) *
                                           (exp (-FR_B1_S * t) *
                                            (exp (-FR_B2_S * t) *
                                             ((1 − exp (-FR_TL1_CR * t)) *
                                              (1 − exp (-FR_TL2_F * t))))))) +
                                         (exp (-FR_TR1_S * t) *
                                          (exp (-FR_TR2_S * t) *
                                           (exp (-FR_TR3_S * t) *
                                            (exp (-FR_B1_S * t) *
                                             (exp (-FR_B2_S * t) *
                                              ((1 − exp (-FR_TL1_CR * t)) *
                                               (1 − exp (-FR_TL2_HR * t))))))) +
                                          (exp (-FR_TR1_S * t) *
                                           (exp (-FR_TR2_S * t) *
                                            (exp (-FR_TR3_S * t) *
                                             (exp (-FR_B1_S * t) *
                                              (exp (-FR_B2_S * t) *
                                               ((1 − exp (-FR_TL1_CR * t)) *
                                                (1 − exp (-FR_TL2_CR * t))))))) +
                                           (exp (-FR_TR1_S * t) *
                                            (exp (-FR_TR2_S * t) *
                                             (exp (-FR_TR3_S * t) *
                                              (exp (-FR_B1_S * t) *
                                               (exp (-FR_B2_S * t) *
                                                ((1 − exp (-FR_TL1_CR * t)) *
                                                 (1 − exp (-FR_TL2_FTL * t))))))) +
                                            (exp (-FR_TR1_S * t) *
                                             (exp (-FR_TR2_S * t) *
                                              (exp (-FR_TR3_S * t) *
                                               (exp (-FR_B1_S * t) *
                                                (exp (-FR_B2_S * t) *
                                                 ((1 − exp (-FR_TL1_FTL * t)) *
                                                  (exp (-FR_TL2_S * t) *
                                                   (exp (-FR_B4_S * t) *
                                                    (1 − exp (-FR_TR5_F * t))))))))) +
                                             (exp (-FR_TR1_S * t) *
                                              (exp (-FR_TR2_S * t) *
                                               (exp (-FR_TR3_S * t) *
                                                (exp (-FR_B1_S * t) *
                                                 (exp (-FR_B2_S * t) *
                                                  ((1 − exp (-FR_TL1_FTL * t)) *
                                                   (exp (-FR_TL2_S * t) *
                                                    (exp (-FR_B4_S * t) *
                                                     (1 −
                                                      exp (-FR_TR5_PF * t))))))))) +
                                              (exp (-FR_TR1_S * t) *
                                               (exp (-FR_TR2_S * t) *
                                                (exp (-FR_TR3_S * t) *
                                                 (exp (-FR_B1_S * t) *
                                                  (exp (-FR_B2_S * t) *
                                                   ((1 −
                                                     exp (-FR_TL1_FTL * t)) *
                                                    (exp (-FR_TL2_S * t) *
                                                     (1 − exp (-FR_B4_F * t)))))))) +
                                               (exp (-FR_TR1_S * t) *
                                                (exp (-FR_TR2_S * t) *
                                                 (exp (-FR_TR3_S * t) *
                                                  (exp (-FR_B1_S * t) *
                                                   (exp (-FR_B2_S * t) *
                                                    ((1 −
                                                      exp (-FR_TL1_FTL * t)) *
                                                     (1 − exp (-FR_TL2_F * t))))))) +
                                                (exp (-FR_TR1_S * t) *
                                                 (exp (-FR_TR2_S * t) *
                                                  (exp (-FR_TR3_S * t) *
                                                   (exp (-FR_B1_S * t) *
                                                    (exp (-FR_B2_S * t) *
                                                     ((1 −
                                                       exp (-FR_TL1_FTL * t)) *
                                                      (1 −
                                                       exp (-FR_TL2_HR * t))))))) +
                                                 (exp (-FR_TR1_S * t) *
                                                  (exp (-FR_TR2_S * t) *
                                                   (exp (-FR_TR3_S * t) *
                                                    (exp (-FR_B1_S * t) *
                                                     (exp (-FR_B2_S * t) *
                                                      ((1 −
                                                        exp (-FR_TL1_FTL * t)) *
                                                       (1 −
                                                        exp (-FR_TL2_CR * t))))))) +
                                                  (exp (-FR_TR1_S * t) *
                                                   (exp (-FR_TR2_S * t) *
                                                    (exp (-FR_TR3_S * t) *
                                                     (exp (-FR_B1_S * t) *
                                                      (exp (-FR_B2_S * t) *
                                                       ((1 −
                                                         exp
                                                           (-FR_TL1_FTL * t)) *
                                                        (1 −
                                                         exp
                                                           (-FR_TL2_FTL * t))))))) +
                                                   (exp (-FR_TR1_S * t) *
                                                    (exp (-FR_TR2_S * t) *
                                                     (exp (-FR_TR3_S * t) *
                                                      (exp (-FR_B1_S * t) *
                                                       ((1 −
                                                         exp (-FR_B2_F * t)) *
                                                        (exp (-FR_TL1_S * t) *
                                                         (exp (-FR_B3_S * t) *
                                                          (1 −
                                                           exp
                                                             (-FR_TR4_F * t)))))))) +
                                                    (exp (-FR_TR1_S * t) *
                                                     (exp (-FR_TR2_S * t) *
                                                      (exp (-FR_TR3_S * t) *
                                                       (exp (-FR_B1_S * t) *
                                                        ((1 −
                                                          exp (-FR_B2_F * t)) *
                                                         (exp (-FR_TL1_S * t) *
                                                          (exp (-FR_B3_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_TR4_PF * t)))))))) +
                                                     (exp (-FR_TR1_S * t) *
                                                      (exp (-FR_TR2_S * t) *
                                                       (exp (-FR_TR3_S * t) *
                                                        (exp (-FR_B1_S * t) *
                                                         ((1 −
                                                           exp (-FR_B2_F * t)) *
                                                          (exp
                                                             (-FR_TL1_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_B3_F * t))))))) +
                                                      (exp (-FR_TR1_S * t) *
                                                       (exp (-FR_TR2_S * t) *
                                                        (exp (-FR_TR3_S * t) *
                                                         (exp (-FR_B1_S * t) *
                                                          ((1 −
                                                            exp
                                                              (-FR_B2_F * t)) *
                                                           (1 −
                                                            exp
                                                              (-FR_TL1_F * t)))))) +
                                                       (exp (-FR_TR1_S * t) *
                                                        (exp (-FR_TR2_S * t) *
                                                         (exp (-FR_TR3_S * t) *
                                                          (exp (-FR_B1_S * t) *
                                                           ((1 −
                                                             exp
                                                               (-FR_B2_F * t)) *
                                                            (1 −
                                                             exp
                                                               (-FR_TL1_HR *
                                                                t)))))) +
                                                        (exp (-FR_TR1_S * t) *
                                                         (exp (-FR_TR2_S * t) *
                                                          (exp
                                                             (-FR_TR3_S * t) *
                                                           (exp
                                                              (-FR_B1_S * t) *
                                                            ((1 −
                                                              exp
                                                                (-FR_B2_F * t)) *
                                                             (1 −
                                                              exp
                                                                (-FR_TL1_CR *
                                                                 t)))))) +
                                                         (exp (-FR_TR1_S * t) *
                                                          (exp
                                                             (-FR_TR2_S * t) *
                                                           (exp
                                                              (-FR_TR3_S * t) *
                                                            (exp
                                                               (-FR_B1_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B2_F *
                                                                  t)) *
                                                              (1 −
                                                               exp
                                                                 (-FR_TL1_FTL *
                                                                  t)))))) +
                                                          (exp
                                                             (-FR_TR1_S * t) *
                                                           (exp
                                                              (-FR_TR2_S * t) *
                                                            (exp
                                                               (-FR_TR3_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B1_F *
                                                                  t)) *
                                                              (exp
                                                                 (-FR_B2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TL2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_B4_S *
                                                                    t) *
                                                                 (1 −
                                                                  exp
                                                                    (-FR_TR5_F *
                                                                     t)))))))) +
                                                           (exp
                                                              (-FR_TR1_S * t) *
                                                            (exp
                                                               (-FR_TR2_S * t) *
                                                             (exp
                                                                (-FR_TR3_S *
                                                                 t) *
                                                              ((1 −
                                                                exp
                                                                  (-FR_B1_F *
                                                                   t)) *
                                                               (exp
                                                                  (-FR_B2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TL2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_B4_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TR5_PF *
                                                                      t)))))))) +
                                                            (exp
                                                               (-FR_TR1_S * t) *
                                                             (exp
                                                                (-FR_TR2_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR3_S *
                                                                  t) *
                                                               ((1 −
                                                                 exp
                                                                   (-FR_B1_F *
                                                                    t)) *
                                                                (exp
                                                                   (-FR_B2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TL2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_B4_F *
                                                                      t))))))) +
                                                             (exp
                                                                (-FR_TR1_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR3_S *
                                                                   t) *
                                                                ((1 −
                                                                  exp
                                                                    (-FR_B1_F *
                                                                     t)) *
                                                                 (exp
                                                                    (-FR_B2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TL2_F *
                                                                      t)))))) +
                                                              (exp
                                                                 (-FR_TR1_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR3_S *
                                                                    t) *
                                                                 ((1 −
                                                                   exp
                                                                     (-FR_B1_F *
                                                                      t)) *
                                                                  (exp
                                                                     (-FR_B2_S *
                                                                      t) *
                                                                   (1 −
                                                                    exp
                                                                      (-FR_TL2_HR *
                                                                       t)))))) +
                                                               (exp
                                                                  (-FR_TR1_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR3_S *
                                                                     t) *
                                                                  ((1 −
                                                                    exp
                                                                      (-FR_B1_F *
                                                                       t)) *
                                                                   (exp
                                                                      (-FR_B2_S *
                                                                       t) *
                                                                    (1 −
                                                                     exp
                                                                       (-FR_TL2_CR *
                                                                        t)))))) +
                                                                (exp
                                                                   (-FR_TR1_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR2_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR3_S *
                                                                      t) *
                                                                   ((1 −
                                                                     exp
                                                                       (-FR_B1_F *
                                                                        t)) *
                                                                    (exp
                                                                       (-FR_B2_S *
                                                                        t) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_TL2_FTL *
                                                                         t)))))) +
                                                                 (exp
                                                                    (-FR_TR1_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR2_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR3_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_B1_F *
                                                                         t)) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_B2_F *
                                                                         t))))) +
                                                                  (exp
                                                                     (-FR_TR1_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR2_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_TR3_F *
                                                                         t)) *
                                                                     (exp
                                                                        (-FR_B1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TL1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_B3_S *
                                                                           t) *
                                                                        (1 −
                                                                         exp
                                                                           (-FR_TR4_F *
                                                                            t))))))) +
                                                                   (exp
                                                                      (-FR_TR1_S *
                                                                       t) *
                                                                    (exp
                                                                       (-FR_TR2_S *
                                                                        t) *
                                                                     ((1 −
                                                                       exp
                                                                         (-FR_TR3_F *
                                                                          t)) *
                                                                      (exp
                                                                         (-FR_B1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TL1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_B3_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TR4_PF *
                                                                             t))))))) +
                                                                    (exp
                                                                       (-FR_TR1_S *
                                                                        t) *
                                                                     (exp
                                                                        (-FR_TR2_S *
                                                                         t) *
                                                                      ((1 −
                                                                        exp
                                                                          (-FR_TR3_F *
                                                                           t)) *
                                                                       (exp
                                                                          (-FR_B1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TL1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_B3_F *
                                                                             t)))))) +
                                                                     (exp
                                                                        (-FR_TR1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TR2_S *
                                                                          t) *
                                                                       ((1 −
                                                                         exp
                                                                           (-FR_TR3_F *
                                                                            t)) *
                                                                        (exp
                                                                           (-FR_B1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TL1_F *
                                                                             t))))) +
                                                                      (exp
                                                                         (-FR_TR1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TR2_S *
                                                                           t) *
                                                                        ((1 −
                                                                          exp
                                                                            (-FR_TR3_F *
                                                                             t)) *
                                                                         (exp
                                                                            (-FR_B1_S *
                                                                             t) *
                                                                          (1 −
                                                                           exp
                                                                             (-FR_TL1_HR *
                                                                              t))))) +
                                                                       (exp
                                                                          (-FR_TR1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TR2_S *
                                                                            t) *
                                                                         ((1 −
                                                                           exp
                                                                             (-FR_TR3_F *
                                                                              t)) *
                                                                          (exp
                                                                             (-FR_B1_S *
                                                                              t) *
                                                                           (1 −
                                                                            exp
                                                                              (-FR_TL1_CR *
                                                                               t))))) +
                                                                        (exp
                                                                           (-FR_TR1_S *
                                                                            t) *
                                                                         (exp
                                                                            (-FR_TR2_S *
                                                                             t) *
                                                                          ((1 −
                                                                            exp
                                                                              (-FR_TR3_F *
                                                                               t)) *
                                                                           (exp
                                                                              (-FR_B1_S *
                                                                               t) *
                                                                            (1 −
                                                                             exp
                                                                               (-FR_TL1_FTL *
                                                                                t))))) +
                                                                         (exp
                                                                            (-FR_TR1_S *
                                                                             t) *
                                                                          (exp
                                                                             (-FR_TR2_S *
                                                                              t) *
                                                                           ((1 −
                                                                             exp
                                                                               (-FR_TR3_PF *
                                                                                t)) *
                                                                            (exp
                                                                               (-FR_B1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TL1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_B3_S *
                                                                                  t) *
                                                                               exp
                                                                                 (-FR_TR4_S *
                                                                                  t)))))) +
                                                                          (exp
                                                                             (-FR_TR1_S *
                                                                              t) *
                                                                           (exp
                                                                              (-FR_TR2_S *
                                                                               t) *
                                                                            ((1 −
                                                                              exp
                                                                                (-FR_TR3_PF *
                                                                                 t)) *
                                                                             (exp
                                                                                (-FR_B1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TL1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_B3_S *
                                                                                   t) *
                                                                                (1 −
                                                                                 exp
                                                                                   (-FR_TR4_F *
                                                                                    t))))))) +
                                                                           (exp
                                                                              (-FR_TR1_S *
                                                                               t) *
                                                                            (exp
                                                                               (-FR_TR2_S *
                                                                                t) *
                                                                             ((1 −
                                                                               exp
                                                                                 (-FR_TR3_PF *
                                                                                  t)) *
                                                                              (exp
                                                                                 (-FR_B1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TL1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_B3_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TR4_PF *
                                                                                     t))))))) +
                                                                            (exp
                                                                               (-FR_TR1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TR2_S *
                                                                                 t) *
                                                                              ((1 −
                                                                                exp
                                                                                  (-FR_TR3_PF *
                                                                                   t)) *
                                                                               (exp
                                                                                  (-FR_B1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TL1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_B3_F *
                                                                                     t)))))) +
                                                                             (exp
                                                                                (-FR_TR1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TR2_S *
                                                                                  t) *
                                                                               ((1 −
                                                                                 exp
                                                                                   (-FR_TR3_PF *
                                                                                    t)) *
                                                                                (exp
                                                                                   (-FR_B1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TL1_F *
                                                                                     t))))) +
                                                                              (exp
                                                                                 (-FR_TR1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TR2_S *
                                                                                   t) *
                                                                                ((1 −
                                                                                  exp
                                                                                    (-FR_TR3_PF *
                                                                                     t)) *
                                                                                 (exp
                                                                                    (-FR_B1_S *
                                                                                     t) *
                                                                                  (1 −
                                                                                   exp
                                                                                     (-FR_TL1_HR *
                                                                                      t))))) +
                                                                               (exp
                                                                                  (-FR_TR1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TR2_S *
                                                                                    t) *
                                                                                 ((1 −
                                                                                   exp
                                                                                     (-FR_TR3_PF *
                                                                                      t)) *
                                                                                  (exp
                                                                                     (-FR_B1_S *
                                                                                      t) *
                                                                                   (1 −
                                                                                    exp
                                                                                      (-FR_TL1_CR *
                                                                                       t))))) +
                                                                                (exp
                                                                                   (-FR_TR1_S *
                                                                                    t) *
                                                                                 (exp
                                                                                    (-FR_TR2_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR3_PF *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_B1_S *
                                                                                       t) *
                                                                                    (1 −
                                                                                     exp
                                                                                       (-FR_TL1_FTL *
                                                                                        t))))) +
                                                                                 (exp
                                                                                    (-FR_TR1_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR2_F *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_TR3_S *
                                                                                       t) *
                                                                                    (exp
                                                                                       (-FR_B2_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_TL2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B4_S *
                                                                                          t) *
                                                                                       exp
                                                                                         (-FR_TR5_S *
                                                                                          t)))))) +
                                                                                  (exp
                                                                                     (-FR_TR1_S *
                                                                                      t) *
                                                                                   ((1 −
                                                                                     exp
                                                                                       (-FR_TR2_F *
                                                                                        t)) *
                                                                                    (exp
                                                                                       (-FR_TR3_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_B2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_TL2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B4_S *
                                                                                           t) *
                                                                                        (1 −
                                                                                         exp
                                                                                           (-FR_TR5_F *
                                                                                            t))))))) +
                                                                                   (exp
                                                                                      (-FR_TR1_S *
                                                                                       t) *
                                                                                    ((1 −
                                                                                      exp
                                                                                        (-FR_TR2_F *
                                                                                         t)) *
                                                                                     (exp
                                                                                        (-FR_TR3_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_TL2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B4_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TR5_PF *
                                                                                             t))))))) +
                                                                                    (exp
                                                                                       (-FR_TR1_S *
                                                                                        t) *
                                                                                     ((1 −
                                                                                       exp
                                                                                         (-FR_TR2_F *
                                                                                          t)) *
                                                                                      (exp
                                                                                         (-FR_TR3_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_TL2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_B4_F *
                                                                                             t)))))) +
                                                                                     (exp
                                                                                        (-FR_TR1_S *
                                                                                         t) *
                                                                                      ((1 −
                                                                                        exp
                                                                                          (-FR_TR2_F *
                                                                                           t)) *
                                                                                       (exp
                                                                                          (-FR_TR3_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TL2_F *
                                                                                             t))))) +
                                                                                      (exp
                                                                                         (-FR_TR1_S *
                                                                                          t) *
                                                                                       ((1 −
                                                                                         exp
                                                                                           (-FR_TR2_F *
                                                                                            t)) *
                                                                                        (exp
                                                                                           (-FR_TR3_S *
                                                                                            t) *
                                                                                         (exp
                                                                                            (-FR_B2_S *
                                                                                             t) *
                                                                                          (1 −
                                                                                           exp
                                                                                             (-FR_TL2_HR *
                                                                                              t))))) +
                                                                                       (exp
                                                                                          (-FR_TR1_S *
                                                                                           t) *
                                                                                        ((1 −
                                                                                          exp
                                                                                            (-FR_TR2_F *
                                                                                             t)) *
                                                                                         (exp
                                                                                            (-FR_TR3_S *
                                                                                             t) *
                                                                                          (exp
                                                                                             (-FR_B2_S *
                                                                                              t) *
                                                                                           (1 −
                                                                                            exp
                                                                                              (-FR_TL2_CR *
                                                                                               t))))) +
                                                                                        (exp
                                                                                           (-FR_TR1_S *
                                                                                            t) *
                                                                                         ((1 −
                                                                                           exp
                                                                                             (-FR_TR2_F *
                                                                                              t)) *
                                                                                          (exp
                                                                                             (-FR_TR3_S *
                                                                                              t) *
                                                                                           (exp
                                                                                              (-FR_B2_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TL2_FTL *
                                                                                                t))))) +
                                                                                         (exp
                                                                                            (-FR_TR1_S *
                                                                                             t) *
                                                                                          ((1 −
                                                                                            exp
                                                                                              (-FR_TR2_F *
                                                                                               t)) *
                                                                                           (exp
                                                                                              (-FR_TR3_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_B2_F *
                                                                                                t)))) +
                                                                                          (exp
                                                                                             (-FR_TR1_S *
                                                                                              t) *
                                                                                           ((1 −
                                                                                             exp
                                                                                               (-FR_TR2_F *
                                                                                                t)) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TR3_F *
                                                                                                t))) +
                                                                                           (exp
                                                                                              (-FR_TR1_S *
                                                                                               t) *
                                                                                            ((1 −
                                                                                              exp
                                                                                                (-FR_TR2_PF *
                                                                                                 t)) *
                                                                                             (exp
                                                                                                (-FR_TR3_S *
                                                                                                 t) *
                                                                                              (exp
                                                                                                 (-FR_B2_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_TL2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B4_S *
                                                                                                    t) *
                                                                                                 exp
                                                                                                   (-FR_TR5_S *
                                                                                                    t)))))) +
                                                                                            (exp
                                                                                               (-FR_TR1_S *
                                                                                                t) *
                                                                                             ((1 −
                                                                                               exp
                                                                                                 (-FR_TR2_PF *
                                                                                                  t)) *
                                                                                              (exp
                                                                                                 (-FR_TR3_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_B2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_TL2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B4_S *
                                                                                                     t) *
                                                                                                  (1 −
                                                                                                   exp
                                                                                                     (-FR_TR5_F *
                                                                                                      t))))))) +
                                                                                             (exp
                                                                                                (-FR_TR1_S *
                                                                                                 t) *
                                                                                              ((1 −
                                                                                                exp
                                                                                                  (-FR_TR2_PF *
                                                                                                   t)) *
                                                                                               (exp
                                                                                                  (-FR_TR3_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_TL2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B4_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TR5_PF *
                                                                                                       t))))))) +
                                                                                              (exp
                                                                                                 (-FR_TR1_S *
                                                                                                  t) *
                                                                                               ((1 −
                                                                                                 exp
                                                                                                   (-FR_TR2_PF *
                                                                                                    t)) *
                                                                                                (exp
                                                                                                   (-FR_TR3_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_TL2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_B4_F *
                                                                                                       t)))))) +
                                                                                               (exp
                                                                                                  (-FR_TR1_S *
                                                                                                   t) *
                                                                                                ((1 −
                                                                                                  exp
                                                                                                    (-FR_TR2_PF *
                                                                                                     t)) *
                                                                                                 (exp
                                                                                                    (-FR_TR3_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TL2_F *
                                                                                                       t))))) +
                                                                                                (exp
                                                                                                   (-FR_TR1_S *
                                                                                                    t) *
                                                                                                 ((1 −
                                                                                                   exp
                                                                                                     (-FR_TR2_PF *
                                                                                                      t)) *
                                                                                                  (exp
                                                                                                     (-FR_TR3_S *
                                                                                                      t) *
                                                                                                   (exp
                                                                                                      (-FR_B2_S *
                                                                                                       t) *
                                                                                                    (1 −
                                                                                                     exp
                                                                                                       (-FR_TL2_HR *
                                                                                                        t))))) +
                                                                                                 (exp
                                                                                                    (-FR_TR1_S *
                                                                                                     t) *
                                                                                                  ((1 −
                                                                                                    exp
                                                                                                      (-FR_TR2_PF *
                                                                                                       t)) *
                                                                                                   (exp
                                                                                                      (-FR_TR3_S *
                                                                                                       t) *
                                                                                                    (exp
                                                                                                       (-FR_B2_S *
                                                                                                        t) *
                                                                                                     (1 −
                                                                                                      exp
                                                                                                        (-FR_TL2_CR *
                                                                                                         t))))) +
                                                                                                  (exp
                                                                                                     (-FR_TR1_S *
                                                                                                      t) *
                                                                                                   ((1 −
                                                                                                     exp
                                                                                                       (-FR_TR2_PF *
                                                                                                        t)) *
                                                                                                    (exp
                                                                                                       (-FR_TR3_S *
                                                                                                        t) *
                                                                                                     (exp
                                                                                                        (-FR_B2_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TL2_FTL *
                                                                                                          t))))) +
                                                                                                   (exp
                                                                                                      (-FR_TR1_S *
                                                                                                       t) *
                                                                                                    ((1 −
                                                                                                      exp
                                                                                                        (-FR_TR2_PF *
                                                                                                         t)) *
                                                                                                     (exp
                                                                                                        (-FR_TR3_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_B2_F *
                                                                                                          t)))) +
                                                                                                    (exp
                                                                                                       (-FR_TR1_S *
                                                                                                        t) *
                                                                                                     ((1 −
                                                                                                       exp
                                                                                                         (-FR_TR2_PF *
                                                                                                          t)) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR3_F *
                                                                                                          t))) +
                                                                                                     (exp
                                                                                                        (-FR_TR1_S *
                                                                                                         t) *
                                                                                                      ((1 −
                                                                                                        exp
                                                                                                          (-FR_TR2_PF *
                                                                                                           t)) *
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR3_PF *
                                                                                                           t))) +
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR1_F *
                                                                                                          t) +
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR1_PF *
                                                                                                           t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * 80``;

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``ASCI``
``(1345 * (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_F * t)) * exp (-FR_TR5_S * t)))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * exp (-FR_TR5_S * t)))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * exp (-FR_TR4_S * t))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              ((1 − exp (-FR_B3_F * t)) *
               (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              ((1 − exp (-FR_TL2_F * t)) *
               (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               ((1 − exp (-FR_TL2_HR * t)) *
                (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                ((1 − exp (-FR_TL2_CR * t)) *
                 (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_FTL * t)) *
                  (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (exp (-FR_B1_S * t) *
                (exp (-FR_B2_S * t) *
                 ((1 − exp (-FR_TL1_F * t)) *
                  (exp (-FR_TL2_S * t) *
                   (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  ((1 − exp (-FR_TL1_HR * t)) *
                   (exp (-FR_TL2_S * t) *
                    (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   ((1 − exp (-FR_TL1_CR * t)) *
                    (exp (-FR_TL2_S * t) *
                     (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    ((1 − exp (-FR_TL1_FTL * t)) *
                     (exp (-FR_TL2_S * t) *
                      (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    ((1 − exp (-FR_B2_F * t)) *
                     (exp (-FR_TL1_S * t) *
                      (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    ((1 − exp (-FR_B1_F * t)) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL2_S * t) *
                       (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    ((1 − exp (-FR_TR3_F * t)) *
                     (exp (-FR_B1_S * t) * exp (-FR_TL1_S * t)))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     ((1 − exp (-FR_TR3_F * t)) * (1 − exp (-FR_B1_F * t)))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      ((1 − exp (-FR_TR3_PF * t)) * (1 − exp (-FR_B1_F * t)))) +
                     exp (-FR_TR1_S * t) *
                     ((1 − exp (-FR_TR2_F * t)) * (1 − exp (-FR_TR3_PF * t)))))))))))))))))))) * 40 +
  2690 * exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_F * t)))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              (exp (-FR_B3_S * t) *
               ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_PF * t)))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              (exp (-FR_TL2_S * t) *
               ((1 − exp (-FR_B3_F * t)) *
                (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_F * t)))))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               (exp (-FR_TL2_S * t) *
                ((1 − exp (-FR_B3_F * t)) *
                 (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_PF * t)))))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                (exp (-FR_TL2_S * t) *
                 ((1 − exp (-FR_B3_F * t)) * (1 − exp (-FR_B4_F * t))))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_F * t)) *
                  (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (RELIABILITY p B1 t *
                (RELIABILITY p B2 t *
                 (exp (-FR_TL1_S * t) *
                  ((1 − exp (-FR_TL2_F * t)) *
                   (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  (exp (-FR_TL1_S * t) *
                   ((1 − exp (-FR_TL2_F * t)) * (1 − exp (-FR_B3_F * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   (exp (-FR_TL1_S * t) *
                    ((1 − exp (-FR_TL2_HR * t)) *
                     (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    (exp (-FR_TL1_S * t) *
                     ((1 − exp (-FR_TL2_HR * t)) *
                      (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    (exp (-FR_B2_S * t) *
                     (exp (-FR_TL1_S * t) *
                      ((1 − exp (-FR_TL2_HR * t)) * (1 − exp (-FR_B3_F * t)))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    (exp (-FR_B1_S * t) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL1_S * t) *
                       ((1 − exp (-FR_TL2_CR * t)) *
                        (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    (exp (-FR_TR3_S * t) *
                     (exp (-FR_B1_S * t) *
                      (exp (-FR_B2_S * t) *
                       (exp (-FR_TL1_S * t) *
                        ((1 − exp (-FR_TL2_CR * t)) *
                         (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     (exp (-FR_TR3_S * t) *
                      (exp (-FR_B1_S * t) *
                       (exp (-FR_B2_S * t) *
                        (exp (-FR_TL1_S * t) *
                         ((1 − exp (-FR_TL2_CR * t)) *
                          (1 − exp (-FR_B3_F * t)))))))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      (exp (-FR_TR3_S * t) *
                       (exp (-FR_B1_S * t) *
                        (exp (-FR_B2_S * t) *
                         (exp (-FR_TL1_S * t) *
                          ((1 − exp (-FR_TL2_FTL * t)) *
                           (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                     (exp (-FR_TR1_S * t) *
                      (exp (-FR_TR2_S * t) *
                       (exp (-FR_TR3_S * t) *
                        (exp (-FR_B1_S * t) *
                         (exp (-FR_B2_S * t) *
                          (exp (-FR_TL1_S * t) *
                           ((1 − exp (-FR_TL2_FTL * t)) *
                            (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                      (exp (-FR_TR1_S * t) *
                       (exp (-FR_TR2_S * t) *
                        (exp (-FR_TR3_S * t) *
                         (exp (-FR_B1_S * t) *
                          (exp (-FR_B2_S * t) *
                           (exp (-FR_TL1_S * t) *
                            ((1 − exp (-FR_TL2_FTL * t)) *
                             (1 − exp (-FR_B3_F * t)))))))) +
                       (exp (-FR_TR1_S * t) *
                        (exp (-FR_TR2_S * t) *
                         (exp (-FR_TR3_S * t) *
                          (exp (-FR_B1_S * t) *
                           (exp (-FR_B2_S * t) *
                            ((1 − exp (-FR_TL1_F * t)) *
                             (exp (-FR_TL2_S * t) *
                              (exp (-FR_B4_S * t) *
                               (1 − exp (-FR_TR5_F * t))))))))) +
                        (exp (-FR_TR1_S * t) *
                         (exp (-FR_TR2_S * t) *
                          (exp (-FR_TR3_S * t) *
                           (exp (-FR_B1_S * t) *
                            (exp (-FR_B2_S * t) *
                             ((1 − exp (-FR_TL1_F * t)) *
                              (exp (-FR_TL2_S * t) *
                               (exp (-FR_B4_S * t) *
                                (1 − exp (-FR_TR5_PF * t))))))))) +
                         (exp (-FR_TR1_S * t) *
                          (exp (-FR_TR2_S * t) *
                           (exp (-FR_TR3_S * t) *
                            (exp (-FR_B1_S * t) *
                             (exp (-FR_B2_S * t) *
                              ((1 − exp (-FR_TL1_F * t)) *
                               (exp (-FR_TL2_S * t) *
                                (1 − exp (-FR_B4_F * t)))))))) +
                          (exp (-FR_TR1_S * t) *
                           (exp (-FR_TR2_S * t) *
                            (exp (-FR_TR3_S * t) *
                             (exp (-FR_B1_S * t) *
                              (exp (-FR_B2_S * t) *
                               ((1 − exp (-FR_TL1_F * t)) *
                                (1 − exp (-FR_TL2_F * t))))))) +
                           (exp (-FR_TR1_S * t) *
                            (exp (-FR_TR2_S * t) *
                             (exp (-FR_TR3_S * t) *
                              (exp (-FR_B1_S * t) *
                               (exp (-FR_B2_S * t) *
                                ((1 − exp (-FR_TL1_F * t)) *
                                 (1 − exp (-FR_TL2_HR * t))))))) +
                            (exp (-FR_TR1_S * t) *
                             (exp (-FR_TR2_S * t) *
                              (exp (-FR_TR3_S * t) *
                               (exp (-FR_B1_S * t) *
                                (exp (-FR_B2_S * t) *
                                 ((1 − exp (-FR_TL1_F * t)) *
                                  (1 − exp (-FR_TL2_CR * t))))))) +
                             (exp (-FR_TR1_S * t) *
                              (exp (-FR_TR2_S * t) *
                               (exp (-FR_TR3_S * t) *
                                (exp (-FR_B1_S * t) *
                                 (exp (-FR_B2_S * t) *
                                  ((1 − exp (-FR_TL1_F * t)) *
                                   (1 − exp (-FR_TL2_FTL * t))))))) +
                              (exp (-FR_TR1_S * t) *
                               (exp (-FR_TR2_S * t) *
                                (exp (-FR_TR3_S * t) *
                                 (exp (-FR_B1_S * t) *
                                  (exp (-FR_B2_S * t) *
                                   ((1 − exp (-FR_TL1_HR * t)) *
                                    (exp (-FR_TL2_S * t) *
                                     (exp (-FR_B4_S * t) *
                                      (1 − exp (-FR_TR5_F * t))))))))) +
                               (exp (-FR_TR1_S * t) *
                                (exp (-FR_TR2_S * t) *
                                 (exp (-FR_TR3_S * t) *
                                  (exp (-FR_B1_S * t) *
                                   (exp (-FR_B2_S * t) *
                                    ((1 − exp (-FR_TL1_HR * t)) *
                                     (exp (-FR_TL2_S * t) *
                                      (exp (-FR_B4_S * t) *
                                       (1 − exp (-FR_TR5_PF * t))))))))) +
                                (exp (-FR_TR1_S * t) *
                                 (exp (-FR_TR2_S * t) *
                                  (exp (-FR_TR3_S * t) *
                                   (exp (-FR_B1_S * t) *
                                    (exp (-FR_B2_S * t) *
                                     ((1 − exp (-FR_TL1_HR * t)) *
                                      (exp (-FR_TL2_S * t) *
                                       (1 − exp (-FR_B4_F * t)))))))) +
                                 (exp (-FR_TR1_S * t) *
                                  (exp (-FR_TR2_S * t) *
                                   (exp (-FR_TR3_S * t) *
                                    (exp (-FR_B1_S * t) *
                                     (exp (-FR_B2_S * t) *
                                      ((1 − exp (-FR_TL1_HR * t)) *
                                       (1 − exp (-FR_TL2_F * t))))))) +
                                  (exp (-FR_TR1_S * t) *
                                   (exp (-FR_TR2_S * t) *
                                    (exp (-FR_TR3_S * t) *
                                     (exp (-FR_B1_S * t) *
                                      (exp (-FR_B2_S * t) *
                                       ((1 − exp (-FR_TL1_HR * t)) *
                                        (1 − exp (-FR_TL2_HR * t))))))) +
                                   (exp (-FR_TR1_S * t) *
                                    (exp (-FR_TR2_S * t) *
                                     (exp (-FR_TR3_S * t) *
                                      (exp (-FR_B1_S * t) *
                                       (exp (-FR_B2_S * t) *
                                        ((1 − exp (-FR_TL1_HR * t)) *
                                         (1 − exp (-FR_TL2_CR * t))))))) +
                                    (exp (-FR_TR1_S * t) *
                                     (exp (-FR_TR2_S * t) *
                                      (exp (-FR_TR3_S * t) *
                                       (exp (-FR_B1_S * t) *
                                        (exp (-FR_B2_S * t) *
                                         ((1 − exp (-FR_TL1_HR * t)) *
                                          (1 − exp (-FR_TL2_FTL * t))))))) +
                                     (exp (-FR_TR1_S * t) *
                                      (exp (-FR_TR2_S * t) *
                                       (exp (-FR_TR3_S * t) *
                                        (exp (-FR_B1_S * t) *
                                         (exp (-FR_B2_S * t) *
                                          ((1 − exp (-FR_TL1_CR * t)) *
                                           (exp (-FR_TL2_S * t) *
                                            (exp (-FR_B4_S * t) *
                                             (1 − exp (-FR_TR5_F * t))))))))) +
                                      (exp (-FR_TR1_S * t) *
                                       (exp (-FR_TR2_S * t) *
                                        (exp (-FR_TR3_S * t) *
                                         (exp (-FR_B1_S * t) *
                                          (exp (-FR_B2_S * t) *
                                           ((1 − exp (-FR_TL1_CR * t)) *
                                            (exp (-FR_TL2_S * t) *
                                             (exp (-FR_B4_S * t) *
                                              (1 − exp (-FR_TR5_PF * t))))))))) +
                                       (exp (-FR_TR1_S * t) *
                                        (exp (-FR_TR2_S * t) *
                                         (exp (-FR_TR3_S * t) *
                                          (exp (-FR_B1_S * t) *
                                           (exp (-FR_B2_S * t) *
                                            ((1 − exp (-FR_TL1_CR * t)) *
                                             (exp (-FR_TL2_S * t) *
                                              (1 − exp (-FR_B4_F * t)))))))) +
                                        (exp (-FR_TR1_S * t) *
                                         (exp (-FR_TR2_S * t) *
                                          (exp (-FR_TR3_S * t) *
                                           (exp (-FR_B1_S * t) *
                                            (exp (-FR_B2_S * t) *
                                             ((1 − exp (-FR_TL1_CR * t)) *
                                              (1 − exp (-FR_TL2_F * t))))))) +
                                         (exp (-FR_TR1_S * t) *
                                          (exp (-FR_TR2_S * t) *
                                           (exp (-FR_TR3_S * t) *
                                            (exp (-FR_B1_S * t) *
                                             (exp (-FR_B2_S * t) *
                                              ((1 − exp (-FR_TL1_CR * t)) *
                                               (1 − exp (-FR_TL2_HR * t))))))) +
                                          (exp (-FR_TR1_S * t) *
                                           (exp (-FR_TR2_S * t) *
                                            (exp (-FR_TR3_S * t) *
                                             (exp (-FR_B1_S * t) *
                                              (exp (-FR_B2_S * t) *
                                               ((1 − exp (-FR_TL1_CR * t)) *
                                                (1 − exp (-FR_TL2_CR * t))))))) +
                                           (exp (-FR_TR1_S * t) *
                                            (exp (-FR_TR2_S * t) *
                                             (exp (-FR_TR3_S * t) *
                                              (exp (-FR_B1_S * t) *
                                               (exp (-FR_B2_S * t) *
                                                ((1 − exp (-FR_TL1_CR * t)) *
                                                 (1 − exp (-FR_TL2_FTL * t))))))) +
                                            (exp (-FR_TR1_S * t) *
                                             (exp (-FR_TR2_S * t) *
                                              (exp (-FR_TR3_S * t) *
                                               (exp (-FR_B1_S * t) *
                                                (exp (-FR_B2_S * t) *
                                                 ((1 − exp (-FR_TL1_FTL * t)) *
                                                  (exp (-FR_TL2_S * t) *
                                                   (exp (-FR_B4_S * t) *
                                                    (1 − exp (-FR_TR5_F * t))))))))) +
                                             (exp (-FR_TR1_S * t) *
                                              (exp (-FR_TR2_S * t) *
                                               (exp (-FR_TR3_S * t) *
                                                (exp (-FR_B1_S * t) *
                                                 (exp (-FR_B2_S * t) *
                                                  ((1 − exp (-FR_TL1_FTL * t)) *
                                                   (exp (-FR_TL2_S * t) *
                                                    (exp (-FR_B4_S * t) *
                                                     (1 −
                                                      exp (-FR_TR5_PF * t))))))))) +
                                              (exp (-FR_TR1_S * t) *
                                               (exp (-FR_TR2_S * t) *
                                                (exp (-FR_TR3_S * t) *
                                                 (exp (-FR_B1_S * t) *
                                                  (exp (-FR_B2_S * t) *
                                                   ((1 −
                                                     exp (-FR_TL1_FTL * t)) *
                                                    (exp (-FR_TL2_S * t) *
                                                     (1 − exp (-FR_B4_F * t)))))))) +
                                               (exp (-FR_TR1_S * t) *
                                                (exp (-FR_TR2_S * t) *
                                                 (exp (-FR_TR3_S * t) *
                                                  (exp (-FR_B1_S * t) *
                                                   (exp (-FR_B2_S * t) *
                                                    ((1 −
                                                      exp (-FR_TL1_FTL * t)) *
                                                     (1 − exp (-FR_TL2_F * t))))))) +
                                                (exp (-FR_TR1_S * t) *
                                                 (exp (-FR_TR2_S * t) *
                                                  (exp (-FR_TR3_S * t) *
                                                   (exp (-FR_B1_S * t) *
                                                    (exp (-FR_B2_S * t) *
                                                     ((1 −
                                                       exp (-FR_TL1_FTL * t)) *
                                                      (1 −
                                                       exp (-FR_TL2_HR * t))))))) +
                                                 (exp (-FR_TR1_S * t) *
                                                  (exp (-FR_TR2_S * t) *
                                                   (exp (-FR_TR3_S * t) *
                                                    (exp (-FR_B1_S * t) *
                                                     (exp (-FR_B2_S * t) *
                                                      ((1 −
                                                        exp (-FR_TL1_FTL * t)) *
                                                       (1 −
                                                        exp (-FR_TL2_CR * t))))))) +
                                                  (exp (-FR_TR1_S * t) *
                                                   (exp (-FR_TR2_S * t) *
                                                    (exp (-FR_TR3_S * t) *
                                                     (exp (-FR_B1_S * t) *
                                                      (exp (-FR_B2_S * t) *
                                                       ((1 −
                                                         exp
                                                           (-FR_TL1_FTL * t)) *
                                                        (1 −
                                                         exp
                                                           (-FR_TL2_FTL * t))))))) +
                                                   (exp (-FR_TR1_S * t) *
                                                    (exp (-FR_TR2_S * t) *
                                                     (exp (-FR_TR3_S * t) *
                                                      (exp (-FR_B1_S * t) *
                                                       ((1 −
                                                         exp (-FR_B2_F * t)) *
                                                        (exp (-FR_TL1_S * t) *
                                                         (exp (-FR_B3_S * t) *
                                                          (1 −
                                                           exp
                                                             (-FR_TR4_F * t)))))))) +
                                                    (exp (-FR_TR1_S * t) *
                                                     (exp (-FR_TR2_S * t) *
                                                      (exp (-FR_TR3_S * t) *
                                                       (exp (-FR_B1_S * t) *
                                                        ((1 −
                                                          exp (-FR_B2_F * t)) *
                                                         (exp (-FR_TL1_S * t) *
                                                          (exp (-FR_B3_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_TR4_PF * t)))))))) +
                                                     (exp (-FR_TR1_S * t) *
                                                      (exp (-FR_TR2_S * t) *
                                                       (exp (-FR_TR3_S * t) *
                                                        (exp (-FR_B1_S * t) *
                                                         ((1 −
                                                           exp (-FR_B2_F * t)) *
                                                          (exp
                                                             (-FR_TL1_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_B3_F * t))))))) +
                                                      (exp (-FR_TR1_S * t) *
                                                       (exp (-FR_TR2_S * t) *
                                                        (exp (-FR_TR3_S * t) *
                                                         (exp (-FR_B1_S * t) *
                                                          ((1 −
                                                            exp
                                                              (-FR_B2_F * t)) *
                                                           (1 −
                                                            exp
                                                              (-FR_TL1_F * t)))))) +
                                                       (exp (-FR_TR1_S * t) *
                                                        (exp (-FR_TR2_S * t) *
                                                         (exp (-FR_TR3_S * t) *
                                                          (exp (-FR_B1_S * t) *
                                                           ((1 −
                                                             exp
                                                               (-FR_B2_F * t)) *
                                                            (1 −
                                                             exp
                                                               (-FR_TL1_HR *
                                                                t)))))) +
                                                        (exp (-FR_TR1_S * t) *
                                                         (exp (-FR_TR2_S * t) *
                                                          (exp
                                                             (-FR_TR3_S * t) *
                                                           (exp
                                                              (-FR_B1_S * t) *
                                                            ((1 −
                                                              exp
                                                                (-FR_B2_F * t)) *
                                                             (1 −
                                                              exp
                                                                (-FR_TL1_CR *
                                                                 t)))))) +
                                                         (exp (-FR_TR1_S * t) *
                                                          (exp
                                                             (-FR_TR2_S * t) *
                                                           (exp
                                                              (-FR_TR3_S * t) *
                                                            (exp
                                                               (-FR_B1_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B2_F *
                                                                  t)) *
                                                              (1 −
                                                               exp
                                                                 (-FR_TL1_FTL *
                                                                  t)))))) +
                                                          (exp
                                                             (-FR_TR1_S * t) *
                                                           (exp
                                                              (-FR_TR2_S * t) *
                                                            (exp
                                                               (-FR_TR3_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B1_F *
                                                                  t)) *
                                                              (exp
                                                                 (-FR_B2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TL2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_B4_S *
                                                                    t) *
                                                                 (1 −
                                                                  exp
                                                                    (-FR_TR5_F *
                                                                     t)))))))) +
                                                           (exp
                                                              (-FR_TR1_S * t) *
                                                            (exp
                                                               (-FR_TR2_S * t) *
                                                             (exp
                                                                (-FR_TR3_S *
                                                                 t) *
                                                              ((1 −
                                                                exp
                                                                  (-FR_B1_F *
                                                                   t)) *
                                                               (exp
                                                                  (-FR_B2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TL2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_B4_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TR5_PF *
                                                                      t)))))))) +
                                                            (exp
                                                               (-FR_TR1_S * t) *
                                                             (exp
                                                                (-FR_TR2_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR3_S *
                                                                  t) *
                                                               ((1 −
                                                                 exp
                                                                   (-FR_B1_F *
                                                                    t)) *
                                                                (exp
                                                                   (-FR_B2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TL2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_B4_F *
                                                                      t))))))) +
                                                             (exp
                                                                (-FR_TR1_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR3_S *
                                                                   t) *
                                                                ((1 −
                                                                  exp
                                                                    (-FR_B1_F *
                                                                     t)) *
                                                                 (exp
                                                                    (-FR_B2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TL2_F *
                                                                      t)))))) +
                                                              (exp
                                                                 (-FR_TR1_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR3_S *
                                                                    t) *
                                                                 ((1 −
                                                                   exp
                                                                     (-FR_B1_F *
                                                                      t)) *
                                                                  (exp
                                                                     (-FR_B2_S *
                                                                      t) *
                                                                   (1 −
                                                                    exp
                                                                      (-FR_TL2_HR *
                                                                       t)))))) +
                                                               (exp
                                                                  (-FR_TR1_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR3_S *
                                                                     t) *
                                                                  ((1 −
                                                                    exp
                                                                      (-FR_B1_F *
                                                                       t)) *
                                                                   (exp
                                                                      (-FR_B2_S *
                                                                       t) *
                                                                    (1 −
                                                                     exp
                                                                       (-FR_TL2_CR *
                                                                        t)))))) +
                                                                (exp
                                                                   (-FR_TR1_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR2_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR3_S *
                                                                      t) *
                                                                   ((1 −
                                                                     exp
                                                                       (-FR_B1_F *
                                                                        t)) *
                                                                    (exp
                                                                       (-FR_B2_S *
                                                                        t) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_TL2_FTL *
                                                                         t)))))) +
                                                                 (exp
                                                                    (-FR_TR1_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR2_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR3_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_B1_F *
                                                                         t)) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_B2_F *
                                                                         t))))) +
                                                                  (exp
                                                                     (-FR_TR1_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR2_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_TR3_F *
                                                                         t)) *
                                                                     (exp
                                                                        (-FR_B1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TL1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_B3_S *
                                                                           t) *
                                                                        (1 −
                                                                         exp
                                                                           (-FR_TR4_F *
                                                                            t))))))) +
                                                                   (exp
                                                                      (-FR_TR1_S *
                                                                       t) *
                                                                    (exp
                                                                       (-FR_TR2_S *
                                                                        t) *
                                                                     ((1 −
                                                                       exp
                                                                         (-FR_TR3_F *
                                                                          t)) *
                                                                      (exp
                                                                         (-FR_B1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TL1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_B3_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TR4_PF *
                                                                             t))))))) +
                                                                    (exp
                                                                       (-FR_TR1_S *
                                                                        t) *
                                                                     (exp
                                                                        (-FR_TR2_S *
                                                                         t) *
                                                                      ((1 −
                                                                        exp
                                                                          (-FR_TR3_F *
                                                                           t)) *
                                                                       (exp
                                                                          (-FR_B1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TL1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_B3_F *
                                                                             t)))))) +
                                                                     (exp
                                                                        (-FR_TR1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TR2_S *
                                                                          t) *
                                                                       ((1 −
                                                                         exp
                                                                           (-FR_TR3_F *
                                                                            t)) *
                                                                        (exp
                                                                           (-FR_B1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TL1_F *
                                                                             t))))) +
                                                                      (exp
                                                                         (-FR_TR1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TR2_S *
                                                                           t) *
                                                                        ((1 −
                                                                          exp
                                                                            (-FR_TR3_F *
                                                                             t)) *
                                                                         (exp
                                                                            (-FR_B1_S *
                                                                             t) *
                                                                          (1 −
                                                                           exp
                                                                             (-FR_TL1_HR *
                                                                              t))))) +
                                                                       (exp
                                                                          (-FR_TR1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TR2_S *
                                                                            t) *
                                                                         ((1 −
                                                                           exp
                                                                             (-FR_TR3_F *
                                                                              t)) *
                                                                          (exp
                                                                             (-FR_B1_S *
                                                                              t) *
                                                                           (1 −
                                                                            exp
                                                                              (-FR_TL1_CR *
                                                                               t))))) +
                                                                        (exp
                                                                           (-FR_TR1_S *
                                                                            t) *
                                                                         (exp
                                                                            (-FR_TR2_S *
                                                                             t) *
                                                                          ((1 −
                                                                            exp
                                                                              (-FR_TR3_F *
                                                                               t)) *
                                                                           (exp
                                                                              (-FR_B1_S *
                                                                               t) *
                                                                            (1 −
                                                                             exp
                                                                               (-FR_TL1_FTL *
                                                                                t))))) +
                                                                         (exp
                                                                            (-FR_TR1_S *
                                                                             t) *
                                                                          (exp
                                                                             (-FR_TR2_S *
                                                                              t) *
                                                                           ((1 −
                                                                             exp
                                                                               (-FR_TR3_PF *
                                                                                t)) *
                                                                            (exp
                                                                               (-FR_B1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TL1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_B3_S *
                                                                                  t) *
                                                                               exp
                                                                                 (-FR_TR4_S *
                                                                                  t)))))) +
                                                                          (exp
                                                                             (-FR_TR1_S *
                                                                              t) *
                                                                           (exp
                                                                              (-FR_TR2_S *
                                                                               t) *
                                                                            ((1 −
                                                                              exp
                                                                                (-FR_TR3_PF *
                                                                                 t)) *
                                                                             (exp
                                                                                (-FR_B1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TL1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_B3_S *
                                                                                   t) *
                                                                                (1 −
                                                                                 exp
                                                                                   (-FR_TR4_F *
                                                                                    t))))))) +
                                                                           (exp
                                                                              (-FR_TR1_S *
                                                                               t) *
                                                                            (exp
                                                                               (-FR_TR2_S *
                                                                                t) *
                                                                             ((1 −
                                                                               exp
                                                                                 (-FR_TR3_PF *
                                                                                  t)) *
                                                                              (exp
                                                                                 (-FR_B1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TL1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_B3_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TR4_PF *
                                                                                     t))))))) +
                                                                            (exp
                                                                               (-FR_TR1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TR2_S *
                                                                                 t) *
                                                                              ((1 −
                                                                                exp
                                                                                  (-FR_TR3_PF *
                                                                                   t)) *
                                                                               (exp
                                                                                  (-FR_B1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TL1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_B3_F *
                                                                                     t)))))) +
                                                                             (exp
                                                                                (-FR_TR1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TR2_S *
                                                                                  t) *
                                                                               ((1 −
                                                                                 exp
                                                                                   (-FR_TR3_PF *
                                                                                    t)) *
                                                                                (exp
                                                                                   (-FR_B1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TL1_F *
                                                                                     t))))) +
                                                                              (exp
                                                                                 (-FR_TR1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TR2_S *
                                                                                   t) *
                                                                                ((1 −
                                                                                  exp
                                                                                    (-FR_TR3_PF *
                                                                                     t)) *
                                                                                 (exp
                                                                                    (-FR_B1_S *
                                                                                     t) *
                                                                                  (1 −
                                                                                   exp
                                                                                     (-FR_TL1_HR *
                                                                                      t))))) +
                                                                               (exp
                                                                                  (-FR_TR1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TR2_S *
                                                                                    t) *
                                                                                 ((1 −
                                                                                   exp
                                                                                     (-FR_TR3_PF *
                                                                                      t)) *
                                                                                  (exp
                                                                                     (-FR_B1_S *
                                                                                      t) *
                                                                                   (1 −
                                                                                    exp
                                                                                      (-FR_TL1_CR *
                                                                                       t))))) +
                                                                                (exp
                                                                                   (-FR_TR1_S *
                                                                                    t) *
                                                                                 (exp
                                                                                    (-FR_TR2_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR3_PF *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_B1_S *
                                                                                       t) *
                                                                                    (1 −
                                                                                     exp
                                                                                       (-FR_TL1_FTL *
                                                                                        t))))) +
                                                                                 (exp
                                                                                    (-FR_TR1_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR2_F *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_TR3_S *
                                                                                       t) *
                                                                                    (exp
                                                                                       (-FR_B2_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_TL2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B4_S *
                                                                                          t) *
                                                                                       exp
                                                                                         (-FR_TR5_S *
                                                                                          t)))))) +
                                                                                  (exp
                                                                                     (-FR_TR1_S *
                                                                                      t) *
                                                                                   ((1 −
                                                                                     exp
                                                                                       (-FR_TR2_F *
                                                                                        t)) *
                                                                                    (exp
                                                                                       (-FR_TR3_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_B2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_TL2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B4_S *
                                                                                           t) *
                                                                                        (1 −
                                                                                         exp
                                                                                           (-FR_TR5_F *
                                                                                            t))))))) +
                                                                                   (exp
                                                                                      (-FR_TR1_S *
                                                                                       t) *
                                                                                    ((1 −
                                                                                      exp
                                                                                        (-FR_TR2_F *
                                                                                         t)) *
                                                                                     (exp
                                                                                        (-FR_TR3_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_TL2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B4_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TR5_PF *
                                                                                             t))))))) +
                                                                                    (exp
                                                                                       (-FR_TR1_S *
                                                                                        t) *
                                                                                     ((1 −
                                                                                       exp
                                                                                         (-FR_TR2_F *
                                                                                          t)) *
                                                                                      (exp
                                                                                         (-FR_TR3_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_TL2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_B4_F *
                                                                                             t)))))) +
                                                                                     (exp
                                                                                        (-FR_TR1_S *
                                                                                         t) *
                                                                                      ((1 −
                                                                                        exp
                                                                                          (-FR_TR2_F *
                                                                                           t)) *
                                                                                       (exp
                                                                                          (-FR_TR3_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TL2_F *
                                                                                             t))))) +
                                                                                      (exp
                                                                                         (-FR_TR1_S *
                                                                                          t) *
                                                                                       ((1 −
                                                                                         exp
                                                                                           (-FR_TR2_F *
                                                                                            t)) *
                                                                                        (exp
                                                                                           (-FR_TR3_S *
                                                                                            t) *
                                                                                         (exp
                                                                                            (-FR_B2_S *
                                                                                             t) *
                                                                                          (1 −
                                                                                           exp
                                                                                             (-FR_TL2_HR *
                                                                                              t))))) +
                                                                                       (exp
                                                                                          (-FR_TR1_S *
                                                                                           t) *
                                                                                        ((1 −
                                                                                          exp
                                                                                            (-FR_TR2_F *
                                                                                             t)) *
                                                                                         (exp
                                                                                            (-FR_TR3_S *
                                                                                             t) *
                                                                                          (exp
                                                                                             (-FR_B2_S *
                                                                                              t) *
                                                                                           (1 −
                                                                                            exp
                                                                                              (-FR_TL2_CR *
                                                                                               t))))) +
                                                                                        (exp
                                                                                           (-FR_TR1_S *
                                                                                            t) *
                                                                                         ((1 −
                                                                                           exp
                                                                                             (-FR_TR2_F *
                                                                                              t)) *
                                                                                          (exp
                                                                                             (-FR_TR3_S *
                                                                                              t) *
                                                                                           (exp
                                                                                              (-FR_B2_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TL2_FTL *
                                                                                                t))))) +
                                                                                         (exp
                                                                                            (-FR_TR1_S *
                                                                                             t) *
                                                                                          ((1 −
                                                                                            exp
                                                                                              (-FR_TR2_F *
                                                                                               t)) *
                                                                                           (exp
                                                                                              (-FR_TR3_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_B2_F *
                                                                                                t)))) +
                                                                                          (exp
                                                                                             (-FR_TR1_S *
                                                                                              t) *
                                                                                           ((1 −
                                                                                             exp
                                                                                               (-FR_TR2_F *
                                                                                                t)) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TR3_F *
                                                                                                t))) +
                                                                                           (exp
                                                                                              (-FR_TR1_S *
                                                                                               t) *
                                                                                            ((1 −
                                                                                              exp
                                                                                                (-FR_TR2_PF *
                                                                                                 t)) *
                                                                                             (exp
                                                                                                (-FR_TR3_S *
                                                                                                 t) *
                                                                                              (exp
                                                                                                 (-FR_B2_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_TL2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B4_S *
                                                                                                    t) *
                                                                                                 exp
                                                                                                   (-FR_TR5_S *
                                                                                                    t)))))) +
                                                                                            (exp
                                                                                               (-FR_TR1_S *
                                                                                                t) *
                                                                                             ((1 −
                                                                                               exp
                                                                                                 (-FR_TR2_PF *
                                                                                                  t)) *
                                                                                              (exp
                                                                                                 (-FR_TR3_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_B2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_TL2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B4_S *
                                                                                                     t) *
                                                                                                  (1 −
                                                                                                   exp
                                                                                                     (-FR_TR5_F *
                                                                                                      t))))))) +
                                                                                             (exp
                                                                                                (-FR_TR1_S *
                                                                                                 t) *
                                                                                              ((1 −
                                                                                                exp
                                                                                                  (-FR_TR2_PF *
                                                                                                   t)) *
                                                                                               (exp
                                                                                                  (-FR_TR3_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_TL2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B4_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TR5_PF *
                                                                                                       t))))))) +
                                                                                              (exp
                                                                                                 (-FR_TR1_S *
                                                                                                  t) *
                                                                                               ((1 −
                                                                                                 exp
                                                                                                   (-FR_TR2_PF *
                                                                                                    t)) *
                                                                                                (exp
                                                                                                   (-FR_TR3_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_TL2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_B4_F *
                                                                                                       t)))))) +
                                                                                               (exp
                                                                                                  (-FR_TR1_S *
                                                                                                   t) *
                                                                                                ((1 −
                                                                                                  exp
                                                                                                    (-FR_TR2_PF *
                                                                                                     t)) *
                                                                                                 (exp
                                                                                                    (-FR_TR3_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TL2_F *
                                                                                                       t))))) +
                                                                                                (exp
                                                                                                   (-FR_TR1_S *
                                                                                                    t) *
                                                                                                 ((1 −
                                                                                                   exp
                                                                                                     (-FR_TR2_PF *
                                                                                                      t)) *
                                                                                                  (exp
                                                                                                     (-FR_TR3_S *
                                                                                                      t) *
                                                                                                   (exp
                                                                                                      (-FR_B2_S *
                                                                                                       t) *
                                                                                                    (1 −
                                                                                                     exp
                                                                                                       (-FR_TL2_HR *
                                                                                                        t))))) +
                                                                                                 (exp
                                                                                                    (-FR_TR1_S *
                                                                                                     t) *
                                                                                                  ((1 −
                                                                                                    exp
                                                                                                      (-FR_TR2_PF *
                                                                                                       t)) *
                                                                                                   (exp
                                                                                                      (-FR_TR3_S *
                                                                                                       t) *
                                                                                                    (exp
                                                                                                       (-FR_B2_S *
                                                                                                        t) *
                                                                                                     (1 −
                                                                                                      exp
                                                                                                        (-FR_TL2_CR *
                                                                                                         t))))) +
                                                                                                  (exp
                                                                                                     (-FR_TR1_S *
                                                                                                      t) *
                                                                                                   ((1 −
                                                                                                     exp
                                                                                                       (-FR_TR2_PF *
                                                                                                        t)) *
                                                                                                    (exp
                                                                                                       (-FR_TR3_S *
                                                                                                        t) *
                                                                                                     (exp
                                                                                                        (-FR_B2_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TL2_FTL *
                                                                                                          t))))) +
                                                                                                   (exp
                                                                                                      (-FR_TR1_S *
                                                                                                       t) *
                                                                                                    ((1 −
                                                                                                      exp
                                                                                                        (-FR_TR2_PF *
                                                                                                         t)) *
                                                                                                     (exp
                                                                                                        (-FR_TR3_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_B2_F *
                                                                                                          t)))) +
                                                                                                    (exp
                                                                                                       (-FR_TR1_S *
                                                                                                        t) *
                                                                                                     ((1 −
                                                                                                       exp
                                                                                                         (-FR_TR2_PF *
                                                                                                          t)) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR3_F *
                                                                                                          t))) +
                                                                                                     (exp
                                                                                                        (-FR_TR1_S *
                                                                                                         t) *
                                                                                                      ((1 −
                                                                                                        exp
                                                                                                          (-FR_TR2_PF *
                                                                                                           t)) *
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR3_PF *
                                                                                                           t))) +
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR1_F *
                                                                                                          t) +
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR1_PF *
                                                                                                           t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * 80)/115,000``;

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)


PROBABILITY ``LOLE``
``(exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_F * t)) * exp (-FR_TR5_S * t)))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * exp (-FR_TR5_S * t)))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * exp (-FR_TR4_S * t))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              ((1 − exp (-FR_B3_F * t)) *
               (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              ((1 − exp (-FR_TL2_F * t)) *
               (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               ((1 − exp (-FR_TL2_HR * t)) *
                (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                ((1 − exp (-FR_TL2_CR * t)) *
                 (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_FTL * t)) *
                  (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (exp (-FR_B1_S * t) *
                (exp (-FR_B2_S * t) *
                 ((1 − exp (-FR_TL1_F * t)) *
                  (exp (-FR_TL2_S * t) *
                   (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  ((1 − exp (-FR_TL1_HR * t)) *
                   (exp (-FR_TL2_S * t) *
                    (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   ((1 − exp (-FR_TL1_CR * t)) *
                    (exp (-FR_TL2_S * t) *
                     (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    ((1 − exp (-FR_TL1_FTL * t)) *
                     (exp (-FR_TL2_S * t) *
                      (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    ((1 − exp (-FR_B2_F * t)) *
                     (exp (-FR_TL1_S * t) *
                      (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    ((1 − exp (-FR_B1_F * t)) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL2_S * t) *
                       (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    ((1 − exp (-FR_TR3_F * t)) *
                     (exp (-FR_B1_S * t) * exp (-FR_TL1_S * t)))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     ((1 − exp (-FR_TR3_F * t)) * (1 − exp (-FR_B1_F * t)))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      ((1 − exp (-FR_TR3_PF * t)) * (1 − exp (-FR_B1_F * t)))) +
                     exp (-FR_TR1_S * t) *
                     ((1 − exp (-FR_TR2_F * t)) * (1 − exp (-FR_TR3_PF * t)))))))))))))))))))) * 40 +
  (exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_F * t)))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              (exp (-FR_B3_S * t) *
               ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_PF * t)))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              (exp (-FR_TL2_S * t) *
               ((1 − exp (-FR_B3_F * t)) *
                (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_F * t)))))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               (exp (-FR_TL2_S * t) *
                ((1 − exp (-FR_B3_F * t)) *
                 (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_PF * t)))))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                (exp (-FR_TL2_S * t) *
                 ((1 − exp (-FR_B3_F * t)) * (1 − exp (-FR_B4_F * t))))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_F * t)) *
                  (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (RELIABILITY p B1 t *
                (RELIABILITY p B2 t *
                 (exp (-FR_TL1_S * t) *
                  ((1 − exp (-FR_TL2_F * t)) *
                   (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  (exp (-FR_TL1_S * t) *
                   ((1 − exp (-FR_TL2_F * t)) * (1 − exp (-FR_B3_F * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   (exp (-FR_TL1_S * t) *
                    ((1 − exp (-FR_TL2_HR * t)) *
                     (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    (exp (-FR_TL1_S * t) *
                     ((1 − exp (-FR_TL2_HR * t)) *
                      (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    (exp (-FR_B2_S * t) *
                     (exp (-FR_TL1_S * t) *
                      ((1 − exp (-FR_TL2_HR * t)) * (1 − exp (-FR_B3_F * t)))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    (exp (-FR_B1_S * t) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL1_S * t) *
                       ((1 − exp (-FR_TL2_CR * t)) *
                        (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    (exp (-FR_TR3_S * t) *
                     (exp (-FR_B1_S * t) *
                      (exp (-FR_B2_S * t) *
                       (exp (-FR_TL1_S * t) *
                        ((1 − exp (-FR_TL2_CR * t)) *
                         (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     (exp (-FR_TR3_S * t) *
                      (exp (-FR_B1_S * t) *
                       (exp (-FR_B2_S * t) *
                        (exp (-FR_TL1_S * t) *
                         ((1 − exp (-FR_TL2_CR * t)) *
                          (1 − exp (-FR_B3_F * t)))))))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      (exp (-FR_TR3_S * t) *
                       (exp (-FR_B1_S * t) *
                        (exp (-FR_B2_S * t) *
                         (exp (-FR_TL1_S * t) *
                          ((1 − exp (-FR_TL2_FTL * t)) *
                           (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                     (exp (-FR_TR1_S * t) *
                      (exp (-FR_TR2_S * t) *
                       (exp (-FR_TR3_S * t) *
                        (exp (-FR_B1_S * t) *
                         (exp (-FR_B2_S * t) *
                          (exp (-FR_TL1_S * t) *
                           ((1 − exp (-FR_TL2_FTL * t)) *
                            (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                      (exp (-FR_TR1_S * t) *
                       (exp (-FR_TR2_S * t) *
                        (exp (-FR_TR3_S * t) *
                         (exp (-FR_B1_S * t) *
                          (exp (-FR_B2_S * t) *
                           (exp (-FR_TL1_S * t) *
                            ((1 − exp (-FR_TL2_FTL * t)) *
                             (1 − exp (-FR_B3_F * t)))))))) +
                       (exp (-FR_TR1_S * t) *
                        (exp (-FR_TR2_S * t) *
                         (exp (-FR_TR3_S * t) *
                          (exp (-FR_B1_S * t) *
                           (exp (-FR_B2_S * t) *
                            ((1 − exp (-FR_TL1_F * t)) *
                             (exp (-FR_TL2_S * t) *
                              (exp (-FR_B4_S * t) *
                               (1 − exp (-FR_TR5_F * t))))))))) +
                        (exp (-FR_TR1_S * t) *
                         (exp (-FR_TR2_S * t) *
                          (exp (-FR_TR3_S * t) *
                           (exp (-FR_B1_S * t) *
                            (exp (-FR_B2_S * t) *
                             ((1 − exp (-FR_TL1_F * t)) *
                              (exp (-FR_TL2_S * t) *
                               (exp (-FR_B4_S * t) *
                                (1 − exp (-FR_TR5_PF * t))))))))) +
                         (exp (-FR_TR1_S * t) *
                          (exp (-FR_TR2_S * t) *
                           (exp (-FR_TR3_S * t) *
                            (exp (-FR_B1_S * t) *
                             (exp (-FR_B2_S * t) *
                              ((1 − exp (-FR_TL1_F * t)) *
                               (exp (-FR_TL2_S * t) *
                                (1 − exp (-FR_B4_F * t)))))))) +
                          (exp (-FR_TR1_S * t) *
                           (exp (-FR_TR2_S * t) *
                            (exp (-FR_TR3_S * t) *
                             (exp (-FR_B1_S * t) *
                              (exp (-FR_B2_S * t) *
                               ((1 − exp (-FR_TL1_F * t)) *
                                (1 − exp (-FR_TL2_F * t))))))) +
                           (exp (-FR_TR1_S * t) *
                            (exp (-FR_TR2_S * t) *
                             (exp (-FR_TR3_S * t) *
                              (exp (-FR_B1_S * t) *
                               (exp (-FR_B2_S * t) *
                                ((1 − exp (-FR_TL1_F * t)) *
                                 (1 − exp (-FR_TL2_HR * t))))))) +
                            (exp (-FR_TR1_S * t) *
                             (exp (-FR_TR2_S * t) *
                              (exp (-FR_TR3_S * t) *
                               (exp (-FR_B1_S * t) *
                                (exp (-FR_B2_S * t) *
                                 ((1 − exp (-FR_TL1_F * t)) *
                                  (1 − exp (-FR_TL2_CR * t))))))) +
                             (exp (-FR_TR1_S * t) *
                              (exp (-FR_TR2_S * t) *
                               (exp (-FR_TR3_S * t) *
                                (exp (-FR_B1_S * t) *
                                 (exp (-FR_B2_S * t) *
                                  ((1 − exp (-FR_TL1_F * t)) *
                                   (1 − exp (-FR_TL2_FTL * t))))))) +
                              (exp (-FR_TR1_S * t) *
                               (exp (-FR_TR2_S * t) *
                                (exp (-FR_TR3_S * t) *
                                 (exp (-FR_B1_S * t) *
                                  (exp (-FR_B2_S * t) *
                                   ((1 − exp (-FR_TL1_HR * t)) *
                                    (exp (-FR_TL2_S * t) *
                                     (exp (-FR_B4_S * t) *
                                      (1 − exp (-FR_TR5_F * t))))))))) +
                               (exp (-FR_TR1_S * t) *
                                (exp (-FR_TR2_S * t) *
                                 (exp (-FR_TR3_S * t) *
                                  (exp (-FR_B1_S * t) *
                                   (exp (-FR_B2_S * t) *
                                    ((1 − exp (-FR_TL1_HR * t)) *
                                     (exp (-FR_TL2_S * t) *
                                      (exp (-FR_B4_S * t) *
                                       (1 − exp (-FR_TR5_PF * t))))))))) +
                                (exp (-FR_TR1_S * t) *
                                 (exp (-FR_TR2_S * t) *
                                  (exp (-FR_TR3_S * t) *
                                   (exp (-FR_B1_S * t) *
                                    (exp (-FR_B2_S * t) *
                                     ((1 − exp (-FR_TL1_HR * t)) *
                                      (exp (-FR_TL2_S * t) *
                                       (1 − exp (-FR_B4_F * t)))))))) +
                                 (exp (-FR_TR1_S * t) *
                                  (exp (-FR_TR2_S * t) *
                                   (exp (-FR_TR3_S * t) *
                                    (exp (-FR_B1_S * t) *
                                     (exp (-FR_B2_S * t) *
                                      ((1 − exp (-FR_TL1_HR * t)) *
                                       (1 − exp (-FR_TL2_F * t))))))) +
                                  (exp (-FR_TR1_S * t) *
                                   (exp (-FR_TR2_S * t) *
                                    (exp (-FR_TR3_S * t) *
                                     (exp (-FR_B1_S * t) *
                                      (exp (-FR_B2_S * t) *
                                       ((1 − exp (-FR_TL1_HR * t)) *
                                        (1 − exp (-FR_TL2_HR * t))))))) +
                                   (exp (-FR_TR1_S * t) *
                                    (exp (-FR_TR2_S * t) *
                                     (exp (-FR_TR3_S * t) *
                                      (exp (-FR_B1_S * t) *
                                       (exp (-FR_B2_S * t) *
                                        ((1 − exp (-FR_TL1_HR * t)) *
                                         (1 − exp (-FR_TL2_CR * t))))))) +
                                    (exp (-FR_TR1_S * t) *
                                     (exp (-FR_TR2_S * t) *
                                      (exp (-FR_TR3_S * t) *
                                       (exp (-FR_B1_S * t) *
                                        (exp (-FR_B2_S * t) *
                                         ((1 − exp (-FR_TL1_HR * t)) *
                                          (1 − exp (-FR_TL2_FTL * t))))))) +
                                     (exp (-FR_TR1_S * t) *
                                      (exp (-FR_TR2_S * t) *
                                       (exp (-FR_TR3_S * t) *
                                        (exp (-FR_B1_S * t) *
                                         (exp (-FR_B2_S * t) *
                                          ((1 − exp (-FR_TL1_CR * t)) *
                                           (exp (-FR_TL2_S * t) *
                                            (exp (-FR_B4_S * t) *
                                             (1 − exp (-FR_TR5_F * t))))))))) +
                                      (exp (-FR_TR1_S * t) *
                                       (exp (-FR_TR2_S * t) *
                                        (exp (-FR_TR3_S * t) *
                                         (exp (-FR_B1_S * t) *
                                          (exp (-FR_B2_S * t) *
                                           ((1 − exp (-FR_TL1_CR * t)) *
                                            (exp (-FR_TL2_S * t) *
                                             (exp (-FR_B4_S * t) *
                                              (1 − exp (-FR_TR5_PF * t))))))))) +
                                       (exp (-FR_TR1_S * t) *
                                        (exp (-FR_TR2_S * t) *
                                         (exp (-FR_TR3_S * t) *
                                          (exp (-FR_B1_S * t) *
                                           (exp (-FR_B2_S * t) *
                                            ((1 − exp (-FR_TL1_CR * t)) *
                                             (exp (-FR_TL2_S * t) *
                                              (1 − exp (-FR_B4_F * t)))))))) +
                                        (exp (-FR_TR1_S * t) *
                                         (exp (-FR_TR2_S * t) *
                                          (exp (-FR_TR3_S * t) *
                                           (exp (-FR_B1_S * t) *
                                            (exp (-FR_B2_S * t) *
                                             ((1 − exp (-FR_TL1_CR * t)) *
                                              (1 − exp (-FR_TL2_F * t))))))) +
                                         (exp (-FR_TR1_S * t) *
                                          (exp (-FR_TR2_S * t) *
                                           (exp (-FR_TR3_S * t) *
                                            (exp (-FR_B1_S * t) *
                                             (exp (-FR_B2_S * t) *
                                              ((1 − exp (-FR_TL1_CR * t)) *
                                               (1 − exp (-FR_TL2_HR * t))))))) +
                                          (exp (-FR_TR1_S * t) *
                                           (exp (-FR_TR2_S * t) *
                                            (exp (-FR_TR3_S * t) *
                                             (exp (-FR_B1_S * t) *
                                              (exp (-FR_B2_S * t) *
                                               ((1 − exp (-FR_TL1_CR * t)) *
                                                (1 − exp (-FR_TL2_CR * t))))))) +
                                           (exp (-FR_TR1_S * t) *
                                            (exp (-FR_TR2_S * t) *
                                             (exp (-FR_TR3_S * t) *
                                              (exp (-FR_B1_S * t) *
                                               (exp (-FR_B2_S * t) *
                                                ((1 − exp (-FR_TL1_CR * t)) *
                                                 (1 − exp (-FR_TL2_FTL * t))))))) +
                                            (exp (-FR_TR1_S * t) *
                                             (exp (-FR_TR2_S * t) *
                                              (exp (-FR_TR3_S * t) *
                                               (exp (-FR_B1_S * t) *
                                                (exp (-FR_B2_S * t) *
                                                 ((1 − exp (-FR_TL1_FTL * t)) *
                                                  (exp (-FR_TL2_S * t) *
                                                   (exp (-FR_B4_S * t) *
                                                    (1 − exp (-FR_TR5_F * t))))))))) +
                                             (exp (-FR_TR1_S * t) *
                                              (exp (-FR_TR2_S * t) *
                                               (exp (-FR_TR3_S * t) *
                                                (exp (-FR_B1_S * t) *
                                                 (exp (-FR_B2_S * t) *
                                                  ((1 − exp (-FR_TL1_FTL * t)) *
                                                   (exp (-FR_TL2_S * t) *
                                                    (exp (-FR_B4_S * t) *
                                                     (1 −
                                                      exp (-FR_TR5_PF * t))))))))) +
                                              (exp (-FR_TR1_S * t) *
                                               (exp (-FR_TR2_S * t) *
                                                (exp (-FR_TR3_S * t) *
                                                 (exp (-FR_B1_S * t) *
                                                  (exp (-FR_B2_S * t) *
                                                   ((1 −
                                                     exp (-FR_TL1_FTL * t)) *
                                                    (exp (-FR_TL2_S * t) *
                                                     (1 − exp (-FR_B4_F * t)))))))) +
                                               (exp (-FR_TR1_S * t) *
                                                (exp (-FR_TR2_S * t) *
                                                 (exp (-FR_TR3_S * t) *
                                                  (exp (-FR_B1_S * t) *
                                                   (exp (-FR_B2_S * t) *
                                                    ((1 −
                                                      exp (-FR_TL1_FTL * t)) *
                                                     (1 − exp (-FR_TL2_F * t))))))) +
                                                (exp (-FR_TR1_S * t) *
                                                 (exp (-FR_TR2_S * t) *
                                                  (exp (-FR_TR3_S * t) *
                                                   (exp (-FR_B1_S * t) *
                                                    (exp (-FR_B2_S * t) *
                                                     ((1 −
                                                       exp (-FR_TL1_FTL * t)) *
                                                      (1 −
                                                       exp (-FR_TL2_HR * t))))))) +
                                                 (exp (-FR_TR1_S * t) *
                                                  (exp (-FR_TR2_S * t) *
                                                   (exp (-FR_TR3_S * t) *
                                                    (exp (-FR_B1_S * t) *
                                                     (exp (-FR_B2_S * t) *
                                                      ((1 −
                                                        exp (-FR_TL1_FTL * t)) *
                                                       (1 −
                                                        exp (-FR_TL2_CR * t))))))) +
                                                  (exp (-FR_TR1_S * t) *
                                                   (exp (-FR_TR2_S * t) *
                                                    (exp (-FR_TR3_S * t) *
                                                     (exp (-FR_B1_S * t) *
                                                      (exp (-FR_B2_S * t) *
                                                       ((1 −
                                                         exp
                                                           (-FR_TL1_FTL * t)) *
                                                        (1 −
                                                         exp
                                                           (-FR_TL2_FTL * t))))))) +
                                                   (exp (-FR_TR1_S * t) *
                                                    (exp (-FR_TR2_S * t) *
                                                     (exp (-FR_TR3_S * t) *
                                                      (exp (-FR_B1_S * t) *
                                                       ((1 −
                                                         exp (-FR_B2_F * t)) *
                                                        (exp (-FR_TL1_S * t) *
                                                         (exp (-FR_B3_S * t) *
                                                          (1 −
                                                           exp
                                                             (-FR_TR4_F * t)))))))) +
                                                    (exp (-FR_TR1_S * t) *
                                                     (exp (-FR_TR2_S * t) *
                                                      (exp (-FR_TR3_S * t) *
                                                       (exp (-FR_B1_S * t) *
                                                        ((1 −
                                                          exp (-FR_B2_F * t)) *
                                                         (exp (-FR_TL1_S * t) *
                                                          (exp (-FR_B3_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_TR4_PF * t)))))))) +
                                                     (exp (-FR_TR1_S * t) *
                                                      (exp (-FR_TR2_S * t) *
                                                       (exp (-FR_TR3_S * t) *
                                                        (exp (-FR_B1_S * t) *
                                                         ((1 −
                                                           exp (-FR_B2_F * t)) *
                                                          (exp
                                                             (-FR_TL1_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_B3_F * t))))))) +
                                                      (exp (-FR_TR1_S * t) *
                                                       (exp (-FR_TR2_S * t) *
                                                        (exp (-FR_TR3_S * t) *
                                                         (exp (-FR_B1_S * t) *
                                                          ((1 −
                                                            exp
                                                              (-FR_B2_F * t)) *
                                                           (1 −
                                                            exp
                                                              (-FR_TL1_F * t)))))) +
                                                       (exp (-FR_TR1_S * t) *
                                                        (exp (-FR_TR2_S * t) *
                                                         (exp (-FR_TR3_S * t) *
                                                          (exp (-FR_B1_S * t) *
                                                           ((1 −
                                                             exp
                                                               (-FR_B2_F * t)) *
                                                            (1 −
                                                             exp
                                                               (-FR_TL1_HR *
                                                                t)))))) +
                                                        (exp (-FR_TR1_S * t) *
                                                         (exp (-FR_TR2_S * t) *
                                                          (exp
                                                             (-FR_TR3_S * t) *
                                                           (exp
                                                              (-FR_B1_S * t) *
                                                            ((1 −
                                                              exp
                                                                (-FR_B2_F * t)) *
                                                             (1 −
                                                              exp
                                                                (-FR_TL1_CR *
                                                                 t)))))) +
                                                         (exp (-FR_TR1_S * t) *
                                                          (exp
                                                             (-FR_TR2_S * t) *
                                                           (exp
                                                              (-FR_TR3_S * t) *
                                                            (exp
                                                               (-FR_B1_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B2_F *
                                                                  t)) *
                                                              (1 −
                                                               exp
                                                                 (-FR_TL1_FTL *
                                                                  t)))))) +
                                                          (exp
                                                             (-FR_TR1_S * t) *
                                                           (exp
                                                              (-FR_TR2_S * t) *
                                                            (exp
                                                               (-FR_TR3_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B1_F *
                                                                  t)) *
                                                              (exp
                                                                 (-FR_B2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TL2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_B4_S *
                                                                    t) *
                                                                 (1 −
                                                                  exp
                                                                    (-FR_TR5_F *
                                                                     t)))))))) +
                                                           (exp
                                                              (-FR_TR1_S * t) *
                                                            (exp
                                                               (-FR_TR2_S * t) *
                                                             (exp
                                                                (-FR_TR3_S *
                                                                 t) *
                                                              ((1 −
                                                                exp
                                                                  (-FR_B1_F *
                                                                   t)) *
                                                               (exp
                                                                  (-FR_B2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TL2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_B4_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TR5_PF *
                                                                      t)))))))) +
                                                            (exp
                                                               (-FR_TR1_S * t) *
                                                             (exp
                                                                (-FR_TR2_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR3_S *
                                                                  t) *
                                                               ((1 −
                                                                 exp
                                                                   (-FR_B1_F *
                                                                    t)) *
                                                                (exp
                                                                   (-FR_B2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TL2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_B4_F *
                                                                      t))))))) +
                                                             (exp
                                                                (-FR_TR1_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR3_S *
                                                                   t) *
                                                                ((1 −
                                                                  exp
                                                                    (-FR_B1_F *
                                                                     t)) *
                                                                 (exp
                                                                    (-FR_B2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TL2_F *
                                                                      t)))))) +
                                                              (exp
                                                                 (-FR_TR1_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR3_S *
                                                                    t) *
                                                                 ((1 −
                                                                   exp
                                                                     (-FR_B1_F *
                                                                      t)) *
                                                                  (exp
                                                                     (-FR_B2_S *
                                                                      t) *
                                                                   (1 −
                                                                    exp
                                                                      (-FR_TL2_HR *
                                                                       t)))))) +
                                                               (exp
                                                                  (-FR_TR1_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR3_S *
                                                                     t) *
                                                                  ((1 −
                                                                    exp
                                                                      (-FR_B1_F *
                                                                       t)) *
                                                                   (exp
                                                                      (-FR_B2_S *
                                                                       t) *
                                                                    (1 −
                                                                     exp
                                                                       (-FR_TL2_CR *
                                                                        t)))))) +
                                                                (exp
                                                                   (-FR_TR1_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR2_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR3_S *
                                                                      t) *
                                                                   ((1 −
                                                                     exp
                                                                       (-FR_B1_F *
                                                                        t)) *
                                                                    (exp
                                                                       (-FR_B2_S *
                                                                        t) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_TL2_FTL *
                                                                         t)))))) +
                                                                 (exp
                                                                    (-FR_TR1_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR2_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR3_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_B1_F *
                                                                         t)) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_B2_F *
                                                                         t))))) +
                                                                  (exp
                                                                     (-FR_TR1_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR2_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_TR3_F *
                                                                         t)) *
                                                                     (exp
                                                                        (-FR_B1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TL1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_B3_S *
                                                                           t) *
                                                                        (1 −
                                                                         exp
                                                                           (-FR_TR4_F *
                                                                            t))))))) +
                                                                   (exp
                                                                      (-FR_TR1_S *
                                                                       t) *
                                                                    (exp
                                                                       (-FR_TR2_S *
                                                                        t) *
                                                                     ((1 −
                                                                       exp
                                                                         (-FR_TR3_F *
                                                                          t)) *
                                                                      (exp
                                                                         (-FR_B1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TL1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_B3_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TR4_PF *
                                                                             t))))))) +
                                                                    (exp
                                                                       (-FR_TR1_S *
                                                                        t) *
                                                                     (exp
                                                                        (-FR_TR2_S *
                                                                         t) *
                                                                      ((1 −
                                                                        exp
                                                                          (-FR_TR3_F *
                                                                           t)) *
                                                                       (exp
                                                                          (-FR_B1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TL1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_B3_F *
                                                                             t)))))) +
                                                                     (exp
                                                                        (-FR_TR1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TR2_S *
                                                                          t) *
                                                                       ((1 −
                                                                         exp
                                                                           (-FR_TR3_F *
                                                                            t)) *
                                                                        (exp
                                                                           (-FR_B1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TL1_F *
                                                                             t))))) +
                                                                      (exp
                                                                         (-FR_TR1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TR2_S *
                                                                           t) *
                                                                        ((1 −
                                                                          exp
                                                                            (-FR_TR3_F *
                                                                             t)) *
                                                                         (exp
                                                                            (-FR_B1_S *
                                                                             t) *
                                                                          (1 −
                                                                           exp
                                                                             (-FR_TL1_HR *
                                                                              t))))) +
                                                                       (exp
                                                                          (-FR_TR1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TR2_S *
                                                                            t) *
                                                                         ((1 −
                                                                           exp
                                                                             (-FR_TR3_F *
                                                                              t)) *
                                                                          (exp
                                                                             (-FR_B1_S *
                                                                              t) *
                                                                           (1 −
                                                                            exp
                                                                              (-FR_TL1_CR *
                                                                               t))))) +
                                                                        (exp
                                                                           (-FR_TR1_S *
                                                                            t) *
                                                                         (exp
                                                                            (-FR_TR2_S *
                                                                             t) *
                                                                          ((1 −
                                                                            exp
                                                                              (-FR_TR3_F *
                                                                               t)) *
                                                                           (exp
                                                                              (-FR_B1_S *
                                                                               t) *
                                                                            (1 −
                                                                             exp
                                                                               (-FR_TL1_FTL *
                                                                                t))))) +
                                                                         (exp
                                                                            (-FR_TR1_S *
                                                                             t) *
                                                                          (exp
                                                                             (-FR_TR2_S *
                                                                              t) *
                                                                           ((1 −
                                                                             exp
                                                                               (-FR_TR3_PF *
                                                                                t)) *
                                                                            (exp
                                                                               (-FR_B1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TL1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_B3_S *
                                                                                  t) *
                                                                               exp
                                                                                 (-FR_TR4_S *
                                                                                  t)))))) +
                                                                          (exp
                                                                             (-FR_TR1_S *
                                                                              t) *
                                                                           (exp
                                                                              (-FR_TR2_S *
                                                                               t) *
                                                                            ((1 −
                                                                              exp
                                                                                (-FR_TR3_PF *
                                                                                 t)) *
                                                                             (exp
                                                                                (-FR_B1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TL1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_B3_S *
                                                                                   t) *
                                                                                (1 −
                                                                                 exp
                                                                                   (-FR_TR4_F *
                                                                                    t))))))) +
                                                                           (exp
                                                                              (-FR_TR1_S *
                                                                               t) *
                                                                            (exp
                                                                               (-FR_TR2_S *
                                                                                t) *
                                                                             ((1 −
                                                                               exp
                                                                                 (-FR_TR3_PF *
                                                                                  t)) *
                                                                              (exp
                                                                                 (-FR_B1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TL1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_B3_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TR4_PF *
                                                                                     t))))))) +
                                                                            (exp
                                                                               (-FR_TR1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TR2_S *
                                                                                 t) *
                                                                              ((1 −
                                                                                exp
                                                                                  (-FR_TR3_PF *
                                                                                   t)) *
                                                                               (exp
                                                                                  (-FR_B1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TL1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_B3_F *
                                                                                     t)))))) +
                                                                             (exp
                                                                                (-FR_TR1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TR2_S *
                                                                                  t) *
                                                                               ((1 −
                                                                                 exp
                                                                                   (-FR_TR3_PF *
                                                                                    t)) *
                                                                                (exp
                                                                                   (-FR_B1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TL1_F *
                                                                                     t))))) +
                                                                              (exp
                                                                                 (-FR_TR1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TR2_S *
                                                                                   t) *
                                                                                ((1 −
                                                                                  exp
                                                                                    (-FR_TR3_PF *
                                                                                     t)) *
                                                                                 (exp
                                                                                    (-FR_B1_S *
                                                                                     t) *
                                                                                  (1 −
                                                                                   exp
                                                                                     (-FR_TL1_HR *
                                                                                      t))))) +
                                                                               (exp
                                                                                  (-FR_TR1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TR2_S *
                                                                                    t) *
                                                                                 ((1 −
                                                                                   exp
                                                                                     (-FR_TR3_PF *
                                                                                      t)) *
                                                                                  (exp
                                                                                     (-FR_B1_S *
                                                                                      t) *
                                                                                   (1 −
                                                                                    exp
                                                                                      (-FR_TL1_CR *
                                                                                       t))))) +
                                                                                (exp
                                                                                   (-FR_TR1_S *
                                                                                    t) *
                                                                                 (exp
                                                                                    (-FR_TR2_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR3_PF *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_B1_S *
                                                                                       t) *
                                                                                    (1 −
                                                                                     exp
                                                                                       (-FR_TL1_FTL *
                                                                                        t))))) +
                                                                                 (exp
                                                                                    (-FR_TR1_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR2_F *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_TR3_S *
                                                                                       t) *
                                                                                    (exp
                                                                                       (-FR_B2_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_TL2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B4_S *
                                                                                          t) *
                                                                                       exp
                                                                                         (-FR_TR5_S *
                                                                                          t)))))) +
                                                                                  (exp
                                                                                     (-FR_TR1_S *
                                                                                      t) *
                                                                                   ((1 −
                                                                                     exp
                                                                                       (-FR_TR2_F *
                                                                                        t)) *
                                                                                    (exp
                                                                                       (-FR_TR3_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_B2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_TL2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B4_S *
                                                                                           t) *
                                                                                        (1 −
                                                                                         exp
                                                                                           (-FR_TR5_F *
                                                                                            t))))))) +
                                                                                   (exp
                                                                                      (-FR_TR1_S *
                                                                                       t) *
                                                                                    ((1 −
                                                                                      exp
                                                                                        (-FR_TR2_F *
                                                                                         t)) *
                                                                                     (exp
                                                                                        (-FR_TR3_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_TL2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B4_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TR5_PF *
                                                                                             t))))))) +
                                                                                    (exp
                                                                                       (-FR_TR1_S *
                                                                                        t) *
                                                                                     ((1 −
                                                                                       exp
                                                                                         (-FR_TR2_F *
                                                                                          t)) *
                                                                                      (exp
                                                                                         (-FR_TR3_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_TL2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_B4_F *
                                                                                             t)))))) +
                                                                                     (exp
                                                                                        (-FR_TR1_S *
                                                                                         t) *
                                                                                      ((1 −
                                                                                        exp
                                                                                          (-FR_TR2_F *
                                                                                           t)) *
                                                                                       (exp
                                                                                          (-FR_TR3_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TL2_F *
                                                                                             t))))) +
                                                                                      (exp
                                                                                         (-FR_TR1_S *
                                                                                          t) *
                                                                                       ((1 −
                                                                                         exp
                                                                                           (-FR_TR2_F *
                                                                                            t)) *
                                                                                        (exp
                                                                                           (-FR_TR3_S *
                                                                                            t) *
                                                                                         (exp
                                                                                            (-FR_B2_S *
                                                                                             t) *
                                                                                          (1 −
                                                                                           exp
                                                                                             (-FR_TL2_HR *
                                                                                              t))))) +
                                                                                       (exp
                                                                                          (-FR_TR1_S *
                                                                                           t) *
                                                                                        ((1 −
                                                                                          exp
                                                                                            (-FR_TR2_F *
                                                                                             t)) *
                                                                                         (exp
                                                                                            (-FR_TR3_S *
                                                                                             t) *
                                                                                          (exp
                                                                                             (-FR_B2_S *
                                                                                              t) *
                                                                                           (1 −
                                                                                            exp
                                                                                              (-FR_TL2_CR *
                                                                                               t))))) +
                                                                                        (exp
                                                                                           (-FR_TR1_S *
                                                                                            t) *
                                                                                         ((1 −
                                                                                           exp
                                                                                             (-FR_TR2_F *
                                                                                              t)) *
                                                                                          (exp
                                                                                             (-FR_TR3_S *
                                                                                              t) *
                                                                                           (exp
                                                                                              (-FR_B2_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TL2_FTL *
                                                                                                t))))) +
                                                                                         (exp
                                                                                            (-FR_TR1_S *
                                                                                             t) *
                                                                                          ((1 −
                                                                                            exp
                                                                                              (-FR_TR2_F *
                                                                                               t)) *
                                                                                           (exp
                                                                                              (-FR_TR3_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_B2_F *
                                                                                                t)))) +
                                                                                          (exp
                                                                                             (-FR_TR1_S *
                                                                                              t) *
                                                                                           ((1 −
                                                                                             exp
                                                                                               (-FR_TR2_F *
                                                                                                t)) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TR3_F *
                                                                                                t))) +
                                                                                           (exp
                                                                                              (-FR_TR1_S *
                                                                                               t) *
                                                                                            ((1 −
                                                                                              exp
                                                                                                (-FR_TR2_PF *
                                                                                                 t)) *
                                                                                             (exp
                                                                                                (-FR_TR3_S *
                                                                                                 t) *
                                                                                              (exp
                                                                                                 (-FR_B2_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_TL2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B4_S *
                                                                                                    t) *
                                                                                                 exp
                                                                                                   (-FR_TR5_S *
                                                                                                    t)))))) +
                                                                                            (exp
                                                                                               (-FR_TR1_S *
                                                                                                t) *
                                                                                             ((1 −
                                                                                               exp
                                                                                                 (-FR_TR2_PF *
                                                                                                  t)) *
                                                                                              (exp
                                                                                                 (-FR_TR3_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_B2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_TL2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B4_S *
                                                                                                     t) *
                                                                                                  (1 −
                                                                                                   exp
                                                                                                     (-FR_TR5_F *
                                                                                                      t))))))) +
                                                                                             (exp
                                                                                                (-FR_TR1_S *
                                                                                                 t) *
                                                                                              ((1 −
                                                                                                exp
                                                                                                  (-FR_TR2_PF *
                                                                                                   t)) *
                                                                                               (exp
                                                                                                  (-FR_TR3_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_TL2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B4_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TR5_PF *
                                                                                                       t))))))) +
                                                                                              (exp
                                                                                                 (-FR_TR1_S *
                                                                                                  t) *
                                                                                               ((1 −
                                                                                                 exp
                                                                                                   (-FR_TR2_PF *
                                                                                                    t)) *
                                                                                                (exp
                                                                                                   (-FR_TR3_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_TL2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_B4_F *
                                                                                                       t)))))) +
                                                                                               (exp
                                                                                                  (-FR_TR1_S *
                                                                                                   t) *
                                                                                                ((1 −
                                                                                                  exp
                                                                                                    (-FR_TR2_PF *
                                                                                                     t)) *
                                                                                                 (exp
                                                                                                    (-FR_TR3_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TL2_F *
                                                                                                       t))))) +
                                                                                                (exp
                                                                                                   (-FR_TR1_S *
                                                                                                    t) *
                                                                                                 ((1 −
                                                                                                   exp
                                                                                                     (-FR_TR2_PF *
                                                                                                      t)) *
                                                                                                  (exp
                                                                                                     (-FR_TR3_S *
                                                                                                      t) *
                                                                                                   (exp
                                                                                                      (-FR_B2_S *
                                                                                                       t) *
                                                                                                    (1 −
                                                                                                     exp
                                                                                                       (-FR_TL2_HR *
                                                                                                        t))))) +
                                                                                                 (exp
                                                                                                    (-FR_TR1_S *
                                                                                                     t) *
                                                                                                  ((1 −
                                                                                                    exp
                                                                                                      (-FR_TR2_PF *
                                                                                                       t)) *
                                                                                                   (exp
                                                                                                      (-FR_TR3_S *
                                                                                                       t) *
                                                                                                    (exp
                                                                                                       (-FR_B2_S *
                                                                                                        t) *
                                                                                                     (1 −
                                                                                                      exp
                                                                                                        (-FR_TL2_CR *
                                                                                                         t))))) +
                                                                                                  (exp
                                                                                                     (-FR_TR1_S *
                                                                                                      t) *
                                                                                                   ((1 −
                                                                                                     exp
                                                                                                       (-FR_TR2_PF *
                                                                                                        t)) *
                                                                                                    (exp
                                                                                                       (-FR_TR3_S *
                                                                                                        t) *
                                                                                                     (exp
                                                                                                        (-FR_B2_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TL2_FTL *
                                                                                                          t))))) +
                                                                                                   (exp
                                                                                                      (-FR_TR1_S *
                                                                                                       t) *
                                                                                                    ((1 −
                                                                                                      exp
                                                                                                        (-FR_TR2_PF *
                                                                                                         t)) *
                                                                                                     (exp
                                                                                                        (-FR_TR3_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_B2_F *
                                                                                                          t)))) +
                                                                                                    (exp
                                                                                                       (-FR_TR1_S *
                                                                                                        t) *
                                                                                                     ((1 −
                                                                                                       exp
                                                                                                         (-FR_TR2_PF *
                                                                                                          t)) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR3_F *
                                                                                                          t))) +
                                                                                                     (exp
                                                                                                        (-FR_TR1_S *
                                                                                                         t) *
                                                                                                      ((1 −
                                                                                                        exp
                                                                                                          (-FR_TR2_PF *
                                                                                                           t)) *
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR3_PF *
                                                                                                           t))) +
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR1_F *
                                                                                                          t) +
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR1_PF *
                                                                                                           t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * 80``;

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``LOEEp.u.``
``((exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_F * t)) * exp (-FR_TR5_S * t)))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * exp (-FR_TR5_S * t)))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * exp (-FR_TR4_S * t))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              ((1 − exp (-FR_B3_F * t)) *
               (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              ((1 − exp (-FR_TL2_F * t)) *
               (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               ((1 − exp (-FR_TL2_HR * t)) *
                (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                ((1 − exp (-FR_TL2_CR * t)) *
                 (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_FTL * t)) *
                  (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (exp (-FR_B1_S * t) *
                (exp (-FR_B2_S * t) *
                 ((1 − exp (-FR_TL1_F * t)) *
                  (exp (-FR_TL2_S * t) *
                   (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  ((1 − exp (-FR_TL1_HR * t)) *
                   (exp (-FR_TL2_S * t) *
                    (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   ((1 − exp (-FR_TL1_CR * t)) *
                    (exp (-FR_TL2_S * t) *
                     (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    ((1 − exp (-FR_TL1_FTL * t)) *
                     (exp (-FR_TL2_S * t) *
                      (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    ((1 − exp (-FR_B2_F * t)) *
                     (exp (-FR_TL1_S * t) *
                      (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    ((1 − exp (-FR_B1_F * t)) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL2_S * t) *
                       (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    ((1 − exp (-FR_TR3_F * t)) *
                     (exp (-FR_B1_S * t) * exp (-FR_TL1_S * t)))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     ((1 − exp (-FR_TR3_F * t)) * (1 − exp (-FR_B1_F * t)))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      ((1 − exp (-FR_TR3_PF * t)) * (1 − exp (-FR_B1_F * t)))) +
                     exp (-FR_TR1_S * t) *
                     ((1 − exp (-FR_TR2_F * t)) * (1 − exp (-FR_TR3_PF * t)))))))))))))))))))) * 1345 +
  (exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_F * t)))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              (exp (-FR_B3_S * t) *
               ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_PF * t)))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              (exp (-FR_TL2_S * t) *
               ((1 − exp (-FR_B3_F * t)) *
                (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_F * t)))))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               (exp (-FR_TL2_S * t) *
                ((1 − exp (-FR_B3_F * t)) *
                 (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_PF * t)))))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                (exp (-FR_TL2_S * t) *
                 ((1 − exp (-FR_B3_F * t)) * (1 − exp (-FR_B4_F * t))))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_F * t)) *
                  (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (RELIABILITY p B1 t *
                (RELIABILITY p B2 t *
                 (exp (-FR_TL1_S * t) *
                  ((1 − exp (-FR_TL2_F * t)) *
                   (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  (exp (-FR_TL1_S * t) *
                   ((1 − exp (-FR_TL2_F * t)) * (1 − exp (-FR_B3_F * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   (exp (-FR_TL1_S * t) *
                    ((1 − exp (-FR_TL2_HR * t)) *
                     (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    (exp (-FR_TL1_S * t) *
                     ((1 − exp (-FR_TL2_HR * t)) *
                      (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    (exp (-FR_B2_S * t) *
                     (exp (-FR_TL1_S * t) *
                      ((1 − exp (-FR_TL2_HR * t)) * (1 − exp (-FR_B3_F * t)))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    (exp (-FR_B1_S * t) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL1_S * t) *
                       ((1 − exp (-FR_TL2_CR * t)) *
                        (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    (exp (-FR_TR3_S * t) *
                     (exp (-FR_B1_S * t) *
                      (exp (-FR_B2_S * t) *
                       (exp (-FR_TL1_S * t) *
                        ((1 − exp (-FR_TL2_CR * t)) *
                         (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     (exp (-FR_TR3_S * t) *
                      (exp (-FR_B1_S * t) *
                       (exp (-FR_B2_S * t) *
                        (exp (-FR_TL1_S * t) *
                         ((1 − exp (-FR_TL2_CR * t)) *
                          (1 − exp (-FR_B3_F * t)))))))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      (exp (-FR_TR3_S * t) *
                       (exp (-FR_B1_S * t) *
                        (exp (-FR_B2_S * t) *
                         (exp (-FR_TL1_S * t) *
                          ((1 − exp (-FR_TL2_FTL * t)) *
                           (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                     (exp (-FR_TR1_S * t) *
                      (exp (-FR_TR2_S * t) *
                       (exp (-FR_TR3_S * t) *
                        (exp (-FR_B1_S * t) *
                         (exp (-FR_B2_S * t) *
                          (exp (-FR_TL1_S * t) *
                           ((1 − exp (-FR_TL2_FTL * t)) *
                            (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                      (exp (-FR_TR1_S * t) *
                       (exp (-FR_TR2_S * t) *
                        (exp (-FR_TR3_S * t) *
                         (exp (-FR_B1_S * t) *
                          (exp (-FR_B2_S * t) *
                           (exp (-FR_TL1_S * t) *
                            ((1 − exp (-FR_TL2_FTL * t)) *
                             (1 − exp (-FR_B3_F * t)))))))) +
                       (exp (-FR_TR1_S * t) *
                        (exp (-FR_TR2_S * t) *
                         (exp (-FR_TR3_S * t) *
                          (exp (-FR_B1_S * t) *
                           (exp (-FR_B2_S * t) *
                            ((1 − exp (-FR_TL1_F * t)) *
                             (exp (-FR_TL2_S * t) *
                              (exp (-FR_B4_S * t) *
                               (1 − exp (-FR_TR5_F * t))))))))) +
                        (exp (-FR_TR1_S * t) *
                         (exp (-FR_TR2_S * t) *
                          (exp (-FR_TR3_S * t) *
                           (exp (-FR_B1_S * t) *
                            (exp (-FR_B2_S * t) *
                             ((1 − exp (-FR_TL1_F * t)) *
                              (exp (-FR_TL2_S * t) *
                               (exp (-FR_B4_S * t) *
                                (1 − exp (-FR_TR5_PF * t))))))))) +
                         (exp (-FR_TR1_S * t) *
                          (exp (-FR_TR2_S * t) *
                           (exp (-FR_TR3_S * t) *
                            (exp (-FR_B1_S * t) *
                             (exp (-FR_B2_S * t) *
                              ((1 − exp (-FR_TL1_F * t)) *
                               (exp (-FR_TL2_S * t) *
                                (1 − exp (-FR_B4_F * t)))))))) +
                          (exp (-FR_TR1_S * t) *
                           (exp (-FR_TR2_S * t) *
                            (exp (-FR_TR3_S * t) *
                             (exp (-FR_B1_S * t) *
                              (exp (-FR_B2_S * t) *
                               ((1 − exp (-FR_TL1_F * t)) *
                                (1 − exp (-FR_TL2_F * t))))))) +
                           (exp (-FR_TR1_S * t) *
                            (exp (-FR_TR2_S * t) *
                             (exp (-FR_TR3_S * t) *
                              (exp (-FR_B1_S * t) *
                               (exp (-FR_B2_S * t) *
                                ((1 − exp (-FR_TL1_F * t)) *
                                 (1 − exp (-FR_TL2_HR * t))))))) +
                            (exp (-FR_TR1_S * t) *
                             (exp (-FR_TR2_S * t) *
                              (exp (-FR_TR3_S * t) *
                               (exp (-FR_B1_S * t) *
                                (exp (-FR_B2_S * t) *
                                 ((1 − exp (-FR_TL1_F * t)) *
                                  (1 − exp (-FR_TL2_CR * t))))))) +
                             (exp (-FR_TR1_S * t) *
                              (exp (-FR_TR2_S * t) *
                               (exp (-FR_TR3_S * t) *
                                (exp (-FR_B1_S * t) *
                                 (exp (-FR_B2_S * t) *
                                  ((1 − exp (-FR_TL1_F * t)) *
                                   (1 − exp (-FR_TL2_FTL * t))))))) +
                              (exp (-FR_TR1_S * t) *
                               (exp (-FR_TR2_S * t) *
                                (exp (-FR_TR3_S * t) *
                                 (exp (-FR_B1_S * t) *
                                  (exp (-FR_B2_S * t) *
                                   ((1 − exp (-FR_TL1_HR * t)) *
                                    (exp (-FR_TL2_S * t) *
                                     (exp (-FR_B4_S * t) *
                                      (1 − exp (-FR_TR5_F * t))))))))) +
                               (exp (-FR_TR1_S * t) *
                                (exp (-FR_TR2_S * t) *
                                 (exp (-FR_TR3_S * t) *
                                  (exp (-FR_B1_S * t) *
                                   (exp (-FR_B2_S * t) *
                                    ((1 − exp (-FR_TL1_HR * t)) *
                                     (exp (-FR_TL2_S * t) *
                                      (exp (-FR_B4_S * t) *
                                       (1 − exp (-FR_TR5_PF * t))))))))) +
                                (exp (-FR_TR1_S * t) *
                                 (exp (-FR_TR2_S * t) *
                                  (exp (-FR_TR3_S * t) *
                                   (exp (-FR_B1_S * t) *
                                    (exp (-FR_B2_S * t) *
                                     ((1 − exp (-FR_TL1_HR * t)) *
                                      (exp (-FR_TL2_S * t) *
                                       (1 − exp (-FR_B4_F * t)))))))) +
                                 (exp (-FR_TR1_S * t) *
                                  (exp (-FR_TR2_S * t) *
                                   (exp (-FR_TR3_S * t) *
                                    (exp (-FR_B1_S * t) *
                                     (exp (-FR_B2_S * t) *
                                      ((1 − exp (-FR_TL1_HR * t)) *
                                       (1 − exp (-FR_TL2_F * t))))))) +
                                  (exp (-FR_TR1_S * t) *
                                   (exp (-FR_TR2_S * t) *
                                    (exp (-FR_TR3_S * t) *
                                     (exp (-FR_B1_S * t) *
                                      (exp (-FR_B2_S * t) *
                                       ((1 − exp (-FR_TL1_HR * t)) *
                                        (1 − exp (-FR_TL2_HR * t))))))) +
                                   (exp (-FR_TR1_S * t) *
                                    (exp (-FR_TR2_S * t) *
                                     (exp (-FR_TR3_S * t) *
                                      (exp (-FR_B1_S * t) *
                                       (exp (-FR_B2_S * t) *
                                        ((1 − exp (-FR_TL1_HR * t)) *
                                         (1 − exp (-FR_TL2_CR * t))))))) +
                                    (exp (-FR_TR1_S * t) *
                                     (exp (-FR_TR2_S * t) *
                                      (exp (-FR_TR3_S * t) *
                                       (exp (-FR_B1_S * t) *
                                        (exp (-FR_B2_S * t) *
                                         ((1 − exp (-FR_TL1_HR * t)) *
                                          (1 − exp (-FR_TL2_FTL * t))))))) +
                                     (exp (-FR_TR1_S * t) *
                                      (exp (-FR_TR2_S * t) *
                                       (exp (-FR_TR3_S * t) *
                                        (exp (-FR_B1_S * t) *
                                         (exp (-FR_B2_S * t) *
                                          ((1 − exp (-FR_TL1_CR * t)) *
                                           (exp (-FR_TL2_S * t) *
                                            (exp (-FR_B4_S * t) *
                                             (1 − exp (-FR_TR5_F * t))))))))) +
                                      (exp (-FR_TR1_S * t) *
                                       (exp (-FR_TR2_S * t) *
                                        (exp (-FR_TR3_S * t) *
                                         (exp (-FR_B1_S * t) *
                                          (exp (-FR_B2_S * t) *
                                           ((1 − exp (-FR_TL1_CR * t)) *
                                            (exp (-FR_TL2_S * t) *
                                             (exp (-FR_B4_S * t) *
                                              (1 − exp (-FR_TR5_PF * t))))))))) +
                                       (exp (-FR_TR1_S * t) *
                                        (exp (-FR_TR2_S * t) *
                                         (exp (-FR_TR3_S * t) *
                                          (exp (-FR_B1_S * t) *
                                           (exp (-FR_B2_S * t) *
                                            ((1 − exp (-FR_TL1_CR * t)) *
                                             (exp (-FR_TL2_S * t) *
                                              (1 − exp (-FR_B4_F * t)))))))) +
                                        (exp (-FR_TR1_S * t) *
                                         (exp (-FR_TR2_S * t) *
                                          (exp (-FR_TR3_S * t) *
                                           (exp (-FR_B1_S * t) *
                                            (exp (-FR_B2_S * t) *
                                             ((1 − exp (-FR_TL1_CR * t)) *
                                              (1 − exp (-FR_TL2_F * t))))))) +
                                         (exp (-FR_TR1_S * t) *
                                          (exp (-FR_TR2_S * t) *
                                           (exp (-FR_TR3_S * t) *
                                            (exp (-FR_B1_S * t) *
                                             (exp (-FR_B2_S * t) *
                                              ((1 − exp (-FR_TL1_CR * t)) *
                                               (1 − exp (-FR_TL2_HR * t))))))) +
                                          (exp (-FR_TR1_S * t) *
                                           (exp (-FR_TR2_S * t) *
                                            (exp (-FR_TR3_S * t) *
                                             (exp (-FR_B1_S * t) *
                                              (exp (-FR_B2_S * t) *
                                               ((1 − exp (-FR_TL1_CR * t)) *
                                                (1 − exp (-FR_TL2_CR * t))))))) +
                                           (exp (-FR_TR1_S * t) *
                                            (exp (-FR_TR2_S * t) *
                                             (exp (-FR_TR3_S * t) *
                                              (exp (-FR_B1_S * t) *
                                               (exp (-FR_B2_S * t) *
                                                ((1 − exp (-FR_TL1_CR * t)) *
                                                 (1 − exp (-FR_TL2_FTL * t))))))) +
                                            (exp (-FR_TR1_S * t) *
                                             (exp (-FR_TR2_S * t) *
                                              (exp (-FR_TR3_S * t) *
                                               (exp (-FR_B1_S * t) *
                                                (exp (-FR_B2_S * t) *
                                                 ((1 − exp (-FR_TL1_FTL * t)) *
                                                  (exp (-FR_TL2_S * t) *
                                                   (exp (-FR_B4_S * t) *
                                                    (1 − exp (-FR_TR5_F * t))))))))) +
                                             (exp (-FR_TR1_S * t) *
                                              (exp (-FR_TR2_S * t) *
                                               (exp (-FR_TR3_S * t) *
                                                (exp (-FR_B1_S * t) *
                                                 (exp (-FR_B2_S * t) *
                                                  ((1 − exp (-FR_TL1_FTL * t)) *
                                                   (exp (-FR_TL2_S * t) *
                                                    (exp (-FR_B4_S * t) *
                                                     (1 −
                                                      exp (-FR_TR5_PF * t))))))))) +
                                              (exp (-FR_TR1_S * t) *
                                               (exp (-FR_TR2_S * t) *
                                                (exp (-FR_TR3_S * t) *
                                                 (exp (-FR_B1_S * t) *
                                                  (exp (-FR_B2_S * t) *
                                                   ((1 −
                                                     exp (-FR_TL1_FTL * t)) *
                                                    (exp (-FR_TL2_S * t) *
                                                     (1 − exp (-FR_B4_F * t)))))))) +
                                               (exp (-FR_TR1_S * t) *
                                                (exp (-FR_TR2_S * t) *
                                                 (exp (-FR_TR3_S * t) *
                                                  (exp (-FR_B1_S * t) *
                                                   (exp (-FR_B2_S * t) *
                                                    ((1 −
                                                      exp (-FR_TL1_FTL * t)) *
                                                     (1 − exp (-FR_TL2_F * t))))))) +
                                                (exp (-FR_TR1_S * t) *
                                                 (exp (-FR_TR2_S * t) *
                                                  (exp (-FR_TR3_S * t) *
                                                   (exp (-FR_B1_S * t) *
                                                    (exp (-FR_B2_S * t) *
                                                     ((1 −
                                                       exp (-FR_TL1_FTL * t)) *
                                                      (1 −
                                                       exp (-FR_TL2_HR * t))))))) +
                                                 (exp (-FR_TR1_S * t) *
                                                  (exp (-FR_TR2_S * t) *
                                                   (exp (-FR_TR3_S * t) *
                                                    (exp (-FR_B1_S * t) *
                                                     (exp (-FR_B2_S * t) *
                                                      ((1 −
                                                        exp (-FR_TL1_FTL * t)) *
                                                       (1 −
                                                        exp (-FR_TL2_CR * t))))))) +
                                                  (exp (-FR_TR1_S * t) *
                                                   (exp (-FR_TR2_S * t) *
                                                    (exp (-FR_TR3_S * t) *
                                                     (exp (-FR_B1_S * t) *
                                                      (exp (-FR_B2_S * t) *
                                                       ((1 −
                                                         exp
                                                           (-FR_TL1_FTL * t)) *
                                                        (1 −
                                                         exp
                                                           (-FR_TL2_FTL * t))))))) +
                                                   (exp (-FR_TR1_S * t) *
                                                    (exp (-FR_TR2_S * t) *
                                                     (exp (-FR_TR3_S * t) *
                                                      (exp (-FR_B1_S * t) *
                                                       ((1 −
                                                         exp (-FR_B2_F * t)) *
                                                        (exp (-FR_TL1_S * t) *
                                                         (exp (-FR_B3_S * t) *
                                                          (1 −
                                                           exp
                                                             (-FR_TR4_F * t)))))))) +
                                                    (exp (-FR_TR1_S * t) *
                                                     (exp (-FR_TR2_S * t) *
                                                      (exp (-FR_TR3_S * t) *
                                                       (exp (-FR_B1_S * t) *
                                                        ((1 −
                                                          exp (-FR_B2_F * t)) *
                                                         (exp (-FR_TL1_S * t) *
                                                          (exp (-FR_B3_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_TR4_PF * t)))))))) +
                                                     (exp (-FR_TR1_S * t) *
                                                      (exp (-FR_TR2_S * t) *
                                                       (exp (-FR_TR3_S * t) *
                                                        (exp (-FR_B1_S * t) *
                                                         ((1 −
                                                           exp (-FR_B2_F * t)) *
                                                          (exp
                                                             (-FR_TL1_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_B3_F * t))))))) +
                                                      (exp (-FR_TR1_S * t) *
                                                       (exp (-FR_TR2_S * t) *
                                                        (exp (-FR_TR3_S * t) *
                                                         (exp (-FR_B1_S * t) *
                                                          ((1 −
                                                            exp
                                                              (-FR_B2_F * t)) *
                                                           (1 −
                                                            exp
                                                              (-FR_TL1_F * t)))))) +
                                                       (exp (-FR_TR1_S * t) *
                                                        (exp (-FR_TR2_S * t) *
                                                         (exp (-FR_TR3_S * t) *
                                                          (exp (-FR_B1_S * t) *
                                                           ((1 −
                                                             exp
                                                               (-FR_B2_F * t)) *
                                                            (1 −
                                                             exp
                                                               (-FR_TL1_HR *
                                                                t)))))) +
                                                        (exp (-FR_TR1_S * t) *
                                                         (exp (-FR_TR2_S * t) *
                                                          (exp
                                                             (-FR_TR3_S * t) *
                                                           (exp
                                                              (-FR_B1_S * t) *
                                                            ((1 −
                                                              exp
                                                                (-FR_B2_F * t)) *
                                                             (1 −
                                                              exp
                                                                (-FR_TL1_CR *
                                                                 t)))))) +
                                                         (exp (-FR_TR1_S * t) *
                                                          (exp
                                                             (-FR_TR2_S * t) *
                                                           (exp
                                                              (-FR_TR3_S * t) *
                                                            (exp
                                                               (-FR_B1_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B2_F *
                                                                  t)) *
                                                              (1 −
                                                               exp
                                                                 (-FR_TL1_FTL *
                                                                  t)))))) +
                                                          (exp
                                                             (-FR_TR1_S * t) *
                                                           (exp
                                                              (-FR_TR2_S * t) *
                                                            (exp
                                                               (-FR_TR3_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B1_F *
                                                                  t)) *
                                                              (exp
                                                                 (-FR_B2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TL2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_B4_S *
                                                                    t) *
                                                                 (1 −
                                                                  exp
                                                                    (-FR_TR5_F *
                                                                     t)))))))) +
                                                           (exp
                                                              (-FR_TR1_S * t) *
                                                            (exp
                                                               (-FR_TR2_S * t) *
                                                             (exp
                                                                (-FR_TR3_S *
                                                                 t) *
                                                              ((1 −
                                                                exp
                                                                  (-FR_B1_F *
                                                                   t)) *
                                                               (exp
                                                                  (-FR_B2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TL2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_B4_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TR5_PF *
                                                                      t)))))))) +
                                                            (exp
                                                               (-FR_TR1_S * t) *
                                                             (exp
                                                                (-FR_TR2_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR3_S *
                                                                  t) *
                                                               ((1 −
                                                                 exp
                                                                   (-FR_B1_F *
                                                                    t)) *
                                                                (exp
                                                                   (-FR_B2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TL2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_B4_F *
                                                                      t))))))) +
                                                             (exp
                                                                (-FR_TR1_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR3_S *
                                                                   t) *
                                                                ((1 −
                                                                  exp
                                                                    (-FR_B1_F *
                                                                     t)) *
                                                                 (exp
                                                                    (-FR_B2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TL2_F *
                                                                      t)))))) +
                                                              (exp
                                                                 (-FR_TR1_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR3_S *
                                                                    t) *
                                                                 ((1 −
                                                                   exp
                                                                     (-FR_B1_F *
                                                                      t)) *
                                                                  (exp
                                                                     (-FR_B2_S *
                                                                      t) *
                                                                   (1 −
                                                                    exp
                                                                      (-FR_TL2_HR *
                                                                       t)))))) +
                                                               (exp
                                                                  (-FR_TR1_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR3_S *
                                                                     t) *
                                                                  ((1 −
                                                                    exp
                                                                      (-FR_B1_F *
                                                                       t)) *
                                                                   (exp
                                                                      (-FR_B2_S *
                                                                       t) *
                                                                    (1 −
                                                                     exp
                                                                       (-FR_TL2_CR *
                                                                        t)))))) +
                                                                (exp
                                                                   (-FR_TR1_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR2_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR3_S *
                                                                      t) *
                                                                   ((1 −
                                                                     exp
                                                                       (-FR_B1_F *
                                                                        t)) *
                                                                    (exp
                                                                       (-FR_B2_S *
                                                                        t) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_TL2_FTL *
                                                                         t)))))) +
                                                                 (exp
                                                                    (-FR_TR1_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR2_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR3_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_B1_F *
                                                                         t)) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_B2_F *
                                                                         t))))) +
                                                                  (exp
                                                                     (-FR_TR1_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR2_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_TR3_F *
                                                                         t)) *
                                                                     (exp
                                                                        (-FR_B1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TL1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_B3_S *
                                                                           t) *
                                                                        (1 −
                                                                         exp
                                                                           (-FR_TR4_F *
                                                                            t))))))) +
                                                                   (exp
                                                                      (-FR_TR1_S *
                                                                       t) *
                                                                    (exp
                                                                       (-FR_TR2_S *
                                                                        t) *
                                                                     ((1 −
                                                                       exp
                                                                         (-FR_TR3_F *
                                                                          t)) *
                                                                      (exp
                                                                         (-FR_B1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TL1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_B3_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TR4_PF *
                                                                             t))))))) +
                                                                    (exp
                                                                       (-FR_TR1_S *
                                                                        t) *
                                                                     (exp
                                                                        (-FR_TR2_S *
                                                                         t) *
                                                                      ((1 −
                                                                        exp
                                                                          (-FR_TR3_F *
                                                                           t)) *
                                                                       (exp
                                                                          (-FR_B1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TL1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_B3_F *
                                                                             t)))))) +
                                                                     (exp
                                                                        (-FR_TR1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TR2_S *
                                                                          t) *
                                                                       ((1 −
                                                                         exp
                                                                           (-FR_TR3_F *
                                                                            t)) *
                                                                        (exp
                                                                           (-FR_B1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TL1_F *
                                                                             t))))) +
                                                                      (exp
                                                                         (-FR_TR1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TR2_S *
                                                                           t) *
                                                                        ((1 −
                                                                          exp
                                                                            (-FR_TR3_F *
                                                                             t)) *
                                                                         (exp
                                                                            (-FR_B1_S *
                                                                             t) *
                                                                          (1 −
                                                                           exp
                                                                             (-FR_TL1_HR *
                                                                              t))))) +
                                                                       (exp
                                                                          (-FR_TR1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TR2_S *
                                                                            t) *
                                                                         ((1 −
                                                                           exp
                                                                             (-FR_TR3_F *
                                                                              t)) *
                                                                          (exp
                                                                             (-FR_B1_S *
                                                                              t) *
                                                                           (1 −
                                                                            exp
                                                                              (-FR_TL1_CR *
                                                                               t))))) +
                                                                        (exp
                                                                           (-FR_TR1_S *
                                                                            t) *
                                                                         (exp
                                                                            (-FR_TR2_S *
                                                                             t) *
                                                                          ((1 −
                                                                            exp
                                                                              (-FR_TR3_F *
                                                                               t)) *
                                                                           (exp
                                                                              (-FR_B1_S *
                                                                               t) *
                                                                            (1 −
                                                                             exp
                                                                               (-FR_TL1_FTL *
                                                                                t))))) +
                                                                         (exp
                                                                            (-FR_TR1_S *
                                                                             t) *
                                                                          (exp
                                                                             (-FR_TR2_S *
                                                                              t) *
                                                                           ((1 −
                                                                             exp
                                                                               (-FR_TR3_PF *
                                                                                t)) *
                                                                            (exp
                                                                               (-FR_B1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TL1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_B3_S *
                                                                                  t) *
                                                                               exp
                                                                                 (-FR_TR4_S *
                                                                                  t)))))) +
                                                                          (exp
                                                                             (-FR_TR1_S *
                                                                              t) *
                                                                           (exp
                                                                              (-FR_TR2_S *
                                                                               t) *
                                                                            ((1 −
                                                                              exp
                                                                                (-FR_TR3_PF *
                                                                                 t)) *
                                                                             (exp
                                                                                (-FR_B1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TL1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_B3_S *
                                                                                   t) *
                                                                                (1 −
                                                                                 exp
                                                                                   (-FR_TR4_F *
                                                                                    t))))))) +
                                                                           (exp
                                                                              (-FR_TR1_S *
                                                                               t) *
                                                                            (exp
                                                                               (-FR_TR2_S *
                                                                                t) *
                                                                             ((1 −
                                                                               exp
                                                                                 (-FR_TR3_PF *
                                                                                  t)) *
                                                                              (exp
                                                                                 (-FR_B1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TL1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_B3_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TR4_PF *
                                                                                     t))))))) +
                                                                            (exp
                                                                               (-FR_TR1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TR2_S *
                                                                                 t) *
                                                                              ((1 −
                                                                                exp
                                                                                  (-FR_TR3_PF *
                                                                                   t)) *
                                                                               (exp
                                                                                  (-FR_B1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TL1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_B3_F *
                                                                                     t)))))) +
                                                                             (exp
                                                                                (-FR_TR1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TR2_S *
                                                                                  t) *
                                                                               ((1 −
                                                                                 exp
                                                                                   (-FR_TR3_PF *
                                                                                    t)) *
                                                                                (exp
                                                                                   (-FR_B1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TL1_F *
                                                                                     t))))) +
                                                                              (exp
                                                                                 (-FR_TR1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TR2_S *
                                                                                   t) *
                                                                                ((1 −
                                                                                  exp
                                                                                    (-FR_TR3_PF *
                                                                                     t)) *
                                                                                 (exp
                                                                                    (-FR_B1_S *
                                                                                     t) *
                                                                                  (1 −
                                                                                   exp
                                                                                     (-FR_TL1_HR *
                                                                                      t))))) +
                                                                               (exp
                                                                                  (-FR_TR1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TR2_S *
                                                                                    t) *
                                                                                 ((1 −
                                                                                   exp
                                                                                     (-FR_TR3_PF *
                                                                                      t)) *
                                                                                  (exp
                                                                                     (-FR_B1_S *
                                                                                      t) *
                                                                                   (1 −
                                                                                    exp
                                                                                      (-FR_TL1_CR *
                                                                                       t))))) +
                                                                                (exp
                                                                                   (-FR_TR1_S *
                                                                                    t) *
                                                                                 (exp
                                                                                    (-FR_TR2_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR3_PF *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_B1_S *
                                                                                       t) *
                                                                                    (1 −
                                                                                     exp
                                                                                       (-FR_TL1_FTL *
                                                                                        t))))) +
                                                                                 (exp
                                                                                    (-FR_TR1_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR2_F *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_TR3_S *
                                                                                       t) *
                                                                                    (exp
                                                                                       (-FR_B2_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_TL2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B4_S *
                                                                                          t) *
                                                                                       exp
                                                                                         (-FR_TR5_S *
                                                                                          t)))))) +
                                                                                  (exp
                                                                                     (-FR_TR1_S *
                                                                                      t) *
                                                                                   ((1 −
                                                                                     exp
                                                                                       (-FR_TR2_F *
                                                                                        t)) *
                                                                                    (exp
                                                                                       (-FR_TR3_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_B2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_TL2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B4_S *
                                                                                           t) *
                                                                                        (1 −
                                                                                         exp
                                                                                           (-FR_TR5_F *
                                                                                            t))))))) +
                                                                                   (exp
                                                                                      (-FR_TR1_S *
                                                                                       t) *
                                                                                    ((1 −
                                                                                      exp
                                                                                        (-FR_TR2_F *
                                                                                         t)) *
                                                                                     (exp
                                                                                        (-FR_TR3_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_TL2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B4_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TR5_PF *
                                                                                             t))))))) +
                                                                                    (exp
                                                                                       (-FR_TR1_S *
                                                                                        t) *
                                                                                     ((1 −
                                                                                       exp
                                                                                         (-FR_TR2_F *
                                                                                          t)) *
                                                                                      (exp
                                                                                         (-FR_TR3_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_TL2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_B4_F *
                                                                                             t)))))) +
                                                                                     (exp
                                                                                        (-FR_TR1_S *
                                                                                         t) *
                                                                                      ((1 −
                                                                                        exp
                                                                                          (-FR_TR2_F *
                                                                                           t)) *
                                                                                       (exp
                                                                                          (-FR_TR3_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TL2_F *
                                                                                             t))))) +
                                                                                      (exp
                                                                                         (-FR_TR1_S *
                                                                                          t) *
                                                                                       ((1 −
                                                                                         exp
                                                                                           (-FR_TR2_F *
                                                                                            t)) *
                                                                                        (exp
                                                                                           (-FR_TR3_S *
                                                                                            t) *
                                                                                         (exp
                                                                                            (-FR_B2_S *
                                                                                             t) *
                                                                                          (1 −
                                                                                           exp
                                                                                             (-FR_TL2_HR *
                                                                                              t))))) +
                                                                                       (exp
                                                                                          (-FR_TR1_S *
                                                                                           t) *
                                                                                        ((1 −
                                                                                          exp
                                                                                            (-FR_TR2_F *
                                                                                             t)) *
                                                                                         (exp
                                                                                            (-FR_TR3_S *
                                                                                             t) *
                                                                                          (exp
                                                                                             (-FR_B2_S *
                                                                                              t) *
                                                                                           (1 −
                                                                                            exp
                                                                                              (-FR_TL2_CR *
                                                                                               t))))) +
                                                                                        (exp
                                                                                           (-FR_TR1_S *
                                                                                            t) *
                                                                                         ((1 −
                                                                                           exp
                                                                                             (-FR_TR2_F *
                                                                                              t)) *
                                                                                          (exp
                                                                                             (-FR_TR3_S *
                                                                                              t) *
                                                                                           (exp
                                                                                              (-FR_B2_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TL2_FTL *
                                                                                                t))))) +
                                                                                         (exp
                                                                                            (-FR_TR1_S *
                                                                                             t) *
                                                                                          ((1 −
                                                                                            exp
                                                                                              (-FR_TR2_F *
                                                                                               t)) *
                                                                                           (exp
                                                                                              (-FR_TR3_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_B2_F *
                                                                                                t)))) +
                                                                                          (exp
                                                                                             (-FR_TR1_S *
                                                                                              t) *
                                                                                           ((1 −
                                                                                             exp
                                                                                               (-FR_TR2_F *
                                                                                                t)) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TR3_F *
                                                                                                t))) +
                                                                                           (exp
                                                                                              (-FR_TR1_S *
                                                                                               t) *
                                                                                            ((1 −
                                                                                              exp
                                                                                                (-FR_TR2_PF *
                                                                                                 t)) *
                                                                                             (exp
                                                                                                (-FR_TR3_S *
                                                                                                 t) *
                                                                                              (exp
                                                                                                 (-FR_B2_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_TL2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B4_S *
                                                                                                    t) *
                                                                                                 exp
                                                                                                   (-FR_TR5_S *
                                                                                                    t)))))) +
                                                                                            (exp
                                                                                               (-FR_TR1_S *
                                                                                                t) *
                                                                                             ((1 −
                                                                                               exp
                                                                                                 (-FR_TR2_PF *
                                                                                                  t)) *
                                                                                              (exp
                                                                                                 (-FR_TR3_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_B2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_TL2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B4_S *
                                                                                                     t) *
                                                                                                  (1 −
                                                                                                   exp
                                                                                                     (-FR_TR5_F *
                                                                                                      t))))))) +
                                                                                             (exp
                                                                                                (-FR_TR1_S *
                                                                                                 t) *
                                                                                              ((1 −
                                                                                                exp
                                                                                                  (-FR_TR2_PF *
                                                                                                   t)) *
                                                                                               (exp
                                                                                                  (-FR_TR3_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_TL2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B4_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TR5_PF *
                                                                                                       t))))))) +
                                                                                              (exp
                                                                                                 (-FR_TR1_S *
                                                                                                  t) *
                                                                                               ((1 −
                                                                                                 exp
                                                                                                   (-FR_TR2_PF *
                                                                                                    t)) *
                                                                                                (exp
                                                                                                   (-FR_TR3_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_TL2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_B4_F *
                                                                                                       t)))))) +
                                                                                               (exp
                                                                                                  (-FR_TR1_S *
                                                                                                   t) *
                                                                                                ((1 −
                                                                                                  exp
                                                                                                    (-FR_TR2_PF *
                                                                                                     t)) *
                                                                                                 (exp
                                                                                                    (-FR_TR3_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TL2_F *
                                                                                                       t))))) +
                                                                                                (exp
                                                                                                   (-FR_TR1_S *
                                                                                                    t) *
                                                                                                 ((1 −
                                                                                                   exp
                                                                                                     (-FR_TR2_PF *
                                                                                                      t)) *
                                                                                                  (exp
                                                                                                     (-FR_TR3_S *
                                                                                                      t) *
                                                                                                   (exp
                                                                                                      (-FR_B2_S *
                                                                                                       t) *
                                                                                                    (1 −
                                                                                                     exp
                                                                                                       (-FR_TL2_HR *
                                                                                                        t))))) +
                                                                                                 (exp
                                                                                                    (-FR_TR1_S *
                                                                                                     t) *
                                                                                                  ((1 −
                                                                                                    exp
                                                                                                      (-FR_TR2_PF *
                                                                                                       t)) *
                                                                                                   (exp
                                                                                                      (-FR_TR3_S *
                                                                                                       t) *
                                                                                                    (exp
                                                                                                       (-FR_B2_S *
                                                                                                        t) *
                                                                                                     (1 −
                                                                                                      exp
                                                                                                        (-FR_TL2_CR *
                                                                                                         t))))) +
                                                                                                  (exp
                                                                                                     (-FR_TR1_S *
                                                                                                      t) *
                                                                                                   ((1 −
                                                                                                     exp
                                                                                                       (-FR_TR2_PF *
                                                                                                        t)) *
                                                                                                    (exp
                                                                                                       (-FR_TR3_S *
                                                                                                        t) *
                                                                                                     (exp
                                                                                                        (-FR_B2_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TL2_FTL *
                                                                                                          t))))) +
                                                                                                   (exp
                                                                                                      (-FR_TR1_S *
                                                                                                       t) *
                                                                                                    ((1 −
                                                                                                      exp
                                                                                                        (-FR_TR2_PF *
                                                                                                         t)) *
                                                                                                     (exp
                                                                                                        (-FR_TR3_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_B2_F *
                                                                                                          t)))) +
                                                                                                    (exp
                                                                                                       (-FR_TR1_S *
                                                                                                        t) *
                                                                                                     ((1 −
                                                                                                       exp
                                                                                                         (-FR_TR2_PF *
                                                                                                          t)) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR3_F *
                                                                                                          t))) +
                                                                                                     (exp
                                                                                                        (-FR_TR1_S *
                                                                                                         t) *
                                                                                                      ((1 −
                                                                                                        exp
                                                                                                          (-FR_TR2_PF *
                                                                                                           t)) *
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR3_PF *
                                                                                                           t))) +
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR1_F *
                                                                                                          t) +
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR1_PF *
                                                                                                           t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * 2690) / 2690``;

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``EIR``
``1 -
  (((exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            (exp (-FR_TR4_S * t) * (1 − exp (-FR_TR4_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_F * t)) * exp (-FR_TR5_S * t)))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * exp (-FR_TR5_S * t)))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * exp (-FR_TR4_S * t))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              ((1 − exp (-FR_B3_F * t)) *
               (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              ((1 − exp (-FR_TL2_F * t)) *
               (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               ((1 − exp (-FR_TL2_HR * t)) *
                (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                ((1 − exp (-FR_TL2_CR * t)) *
                 (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_FTL * t)) *
                  (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t)))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (exp (-FR_B1_S * t) *
                (exp (-FR_B2_S * t) *
                 ((1 − exp (-FR_TL1_F * t)) *
                  (exp (-FR_TL2_S * t) *
                   (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  ((1 − exp (-FR_TL1_HR * t)) *
                   (exp (-FR_TL2_S * t) *
                    (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   ((1 − exp (-FR_TL1_CR * t)) *
                    (exp (-FR_TL2_S * t) *
                     (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    ((1 − exp (-FR_TL1_FTL * t)) *
                     (exp (-FR_TL2_S * t) *
                      (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t)))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    ((1 − exp (-FR_B2_F * t)) *
                     (exp (-FR_TL1_S * t) *
                      (exp (-FR_B3_S * t) * exp (-FR_TR4_S * t))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    ((1 − exp (-FR_B1_F * t)) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL2_S * t) *
                       (exp (-FR_B4_S * t) * exp (-FR_TR5_S * t))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    ((1 − exp (-FR_TR3_F * t)) *
                     (exp (-FR_B1_S * t) * exp (-FR_TL1_S * t)))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     ((1 − exp (-FR_TR3_F * t)) * (1 − exp (-FR_B1_F * t)))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      ((1 − exp (-FR_TR3_PF * t)) * (1 − exp (-FR_B1_F * t)))) +
                     exp (-FR_TR1_S * t) *
                     ((1 − exp (-FR_TR2_F * t)) * (1 − exp (-FR_TR3_PF * t)))))))))))))))))))) * 1345 +
  (exp (-FR_TR1_S * t) *
   (exp (-FR_TR2_S * t) *
    (exp (-FR_TR3_S * t) *
     (exp (-FR_B1_S * t) *
      (exp (-FR_B2_S * t) *
       (exp (-FR_TL1_S * t) *
        (exp (-FR_TL2_S * t) *
         (exp (-FR_B3_S * t) *
          (exp (-FR_B4_S * t) *
           ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
   (exp (-FR_TR1_S * t) *
    (exp (-FR_TR2_S * t) *
     (exp (-FR_TR3_S * t) *
      (exp (-FR_B1_S * t) *
       (exp (-FR_B2_S * t) *
        (exp (-FR_TL1_S * t) *
         (exp (-FR_TL2_S * t) *
          (exp (-FR_B3_S * t) *
           (exp (-FR_B4_S * t) *
            ((1 − exp (-FR_TR4_F * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
    (exp (-FR_TR1_S * t) *
     (exp (-FR_TR2_S * t) *
      (exp (-FR_TR3_S * t) *
       (exp (-FR_B1_S * t) *
        (exp (-FR_B2_S * t) *
         (exp (-FR_TL1_S * t) *
          (exp (-FR_TL2_S * t) *
           (exp (-FR_B3_S * t) *
            (exp (-FR_B4_S * t) *
             ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_F * t))))))))))) +
     (exp (-FR_TR1_S * t) *
      (exp (-FR_TR2_S * t) *
       (exp (-FR_TR3_S * t) *
        (exp (-FR_B1_S * t) *
         (exp (-FR_B2_S * t) *
          (exp (-FR_TL1_S * t) *
           (exp (-FR_TL2_S * t) *
            (exp (-FR_B3_S * t) *
             (exp (-FR_B4_S * t) *
              ((1 − exp (-FR_TR4_PF * t)) * (1 − exp (-FR_TR5_PF * t))))))))))) +
      (exp (-FR_TR1_S * t) *
       (exp (-FR_TR2_S * t) *
        (exp (-FR_TR3_S * t) *
         (exp (-FR_B1_S * t) *
          (exp (-FR_B2_S * t) *
           (exp (-FR_TL1_S * t) *
            (exp (-FR_TL2_S * t) *
             (exp (-FR_B3_S * t) *
              ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_F * t)))))))))) +
       (exp (-FR_TR1_S * t) *
        (exp (-FR_TR2_S * t) *
         (exp (-FR_TR3_S * t) *
          (exp (-FR_B1_S * t) *
           (exp (-FR_B2_S * t) *
            (exp (-FR_TL1_S * t) *
             (exp (-FR_TL2_S * t) *
              (exp (-FR_B3_S * t) *
               ((1 − exp (-FR_B4_F * t)) * (1 − exp (-FR_TR4_PF * t)))))))))) +
        (exp (-FR_TR1_S * t) *
         (exp (-FR_TR2_S * t) *
          (exp (-FR_TR3_S * t) *
           (exp (-FR_B1_S * t) *
            (exp (-FR_B2_S * t) *
             (exp (-FR_TL1_S * t) *
              (exp (-FR_TL2_S * t) *
               ((1 − exp (-FR_B3_F * t)) *
                (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_F * t)))))))))) +
         (exp (-FR_TR1_S * t) *
          (exp (-FR_TR2_S * t) *
           (exp (-FR_TR3_S * t) *
            (exp (-FR_B1_S * t) *
             (exp (-FR_B2_S * t) *
              (exp (-FR_TL1_S * t) *
               (exp (-FR_TL2_S * t) *
                ((1 − exp (-FR_B3_F * t)) *
                 (exp (-FR_B4_S * t) * (1 − exp (-FR_TR5_PF * t)))))))))) +
          (exp (-FR_TR1_S * t) *
           (exp (-FR_TR2_S * t) *
            (exp (-FR_TR3_S * t) *
             (exp (-FR_B1_S * t) *
              (exp (-FR_B2_S * t) *
               (exp (-FR_TL1_S * t) *
                (exp (-FR_TL2_S * t) *
                 ((1 − exp (-FR_B3_F * t)) * (1 − exp (-FR_B4_F * t))))))))) +
           (exp (-FR_TR1_S * t) *
            (exp (-FR_TR2_S * t) *
             (exp (-FR_TR3_S * t) *
              (exp (-FR_B1_S * t) *
               (exp (-FR_B2_S * t) *
                (exp (-FR_TL1_S * t) *
                 ((1 − exp (-FR_TL2_F * t)) *
                  (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
            (exp (-FR_TR1_S * t) *
             (exp (-FR_TR2_S * t) *
              (exp (-FR_TR3_S * t) *
               (RELIABILITY p B1 t *
                (RELIABILITY p B2 t *
                 (exp (-FR_TL1_S * t) *
                  ((1 − exp (-FR_TL2_F * t)) *
                   (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
             (exp (-FR_TR1_S * t) *
              (exp (-FR_TR2_S * t) *
               (exp (-FR_TR3_S * t) *
                (exp (-FR_B1_S * t) *
                 (exp (-FR_B2_S * t) *
                  (exp (-FR_TL1_S * t) *
                   ((1 − exp (-FR_TL2_F * t)) * (1 − exp (-FR_B3_F * t)))))))) +
              (exp (-FR_TR1_S * t) *
               (exp (-FR_TR2_S * t) *
                (exp (-FR_TR3_S * t) *
                 (exp (-FR_B1_S * t) *
                  (exp (-FR_B2_S * t) *
                   (exp (-FR_TL1_S * t) *
                    ((1 − exp (-FR_TL2_HR * t)) *
                     (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
               (exp (-FR_TR1_S * t) *
                (exp (-FR_TR2_S * t) *
                 (exp (-FR_TR3_S * t) *
                  (exp (-FR_B1_S * t) *
                   (exp (-FR_B2_S * t) *
                    (exp (-FR_TL1_S * t) *
                     ((1 − exp (-FR_TL2_HR * t)) *
                      (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                (exp (-FR_TR1_S * t) *
                 (exp (-FR_TR2_S * t) *
                  (exp (-FR_TR3_S * t) *
                   (exp (-FR_B1_S * t) *
                    (exp (-FR_B2_S * t) *
                     (exp (-FR_TL1_S * t) *
                      ((1 − exp (-FR_TL2_HR * t)) * (1 − exp (-FR_B3_F * t)))))))) +
                 (exp (-FR_TR1_S * t) *
                  (exp (-FR_TR2_S * t) *
                   (exp (-FR_TR3_S * t) *
                    (exp (-FR_B1_S * t) *
                     (exp (-FR_B2_S * t) *
                      (exp (-FR_TL1_S * t) *
                       ((1 − exp (-FR_TL2_CR * t)) *
                        (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                  (exp (-FR_TR1_S * t) *
                   (exp (-FR_TR2_S * t) *
                    (exp (-FR_TR3_S * t) *
                     (exp (-FR_B1_S * t) *
                      (exp (-FR_B2_S * t) *
                       (exp (-FR_TL1_S * t) *
                        ((1 − exp (-FR_TL2_CR * t)) *
                         (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                   (exp (-FR_TR1_S * t) *
                    (exp (-FR_TR2_S * t) *
                     (exp (-FR_TR3_S * t) *
                      (exp (-FR_B1_S * t) *
                       (exp (-FR_B2_S * t) *
                        (exp (-FR_TL1_S * t) *
                         ((1 − exp (-FR_TL2_CR * t)) *
                          (1 − exp (-FR_B3_F * t)))))))) +
                    (exp (-FR_TR1_S * t) *
                     (exp (-FR_TR2_S * t) *
                      (exp (-FR_TR3_S * t) *
                       (exp (-FR_B1_S * t) *
                        (exp (-FR_B2_S * t) *
                         (exp (-FR_TL1_S * t) *
                          ((1 − exp (-FR_TL2_FTL * t)) *
                           (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_F * t))))))))) +
                     (exp (-FR_TR1_S * t) *
                      (exp (-FR_TR2_S * t) *
                       (exp (-FR_TR3_S * t) *
                        (exp (-FR_B1_S * t) *
                         (exp (-FR_B2_S * t) *
                          (exp (-FR_TL1_S * t) *
                           ((1 − exp (-FR_TL2_FTL * t)) *
                            (exp (-FR_B3_S * t) * (1 − exp (-FR_TR4_PF * t))))))))) +
                      (exp (-FR_TR1_S * t) *
                       (exp (-FR_TR2_S * t) *
                        (exp (-FR_TR3_S * t) *
                         (exp (-FR_B1_S * t) *
                          (exp (-FR_B2_S * t) *
                           (exp (-FR_TL1_S * t) *
                            ((1 − exp (-FR_TL2_FTL * t)) *
                             (1 − exp (-FR_B3_F * t)))))))) +
                       (exp (-FR_TR1_S * t) *
                        (exp (-FR_TR2_S * t) *
                         (exp (-FR_TR3_S * t) *
                          (exp (-FR_B1_S * t) *
                           (exp (-FR_B2_S * t) *
                            ((1 − exp (-FR_TL1_F * t)) *
                             (exp (-FR_TL2_S * t) *
                              (exp (-FR_B4_S * t) *
                               (1 − exp (-FR_TR5_F * t))))))))) +
                        (exp (-FR_TR1_S * t) *
                         (exp (-FR_TR2_S * t) *
                          (exp (-FR_TR3_S * t) *
                           (exp (-FR_B1_S * t) *
                            (exp (-FR_B2_S * t) *
                             ((1 − exp (-FR_TL1_F * t)) *
                              (exp (-FR_TL2_S * t) *
                               (exp (-FR_B4_S * t) *
                                (1 − exp (-FR_TR5_PF * t))))))))) +
                         (exp (-FR_TR1_S * t) *
                          (exp (-FR_TR2_S * t) *
                           (exp (-FR_TR3_S * t) *
                            (exp (-FR_B1_S * t) *
                             (exp (-FR_B2_S * t) *
                              ((1 − exp (-FR_TL1_F * t)) *
                               (exp (-FR_TL2_S * t) *
                                (1 − exp (-FR_B4_F * t)))))))) +
                          (exp (-FR_TR1_S * t) *
                           (exp (-FR_TR2_S * t) *
                            (exp (-FR_TR3_S * t) *
                             (exp (-FR_B1_S * t) *
                              (exp (-FR_B2_S * t) *
                               ((1 − exp (-FR_TL1_F * t)) *
                                (1 − exp (-FR_TL2_F * t))))))) +
                           (exp (-FR_TR1_S * t) *
                            (exp (-FR_TR2_S * t) *
                             (exp (-FR_TR3_S * t) *
                              (exp (-FR_B1_S * t) *
                               (exp (-FR_B2_S * t) *
                                ((1 − exp (-FR_TL1_F * t)) *
                                 (1 − exp (-FR_TL2_HR * t))))))) +
                            (exp (-FR_TR1_S * t) *
                             (exp (-FR_TR2_S * t) *
                              (exp (-FR_TR3_S * t) *
                               (exp (-FR_B1_S * t) *
                                (exp (-FR_B2_S * t) *
                                 ((1 − exp (-FR_TL1_F * t)) *
                                  (1 − exp (-FR_TL2_CR * t))))))) +
                             (exp (-FR_TR1_S * t) *
                              (exp (-FR_TR2_S * t) *
                               (exp (-FR_TR3_S * t) *
                                (exp (-FR_B1_S * t) *
                                 (exp (-FR_B2_S * t) *
                                  ((1 − exp (-FR_TL1_F * t)) *
                                   (1 − exp (-FR_TL2_FTL * t))))))) +
                              (exp (-FR_TR1_S * t) *
                               (exp (-FR_TR2_S * t) *
                                (exp (-FR_TR3_S * t) *
                                 (exp (-FR_B1_S * t) *
                                  (exp (-FR_B2_S * t) *
                                   ((1 − exp (-FR_TL1_HR * t)) *
                                    (exp (-FR_TL2_S * t) *
                                     (exp (-FR_B4_S * t) *
                                      (1 − exp (-FR_TR5_F * t))))))))) +
                               (exp (-FR_TR1_S * t) *
                                (exp (-FR_TR2_S * t) *
                                 (exp (-FR_TR3_S * t) *
                                  (exp (-FR_B1_S * t) *
                                   (exp (-FR_B2_S * t) *
                                    ((1 − exp (-FR_TL1_HR * t)) *
                                     (exp (-FR_TL2_S * t) *
                                      (exp (-FR_B4_S * t) *
                                       (1 − exp (-FR_TR5_PF * t))))))))) +
                                (exp (-FR_TR1_S * t) *
                                 (exp (-FR_TR2_S * t) *
                                  (exp (-FR_TR3_S * t) *
                                   (exp (-FR_B1_S * t) *
                                    (exp (-FR_B2_S * t) *
                                     ((1 − exp (-FR_TL1_HR * t)) *
                                      (exp (-FR_TL2_S * t) *
                                       (1 − exp (-FR_B4_F * t)))))))) +
                                 (exp (-FR_TR1_S * t) *
                                  (exp (-FR_TR2_S * t) *
                                   (exp (-FR_TR3_S * t) *
                                    (exp (-FR_B1_S * t) *
                                     (exp (-FR_B2_S * t) *
                                      ((1 − exp (-FR_TL1_HR * t)) *
                                       (1 − exp (-FR_TL2_F * t))))))) +
                                  (exp (-FR_TR1_S * t) *
                                   (exp (-FR_TR2_S * t) *
                                    (exp (-FR_TR3_S * t) *
                                     (exp (-FR_B1_S * t) *
                                      (exp (-FR_B2_S * t) *
                                       ((1 − exp (-FR_TL1_HR * t)) *
                                        (1 − exp (-FR_TL2_HR * t))))))) +
                                   (exp (-FR_TR1_S * t) *
                                    (exp (-FR_TR2_S * t) *
                                     (exp (-FR_TR3_S * t) *
                                      (exp (-FR_B1_S * t) *
                                       (exp (-FR_B2_S * t) *
                                        ((1 − exp (-FR_TL1_HR * t)) *
                                         (1 − exp (-FR_TL2_CR * t))))))) +
                                    (exp (-FR_TR1_S * t) *
                                     (exp (-FR_TR2_S * t) *
                                      (exp (-FR_TR3_S * t) *
                                       (exp (-FR_B1_S * t) *
                                        (exp (-FR_B2_S * t) *
                                         ((1 − exp (-FR_TL1_HR * t)) *
                                          (1 − exp (-FR_TL2_FTL * t))))))) +
                                     (exp (-FR_TR1_S * t) *
                                      (exp (-FR_TR2_S * t) *
                                       (exp (-FR_TR3_S * t) *
                                        (exp (-FR_B1_S * t) *
                                         (exp (-FR_B2_S * t) *
                                          ((1 − exp (-FR_TL1_CR * t)) *
                                           (exp (-FR_TL2_S * t) *
                                            (exp (-FR_B4_S * t) *
                                             (1 − exp (-FR_TR5_F * t))))))))) +
                                      (exp (-FR_TR1_S * t) *
                                       (exp (-FR_TR2_S * t) *
                                        (exp (-FR_TR3_S * t) *
                                         (exp (-FR_B1_S * t) *
                                          (exp (-FR_B2_S * t) *
                                           ((1 − exp (-FR_TL1_CR * t)) *
                                            (exp (-FR_TL2_S * t) *
                                             (exp (-FR_B4_S * t) *
                                              (1 − exp (-FR_TR5_PF * t))))))))) +
                                       (exp (-FR_TR1_S * t) *
                                        (exp (-FR_TR2_S * t) *
                                         (exp (-FR_TR3_S * t) *
                                          (exp (-FR_B1_S * t) *
                                           (exp (-FR_B2_S * t) *
                                            ((1 − exp (-FR_TL1_CR * t)) *
                                             (exp (-FR_TL2_S * t) *
                                              (1 − exp (-FR_B4_F * t)))))))) +
                                        (exp (-FR_TR1_S * t) *
                                         (exp (-FR_TR2_S * t) *
                                          (exp (-FR_TR3_S * t) *
                                           (exp (-FR_B1_S * t) *
                                            (exp (-FR_B2_S * t) *
                                             ((1 − exp (-FR_TL1_CR * t)) *
                                              (1 − exp (-FR_TL2_F * t))))))) +
                                         (exp (-FR_TR1_S * t) *
                                          (exp (-FR_TR2_S * t) *
                                           (exp (-FR_TR3_S * t) *
                                            (exp (-FR_B1_S * t) *
                                             (exp (-FR_B2_S * t) *
                                              ((1 − exp (-FR_TL1_CR * t)) *
                                               (1 − exp (-FR_TL2_HR * t))))))) +
                                          (exp (-FR_TR1_S * t) *
                                           (exp (-FR_TR2_S * t) *
                                            (exp (-FR_TR3_S * t) *
                                             (exp (-FR_B1_S * t) *
                                              (exp (-FR_B2_S * t) *
                                               ((1 − exp (-FR_TL1_CR * t)) *
                                                (1 − exp (-FR_TL2_CR * t))))))) +
                                           (exp (-FR_TR1_S * t) *
                                            (exp (-FR_TR2_S * t) *
                                             (exp (-FR_TR3_S * t) *
                                              (exp (-FR_B1_S * t) *
                                               (exp (-FR_B2_S * t) *
                                                ((1 − exp (-FR_TL1_CR * t)) *
                                                 (1 − exp (-FR_TL2_FTL * t))))))) +
                                            (exp (-FR_TR1_S * t) *
                                             (exp (-FR_TR2_S * t) *
                                              (exp (-FR_TR3_S * t) *
                                               (exp (-FR_B1_S * t) *
                                                (exp (-FR_B2_S * t) *
                                                 ((1 − exp (-FR_TL1_FTL * t)) *
                                                  (exp (-FR_TL2_S * t) *
                                                   (exp (-FR_B4_S * t) *
                                                    (1 − exp (-FR_TR5_F * t))))))))) +
                                             (exp (-FR_TR1_S * t) *
                                              (exp (-FR_TR2_S * t) *
                                               (exp (-FR_TR3_S * t) *
                                                (exp (-FR_B1_S * t) *
                                                 (exp (-FR_B2_S * t) *
                                                  ((1 − exp (-FR_TL1_FTL * t)) *
                                                   (exp (-FR_TL2_S * t) *
                                                    (exp (-FR_B4_S * t) *
                                                     (1 −
                                                      exp (-FR_TR5_PF * t))))))))) +
                                              (exp (-FR_TR1_S * t) *
                                               (exp (-FR_TR2_S * t) *
                                                (exp (-FR_TR3_S * t) *
                                                 (exp (-FR_B1_S * t) *
                                                  (exp (-FR_B2_S * t) *
                                                   ((1 −
                                                     exp (-FR_TL1_FTL * t)) *
                                                    (exp (-FR_TL2_S * t) *
                                                     (1 − exp (-FR_B4_F * t)))))))) +
                                               (exp (-FR_TR1_S * t) *
                                                (exp (-FR_TR2_S * t) *
                                                 (exp (-FR_TR3_S * t) *
                                                  (exp (-FR_B1_S * t) *
                                                   (exp (-FR_B2_S * t) *
                                                    ((1 −
                                                      exp (-FR_TL1_FTL * t)) *
                                                     (1 − exp (-FR_TL2_F * t))))))) +
                                                (exp (-FR_TR1_S * t) *
                                                 (exp (-FR_TR2_S * t) *
                                                  (exp (-FR_TR3_S * t) *
                                                   (exp (-FR_B1_S * t) *
                                                    (exp (-FR_B2_S * t) *
                                                     ((1 −
                                                       exp (-FR_TL1_FTL * t)) *
                                                      (1 −
                                                       exp (-FR_TL2_HR * t))))))) +
                                                 (exp (-FR_TR1_S * t) *
                                                  (exp (-FR_TR2_S * t) *
                                                   (exp (-FR_TR3_S * t) *
                                                    (exp (-FR_B1_S * t) *
                                                     (exp (-FR_B2_S * t) *
                                                      ((1 −
                                                        exp (-FR_TL1_FTL * t)) *
                                                       (1 −
                                                        exp (-FR_TL2_CR * t))))))) +
                                                  (exp (-FR_TR1_S * t) *
                                                   (exp (-FR_TR2_S * t) *
                                                    (exp (-FR_TR3_S * t) *
                                                     (exp (-FR_B1_S * t) *
                                                      (exp (-FR_B2_S * t) *
                                                       ((1 −
                                                         exp
                                                           (-FR_TL1_FTL * t)) *
                                                        (1 −
                                                         exp
                                                           (-FR_TL2_FTL * t))))))) +
                                                   (exp (-FR_TR1_S * t) *
                                                    (exp (-FR_TR2_S * t) *
                                                     (exp (-FR_TR3_S * t) *
                                                      (exp (-FR_B1_S * t) *
                                                       ((1 −
                                                         exp (-FR_B2_F * t)) *
                                                        (exp (-FR_TL1_S * t) *
                                                         (exp (-FR_B3_S * t) *
                                                          (1 −
                                                           exp
                                                             (-FR_TR4_F * t)))))))) +
                                                    (exp (-FR_TR1_S * t) *
                                                     (exp (-FR_TR2_S * t) *
                                                      (exp (-FR_TR3_S * t) *
                                                       (exp (-FR_B1_S * t) *
                                                        ((1 −
                                                          exp (-FR_B2_F * t)) *
                                                         (exp (-FR_TL1_S * t) *
                                                          (exp (-FR_B3_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_TR4_PF * t)))))))) +
                                                     (exp (-FR_TR1_S * t) *
                                                      (exp (-FR_TR2_S * t) *
                                                       (exp (-FR_TR3_S * t) *
                                                        (exp (-FR_B1_S * t) *
                                                         ((1 −
                                                           exp (-FR_B2_F * t)) *
                                                          (exp
                                                             (-FR_TL1_S * t) *
                                                           (1 −
                                                            exp
                                                              (-FR_B3_F * t))))))) +
                                                      (exp (-FR_TR1_S * t) *
                                                       (exp (-FR_TR2_S * t) *
                                                        (exp (-FR_TR3_S * t) *
                                                         (exp (-FR_B1_S * t) *
                                                          ((1 −
                                                            exp
                                                              (-FR_B2_F * t)) *
                                                           (1 −
                                                            exp
                                                              (-FR_TL1_F * t)))))) +
                                                       (exp (-FR_TR1_S * t) *
                                                        (exp (-FR_TR2_S * t) *
                                                         (exp (-FR_TR3_S * t) *
                                                          (exp (-FR_B1_S * t) *
                                                           ((1 −
                                                             exp
                                                               (-FR_B2_F * t)) *
                                                            (1 −
                                                             exp
                                                               (-FR_TL1_HR *
                                                                t)))))) +
                                                        (exp (-FR_TR1_S * t) *
                                                         (exp (-FR_TR2_S * t) *
                                                          (exp
                                                             (-FR_TR3_S * t) *
                                                           (exp
                                                              (-FR_B1_S * t) *
                                                            ((1 −
                                                              exp
                                                                (-FR_B2_F * t)) *
                                                             (1 −
                                                              exp
                                                                (-FR_TL1_CR *
                                                                 t)))))) +
                                                         (exp (-FR_TR1_S * t) *
                                                          (exp
                                                             (-FR_TR2_S * t) *
                                                           (exp
                                                              (-FR_TR3_S * t) *
                                                            (exp
                                                               (-FR_B1_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B2_F *
                                                                  t)) *
                                                              (1 −
                                                               exp
                                                                 (-FR_TL1_FTL *
                                                                  t)))))) +
                                                          (exp
                                                             (-FR_TR1_S * t) *
                                                           (exp
                                                              (-FR_TR2_S * t) *
                                                            (exp
                                                               (-FR_TR3_S * t) *
                                                             ((1 −
                                                               exp
                                                                 (-FR_B1_F *
                                                                  t)) *
                                                              (exp
                                                                 (-FR_B2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TL2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_B4_S *
                                                                    t) *
                                                                 (1 −
                                                                  exp
                                                                    (-FR_TR5_F *
                                                                     t)))))))) +
                                                           (exp
                                                              (-FR_TR1_S * t) *
                                                            (exp
                                                               (-FR_TR2_S * t) *
                                                             (exp
                                                                (-FR_TR3_S *
                                                                 t) *
                                                              ((1 −
                                                                exp
                                                                  (-FR_B1_F *
                                                                   t)) *
                                                               (exp
                                                                  (-FR_B2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TL2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_B4_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TR5_PF *
                                                                      t)))))))) +
                                                            (exp
                                                               (-FR_TR1_S * t) *
                                                             (exp
                                                                (-FR_TR2_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR3_S *
                                                                  t) *
                                                               ((1 −
                                                                 exp
                                                                   (-FR_B1_F *
                                                                    t)) *
                                                                (exp
                                                                   (-FR_B2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TL2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_B4_F *
                                                                      t))))))) +
                                                             (exp
                                                                (-FR_TR1_S *
                                                                 t) *
                                                              (exp
                                                                 (-FR_TR2_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR3_S *
                                                                   t) *
                                                                ((1 −
                                                                  exp
                                                                    (-FR_B1_F *
                                                                     t)) *
                                                                 (exp
                                                                    (-FR_B2_S *
                                                                     t) *
                                                                  (1 −
                                                                   exp
                                                                     (-FR_TL2_F *
                                                                      t)))))) +
                                                              (exp
                                                                 (-FR_TR1_S *
                                                                  t) *
                                                               (exp
                                                                  (-FR_TR2_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR3_S *
                                                                    t) *
                                                                 ((1 −
                                                                   exp
                                                                     (-FR_B1_F *
                                                                      t)) *
                                                                  (exp
                                                                     (-FR_B2_S *
                                                                      t) *
                                                                   (1 −
                                                                    exp
                                                                      (-FR_TL2_HR *
                                                                       t)))))) +
                                                               (exp
                                                                  (-FR_TR1_S *
                                                                   t) *
                                                                (exp
                                                                   (-FR_TR2_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR3_S *
                                                                     t) *
                                                                  ((1 −
                                                                    exp
                                                                      (-FR_B1_F *
                                                                       t)) *
                                                                   (exp
                                                                      (-FR_B2_S *
                                                                       t) *
                                                                    (1 −
                                                                     exp
                                                                       (-FR_TL2_CR *
                                                                        t)))))) +
                                                                (exp
                                                                   (-FR_TR1_S *
                                                                    t) *
                                                                 (exp
                                                                    (-FR_TR2_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR3_S *
                                                                      t) *
                                                                   ((1 −
                                                                     exp
                                                                       (-FR_B1_F *
                                                                        t)) *
                                                                    (exp
                                                                       (-FR_B2_S *
                                                                        t) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_TL2_FTL *
                                                                         t)))))) +
                                                                 (exp
                                                                    (-FR_TR1_S *
                                                                     t) *
                                                                  (exp
                                                                     (-FR_TR2_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR3_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_B1_F *
                                                                         t)) *
                                                                     (1 −
                                                                      exp
                                                                        (-FR_B2_F *
                                                                         t))))) +
                                                                  (exp
                                                                     (-FR_TR1_S *
                                                                      t) *
                                                                   (exp
                                                                      (-FR_TR2_S *
                                                                       t) *
                                                                    ((1 −
                                                                      exp
                                                                        (-FR_TR3_F *
                                                                         t)) *
                                                                     (exp
                                                                        (-FR_B1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TL1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_B3_S *
                                                                           t) *
                                                                        (1 −
                                                                         exp
                                                                           (-FR_TR4_F *
                                                                            t))))))) +
                                                                   (exp
                                                                      (-FR_TR1_S *
                                                                       t) *
                                                                    (exp
                                                                       (-FR_TR2_S *
                                                                        t) *
                                                                     ((1 −
                                                                       exp
                                                                         (-FR_TR3_F *
                                                                          t)) *
                                                                      (exp
                                                                         (-FR_B1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TL1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_B3_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TR4_PF *
                                                                             t))))))) +
                                                                    (exp
                                                                       (-FR_TR1_S *
                                                                        t) *
                                                                     (exp
                                                                        (-FR_TR2_S *
                                                                         t) *
                                                                      ((1 −
                                                                        exp
                                                                          (-FR_TR3_F *
                                                                           t)) *
                                                                       (exp
                                                                          (-FR_B1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TL1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_B3_F *
                                                                             t)))))) +
                                                                     (exp
                                                                        (-FR_TR1_S *
                                                                         t) *
                                                                      (exp
                                                                         (-FR_TR2_S *
                                                                          t) *
                                                                       ((1 −
                                                                         exp
                                                                           (-FR_TR3_F *
                                                                            t)) *
                                                                        (exp
                                                                           (-FR_B1_S *
                                                                            t) *
                                                                         (1 −
                                                                          exp
                                                                            (-FR_TL1_F *
                                                                             t))))) +
                                                                      (exp
                                                                         (-FR_TR1_S *
                                                                          t) *
                                                                       (exp
                                                                          (-FR_TR2_S *
                                                                           t) *
                                                                        ((1 −
                                                                          exp
                                                                            (-FR_TR3_F *
                                                                             t)) *
                                                                         (exp
                                                                            (-FR_B1_S *
                                                                             t) *
                                                                          (1 −
                                                                           exp
                                                                             (-FR_TL1_HR *
                                                                              t))))) +
                                                                       (exp
                                                                          (-FR_TR1_S *
                                                                           t) *
                                                                        (exp
                                                                           (-FR_TR2_S *
                                                                            t) *
                                                                         ((1 −
                                                                           exp
                                                                             (-FR_TR3_F *
                                                                              t)) *
                                                                          (exp
                                                                             (-FR_B1_S *
                                                                              t) *
                                                                           (1 −
                                                                            exp
                                                                              (-FR_TL1_CR *
                                                                               t))))) +
                                                                        (exp
                                                                           (-FR_TR1_S *
                                                                            t) *
                                                                         (exp
                                                                            (-FR_TR2_S *
                                                                             t) *
                                                                          ((1 −
                                                                            exp
                                                                              (-FR_TR3_F *
                                                                               t)) *
                                                                           (exp
                                                                              (-FR_B1_S *
                                                                               t) *
                                                                            (1 −
                                                                             exp
                                                                               (-FR_TL1_FTL *
                                                                                t))))) +
                                                                         (exp
                                                                            (-FR_TR1_S *
                                                                             t) *
                                                                          (exp
                                                                             (-FR_TR2_S *
                                                                              t) *
                                                                           ((1 −
                                                                             exp
                                                                               (-FR_TR3_PF *
                                                                                t)) *
                                                                            (exp
                                                                               (-FR_B1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TL1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_B3_S *
                                                                                  t) *
                                                                               exp
                                                                                 (-FR_TR4_S *
                                                                                  t)))))) +
                                                                          (exp
                                                                             (-FR_TR1_S *
                                                                              t) *
                                                                           (exp
                                                                              (-FR_TR2_S *
                                                                               t) *
                                                                            ((1 −
                                                                              exp
                                                                                (-FR_TR3_PF *
                                                                                 t)) *
                                                                             (exp
                                                                                (-FR_B1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TL1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_B3_S *
                                                                                   t) *
                                                                                (1 −
                                                                                 exp
                                                                                   (-FR_TR4_F *
                                                                                    t))))))) +
                                                                           (exp
                                                                              (-FR_TR1_S *
                                                                               t) *
                                                                            (exp
                                                                               (-FR_TR2_S *
                                                                                t) *
                                                                             ((1 −
                                                                               exp
                                                                                 (-FR_TR3_PF *
                                                                                  t)) *
                                                                              (exp
                                                                                 (-FR_B1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TL1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_B3_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TR4_PF *
                                                                                     t))))))) +
                                                                            (exp
                                                                               (-FR_TR1_S *
                                                                                t) *
                                                                             (exp
                                                                                (-FR_TR2_S *
                                                                                 t) *
                                                                              ((1 −
                                                                                exp
                                                                                  (-FR_TR3_PF *
                                                                                   t)) *
                                                                               (exp
                                                                                  (-FR_B1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TL1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_B3_F *
                                                                                     t)))))) +
                                                                             (exp
                                                                                (-FR_TR1_S *
                                                                                 t) *
                                                                              (exp
                                                                                 (-FR_TR2_S *
                                                                                  t) *
                                                                               ((1 −
                                                                                 exp
                                                                                   (-FR_TR3_PF *
                                                                                    t)) *
                                                                                (exp
                                                                                   (-FR_B1_S *
                                                                                    t) *
                                                                                 (1 −
                                                                                  exp
                                                                                    (-FR_TL1_F *
                                                                                     t))))) +
                                                                              (exp
                                                                                 (-FR_TR1_S *
                                                                                  t) *
                                                                               (exp
                                                                                  (-FR_TR2_S *
                                                                                   t) *
                                                                                ((1 −
                                                                                  exp
                                                                                    (-FR_TR3_PF *
                                                                                     t)) *
                                                                                 (exp
                                                                                    (-FR_B1_S *
                                                                                     t) *
                                                                                  (1 −
                                                                                   exp
                                                                                     (-FR_TL1_HR *
                                                                                      t))))) +
                                                                               (exp
                                                                                  (-FR_TR1_S *
                                                                                   t) *
                                                                                (exp
                                                                                   (-FR_TR2_S *
                                                                                    t) *
                                                                                 ((1 −
                                                                                   exp
                                                                                     (-FR_TR3_PF *
                                                                                      t)) *
                                                                                  (exp
                                                                                     (-FR_B1_S *
                                                                                      t) *
                                                                                   (1 −
                                                                                    exp
                                                                                      (-FR_TL1_CR *
                                                                                       t))))) +
                                                                                (exp
                                                                                   (-FR_TR1_S *
                                                                                    t) *
                                                                                 (exp
                                                                                    (-FR_TR2_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR3_PF *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_B1_S *
                                                                                       t) *
                                                                                    (1 −
                                                                                     exp
                                                                                       (-FR_TL1_FTL *
                                                                                        t))))) +
                                                                                 (exp
                                                                                    (-FR_TR1_S *
                                                                                     t) *
                                                                                  ((1 −
                                                                                    exp
                                                                                      (-FR_TR2_F *
                                                                                       t)) *
                                                                                   (exp
                                                                                      (-FR_TR3_S *
                                                                                       t) *
                                                                                    (exp
                                                                                       (-FR_B2_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_TL2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B4_S *
                                                                                          t) *
                                                                                       exp
                                                                                         (-FR_TR5_S *
                                                                                          t)))))) +
                                                                                  (exp
                                                                                     (-FR_TR1_S *
                                                                                      t) *
                                                                                   ((1 −
                                                                                     exp
                                                                                       (-FR_TR2_F *
                                                                                        t)) *
                                                                                    (exp
                                                                                       (-FR_TR3_S *
                                                                                        t) *
                                                                                     (exp
                                                                                        (-FR_B2_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_TL2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B4_S *
                                                                                           t) *
                                                                                        (1 −
                                                                                         exp
                                                                                           (-FR_TR5_F *
                                                                                            t))))))) +
                                                                                   (exp
                                                                                      (-FR_TR1_S *
                                                                                       t) *
                                                                                    ((1 −
                                                                                      exp
                                                                                        (-FR_TR2_F *
                                                                                         t)) *
                                                                                     (exp
                                                                                        (-FR_TR3_S *
                                                                                         t) *
                                                                                      (exp
                                                                                         (-FR_B2_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_TL2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B4_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TR5_PF *
                                                                                             t))))))) +
                                                                                    (exp
                                                                                       (-FR_TR1_S *
                                                                                        t) *
                                                                                     ((1 −
                                                                                       exp
                                                                                         (-FR_TR2_F *
                                                                                          t)) *
                                                                                      (exp
                                                                                         (-FR_TR3_S *
                                                                                          t) *
                                                                                       (exp
                                                                                          (-FR_B2_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_TL2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_B4_F *
                                                                                             t)))))) +
                                                                                     (exp
                                                                                        (-FR_TR1_S *
                                                                                         t) *
                                                                                      ((1 −
                                                                                        exp
                                                                                          (-FR_TR2_F *
                                                                                           t)) *
                                                                                       (exp
                                                                                          (-FR_TR3_S *
                                                                                           t) *
                                                                                        (exp
                                                                                           (-FR_B2_S *
                                                                                            t) *
                                                                                         (1 −
                                                                                          exp
                                                                                            (-FR_TL2_F *
                                                                                             t))))) +
                                                                                      (exp
                                                                                         (-FR_TR1_S *
                                                                                          t) *
                                                                                       ((1 −
                                                                                         exp
                                                                                           (-FR_TR2_F *
                                                                                            t)) *
                                                                                        (exp
                                                                                           (-FR_TR3_S *
                                                                                            t) *
                                                                                         (exp
                                                                                            (-FR_B2_S *
                                                                                             t) *
                                                                                          (1 −
                                                                                           exp
                                                                                             (-FR_TL2_HR *
                                                                                              t))))) +
                                                                                       (exp
                                                                                          (-FR_TR1_S *
                                                                                           t) *
                                                                                        ((1 −
                                                                                          exp
                                                                                            (-FR_TR2_F *
                                                                                             t)) *
                                                                                         (exp
                                                                                            (-FR_TR3_S *
                                                                                             t) *
                                                                                          (exp
                                                                                             (-FR_B2_S *
                                                                                              t) *
                                                                                           (1 −
                                                                                            exp
                                                                                              (-FR_TL2_CR *
                                                                                               t))))) +
                                                                                        (exp
                                                                                           (-FR_TR1_S *
                                                                                            t) *
                                                                                         ((1 −
                                                                                           exp
                                                                                             (-FR_TR2_F *
                                                                                              t)) *
                                                                                          (exp
                                                                                             (-FR_TR3_S *
                                                                                              t) *
                                                                                           (exp
                                                                                              (-FR_B2_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TL2_FTL *
                                                                                                t))))) +
                                                                                         (exp
                                                                                            (-FR_TR1_S *
                                                                                             t) *
                                                                                          ((1 −
                                                                                            exp
                                                                                              (-FR_TR2_F *
                                                                                               t)) *
                                                                                           (exp
                                                                                              (-FR_TR3_S *
                                                                                               t) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_B2_F *
                                                                                                t)))) +
                                                                                          (exp
                                                                                             (-FR_TR1_S *
                                                                                              t) *
                                                                                           ((1 −
                                                                                             exp
                                                                                               (-FR_TR2_F *
                                                                                                t)) *
                                                                                            (1 −
                                                                                             exp
                                                                                               (-FR_TR3_F *
                                                                                                t))) +
                                                                                           (exp
                                                                                              (-FR_TR1_S *
                                                                                               t) *
                                                                                            ((1 −
                                                                                              exp
                                                                                                (-FR_TR2_PF *
                                                                                                 t)) *
                                                                                             (exp
                                                                                                (-FR_TR3_S *
                                                                                                 t) *
                                                                                              (exp
                                                                                                 (-FR_B2_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_TL2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B4_S *
                                                                                                    t) *
                                                                                                 exp
                                                                                                   (-FR_TR5_S *
                                                                                                    t)))))) +
                                                                                            (exp
                                                                                               (-FR_TR1_S *
                                                                                                t) *
                                                                                             ((1 −
                                                                                               exp
                                                                                                 (-FR_TR2_PF *
                                                                                                  t)) *
                                                                                              (exp
                                                                                                 (-FR_TR3_S *
                                                                                                  t) *
                                                                                               (exp
                                                                                                  (-FR_B2_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_TL2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B4_S *
                                                                                                     t) *
                                                                                                  (1 −
                                                                                                   exp
                                                                                                     (-FR_TR5_F *
                                                                                                      t))))))) +
                                                                                             (exp
                                                                                                (-FR_TR1_S *
                                                                                                 t) *
                                                                                              ((1 −
                                                                                                exp
                                                                                                  (-FR_TR2_PF *
                                                                                                   t)) *
                                                                                               (exp
                                                                                                  (-FR_TR3_S *
                                                                                                   t) *
                                                                                                (exp
                                                                                                   (-FR_B2_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_TL2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B4_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TR5_PF *
                                                                                                       t))))))) +
                                                                                              (exp
                                                                                                 (-FR_TR1_S *
                                                                                                  t) *
                                                                                               ((1 −
                                                                                                 exp
                                                                                                   (-FR_TR2_PF *
                                                                                                    t)) *
                                                                                                (exp
                                                                                                   (-FR_TR3_S *
                                                                                                    t) *
                                                                                                 (exp
                                                                                                    (-FR_B2_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_TL2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_B4_F *
                                                                                                       t)))))) +
                                                                                               (exp
                                                                                                  (-FR_TR1_S *
                                                                                                   t) *
                                                                                                ((1 −
                                                                                                  exp
                                                                                                    (-FR_TR2_PF *
                                                                                                     t)) *
                                                                                                 (exp
                                                                                                    (-FR_TR3_S *
                                                                                                     t) *
                                                                                                  (exp
                                                                                                     (-FR_B2_S *
                                                                                                      t) *
                                                                                                   (1 −
                                                                                                    exp
                                                                                                      (-FR_TL2_F *
                                                                                                       t))))) +
                                                                                                (exp
                                                                                                   (-FR_TR1_S *
                                                                                                    t) *
                                                                                                 ((1 −
                                                                                                   exp
                                                                                                     (-FR_TR2_PF *
                                                                                                      t)) *
                                                                                                  (exp
                                                                                                     (-FR_TR3_S *
                                                                                                      t) *
                                                                                                   (exp
                                                                                                      (-FR_B2_S *
                                                                                                       t) *
                                                                                                    (1 −
                                                                                                     exp
                                                                                                       (-FR_TL2_HR *
                                                                                                        t))))) +
                                                                                                 (exp
                                                                                                    (-FR_TR1_S *
                                                                                                     t) *
                                                                                                  ((1 −
                                                                                                    exp
                                                                                                      (-FR_TR2_PF *
                                                                                                       t)) *
                                                                                                   (exp
                                                                                                      (-FR_TR3_S *
                                                                                                       t) *
                                                                                                    (exp
                                                                                                       (-FR_B2_S *
                                                                                                        t) *
                                                                                                     (1 −
                                                                                                      exp
                                                                                                        (-FR_TL2_CR *
                                                                                                         t))))) +
                                                                                                  (exp
                                                                                                     (-FR_TR1_S *
                                                                                                      t) *
                                                                                                   ((1 −
                                                                                                     exp
                                                                                                       (-FR_TR2_PF *
                                                                                                        t)) *
                                                                                                    (exp
                                                                                                       (-FR_TR3_S *
                                                                                                        t) *
                                                                                                     (exp
                                                                                                        (-FR_B2_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TL2_FTL *
                                                                                                          t))))) +
                                                                                                   (exp
                                                                                                      (-FR_TR1_S *
                                                                                                       t) *
                                                                                                    ((1 −
                                                                                                      exp
                                                                                                        (-FR_TR2_PF *
                                                                                                         t)) *
                                                                                                     (exp
                                                                                                        (-FR_TR3_S *
                                                                                                         t) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_B2_F *
                                                                                                          t)))) +
                                                                                                    (exp
                                                                                                       (-FR_TR1_S *
                                                                                                        t) *
                                                                                                     ((1 −
                                                                                                       exp
                                                                                                         (-FR_TR2_PF *
                                                                                                          t)) *
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR3_F *
                                                                                                          t))) +
                                                                                                     (exp
                                                                                                        (-FR_TR1_S *
                                                                                                         t) *
                                                                                                      ((1 −
                                                                                                        exp
                                                                                                          (-FR_TR2_PF *
                                                                                                           t)) *
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR3_PF *
                                                                                                           t))) +
                                                                                                      (1 −
                                                                                                       exp
                                                                                                         (-FR_TR1_F *
                                                                                                          t) +
                                                                                                       (1 −
                                                                                                        exp
                                                                                                          (-FR_TR1_PF *
                                                                                                           t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) * 2690) / 2690)``;

(*------------------------------------------------------------------------------------------------------*)
		(*--------------------------------------------------------*)
			(*--------------------------------------*)
				(*------------------------*)
