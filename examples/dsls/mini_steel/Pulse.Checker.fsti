module Pulse.Checker
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

val check_tot (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })

val check (f:RT.fstar_top_env)
          (g:env)
          (t:term)
          (pre:pure_term)
          (pre_typing: tot_typing f g pre Tm_VProp)
  : T.Tac (c:pure_comp { C_ST? c ==> comp_pre c == pre } &
           src_typing f g t c)
