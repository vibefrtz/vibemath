/-
DSS/Guard.lean

A build-time guard on the axiom base.

`axiom_audit.txt` records the axiom closure of every result, but it is a
committed expected output: a reader has to run the audit and diff it, and
nothing stops a later edit from quietly making an unconditional result depend
on an axiom.  The `#assert_axioms` command below turns that discipline into a
build invariant.  If any of the assertions in this file ever becomes false,
the project does not compile.

The guard is not decorative: narrowing an allowed set to exclude an axiom that
is genuinely used makes `lake build` fail with `AXIOM GUARD FAILED`.
-/
import DSS.Digits
import DSS.Sidon
import DSS.CarryFree
import DSS.CarryFreeTwo
import DSS.BoseChowla
import DSS.Singleton
import DSS.Squares
import DSS.PrimeCount
import DSS.FWeight
import DSS.Examples
import DSS.P2

namespace DSS

open Lean Elab Command in
/-- `#assert_axioms foo ⊆ a, b, c` fails at elaboration time unless the axiom
closure of `foo` is contained in `{a, b, c}`. -/
elab "#assert_axioms " id:ident "⊆" names:ident,* : command => do
  let cst ← liftCoreM <| realizeGlobalConstNoOverload id
  let allowed : Array Name ← names.getElems.mapM fun n =>
    liftCoreM <| realizeGlobalConstNoOverload n
  let used ← liftCoreM <| collectAxioms cst
  let bad := used.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AXIOM GUARD FAILED: {cst} depends on {bad.toList}, \
                which is not contained in the permitted set {allowed.toList}"

/-! ### Unconditional: these must depend on nothing but Lean's own axioms.

If any of these ever acquires `DSS.mmr` or `DSS.hhbr`, the build breaks here.
In particular **the entire squares half of the paper — Theorem 1.10, its
corollaries, and Bose–Chowla itself — is certified axiom-free.** -/

-- the digit-sum toolkit
#assert_axioms DSS.sb_add_pow_mul       ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_pow_sub           ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_sum_pow           ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_pow_mul           ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_modEq             ⊆ propext, Classical.choice, Quot.sound

-- Sidon sets and the carry-free construction
#assert_axioms DSS.isSidon_insert_zero  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sqCoeff_le_two       ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sq_sum_pow           ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sum_sqCoeff          ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sum_pow_injective    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.aT_injective         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_aT_sq             ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_aT_sq_sub_one     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_two_aT_sub_one    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_shifted_sq        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.card_pairsLT         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.aT_sq_eq_sum_expSet  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.card_expSet          ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_shifted_sq_two    ⊆ propext, Classical.choice, Quot.sound

-- Bose–Chowla, proved (not assumed)
#assert_axioms DSS.pair_eq_of_sum_prod  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.bose_chowla          ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.exists_sidon_of_card ⊆ propext, Classical.choice, Quot.sound

-- the singleton family and the unconditional infinitude
#assert_axioms DSS.coprime_shifted      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sb_singleton         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.infinite_coprime_sq_prime_digit_sum
  ⊆ propext, Classical.choice, Quot.sound

-- Theorem 1.10 and Corollary 1.11
#assert_axioms DSS.two_pow_le_choose    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sq_digit_sum_count   ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sq_digit_sum_count_two ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sq_prime_digit_sum_count_two
  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sq_prime_digit_sum_count_three
  ⊆ propext, Classical.choice, Quot.sound

-- weights that see the length, and the paper's examples
#assert_axioms DSS.Fw_eq_split          ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.Zb_eq_Fw             ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.zeroWeight_coprime₁  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.zeroWeight_dg        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.zeroWeight_mu        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.zeroWeight_sigSq     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.zeroWeight_shell_centre ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.base3_odd_shell_forcing ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.exWeight3_dg         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.exWeight4_dg         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.exWeight4_mu         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sbWeight_two_dg      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sbWeight_two_mu      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.eval_sbWeight        ⊆ propext, Classical.choice, Quot.sound

-- the inherited elementary core (Lemma 2.2 of the predecessor)
#assert_axioms DSS.Weight.sigSq_pos     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.Weight.coprime_w_one_dg ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.Weight.dg_dvd_eval_sub ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.piCong_of_dg_eq_one  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sum_countEq          ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.countEq_le_piCong    ⊆ propext, Classical.choice, Quot.sound

-- the real-analytic helpers of the P₂ argument
#assert_axioms DSS.log_le_eight_rpow    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.exists_rpow_threshold ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.gaussian_lower       ⊆ propext, Classical.choice, Quot.sound

/-! ### Conditional: these may use `DSS.mmr` and `DSS.hhbr`, and nothing else.

If any of these ever acquires a further axiom, the build breaks here. -/

#assert_axioms DSS.p2_count
  ⊆ propext, Classical.choice, Quot.sound, DSS.mmr, DSS.hhbr
#assert_axioms DSS.p2_count_S
  ⊆ propext, Classical.choice, Quot.sound, DSS.mmr, DSS.hhbr
#assert_axioms DSS.p2_count_binary
  ⊆ propext, Classical.choice, Quot.sound, DSS.mmr, DSS.hhbr

end DSS
