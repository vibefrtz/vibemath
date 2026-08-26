/-
DigSq/Guard.lean

A build-time guard on the axiom base.

`axiom_audit.txt` records the axiom closure of every result, but it is a
committed expected output: a reader has to run the audit and diff it, and
nothing stops a later edit from quietly making an unconditional result depend on
`DigSq.mmr`.  The `#assert_axioms` command below turns that discipline into a
build invariant.  If any of the assertions in this file ever becomes false, the
project does not compile.

The guard is not decorative: narrowing an allowed set to exclude an axiom that
is genuinely used makes `lake build` fail with `AXIOM GUARD FAILED`.
-/
import DigSq.Main
import DigSq.Sharp
import DigSq.Happy

namespace DigSq

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

If any of these ever acquires `DigSq.mmr`, the build breaks here. -/

#assert_axioms DigSq.Weight.eval_add_mul   ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.Weight.eval_ofDigits  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.Weight.dg_dvd_sub_one ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.Weight.dg_dvd_sub     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.Weight.dg_pos         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.Weight.dg_dvd_eval_sub ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.Weight.sigSq_pos      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.Weight.coprime_w_one_dg ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.sum_countEq           ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.countEq_le_piCong     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.piCong_of_dg_eq_one   ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.sqrt_lt_rpow_three_quarters ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.mu_wS                 ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.dg_wS                 ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.eval_wS               ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.dg_powWeight_ten_even ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.dg_digitCount         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.infinite_of_exists_prime_eval_eq ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.three_dvd_of_S_eq_three ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.eq_pow_ten_of_S_eq_one  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.S_ne_one_of_prime       ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.S_ne_three_of_prime     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.S_lt_self               ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.reaches_one_or_cycle    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DigSq.exists_iterate_not_prime ⊆ propext, Classical.choice, Quot.sound

/-! ### Conditional: these may use `DigSq.mmr`, and nothing else.

If any of these ever acquires a second axiom, the build breaks here. -/

#assert_axioms DigSq.exists_prime_eval_eq_of_dg_one ⊆ propext, Classical.choice, Quot.sound, DigSq.mmr
#assert_axioms DigSq.infinite_prime_eval_prime_of_dg_one ⊆ propext, Classical.choice, Quot.sound, DigSq.mmr
#assert_axioms DigSq.infinite_prime_powDigitSum_prime ⊆ propext, Classical.choice, Quot.sound, DigSq.mmr
#assert_axioms DigSq.infinite_prime_digitOccurrences_prime ⊆ propext, Classical.choice, Quot.sound, DigSq.mmr
#assert_axioms DigSq.exists_prime_S_eq ⊆ propext, Classical.choice, Quot.sound, DigSq.mmr
#assert_axioms DigSq.A052034_infinite ⊆ propext, Classical.choice, Quot.sound, DigSq.mmr
#assert_axioms DigSq.A052034_infinite_inlined ⊆ propext, Classical.choice, Quot.sound, DigSq.mmr
#assert_axioms DigSq.A052034_exists_gt ⊆ propext, Classical.choice, Quot.sound, DigSq.mmr

end DigSq
