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
import DSS.RhoSquare
import DSS.SquareLLT
import DSS.SquareGeneral
import DSS.RhoFourier
import DSS.GaussSum
import DSS.OutputLevel
import DSS.SquareP2
import DSS.SpectralGap
import DSS.SquareAssembly
import DSS.KappaM
import DSS.Blocking
import DSS.BinaryAudit
import DSS.ShiftSquares

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
In particular **the entire squares half of the paper — Theorem 1.8, its
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

-- Theorem 1.8 and Corollary 1.9
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

-- the square lattice density and the restriction equivalence (§4, §8)
#assert_axioms DSS.rhoSq_dg_one         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.rhoSq_periodic       ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sum_rhoSq            ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sum_rhoSq_coprime    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.coprime_eval_sq_iff  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sum_sqCountEq        ⊆ propext, Classical.choice, Quot.sound

-- the two-digit spectral gap (Lemma 2.4), now in every base
#assert_axioms DSS.gcd_bezout           ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.lattice_abs_one      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.one_sub_cos_ge       ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.two_digit_gap_two    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.finset_gcd_bezout    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.dg_combination       ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.dist01_dg_le         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.norm_digitalFactor_le_pair ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.two_digit_gap        ⊆ propext, Classical.choice, Quot.sound

-- the Fourier assembly of Theorem 1.1 (§2.4): the implication
-- `SquareMinor → SquareMajor → SquareLLT` and its ingredients
#assert_axioms DSS.integral_ee_mul_int  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sqPhi_inversion      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.window_split         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.arc_integral_eq      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.integral_ee_gaussian ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.gaussian_tail_bound  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.norm_etaSq_le_one    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.small_x_bound        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.squareLLT_of_arcs    ⊆ propext, Classical.choice, Quot.sound

-- the binary-endpoint audit of Remark 2.3
#assert_axioms DSS.binary_bracket_eval  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.binary_bracket_gt    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.binary_sum_eval      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.binary_domination    ⊆ propext, Classical.choice, Quot.sound

-- the κ_m local factors (Theorem 5.12): primes, prime powers, and — new —
-- the Chinese-remainder multiplicativity, the product formula (60) for an
-- arbitrary modulus, and the mean formula (61)
#assert_axioms DSS.nboth_prime          ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.nboth_prime_pow      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.kappaM_prime         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.kappaM_prime_pow     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.local_average        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.nboth_mul            ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.kappaM_product       ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.kappaM_average       ⊆ propext, Classical.choice, Quot.sound

-- the finite Fourier identity (37)
#assert_axioms DSS.sum_ee_mul_eq        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.rhoSq_fourier        ⊆ propext, Classical.choice, Quot.sound

-- the `h_g`-scaling reduction of Theorem 2.1 to Theorem 1.1
#assert_axioms DSS.Weight.eval_smulW    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.Weight.mu_smulW      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.Weight.sigSq_smulW   ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.squareLLT_general    ⊆ propext, Classical.choice, Quot.sound

-- Poisson summation and Lemma 4.3
#assert_axioms DSS.tsum_gauss_shift     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.abs_tsum_gauss_shift_sub ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.tsum_gauss_shift_le  ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.gaussian_progression ⊆ propext, Classical.choice, Quot.sound

-- digit-shift invariance and the exact reciprocal identity of §8
#assert_axioms DSS.eval_sq_base_mul     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.recipSum_split       ⊆ propext, Classical.choice, Quot.sound

-- the complement lemma and linear blocking (§7.2)
#assert_axioms DSS.ofDigits_comp        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.eval_pow_sub         ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.eval_add_pow_mul     ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.eval_linear_blocking ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.eval_linear_blocking_const ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.infinite_prime_linear_blocking
  ⊆ propext, Classical.choice, Quot.sound

/-! ### Conditional: these may use `DSS.mmr` and `DSS.hhbr`, and nothing else.

If any of these ever acquires a further axiom, the build breaks here. -/

#assert_axioms DSS.p2_count
  ⊆ propext, Classical.choice, Quot.sound, DSS.mmr, DSS.hhbr
#assert_axioms DSS.p2_count_S
  ⊆ propext, Classical.choice, Quot.sound, DSS.mmr, DSS.hhbr
#assert_axioms DSS.p2_count_binary
  ⊆ propext, Classical.choice, Quot.sound, DSS.mmr, DSS.hhbr

/-! ### The square `P₂` implication: `hhbr` only — **not** `mmr`.

Corollary 1.3 (`P₂` part) is machine-checked as an implication from the
*statement* of Theorem 1.1 (`SquareLLT`, a definition, never an axiom) and
the short-interval axiom.  The guard certifies that no other axiom — in
particular not `mmr` — enters. -/

#assert_axioms DSS.square_p2_of_llt
  ⊆ propext, Classical.choice, Quot.sound, DSS.hhbr
#assert_axioms DSS.square_p2_binary
  ⊆ propext, Classical.choice, Quot.sound, DSS.hhbr

/-! ### Theorem 1.2 as an implication: **no axioms at all**.

The output-distribution theorem is proved from the two clauses of
Theorem 1.1, both of which are *definitions* (`SquareLLT`, `SquareTail`).
Unlike the `P₂` corollary, this one quotes nothing from the literature, so
its axiom closure is Lean's three built-ins and nothing else. -/

#assert_axioms DSS.gaussKer_class       ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.gaussKer_tail        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sqCountCong_window   ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sqCountCong_crt      ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.class_bound          ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.modulus_bound        ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.sum_inv_moduli_le    ⊆ propext, Classical.choice, Quot.sound
#assert_axioms DSS.square_output_level  ⊆ propext, Classical.choice, Quot.sound

end DSS
