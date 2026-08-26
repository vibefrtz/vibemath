/-
AxiomAudit.lean — run `lake env lean AxiomAudit.lean` to print, for each result,
the complete list of axioms its proof depends on.

Expected: Lean's three built-in axioms (`propext`, `Classical.choice`,
`Quot.sound`) for the unconditional results, and additionally `DigSq.mmr` — and
nothing else — for the results deduced from the local limit theorem.
-/
import DigSq

open DigSq

/- ## Unconditional (Phase 1): these must NOT mention `DigSq.mmr`. -/

-- Lemma 2.2 and the theory of `d_g`
#print axioms DigSq.Weight.sigSq_pos
#print axioms DigSq.Weight.coprime_w_one_dg
#print axioms DigSq.Weight.dg_dvd_sub_one
#print axioms DigSq.Weight.dg_pos
#print axioms DigSq.Weight.dg_dvd_eval_sub
#print axioms DigSq.Weight.dg_dvd_sub
#print axioms DigSq.Weight.eval_add_mul
#print axioms DigSq.Weight.eval_ofDigits

-- the examples and their constants (§6.1)
#print axioms DigSq.powWeight_coprime₁
#print axioms DigSq.powWeight_mu_pos
#print axioms DigSq.eval_powWeight
#print axioms DigSq.dg_powWeight_ten_even
#print axioms DigSq.mu_wS
#print axioms DigSq.dg_wS
#print axioms DigSq.eval_wS
#print axioms DigSq.digitCount_coprime₁
#print axioms DigSq.dg_digitCount
#print axioms DigSq.digitCount_mu_pos
#print axioms DigSq.eval_digitCount

-- the analytic core, and the counting identity that removes the need for PNT
#print axioms DigSq.sqrt_lt_rpow_three_quarters
#print axioms DigSq.piCong_of_dg_eq_one
#print axioms DigSq.sum_countEq
#print axioms DigSq.countEq_le_piCong

-- the infinitude bridge: distinct targets give distinct primes
#print axioms DigSq.infinite_of_exists_prime_eval_eq

-- §6.2: "sufficiently large" cannot be dropped
#print axioms DigSq.three_dvd_of_S_eq_three
#print axioms DigSq.eq_pow_ten_of_S_eq_one
#print axioms DigSq.S_ne_one_of_prime
#print axioms DigSq.S_ne_three_of_prime

-- §6.3: the happy-number theorem
#print axioms DigSq.S_lt_self
#print axioms DigSq.S_mem_happyCycle
#print axioms DigSq.reaches_one_or_cycle
#print axioms DigSq.exists_iterate_not_prime

/- ## Conditional (Phase 2): these depend on `DigSq.mmr`, and on nothing else. -/

#print axioms DigSq.exists_prime_eval_eq_of_dg_one
#print axioms DigSq.infinite_prime_eval_prime_of_dg_one
#print axioms DigSq.infinite_prime_powDigitSum_prime
#print axioms DigSq.infinite_prime_digitOccurrences_prime
#print axioms DigSq.exists_prime_S_eq
#print axioms DigSq.A052034_infinite
#print axioms DigSq.A052034_infinite_inlined
#print axioms DigSq.A052034_exists_gt
