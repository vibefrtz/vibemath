/-
AxiomAudit.lean — run `lake env lean AxiomAudit.lean` to print, for each result,
the complete list of axioms its proof depends on; compare with
`axiom_audit.txt`.

Expected: Lean's three built-in axioms (`propext`, `Classical.choice`,
`Quot.sound`) for everything in the squares half and the elementary theory —
including Theorem 1.10 and Bose–Chowla — and additionally `DSS.mmr` and
`DSS.hhbr`, and nothing else, for the `P₂` results.
-/
import DSS

open DSS

/- ## The squares half (Theorem 1.10 and companions): NO axioms. -/

-- the digit-sum toolkit of §7
#print axioms DSS.sb_add_pow_mul
#print axioms DSS.sb_pow_sub
#print axioms DSS.sb_sum_pow
#print axioms DSS.sb_pow_mul
#print axioms DSS.sb_modEq

-- Sidon sets and the carry-free computation (Lemmas 7.1–7.2)
#print axioms DSS.isSidon_insert_zero
#print axioms DSS.sqCoeff_le_two
#print axioms DSS.sum_pow_injective
#print axioms DSS.aT_injective
#print axioms DSS.sb_aT_sq
#print axioms DSS.sb_aT_sq_sub_one
#print axioms DSS.sb_shifted_sq
#print axioms DSS.card_pairsLT
#print axioms DSS.aT_sq_eq_sum_expSet
#print axioms DSS.sb_shifted_sq_two

-- Bose–Chowla, PROVED inside Lean
#print axioms DSS.pair_eq_of_sum_prod
#print axioms DSS.bose_chowla
#print axioms DSS.exists_sidon_of_card

-- the singleton family and Dirichlet (Remark 7.3)
#print axioms DSS.sb_singleton
#print axioms DSS.infinite_coprime_sq_prime_digit_sum

-- **Theorem 1.10** and **Corollary 1.11**
#print axioms DSS.sq_digit_sum_count
#print axioms DSS.sq_digit_sum_count_two
#print axioms DSS.sq_prime_digit_sum_count_two
#print axioms DSS.sq_prime_digit_sum_count_three

/- ## Weights that see the length (§5): NO axioms. -/

#print axioms DSS.Fw_eq_split
#print axioms DSS.Zb_eq_Fw
#print axioms DSS.zeroWeight_coprime₁
#print axioms DSS.zeroWeight_dg
#print axioms DSS.zeroWeight_mu
#print axioms DSS.zeroWeight_sigSq
#print axioms DSS.zeroWeight_shell_centre
#print axioms DSS.base3_odd_shell_forcing
#print axioms DSS.exWeight3_coprime₁
#print axioms DSS.exWeight3_dg
#print axioms DSS.exWeight4_coprime₁
#print axioms DSS.exWeight4_dg
#print axioms DSS.exWeight4_mu
#print axioms DSS.sbWeight_two_dg
#print axioms DSS.sbWeight_two_mu

/- ## The inherited elementary core: NO axioms. -/

#print axioms DSS.Weight.sigSq_pos
#print axioms DSS.Weight.coprime_w_one_dg
#print axioms DSS.Weight.dg_dvd_eval_sub
#print axioms DSS.piCong_of_dg_eq_one
#print axioms DSS.sum_countEq
#print axioms DSS.countEq_le_piCong

/- ## The `P₂` theorem (Corollary 1.3): `DSS.mmr` and `DSS.hhbr`, nothing else. -/

#print axioms DSS.p2_count
#print axioms DSS.p2_count_S
#print axioms DSS.p2_count_binary
