/-
AxiomAudit.lean — run `lake env lean AxiomAudit.lean` to print, for each result,
the complete list of axioms its proof depends on; compare with
`axiom_audit.txt`.

Expected: Lean's three built-in axioms (`propext`, `Classical.choice`,
`Quot.sound`) for everything in the squares half and the elementary theory —
including Theorem 1.8 and Bose–Chowla — and additionally `DSS.mmr` and
`DSS.hhbr`, and nothing else, for the `P₂` results.
-/
import DSS

open DSS

/- ## The squares half (Theorem 1.8 and companions): NO axioms. -/

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

-- **Theorem 1.8** and **Corollary 1.9**
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

/- ## The spectral gap in every base and the Fourier assembly of
Theorem 1.1: NO axioms. -/

#print axioms DSS.finset_gcd_bezout
#print axioms DSS.dg_combination
#print axioms DSS.dist01_dg_le
#print axioms DSS.norm_digitalFactor_le_pair
#print axioms DSS.two_digit_gap
#print axioms DSS.integral_ee_mul_int
#print axioms DSS.sqPhi_inversion
#print axioms DSS.window_split
#print axioms DSS.arc_integral_eq
#print axioms DSS.integral_ee_gaussian
#print axioms DSS.gaussian_tail_bound
#print axioms DSS.norm_etaSq_le_one
#print axioms DSS.small_x_bound
#print axioms DSS.squareLLT_of_arcs

/- ## The `P₂` theorem (Corollary 4.6): `DSS.mmr` and `DSS.hhbr`, nothing else. -/

#print axioms DSS.p2_count
#print axioms DSS.p2_count_S
#print axioms DSS.p2_count_binary

/- ## The revision: the square lattice density, the spectral gap, the
binary audit, the κ_m factors, the shift identity, the blocking lemmas —
NO axioms. -/

#print axioms DSS.rhoSq_dg_one
#print axioms DSS.sum_rhoSq
#print axioms DSS.sum_rhoSq_coprime
#print axioms DSS.coprime_eval_sq_iff
#print axioms DSS.sum_sqCountEq
#print axioms DSS.gcd_bezout
#print axioms DSS.lattice_abs_one
#print axioms DSS.one_sub_cos_ge
#print axioms DSS.two_digit_gap_two
#print axioms DSS.binary_domination
#print axioms DSS.nboth_prime
#print axioms DSS.nboth_prime_pow
#print axioms DSS.kappaM_prime
#print axioms DSS.kappaM_prime_pow
#print axioms DSS.local_average
#print axioms DSS.nboth_mul
#print axioms DSS.kappaM_product
#print axioms DSS.kappaM_average
#print axioms DSS.eval_sq_base_mul
#print axioms DSS.recipSum_split
#print axioms DSS.eval_pow_sub
#print axioms DSS.eval_add_pow_mul
#print axioms DSS.eval_linear_blocking
#print axioms DSS.eval_linear_blocking_const
#print axioms DSS.infinite_prime_linear_blocking

/- ## The finite Fourier identity (37), the `h_g`-scaling reduction of
Theorem 2.1, and Poisson summation (Lemma 4.3): NO axioms. -/

#print axioms DSS.sum_ee_mul_eq
#print axioms DSS.rhoSq_fourier
#print axioms DSS.Weight.eval_smulW
#print axioms DSS.Weight.mu_smulW
#print axioms DSS.Weight.sigSq_smulW
#print axioms DSS.squareLLT_general
#print axioms DSS.tsum_gauss_shift
#print axioms DSS.abs_tsum_gauss_shift_sub
#print axioms DSS.tsum_gauss_shift_le
#print axioms DSS.gaussian_progression

/- ## The square `P₂` implication: `hhbr` only (the square local theorem
enters as the hypothesis `SquareLLT`, never as an axiom). -/

#print axioms DSS.square_p2_of_llt
#print axioms DSS.square_p2_binary

/- ## Theorem 1.2 as an implication from `SquareLLT` and `SquareTail`:
NO axioms at all. -/

#print axioms DSS.gaussKer_class
#print axioms DSS.gaussKer_tail
#print axioms DSS.sqCountCong_window
#print axioms DSS.sqCountCong_crt
#print axioms DSS.class_bound
#print axioms DSS.modulus_bound
#print axioms DSS.sum_inv_moduli_le
#print axioms DSS.square_output_level
