/-
EKRev/PalOmega.lean

**Lemma 3.3(iii)**: `∑_{n∈𝒯_λ}(Ω(n)-ω(n)) ≪ #𝒯_λ`.

Following the paper's proof: the identity
`Ω-ω = ∑_{m≥2} #{ℓ : ℓ^m ∣ ·}` (via `sum_excess_eq`), then a case split on
the prime-power modulus `ℓ^m`:
* `ℓ ∈ ℰ_b`: Theorem 3.2 (`bsh_thm7`), summed geometrically;
* `ℓ ∉ ℰ_b`, `ℓ^m ≤ b^{ξλ}`: the level of distribution
  (`pal_col_package` at `A = 1`), main terms `∑ ℓ^{-m} ≤ 2`;
* `ℓ ∉ ℰ_b`, `ℓ^m > b^{ξλ}`, `m = 2`: Theorem 3.2 and Mertens' theorem on
  the window `(b^{ξλ/2}, b^λ]`, contributing `log(2/ξ)+O(1)`;
* `ℓ ∉ ℰ_b`, `ℓ^m > b^{ξλ}`, `m ≥ 3`: Theorem 3.2 with
  `(√ℓ)^{-m} ≤ ℓ^{-1} b^{-ξλ/6}` and the crude Mertens bound
  `∑_{ℓ≤b^λ} 1/ℓ ≤ L + O(1)`, giving `≪ λ² L b^{-ξλ/6} → 0`.

Fully proved from the axioms of `Cited.lean`.
-/
import Mathlib.Tactic
import EKRev.PalHyp

namespace EKRev

open Finset Filter Real Topology

variable {b : ℕ}

set_option maxHeartbeats 1600000 in
theorem palOmegaHyp (hb : 2 ≤ b) : OmegaHyp (fun lam => palSet b lam) := by
  obtain ⟨ξ', hx0, hxh, hpkg⟩ := pal_col_package hb
  obtain ⟨C1, hC10, hpkg1⟩ := hpkg 1 one_pos
  obtain ⟨Cb, hCb0, hbsh⟩ := bsh_thm7 b hb
  obtain ⟨Cm, hCm0, hmert⟩ := mertens_regular.bound
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0R : (0:ℝ) < (b:ℝ) := by linarith
  set W : ℝ := Real.log (2/ξ') + 1 + 2*Cm with hWdef
  have hW0 : 0 ≤ W := by
    have h1 : (1:ℝ) ≤ 2/ξ' := by
      rw [le_div_iff₀ hx0]
      linarith
    have h2 := Real.log_nonneg h1
    rw [hWdef]
    linarith
  refine ⟨Cb*(2*((Eb b).card:ℝ)) + (2 + 2*(b:ℝ)*C1) + (Cb*W + Cb), ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ Cb*(2*((Eb b).card:ℝ)) :=
      mul_nonneg hCb0 (by positivity)
    have h2 : (0:ℝ) ≤ 2*(b:ℝ)*C1 :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hC10
    have h3 : (0:ℝ) ≤ Cb*W := mul_nonneg hCb0 hW0
    linarith
  · have hev4 : ∀ᶠ lam : ℕ in atTop,
        (b:ℝ) * (lam:ℝ) * (LL b lam + Cm) / ytr b ξ' 6 lam ≤ 1 := by
      have h0 := tendsto_linLL_div_ytr hb hx0 (K := 6) (by omega) (b:ℝ) Cm
        (by linarith) hCm0
      have h1 := h0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
      exact h1.mono (fun lam h => le_of_lt h)
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_ytr_atTop hb hx0 (show 1 ≤ 2 by omega)).eventually_ge_atTop 4,
      hev4,
      (tendsto_LL_atTop hb).eventually_ge_atTop 0] with lam hlam2 hytr2 hlin hLL0
    have hlam1 : 1 ≤ lam := by omega
    have hlamR : (1:ℝ) ≤ (lam:ℝ) := by exact_mod_cast hlam1
    have hlamR0 : (0:ℝ) < (lam:ℝ) := by linarith
    have hlamne : (lam:ℝ) ≠ 0 := ne_of_gt hlamR0
    obtain ⟨Bnd, hB0, hBrem, hBsum⟩ := hpkg1 lam hlam1
    have hcT0 : (0:ℝ) ≤ ((palSet b lam).card : ℝ) := by positivity
    set M : ℕ := b * lam with hMdef
    have hM2 : 2 ≤ M := by
      rw [hMdef]
      have := Nat.mul_le_mul hb hlam1
      omega
    set Ylam : ℕ := ⌊(b:ℝ) ^ (ξ' * (lam:ℝ))⌋₊ with hYlam
    have hpos : ∀ n ∈ palSet b lam, 1 ≤ n := by
      intro n hn
      have h := (mem_palSet_iff.mp hn).1
      have h2 : 1 ≤ b ^ (lam - 1) := Nat.one_le_pow _ _ (by omega)
      omega
    have hltb : ∀ n ∈ palSet b lam, n < b ^ lam :=
      fun n hn => (mem_palSet_iff.mp hn).2.1
    have hid : ∑ n ∈ palSet b lam, ((bigOmega n : ℝ) - (smallOmega n : ℝ))
        = ∑ m ∈ Finset.Icc 2 M, ∑ ℓ ∈ Pamb b lam,
            (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ) :=
      sum_excess_eq hb lam (palSet b lam) (fun n => n) hpos hltb
    -- BSh count bound, in the `(√ℓ)^{-m}` form
    have hbshcnt : ∀ ℓ : ℕ, ℓ.Prime → ∀ m : ℕ, 1 ≤ m →
        (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
          ≤ Cb * ((palSet b lam).card : ℝ) * ((Real.sqrt (ℓ:ℝ))⁻¹) ^ m := by
      intro ℓ hp m hm
      have h1 := hbsh lam hlam1 (ℓ ^ m) (Nat.one_le_pow _ _ hp.pos)
      have h2 : Real.sqrt (((ℓ ^ m : ℕ) : ℝ)) = (Real.sqrt (ℓ:ℝ)) ^ m := by
        push_cast
        exact sqrt_pow_comm (by positivity) m
      calc (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
          ≤ Cb * ((palSet b lam).card : ℝ) / Real.sqrt (((ℓ ^ m : ℕ)) : ℝ) := h1
        _ = Cb * ((palSet b lam).card : ℝ) * ((Real.sqrt (ℓ:ℝ))⁻¹) ^ m := by
            rw [h2, div_eq_mul_inv, inv_pow]
    -- ── Part A: the primes of ℰ_b ──
    have hboundA : ∑ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∈ Eb b),
          (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
        ≤ Cb * (2*((Eb b).card:ℝ)) * ((palSet b lam).card : ℝ) := by
      rw [Finset.sum_comm]
      have hper : ∀ ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∈ Eb b),
          ∑ m ∈ Finset.Icc 2 M,
            (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
            ≤ Cb * ((palSet b lam).card : ℝ) * 2 := by
        intro ℓ hℓ
        rw [Finset.mem_filter] at hℓ
        have hp : ℓ.Prime := (mem_Pamb.mp hℓ.1).2
        calc ∑ m ∈ Finset.Icc 2 M,
              (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
            ≤ ∑ m ∈ Finset.Icc 2 M,
                Cb * ((palSet b lam).card : ℝ) * ((Real.sqrt (ℓ:ℝ))⁻¹) ^ m := by
              refine Finset.sum_le_sum fun m hm => ?_
              rw [Finset.mem_Icc] at hm
              exact hbshcnt ℓ hp m (by omega)
          _ = Cb * ((palSet b lam).card : ℝ)
                * ∑ m ∈ Finset.Icc 2 M, ((Real.sqrt (ℓ:ℝ))⁻¹) ^ m := by
              rw [Finset.mul_sum]
          _ ≤ Cb * ((palSet b lam).card : ℝ) * 2 := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCb0 hcT0)
              exact sum_Icc_inv_sqrt_pow_le hp.two_le M
      calc ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∈ Eb b),
            ∑ m ∈ Finset.Icc 2 M,
              (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
          ≤ ∑ _ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∈ Eb b),
              Cb * ((palSet b lam).card : ℝ) * 2 :=
            Finset.sum_le_sum hper
        _ = (((Pamb b lam).filter (fun ℓ => ℓ ∈ Eb b)).card : ℝ)
              * (Cb * ((palSet b lam).card : ℝ) * 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((Eb b).card : ℝ) * (Cb * ((palSet b lam).card : ℝ) * 2) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact_mod_cast Finset.card_le_card
                (fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2)
            · have := mul_nonneg hCb0 hcT0
              linarith
        _ = Cb * (2*((Eb b).card:ℝ)) * ((palSet b lam).card : ℝ) := by ring
    -- ── Part B: small prime powers, ℓ ∉ ℰ_b ──
    have hboundB : ∑ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
          (fun ℓ => ℓ ^ m ≤ Ylam),
          (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
        ≤ (2 + 2*(b:ℝ)*C1) * ((palSet b lam).card : ℝ) := by
      have hptwB : ∀ m ∈ Finset.Icc 2 M,
          ∀ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
            (fun ℓ => ℓ ^ m ≤ Ylam),
          (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
            ≤ ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m + 2 * Bnd (ℓ ^ m) := by
        intro m hm ℓ hℓ
        rw [Finset.mem_Icc] at hm
        rw [Finset.mem_filter, Finset.mem_filter] at hℓ
        obtain ⟨⟨hPam, hnotE⟩, hsm⟩ := hℓ
        have hp : ℓ.Prime := (mem_Pamb.mp hPam).2
        have hcop : Nat.Coprime (ℓ ^ m) (b ^ 3 - b) :=
          Nat.Coprime.pow_left _ (prime_not_Eb_coprime hb hp hnotE)
        have hle : ((ℓ ^ m : ℕ) : ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ)) := by
          calc ((ℓ ^ m : ℕ) : ℝ) ≤ (Ylam : ℝ) := by exact_mod_cast hsm
            _ ≤ (b:ℝ) ^ (ξ' * (lam:ℝ)) := Nat.floor_le (Real.rpow_nonneg hb0R.le _)
        have hrem := hBrem (ℓ ^ m) (Nat.one_le_pow _ _ hp.pos) hcop hle
        have hcnt : (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
            = ((palSet b lam).card : ℝ) / ((ℓ ^ m : ℕ) : ℝ)
              + rem (palSet b lam) (ℓ ^ m) := by
          unfold rem
          ring
        rw [hcnt]
        have hdiv : ((palSet b lam).card : ℝ) / ((ℓ ^ m : ℕ) : ℝ)
            = ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m := by
          push_cast
          rw [div_eq_mul_inv, inv_pow]
        rw [hdiv]
        have h2 := le_abs_self (rem (palSet b lam) (ℓ ^ m))
        linarith
      have hmainB : ∑ m ∈ Finset.Icc 2 M,
          ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
            (fun ℓ => ℓ ^ m ≤ Ylam),
            ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
          ≤ 2 * ((palSet b lam).card : ℝ) := by
        have hstep1 : ∀ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ℓ ^ m ≤ Ylam),
              ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
            ≤ ∑ ℓ ∈ Pamb b lam, ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m := by
          intro m _
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
          · intro ℓ _ _
            exact mul_nonneg hcT0 (by positivity)
        calc ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam),
                ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
            ≤ ∑ m ∈ Finset.Icc 2 M,
                ∑ ℓ ∈ Pamb b lam, ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m :=
              Finset.sum_le_sum hstep1
          _ = ∑ ℓ ∈ Pamb b lam,
                ∑ m ∈ Finset.Icc 2 M, ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m :=
              Finset.sum_comm
          _ ≤ ∑ ℓ ∈ Pamb b lam,
                ((palSet b lam).card : ℝ) * (2 * ((ℓ:ℝ)⁻¹) ^ 2) := by
              refine Finset.sum_le_sum fun ℓ hℓ => ?_
              have hp : ℓ.Prime := (mem_Pamb.mp hℓ).2
              have h2ℓ : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hp.two_le
              rw [← Finset.mul_sum]
              refine mul_le_mul_of_nonneg_left ?_ hcT0
              refine sum_Icc_geom_le (by positivity) ?_ M
              have hinv := inv_le_inv_of_le' (by norm_num : (0:ℝ) < 2) h2ℓ
              rw [show ((2:ℝ))⁻¹ = 1/2 by norm_num] at hinv
              exact hinv
          _ = 2 * ((palSet b lam).card : ℝ) * ∑ ℓ ∈ Pamb b lam, ((ℓ:ℝ)⁻¹) ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ℓ _ => ?_
              ring
          _ ≤ 2 * ((palSet b lam).card : ℝ) * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              have hsub2 : Pamb b lam ⊆ Finset.Ioc 1 (b ^ lam) := by
                intro ℓ hℓ
                have h := mem_Pamb.mp hℓ
                rw [Finset.mem_Ioc]
                have := h.2.two_le
                omega
              have hIoc := sum_Ioc_inv_sq_le (u := 1) (N := b ^ lam) le_rfl
                (Nat.one_le_pow _ _ (by omega))
              have hN0 : (0:ℝ) ≤ ((b ^ lam : ℕ):ℝ)⁻¹ := by positivity
              calc ∑ ℓ ∈ Pamb b lam, ((ℓ:ℝ)⁻¹) ^ 2
                  ≤ ∑ n ∈ Finset.Ioc 1 (b ^ lam), ((n:ℝ)⁻¹) ^ 2 :=
                    Finset.sum_le_sum_of_subset_of_nonneg hsub2
                      (fun n _ _ => by positivity)
                _ ≤ ((1:ℕ):ℝ)⁻¹ - ((b ^ lam : ℕ):ℝ)⁻¹ := hIoc
                _ ≤ 1 := by
                    have e : ((1:ℕ):ℝ)⁻¹ = 1 := by norm_num
                    rw [e]
                    linarith
          _ = 2 * ((palSet b lam).card : ℝ) := by ring
      have hbndB : ∑ m ∈ Finset.Icc 2 M,
          ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
            (fun ℓ => ℓ ^ m ≤ Ylam), 2 * Bnd (ℓ ^ m)
          ≤ 2*(b:ℝ)*C1 * ((palSet b lam).card : ℝ) := by
        have hperm : ∀ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ℓ ^ m ≤ Ylam), Bnd (ℓ ^ m)
            ≤ C1 * ((palSet b lam).card : ℝ) / (lam:ℝ) := by
          intro m hm
          rw [Finset.mem_Icc] at hm
          have hinj : ∀ x ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ℓ ^ m ≤ Ylam),
              ∀ y ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ℓ ^ m ≤ Ylam), x ^ m = y ^ m → x = y :=
            fun x _ y _ h => Nat.pow_left_injective (by omega : m ≠ 0) h
          rw [← Finset.sum_image hinj]
          have hsubm : (((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ℓ ^ m ≤ Ylam)).image (· ^ m)
              ⊆ (Finset.Icc 1 (b ^ lam)).filter
                (fun q => Nat.Coprime q (b ^ 3 - b)
                  ∧ (q : ℝ) ≤ (b : ℝ) ^ (ξ' * (lam : ℝ))) := by
            intro d hd
            simp only [Finset.mem_image] at hd
            obtain ⟨ℓ, hℓ, rfl⟩ := hd
            rw [Finset.mem_filter, Finset.mem_filter] at hℓ
            obtain ⟨⟨hPam, hnotE⟩, hsm⟩ := hℓ
            have hp : ℓ.Prime := (mem_Pamb.mp hPam).2
            have hle : ((ℓ ^ m : ℕ) : ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ)) := by
              calc ((ℓ ^ m : ℕ) : ℝ) ≤ (Ylam : ℝ) := by exact_mod_cast hsm
                _ ≤ (b:ℝ) ^ (ξ' * (lam:ℝ)) :=
                  Nat.floor_le (Real.rpow_nonneg hb0R.le _)
            have hleN : ℓ ^ m ≤ b ^ lam := by
              have h2 : (b:ℝ) ^ (ξ' * (lam:ℝ)) ≤ ((b ^ lam : ℕ) : ℝ) := by
                push_cast
                calc (b:ℝ) ^ (ξ' * (lam:ℝ)) ≤ (b:ℝ) ^ ((lam:ℝ)) := by
                      rw [Real.rpow_le_rpow_left_iff hbR]
                      nlinarith [hxh, hlamR, hx0]
                  _ = (b:ℝ) ^ (lam:ℕ) := Real.rpow_natCast (b:ℝ) lam
              exact_mod_cast le_trans hle h2
            simp only [Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨Nat.one_le_pow _ _ hp.pos, hleN⟩,
              Nat.Coprime.pow_left _ (prime_not_Eb_coprime hb hp hnotE), hle⟩
          calc ∑ d ∈ (((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam)).image (· ^ m), Bnd d
              ≤ ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
                  (fun q => Nat.Coprime q (b ^ 3 - b)
                    ∧ (q : ℝ) ≤ (b : ℝ) ^ (ξ' * (lam : ℝ))), Bnd d :=
                Finset.sum_le_sum_of_subset_of_nonneg hsubm (fun d _ _ => hB0 d)
            _ ≤ C1 * ((palSet b lam).card : ℝ) / (lam : ℝ) ^ (1:ℝ) := hBsum
            _ = C1 * ((palSet b lam).card : ℝ) / (lam:ℝ) := by
                rw [Real.rpow_one]
        calc ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam), 2 * Bnd (ℓ ^ m)
            = ∑ m ∈ Finset.Icc 2 M,
                2 * ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                  (fun ℓ => ℓ ^ m ≤ Ylam), Bnd (ℓ ^ m) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [Finset.mul_sum]
          _ ≤ ∑ _m ∈ Finset.Icc 2 M,
                2 * (C1 * ((palSet b lam).card : ℝ) / (lam:ℝ)) := by
              refine Finset.sum_le_sum fun m hm => ?_
              have := hperm m hm
              linarith
          _ = ((Finset.Icc 2 M).card : ℝ)
                * (2 * (C1 * ((palSet b lam).card : ℝ) / (lam:ℝ))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((b:ℝ) * (lam:ℝ))
                * (2 * (C1 * ((palSet b lam).card : ℝ) / (lam:ℝ))) := by
              refine mul_le_mul_of_nonneg_right ?_ ?_
              · have hcard : (Finset.Icc 2 M).card ≤ M := by
                  rw [Nat.card_Icc]
                  omega
                calc ((Finset.Icc 2 M).card : ℝ) ≤ (M:ℝ) := by exact_mod_cast hcard
                  _ = (b:ℝ) * (lam:ℝ) := by rw [hMdef]; push_cast; ring
              · have h1 : (0:ℝ) ≤ C1 * ((palSet b lam).card : ℝ) / (lam:ℝ) :=
                  div_nonneg (mul_nonneg hC10 hcT0) hlamR0.le
                linarith
          _ = 2*(b:ℝ)*C1 * ((palSet b lam).card : ℝ) := by
              field_simp
              try ring
      calc ∑ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ℓ ^ m ≤ Ylam),
              (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
          ≤ ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam),
                (((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m + 2 * Bnd (ℓ ^ m)) :=
            Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (hptwB m hm))
        _ = (∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam),
                ((palSet b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m)
            + ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam), 2 * Bnd (ℓ ^ m) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [← Finset.sum_add_distrib]
        _ ≤ 2 * ((palSet b lam).card : ℝ)
              + 2*(b:ℝ)*C1 * ((palSet b lam).card : ℝ) := add_le_add hmainB hbndB
        _ = (2 + 2*(b:ℝ)*C1) * ((palSet b lam).card : ℝ) := by ring
    -- ── Part C: large prime powers, ℓ ∉ ℰ_b ──
    have hN3 : 3 ≤ b ^ lam := by
      calc 3 ≤ 2^2 := by norm_num
        _ ≤ b^2 := Nat.pow_le_pow_left hb 2
        _ ≤ b^lam := Nat.pow_le_pow_right (by omega) hlam2
    have hmN := hmert (b ^ lam) hN3
    rw [one_mul] at hmN
    have hLLN : Real.log (Real.log ((b ^ lam : ℕ):ℝ)) = LL b lam := by
      unfold LL
      push_cast
      rfl
    have hpRSle : primeRecipSum {p : ℕ | p.Prime} (b ^ lam) ≤ LL b lam + Cm := by
      have := (abs_le.mp hmN).2
      rw [hLLN] at this
      linarith
    have hboundC : ∑ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
          (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
          (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
        ≤ Cb * W * ((palSet b lam).card : ℝ) + Cb * ((palSet b lam).card : ℝ) := by
      rw [Icc_two_split M hM2, Finset.sum_insert (by simp)]
      have hy6 : (0:ℝ) < ytr b ξ' 6 lam := ytr_pos hb
      -- the m = 2 term
      have hC2 : ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
          (fun ℓ => ¬ ℓ ^ 2 ≤ Ylam),
          (((palSet b lam).filter fun n => ℓ ^ 2 ∣ n).card : ℝ)
          ≤ Cb * W * ((palSet b lam).card : ℝ) := by
        have hptw2 : ∀ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
            (fun ℓ => ¬ ℓ ^ 2 ≤ Ylam),
            (((palSet b lam).filter fun n => ℓ ^ 2 ∣ n).card : ℝ)
              ≤ Cb * ((palSet b lam).card : ℝ) * ((1:ℝ)/(ℓ:ℝ)) := by
          intro ℓ hℓ
          rw [Finset.mem_filter, Finset.mem_filter] at hℓ
          have hp : ℓ.Prime := (mem_Pamb.mp hℓ.1.1).2
          have hℓ0 : (0:ℝ) ≤ (ℓ:ℝ) := by positivity
          have h1 := hbshcnt ℓ hp 2 (by omega)
          have h2 : ((Real.sqrt (ℓ:ℝ))⁻¹) ^ 2 = (1:ℝ)/(ℓ:ℝ) := by
            rw [inv_pow, Real.sq_sqrt hℓ0, one_div]
          rwa [h2] at h1
        -- the Mertens window
        have hu3 : 3 ≤ ⌊ytr b ξ' 2 lam⌋₊ := by
          have h1 : ((3:ℕ):ℝ) ≤ ytr b ξ' 2 lam := by
            push_cast
            linarith [hytr2]
          exact Nat.le_floor h1
        have hytr2N : (⌊ytr b ξ' 2 lam⌋₊:ℝ) ≤ ytr b ξ' 2 lam :=
          Nat.floor_le (ytr_nonneg hb)
        have huN : ⌊ytr b ξ' 2 lam⌋₊ ≤ b ^ lam := by
          have h1 : (⌊ytr b ξ' 2 lam⌋₊ : ℝ) ≤ ((b ^ lam : ℕ) : ℝ) := by
            calc (⌊ytr b ξ' 2 lam⌋₊:ℝ) ≤ ytr b ξ' 2 lam := hytr2N
              _ ≤ (b:ℝ) ^ ((lam:ℝ)) := by
                  unfold ytr
                  rw [Real.rpow_le_rpow_left_iff hbR]
                  push_cast
                  nlinarith [hx0, hxh, hlamR]
              _ = ((b ^ lam : ℕ):ℝ) := by
                  push_cast
                  exact (Real.rpow_natCast (b:ℝ) lam)
          exact_mod_cast h1
        have hmemw : ∀ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
            (fun ℓ => ¬ ℓ ^ 2 ≤ Ylam),
            ℓ.Prime ∧ ⌊ytr b ξ' 2 lam⌋₊ < ℓ ∧ ℓ ≤ b ^ lam := by
          intro ℓ hℓ
          rw [Finset.mem_filter, Finset.mem_filter] at hℓ
          obtain ⟨⟨hPam, _⟩, hlg⟩ := hℓ
          have hmem := mem_Pamb.mp hPam
          have hp : ℓ.Prime := hmem.2
          refine ⟨hp, ?_, by omega⟩
          -- ℓ > ⌊ytr2⌋
          have h1 : Ylam < ℓ ^ 2 := by omega
          have h2 : (b:ℝ) ^ (ξ' * (lam:ℝ)) < ((ℓ ^ 2 : ℕ):ℝ) :=
            (Nat.floor_lt (Real.rpow_nonneg hb0R.le _)).mp h1
          have h3 : ytr b ξ' 2 lam < (ℓ:ℝ) := by
            by_contra hcon
            push_neg at hcon
            have h4 : (ℓ:ℝ)^2 ≤ (ytr b ξ' 2 lam)^2 :=
              pow_le_pow_left' (by positivity) hcon 2
            rw [ytr_pow_K hb (by omega : 1 ≤ 2) hx0] at h4
            have h5 : ((ℓ ^ 2 : ℕ):ℝ) = (ℓ:ℝ)^2 := by push_cast; rfl
            rw [h5] at h2
            linarith
          have h6 : (⌊ytr b ξ' 2 lam⌋₊:ℝ) < (ℓ:ℝ) := lt_of_le_of_lt hytr2N h3
          exact_mod_cast h6
        have hwin : ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
            (fun ℓ => ¬ ℓ ^ 2 ≤ Ylam), (1:ℝ)/(ℓ:ℝ) ≤ W := by
          have h1 := sum_primes_window_le huN hmemw
          have hmu := hmert (⌊ytr b ξ' 2 lam⌋₊) hu3
          rw [one_mul] at hmu
          have hlo := (abs_le.mp hmu).1
          -- log log ⌊ytr2⌋ ≥ log log (ytr2) − 1
          have hyge3 : (3:ℝ) ≤ ytr b ξ' 2 lam := by linarith [hytr2]
          have hfl := (loglog_floor_close hyge3).2
          have hlog2 := loglog_ytr hb hx0 (by omega : 1 ≤ 2) hlam1
          -- −log(ξ'/2) = log(2/ξ')
          have hloginv : Real.log (2/ξ') = - Real.log (ξ'/(2:ℕ)) := by
            rw [← Real.log_inv]
            congr 1
            rw [inv_div]
            push_cast
            rfl
          have hup := (abs_le.mp hmN).2
          rw [hLLN] at hup
          rw [hWdef, hloginv]
          -- assemble: Σ ≤ pRS(N) − pRS(u) ≤ (LL + Cm) − (loglog u − Cm)
          --        ≤ LL + Cm − (LL + log(ξ'/2) − 1) + Cm
          have h2 : primeRecipSum {p : ℕ | p.Prime} (⌊ytr b ξ' 2 lam⌋₊)
              ≥ LL b lam + Real.log (ξ'/(2:ℕ)) - 1 - Cm := by
            have h3 : Real.log (Real.log (ytr b ξ' 2 lam))
                ≤ Real.log (Real.log ((⌊ytr b ξ' 2 lam⌋₊:ℕ):ℝ)) + 1 := hfl
            rw [hlog2] at h3
            linarith
          linarith [h1, hpRSle]
        calc ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ¬ ℓ ^ 2 ≤ Ylam),
              (((palSet b lam).filter fun n => ℓ ^ 2 ∣ n).card : ℝ)
            ≤ ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ¬ ℓ ^ 2 ≤ Ylam),
                Cb * ((palSet b lam).card : ℝ) * ((1:ℝ)/(ℓ:ℝ)) :=
              Finset.sum_le_sum hptw2
          _ = Cb * ((palSet b lam).card : ℝ)
                * ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                  (fun ℓ => ¬ ℓ ^ 2 ≤ Ylam), (1:ℝ)/(ℓ:ℝ) := by
              rw [Finset.mul_sum]
          _ ≤ Cb * ((palSet b lam).card : ℝ) * W :=
              mul_le_mul_of_nonneg_left hwin (mul_nonneg hCb0 hcT0)
          _ = Cb * W * ((palSet b lam).card : ℝ) := by ring
      -- the m ≥ 3 terms
      have hC3 : ∑ m ∈ Finset.Icc 3 M,
          ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
            (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
            (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
          ≤ Cb * ((palSet b lam).card : ℝ) := by
        have hptw3 : ∀ m ∈ Finset.Icc 3 M,
            ∀ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
            (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
              ≤ Cb * ((palSet b lam).card : ℝ)
                * ((1:ℝ)/(ℓ:ℝ) * (ytr b ξ' 6 lam)⁻¹) := by
          intro m hm ℓ hℓ
          rw [Finset.mem_Icc] at hm
          rw [Finset.mem_filter, Finset.mem_filter] at hℓ
          obtain ⟨⟨hPam, _⟩, hlg⟩ := hℓ
          have hp : ℓ.Prime := (mem_Pamb.mp hPam).2
          have hℓ0 : (0:ℝ) < (ℓ:ℝ) := by exact_mod_cast hp.pos
          have hbig : (b:ℝ) ^ (ξ' * (lam:ℝ)) < (ℓ:ℝ) ^ m := by
            have h1 : Ylam < ℓ ^ m := by omega
            have h2 := (Nat.floor_lt (Real.rpow_nonneg hb0R.le _)).mp h1
            calc (b:ℝ)^(ξ'*(lam:ℝ)) < ((ℓ ^ m : ℕ):ℝ) := h2
              _ = (ℓ:ℝ)^m := by push_cast; rfl
          have hℓgt : ytr b ξ' m lam < (ℓ:ℝ) := by
            by_contra hcon
            push_neg at hcon
            have h3 : (ℓ:ℝ)^m ≤ (ytr b ξ' m lam)^m :=
              pow_le_pow_left' hℓ0.le hcon m
            rw [ytr_pow_K hb (by omega : 1 ≤ m) hx0] at h3
            linarith
          have hsq : ytr b ξ' 6 lam ≤ (Real.sqrt (ℓ:ℝ)) ^ (m - 2) := by
            have hs1 : (ytr b ξ' 6 lam)^2 ≤ ((Real.sqrt (ℓ:ℝ)) ^ (m-2))^2 := by
              have e1 : ((Real.sqrt (ℓ:ℝ)) ^ (m-2))^2 = (ℓ:ℝ) ^ (m-2) := by
                rw [← pow_mul, mul_comm (m-2) 2, pow_mul, Real.sq_sqrt hℓ0.le]
              have e2 : (ytr b ξ' 6 lam)^2 = (b:ℝ) ^ (ξ' * (lam:ℝ) / 3) := by
                unfold ytr
                rw [← Real.rpow_natCast ((b:ℝ) ^ (ξ' * (lam:ℝ) / ((6:ℕ):ℝ))) 2,
                  ← Real.rpow_mul hb0R.le]
                congr 1
                push_cast
                ring
              rw [e1, e2]
              have h4 : (ytr b ξ' m lam) ^ (m-2) ≤ (ℓ:ℝ) ^ (m-2) :=
                pow_le_pow_left' (ytr_nonneg hb) hℓgt.le _
              have h5 : (ytr b ξ' m lam) ^ (m-2)
                  = (b:ℝ) ^ (ξ' * (lam:ℝ) * (((m:ℝ) - 2) / (m:ℝ))) := by
                unfold ytr
                rw [← Real.rpow_natCast ((b:ℝ) ^ (ξ' * (lam:ℝ) / ((m:ℕ):ℝ))) (m-2),
                  ← Real.rpow_mul hb0R.le]
                congr 1
                have hc : ((m - 2 : ℕ):ℝ) = (m:ℝ) - 2 := by
                  have h2m : (2:ℕ) ≤ m := by omega
                  rw [Nat.cast_sub h2m]
                  norm_num
                have hm0 : ((m:ℕ):ℝ) ≠ 0 := by
                  have : (0:ℕ) < m := by omega
                  positivity
                rw [hc]
                field_simp
                try ring
              have h6 : (b:ℝ) ^ (ξ' * (lam:ℝ) / 3)
                  ≤ (b:ℝ) ^ (ξ' * (lam:ℝ) * (((m:ℝ) - 2) / (m:ℝ))) := by
                rw [Real.rpow_le_rpow_left_iff hbR]
                have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
                have hm0 : (0:ℝ) < (m:ℝ) := by linarith
                have hxil : (0:ℝ) ≤ ξ' * (lam:ℝ) :=
                  mul_nonneg hx0.le (by positivity)
                have hfrac : (1:ℝ)/3 ≤ ((m:ℝ) - 2) / (m:ℝ) := by
                  rw [div_le_div_iff₀ (by norm_num) hm0]
                  linarith
                calc ξ' * (lam:ℝ) / 3 = ξ' * (lam:ℝ) * ((1:ℝ)/3) := by ring
                  _ ≤ ξ' * (lam:ℝ) * (((m:ℝ) - 2) / (m:ℝ)) :=
                      mul_le_mul_of_nonneg_left hfrac hxil
              calc (b:ℝ) ^ (ξ' * (lam:ℝ) / 3)
                  ≤ (b:ℝ) ^ (ξ' * (lam:ℝ) * (((m:ℝ) - 2) / (m:ℝ))) := h6
                _ = (ytr b ξ' m lam) ^ (m-2) := h5.symm
                _ ≤ (ℓ:ℝ) ^ (m-2) := h4
            have hy60 : (0:ℝ) ≤ ytr b ξ' 6 lam := hy6.le
            have hsqrt0 : (0:ℝ) ≤ (Real.sqrt (ℓ:ℝ)) ^ (m-2) := by positivity
            have := Real.sqrt_le_sqrt hs1
            rwa [Real.sqrt_sq hy60, Real.sqrt_sq hsqrt0] at this
          have hkey : ((Real.sqrt (ℓ:ℝ))⁻¹) ^ m
              ≤ (1:ℝ)/(ℓ:ℝ) * (ytr b ξ' 6 lam)⁻¹ := by
            have e1 : (Real.sqrt (ℓ:ℝ)) ^ m
                = (ℓ:ℝ) * (Real.sqrt (ℓ:ℝ)) ^ (m - 2) := by
              have e2 : m = 2 + (m - 2) := by omega
              calc (Real.sqrt (ℓ:ℝ)) ^ m
                  = (Real.sqrt (ℓ:ℝ)) ^ (2 + (m-2)) := by rw [← e2]
                _ = (Real.sqrt (ℓ:ℝ))^2 * (Real.sqrt (ℓ:ℝ))^(m-2) := pow_add _ _ _
                _ = (ℓ:ℝ) * (Real.sqrt (ℓ:ℝ))^(m-2) := by
                    rw [Real.sq_sqrt hℓ0.le]
            rw [inv_pow, e1]
            have hge : (ℓ:ℝ) * ytr b ξ' 6 lam
                ≤ (ℓ:ℝ) * (Real.sqrt (ℓ:ℝ)) ^ (m-2) :=
              mul_le_mul_of_nonneg_left hsq hℓ0.le
            have hpos6 : (0:ℝ) < (ℓ:ℝ) * ytr b ξ' 6 lam := mul_pos hℓ0 hy6
            calc ((ℓ:ℝ) * (Real.sqrt (ℓ:ℝ))^(m-2))⁻¹
                ≤ ((ℓ:ℝ) * ytr b ξ' 6 lam)⁻¹ := inv_le_inv_of_le' hpos6 hge
              _ = (1:ℝ)/(ℓ:ℝ) * (ytr b ξ' 6 lam)⁻¹ := by
                  rw [mul_inv, one_div]
          calc (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
              ≤ Cb * ((palSet b lam).card : ℝ) * ((Real.sqrt (ℓ:ℝ))⁻¹) ^ m :=
                hbshcnt ℓ hp m (by omega)
            _ ≤ Cb * ((palSet b lam).card : ℝ)
                  * ((1:ℝ)/(ℓ:ℝ) * (ytr b ξ' 6 lam)⁻¹) :=
                mul_le_mul_of_nonneg_left hkey (mul_nonneg hCb0 hcT0)
        have hperm3 : ∀ m ∈ Finset.Icc 3 M,
            ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
              (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
            ≤ Cb * ((palSet b lam).card : ℝ)
                * ((ytr b ξ' 6 lam)⁻¹ * (LL b lam + Cm)) := by
          intro m hm
          have hsum1 : ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
              (fun ℓ => ¬ ℓ ^ m ≤ Ylam), (1:ℝ)/(ℓ:ℝ) ≤ LL b lam + Cm := by
            have h1 : ∀ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ¬ ℓ ^ m ≤ Ylam), ℓ.Prime ∧ ℓ ≤ b ^ lam := by
              intro ℓ hℓ
              rw [Finset.mem_filter, Finset.mem_filter] at hℓ
              have hmem := mem_Pamb.mp hℓ.1.1
              exact ⟨hmem.2, by omega⟩
            exact le_trans (sum_primes_le h1) hpRSle
          calc ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
              ≤ ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                  (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                  Cb * ((palSet b lam).card : ℝ)
                    * ((1:ℝ)/(ℓ:ℝ) * (ytr b ξ' 6 lam)⁻¹) :=
                Finset.sum_le_sum (hptw3 m hm)
            _ = Cb * ((palSet b lam).card : ℝ) * (ytr b ξ' 6 lam)⁻¹
                  * ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                    (fun ℓ => ¬ ℓ ^ m ≤ Ylam), (1:ℝ)/(ℓ:ℝ) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun ℓ _ => ?_
                ring
            _ ≤ Cb * ((palSet b lam).card : ℝ) * (ytr b ξ' 6 lam)⁻¹
                  * (LL b lam + Cm) := by
                refine mul_le_mul_of_nonneg_left hsum1 ?_
                exact mul_nonneg (mul_nonneg hCb0 hcT0) (by positivity)
            _ = Cb * ((palSet b lam).card : ℝ)
                  * ((ytr b ξ' 6 lam)⁻¹ * (LL b lam + Cm)) := by ring
        have hnn3 : (0:ℝ) ≤ Cb * ((palSet b lam).card : ℝ)
            * ((ytr b ξ' 6 lam)⁻¹ * (LL b lam + Cm)) := by
          refine mul_nonneg (mul_nonneg hCb0 hcT0) ?_
          refine mul_nonneg (by positivity) (by linarith)
        calc ∑ m ∈ Finset.Icc 3 M,
              ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
            ≤ ∑ _m ∈ Finset.Icc 3 M,
                Cb * ((palSet b lam).card : ℝ)
                  * ((ytr b ξ' 6 lam)⁻¹ * (LL b lam + Cm)) :=
              Finset.sum_le_sum hperm3
          _ = ((Finset.Icc 3 M).card : ℝ)
                * (Cb * ((palSet b lam).card : ℝ)
                  * ((ytr b ξ' 6 lam)⁻¹ * (LL b lam + Cm))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((b:ℝ) * (lam:ℝ))
                * (Cb * ((palSet b lam).card : ℝ)
                  * ((ytr b ξ' 6 lam)⁻¹ * (LL b lam + Cm))) := by
              refine mul_le_mul_of_nonneg_right ?_ hnn3
              have hcard : (Finset.Icc 3 M).card ≤ M := by
                rw [Nat.card_Icc]
                omega
              calc ((Finset.Icc 3 M).card : ℝ) ≤ (M:ℝ) := by exact_mod_cast hcard
                _ = (b:ℝ) * (lam:ℝ) := by rw [hMdef]; push_cast; ring
          _ = Cb * ((palSet b lam).card : ℝ)
                * ((b:ℝ) * (lam:ℝ) * (LL b lam + Cm) / ytr b ξ' 6 lam) := by
              rw [div_eq_mul_inv]
              ring
          _ ≤ Cb * ((palSet b lam).card : ℝ) * 1 := by
              refine mul_le_mul_of_nonneg_left hlin (mul_nonneg hCb0 hcT0)
          _ = Cb * ((palSet b lam).card : ℝ) := by ring
      exact add_le_add hC2 hC3
    -- ── assemble the three parts ──
    have hsplit : ∀ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ Pamb b lam,
          (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)
          = (∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∈ Eb b),
              (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))
            + ((∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam),
                (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))
              + (∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))) := by
      intro m _
      have h1 := Finset.sum_filter_add_sum_filter_not (Pamb b lam)
        (fun ℓ => ℓ ∈ Eb b)
        (fun ℓ => (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))
      have h2 := Finset.sum_filter_add_sum_filter_not
        ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b))
        (fun ℓ => ℓ ^ m ≤ Ylam)
        (fun ℓ => (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))
      linarith
    calc ∑ n ∈ palSet b lam, ((bigOmega n : ℝ) - (smallOmega n : ℝ))
        = ∑ m ∈ Finset.Icc 2 M, ∑ ℓ ∈ Pamb b lam,
            (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ) := hid
      _ = ∑ m ∈ Finset.Icc 2 M,
            ((∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∈ Eb b),
              (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))
            + ((∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam),
                (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))
              + (∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ)))) :=
          Finset.sum_congr rfl hsplit
      _ = (∑ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∈ Eb b),
              (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))
          + ((∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ℓ ^ m ≤ Ylam),
                (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))
            + (∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ¬ ℓ ∈ Eb b)).filter
                (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                (((palSet b lam).filter fun n => ℓ ^ m ∣ n).card : ℝ))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ Cb * (2*((Eb b).card:ℝ)) * ((palSet b lam).card : ℝ)
          + ((2 + 2*(b:ℝ)*C1) * ((palSet b lam).card : ℝ)
            + (Cb * W * ((palSet b lam).card : ℝ)
              + Cb * ((palSet b lam).card : ℝ))) :=
          add_le_add hboundA (add_le_add hboundB hboundC)
      _ = (Cb*(2*((Eb b).card:ℝ)) + (2 + 2*(b:ℝ)*C1) + (Cb*W + Cb))
            * ((palSet b lam).card : ℝ) := by ring

end EKRev
