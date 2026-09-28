import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIFactors
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition42Integral

/-!
# Amplified mean values for Matomäki–Teräväinen §5.3

* `factorial_sq_mul_integral_amplifier_le`: for the prime-power amplifier `𝓜 = P(s)^k/k!` at
  `k = ⌊log X/log 2P⌋` and a dense one-line Dirichlet polynomial with coefficients `≤ B` on
  `(N, N·2^R]`, `N·2^R ≤ 64X`,
  `k!² ∫_{-X}^{X} |𝓜 A|² ≤ 4R² C_η B² · 128 X^{4η}(1 + X^{1/a}/N)`
  (Heath-Brown's Lemma 3.4 with the amplifier's size estimates).
* `matomakiTeravainenDirichletAmplitude_shift`: the Proposition 4.2 amplitude of the shifted
  coefficient vector `n ↦ c(n+1)` is `|∑_{n ≤ N} c_n n^{-1-it}|`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The amplifier's Perron polynomial is `P(s)^k/k!` once the cutoff exceeds `(2P)^k`. -/
theorem perronPoly_primeSetAmplifierCoeff_floor {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P X : ℝ}
    (hP : 0 ≤ P) (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k)
    (hkX : (2 * P) ^ k ≤ X) (t : ℝ) :
    perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t =
      (∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) ^ k / k.factorial :=
  perronPoly_primeSetAmplifierCoeff hBp (fun _m hm =>
    Nat.le_floor ((mem_primeSetSupport_bounds hP hB hk hm).2.trans hkX)) t

/-- **Amplified Heath-Brown mean value.** -/
theorem factorial_sq_mul_integral_amplifier_le {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime)
    {P X a η Bc : ℝ} (hP : 1 ≤ P) (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k)
    (hkX : (2 * P) ^ k ≤ X) (hlo : X ^ (1 - η) ≤ P ^ k) (hstars : (P + k) ^ k ≤ P ^ k * X ^ η)
    (hfac : (k.factorial : ℝ) ≤ (P ^ k) ^ (1 / a)) (ha1 : 1 ≤ a) (ha43 : a ≤ 4 / 3)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (c : ℕ → ℂ) {K N R : ℕ} (hN : 2 ≤ N) (hc : ∀ n, c n ≠ 0 → n ≤ K ∧ N < n ∧ n ≤ N * 2 ^ R)
    (hBc : ∀ n, ‖c n‖ ≤ Bc) (hNX : ((N * 2 ^ R : ℕ) : ℝ) ≤ 64 * X) :
    (k.factorial : ℝ) ^ 2 * ∫ t in Set.Icc (-X) X,
        ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t * perronPoly c K 1 t‖ ^ 2 ≤
      4 * R ^ 2 * heathBrownLemma34Coefficient η * Bc ^ 2 *
        (128 * X ^ (4 * η) * (1 + X ^ (1 / a) / N)) := by
  have hP0 : 0 ≤ P := by linarith
  have hPk1 : 1 ≤ P ^ k := one_le_pow₀ hP
  have hPkX : P ^ k ≤ X := (pow_le_pow_left₀ hP0 (by linarith) k).trans hkX
  have hX1 : 1 ≤ X := hPk1.trans hPkX
  have he : ∀ m, primeSetAmplifierCoeff B k m ≠ 0 → P ^ k ≤ m ∧ (m : ℝ) ≤ X := by
    intro m hm
    have hb := mem_primeSetSupport_bounds hP0 hB hk (mem_primeSetSupport_of_amplifierCoeff_ne_zero hm)
    exact ⟨hb.1.le, hb.2.trans hkX⟩
  have hmain := integral_normSq_perronPoly_mul_le_lemma34 (primeSetAmplifierCoeff B k) c ⌊X⌋₊ K
    hPk1 (by linarith) hPkX he (norm_primeSetAmplifierCoeff_le_one hBp k) hN hc hBc hη
  set A := (primeSetSupport B k).card with hA
  have hfilter : ((((Finset.Icc 1 ⌊X⌋₊).filter fun m => primeSetAmplifierCoeff B k m ≠ 0).card
      : ℕ) : ℝ) ≤ A := by exact_mod_cast card_filter_primeSetAmplifierCoeff_le B k ⌊X⌋₊
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbr := heathBrownLemma34Bracket_mono (T := X) (eta := η) (L := ((N * 2 ^ R : ℕ) : ℝ))
    (L' := ((N * 2 ^ R : ℕ) : ℝ)) (N := N) (N' := N) (M := P ^ k) (Nat.cast_nonneg _) hfilter
    (by linarith) hNpos le_rfl (Nat.cast_nonneg _) le_rfl (by linarith) hη.le
  have hfacA : (k.factorial : ℝ) * A ≤ P ^ k * X ^ η :=
    (factorial_mul_card_primeSetSupport_le hP0 hB k).trans hstars
  have hamp := factorial_sq_mul_heathBrownLemma34Bracket_le (A := A) (F := k.factorial)
    (N := N) (L := ((N * 2 ^ R : ℕ) : ℝ)) hX1 hPk1 hlo (Nat.cast_nonneg _)
    (by exact_mod_cast k.factorial_pos) hfacA hfac ha1 ha43 (by exact_mod_cast (by omega : 1 ≤ N))
    (Nat.cast_nonneg _) hNX hη.le hη1
  have hC0 := heathBrownLemma34Coefficient_nonneg η
  have hBc0 : 0 ≤ Bc := (norm_nonneg _).trans (hBc 0)
  have hpre : 0 ≤ 4 * (R : ℝ) ^ 2 * heathBrownLemma34Coefficient η * Bc ^ 2 := by positivity
  calc (k.factorial : ℝ) ^ 2 * ∫ t in Set.Icc (-X) X,
        ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t * perronPoly c K 1 t‖ ^ 2
      ≤ (k.factorial : ℝ) ^ 2 * (4 * R ^ 2 * heathBrownLemma34Coefficient η * Bc ^ 2 *
          heathBrownLemma34Bracket (A : ℝ) (P ^ k) N ((N * 2 ^ R : ℕ) : ℝ) X η) := by
        refine mul_le_mul_of_nonneg_left (hmain.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hbr hpre
    _ = 4 * R ^ 2 * heathBrownLemma34Coefficient η * Bc ^ 2 *
          ((k.factorial : ℝ) ^ 2 *
            heathBrownLemma34Bracket (A : ℝ) (P ^ k) N ((N * 2 ^ R : ℕ) : ℝ) X η) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hamp hpre

/-- The Proposition 4.2 amplitude of a shifted coefficient vector is the one-line value of the
truncated Dirichlet polynomial. -/
theorem matomakiTeravainenDirichletAmplitude_shift (N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    matomakiTeravainenDirichletAmplitude N (fun n : Fin N => c ((n : ℕ) + 1)) t =
      ‖perronPoly c N 1 t‖ := by
  rw [matomakiTeravainenDirichletAmplitude, dirPoly, perronPoly]
  congr 1
  rw [← sum_fin_add_one_eq_sum_Icc N
    (fun n => c n * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [sigmaWeightedCoeff]
  have h := natCast_cpow_neg_one_add_eq_phase ⟨(n : ℕ) + 1, Nat.succ_pos _⟩ t
  simp only [PNat.mk_coe] at h
  push_cast at h ⊢
  rw [h, heathBrownDirichletPhase, Real.rpow_neg_one]
  simp only [PNat.mk_coe]
  push_cast
  ring_nf

end

end RHTower.Sieve
