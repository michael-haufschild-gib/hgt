import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverEnergyGrowthAtTheZeroAbscissa
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.CompactWindowsHavePolynomialPoleGrowth

/-!
# The actual spectral density at the translated zero frontier

The unconditional energy estimate identifies every nearby right-hand line
with the centered meromorphic symbol. Finite factorization of the residue
unit gives polynomial control on every compact height window.
-/

open Complex Set Filter Topology MeasureTheory
open RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The actual receiver has integrable and square-integrable data strictly
right of its translated zero frontier. -/
theorem receiver_data_at_zeroAbscissa {ε e : ℝ} (hε : 0 < ε)
    (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2) (he : 0 < e) :
    Integrable (dampedProfile (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e)) ∧
      MemLp (dampedProfile (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e)) 2 := by
  obtain ⟨C, hC, hE⟩ := exists_receiver_energy_le_of_zeroAbscissa hε
    (κ := 2 * (zetaZeroAbscissa - ε - 1 / 2) + e)
    (max_lt (by linarith) (by linarith))
  exact integrable_and_memLp_dampedProfile_receiver hC (by linarith) hE (by linarith)

/-- Near an attained zero abscissa, the actual Fourier density equals the
centered zeta quotient, with its energy premise discharged. -/
theorem lineSymbol_receiver_eq_centered_at_zeroAbscissa {ε e : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2)
    (he : 0 < e) (he1 : e < 1 - zetaZeroAbscissa) (y : ℝ) :
    lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y =
      centeredReceiverSymbol ε (((zetaZeroAbscissa - ε + e : ℝ) : ℂ) + (y : ℂ) * I) := by
  obtain ⟨C, hC, hE⟩ := exists_receiver_energy_le_of_zeroAbscissa hε
    (κ := 2 * (zetaZeroAbscissa - ε - 1 / 2) + e)
    (max_lt (by linarith) (by linarith))
  let s : ℂ := ((zetaZeroAbscissa - ε + e : ℝ) : ℂ) + (y : ℂ) * I
  have hsre : s.re = zetaZeroAbscissa - ε + e := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre, one_re] at this
    linarith
  have hse1 : s + (ε : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, one_re, hsre] at this
    linarith
  have hζ : riemannZeta (s + (ε : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_zetaZeroAbscissa_lt
      (by simp only [add_re, ofReal_re, hsre]; linarith)
  have hε1 : ε < 1 := by linarith [zetaZeroAbscissa_le_one]
  have hΦ := complexMellinPairing_receiver_eq hε hε1 hC (by linarith) hE
    (s := s) (by rw [hsre]; linarith) (by rw [hsre]; linarith) hζ hse1
  rw [lineSymbol_receiver_eq hC (by linarith) hE (by linarith)]
  rw [show zetaZeroAbscissa - ε - 1 / 2 + e + 1 / 2 =
    zetaZeroAbscissa - ε + e by ring]
  change complexMellinPairing (receiver ε) s / s = centeredReceiverSymbol ε s
  rw [hΦ, centeredReceiverSymbol_eq hs1, invZeta_eq_inv hse1,
    invZeta_one_add_eq_dampedDensity hε]
  ring

/-- The entire residue unit has only polynomial reciprocal growth on any
fixed compact height window at its actual zero frontier. -/
theorem exists_compact_inverse_zetaResidueUnit_bound (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ,
      zetaZeroAbscissa < z.re → z.re ≤ zetaZeroAbscissa + 1 → |z.im| ≤ R →
      (z.re - zetaZeroAbscissa) ^ N * ‖(zetaResidueUnit z)⁻¹‖ ≤ C := by
  exact exists_compact_inverse_polynomial_bound
    (fun z _ => analyticAt_zetaResidueUnit z)
    (fun z hz => zetaResidueUnit_ne_zero_of_zeroFree
      (fun _ ht => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt ht) hz) R

/-- The centered symbol has a finite polynomial order on each compact window. -/
theorem exists_centeredReceiverSymbol_compact_polynomial_bound {ε : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2) (R : ℝ) :
    ∃ (N : ℕ) (C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧ ∀ e ∈ Ioo 0 δ, ∀ y : ℝ,
      |y| ≤ R → e ^ N *
        ‖centeredReceiverSymbol ε (((zetaZeroAbscissa - ε + e : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  let b : ℝ := zetaZeroAbscissa - ε
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith [zetaZeroAbscissa_le_one]
  let δ : ℝ := min 1 ((1 - b) / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (by linarith)
  let A : ℝ := |b| + |R| + 3
  let K : Set ℂ := Metric.closedBall 0 A ∩ {s : ℂ | b ≤ s.re ∧ s.re ≤ (b + 1) / 2}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) A).inter_right
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const))
  have hK0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs h
    have := hs.2.1
    rw [h, zero_re] at this
    linarith
  have hK1 : ∀ s ∈ K, s ≠ 1 := by
    intro s hs h
    have := hs.2.2
    rw [h, one_re] at this
    linarith
  have hc : ContinuousOn (fun s : ℂ => riemannZeta s / s) K := by
    intro s hs
    exact ((analyticOn_riemannZeta s (hK1 s hs)).continuousAt.div
      continuousAt_id (hK0 s hs)).continuousWithinAt
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨N, C, hC, hInv⟩ := exists_compact_inverse_zetaResidueUnit_bound R
  let B : ℝ := A + |ε| + 1
  have hB : 0 ≤ B := by dsimp [B, A]; positivity
  let c : ℂ := invZeta (1 + (ε : ℂ))
  refine ⟨N, max D 0 * (B * C + ‖c‖), δ, by positivity, hδ, ?_⟩
  intro e he y hy
  have he0 : 0 < e := he.1
  have he1 : e ≤ 1 := he.2.le.trans (min_le_left _ _)
  have heδ : e ≤ (1 - b) / 2 := he.2.le.trans (min_le_right _ _)
  let s : ℂ := ((b + e : ℝ) : ℂ) + (y : ℂ) * I
  have hsre : s.re = b + e := by simp [s]
  have hsim : s.im = y := by simp [s]
  have hsA : ‖s‖ ≤ A := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ A := by
        rw [hsre, hsim, abs_of_pos (by linarith : 0 < b + e)]
        dsimp [A]
        linarith [le_abs_self b, le_abs_self R]
  have hsK : s ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hsA
    · rw [hsre]; linarith [he.1]
    · rw [hsre]; linarith
  have hi : e ^ N * ‖(zetaResidueUnit (s + (ε : ℂ)))⁻¹‖ ≤ C := by
    have h := hInv (s + (ε : ℂ))
      (by simp only [add_re, ofReal_re, hsre]; dsimp [b]; linarith [he.1])
      (by simp only [add_re, ofReal_re, hsre]; dsimp only [b]; linarith only [he1])
      (by simpa only [add_im, ofReal_im, add_zero, hsim] using hy)
    simpa only [add_re, ofReal_re, hsre,
      show b + e + ε - zetaZeroAbscissa = e by dsimp [b]; ring] using h
  have hnum : ‖s + (ε : ℂ) - 1‖ ≤ B := by
    calc ‖s + (ε : ℂ) - 1‖ ≤ ‖s + (ε : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖s‖ + ‖(ε : ℂ)‖) + 1 := by
        rw [norm_one]
        exact add_le_add (norm_add_le s (ε : ℂ)) le_rfl
      _ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; dsimp [B]; linarith
  have hr : e ^ N * ‖invZeta (s + (ε : ℂ))‖ ≤ B * C := by
    rw [invZeta, norm_mul]
    calc e ^ N * (‖s + (ε : ℂ) - 1‖ * ‖(zetaResidueUnit (s + (ε : ℂ)))⁻¹‖)
        = ‖s + (ε : ℂ) - 1‖ * (e ^ N * ‖(zetaResidueUnit (s + (ε : ℂ)))⁻¹‖) := by ring
      _ ≤ B * C := mul_le_mul hnum hi (by positivity) hB
  have hp : e ^ N ≤ 1 := pow_le_one₀ he.1.le he1
  have hdiff : e ^ N * ‖invZeta (s + (ε : ℂ)) - c‖ ≤ B * C + ‖c‖ := by
    calc e ^ N * ‖invZeta (s + (ε : ℂ)) - c‖
        ≤ e ^ N * (‖invZeta (s + (ε : ℂ))‖ + ‖c‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg he.1.le _)
      _ ≤ B * C + ‖c‖ := by
        have h := mul_le_mul_of_nonneg_right hp (norm_nonneg c)
        nlinarith only [hr, h]
  have hq : centeredReceiverSymbol ε s = (riemannZeta s / s) *
      (invZeta (s + (ε : ℂ)) - c) := by
    rw [centeredReceiverSymbol_eq (hK1 s hsK)]
    dsimp only [c]
    ring
  change e ^ N * ‖centeredReceiverSymbol ε s‖ ≤ _
  rw [hq, norm_mul]
  calc e ^ N * (‖riemannZeta s / s‖ * ‖invZeta (s + (ε : ℂ)) - c‖)
      = ‖riemannZeta s / s‖ * (e ^ N * ‖invZeta (s + (ε : ℂ)) - c‖) := by ring
    _ ≤ max D 0 * (B * C + ‖c‖) :=
      mul_le_mul ((hD s hsK).trans (le_max_left _ _)) hdiff
        (by positivity) (le_max_right _ _)

/-- Compact polynomial control for the actual Fourier symbol, without an
energy-growth or reciprocal-zeta bound as an assumption. -/
theorem exists_receiver_lineSymbol_compact_polynomial_bound {ε : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2)
    (hΘ1 : zetaZeroAbscissa < 1) (R : ℝ) :
    ∃ (N : ℕ) (C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧ ∀ e ∈ Ioo 0 δ, ∀ y : ℝ,
      |y| ≤ R → e ^ N *
        ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ≤ C := by
  obtain ⟨N, C, δ, hC, hδ, h⟩ := exists_centeredReceiverSymbol_compact_polynomial_bound hε hθ R
  refine ⟨N, C, min δ (1 - zetaZeroAbscissa), hC,
    lt_min hδ (by linarith), fun e he y hy => ?_⟩
  rw [lineSymbol_receiver_eq_centered_at_zeroAbscissa hε hθ he.1
    (he.2.trans_le (min_le_right _ _))]
  exact h e ⟨he.1, he.2.trans_le (min_le_left _ _)⟩ y hy

/-- Every fixed spectral window has a finite polynomial mass bound. -/
theorem exists_receiver_window_mass_polynomial_bound {ε : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2)
    (hΘ1 : zetaZeroAbscissa < 1) (a b : ℝ) (hab : a ≤ b) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ᶠ e : ℝ in 𝓝[>] 0,
      e ^ N * (∫ y in Icc a b,
        ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2) ≤ C := by
  obtain ⟨N, C, δ, hC, hδ, h⟩ :=
    exists_receiver_lineSymbol_compact_polynomial_bound hε hθ hΘ1 (|a| + |b| + 1)
  refine ⟨2 * N, C ^ 2 * |b - a|, by positivity, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ] with e he
  let S : ℝ → ℂ := lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e)
  have hpoint : ∀ y ∈ Icc a b, e ^ N * ‖S y‖ ≤ C := by
    intro y hy
    apply h e he y
    exact abs_le.mpr ⟨by linarith [hy.1, neg_abs_le a, abs_nonneg b],
      by linarith [hy.2, le_abs_self b, abs_nonneg a]⟩
  have heq : e ^ (2 * N) * (∫ y in Icc a b, ‖S y‖ ^ 2) =
      ∫ y in a..b, (e ^ N * ‖S y‖) ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    change e ^ (2 * N) * ‖S y‖ ^ 2 = (e ^ N * ‖S y‖) ^ 2
    rw [mul_pow, ← pow_mul, Nat.mul_comm N 2]
  change e ^ (2 * N) * (∫ y in Icc a b, ‖S y‖ ^ 2) ≤ _
  rw [heq]
  refine (le_abs_self _).trans ?_
  change ‖∫ y in a..b, (e ^ N * ‖S y‖) ^ 2‖ ≤ C ^ 2 * |b - a|
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  have hyI : y ∈ Icc a b := by
    rw [uIoc_of_le hab] at hy
    exact Ioc_subset_Icc_self hy
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (mul_nonneg (pow_nonneg he.1.le _) (norm_nonneg _)) (hpoint y hyI) 2

#print axioms exists_receiver_window_mass_polynomial_bound

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
