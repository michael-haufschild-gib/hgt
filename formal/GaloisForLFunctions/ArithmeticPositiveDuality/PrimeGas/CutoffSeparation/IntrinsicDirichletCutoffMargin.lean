import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.EulerSieveAbscissaMargin
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# Intrinsic Dirichlet shell convolutions and exact finite Möbius pole-unit splitting above `84.5`

External multiplication `mollifiedAlignedReconstructed M c K w = Q_{M,c}(w) · alignedReconstructedCutoff K w`
scales reading and error by the same factor `‖Q_{M,c}(w)‖`. Whenever `Q_{M,c}(w) ≠ 0` — in particular
for `eulerSieveSurgCoeff y` across `Re w > 0` — `‖Q_{M,c}(w)‖` cancels identically from the margin
inequality (`external_mollifier_margin_iff_unmollified`), leaving the winning depth set `{K ≥ 1}`
unchanged.

Applying the Dirichlet convolution `dirichletSurgWeight M c` **inside** the prime-gas shell sums
before truncation (`weightedAlignedReconstructed (dirichletSurgWeight M c) K w`) breaks equal
scaling and exposes an exact finite-depth Möbius pole-unit decomposition:

1. **Intrinsic `|ζ|`-free, `‖Q‖`-free zero threshold (`intrinsicDirichletZeroThreshold`,
   `norm_weightedAlignedReconstructed_le_intrinsicZeroThreshold_of_zeta_eq_zero`,
   `moebius_powerSaving_intrinsic_linear_margin`)**: at any zero `ζ(w) = 0` (`Re w > 0`), both the
   limit and the `|ζ|` remainder of `adjacentCutoff` vanish identically, bounding
   `‖weightedAlignedReconstructed (dirichletSurgWeight M c) K w‖` (`M ≤ 4^K`) by an elementary
   threshold independent of `‖Q_{M,c}(w)‖`; in the high-ordinate Möbius power-saving window, the
   intrinsic shell reading beats this threshold by a linear-in-height margin `> t / 8`.
2. **Exact finite Möbius shell inversion (`weightedAdjacentCutoff_fullMoebius_eq`,
   `weightedAlignedReconstructed_fullMoebius_eq_sub_one`)**: for `M ≥ C^(2K)`, Möbius cancellation
   `∑_{d ∣ n} μ(d) = [n = 1]` collapses every inner shell sum to `1`, giving the exact identity
   `weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) t j (C^(2K)) w = (w - 1) · finiteContrastTransfer C K w`
   across all `w ∈ ℂ`, and `weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K w = w - 1`
   for `M ≥ 9^K`, `K ≥ 1`, `Re w > 0`.
3. **Dyadic pole-unit split and residual `RH` equivalence (`exact_head_plus_moebiusTail_eq_sub_one`,
   `tendsto_intrinsicZeroThreshold_two_pow_zero`,
   `rh_of_dyadic_moebiusTail_le_eightyFour_and_half`,
   `rh_iff_intrinsic_moebius_margin_above_eightyFour_and_half`)**: splitting `9^K` at `M = 2^K`
   decomposes `w - 1` into the `2^K` intrinsic head (whose zero threshold decays as
   `O(K · 2^{-K(2 Re w - 1)}) → 0` for `Re w > 1/2`) plus `intrinsicMoebiusTail (2^K) K w`, so
   `∃ᶠ K in atTop, ‖intrinsicMoebiusTail (2^K) K w‖ ≤ 169 / 2` unconditionally forces `ζ(w) ≠ 0`
   on `{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}`, and `RiemannHypothesis` is unconditionally
   equivalent to `‖(w - 1) - intrinsicMoebiusTail M K₀ w‖` beating `intrinsicDirichletZeroThreshold`.
4. **Integer-ray dilation elimination below `84.5 k`
   (`strip_div_nat_zeta_ne_zero_below_scaled_eightyFour_and_half`)**: for every `k ≥ 2` and every
   `0 < Re w < 1` with `|Im w| ≤ (169 / 2) k`, `ζ(w / k) ≠ 0` unconditionally and the reflected
   partner `1 - conj (w / k)` carries a strict cutoff margin.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter MeasureTheory Set Metric
open scoped Topology ComplexConjugate BigOperators

/-! ### Part 1: Exact equal-scaling cancellation law for external Dirichlet/Euler multipliers -/

/-- External multiplication `mollifiedAlignedReconstructed M c K w` preserves the exact cutoff-margin
depth set whenever `dirichletSurgPoly M c w ≠ 0`: `‖Q_{M,c}(w)‖` cancels identically from both sides. -/
theorem external_mollifier_margin_iff_unmollified (M : ℕ) (c : ℕ → ℝ) (K : ℕ) {w : ℂ}
    (hQ : dirichletSurgPoly M c w ≠ 0) :
    mollifiedAlignedError M c K w < ‖mollifiedAlignedReconstructed M c K w‖ ↔
      alignedReconstructionError K w < ‖alignedReconstructedCutoff K w‖ := by
  have hpos : 0 < ‖dirichletSurgPoly M c w‖ := norm_pos_iff.mpr hQ
  unfold mollifiedAlignedError mollifiedAlignedReconstructed
  rw [norm_mul]
  exact ⟨fun h => lt_of_mul_lt_mul_left h hpos.le, fun h => mul_lt_mul_of_pos_left h hpos⟩

/-- At a mollifier zero `dirichletSurgPoly M c w = 0`, external multiplication scales both reading
and error to `0`, making the strict margin false at every depth `K`. -/
theorem external_mollifier_margin_false_of_poly_eq_zero (M : ℕ) (c : ℕ → ℝ) (K : ℕ) {w : ℂ}
    (hQ : dirichletSurgPoly M c w = 0) :
    ¬ (mollifiedAlignedError M c K w < ‖mollifiedAlignedReconstructed M c K w‖) := by
  unfold mollifiedAlignedError mollifiedAlignedReconstructed
  rw [hQ, norm_zero, zero_mul, zero_mul, norm_zero]
  exact lt_irrefl 0

/-- For every Euler-sieve aperture `y : ℕ` and every `w` with `Re w > 0`, the external Euler-sieve
margin holds at depth `K` if and only if the unmollified aligned margin holds at the same depth `K`. -/
theorem eulerSieve_margin_iff_unmollified (y K : ℕ) {w : ℂ} (hw : 0 < w.re) :
    mollifiedAlignedError (eulerPrimorial y) (eulerSieveSurgCoeff y) K w <
      ‖mollifiedAlignedReconstructed (eulerPrimorial y) (eulerSieveSurgCoeff y) K w‖ ↔
      alignedReconstructionError K w < ‖alignedReconstructedCutoff K w‖ :=
  external_mollifier_margin_iff_unmollified (eulerPrimorial y) (eulerSieveSurgCoeff y) K
    (dirichletSurgPoly_eulerSieve_ne_zero y hw)

/-! ### Part 2: Intrinsic `|ζ|`-free, `‖Q‖`-free shell zero-threshold and linear high-ordinate margin -/

/-- Purely elementary `|ζ(w)|`-free truncation bound for `adjacentCutoff t j Y w` at `ζ(w) = 0`. -/
def zetaFreeAdjacentBound (t : ExceptionalTime) (j Y : ℕ) (w : ℂ) : ℝ :=
  zetaFreeTruncationBound t j Y w +
    (((tailRadix t j).val : ℝ) + 1) * zetaFreeTruncationBound t (j + 1) Y w

/-- Intrinsic `|ζ(w)|`-free, `‖Q_{M,c}(w)‖`-free zero-exclusion threshold for
`weightedAlignedReconstructed (dirichletSurgWeight M c) K w`. -/
def intrinsicDirichletZeroThreshold (M : ℕ) (c : ℕ → ℝ) (K : ℕ) (w : ℂ) : ℝ :=
  let s₂ := (∑ d ∈ Finset.Icc 1 M, |c d| * (d : ℝ) ^ (-w.re) *
    zetaFreeAdjacentBound halfTurnClock 0 (2 ^ (2 * K) / d) w) /
    (1 - (2 : ℝ) ^ (-(2 * K : ℝ) * w.re))
  let s₃ := (∑ d ∈ Finset.Icc 1 M, |c d| * (d : ℝ) ^ (-w.re) *
    zetaFreeAdjacentBound primeThreeClock 0 (3 ^ (2 * K) / d) w) /
    (1 - (3 : ℝ) ^ (-(2 * K : ℝ) * w.re))
  (‖contrastTransfer 2 w‖ * s₂ + ‖contrastTransfer 3 w‖ * s₃) / twoPrimeTransferMass w

/-- Algebraic cancellation of the `X^(1 - w) / (1 - w)` counterterms between `renormalizedCutoff`
at refinements `j` and `j + 1`. -/
theorem adjacentCutoff_eq_renormalized_sub (t : ExceptionalTime) (j Y : ℕ) (w : ℂ) :
    adjacentCutoff t j Y w =
      renormalizedCutoff t j Y w -
        (((tailRadix t j).val : ℂ) + 1) * renormalizedCutoff t (j + 1) Y w := by
  let C := tailRadix t j
  let c : ℂ := C.val
  have hcp : 1 < C.val := radix_gt_one t j
  have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr (show (C.val : ℂ) ≠ 1 by exact_mod_cast hcp.ne')
  have hcr : 1 < C.val ^ 2 := one_lt_pow₀ hcp (by norm_num)
  have hc2 : c ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (show (C.val : ℂ) ^ 2 ≠ 1 by exact_mod_cast hcr.ne')
  have hd : 2 / (c - 1) = (c + 1) * (2 / (c ^ 2 - 1)) := by
    field_simp [hc1, hc2]; ring
  simp only [renormalizedCutoff, tailRadix_succ, PNat.pow_coe, Nat.cast_pow, adjacentCutoff]
  change _ = shellCutoff t j Y w - 2 / (c - 1) * _ -
    (c + 1) * (shellCutoff t (j + 1) Y w - 2 / (c ^ 2 - 1) * _)
  rw [hd]
  ring

/-- At any zero `ζ(w) = 0` in `Re w > 0`, `adjacentCutoff t j Y w` (`Y ≥ 1`) is bounded solely by
`zetaFreeAdjacentBound t j Y w`, with zero `|ζ(w)|` remainder. -/
theorem norm_adjacentCutoff_le_zetaFreeAdjacentBound_of_zeta_eq_zero
    (t : ExceptionalTime) (j : ℕ) {Y : ℕ} (hY : 1 ≤ Y)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hζ : riemannZeta w = 0) :
    ‖adjacentCutoff t j Y w‖ ≤ zetaFreeAdjacentBound t j Y w := by
  have hren : ∀ m : ℕ, ‖renormalizedCutoff t m Y w‖ ≤ zetaFreeTruncationBound t m Y w := by
    intro m
    have hb := norm_renormalizedCutoff_sub_limit_le t m hY hw hw1
    dsimp only at hb
    rw [digitImbalanceErrorConst_eq_zeta_add_zetaFree] at hb
    rw [hζ, mul_zero, zero_div, sub_zero, norm_zero, zero_mul, zero_add] at hb
    simpa only [zetaFreeTruncationBound] using hb
  rw [adjacentCutoff_eq_renormalized_sub]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have hc_norm : ‖((tailRadix t j).val : ℂ) + 1‖ = ((tailRadix t j).val : ℝ) + 1 := by
    have : ((tailRadix t j).val : ℂ) + 1 = ((((tailRadix t j).val : ℝ) + 1 : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc_norm]
  unfold zetaFreeAdjacentBound
  exact add_le_add (hren j) (mul_le_mul_of_nonneg_left (hren (j + 1)) (by positivity))

private theorem norm_real_mul_nat_cpow_neg (r : ℝ) {d : ℕ} (hd : 1 ≤ d) (w : ℂ) :
    ‖(r : ℂ) * (d : ℂ) ^ (-w)‖ = |r| * (d : ℝ) ^ (-w.re) := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show (d : ℂ) = ((d : ℝ) : ℂ) by simp,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hd_pos.ne'),
    ← Complex.ofReal_log hd_pos.le, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    zero_mul, sub_zero, Real.rpow_def_of_pos hd_pos]

private theorem zetaFreeAdjacentBound_nonneg_of_re_pos (t : ExceptionalTime) (j : ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) {w : ℂ} (hw : 0 < w.re) :
    0 ≤ zetaFreeAdjacentBound t j Y w := by
  have zf_nn : ∀ m : ℕ, 0 ≤ zetaFreeTruncationBound t m Y w := by
    intro m
    have hC1 : (1 : ℝ) < (tailRadix t m).val := by exact_mod_cast radix_gt_one t m
    have hYr1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
    have hlog_nn : 0 ≤ Real.logb (tailRadix t m).val Y := Real.logb_nonneg hC1 hYr1
    have hconst_nn : 0 ≤ zetaFreeDigitErrorConst t m w := by
      unfold zetaFreeDigitErrorConst
      dsimp only
      have h1 : 0 ≤ 2 * ((tailRadix t m).val : ℝ) / (((tailRadix t m).val - 1) * ‖1 - w‖) :=
        div_nonneg (by positivity) (mul_nonneg (sub_pos.mpr hC1).le (norm_nonneg _))
      have h2 : 0 ≤ 2 * ((tailRadix t m).val : ℝ) / ((tailRadix t m).val - 1) + 1 :=
        add_nonneg (div_nonneg (by positivity) (sub_pos.mpr hC1).le) zero_le_one
      have h3 : 0 ≤ (((tailRadix t m).val : ℝ) / ((tailRadix t m).val - 1)) *
          (2 : ℝ) ^ (w.re + 1) * (3 * ‖w‖ + ‖w * (w + 1)‖ / (4 * (w.re + 1))) :=
        mul_nonneg (mul_nonneg (div_nonneg (by positivity) (sub_pos.mpr hC1).le)
          (Real.rpow_nonneg zero_le_two _))
          (add_nonneg (by positivity) (div_nonneg (norm_nonneg _) (by linarith)))
      linarith
    unfold zetaFreeTruncationBound
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  unfold zetaFreeAdjacentBound
  exact add_nonneg (zf_nn j) (mul_nonneg (by positivity) (zf_nn (j + 1)))

/-- **Intrinsic `|ζ|`-free zero bound:** at any zero `ζ(w) = 0` (`Re w > 0`), for every `(M, c, K)`
with `1 ≤ K` and `M ≤ 4^K`, `‖weightedAlignedReconstructed (dirichletSurgWeight M c) K w‖` is bounded
by `intrinsicDirichletZeroThreshold M c K w` without any external `‖Q_{M,c}(w)‖` factor. -/
theorem norm_weightedAlignedReconstructed_le_intrinsicZeroThreshold_of_zeta_eq_zero
    (M : ℕ) (c : ℕ → ℝ) {K : ℕ} (hK : 1 ≤ K) (hM : M ≤ 2 ^ (2 * K))
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hζ : riemannZeta w = 0) :
    ‖weightedAlignedReconstructed (dirichletSurgWeight M c) K w‖ ≤
      intrinsicDirichletZeroThreshold M c K w := by
  have hm_pos : 0 < twoPrimeTransferMass w := two_prime_transfer_mass_pos ⟨w, hw⟩
  have h23 : 2 ^ (2 * K) ≤ 3 ^ (2 * K) := Nat.pow_le_pow_left (by norm_num) (2 * K)
  have hchan : ∀ (tc : ExceptionalTime) (B : ℕ+),
      tailRadix tc 0 = B → (1 : ℝ) < B.val → M ≤ B.val ^ (2 * K) →
      ‖weightedAdjacentCutoff (dirichletSurgWeight M c) tc 0 (B.val ^ (2 * K)) w /
          (1 - (heat w B) ^ (2 * K))‖ ≤
        (∑ d ∈ Finset.Icc 1 M, |c d| * (d : ℝ) ^ (-w.re) *
          zetaFreeAdjacentBound tc 0 (B.val ^ (2 * K) / d) w) /
          (1 - (B.val : ℝ) ^ (-(2 * K : ℝ) * w.re)) := by
    intro tc B hrad hB1 hMB
    have hrpow_lt1 : (B.val : ℝ) ^ (-(2 * K : ℝ) * w.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hB1
        (mul_neg_of_neg_of_pos (by have : (0 : ℝ) < K := Nat.cast_pos.mpr hK; linarith) hw)
    have hden_r : 0 < 1 - (B.val : ℝ) ^ (-(2 * K : ℝ) * w.re) := sub_pos.mpr hrpow_lt1
    have hden_ge : 1 - (B.val : ℝ) ^ (-(2 * K : ℝ) * w.re) ≤ ‖(1 : ℂ) - (heat w B) ^ (2 * K)‖ := by
      have h := norm_sub_norm_le (1 : ℂ) ((heat w B) ^ (2 * K))
      have hnorm : ‖(heat w B) ^ (2 * K)‖ = (B.val : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using norm_heat_pow B (2 * K) w
      rwa [norm_one, hnorm] at h
    have hden_pos : 0 < ‖(1 : ℂ) - (heat w B) ^ (2 * K)‖ := lt_of_lt_of_le hden_r hden_ge
    have hnum_le : ‖weightedAdjacentCutoff (dirichletSurgWeight M c) tc 0 (B.val ^ (2 * K)) w‖ ≤
        ∑ d ∈ Finset.Icc 1 M, |c d| * (d : ℝ) ^ (-w.re) *
          zetaFreeAdjacentBound tc 0 (B.val ^ (2 * K) / d) w := by
      rw [weightedAdjacentCutoff_dirichletSurgWeight]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
      rw [Finset.mem_Icc] at hd
      have hd_pos : 0 < d := by omega
      have hdiv1 : 1 ≤ B.val ^ (2 * K) / d :=
        (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [one_mul]; exact hd.2.trans hMB)
      rw [norm_mul, norm_real_mul_nat_cpow_neg (c d) hd.1 w]
      exact mul_le_mul_of_nonneg_left
        (norm_adjacentCutoff_le_zetaFreeAdjacentBound_of_zeta_eq_zero tc 0 hdiv1 hw hw1 hζ)
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
    have hsum_nn : 0 ≤ ∑ d ∈ Finset.Icc 1 M, |c d| * (d : ℝ) ^ (-w.re) *
        zetaFreeAdjacentBound tc 0 (B.val ^ (2 * K) / d) w := by
      refine Finset.sum_nonneg fun d hd => ?_
      rw [Finset.mem_Icc] at hd
      have hdiv1 : 1 ≤ B.val ^ (2 * K) / d :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [one_mul]; exact hd.2.trans hMB)
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
        (zetaFreeAdjacentBound_nonneg_of_re_pos tc 0 hdiv1 hw)
    rw [norm_div]
    exact (div_le_div_of_nonneg_right hnum_le hden_pos.le).trans
      (div_le_div_of_nonneg_left hsum_nn hden_r hden_ge)
  have hc2 := hchan halfTurnClock 2 tailRadix_halfTurnClock_zero (by norm_num) hM
  have hc3 := hchan primeThreeClock 3 tailRadix_primeThreeClock_zero (by norm_num) (hM.trans h23)
  unfold weightedAlignedReconstructed intrinsicDirichletZeroThreshold
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm_pos]
  refine div_le_div_of_nonneg_right ((norm_add_le _ _).trans ?_) hm_pos.le
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  exact add_le_add (mul_le_mul_of_nonneg_left hc2 (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hc3 (norm_nonneg _))

/-- Beating `intrinsicDirichletZeroThreshold M c K₀ w` at a single shell depth `K₀ ≥ 1` (`M ≤ 4^K₀`)
unconditionally excludes `ζ(w) = 0` and transfers to an actual unmollified `renormalizedCutoff`
margin on every prime clock. -/
theorem intrinsicDirichlet_margin_forces_zeta_ne_zero
    (M : ℕ) (c : ℕ → ℝ) {K₀ : ℕ} (hK₀ : 1 ≤ K₀) (hM : M ≤ 2 ^ (2 * K₀))
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1)
    (hmarg : intrinsicDirichletZeroThreshold M c K₀ w <
      ‖weightedAlignedReconstructed (dirichletSurgWeight M c) K₀ w‖) :
    riemannZeta w ≠ 0 ∧
      ∀ (t : ExceptionalTime) (j : ℕ),
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  have hne : riemannZeta w ≠ 0 := fun hζ =>
    (norm_weightedAlignedReconstructed_le_intrinsicZeroThreshold_of_zeta_eq_zero
      M c hK₀ hM hw hw1 hζ).not_gt hmarg
  exact ⟨hne, fun t j => (exists_zetaFree_margin_iff_zeta_ne_zero t j hw hw1).mpr hne⟩

/-- For any fixed `(M, c)` and `Re w > 0`, `intrinsicDirichletZeroThreshold M c K w → 0` as `K → ∞`. -/
theorem tendsto_intrinsicDirichletZeroThreshold_zero (M : ℕ) (c : ℕ → ℝ)
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun K : ℕ => intrinsicDirichletZeroThreshold M c K w) atTop (𝓝 0) := by
  have hchan : ∀ (tc : ExceptionalTime) (B : ℕ), 1 < B →
      Tendsto (fun K : ℕ =>
        (∑ d ∈ Finset.Icc 1 M, |c d| * (d : ℝ) ^ (-w.re) *
          zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w) /
          (1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re))) atTop (𝓝 0) := by
    intro tc B hB
    have hBr : (1 : ℝ) < B := by exact_mod_cast hB
    have hpow_top : ∀ d : ℕ, 0 < d → Tendsto (fun K : ℕ => B ^ (2 * K) / d) atTop atTop := by
      intro d hd
      refine tendsto_atTop.mpr fun N => (eventually_ge_atTop (N * d)).mono fun K hK => ?_
      exact (Nat.le_div_iff_mul_le hd).mpr (hK.trans ((by omega : K ≤ 2 * K).trans (Nat.lt_pow_self hB).le))
    have hsum0 : Tendsto (fun K : ℕ =>
        ∑ d ∈ Finset.Icc 1 M, |c d| * (d : ℝ) ^ (-w.re) *
          zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w) atTop (𝓝 0) := by
      have hs := tendsto_finsetSum (Finset.Icc 1 M) fun d hd => by
        have hd_pos : 0 < d := by linarith [(Finset.mem_Icc.mp hd).1]
        have hzf0 := (tendsto_zetaFreeTruncationBound_zero tc 0 hw).comp (hpow_top d hd_pos)
        have hzf1 := ((tendsto_zetaFreeTruncationBound_zero tc 1 hw).comp
          (hpow_top d hd_pos)).const_mul (((tailRadix tc 0).val : ℝ) + 1)
        rw [mul_zero] at hzf1
        have hadj := hzf0.add hzf1
        rw [add_zero] at hadj
        have hmul := hadj.const_mul (|c d| * (d : ℝ) ^ (-w.re))
        rw [mul_zero] at hmul
        exact hmul
      rw [Finset.sum_const_zero] at hs
      exact hs.congr fun _ => rfl
    have hden1 : Tendsto (fun K : ℕ => 1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re)) atTop (𝓝 1) := by
      have hexp : Tendsto (fun K : ℕ => (K : ℝ) * (2 * w.re * Real.log B)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos (by linarith) (Real.log_pos hBr))
      have hr0 : Tendsto (fun K : ℕ => (B : ℝ) ^ (-(2 * K : ℝ) * w.re)) atTop (𝓝 0) := by
        refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hexp).congr fun K => ?_
        dsimp only [Function.comp_apply]
        rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < B)]
        congr 1; ring
      simpa only [sub_zero] using tendsto_const_nhds.sub hr0
    have hdiv0 := hsum0.div hden1 one_ne_zero
    rw [zero_div] at hdiv0
    exact hdiv0.congr fun _ => rfl
  have hs2 := (hchan halfTurnClock 2 (by norm_num)).const_mul ‖contrastTransfer 2 w‖
  have hs3 := (hchan primeThreeClock 3 (by norm_num)).const_mul ‖contrastTransfer 3 w‖
  rw [mul_zero] at hs2 hs3
  have htot := (hs2.add hs3).div_const (twoPrimeTransferMass w)
  rw [add_zero, zero_div] at htot
  exact htot

/-- **Linear-in-height intrinsic Möbius margin at high ordinates:** in the power-saving window
`U ≥ exp 100`, `M = ⌊U^{1/4}⌋₊`, `[T₁, T₂] ⊂ (U/4, U/2)`, outside the `O((log U)^5 U^{1 - (σ - 1/2)/5})`
exceptional set, every `t ∈ [T₁, T₂] \ badSet` admits a shell depth `K₀ ≥ 1` (`M ≤ 4^K₀`) where
`weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K₀ (σ + i t)` exceeds the
`‖Q‖`-free threshold `intrinsicDirichletZeroThreshold` by at least `t / 8`. -/
theorem moebius_powerSaving_intrinsic_linear_margin :
    ∃ B_mob : ℝ, 0 < B_mob ∧
      ∀ {σ U T₁ T₂ : ℝ}, 1 / 2 < σ → σ ≤ 1 → Real.exp 100 ≤ U →
        U / 4 < T₁ → T₁ ≤ T₂ → T₂ < U / 2 →
        let M : ℕ := ⌊U ^ (1 / 4 : ℝ)⌋₊
        let badSet : Set ℝ := {t ∈ Icc T₁ T₂ |
          (1 / 2 : ℝ) < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
            dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖}
        MeasurableSet badSet ∧
        (volume badSet).toReal ≤
          4 * B_mob * (Real.log U + 2) ^ 5 * U ^ (1 - (σ - 1 / 2) / 5) ∧
        ∀ t ∈ Icc T₁ T₂ \ badSet,
          ∃ K₀ : ℕ, 1 ≤ K₀ ∧ M ≤ 2 ^ (2 * K₀) ∧
            intrinsicDirichletZeroThreshold M moebiusReal K₀ ((σ : ℂ) + (t : ℂ) * Complex.I) + t / 8 <
              ‖weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K₀
                ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨B_mob, hB_pos, hmob⟩ := moebius_mollifier_powerSaving_highOrdinate_margin
  refine ⟨B_mob, hB_pos, fun {σ U T₁ T₂} hσ hσ1 hU hT₁ hT hT₂ => ?_⟩
  obtain ⟨-, hmeas, hvol, hgood⟩ := hmob hσ hσ1 hU hT₁ hT hT₂
  refine ⟨hmeas, hvol, fun t ht => ?_⟩
  set M : ℕ := ⌊U ^ (1 / 4 : ℝ)⌋₊
  set w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hw_re : w.re = σ := by
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  have hw0 : 0 < w.re := by linarith
  have hU_pos : 0 < U := (Real.exp_pos 100).trans_le hU
  have ht_pos : 0 < t := by linarith [ht.1.1]
  have hfloor := (hgood t ht).1
  have hthr0 := tendsto_intrinsicDirichletZeroThreshold_zero M moebiusReal hw0
  obtain ⟨K₀, ⟨⟨hK1, hKM⟩, hthr_lt⟩, hw_ge⟩ :=
    ((((eventually_ge_atTop 1).and (eventually_ge_atTop M)).and
      (hthr0.eventually (Iio_mem_nhds (by positivity : 0 < t / 8)))).and hfloor).exists
  have hM_pow : M ≤ 2 ^ (2 * K₀) :=
    hKM.trans ((by omega : K₀ ≤ 2 * K₀).trans (Nat.lt_pow_self (by norm_num : 1 < 2)).le)
  exact ⟨K₀, hK1, hM_pow, by linarith⟩

/-! ### Part 3: Exact finite Möbius shell inversion and dyadic pole-unit splitting -/

private theorem weightedRadialCutoff_moebius_of_le {Y M : ℕ} (hY1 : 1 ≤ Y) (hYM : Y ≤ M) (w : ℂ) :
    weightedRadialCutoff (dirichletSurgWeight M moebiusReal) Y w = 1 := by
  have hsub : ({1} : Finset ℕ) ⊆ Finset.Icc 1 Y := by
    intro n hn
    rw [Finset.mem_singleton.mp hn]
    exact Finset.mem_Icc.mpr ⟨le_rfl, hY1⟩
  unfold weightedRadialCutoff
  rw [← Finset.sum_subset hsub]
  · simp [dirichletSurgWeight_moebiusReal_of_le le_rfl (hY1.trans hYM)]
  · intro n hn hnot
    rw [Finset.mem_Icc] at hn
    have hn_ne1 : n ≠ 1 := by simpa using hnot
    rw [dirichletSurgWeight_moebiusReal_of_le hn.1 (hn.2.trans hYM), if_neg hn_ne1]
    simp

/-- **Exact finite Möbius shell inversion on every prime-gas clock:** whenever `C^(2K) ≤ M`
(`C = tailRadix t j`), Möbius cancellation collapses every inner shell sum to `1`, so
`weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) t j (C^(2K)) w` equals the exact
`ζ`-free pole-unit response `(w - 1) · finiteContrastTransfer C K w` for **all** `w ∈ ℂ`. -/
theorem weightedAdjacentCutoff_fullMoebius_eq (t : ExceptionalTime) (j K : ℕ)
    {M : ℕ} (hM : (tailRadix t j).val ^ (2 * K) ≤ M) (w : ℂ) :
    weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) t j
        ((tailRadix t j).val ^ (2 * K)) w =
      (w - 1) * finiteContrastTransfer (tailRadix t j) K w := by
  set C := tailRadix t j with hCdef
  set q := heat w C with hqdef
  have hC1 : 1 < C.val := radix_gt_one t j
  have hrad_succ : tailRadix t (j + 1) = C ^ 2 := tailRadix_succ t j
  have hB1 : 1 < (tailRadix t (j + 1)).val := radix_gt_one t (j + 1)
  have hpow_B : C.val ^ (2 * K) = (tailRadix t (j + 1)).val ^ K := by
    rw [hrad_succ, PNat.pow_coe, ← pow_mul]
  have hlog_C : Nat.log C.val (C.val ^ (2 * K)) = 2 * K :=
    (Nat.log_eq_iff (Or.inr ⟨hC1, (pow_pos C.pos (2 * K)).ne'⟩)).mpr
      ⟨le_rfl, Nat.pow_lt_pow_right hC1 (Nat.lt_succ_self _)⟩
  have hlog_B : Nat.log (tailRadix t (j + 1)).val (C.val ^ (2 * K)) = K := by
    rw [hpow_B]
    exact (Nat.log_eq_iff (Or.inr ⟨hB1, (pow_pos (tailRadix t (j + 1)).pos K).ne'⟩)).mpr
      ⟨le_rfl, Nat.pow_lt_pow_right hB1 (Nat.lt_succ_self _)⟩
  have hsh_j : weightedShellCutoff (dirichletSurgWeight M moebiusReal) t j (C.val ^ (2 * K)) w =
      2 * ∑ i ∈ Finset.range (2 * K), q ^ (i + 1) := by
    rw [weightedShellCutoff, ← hCdef, ← hqdef, hlog_C]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi_lt : i < 2 * K := Finset.mem_range.mp hi
    have hdiv1 : 1 ≤ C.val ^ (2 * K) / C.val ^ (i + 1) :=
      (Nat.le_div_iff_mul_le (pow_pos C.pos (i + 1))).mpr
        (by rw [one_mul]; exact Nat.pow_le_pow_right C.pos (by omega))
    have hdivM : C.val ^ (2 * K) / C.val ^ (i + 1) ≤ M := (Nat.div_le_self _ _).trans hM
    rw [weightedRadialCutoff_moebius_of_le hdiv1 hdivM w, mul_one]
  have hheat_succ : heat w (tailRadix t (j + 1)) = q ^ 2 := by
    rw [hrad_succ, pow_two, heat_mul, pow_two, ← hqdef]
  have hsh_succ : weightedShellCutoff (dirichletSurgWeight M moebiusReal) t (j + 1)
        (C.val ^ (2 * K)) w =
      2 * ∑ r ∈ Finset.range K, (q ^ 2) ^ (r + 1) := by
    rw [weightedShellCutoff, hheat_succ, hlog_B]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_lt : r < K := Finset.mem_range.mp hr
    have hdiv1 : 1 ≤ C.val ^ (2 * K) / (tailRadix t (j + 1)).val ^ (r + 1) := by
      rw [hpow_B]
      exact (Nat.le_div_iff_mul_le (pow_pos (tailRadix t (j + 1)).pos (r + 1))).mpr
        (by rw [one_mul]; exact Nat.pow_le_pow_right (tailRadix t (j + 1)).pos (by omega))
    have hdivM : C.val ^ (2 * K) / (tailRadix t (j + 1)).val ^ (r + 1) ≤ M :=
      (Nat.div_le_self _ _).trans hM
    rw [weightedRadialCutoff_moebius_of_le hdiv1 hdivM w, mul_one]
  have hpair : (∑ i ∈ Finset.range (2 * K), q ^ (i + 1)) -
      ((C.val : ℂ) + 1) * (∑ r ∈ Finset.range K, (q ^ 2) ^ (r + 1)) =
      q * (1 - (C.val : ℂ) * q) * ∑ r ∈ Finset.range K, q ^ (2 * r) := by
    have hsplit : ∀ m : ℕ, (∑ i ∈ Finset.range (2 * m), q ^ (i + 1)) =
        ∑ r ∈ Finset.range m, (q ^ (2 * r + 1) + q ^ (2 * r + 2)) := by
      intro m
      induction m with
      | zero => simp
      | succ n ih =>
        rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
          Finset.sum_range_succ, add_assoc]
    rw [hsplit K, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hp1 : q ^ (2 * r + 1) = q ^ (2 * r) * q := pow_succ q (2 * r)
    have hp2 : q ^ (2 * r + 2) = q ^ (2 * r) * q * q := by rw [pow_succ, hp1]
    have hp3 : (q ^ 2) ^ (r + 1) = q ^ (2 * r) * q * q := by
      rw [← pow_mul, Nat.mul_add, mul_one, hp2]
    rw [hp1, hp2, hp3]; ring
  have hdslope : (w - 1) * dslope (fun z => heat z C) 1 w = q - (C.val : ℂ)⁻¹ := by
    have h1 : heat 1 C = (C.val : ℂ)⁻¹ := by rw [heat_eq_cpow, Complex.cpow_neg_one]
    by_cases hw1 : w = 1
    · subst hw1
      rw [sub_self, zero_mul, hqdef, h1, sub_self]
    · rw [dslope_of_ne _ hw1, slope_def_field, h1, ← hqdef]
      field_simp [sub_ne_zero.mpr hw1]
  have hc_ne : (C.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr C.ne_zero
  rw [weightedAdjacentCutoff, ← hCdef, hsh_j, hsh_succ]
  have lhs_eq : 2 * (∑ i ∈ Finset.range (2 * K), q ^ (i + 1)) -
      ((C.val : ℂ) + 1) * (2 * ∑ r ∈ Finset.range K, (q ^ 2) ^ (r + 1)) =
      2 * (q * (1 - (C.val : ℂ) * q) * ∑ r ∈ Finset.range K, q ^ (2 * r)) := by
    linear_combination 2 * hpair
  rw [lhs_eq]
  unfold finiteContrastTransfer
  rw [← hqdef]
  have rhs_eq : (w - 1) * (-2 * (C.val : ℂ) * q * dslope (fun z => heat z C) 1 w *
      ∑ r ∈ Finset.range K, q ^ (2 * r)) =
      -2 * (C.val : ℂ) * q * ((w - 1) * dslope (fun z => heat z C) 1 w) *
        ∑ r ∈ Finset.range K, q ^ (2 * r) := by ring
  rw [rhs_eq, hdslope]
  field_simp [hc_ne]; ring

/-- **Exact finite-depth recovery of `w - 1` across `Re w > 0`:** for every `K ≥ 1` and `M ≥ 9^K`,
`weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K w = w - 1` identically — even at
hypothetical zeros of `riemannZeta`. -/
theorem weightedAlignedReconstructed_fullMoebius_eq_sub_one
    {K M : ℕ} (hK : 1 ≤ K) (hM : 3 ^ (2 * K) ≤ M) {w : ℂ} (hw : 0 < w.re) :
    weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K w = w - 1 := by
  have hm_ne : (twoPrimeTransferMass w : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (two_prime_transfer_mass_pos ⟨w, hw⟩).ne'
  have h23 : 2 ^ (2 * K) ≤ 3 ^ (2 * K) := Nat.pow_le_pow_left (by norm_num) (2 * K)
  have hchan : ∀ (tc : ExceptionalTime) (B : ℕ+),
      tailRadix tc 0 = B → 1 < B.val → B.val ^ (2 * K) ≤ M →
      weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) tc 0 (B.val ^ (2 * K)) w /
          (1 - (heat w B) ^ (2 * K)) =
        (w - 1) * contrastTransfer B w := by
    intro tc B hrad hB1 hBM
    have hq2_lt : ‖(heat w B) ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (heat_contraction B hB1 w hw) (by norm_num)
    have hq2_ne : (1 : ℂ) - (heat w B) ^ 2 ≠ 0 :=
      sub_ne_zero.mpr fun he => hq2_lt.ne (by rw [← he, norm_one])
    have hq2K_lt : ‖(heat w B) ^ (2 * K)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (heat_contraction B hB1 w hw) (by omega)
    have hq2K_ne : (1 : ℂ) - (heat w B) ^ (2 * K) ≠ 0 :=
      sub_ne_zero.mpr fun he => hq2K_lt.ne (by rw [← he, norm_one])
    have hBM' : (tailRadix tc 0).val ^ (2 * K) ≤ M := by rwa [hrad]
    have heq := weightedAdjacentCutoff_fullMoebius_eq tc 0 K hBM' w
    rw [hrad] at heq
    rw [heq, finiteContrastTransfer_eq_damped B K hq2_ne]
    field_simp [hq2K_ne]
  have hc2 := hchan halfTurnClock 2 tailRadix_halfTurnClock_zero (by change 1 < (2 : ℕ); norm_num)
    (h23.trans hM)
  have hc3 := hchan primeThreeClock 3 tailRadix_primeThreeClock_zero (by change 1 < (3 : ℕ); norm_num) hM
  change weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) halfTurnClock 0 (2 ^ (2 * K)) w /
      (1 - (heat w 2) ^ (2 * K)) = (w - 1) * contrastTransfer 2 w at hc2
  change weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) primeThreeClock 0 (3 ^ (2 * K)) w /
      (1 - (heat w 3) ^ (2 * K)) = (w - 1) * contrastTransfer 3 w at hc3
  unfold weightedAlignedReconstructed
  rw [hc2, hc3]
  have hmass : conj (contrastTransfer 2 w) * contrastTransfer 2 w +
      conj (contrastTransfer 3 w) * contrastTransfer 3 w = (twoPrimeTransferMass w : ℂ) := by
    change _ = ((Complex.normSq (contrastTransfer 2 w) +
      Complex.normSq (contrastTransfer 3 w) : ℝ) : ℂ)
    rw [Complex.ofReal_add, ← Complex.mul_conj, ← Complex.mul_conj]; ring
  field_simp [hm_ne]
  linear_combination (w - 1) * hmass

/-- Short-shell Möbius tail `M < d ≤ 9^K` complementing the intrinsic `M`-truncated Möbius shell
reading inside `w - 1`. -/
def intrinsicMoebiusTail (M K : ℕ) (w : ℂ) : ℂ :=
  weightedAlignedReconstructed (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) K w -
    weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K w

/-- **Exact finite head–tail pole-unit conservation (`K ≥ 1`):** for every intermediate scale `M`
and every `w` with `Re w > 0`, the `M`-truncated intrinsic Möbius shell reading plus
`intrinsicMoebiusTail M K w` equals `w - 1` identically. -/
theorem exact_head_plus_moebiusTail_eq_sub_one (M : ℕ) {K : ℕ} (hK : 1 ≤ K)
    {w : ℂ} (hw : 0 < w.re) :
    weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K w +
      intrinsicMoebiusTail M K w = w - 1 := by
  unfold intrinsicMoebiusTail
  rw [add_sub_cancel, weightedAlignedReconstructed_fullMoebius_eq_sub_one hK le_rfl hw]

private theorem abs_moebiusReal_le_one (d : ℕ) : |moebiusReal d| ≤ 1 := by
  unfold moebiusReal
  by_cases hsq : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, Int.cast_pow, Int.cast_neg,
      Int.cast_one, abs_pow, abs_neg, abs_one, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero, abs_zero]
    exact zero_le_one

/-- **Exponential decay of the dyadic `2^K` intrinsic zero-threshold across `Re w > 1/2`:** for any
unit-bounded coefficients `|c d| ≤ 1` (in particular `moebiusReal`), `intrinsicDirichletZeroThreshold (2^K) c K w → 0`
as `K → ∞` whenever `1 / 2 < w.re`. -/
theorem tendsto_intrinsicZeroThreshold_two_pow_zero {c : ℕ → ℝ} (hc : ∀ d : ℕ, |c d| ≤ 1)
    {w : ℂ} (hw : 1 / 2 < w.re) :
    Tendsto (fun K : ℕ => intrinsicDirichletZeroThreshold (2 ^ K) c K w) atTop (𝓝 0) := by
  have hw0 : 0 < w.re := by linarith
  have hchan : ∀ (tc : ExceptionalTime) (B : ℕ), 2 ≤ B → (tailRadix tc 0).val = B →
      Tendsto (fun K : ℕ =>
        (∑ d ∈ Finset.Icc 1 (2 ^ K), |c d| * (d : ℝ) ^ (-w.re) *
          zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w) /
          (1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re))) atTop (𝓝 0) := by
    intro tc B hB2 hrad
    have hBr1 : (1 : ℝ) < B := by exact_mod_cast (by omega : 1 < B)
    have hBr0 : (0 : ℝ) < B := by positivity
    -- Uniform polynomial-in-`K` envelope times `2^K * 2^(-2 K w.re) = 2^(-K (2 w.re - 1))`.
    let A₁ : ℝ := (2 * Real.log B / Real.log 2) * (1 + ((B : ℝ) + 1)) * (2 : ℝ) ^ w.re
    let A₀ : ℝ := ((1 + zetaFreeDigitErrorConst tc 0 w) +
      ((B : ℝ) + 1) * (1 + zetaFreeDigitErrorConst tc 1 w)) * (2 : ℝ) ^ w.re
    have hnum_maj : ∀ K : ℕ, 1 ≤ K →
        ∑ d ∈ Finset.Icc 1 (2 ^ K), |c d| * (d : ℝ) ^ (-w.re) *
          zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w ≤
        (A₁ * (K : ℝ) + A₀) * Real.exp (-(K : ℝ) * ((2 * w.re - 1) * Real.log 2)) := by
      intro K hK1
      have hterm : ∀ d ∈ Finset.Icc 1 (2 ^ K),
          |c d| * (d : ℝ) ^ (-w.re) * zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w ≤
            (A₁ * (K : ℝ) + A₀) * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hd_pos : 0 < d := by omega
        have hdr_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
        set Q := B ^ (2 * K) / d
        have h2d_le : 2 * d ≤ B ^ (2 * K) := by
          have h1 : 2 * d ≤ 2 ^ (K + 1) := by rw [pow_succ']; exact Nat.mul_le_mul_left 2 hd.2
          have h2 : 2 ^ (K + 1) ≤ 2 ^ (2 * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
          exact (h1.trans h2).trans (Nat.pow_le_pow_left hB2 (2 * K))
        have hQ2 : 2 ≤ Q := (Nat.le_div_iff_mul_le hd_pos).mpr h2d_le
        have hQ1 : 1 ≤ Q := by omega
        have hQr_pos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ1
        have hB_le_2dQ : B ^ (2 * K) ≤ 2 * d * Q := by
          have hdiv : d * Q + B ^ (2 * K) % d = B ^ (2 * K) := Nat.div_add_mod (B ^ (2 * K)) d
          have hmod := Nat.mod_lt (B ^ (2 * K)) hd_pos
          have hQ_succ : d * Q + B ^ (2 * K) % d < d * (Q + 1) := by
            rw [Nat.mul_add, mul_one]
            exact Nat.add_lt_add_left hmod (d * Q)
          have hle1 : B ^ (2 * K) ≤ d * (Q + 1) := by omega
          have hle2 : d * (Q + 1) ≤ 2 * d * Q := by
            have : Q + 1 ≤ 2 * Q := by omega
            calc d * (Q + 1) ≤ d * (2 * Q) := Nat.mul_le_mul_left d this
              _ = 2 * d * Q := by ring
          exact hle1.trans hle2
        have hQ_ge_real : (2 : ℝ) ^ (2 * K) / (2 * (d : ℝ)) ≤ (Q : ℝ) := by
          have hpow_le : (2 : ℝ) ^ (2 * K) ≤ (B : ℝ) ^ (2 * K) := by
            exact_mod_cast Nat.pow_le_pow_left hB2 (2 * K)
          have hcast : (B : ℝ) ^ (2 * K) ≤ 2 * (d : ℝ) * (Q : ℝ) := by exact_mod_cast hB_le_2dQ
          exact (div_le_iff₀ (by positivity)).mpr (hpow_le.trans (by linarith))
        have hrpow_prod : (d : ℝ) ^ (-w.re) * (Q : ℝ) ^ (-w.re) ≤
            (2 : ℝ) ^ w.re * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
          have hbase_pos : 0 < (2 : ℝ) ^ (2 * K) / (2 * (d : ℝ)) := by positivity
          have hanti := Real.rpow_le_rpow_of_nonpos hbase_pos hQ_ge_real (by linarith : -w.re ≤ 0)
          calc (d : ℝ) ^ (-w.re) * (Q : ℝ) ^ (-w.re)
              ≤ (d : ℝ) ^ (-w.re) * ((2 : ℝ) ^ (2 * K) / (2 * (d : ℝ))) ^ (-w.re) :=
                mul_le_mul_of_nonneg_left hanti (Real.rpow_nonneg hdr_pos.le _)
            _ = (2 : ℝ) ^ w.re * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
                have h2_neg : (2 : ℝ) ^ (-w.re) = ((2 : ℝ) ^ w.re)⁻¹ :=
                  Real.rpow_neg zero_le_two w.re
                have h2_nz : (2 : ℝ) ^ w.re ≠ 0 := (Real.rpow_pos_of_pos zero_lt_two _).ne'
                have hd_nz : (d : ℝ) ^ (-w.re) ≠ 0 := (Real.rpow_pos_of_pos hdr_pos _).ne'
                rw [Real.div_rpow (by positivity) (by positivity),
                  Real.mul_rpow zero_le_two hdr_pos.le,
                  show ((2 : ℝ) ^ (2 * K)) ^ (-w.re) = (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]; push_cast; ring,
                  h2_neg]
                field_simp [hd_nz, h2_nz]
        -- Bound `logb` on refinements `0` and `1`.
        have hQ_le_B : (Q : ℝ) ≤ (B : ℝ) ^ (2 * K) := by
          exact_mod_cast Nat.div_le_self (B ^ (2 * K)) d
        have hlogQ : Real.log Q ≤ (2 * Real.log B) * (K : ℝ) := by
          calc Real.log Q ≤ Real.log ((B : ℝ) ^ (2 * K)) := Real.log_le_log hQr_pos hQ_le_B
            _ = (2 * Real.log B) * (K : ℝ) := by rw [Real.log_pow]; push_cast; ring
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hlogb_le : ∀ m : ℕ, 2 ≤ (tailRadix tc m).val →
            Real.logb (tailRadix tc m).val Q ≤ (2 * Real.log B / Real.log 2) * (K : ℝ) := by
          intro m hm2
          have hCm_ge : Real.log 2 ≤ Real.log (tailRadix tc m).val :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
          have hlogQ_nn : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ1)
          rw [Real.logb]
          calc Real.log Q / Real.log (tailRadix tc m).val
              ≤ Real.log Q / Real.log 2 := div_le_div_of_nonneg_left hlogQ_nn hlog2_pos hCm_ge
            _ ≤ ((2 * Real.log B) * (K : ℝ)) / Real.log 2 :=
                div_le_div_of_nonneg_right hlogQ hlog2_pos.le
            _ = (2 * Real.log B / Real.log 2) * (K : ℝ) := by ring
        have hm0_ge2 : 2 ≤ (tailRadix tc 0).val := by omega
        have hm1_ge2 : 2 ≤ (tailRadix tc 1).val := by
          have hs := tailRadix_succ tc 0
          have hv : (tailRadix tc 1).val = B ^ 2 := by rw [hs, PNat.pow_coe, hrad]
          rw [hv]; nlinarith
        have hconst_nn : ∀ m : ℕ, 0 ≤ 1 + zetaFreeDigitErrorConst tc m w := by
          intro m
          have hC1 : (1 : ℝ) < (tailRadix tc m).val := by exact_mod_cast radix_gt_one tc m
          unfold zetaFreeDigitErrorConst; dsimp only
          have h1 : 0 ≤ 2 * ((tailRadix tc m).val : ℝ) / (((tailRadix tc m).val - 1) * ‖1 - w‖) :=
            div_nonneg (by positivity) (mul_nonneg (sub_pos.mpr hC1).le (norm_nonneg _))
          have h2 : 0 ≤ 2 * ((tailRadix tc m).val : ℝ) / ((tailRadix tc m).val - 1) + 1 :=
            add_nonneg (div_nonneg (by positivity) (sub_pos.mpr hC1).le) zero_le_one
          have h3 : 0 ≤ (((tailRadix tc m).val : ℝ) / ((tailRadix tc m).val - 1)) *
              (2 : ℝ) ^ (w.re + 1) * (3 * ‖w‖ + ‖w * (w + 1)‖ / (4 * (w.re + 1))) :=
            mul_nonneg (mul_nonneg (div_nonneg (by positivity) (sub_pos.mpr hC1).le)
              (Real.rpow_nonneg zero_le_two _))
              (add_nonneg (by positivity) (div_nonneg (norm_nonneg _) (by linarith)))
          linarith
        have hadj_nn := zetaFreeAdjacentBound_nonneg_of_re_pos tc 0 hQ1 hw0
        have hc1_le : |c d| * (d : ℝ) ^ (-w.re) * zetaFreeAdjacentBound tc 0 Q w ≤
            (d : ℝ) ^ (-w.re) * zetaFreeAdjacentBound tc 0 Q w := by
          have := mul_le_mul_of_nonneg_right (hc d)
            (mul_nonneg (Real.rpow_nonneg hdr_pos.le (-w.re)) hadj_nn)
          linarith
        have hpoly_le : (Real.logb (tailRadix tc 0).val Q + 1 + zetaFreeDigitErrorConst tc 0 w) +
            (((tailRadix tc 0).val : ℝ) + 1) *
              (Real.logb (tailRadix tc 1).val Q + 1 + zetaFreeDigitErrorConst tc 1 w) ≤
            ((2 * Real.log B / Real.log 2) * (1 + ((B : ℝ) + 1))) * (K : ℝ) +
              ((1 + zetaFreeDigitErrorConst tc 0 w) +
                ((B : ℝ) + 1) * (1 + zetaFreeDigitErrorConst tc 1 w)) := by
          have hb0 := hlogb_le 0 hm0_ge2
          have hb1 := mul_le_mul_of_nonneg_left (hlogb_le 1 hm1_ge2)
            (by positivity : (0 : ℝ) ≤ (B : ℝ) + 1)
          rw [hrad] at hb0 ⊢
          have hexp_ring : ((2 * Real.log B / Real.log 2) * (1 + ((B : ℝ) + 1))) * (K : ℝ) =
              (2 * Real.log B / Real.log 2) * (K : ℝ) +
                ((B : ℝ) + 1) * ((2 * Real.log B / Real.log 2) * (K : ℝ)) := by ring
          linarith
        have hpoly_nn : 0 ≤ (Real.logb (tailRadix tc 0).val Q + 1 + zetaFreeDigitErrorConst tc 0 w) +
            (((tailRadix tc 0).val : ℝ) + 1) *
              (Real.logb (tailRadix tc 1).val Q + 1 + zetaFreeDigitErrorConst tc 1 w) := by
          have hl0 : 0 ≤ Real.logb (tailRadix tc 0).val Q :=
            Real.logb_nonneg (by exact_mod_cast radix_gt_one tc 0) (by exact_mod_cast hQ1)
          have hl1 : 0 ≤ Real.logb (tailRadix tc 1).val Q :=
            Real.logb_nonneg (by exact_mod_cast radix_gt_one tc 1) (by exact_mod_cast hQ1)
          nlinarith [hconst_nn 0, hconst_nn 1, show (0 : ℝ) ≤ (tailRadix tc 0).val by positivity]
        have hfact : (d : ℝ) ^ (-w.re) * zetaFreeAdjacentBound tc 0 Q w =
            ((Real.logb (tailRadix tc 0).val Q + 1 + zetaFreeDigitErrorConst tc 0 w) +
              (((tailRadix tc 0).val : ℝ) + 1) *
                (Real.logb (tailRadix tc 1).val Q + 1 + zetaFreeDigitErrorConst tc 1 w)) *
              ((d : ℝ) ^ (-w.re) * (Q : ℝ) ^ (-w.re)) := by
          unfold zetaFreeAdjacentBound zetaFreeTruncationBound
          ring
        calc |c d| * (d : ℝ) ^ (-w.re) * zetaFreeAdjacentBound tc 0 Q w
            ≤ (d : ℝ) ^ (-w.re) * zetaFreeAdjacentBound tc 0 Q w := hc1_le
          _ = _ := hfact
          _ ≤ (((2 * Real.log B / Real.log 2) * (1 + ((B : ℝ) + 1))) * (K : ℝ) +
                ((1 + zetaFreeDigitErrorConst tc 0 w) +
                  ((B : ℝ) + 1) * (1 + zetaFreeDigitErrorConst tc 1 w))) *
              ((2 : ℝ) ^ w.re * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re)) :=
                mul_le_mul hpoly_le hrpow_prod (by positivity)
                  (le_trans hpoly_nn hpoly_le)
          _ = (A₁ * (K : ℝ) + A₀) * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
                dsimp only [A₁, A₀]; ring
      have hcard : ((Finset.Icc 1 (2 ^ K)).card : ℝ) = (2 : ℝ) ^ K := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]; simp
      calc ∑ d ∈ Finset.Icc 1 (2 ^ K), |c d| * (d : ℝ) ^ (-w.re) *
              zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w
          ≤ ∑ _d ∈ Finset.Icc 1 (2 ^ K),
              (A₁ * (K : ℝ) + A₀) * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) :=
            Finset.sum_le_sum hterm
        _ = (2 : ℝ) ^ K * ((A₁ * (K : ℝ) + A₀) * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard]
        _ = (A₁ * (K : ℝ) + A₀) * Real.exp (-(K : ℝ) * ((2 * w.re - 1) * Real.log 2)) := by
            rw [← Real.rpow_natCast (2 : ℝ) K, Real.rpow_def_of_pos zero_lt_two,
              Real.rpow_def_of_pos zero_lt_two]
            have : (A₁ * (K : ℝ) + A₀) * Real.exp (-(K : ℝ) * ((2 * w.re - 1) * Real.log 2)) =
                Real.exp (Real.log 2 * (K : ℝ)) *
                  ((A₁ * (K : ℝ) + A₀) * Real.exp (Real.log 2 * (-(2 * K : ℝ) * w.re))) := by
              rw [mul_left_comm (Real.exp _), ← Real.exp_add]
              congr 2; ring
            exact this.symm
    -- Show `(A₁ * K + A₀) * exp(-K * α) → 0` for `α = (2 w.re - 1) log 2 > 0`.
    set α : ℝ := (2 * w.re - 1) * Real.log 2
    have hα : 0 < α := mul_pos (by linarith) (Real.log_pos (by norm_num))
    have hexp_K : Tendsto (fun K : ℕ => (K : ℝ) * Real.exp (-(K : ℝ) * α)) atTop (𝓝 0) := by
      have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hα)).const_mul (1 / α)
      rw [mul_zero] at h
      refine h.congr fun K => ?_
      dsimp only [Function.comp_apply]
      rw [pow_one, show -((K : ℝ) * α) = -(K : ℝ) * α by ring]
      field_simp [hα.ne']
    have hexp_1 : Tendsto (fun K : ℕ => Real.exp (-(K : ℝ) * α)) atTop (𝓝 0) := by
      refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hα)).congr fun K => ?_
      dsimp only [Function.comp_apply]; congr 1; ring
    have hmaj0 : Tendsto (fun K : ℕ => (A₁ * (K : ℝ) + A₀) * Real.exp (-(K : ℝ) * α))
        atTop (𝓝 0) := by
      have h := (hexp_K.const_mul A₁).add (hexp_1.const_mul A₀)
      rw [mul_zero, mul_zero, add_zero] at h
      exact h.congr fun K => by ring
    have hsum0 : Tendsto (fun K : ℕ =>
        ∑ d ∈ Finset.Icc 1 (2 ^ K), |c d| * (d : ℝ) ^ (-w.re) *
          zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hmaj0
      · filter_upwards [eventually_ge_atTop 1] with K hK1
        refine Finset.sum_nonneg fun d hd => ?_
        rw [Finset.mem_Icc] at hd
        have hdiv1 : 1 ≤ B ^ (2 * K) / d := by
          have hle : d ≤ B ^ (2 * K) :=
            hd.2.trans ((Nat.pow_le_pow_right (by norm_num) (by omega : K ≤ 2 * K)).trans
              (Nat.pow_le_pow_left hB2 (2 * K)))
          exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [one_mul]; exact hle)
        exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
          (zetaFreeAdjacentBound_nonneg_of_re_pos tc 0 hdiv1 hw0)
      · filter_upwards [eventually_ge_atTop 1] with K hK1
        exact hnum_maj K hK1
    have hden1 : Tendsto (fun K : ℕ => 1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re)) atTop (𝓝 1) := by
      have hexp : Tendsto (fun K : ℕ => (K : ℝ) * (2 * w.re * Real.log B)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos (by linarith) (Real.log_pos hBr1))
      have hr0 : Tendsto (fun K : ℕ => (B : ℝ) ^ (-(2 * K : ℝ) * w.re)) atTop (𝓝 0) := by
        refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hexp).congr fun K => ?_
        dsimp only [Function.comp_apply]
        rw [Real.rpow_def_of_pos hBr0]; congr 1; ring
      simpa only [sub_zero] using tendsto_const_nhds.sub hr0
    have hdiv0 := hsum0.div hden1 one_ne_zero
    rw [zero_div] at hdiv0
    exact hdiv0.congr fun _ => rfl
  have hs2 := (hchan halfTurnClock 2 (by norm_num)
    (congrArg PNat.val tailRadix_halfTurnClock_zero)).const_mul ‖contrastTransfer 2 w‖
  have hs3 := (hchan primeThreeClock 3 (by norm_num)
    (congrArg PNat.val tailRadix_primeThreeClock_zero)).const_mul ‖contrastTransfer 3 w‖
  rw [mul_zero] at hs2 hs3
  have htot := (hs2.add hs3).div_const (twoPrimeTransferMass w)
  rw [add_zero, zero_div] at htot
  exact htot

/-- At any right-half-strip zero `ζ(w) = 0` (`1 / 2 < w.re`, `w ≠ 1`), the `2^K` intrinsic head
tends to `0` and the short-shell Möbius tail `intrinsicMoebiusTail (2^K) K w` is forced to converge
to `w - 1`. -/
theorem tendsto_intrinsicMoebiusTail_two_pow_of_zeta_eq_zero
    {w : ℂ} (hw : 1 / 2 < w.re) (hw1 : w ≠ 1) (hζ : riemannZeta w = 0) :
    Tendsto (fun K : ℕ => intrinsicMoebiusTail (2 ^ K) K w) atTop (𝓝 (w - 1)) := by
  have hw0 : 0 < w.re := by linarith
  have hhead0 : Tendsto (fun K : ℕ =>
      weightedAlignedReconstructed (dirichletSurgWeight (2 ^ K) moebiusReal) K w)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (tendsto_intrinsicZeroThreshold_two_pow_zero abs_moebiusReal_le_one hw)
    filter_upwards [eventually_ge_atTop 1] with K hK1
    have hM : 2 ^ K ≤ 2 ^ (2 * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact norm_weightedAlignedReconstructed_le_intrinsicZeroThreshold_of_zeta_eq_zero
      (2 ^ K) moebiusReal hK1 hM hw0 hw1 hζ
  have hsub := (tendsto_const_nhds (x := w - 1)).sub hhead0
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK1
  have hid := exact_head_plus_moebiusTail_eq_sub_one (2 ^ K) hK1 hw0
  linear_combination -hid

/-- **Pointwise dyadic Möbius tail nonvanishing certificate:** if at `w` (`1 / 2 < w.re`, `w ≠ 1`)
the short-shell dyadic Möbius tail `intrinsicMoebiusTail (2^K) K w` falls infinitely often below
any threshold `r < ‖w - 1‖` (in particular `r = 169 / 2` whenever `169 / 2 < |w.im|`), then there is
a finite depth `K₀ ≥ 1` where the `2^K₀` intrinsic Möbius shell reading beats
`intrinsicDirichletZeroThreshold`, forcing `riemannZeta w ≠ 0`. -/
theorem zeta_ne_zero_of_dyadic_moebiusTail_subPole {w : ℂ} (hw : 1 / 2 < w.re) (hw1 : w ≠ 1)
    {r : ℝ} (hr : r < ‖w - 1‖)
    (hfreq : ∃ᶠ K : ℕ in atTop, ‖intrinsicMoebiusTail (2 ^ K) K w‖ ≤ r) :
    (∃ K₀ : ℕ, 1 ≤ K₀ ∧
      intrinsicDirichletZeroThreshold (2 ^ K₀) moebiusReal K₀ w <
        ‖weightedAlignedReconstructed (dirichletSurgWeight (2 ^ K₀) moebiusReal) K₀ w‖) ∧
    riemannZeta w ≠ 0 := by
  have hw0 : 0 < w.re := by linarith
  have hε : 0 < ‖w - 1‖ - r := sub_pos.mpr hr
  have hthr := tendsto_intrinsicZeroThreshold_two_pow_zero abs_moebiusReal_le_one hw
  have hev := (eventually_ge_atTop 1).and (hthr.eventually (Iio_mem_nhds hε))
  obtain ⟨K₀, htail_le, hK1, hthr_lt⟩ := (hfreq.and_eventually hev).exists
  have hid := exact_head_plus_moebiusTail_eq_sub_one (2 ^ K₀) hK1 hw0
  have htri : ‖w - 1‖ ≤
      ‖weightedAlignedReconstructed (dirichletSurgWeight (2 ^ K₀) moebiusReal) K₀ w‖ +
        ‖intrinsicMoebiusTail (2 ^ K₀) K₀ w‖ := by
    rw [← hid]
    exact norm_add_le _ _
  have hmarg : intrinsicDirichletZeroThreshold (2 ^ K₀) moebiusReal K₀ w <
      ‖weightedAlignedReconstructed (dirichletSurgWeight (2 ^ K₀) moebiusReal) K₀ w‖ := by
    linarith
  have hM : 2 ^ K₀ ≤ 2 ^ (2 * K₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨⟨K₀, hK1, hmarg⟩,
    (intrinsicDirichlet_margin_forces_zeta_ne_zero (2 ^ K₀) moebiusReal hK1 hM hw0 hw1 hmarg).1⟩

/-- Unconditional reduction of `RiemannHypothesis` to bounding the dyadic short-shell Möbius tail
by `169 / 2` along a sequence of depths `K → ∞` on `{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}`. -/
theorem rh_of_dyadic_moebiusTail_le_eightyFour_and_half
    (htail : ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| →
      ∃ᶠ K : ℕ in atTop, ‖intrinsicMoebiusTail (2 ^ K) K w‖ ≤ 169 / 2) :
    RiemannHypothesis := by
  rw [rh_iff_zetaFree_margin_above_eightyFour_and_half halfTurnClock 0]
  intro w hlo hhi him
  have hw0 : 0 < w.re := by linarith
  have hw_lt1 : w.re < 1 := by linarith
  have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
  have him_le : |w.im| ≤ ‖w - 1‖ := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (w - 1)
  have hne := (zeta_ne_zero_of_dyadic_moebiusTail_subPole hlo hw1 (him.trans_le him_le)
    (htail w hlo hhi him)).2
  exact (exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw0 hw1).mpr hne

/-- **Exact residual `RH` equivalence via intrinsic Möbius shell margins and `intrinsicMoebiusTail`:**
above Bohman height `169 / 2 = 84.5`, `RiemannHypothesis` is unconditionally equivalent both to
having a finite intrinsic Möbius shell margin (`M ≤ 4^K₀`) at every remaining point in
`{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}` and to `intrinsicMoebiusTail M K₀ w` staying outside
the `intrinsicDirichletZeroThreshold` ball around `w - 1`. -/
theorem rh_iff_intrinsic_moebius_margin_above_eightyFour_and_half :
    (RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| →
        ∃ M K₀ : ℕ, 1 ≤ K₀ ∧ M ≤ 2 ^ (2 * K₀) ∧
          intrinsicDirichletZeroThreshold M moebiusReal K₀ w <
            ‖weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K₀ w‖) ∧
    (RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| →
        ∃ M K₀ : ℕ, 1 ≤ K₀ ∧ M ≤ 2 ^ (2 * K₀) ∧
          intrinsicDirichletZeroThreshold M moebiusReal K₀ w <
            ‖(w - 1) - intrinsicMoebiusTail M K₀ w‖) := by
  have h1 : RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| →
        ∃ M K₀ : ℕ, 1 ≤ K₀ ∧ M ≤ 2 ^ (2 * K₀) ∧
          intrinsicDirichletZeroThreshold M moebiusReal K₀ w <
            ‖weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K₀ w‖ := by
    rw [rh_iff_zetaFree_margin_above_eightyFour_and_half halfTurnClock 0]
    refine forall_congr' fun w => imp_congr_right fun hlo => imp_congr_right fun hhi =>
      imp_congr_right fun _ => ?_
    have hw0 : 0 < w.re := by linarith
    have hw_lt1 : w.re < 1 := by linarith
    have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
    rw [exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw0 hw1]
    constructor
    · intro hzeta
      have hQ1 : dirichletSurgPoly 1 moebiusReal w = 1 := by simp [dirichletSurgPoly, moebiusReal]
      have hlim := (tendsto_weightedAlignedReconstructed_dirichletSurgWeight 1 moebiusReal hw0).norm
      rw [hQ1, one_mul] at hlim
      have hZ_pos : 0 < ‖_root_.RHTower.zetaPoleUnit w‖ := by
        rw [_root_.RHTower.zetaPoleUnit_of_ne hw1]
        exact norm_pos_iff.mpr (mul_ne_zero (sub_ne_zero.mpr hw1) hzeta)
      have hthr := tendsto_intrinsicDirichletZeroThreshold_zero 1 moebiusReal hw0
      obtain ⟨K₀, ⟨hK1, hthr_lt⟩, hw_gt⟩ :=
        (((eventually_ge_atTop 1).and (hthr.eventually (Iio_mem_nhds (half_pos hZ_pos)))).and
          (hlim.eventually (Ioi_mem_nhds (half_lt_self hZ_pos)))).exists
      have h1_le : 1 ≤ 2 ^ (2 * K₀) := one_le_pow₀ (by norm_num)
      exact ⟨1, K₀, hK1, h1_le, hthr_lt.trans hw_gt⟩
    · rintro ⟨M, K₀, hK1, hM, hmarg⟩
      exact (intrinsicDirichlet_margin_forces_zeta_ne_zero M moebiusReal hK1 hM hw0 hw1 hmarg).1
  refine ⟨h1, h1.trans ?_⟩
  refine forall_congr' fun w => imp_congr_right fun hlo => imp_congr_right fun _ =>
    imp_congr_right fun _ => exists_congr fun M => exists_congr fun K₀ =>
      and_congr_right fun hK1 => and_congr_right fun _ => ?_
  have hw0 : 0 < w.re := by linarith
  have heq : weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K₀ w =
      (w - 1) - intrinsicMoebiusTail M K₀ w := by
    linear_combination exact_head_plus_moebiusTail_eq_sub_one M hK1 hw0
  rw [heq]

/-! ### Part 4: Unconditional integer-ray dilation elimination below `84.5 k` -/

/-- **Unconditional integer-ray dilation elimination below `84.5 k` (`k ≥ 2`):** while
`riemannZeta_div_nat_ne_zero_of_seven_le` requires `k ≥ 7` globally, for **every** `k ≥ 2` and every
open-strip point `0 < Re w < 1` with `|Im w| ≤ (169 / 2) k` (closing `k ∈ {2, 3, 4, 5, 6}` up to
height `507`), `w / k` has `0 < Re (w / k) < 1 / 2` and `|Im (w / k)| ≤ 169 / 2`, so `ζ(w / k) ≠ 0`
unconditionally and its reflected right-strip partner `1 - conj (w / k)` carries a strict cutoff
margin on every prime clock. -/
theorem strip_div_nat_zeta_ne_zero_below_scaled_eightyFour_and_half {k : ℕ} (hk : 2 ≤ k)
    {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ (169 / 2 : ℝ) * (k : ℝ)) :
    let z := w / (k : ℂ)
    let wRefl := 1 - conj z
    riemannZeta z ≠ 0 ∧
      1 / 2 < wRefl.re ∧ wRefl.re < 1 ∧
      riemannZeta wRefl ≠ 0 ∧
      ∀ (t : ExceptionalTime) (j : ℕ),
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ wRefl < ‖renormalizedCutoff t j X₀ wRefl‖ := by
  dsimp only
  set z := w / (k : ℂ)
  set wRefl := 1 - conj z
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hz_re : z.re = w.re / (k : ℝ) := by
    have hkeq : z = w * (((k : ℝ)⁻¹ : ℝ) : ℂ) := by
      dsimp only [z]
      rw [Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
    rw [hkeq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  have hz_im : z.im = w.im / (k : ℝ) := by
    have hkeq : z = w * (((k : ℝ)⁻¹ : ℝ) : ℂ) := by
      dsimp only [z]
      rw [Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
    rw [hkeq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, div_eq_mul_inv]
  have hz_re_pos : 0 < z.re := by rw [hz_re]; exact div_pos h0 hk_pos
  have hz_re_lt_half : z.re < 1 / 2 := by
    rw [hz_re, div_lt_iff₀ hk_pos]; linarith
  have hz_re_lt1 : z.re < 1 := by linarith
  have hz_im_le : |z.im| ≤ 169 / 2 := by
    rw [hz_im, abs_div, abs_of_pos hk_pos, div_le_iff₀ hk_pos]; exact him
  have hz_ne1 : z ≠ 1 := fun he => hz_re_lt1.ne (by rw [he, Complex.one_re])
  have hz_zeta : riemannZeta z ≠ 0 := by
    intro hζ
    have hxi : _root_.RHTower.xi z = 0 := (_root_.RHTower.xi_eq_zero_iff hz_re_pos hz_ne1).mpr hζ
    have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
      VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_oneHundredSixtyNine_halves
      hxi hz_re_pos hz_re_lt1 hz_re_lt_half.ne
    linarith
  have hwR_re : wRefl.re = 1 - z.re := by
    simp only [wRefl, Complex.sub_re, Complex.one_re, Complex.conj_re]
  have hwR_im : |wRefl.im| ≤ 169 / 2 := by
    have : wRefl.im = z.im := by
      simp only [wRefl, Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]
    rwa [this]
  have hwR_lo : 1 / 2 < wRefl.re := by linarith
  have hwR_hi : wRefl.re < 1 := by linarith
  have hwR_zeta : riemannZeta wRefl ≠ 0 :=
    riemannZeta_ne_zero_of_strip_abs_im_le_eightyFour_and_half hwR_lo hwR_hi hwR_im
  exact ⟨hz_zeta, hwR_lo, hwR_hi, hwR_zeta, fun t j =>
    exists_zetaFree_margin_of_abs_im_le_eightyFour_and_half t j hwR_lo hwR_hi hwR_im⟩

#print axioms external_mollifier_margin_iff_unmollified
#print axioms eulerSieve_margin_iff_unmollified
#print axioms norm_weightedAlignedReconstructed_le_intrinsicZeroThreshold_of_zeta_eq_zero
#print axioms intrinsicDirichlet_margin_forces_zeta_ne_zero
#print axioms moebius_powerSaving_intrinsic_linear_margin
#print axioms weightedAdjacentCutoff_fullMoebius_eq
#print axioms weightedAlignedReconstructed_fullMoebius_eq_sub_one
#print axioms exact_head_plus_moebiusTail_eq_sub_one
#print axioms tendsto_intrinsicZeroThreshold_two_pow_zero
#print axioms tendsto_intrinsicMoebiusTail_two_pow_of_zeta_eq_zero
#print axioms zeta_ne_zero_of_dyadic_moebiusTail_subPole
#print axioms rh_of_dyadic_moebiusTail_le_eightyFour_and_half
#print axioms rh_iff_intrinsic_moebius_margin_above_eightyFour_and_half
#print axioms strip_div_nat_zeta_ne_zero_below_scaled_eightyFour_and_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
