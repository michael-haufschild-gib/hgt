import GaloisForLFunctions.RHTower.GaussHodgeWeilSymmetryInsufficiency
import GaloisForLFunctions.PNTPlus.ZetaBounds

/-!
# Arithmetic input enters the deviation moment: the zero-free gap

The symmetry-insufficiency theorem shows a Weil-positivity producer must consume the Euler
product.  This module feeds the first formalized Euler-product positivity in the corpus — the
classical zero-free region of `PNTPlus` (proved from the `3-4-1` inequality, i.e. from
`Λ ≥ 0`) — into the deviation moment of the Weil form.

* `zeta_zero_of_xi_zero` — divisor transfer: every `xi` zero is a `riemannZeta` zero.
* `exists_xi_deviation_gap_high` — at heights `|Im ρ| > 3` the deviation of every zero from
  the critical line is bounded away from the strip wall by the de la Vallée-Poussin margin:
  `(Re ρ − 1/2)² ≤ 1/4 − A/(2 log⁹|Im ρ|)`, using the region on both sides of the line via the
  functional equation.
* `exists_xi_deviation_gap_low` — at heights `|Im ρ| ≤ 3` a single uniform gap `δ > 0` bounds
  `(Re ρ − 1/2)² ≤ 1/4 − δ`.
* `exists_arithmetic_gap_lowSupported` — **the producer fragment**: for tests whose divided
  differences are supported at height ≤ 3, the deviation-moment lower bound strictly improves
  the bare strip constant: `Re W(F,F) ≥ Σ‖even‖² − (1/4 − δ)·Σ‖ΔF‖²` with an arithmetic
  `δ > 0`.

This is the first point in the lane where the Euler product quantitatively improves the Weil
form.  The honest calibration: the region pushes zeros away from the strip *walls*, so it
shrinks the deviation weight below `1/4`; positivity itself needs the weight pushed to `0`,
which is RH.  The gap between `1/4 − δ` and `0` is the exact analytic distance between the
`3-4-1` positivity and the positivity the socket demands.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every zero of the completed `xi` is a zero of `riemannZeta`. -/
theorem zeta_zero_of_xi_zero {ρ : ℂ} (hρ : xi ρ = 0) : riemannZeta ρ = 0 := by
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hρ
  have hne1 : ρ ≠ 1 := by
    intro hcon
    rw [hcon] at h1
    simp at h1
  exact (xi_eq_zero_iff h0 hne1).mp hρ

/-- **The high-height deviation gap.**  Above height `3` the classical zero-free region,
applied on both sides of the critical line through the functional equation, bounds the squared
deviation of every `xi` zero strictly below the strip constant by the de la Vallée-Poussin
margin. -/
theorem exists_xi_deviation_gap_high :
    ∃ A : ℝ, A ∈ Set.Ioc 0 (1 / 2) ∧ ∀ ρ : ℂ, xi ρ = 0 → 3 < |ρ.im| →
      (ρ.re - 1 / 2) ^ (2 : ℕ) ≤ 1 / 4 - A / Real.log |ρ.im| ^ (9 : ℕ) / 2 := by
  obtain ⟨A, hA, hfree⟩ := ZetaZeroFree
  refine ⟨A, hA, ?_⟩
  intro ρ hρ ht
  obtain ⟨hre0, hre1⟩ := xi_zero_re_mem_open_unit hρ
  have hζ : riemannZeta ρ = 0 := zeta_zero_of_xi_zero hρ
  have hlog : 1 < Real.log |ρ.im| := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hpow : 1 ≤ Real.log |ρ.im| ^ (9 : ℕ) := one_le_pow₀ hlog.le
  have hεpos : 0 < A / Real.log |ρ.im| ^ (9 : ℕ) := div_pos hA.1 (by linarith)
  have hεle : A / Real.log |ρ.im| ^ (9 : ℕ) ≤ 1 / 2 :=
    le_trans (div_le_self hA.1.le hpow) hA.2
  have hupper : ρ.re < 1 - A / Real.log |ρ.im| ^ (9 : ℕ) := by
    by_contra hge
    exact hfree ρ.re ρ.im ht ⟨not_lt.mp hge, hre1⟩
      (by rw [Complex.re_add_im]; exact hζ)
  have hlower : A / Real.log |ρ.im| ^ (9 : ℕ) < ρ.re := by
    by_contra hge
    have hxi1 : xi (1 - ρ) = 0 := by rw [xi_one_sub]; exact hρ
    have hζ1 : riemannZeta (1 - ρ) = 0 := zeta_zero_of_xi_zero hxi1
    have him1 : (1 - ρ).im = -ρ.im := by simp [Complex.sub_im]
    have hre1' : (1 - ρ).re = 1 - ρ.re := by simp [Complex.sub_re]
    have habs : 3 < |(1 - ρ).im| := by rw [him1, abs_neg]; exact ht
    have hlogeq : Real.log |(1 - ρ).im| = Real.log |ρ.im| := by rw [him1, abs_neg]
    apply hfree (1 - ρ).re (1 - ρ).im habs ⟨?_, ?_⟩
      (by rw [Complex.re_add_im]; exact hζ1)
    · rw [hre1', hlogeq]
      linarith [not_lt.mp hge]
    · rw [hre1']
      linarith
  have hsq : (ρ.re - 1 / 2) ^ (2 : ℕ) ≤ (1 / 2 - A / Real.log |ρ.im| ^ (9 : ℕ)) ^ (2 : ℕ) :=
    sq_le_sq' (by linarith) (by linarith)
  nlinarith [hεpos, hεle]

/-- **The low-height deviation gap.**  Below height `3` the zero-free box supplies one uniform
arithmetic gap between the squared deviations and the strip constant. -/
theorem exists_xi_deviation_gap_low :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℂ, xi ρ = 0 → |ρ.im| ≤ 3 →
      (ρ.re - 1 / 2) ^ (2 : ℕ) ≤ 1 / 4 - δ := by
  obtain ⟨σ₁, hσ₁, hbox⟩ := ZetaNoZerosInBox 3
  set σ₂ : ℝ := max σ₁ (3 / 4) with hσ₂def
  have hσ₂lt : σ₂ < 1 := by
    rw [hσ₂def]
    exact max_lt hσ₁ (by norm_num)
  have hσ₂ge : (3 / 4 : ℝ) ≤ σ₂ := le_max_right _ _
  refine ⟨1 / 4 - (σ₂ - 1 / 2) ^ (2 : ℕ), by nlinarith, ?_⟩
  intro ρ hρ ht
  have hζ : riemannZeta ρ = 0 := zeta_zero_of_xi_zero hρ
  have hupper : ρ.re < σ₂ := by
    by_contra hge
    exact hbox ρ.im ht ρ.re (le_trans (le_max_left _ _) (not_lt.mp hge))
      (by rw [Complex.re_add_im]; exact hζ)
  have hlower : 1 - σ₂ < ρ.re := by
    by_contra hge
    have hxi1 : xi (1 - ρ) = 0 := by rw [xi_one_sub]; exact hρ
    have hζ1 : riemannZeta (1 - ρ) = 0 := zeta_zero_of_xi_zero hxi1
    have him1 : (1 - ρ).im = -ρ.im := by simp [Complex.sub_im]
    have hre1' : (1 - ρ).re = 1 - ρ.re := by simp [Complex.sub_re]
    have habs : |(1 - ρ).im| ≤ 3 := by rw [him1, abs_neg]; exact ht
    apply hbox (1 - ρ).im habs (1 - ρ).re ?_
      (by rw [Complex.re_add_im]; exact hζ1)
    have hσ₁le : σ₁ ≤ σ₂ := by rw [hσ₂def]; exact le_max_left _ _
    rw [hre1']
    linarith [not_lt.mp hge]
  have hsq : (ρ.re - 1 / 2) ^ (2 : ℕ) ≤ (σ₂ - 1 / 2) ^ (2 : ℕ) :=
    sq_le_sq' (by linarith) (by linarith)
  linarith

/-! ## The gaps in divisor coordinates -/

/-- The real part of a centered spectral point is the ordinate of the underlying zero. -/
theorem xiSpectralPoint_re (q : XiZeroCopy) :
    (xiSpectralPoint q).re = ((q.1 : ℂ)).im := by
  rw [xiSpectralPoint_eq_support, xiSpectralPointSupport]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]

/-- The squared deviation of a divisor copy in classical coordinates. -/
theorem xiSpectralPoint_im_sq (q : XiZeroCopy) :
    (xiSpectralPoint q).im ^ (2 : ℕ) = (((q.1 : ℂ)).re - 1 / 2) ^ (2 : ℕ) := by
  rw [xiSpectralPoint_im]
  ring

/-- The low-height deviation gap on the multiplicity-exact divisor. -/
theorem exists_xiSpectralPoint_deviation_gap_low :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : XiZeroCopy, |(xiSpectralPoint q).re| ≤ 3 →
      (xiSpectralPoint q).im ^ (2 : ℕ) ≤ 1 / 4 - δ := by
  obtain ⟨δ, hδ, hbound⟩ := exists_xi_deviation_gap_low
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have him : |((q.1 : ℂ)).im| ≤ 3 := by rwa [← xiSpectralPoint_re]
  rw [xiSpectralPoint_im_sq]
  exact hbound _ (xi_zeroCopy_eq_zero q) him

/-- The high-height deviation gap on the multiplicity-exact divisor. -/
theorem exists_xiSpectralPoint_deviation_gap_high :
    ∃ A : ℝ, A ∈ Set.Ioc 0 (1 / 2) ∧ ∀ q : XiZeroCopy, 3 < |(xiSpectralPoint q).re| →
      (xiSpectralPoint q).im ^ (2 : ℕ) ≤
        1 / 4 - A / Real.log |(xiSpectralPoint q).re| ^ (9 : ℕ) / 2 := by
  obtain ⟨A, hA, hbound⟩ := exists_xi_deviation_gap_high
  refine ⟨A, hA, ?_⟩
  intro q hq
  have him : 3 < |((q.1 : ℂ)).im| := by rwa [← xiSpectralPoint_re]
  rw [xiSpectralPoint_im_sq, xiSpectralPoint_re]
  exact hbound _ (xi_zeroCopy_eq_zero q) him

/-! ## The producer fragment: arithmetic strictly improves the strip bound -/

/-- **Arithmetic strictly improves the deviation-moment bound.**  For every test whose divided
differences are supported at height at most `3`, the diagonal Weil value obeys the strip lower
bound with the constant improved from `1/4` to `1/4 − δ` for one uniform arithmetic `δ > 0`
sourced from the Euler product through the zero-free box.  This is the first quantitative entry
of arithmetic positivity into the Weil form; closing the remaining gap from `1/4 − δ` to `0`
is RH. -/
theorem exists_arithmetic_gap_lowSupported :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
      Summable (fun q : XiZeroCopy =>
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ (2 : ℕ)) →
      (∀ q : XiZeroCopy, 3 < |(xiSpectralPoint q).re| →
        dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q) = 0) →
      (∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ (2 : ℕ)) -
          (1 / 4 - δ) * ∑' q : XiZeroCopy,
            ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ (2 : ℕ) ≤
        (xiWeilPolarization F F).re := by
  obtain ⟨δ, hδ, hgap⟩ := exists_xiSpectralPoint_deviation_gap_low
  refine ⟨δ, hδ, ?_⟩
  intro F hF hD hsupp
  rw [xiWeilPolarization_re_eq_deviation_moment hF]
  have hpt : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ (2 : ℕ) *
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ (2 : ℕ) ≤
        (1 / 4 - δ) *
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ (2 : ℕ) := by
    intro q
    by_cases hq : 3 < |(xiSpectralPoint q).re|
    · rw [hsupp q hq]
      simp
    · exact mul_le_mul_of_nonneg_right (hgap q (not_lt.mp hq)) (sq_nonneg _)
  have hmoment : (∑' q : XiZeroCopy, (xiSpectralPoint q).im ^ (2 : ℕ) *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ (2 : ℕ)) ≤
      (1 / 4 - δ) * ∑' q : XiZeroCopy,
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ (2 : ℕ) := by
    rw [← tsum_mul_left]
    exact (deviation_dslope_energy_summable hF).tsum_le_tsum hpt (hD.mul_left _)
  linarith

end

end RHTower
