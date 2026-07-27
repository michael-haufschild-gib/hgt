import GaloisForLFunctions.RHTower.MobiusCausalFarFieldBound

/-!
# The mid-range bound for the parameter derivative

Between the origin ball and the far field the boundary line meets a compact rectangle

```text
S = {1 ≤ Re s ≤ 1+2ω₀, δ ≤ |Im s| ≤ 9}
```

on which `ζ` has no zero and no pole.  Continuity therefore bounds `ζ`, `ζ′` and `1/ζ` there, and
the parameter derivative of the coupled causal multiplier is bounded on the corresponding segment
of the boundary line, uniformly in `0 < ω ≤ ω₀`.
-/

open Filter Topology Complex Metric

namespace RHTower

noncomputable section

/-- The compact mid-range rectangle. -/
def midRangeSet (ω₀ δ : ℝ) : Set ℂ :=
  {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 1 + 2 * ω₀ ∧ δ ≤ |s.im| ∧ |s.im| ≤ 9}

theorem isCompact_midRangeSet (ω₀ δ : ℝ) : IsCompact (midRangeSet ω₀ δ) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h1 : IsClosed {s : ℂ | 1 ≤ s.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {s : ℂ | s.re ≤ 1 + 2 * ω₀} :=
      isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {s : ℂ | δ ≤ |s.im|} :=
      isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)
    have h4 : IsClosed {s : ℂ | |s.im| ≤ 9} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    have hset : midRangeSet ω₀ δ
        = {s : ℂ | 1 ≤ s.re} ∩ ({s : ℂ | s.re ≤ 1 + 2 * ω₀} ∩
          ({s : ℂ | δ ≤ |s.im|} ∩ {s : ℂ | |s.im| ≤ 9})) := by
      ext s
      simp only [midRangeSet, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hset]
    exact h1.inter (h2.inter (h3.inter h4))
  · apply Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (1 + 2 * ω₀) + 9 + 9))
    rintro s ⟨hs1, hs2, -, hs4⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre : |s.re| ≤ 1 + 2 * ω₀ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re)]
      linarith
    linarith

theorem midRangeSet_ne_one {ω₀ δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : s ∈ midRangeSet ω₀ δ) :
    s ≠ 1 := by
  intro h
  have him : |s.im| = 0 := by rw [h]; simp
  have := hs.2.2.1
  rw [him] at this
  linarith

theorem riemannZeta_ne_zero_midRangeSet {ω₀ δ : ℝ} {s : ℂ}
    (hs : s ∈ midRangeSet ω₀ δ) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs.1

/-- **The mid-range bound.** -/
theorem exists_mid_range_bound {ω₀ δ : ℝ} (hω₀ : 0 < ω₀) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ →
      ‖(riemannZeta (1 + 2 * (ω : ℂ)) +
          2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
        ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2‖ ≤ 3 →
      ∀ τ : ℝ, δ ≤ |τ| → |τ| ≤ 9 →
        ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ≤ C := by
  have hcomp := isCompact_midRangeSet ω₀ δ
  -- continuity of zeta, its derivative and its reciprocal on the rectangle
  have hana : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    have hdiffOn : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
      intro s hs
      exact (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt
    exact hdiffOn.analyticOnNhd isOpen_compl_singleton
  have hmemc : ∀ s ∈ midRangeSet ω₀ δ, s ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro s hs
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using midRangeSet_ne_one hδ hs
  have hζcont : ContinuousOn riemannZeta (midRangeSet ω₀ δ) := by
    intro s hs
    exact ((hana s (hmemc s hs)).continuousAt).continuousWithinAt
  have hζ'cont : ContinuousOn (deriv riemannZeta) (midRangeSet ω₀ δ) := by
    intro s hs
    exact (((hana s (hmemc s hs)).deriv).continuousAt).continuousWithinAt
  have hinvcont : ContinuousOn (fun s : ℂ => (riemannZeta s)⁻¹) (midRangeSet ω₀ δ) :=
    hζcont.inv₀ (fun s hs => riemannZeta_ne_zero_midRangeSet hs)
  obtain ⟨C1', hC1'⟩ := hcomp.exists_bound_of_continuousOn hinvcont
  obtain ⟨C2', hC2'⟩ := hcomp.exists_bound_of_continuousOn hζ'cont
  obtain ⟨C3', hC3'⟩ := hcomp.exists_bound_of_continuousOn hζcont
  set C1 : ℝ := max C1' 0 with hC1def
  set C2 : ℝ := max C2' 0 with hC2def
  set C3 : ℝ := max C3' 0 with hC3def
  have hC1 : ∀ x ∈ midRangeSet ω₀ δ, ‖(riemannZeta x)⁻¹‖ ≤ C1 :=
    fun x hx => le_trans (hC1' x hx) (le_max_left _ _)
  have hC2 : ∀ x ∈ midRangeSet ω₀ δ, ‖deriv riemannZeta x‖ ≤ C2 :=
    fun x hx => le_trans (hC2' x hx) (le_max_left _ _)
  have hC3 : ∀ x ∈ midRangeSet ω₀ δ, ‖riemannZeta x‖ ≤ C3 :=
    fun x hx => le_trans (hC3' x hx) (le_max_left _ _)
  have hC10 : (0 : ℝ) ≤ C1 := le_max_right _ _
  have hC20 : (0 : ℝ) ≤ C2 := le_max_right _ _
  have hC30 : (0 : ℝ) ≤ C3 := le_max_right _ _
  refine ⟨C3 * C1 * (1 + 2 * (C2 * C1)) + 3 / δ, ?_, ?_⟩
  · have h1 : 0 ≤ C3 * C1 * (1 + 2 * (C2 * C1)) := by positivity
    have h2 : 0 ≤ 3 / δ := by positivity
    linarith
  · intro ω hω hωle hK τ hτδ hτ9
    set z : ℂ := (τ : ℂ) * Complex.I with hzdef
    have hzim : z.im = τ := by rw [hzdef]; simp
    have hznorm : ‖z‖ = |τ| := by
      rw [hzdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hτ0 : (0 : ℝ) < |τ| := by linarith
    have hmem1 : (1 : ℂ) + z ∈ midRangeSet ω₀ δ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hzdef]; simp
      · rw [hzdef]; simp; linarith
      · have : ((1 : ℂ) + z).im = τ := by simp [Complex.add_im, hzim]
        rw [this]; exact hτδ
      · have : ((1 : ℂ) + z).im = τ := by simp [Complex.add_im, hzim]
        rw [this]; exact hτ9
    have hmem2 : (1 : ℂ) + 2 * (ω : ℂ) + z ∈ midRangeSet ω₀ δ := by
      have hre : ((1 : ℂ) + 2 * (ω : ℂ) + z).re = 1 + 2 * ω := by
        rw [hzdef]
        simp [Complex.add_re, Complex.mul_re]
      have him : ((1 : ℂ) + 2 * (ω : ℂ) + z).im = τ := by
        rw [hzdef]
        simp [Complex.add_im, Complex.mul_im]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hre]; linarith
      · rw [hre]; linarith
      · rw [him]; exact hτδ
      · rw [him]; exact hτ9
    -- the linear factor
    have hlin_lb1 : (1 : ℝ) ≤ ‖1 + (ω : ℂ) + z‖ := by
      have h1 : ((1 : ℂ) + (ω : ℂ) + z).re ≤ ‖1 + (ω : ℂ) + z‖ := Complex.re_le_norm _
      have h2 : ((1 : ℂ) + (ω : ℂ) + z).re = 1 + ω := by
        rw [hzdef]; simp [Complex.add_re]
      rw [h2] at h1
      linarith
    have hlinpos : (0 : ℝ) < ‖1 + (ω : ℂ) + z‖ := by linarith
    have hinvlin : ‖1 + (ω : ℂ) + z‖⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hlin_lb1
    have hb1 := hC3 _ hmem1
    have hb2 := hC1 _ hmem2
    have hb3 := hC2 _ hmem2
    have hC10' : (0 : ℝ) ≤ C1 := hC10
    -- the first factor
    have hfac : ‖riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z))‖
        ≤ C3 * C1 := by
      have hsplit : ‖riemannZeta (1 + z) /
          ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z))‖
          = ‖riemannZeta (1 + z)‖ * ‖1 + (ω : ℂ) + z‖⁻¹ *
            ‖(riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹‖ := by
        rw [norm_div, norm_mul, norm_inv, div_eq_mul_inv, mul_inv]
        ring
      rw [hsplit]
      have hstep : ‖riemannZeta (1 + z)‖ * ‖1 + (ω : ℂ) + z‖⁻¹ ≤ C3 * 1 :=
        mul_le_mul hb1 hinvlin (by positivity) hC30
      rw [mul_one] at hstep
      exact mul_le_mul hstep hb2 (norm_nonneg _) hC30
    -- the bracket
    have hbr : ‖-(1 / (1 + (ω : ℂ) + z)) -
        2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) / riemannZeta (1 + 2 * (ω : ℂ) + z)‖
        ≤ 1 + 2 * (C2 * C1) := by
      refine le_trans (norm_sub_le _ _) ?_
      have h1 : ‖-(1 / (1 + (ω : ℂ) + z))‖ ≤ 1 := by
        rw [norm_neg, norm_div, norm_one, div_le_one hlinpos]
        exact hlin_lb1
      have h2 : ‖2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) /
          riemannZeta (1 + 2 * (ω : ℂ) + z)‖ ≤ 2 * (C2 * C1) := by
        have hrw : 2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) /
            riemannZeta (1 + 2 * (ω : ℂ) + z)
            = 2 * (deriv riemannZeta (1 + 2 * (ω : ℂ) + z) *
              (riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹) := by
          rw [div_eq_mul_inv]
          ring
        rw [hrw, norm_mul, norm_mul]
        have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2n]
        have := mul_le_mul hb3 hb2 (norm_nonneg _) hC20
        linarith
      linarith
    -- the subtracted pole term
    have hpole : ‖1 / z * ((riemannZeta (1 + 2 * (ω : ℂ)) +
        2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
          ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2)‖ ≤ 3 / δ := by
      rw [norm_mul, norm_div, norm_one, hznorm, one_div]
      have hinvτ : |τ|⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hτδ
      have hstep : |τ|⁻¹ * ‖(riemannZeta (1 + 2 * (ω : ℂ)) +
          2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
            ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2‖ ≤ δ⁻¹ * 3 :=
        mul_le_mul hinvτ hK (norm_nonneg _) (by positivity)
      calc |τ|⁻¹ * ‖(riemannZeta (1 + 2 * (ω : ℂ)) +
              2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
            ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2‖ ≤ δ⁻¹ * 3 := hstep
        _ = 3 / δ := by
            rw [div_eq_mul_inv]
            ring
    -- assemble
    rw [mobiusCausalMultiplierDeriv]
    refine le_trans (norm_add_le _ _) ?_
    have hprod : ‖riemannZeta (1 + z) /
        ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)) *
        (-(1 / (1 + (ω : ℂ) + z)) -
          2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) / riemannZeta (1 + 2 * (ω : ℂ) + z))‖
        ≤ C3 * C1 * (1 + 2 * (C2 * C1)) := by
      rw [norm_mul]
      refine mul_le_mul hfac hbr (norm_nonneg _) ?_
      positivity
    linarith

end

end RHTower
