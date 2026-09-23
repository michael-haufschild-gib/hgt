import GaloisForLFunctions.RHTower.ProlateBandEigenvalueSimplicity
import GaloisForLFunctions.RHTower.BandFormBridge
import GaloisForLFunctions.RHTower.ProlateBandHilbertSum
import GaloisForLFunctions.RHTower.ProlateBandEigenMass
import GaloisForLFunctions.RHTower.ProlateSeparationEnergy
import GaloisForLFunctions.RHTower.ProlateBandComponentEven
import GaloisForLFunctions.RHTower.ProlateBandOperatorInjective
import GaloisForLFunctions.RHTower.BandOperatorContraction

/-!
# The small-aperture rank-one anchor for the Slepian band family

At aperture zero the band operator vanishes, and its operator-norm derivative is the constant-kernel
operator.  This file identifies that derivative exactly as a positive rank-one operator and packages
the quantitative expansion

```text
B_c = (c / π) |1⟩⟨1| + R_c,       ‖R_c‖ ≤ 4 c² / π,
```

where `1` is the unnormalised constant class on `[-1,1]`, of squared norm `2`.  Thus the leading
eigenvalue is `2c/π` and every other leading-order direction is zero.  This is the rank-one
spectral anchor needed by the Slepian--Pollak no-crossing argument; no eigenvalue asymptotic is
assumed.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The entire sinc profile vanishes when the aperture is zero. -/
theorem sincSmooth_aperture_zero (u : ℝ) : sincSmooth 0 u = 0 := by
  rw [sincSmooth]
  rcases eq_or_ne u 0 with rfl | hu
  · rw [dslope_same]
    simp
  · rw [dslope_of_ne _ hu]
    simp [slope]

/-- The continuous Slepian kernel is zero at aperture zero. -/
theorem sincKernelContinuous_zero : sincKernelContinuous 0 = 0 := by
  ext z
  change sincSmooth 0 ((z.1 : ℝ) - (z.2 : ℝ)) = 0
  exact sincSmooth_aperture_zero _

/-- The band operator itself vanishes at aperture zero. -/
theorem bandOperatorL2_zero : bandOperatorL2 0 = 0 := by
  apply norm_eq_zero.mp
  have h := norm_continuousKernelOperator_le (a := (-1 : ℝ)) (b := 1)
    (by norm_num : (-1 : ℝ) ≤ 1) (sincKernelContinuous 0)
  rw [← bandOperatorL2] at h
  rw [sincKernelContinuous_zero] at h
  simpa using h

/-- Quantitative operator-norm linearisation at the zero aperture. -/
theorem norm_bandOperatorL2_sub_linear_zero_le (c : ℝ) :
    ‖bandOperatorL2 c - c • cosOperatorL2 0‖ ≤ 4 * c ^ (2 : ℕ) / Real.pi := by
  have h := norm_bandOperator_taylor_le 0 c
  simpa [bandOperatorL2_zero] using h

/-- The unnormalised constant class on the unit band. -/
noncomputable def constantBandClass : RealIntervalL2 (-1 : ℝ) 1 :=
  bandClass (fun _ : ℝ => 1) continuous_const

/-- The zero-aperture cosine operator maps every vector to its integral times the constant class. -/
theorem cosOperatorL2_zero_apply (f : RealIntervalL2 (-1 : ℝ) 1) :
    cosOperatorL2 0 f =
      ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi) • constantBandClass := by
  change continuousKernelOperator (cosKernelContinuous 0) f = _
  apply Lp.ext
  filter_upwards [continuousKernelOperator_coeFn (cosKernelContinuous 0) f,
    Lp.coeFn_smul ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi)
      constantBandClass,
    coeFn_bandClass (fun _ : ℝ => 1) continuous_const] with x hleft hright hone
  rw [hleft, hright]
  change (∫ y : ClosedInterval (-1 : ℝ) 1,
      cosKernelContinuous 0 (x, y) * f y ∂volume) =
    ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi) *
      (bandClass (fun _ : ℝ => 1) continuous_const :
        ClosedInterval (-1 : ℝ) 1 → ℝ) x
  rw [hone, mul_one]
  calc
    (∫ y : ClosedInterval (-1 : ℝ) 1,
        cosKernelContinuous 0 (x, y) * f y ∂volume) =
        ∫ y : ClosedInterval (-1 : ℝ) 1, (1 / Real.pi) * f y ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [cosKernelContinuous]
    _ = (1 / Real.pi) * ∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume := by
      rw [integral_const_mul]
    _ = (∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi := by ring

/-- Pairing against the constant class is literal integration over the aperture. -/
theorem inner_constantBandClass_eq_integral (f : RealIntervalL2 (-1 : ℝ) 1) :
    (inner ℝ constantBandClass f : ℝ) =
      ∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_bandClass (fun _ : ℝ => 1) continuous_const] with x hx
  rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  change f x * (constantBandClass : ClosedInterval (-1 : ℝ) 1 → ℝ) x = f x
  change f x * (bandClass (fun _ : ℝ => 1) continuous_const :
    ClosedInterval (-1 : ℝ) 1 → ℝ) x = f x
  rw [hx]
  ring

/-- The constant class has squared norm equal to the aperture length `2`. -/
theorem norm_sq_constantBandClass : ‖constantBandClass‖ ^ (2 : ℕ) = 2 := by
  change ‖bandClass (fun _ : ℝ => 1) continuous_const‖ ^ (2 : ℕ) = 2
  rw [norm_sq_bandClass]
  norm_num

/-- Exact rank-one identification of the zero-aperture derivative. -/
theorem cosOperatorL2_zero_eq_rankOne :
    cosOperatorL2 0 =
      (1 / Real.pi) •
        InnerProductSpace.rankOne ℝ constantBandClass constantBandClass := by
  apply ContinuousLinearMap.ext
  intro f
  rw [smul_apply, InnerProductSpace.rankOne_apply, inner_constantBandClass_eq_integral]
  calc
    cosOperatorL2 0 f =
        ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi) •
          constantBandClass := cosOperatorL2_zero_apply f
    _ = ((1 / Real.pi) *
        (∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume)) • constantBandClass := by
      congr 1
      ring
    _ = (1 / Real.pi) •
        ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) • constantBandClass) := by
      rw [smul_smul]

/-- The rank-one tangent acts on the constant line by its unique nonzero eigenvalue `2/π`. -/
theorem cosOperatorL2_zero_constantBandClass :
    cosOperatorL2 0 constantBandClass = (2 / Real.pi) • constantBandClass := by
  rw [cosOperatorL2_zero_eq_rankOne, smul_apply, InnerProductSpace.rankOne_apply,
    real_inner_self_eq_norm_sq, norm_sq_constantBandClass, smul_smul]
  congr 1
  ring

/-- Every zero-aperture tangent value lies on the constant line. -/
theorem cosOperatorL2_zero_mem_span (f : RealIntervalL2 (-1 : ℝ) 1) :
    cosOperatorL2 0 f ∈ ℝ ∙ constantBandClass := by
  rw [cosOperatorL2_zero_apply]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The zero-aperture tangent has rank at most one. -/
theorem hasRankLE_cosOperatorL2_zero :
    Module.finrank ℝ (LinearMap.range (cosOperatorL2 0).toLinearMap) ≤ 1 := by
  have hrange : LinearMap.range (cosOperatorL2 0).toLinearMap ≤
      ℝ ∙ constantBandClass := by
    rintro _ ⟨f, rfl⟩
    exact cosOperatorL2_zero_mem_span f
  have hconst : constantBandClass ≠ 0 := by
    intro hzero
    have hnorm := norm_sq_constantBandClass
    rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
    norm_num at hnorm
  simpa [finrank_span_singleton hconst] using Submodule.finrank_mono hrange

/-- A normalized eigenline orthogonal to the constant tangent direction cannot rise above the
quadratic Taylor remainder. -/
theorem bandEigenvalue_le_remainder_of_constant_orthogonal
    {c lam : ℝ} {f : RealIntervalL2 (-1 : ℝ) 1}
    (hf : bandOperatorL2 c f = lam • f)
    (hfnorm : (inner ℝ f f : ℝ) = 1)
    (hfortho : (inner ℝ constantBandClass f : ℝ) = 0) :
    lam ≤ 4 * c ^ (2 : ℕ) / Real.pi := by
  have hnorm : ‖f‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hfnorm
    nlinarith [norm_nonneg f]
  have hcos : cosOperatorL2 0 f = 0 := by
    rw [cosOperatorL2_zero_apply]
    rw [← inner_constantBandClass_eq_integral, hfortho]
    simp
  have happly : (bandOperatorL2 c - c • cosOperatorL2 0) f = lam • f := by
    simp [hf, hcos]
  have hbound := ContinuousLinearMap.le_opNorm
    (bandOperatorL2 c - c • cosOperatorL2 0) f
  rw [happly, norm_smul, Real.norm_eq_abs, hnorm, mul_one] at hbound
  have hrem := norm_bandOperatorL2_sub_linear_zero_le c
  have habs : |lam| ≤ ‖bandOperatorL2 c - c • cosOperatorL2 0‖ := by
    simpa using hbound
  exact (le_abs_self lam).trans (habs.trans hrem)

/-- There is at most one band eigenvalue above the rank-one Taylor remainder.  If two normalized
eigenvectors had distinct values there, their span would contain a nonzero constant-orthogonal
direction on which the band quadratic form is simultaneously above and below the remainder. -/
theorem bandEigenvalue_eq_of_above_rankOne_remainder
    {c lam mu : ℝ} {f g : RealIntervalL2 (-1 : ℝ) 1}
    (hf : bandOperatorL2 c f = lam • f)
    (hg : bandOperatorL2 c g = mu • g)
    (hfnorm : (inner ℝ f f : ℝ) = 1)
    (hgnorm : (inner ℝ g g : ℝ) = 1)
    (hlam : 4 * c ^ (2 : ℕ) / Real.pi < lam)
    (hmu : 4 * c ^ (2 : ℕ) / Real.pi < mu) :
    lam = mu := by
  by_contra hne
  have hfg : (inner ℝ f g : ℝ) = 0 := by
    have hsym := bandOperatorL2_symmetric c f g
    rw [hf, hg, inner_smul_left, inner_smul_right] at hsym
    simp only [starRingEnd_apply, star_trivial] at hsym
    have : (lam - mu) * (inner ℝ f g : ℝ) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have hgf : (inner ℝ g f : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hfg
  let b : ℝ := inner ℝ constantBandClass f
  by_cases hb : b = 0
  · exact (not_lt_of_ge
      (bandEigenvalue_le_remainder_of_constant_orthogonal hf hfnorm hb)) hlam
  · let a : ℝ := inner ℝ constantBandClass g
    let v : RealIntervalL2 (-1 : ℝ) 1 := a • f - b • g
    have hvortho : (inner ℝ constantBandClass v : ℝ) = 0 := by
      dsimp only [v, a, b]
      rw [inner_sub_right, inner_smul_right, inner_smul_right]
      ring
    have hvne : v ≠ 0 := by
      intro hv
      have hvg := congrArg (fun w : RealIntervalL2 (-1 : ℝ) 1 => (inner ℝ w g : ℝ)) hv
      dsimp only [v] at hvg
      rw [inner_sub_left, inner_smul_left, inner_smul_left, hfg, hgnorm] at hvg
      simp only [starRingEnd_apply, star_trivial, mul_zero, mul_one, zero_sub,
        inner_zero_left] at hvg
      exact hb (neg_eq_zero.mp hvg)
    have hcos : cosOperatorL2 0 v = 0 := by
      rw [cosOperatorL2_zero_apply]
      rw [← inner_constantBandClass_eq_integral, hvortho]
      simp
    have hvnormsq : ‖v‖ ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
      rw [← real_inner_self_eq_norm_sq]
      dsimp only [v]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        starRingEnd_apply, star_trivial, hfg, hgf, hfnorm, hgnorm,
        mul_zero, mul_one]
      ring
    have hBv : bandOperatorL2 c v = (a * lam) • f - (b * mu) • g := by
      dsimp only [v]
      rw [map_sub, map_smul, map_smul, hf, hg, smul_smul, smul_smul]
    have hquad : (inner ℝ (bandOperatorL2 c v) v : ℝ) =
        lam * a ^ (2 : ℕ) + mu * b ^ (2 : ℕ) := by
      rw [hBv]
      dsimp only [v]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        starRingEnd_apply, star_trivial, hfg, hgf, hfnorm, hgnorm,
        mul_zero, mul_one]
      ring
    let eps : ℝ := 4 * c ^ (2 : ℕ) / Real.pi
    have hstrict : eps * ‖v‖ ^ (2 : ℕ) < (inner ℝ (bandOperatorL2 c v) v : ℝ) := by
      rw [hquad, hvnormsq]
      dsimp only [eps]
      have hb2 : 0 < b ^ (2 : ℕ) := sq_pos_of_ne_zero hb
      have ha2 : 0 ≤ a ^ (2 : ℕ) := sq_nonneg a
      nlinarith
    have hdiff : (bandOperatorL2 c - c • cosOperatorL2 0) v = bandOperatorL2 c v := by
      simp [hcos]
    have hinner : (inner ℝ (bandOperatorL2 c v) v : ℝ) ≤
        ‖bandOperatorL2 c - c • cosOperatorL2 0‖ * ‖v‖ ^ (2 : ℕ) := by
      rw [← hdiff]
      calc
        (inner ℝ ((bandOperatorL2 c - c • cosOperatorL2 0) v) v : ℝ)
            ≤ |(inner ℝ ((bandOperatorL2 c - c • cosOperatorL2 0) v) v : ℝ)| :=
          le_abs_self _
        _ ≤ ‖(bandOperatorL2 c - c • cosOperatorL2 0) v‖ * ‖v‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (‖bandOperatorL2 c - c • cosOperatorL2 0‖ * ‖v‖) * ‖v‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖bandOperatorL2 c - c • cosOperatorL2 0‖ * ‖v‖ ^ (2 : ℕ) := by ring
    have hrem := norm_bandOperatorL2_sub_linear_zero_le c
    have hnonneg : 0 ≤ ‖v‖ ^ (2 : ℕ) := sq_nonneg _
    have hle : (inner ℝ (bandOperatorL2 c v) v : ℝ) ≤ eps * ‖v‖ ^ (2 : ℕ) :=
      hinner.trans (mul_le_mul_of_nonneg_right hrem hnonneg)
    exact (not_lt_of_ge hle) hstrict

/-- Below aperture `1/4`, the constant trial has Rayleigh numerator strictly above the rank-one
remainder threshold. -/
theorem inner_bandOperatorL2_constant_gt_rankOne_remainder
    {c : ℝ} (hc : 0 < c) (hcsmall : c < 1 / 4) :
    (4 * c ^ (2 : ℕ) / Real.pi) * ‖constantBandClass‖ ^ (2 : ℕ) <
      (inner ℝ (bandOperatorL2 c constantBandClass) constantBandClass : ℝ) := by
  let A := bandOperatorL2 c - c • cosOperatorL2 0
  let eps := 4 * c ^ (2 : ℕ) / Real.pi
  have hA : ‖A‖ ≤ eps := by
    simpa only [A, eps] using norm_bandOperatorL2_sub_linear_zero_le c
  have hsplit : bandOperatorL2 c constantBandClass =
      A constantBandClass + (c • cosOperatorL2 0) constantBandClass := by
    dsimp only [A]
    simp
  have herr : |(inner ℝ (A constantBandClass) constantBandClass : ℝ)| ≤
      eps * ‖constantBandClass‖ ^ (2 : ℕ) := by
    calc
      |(inner ℝ (A constantBandClass) constantBandClass : ℝ)| ≤
          ‖A constantBandClass‖ * ‖constantBandClass‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖constantBandClass‖) * ‖constantBandClass‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm A constantBandClass
      _ = ‖A‖ * ‖constantBandClass‖ ^ (2 : ℕ) := by ring
      _ ≤ eps * ‖constantBandClass‖ ^ (2 : ℕ) := by
        gcongr
  have hmain :
      (inner ℝ ((c • cosOperatorL2 0) constantBandClass) constantBandClass : ℝ) =
        4 * c / Real.pi := by
    rw [smul_apply, cosOperatorL2_zero_constantBandClass, smul_smul,
      inner_smul_left, real_inner_self_eq_norm_sq, norm_sq_constantBandClass]
    simp only [starRingEnd_apply, star_trivial]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hsplit, inner_add_left, hmain, norm_sq_constantBandClass]
  rw [norm_sq_constantBandClass] at herr
  have hlower := (abs_le.mp herr).1
  dsimp only [eps] at hlower
  have hpi : 0 < Real.pi := Real.pi_pos
  have hgap : 4 * eps < 4 * c / Real.pi := by
    dsimp only [eps]
    rw [show 4 * (4 * c ^ (2 : ℕ) / Real.pi) = 16 * c ^ (2 : ℕ) / Real.pi by ring]
    rw [div_lt_div_iff_of_pos_right hpi]
    nlinarith [mul_pos hc (sub_pos.mpr hcsmall)]
  nlinarith

/-- **Small-aperture spectral isolation.**  For `0 < c < 1/4` the real band operator has a
normalized eigenvector whose eigenvalue is above `4c²/π`, and every normalized eigenvector above
that threshold carries the same eigenvalue.  Full live-eigenspace simplicity then makes this one
spectral line. -/
theorem exists_unique_above_rankOne_remainder
    {c : ℝ} (hc : 0 < c) (hcsmall : c < 1 / 4) :
    ∃ (lam : ℝ) (f : RealIntervalL2 (-1 : ℝ) 1),
      4 * c ^ (2 : ℕ) / Real.pi < lam ∧
      (inner ℝ f f : ℝ) = 1 ∧
      bandOperatorL2 c f = lam • f ∧
      ∀ (mu : ℝ) (g : RealIntervalL2 (-1 : ℝ) 1),
        4 * c ^ (2 : ℕ) / Real.pi < mu →
        (inner ℝ g g : ℝ) = 1 →
        bandOperatorL2 c g = mu • g → mu = lam := by
  let u := constantBandClass
  let eps := 4 * c ^ (2 : ℕ) / Real.pi
  have htrial : eps * ‖u‖ ^ (2 : ℕ) < (inner ℝ (bandOperatorL2 c u) u : ℝ) := by
    simpa only [u, eps] using
      inner_bandOperatorL2_constant_gt_rankOne_remainder hc hcsmall
  have hex : ∃ (lam : ℝ) (f : RealIntervalL2 (-1 : ℝ) 1),
      eps < lam ∧ (inner ℝ f f : ℝ) = 1 ∧ bandOperatorL2 c f = lam • f := by
    by_contra hnone
    push Not at hnone
    have hstep : ∀ mu : ℝ,
        (inner ℝ (bandOperatorL2 c u) (bandComponent c u mu) : ℝ) ≤
          eps * (inner ℝ u (bandComponent c u mu) : ℝ) := by
      intro mu
      let w := bandComponent c u mu
      by_cases hw : w = 0
      · simp [w, hw]
      · have hwmem := bandComponent_mem c u mu
        have hweig : bandOperatorL2 c w = mu • w := mem_bandEigenspace_iff.mp hwmem
        have hmu : mu ≤ eps := by
          by_contra hgt
          push Not at hgt
          have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
          let g : RealIntervalL2 (-1 : ℝ) 1 := ‖w‖⁻¹ • w
          have hgnorm : (inner ℝ g g : ℝ) = 1 := by
            dsimp only [g]
            rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
            simp only [starRingEnd_apply, star_trivial]
            field_simp [ne_of_gt hwnorm]
          have hgeig : bandOperatorL2 c g = mu • g := by
            dsimp only [g]
            rw [map_smul, hweig, smul_smul, smul_smul]
            congr 1
            ring
          exact hnone mu g hgt hgnorm hgeig
        have hproj : (inner ℝ (bandOperatorL2 c u) w : ℝ) =
            mu * ‖w‖ ^ (2 : ℕ) := by
          rw [bandOperatorL2_symmetric c u w, hweig, inner_smul_right,
            inner_self_bandComponent c u mu]
        rw [hproj, inner_self_bandComponent c u mu]
        exact mul_le_mul_of_nonneg_right hmu (sq_nonneg _)
    have hsum1 : HasSum
        (fun mu : ℝ => (inner ℝ (bandOperatorL2 c u) (bandComponent c u mu) : ℝ))
        (inner ℝ (bandOperatorL2 c u) u : ℝ) :=
      ContinuousLinearMap.hasSum (innerSL ℝ (bandOperatorL2 c u)) (hasSum_bandComponent c u)
    have hsum2 : HasSum
        (fun mu : ℝ => eps * (inner ℝ u (bandComponent c u mu) : ℝ))
        (eps * (inner ℝ u u : ℝ)) :=
      HasSum.mul_left _ (ContinuousLinearMap.hasSum (innerSL ℝ u) (hasSum_bandComponent c u))
    have hle : (inner ℝ (bandOperatorL2 c u) u : ℝ) ≤
        eps * (inner ℝ u u : ℝ) := hasSum_le hstep hsum1 hsum2
    rw [real_inner_self_eq_norm_sq] at hle
    exact (not_lt_of_ge hle) htrial
  obtain ⟨lam, f, hlam, hfnorm, hf⟩ := hex
  refine ⟨lam, f, by simpa only [eps] using hlam, hfnorm, hf, ?_⟩
  intro mu g hmu hgnorm hg
  exact (bandEigenvalue_eq_of_above_rankOne_remainder hg hf hgnorm hfnorm hmu
    (by simpa only [eps] using hlam))


/-- Every live joint profile above the rank-one remainder is even.  An odd profile is orthogonal
to the constant tangent direction, contradicting the remainder ceiling after normalization. -/
theorem joint_profile_even_of_bandEigenvalue_above_rankOne_remainder
    {c lam chi : ℝ} {Phi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPhiNe : Phi ≠ 0) (hlam : 4 * c ^ (2 : ℕ) / Real.pi < lam)
    (hPhiBand : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    Function.Even Phi := by
  have hlam0 : lam ≠ 0 := by
    have hrem0 : 0 ≤ 4 * c ^ (2 : ℕ) / Real.pi := by positivity
    linarith
  rcases joint_prolate_even_or_odd hPhiSmooth hPhiNe hlam0 hPhiBand hPhiProlate with
    heven | hodd
  · exact heven
  · let p : RealIntervalL2 (-1 : ℝ) 1 := bandClass Phi hPhiSmooth.continuous
    have hpne : p ≠ 0 :=
      bandClass_ne_zero_of_global_band_eigen hPhiSmooth.continuous hlam0 hPhiNe hPhiBand
    have hpnorm : 0 < ‖p‖ := norm_pos_iff.mpr hpne
    let q : RealIntervalL2 (-1 : ℝ) 1 := ‖p‖⁻¹ • p
    have hpEig : bandOperatorL2 c p = lam • p :=
      bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
        hPhiSmooth.continuous hPhiBand
    have hqEig : bandOperatorL2 c q = lam • q := by
      dsimp only [q]
      rw [map_smul, hpEig, smul_smul, smul_smul]
      congr 1
      ring
    have hqnorm : (inner ℝ q q : ℝ) = 1 := by
      dsimp only [q]
      rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [ne_of_gt hpnorm]
    have hportho : (inner ℝ constantBandClass p : ℝ) = 0 := by
      change (inner ℝ (bandClass (fun _ : ℝ => 1) continuous_const)
        (bandClass Phi hPhiSmooth.continuous) : ℝ) = 0
      rw [inner_bandClass_eq]
      exact integral_even_mul_odd_eq_zero continuous_const hPhiSmooth.continuous
        (fun _ => rfl) hodd
    have hqortho : (inner ℝ constantBandClass q : ℝ) = 0 := by
      dsimp only [q]
      rw [inner_smul_right, hportho]
      simp
    exact False.elim ((not_lt_of_ge
      (bandEigenvalue_le_remainder_of_constant_orthogonal hqEig hqnorm hqortho)) hlam)

/-- The isolated small-aperture band line carries a genuine smooth even joint prolate profile. -/
theorem exists_unique_even_joint_above_rankOne_remainder
    {c : ℝ} (hc : 0 < c) (hcsmall : c < 1 / 4) :
    ∃ (lam chi : ℝ) (Phi : ℝ → ℝ),
      4 * c ^ (2 : ℕ) / Real.pi < lam ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧
      Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x := by
  obtain ⟨lam, f, hlam, hfnorm, hf, _hunique⟩ :=
    exists_unique_above_rankOne_remainder hc hcsmall
  have hlam0 : lam ≠ 0 := by
    have hrem0 : 0 ≤ 4 * c ^ (2 : ℕ) / Real.pi := by positivity
    linarith
  have hfne : f ≠ 0 := by
    intro hzero
    rw [hzero, inner_zero_left] at hfnorm
    norm_num at hfnorm
  obtain ⟨Phi, chi, hsm, hne, hband, hprolate⟩ :=
    exists_joint_prolate_band_eigen hc hlam0 hf hfne
  exact ⟨lam, chi, Phi, hlam, hsm, hne,
    joint_profile_even_of_bandEigenvalue_above_rankOne_remainder
      hsm hne hlam hband hprolate,
    hband, hprolate⟩

/-- Exact operator norm of the zero-aperture rank-one tangent. -/
theorem norm_cosOperatorL2_zero : ‖cosOperatorL2 0‖ = 2 / Real.pi := by
  rw [cosOperatorL2_zero_eq_rankOne, norm_smul,
    InnerProductSpace.norm_rankOne, ← pow_two, norm_sq_constantBandClass]
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr Real.pi_pos)]
  ring

/-- Every normalized band eigenvalue lies below the rank-one eigenvalue plus the quadratic
Taylor remainder. -/
theorem bandEigenvalue_le_linear_rankOne_add_remainder
    {c lam : ℝ} (hc : 0 ≤ c) {f : RealIntervalL2 (-1 : ℝ) 1}
    (hf : bandOperatorL2 c f = lam • f)
    (hfnorm : (inner ℝ f f : ℝ) = 1) :
    lam ≤ 2 * c / Real.pi + 4 * c ^ (2 : ℕ) / Real.pi := by
  have hnorm : ‖f‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hfnorm
    nlinarith [norm_nonneg f]
  have hrem := norm_bandOperatorL2_sub_linear_zero_le c
  have hsplit : bandOperatorL2 c =
      (bandOperatorL2 c - c • cosOperatorL2 0) + c • cosOperatorL2 0 := by
    module
  have hBnorm : ‖bandOperatorL2 c‖ ≤
      4 * c ^ (2 : ℕ) / Real.pi + 2 * c / Real.pi := by
    calc
      ‖bandOperatorL2 c‖ = ‖(bandOperatorL2 c - c • cosOperatorL2 0) +
          c • cosOperatorL2 0‖ := congrArg norm hsplit
      _ ≤ ‖bandOperatorL2 c - c • cosOperatorL2 0‖ +
          ‖c • cosOperatorL2 0‖ := norm_add_le _ _
      _ ≤ 4 * c ^ (2 : ℕ) / Real.pi + ‖c • cosOperatorL2 0‖ :=
        add_le_add hrem (le_refl _)
      _ = 4 * c ^ (2 : ℕ) / Real.pi + 2 * c / Real.pi := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
          norm_cosOperatorL2_zero]
        ring
  have habs : |lam| ≤ 2 * c / Real.pi + 4 * c ^ (2 : ℕ) / Real.pi := by
    calc
      |lam| = ‖bandOperatorL2 c f‖ := by
        rw [hf, norm_smul, Real.norm_eq_abs, hnorm, mul_one]
      _ ≤ ‖bandOperatorL2 c‖ := by
        calc
          ‖bandOperatorL2 c f‖ ≤ ‖bandOperatorL2 c‖ * ‖f‖ :=
            ContinuousLinearMap.le_opNorm (bandOperatorL2 c) f
          _ = ‖bandOperatorL2 c‖ := by rw [hnorm, mul_one]
      _ ≤ 4 * c ^ (2 : ℕ) / Real.pi + 2 * c / Real.pi := hBnorm
      _ = 2 * c / Real.pi + 4 * c ^ (2 : ℕ) / Real.pi := by ring
  exact (le_abs_self lam).trans habs

/-- Lower bound for the constant-vector band quadratic form obtained from the rank-one tangent. -/
theorem inner_bandOperatorL2_constant_lower (c : ℝ) :
    4 * c / Real.pi - 2 * (4 * c ^ (2 : ℕ) / Real.pi) ≤
      (inner ℝ (bandOperatorL2 c constantBandClass) constantBandClass : ℝ) := by
  let A := bandOperatorL2 c - c • cosOperatorL2 0
  let eps := 4 * c ^ (2 : ℕ) / Real.pi
  have hA : ‖A‖ ≤ eps := by
    simpa only [A, eps] using norm_bandOperatorL2_sub_linear_zero_le c
  have hsplit : bandOperatorL2 c constantBandClass =
      A constantBandClass + (c • cosOperatorL2 0) constantBandClass := by
    dsimp only [A]
    simp
  have herr : |(inner ℝ (A constantBandClass) constantBandClass : ℝ)| ≤
      2 * eps := by
    calc
      |(inner ℝ (A constantBandClass) constantBandClass : ℝ)| ≤
          ‖A constantBandClass‖ * ‖constantBandClass‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖constantBandClass‖) * ‖constantBandClass‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm A constantBandClass
      _ = ‖A‖ * 2 := by rw [mul_assoc, ← pow_two, norm_sq_constantBandClass]
      _ ≤ eps * 2 := mul_le_mul_of_nonneg_right hA (by norm_num)
      _ = 2 * eps := by ring
  have hmain :
      (inner ℝ ((c • cosOperatorL2 0) constantBandClass) constantBandClass : ℝ) =
        4 * c / Real.pi := by
    rw [smul_apply, cosOperatorL2_zero_constantBandClass, smul_smul,
      inner_smul_left, real_inner_self_eq_norm_sq, norm_sq_constantBandClass]
    simp only [starRingEnd_apply, star_trivial]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hsplit, inner_add_left, hmain]
  have hlower := (abs_le.mp herr).1
  dsimp only [eps] at hlower
  linarith

/-- Once `lam` is the unique band eigenvalue above the rank-one remainder, its orthogonal
complement has band quadratic form at most that remainder. -/
theorem bandQuadratic_le_remainder_of_orthogonal_isolated
    {c lam : ℝ} (hc : 0 < c) {f : RealIntervalL2 (-1 : ℝ) 1}
    (hf : bandOperatorL2 c f = lam • f)
    (hfnorm : (inner ℝ f f : ℝ) = 1)
    (hlam : 4 * c ^ (2 : ℕ) / Real.pi < lam)
    {z : RealIntervalL2 (-1 : ℝ) 1} (hzorth : (inner ℝ f z : ℝ) = 0) :
    (inner ℝ (bandOperatorL2 c z) z : ℝ) ≤
      (4 * c ^ (2 : ℕ) / Real.pi) * ‖z‖ ^ (2 : ℕ) := by
  let eps := 4 * c ^ (2 : ℕ) / Real.pi
  have hlam0 : lam ≠ 0 := by
    have heps0 : 0 ≤ eps := by dsimp only [eps]; positivity
    linarith
  have hfne : f ≠ 0 := by
    intro hzero
    rw [hzero, inner_zero_left] at hfnorm
    norm_num at hfnorm
  have hzf : (inner ℝ z f : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hzorth
  have hstep : ∀ mu : ℝ,
      (inner ℝ (bandOperatorL2 c z) (bandComponent c z mu) : ℝ) ≤
        eps * (inner ℝ z (bandComponent c z mu) : ℝ) := by
    intro mu
    let w := bandComponent c z mu
    by_cases hw : w = 0
    · simp [w, hw]
    · have hwmem := bandComponent_mem c z mu
      have hweig : bandOperatorL2 c w = mu • w := mem_bandEigenspace_iff.mp hwmem
      have hmu : mu ≤ eps := by
        by_contra hgt
        push Not at hgt
        have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
        let g : RealIntervalL2 (-1 : ℝ) 1 := ‖w‖⁻¹ • w
        have hgnorm : (inner ℝ g g : ℝ) = 1 := by
          dsimp only [g]
          rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
          simp only [starRingEnd_apply, star_trivial]
          field_simp [ne_of_gt hwnorm]
        have hgeig : bandOperatorL2 c g = mu • g := by
          dsimp only [g]
          rw [map_smul, hweig, smul_smul, smul_smul]
          congr 1
          ring
        have hmueq : mu = lam :=
          bandEigenvalue_eq_of_above_rankOne_remainder hgeig hf hgnorm hfnorm hgt hlam
        subst mu
        obtain ⟨s, hs⟩ := bandOperatorL2_eigenvectors_proportional
          hc hlam0 hf hfne hweig
        have hzw : (inner ℝ z w : ℝ) = 0 := by
          rw [hs, inner_smul_right, hzf]
          simp
        have hself := inner_self_bandComponent c z lam
        rw [show bandComponent c z lam = w from rfl, hzw] at hself
        have hwnorm0 : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
        exact hw (norm_eq_zero.mp hwnorm0)
      have hproj : (inner ℝ (bandOperatorL2 c z) w : ℝ) = mu * ‖w‖ ^ (2 : ℕ) := by
        rw [bandOperatorL2_symmetric c z w, hweig, inner_smul_right,
          inner_self_bandComponent c z mu]
      rw [hproj, inner_self_bandComponent c z mu]
      exact mul_le_mul_of_nonneg_right hmu (sq_nonneg _)
  have hsum1 : HasSum
      (fun mu : ℝ => (inner ℝ (bandOperatorL2 c z) (bandComponent c z mu) : ℝ))
      (inner ℝ (bandOperatorL2 c z) z : ℝ) :=
    ContinuousLinearMap.hasSum (innerSL ℝ (bandOperatorL2 c z)) (hasSum_bandComponent c z)
  have hsum2 : HasSum
      (fun mu : ℝ => eps * (inner ℝ z (bandComponent c z mu) : ℝ))
      (eps * (inner ℝ z z : ℝ)) :=
    HasSum.mul_left _ (ContinuousLinearMap.hasSum (innerSL ℝ z) (hasSum_bandComponent c z))
  have hle : (inner ℝ (bandOperatorL2 c z) z : ℝ) ≤
      eps * (inner ℝ z z : ℝ) := hasSum_le hstep hsum1 hsum2
  rw [real_inner_self_eq_norm_sq] at hle
  simpa only [eps] using hle

/-- **Small-aperture mass anchor.**  For `0 < c < 1/8`, the unique band eigenline above the
rank-one remainder captures more than half of the constant vector's total spectral mass: its
squared component norm is strictly greater than `1`, while the constant vector has squared norm
`2`. -/
theorem leadingBandComponent_constant_mass_gt_one
    {c lam : ℝ} (hc : 0 < c) (hcsmall : c < 1 / 8)
    {f : RealIntervalL2 (-1 : ℝ) 1}
    (hf : bandOperatorL2 c f = lam • f)
    (hfnorm : (inner ℝ f f : ℝ) = 1)
    (hlam : 4 * c ^ (2 : ℕ) / Real.pi < lam) :
    1 < ‖bandComponent c constantBandClass lam‖ ^ (2 : ℕ) := by
  let u := constantBandClass
  let w := bandComponent c u lam
  let z := u - w
  let eps := 4 * c ^ (2 : ℕ) / Real.pi
  have hwmem := bandComponent_mem c u lam
  have hwEig : bandOperatorL2 c w = lam • w := mem_bandEigenspace_iff.mp hwmem
  have hproj : (inner ℝ u f : ℝ) = (inner ℝ w f : ℝ) :=
    inner_eq_inner_bandComponent c u f (mem_bandEigenspace_iff.mpr hf)
  have hzorth : (inner ℝ f z : ℝ) = 0 := by
    have hproj' : (inner ℝ f u : ℝ) = (inner ℝ f w : ℝ) := by
      calc
        (inner ℝ f u : ℝ) = inner ℝ u f := real_inner_comm _ _
        _ = inner ℝ w f := hproj
        _ = inner ℝ f w := real_inner_comm _ _
    dsimp only [z]
    rw [inner_sub_right, hproj', sub_self]
  have hwz : (inner ℝ w z : ℝ) = 0 := by
    have hprojw : (inner ℝ w u : ℝ) = ‖w‖ ^ (2 : ℕ) := by
      rw [real_inner_comm]
      exact inner_self_bandComponent c u lam
    dsimp only [z]
    rw [inner_sub_right, hprojw, real_inner_self_eq_norm_sq, sub_self]
  have hzw : (inner ℝ z w : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hwz
  have hznorm : ‖z‖ ^ (2 : ℕ) = 2 - ‖w‖ ^ (2 : ℕ) := by
    have hu : u = w + z := by simp [z]
    have hnormadd : ‖u‖ ^ (2 : ℕ) = ‖w‖ ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ) := by
      rw [hu, ← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, hwz, hzw,
        real_inner_self_eq_norm_sq, add_zero, zero_add]
    rw [show ‖u‖ ^ (2 : ℕ) = 2 by exact norm_sq_constantBandClass] at hnormadd
    linarith
  have hquadSplit : (inner ℝ (bandOperatorL2 c u) u : ℝ) =
      lam * ‖w‖ ^ (2 : ℕ) + (inner ℝ (bandOperatorL2 c z) z : ℝ) := by
    have hu : u = w + z := by simp [z]
    have hcross1 : (inner ℝ (lam • w) z : ℝ) = 0 := by
      rw [inner_smul_left, hwz]
      simp
    have hcross2 : (inner ℝ (bandOperatorL2 c z) w : ℝ) = 0 := by
      rw [bandOperatorL2_symmetric c z w, hwEig, inner_smul_right, hzw]
      simp
    rw [hu, map_add, inner_add_left, inner_add_right, inner_add_right, hwEig,
      inner_smul_left, real_inner_self_eq_norm_sq, hcross1, hcross2]
    simp only [starRingEnd_apply, star_trivial, add_zero, zero_add]
  have hzquad := bandQuadratic_le_remainder_of_orthogonal_isolated
    hc hf hfnorm hlam hzorth
  have hlamUpper := bandEigenvalue_le_linear_rankOne_add_remainder hc.le hf hfnorm
  have hlower := inner_bandOperatorL2_constant_lower c
  have hupper : (inner ℝ (bandOperatorL2 c u) u : ℝ) ≤
      (2 * c / Real.pi) * ‖w‖ ^ (2 : ℕ) + 2 * eps := by
    rw [hquadSplit]
    calc
      lam * ‖w‖ ^ (2 : ℕ) + (inner ℝ (bandOperatorL2 c z) z : ℝ) ≤
          (2 * c / Real.pi + eps) * ‖w‖ ^ (2 : ℕ) + eps * ‖z‖ ^ (2 : ℕ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (by simpa only [eps] using hlamUpper) (sq_nonneg _))
          (by simpa only [eps] using hzquad)
      _ = (2 * c / Real.pi) * ‖w‖ ^ (2 : ℕ) + 2 * eps := by
        rw [hznorm]
        ring
  have hraw : 4 * c / Real.pi - 4 * eps ≤
      (2 * c / Real.pi) * ‖w‖ ^ (2 : ℕ) := by
    have hlower' : 4 * c / Real.pi - 2 * eps ≤
        (inner ℝ (bandOperatorL2 c u) u : ℝ) := by
      simpa only [u, eps] using hlower
    linarith
  have hmul := mul_le_mul_of_nonneg_right hraw Real.pi_pos.le
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  dsimp only [eps] at hmul
  field_simp [hpi0] at hmul
  nlinarith


/-- The isolated line above the rank-one remainder globally dominates the band quadratic form. -/
theorem bandQuadratic_le_isolated_eigenvalue
    {c lam : ℝ} {f : RealIntervalL2 (-1 : ℝ) 1}
    (hf : bandOperatorL2 c f = lam • f)
    (hfnorm : (inner ℝ f f : ℝ) = 1)
    (hlam : 4 * c ^ (2 : ℕ) / Real.pi < lam)
    (z : RealIntervalL2 (-1 : ℝ) 1) :
    (inner ℝ (bandOperatorL2 c z) z : ℝ) ≤ lam * ‖z‖ ^ (2 : ℕ) := by
  let eps := 4 * c ^ (2 : ℕ) / Real.pi
  have hstep : ∀ mu : ℝ,
      (inner ℝ (bandOperatorL2 c z) (bandComponent c z mu) : ℝ) ≤
        lam * (inner ℝ z (bandComponent c z mu) : ℝ) := by
    intro mu
    let w := bandComponent c z mu
    by_cases hw : w = 0
    · simp [w, hw]
    · have hwmem := bandComponent_mem c z mu
      have hweig : bandOperatorL2 c w = mu • w := mem_bandEigenspace_iff.mp hwmem
      have hmu : mu ≤ lam := by
        by_cases hmueps : mu ≤ eps
        · exact hmueps.trans (le_of_lt (by simpa only [eps] using hlam))
        · push Not at hmueps
          have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
          let g : RealIntervalL2 (-1 : ℝ) 1 := ‖w‖⁻¹ • w
          have hgnorm : (inner ℝ g g : ℝ) = 1 := by
            dsimp only [g]
            rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
            simp only [starRingEnd_apply, star_trivial]
            field_simp [ne_of_gt hwnorm]
          have hgeig : bandOperatorL2 c g = mu • g := by
            dsimp only [g]
            rw [map_smul, hweig, smul_smul, smul_smul]
            congr 1
            ring
          exact le_of_eq (bandEigenvalue_eq_of_above_rankOne_remainder
            hgeig hf hgnorm hfnorm hmueps hlam)
      have hproj : (inner ℝ (bandOperatorL2 c z) w : ℝ) = mu * ‖w‖ ^ (2 : ℕ) := by
        rw [bandOperatorL2_symmetric c z w, hweig, inner_smul_right,
          inner_self_bandComponent c z mu]
      rw [hproj, inner_self_bandComponent c z mu]
      exact mul_le_mul_of_nonneg_right hmu (sq_nonneg _)
  have hsum1 : HasSum
      (fun mu : ℝ => (inner ℝ (bandOperatorL2 c z) (bandComponent c z mu) : ℝ))
      (inner ℝ (bandOperatorL2 c z) z : ℝ) :=
    ContinuousLinearMap.hasSum (innerSL ℝ (bandOperatorL2 c z)) (hasSum_bandComponent c z)
  have hsum2 : HasSum
      (fun mu : ℝ => lam * (inner ℝ z (bandComponent c z mu) : ℝ))
      (lam * (inner ℝ z z : ℝ)) :=
    HasSum.mul_left _ (ContinuousLinearMap.hasSum (innerSL ℝ z) (hasSum_bandComponent c z))
  have hle : (inner ℝ (bandOperatorL2 c z) z : ℝ) ≤
      lam * (inner ℝ z z : ℝ) := hasSum_le hstep hsum1 hsum2
  rw [real_inner_self_eq_norm_sq] at hle
  exact hle

/-- An eigenvalue above the rank-one remainder is the actual top concentration eigenvalue. -/
theorem isolated_bandEigenvalue_eq_norm
    {c lam : ℝ} (hc : 0 < c) {f : RealIntervalL2 (-1 : ℝ) 1}
    (hf : bandOperatorL2 c f = lam • f)
    (hfnorm : (inner ℝ f f : ℝ) = 1)
    (hlam : 4 * c ^ (2 : ℕ) / Real.pi < lam) :
    lam = ‖bandOperatorL2 c‖ := by
  have hnorm : ‖f‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hfnorm
    nlinarith [norm_nonneg f]
  have hlam0 : 0 < lam := by
    have hrem0 : 0 ≤ 4 * c ^ (2 : ℕ) / Real.pi := by positivity
    linarith
  have hleNorm : lam ≤ ‖bandOperatorL2 c‖ := by
    have happ := ContinuousLinearMap.le_opNorm (bandOperatorL2 c) f
    rw [hf, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0, hnorm, mul_one,
      mul_one] at happ
    exact happ
  have hsym : ((bandOperatorL2 c :
      RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1) :
      RealIntervalL2 (-1 : ℝ) 1 →ₗ[ℝ] RealIntervalL2 (-1 : ℝ) 1).IsSymmetric :=
    fun x y => bandOperatorL2_symmetric c x y
  have hnormLe : ‖bandOperatorL2 c‖ ≤ lam := by
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hsym]
    refine ciSup_le fun z => ?_
    rcases eq_or_ne z 0 with rfl | hz
    · simp [hlam0.le]
    · have hsq : 0 < ‖z‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hz)
      have hquad := bandQuadratic_le_isolated_eigenvalue hf hfnorm hlam z
      have hquad0 := inner_bandOperatorL2_nonneg hc z
      rw [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
        abs_div, abs_of_pos hsq, abs_of_nonneg hquad0]
      rw [div_le_iff₀ hsq]
      simpa [mul_comm] using hquad
  exact le_antisymm hleNorm hnormLe


/-- Exact prolate action on the constant trial profile. -/
theorem prolateSLAction_const_one (c x : ℝ) :
    prolateSLAction c (fun _ : ℝ => 1) x = -(c ^ (2 : ℕ) * x ^ (2 : ℕ)) := by
  simp [prolateSLAction]

/-- The constant profile has exact prolate energy `-2c²/3` on `[-1,1]`. -/
theorem inner_constantProlateAction_constant (c : ℝ) :
    (inner ℝ
      (bandClass (prolateSLAction c (fun _ : ℝ => (1 : ℝ)))
        (contDiff_prolateSLAction (contDiff_const :
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (1 : ℝ)))).continuous)
      constantBandClass : ℝ) = -(2 * c ^ (2 : ℕ) / 3) := by
  rw [show constantBandClass = bandClass (fun _ : ℝ => 1) continuous_const from rfl,
    inner_bandClass_eq]
  simp_rw [prolateSLAction_const_one]
  norm_num
  ring

/-- Every live band component of the constant profile has nonpositive prolate energy. -/
theorem inner_constantProlateAction_bandComponent_nonpos
    {c mu : ℝ} (hc : 0 < c) (hmu : mu ≠ 0) :
    (inner ℝ
      (bandClass (prolateSLAction c (fun _ : ℝ => (1 : ℝ)))
        (contDiff_prolateSLAction (contDiff_const :
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (1 : ℝ)))).continuous)
      (bandComponent c constantBandClass mu) : ℝ) ≤ 0 := by
  let g : ℝ → ℝ := fun _ => 1
  have hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_const
  have hgc : Continuous g := hgsm.continuous
  have hgd1 : Differentiable ℝ g := (contDiff_infty_iff_deriv.mp hgsm).1
  have hgd2 : Differentiable ℝ (deriv g) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hgsm).2).1
  have hgd3 : Continuous (deriv (deriv g)) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hgsm).2).2).continuous
  have hLgc : Continuous (prolateSLAction c g) :=
    (contDiff_prolateSLAction hgsm).continuous
  let v := bandClass g hgc
  let Lv := bandClass (prolateSLAction c g) hLgc
  let u := bandComponent c v mu
  let bf : bandEigenspace c mu := ⟨u, bandComponent_mem c v mu⟩
  let Phi := eigenRep c mu bf
  have hPhic : Continuous Phi := continuous_eigenRep c mu bf
  have hPhism : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi :=
    contDiff_eigenRep hc hmu bf
  have hPhiclass : bandClass Phi hPhic = u := bandClass_eigenRep hmu bf
  have hLPhic : Continuous (prolateSLAction c Phi) :=
    (contDiff_prolateSLAction hPhism).continuous
  have hsymm := _root_.RHTower.prolateSLAction_band_symmetric hgd1 hgd2 hgd3
    (differentiable_eigenRep hc hmu bf)
    (differentiable_deriv_eigenRep hc hmu bf)
    (continuous_deriv2_eigenRep hc hmu bf) c
  have hmove : (inner ℝ Lv u : ℝ) =
      (inner ℝ v (bandClass (prolateSLAction c Phi) hLPhic) : ℝ) := by
    rw [show Lv = bandClass (prolateSLAction c g) hLgc from rfl,
      ← hPhiclass, inner_bandClass_eq,
      show v = bandClass g hgc from rfl, inner_bandClass_eq]
    rw [show (∫ x in (-1 : ℝ)..1, prolateSLAction c g x * Phi x) =
        ∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c g x from
      intervalIntegral.integral_congr fun x _ => mul_comm _ _]
    exact hsymm
  have hTmem : bandClass (prolateSLAction c Phi) hLPhic ∈ bandEigenspace c mu :=
    prolate_bandClass_mem hc hmu bf
  have hproj : (inner ℝ v (bandClass (prolateSLAction c Phi) hLPhic) : ℝ) =
      (inner ℝ u (bandClass (prolateSLAction c Phi) hLPhic) : ℝ) :=
    inner_eq_inner_bandComponent c v _ hTmem
  have hquad : (inner ℝ u (bandClass (prolateSLAction c Phi) hLPhic) : ℝ) ≤ 0 := by
    rw [← hPhiclass, inner_bandClass_eq]
    have hnonpos := integral_mul_prolateSLAction_nonpos (c := c)
      (differentiable_eigenRep hc hmu bf)
      (differentiable_deriv_eigenRep hc hmu bf)
      (continuous_deriv2_eigenRep hc hmu bf)
    exact hnonpos
  change (inner ℝ Lv u : ℝ) ≤ 0
  rw [hmove, hproj]
  exact hquad

/-- On a joint band/prolate line, the constant profile's component energy is its separation
value times its squared component mass. -/
theorem inner_constantProlateAction_bandComponent_eq_of_prolate
    {c mu eta : ℝ} (hc : 0 < c) (hmu : mu ≠ 0)
    (hP : prolateOnEigenspace hc hmu
        (⟨bandComponent c constantBandClass mu,
          bandComponent_mem c constantBandClass mu⟩ : bandEigenspace c mu) =
      eta • (⟨bandComponent c constantBandClass mu,
        bandComponent_mem c constantBandClass mu⟩ : bandEigenspace c mu)) :
    (inner ℝ
      (bandClass (prolateSLAction c (fun _ : ℝ => (1 : ℝ)))
        (contDiff_prolateSLAction (contDiff_const :
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (1 : ℝ)))).continuous)
      (bandComponent c constantBandClass mu) : ℝ) =
      eta * ‖bandComponent c constantBandClass mu‖ ^ (2 : ℕ) := by
  let g : ℝ → ℝ := fun _ => 1
  have hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_const
  have hgc : Continuous g := hgsm.continuous
  have hgd1 : Differentiable ℝ g := (contDiff_infty_iff_deriv.mp hgsm).1
  have hgd2 : Differentiable ℝ (deriv g) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hgsm).2).1
  have hgd3 : Continuous (deriv (deriv g)) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hgsm).2).2).continuous
  have hLgc : Continuous (prolateSLAction c g) :=
    (contDiff_prolateSLAction hgsm).continuous
  let v := bandClass g hgc
  let Lv := bandClass (prolateSLAction c g) hLgc
  let u := bandComponent c v mu
  let bf : bandEigenspace c mu := ⟨u, bandComponent_mem c v mu⟩
  let Phi := eigenRep c mu bf
  have hPhic : Continuous Phi := continuous_eigenRep c mu bf
  have hPhiclass : bandClass Phi hPhic = u := bandClass_eigenRep hmu bf
  have hLPhic : Continuous (prolateSLAction c Phi) :=
    (contDiff_prolateSLAction (contDiff_eigenRep hc hmu bf)).continuous
  have hsymm := _root_.RHTower.prolateSLAction_band_symmetric hgd1 hgd2 hgd3
    (differentiable_eigenRep hc hmu bf)
    (differentiable_deriv_eigenRep hc hmu bf)
    (continuous_deriv2_eigenRep hc hmu bf) c
  have hmove : (inner ℝ Lv u : ℝ) =
      (inner ℝ v (bandClass (prolateSLAction c Phi) hLPhic) : ℝ) := by
    rw [show Lv = bandClass (prolateSLAction c g) hLgc from rfl,
      ← hPhiclass, inner_bandClass_eq,
      show v = bandClass g hgc from rfl, inner_bandClass_eq]
    rw [show (∫ x in (-1 : ℝ)..1, prolateSLAction c g x * Phi x) =
        ∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c g x from
      intervalIntegral.integral_congr fun x _ => mul_comm _ _]
    exact hsymm
  have hTmem : bandClass (prolateSLAction c Phi) hLPhic ∈ bandEigenspace c mu :=
    prolate_bandClass_mem hc hmu bf
  have hproj : (inner ℝ v (bandClass (prolateSLAction c Phi) hLPhic) : ℝ) =
      (inner ℝ u (bandClass (prolateSLAction c Phi) hLPhic) : ℝ) :=
    inner_eq_inner_bandComponent c v _ hTmem
  have hP' : prolateOnEigenspace hc hmu bf = eta • bf := by
    simpa only [bf, u, v, g, constantBandClass] using hP
  have hclassP : bandClass (prolateSLAction c Phi) hLPhic = eta • u := by
    exact congrArg Subtype.val hP'
  change (inner ℝ Lv u : ℝ) = eta * ‖u‖ ^ (2 : ℕ)
  rw [hmove, hproj, hclassP, inner_smul_right, real_inner_self_eq_norm_sq]

/-- **Small-aperture first-rung anchor.** For `0 < c < 1/8`, the actual top concentration
eigenvalue is a smooth nonzero even joint line, and its separation value is strictly larger than
the constant profile's total energy `-2c²/3`. -/
theorem exists_smallAperture_leading_joint_separation_anchor
    {c : ℝ} (hc : 0 < c) (hcsmall : c < 1 / 8) :
    ∃ (lam eta : ℝ) (Phi : ℝ → ℝ),
      4 * c ^ (2 : ℕ) / Real.pi < lam ∧
      lam = ‖bandOperatorL2 c‖ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧
      Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      -(2 * c ^ (2 : ℕ) / 3) < eta := by
  have hcquarter : c < 1 / 4 := lt_trans hcsmall (by norm_num)
  obtain ⟨lam, f, hlam, hfnorm, hf, _⟩ :=
    exists_unique_above_rankOne_remainder hc hcquarter
  have hlamNorm : lam = ‖bandOperatorL2 c‖ :=
    isolated_bandEigenvalue_eq_norm hc hf hfnorm hlam
  have hlam0 : lam ≠ 0 := by
    have hrem0 : 0 ≤ 4 * c ^ (2 : ℕ) / Real.pi := by positivity
    linarith
  let v := constantBandClass
  let w := bandComponent c v lam
  have hwmem := bandComponent_mem c v lam
  have hwEig : bandOperatorL2 c w = lam • w := mem_bandEigenspace_iff.mp hwmem
  have hmass : 1 < ‖w‖ ^ (2 : ℕ) := by
    simpa only [w, v] using
      leadingBandComponent_constant_mass_gt_one hc hcsmall hf hfnorm hlam
  have hwne : w ≠ 0 := by
    intro hwzero
    rw [hwzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hmass
    norm_num at hmass
  let bf : bandEigenspace c lam := ⟨w, hwmem⟩
  let pbf := prolateOnEigenspace hc hlam0 bf
  have hpEig : bandOperatorL2 c (pbf : RealIntervalL2 (-1 : ℝ) 1) =
      lam • (pbf : RealIntervalL2 (-1 : ℝ) 1) :=
    mem_bandEigenspace_iff.mp pbf.property
  obtain ⟨eta, hp⟩ := bandOperatorL2_eigenvectors_proportional
    hc hlam0 hwEig hwne hpEig
  have hP : prolateOnEigenspace hc hlam0 bf = eta • bf := by
    apply Subtype.ext
    exact hp
  let Phi := eigenRep c lam bf
  have hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi :=
    contDiff_eigenRep hc hlam0 bf
  have hPhiNe : Phi ≠ 0 := by
    intro hzero
    apply hwne
    have hclassZero : bandClass Phi (continuous_eigenRep c lam bf) = 0 := by
      have hstep := bandClass_congr (continuous_eigenRep c lam bf) continuous_const hzero
      rw [hstep]
      exact bandClass_zero _
    change (bf : RealIntervalL2 (-1 : ℝ) 1) = 0
    rw [← bandClass_eigenRep hlam0 bf]
    exact hclassZero
  have hPhiEven : Function.Even Phi := by
    have hweven := bandComponent_mem_evenBandEigenspace
      (c := c) (g := fun _ : ℝ => (1 : ℝ)) (μ := lam)
      continuous_const (fun _ => rfl) hlam0
    exact hweven.2
  have hPhiBand : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x :=
    bandTransform_eigenRep hlam0 bf
  have hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x := by
    have hrepeq := congrArg (fun q : bandEigenspace c lam => eigenRep c lam q) hP
    rw [eigenRep_prolateOnEigenspace hc hlam0] at hrepeq
    intro x
    have hx := congrFun hrepeq x
    have hsmul : eigenRep c lam (eta • bf) x = eta * eigenRep c lam bf x :=
      eigenExtension_smul c lam eta bf x
    rw [hsmul] at hx
    exact hx
  have heta0 : eta ≤ 0 :=
    prolateSeparation_nonpos_of_global_joint hlam0 hPhiSmooth hPhiNe hPhiBand hPhiProlate
  let g : ℝ → ℝ := fun _ => 1
  have hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_const
  have hgc : Continuous g := hgsm.continuous
  have hLgc : Continuous (prolateSLAction c g) :=
    (contDiff_prolateSLAction hgsm).continuous
  let Lv := bandClass (prolateSLAction c g) hLgc
  have hsum : HasSum (fun mu : ℝ =>
      (inner ℝ Lv (bandComponent c v mu) : ℝ)) (inner ℝ Lv v : ℝ) :=
    ContinuousLinearMap.hasSum (innerSL ℝ Lv) (hasSum_bandComponent c v)
  have htop : HasSum (fun mu : ℝ => if mu = lam then eta * ‖w‖ ^ (2 : ℕ) else 0)
      (eta * ‖w‖ ^ (2 : ℕ)) := hasSum_ite_eq lam _
  have hstep : ∀ mu : ℝ,
      (inner ℝ Lv (bandComponent c v mu) : ℝ) ≤
        if mu = lam then eta * ‖w‖ ^ (2 : ℕ) else 0 := by
    intro mu
    by_cases hm : mu = lam
    · subst mu
      rw [if_pos rfl]
      exact le_of_eq (by
        simpa only [Lv, v, w, g, hLgc, hgsm] using
          inner_constantProlateAction_bandComponent_eq_of_prolate hc hlam0 hP)
    · rw [if_neg hm]
      by_cases hmu0 : mu = 0
      · subst mu
        rw [bandComponent_zero_eq_zero hc v]
        simp
      · simpa only [Lv, v, g, hLgc, hgsm] using
          inner_constantProlateAction_bandComponent_nonpos hc hmu0
  have htotalUpper : (inner ℝ Lv v : ℝ) ≤ eta * ‖w‖ ^ (2 : ℕ) :=
    hasSum_le hstep hsum htop
  have htotal : (inner ℝ Lv v : ℝ) = -(2 * c ^ (2 : ℕ) / 3) := by
    simpa only [Lv, v, g, hLgc, hgsm] using inner_constantProlateAction_constant c
  have hc2 : 0 < c ^ (2 : ℕ) := sq_pos_of_pos hc
  have hetaLower : -(2 * c ^ (2 : ℕ) / 3) < eta := by
    rw [htotal] at htotalUpper
    nlinarith
  exact ⟨lam, eta, Phi, hlam, hlamNorm, hPhiSmooth, hPhiNe, hPhiEven,
    hPhiBand, hPhiProlate, hetaLower⟩


end GaloisForLFunctions.RHTower

end
