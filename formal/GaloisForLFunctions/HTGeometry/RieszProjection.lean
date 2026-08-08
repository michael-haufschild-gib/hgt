/-
# The Riesz projection of a spectral contour

For an element `a` of a complete normed `ℂ`-algebra and a circle lying in the resolvent set, the
Riesz projection is

  `P = (2πi)⁻¹ ∮_{|λ−c|=r} (λ − a)⁻¹ dλ`.

Mathlib has the resolvent and its differentiability on the resolvent set
(`spectrum.hasDerivAt_resolvent`) but no Riesz projection.  This file introduces it and proves what
follows immediately from Cauchy's theorem: a contour whose whole disc avoids the spectrum gives the
zero projection.

Main results:
* `resolvent_sub_resolvent` — the **resolvent identity**.
* `commute_resolvent`, `rieszProjection_commute` — the projection commutes with `a`.
* `rieszProjection_eq_of_annulus` — **contour independence**: the projection depends only on which
  part of the spectrum the circle encloses.
* `resolventCauchyTransform`, `differentiableOn_resolventCauchyTransform` — the Cauchy transform of
  the resolvent along a circle is holomorphic inside it.
* `rieszProjection_mul_self` — **idempotence** `P ^ 2 = P`.
* `rieszProjection` — the definition.
* `circleIntegrable_resolvent` — the resolvent is circle-integrable on a contour in the resolvent
  set.
* `rieszProjection_eq_zero_of_closedBall_subset` — a spectrum-free disc gives the zero projection.
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.CauchyIntegral

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **The Riesz projection** attached to a circle in the resolvent set. -/
noncomputable def rieszProjection (a : A) (c : ℂ) (r : ℝ) : A :=
  (2 * Real.pi * Complex.I)⁻¹ • ∮ lam in C(c, r), resolvent a lam

/-- The resolvent is continuous, hence circle-integrable, on a contour in the resolvent set. -/
theorem circleIntegrable_resolvent {a : A} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ a) :
    CircleIntegrable (resolvent a) c r := by
  refine ContinuousOn.circleIntegrable hr fun lam hlam => ?_
  exact ((spectrum.hasDerivAt_resolvent_const_left (h lam hlam)).continuousAt).continuousWithinAt

/-- **A spectrum-free disc gives the zero Riesz projection**, by Cauchy's theorem. -/
theorem rieszProjection_eq_zero_of_closedBall_subset (a : A) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ lam ∈ closedBall c r, lam ∈ resolventSet ℂ a) :
    rieszProjection a c r = 0 := by
  have hcont : ContinuousOn (resolvent a) (closedBall c r) := fun lam hlam =>
    ((spectrum.hasDerivAt_resolvent_const_left (h lam hlam)).continuousAt).continuousWithinAt
  have hdiff : ∀ lam ∈ ball c r \ (∅ : Set ℂ), DifferentiableAt ℂ (resolvent a) lam := by
    intro lam hlam
    exact (spectrum.hasDerivAt_resolvent_const_left
      (h lam (ball_subset_closedBall hlam.1))).differentiableAt
  rw [rieszProjection,
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
      hcont hdiff,
    smul_zero]

/-! ## The resolvent identity -/

omit [CompleteSpace A] in
theorem isUnit_of_mem_resolventSet {a : A} {l : ℂ} (hl : l ∈ resolventSet ℂ a) :
    IsUnit (algebraMap ℂ A l - a) := hl

omit [CompleteSpace A] in
theorem resolvent_mul_sub {a : A} {l : ℂ} (hl : l ∈ resolventSet ℂ a) :
    resolvent a l * (algebraMap ℂ A l - a) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_of_mem_resolventSet hl)

omit [CompleteSpace A] in
theorem sub_mul_resolvent {a : A} {l : ℂ} (hl : l ∈ resolventSet ℂ a) :
    (algebraMap ℂ A l - a) * resolvent a l = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_of_mem_resolventSet hl)

omit [CompleteSpace A] in
/-- **The resolvent identity** `R(λ) − R(μ) = (μ − λ)·R(λ)R(μ)`. -/
theorem resolvent_sub_resolvent {a : A} {l m : ℂ} (hl : l ∈ resolventSet ℂ a)
    (hm : m ∈ resolventSet ℂ a) :
    resolvent a l - resolvent a m = (m - l) • (resolvent a l * resolvent a m) := by
  have h1 : resolvent a l * (algebraMap ℂ A l - a) = 1 := resolvent_mul_sub hl
  have h2 : (algebraMap ℂ A m - a) * resolvent a m = 1 := sub_mul_resolvent hm
  have hstep : resolvent a l - resolvent a m
      = resolvent a l * ((algebraMap ℂ A m - a) - (algebraMap ℂ A l - a)) * resolvent a m := by
    have e1 : resolvent a l * (algebraMap ℂ A m - a) * resolvent a m = resolvent a l := by
      rw [mul_assoc, h2, mul_one]
    have e2 : resolvent a l * (algebraMap ℂ A l - a) * resolvent a m = resolvent a m := by
      rw [h1, one_mul]
    rw [mul_sub, sub_mul, e1, e2]
  have hdiff : (algebraMap ℂ A m - a) - (algebraMap ℂ A l - a) = (m - l) • (1 : A) := by
    rw [sub_sub_sub_cancel_right, ← map_sub, Algebra.algebraMap_eq_smul_one]
  rw [hstep, hdiff, mul_smul_comm, mul_one, smul_mul_assoc]

/-! ## Commutation with `a` -/

theorem circleIntegral_mul_left {a : A} {f : ℂ → A} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) :
    a * (∮ z in C(c, r), f z) = ∮ z in C(c, r), a * f z := by
  have key := (ContinuousLinearMap.intervalIntegral_comp_comm
    ((ContinuousLinearMap.mul ℂ A) a) hf.out).symm
  simp only [ContinuousLinearMap.mul_apply'] at key
  simp only [circleIntegral]
  rw [key]
  exact intervalIntegral.integral_congr fun θ _ => mul_smul_comm _ _ _

theorem circleIntegral_mul_right {a : A} {f : ℂ → A} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) :
    (∮ z in C(c, r), f z) * a = ∮ z in C(c, r), f z * a := by
  have key := (ContinuousLinearMap.intervalIntegral_comp_comm
    (((ContinuousLinearMap.mul ℂ A).flip) a) hf.out).symm
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at key
  simp only [circleIntegral]
  rw [key]
  exact intervalIntegral.integral_congr fun θ _ => smul_mul_assoc _ _ _

omit [CompleteSpace A] in
/-- The resolvent commutes with the element. -/
theorem commute_resolvent (a : A) {l : ℂ} (hl : l ∈ resolventSet ℂ a) :
    a * resolvent a l = resolvent a l * a := by
  have h1 : resolvent a l * (algebraMap ℂ A l - a) = 1 := resolvent_mul_sub hl
  have h2 : (algebraMap ℂ A l - a) * resolvent a l = 1 := sub_mul_resolvent hl
  have hcomm : a * (algebraMap ℂ A l - a) = (algebraMap ℂ A l - a) * a := by
    rw [mul_sub, sub_mul, Algebra.commutes]
  calc a * resolvent a l
      = (resolvent a l * (algebraMap ℂ A l - a)) * (a * resolvent a l) := by rw [h1, one_mul]
    _ = resolvent a l * (((algebraMap ℂ A l - a) * a) * resolvent a l) := by noncomm_ring
    _ = resolvent a l * ((a * (algebraMap ℂ A l - a)) * resolvent a l) := by rw [hcomm]
    _ = resolvent a l * a * ((algebraMap ℂ A l - a) * resolvent a l) := by noncomm_ring
    _ = resolvent a l * a := by rw [h2, mul_one]

/-- **The Riesz projection commutes with the element.** -/
theorem rieszProjection_commute (a : A) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ a) :
    a * rieszProjection a c r = rieszProjection a c r * a := by
  have hci : CircleIntegrable (resolvent a) c r := circleIntegrable_resolvent hr h
  rw [rieszProjection, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    circleIntegral_mul_left hci, circleIntegral_mul_right hci]
  congr 1
  exact circleIntegral.integral_congr hr fun lam hlam => commute_resolvent a (h lam hlam)

/-! ## Contour independence -/

/-- **The Riesz projection is unchanged by deforming the contour through the resolvent set.**  If
the closed annulus between two circles avoids the spectrum, the two projections agree. -/
theorem rieszProjection_eq_of_annulus (a : A) {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R)
    (h : ∀ lam ∈ closedBall c R \ ball c r, lam ∈ resolventSet ℂ a) :
    rieszProjection a c R = rieszProjection a c r := by
  rw [rieszProjection, rieszProjection]
  congr 1
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable h0 hle
    Set.countable_empty (fun lam hlam => ?_) (fun lam hlam => ?_)
  · exact ((spectrum.hasDerivAt_resolvent_const_left (h lam hlam)).continuousAt).continuousWithinAt
  · refine (spectrum.hasDerivAt_resolvent_const_left (h lam ?_)).differentiableAt
    exact ⟨ball_subset_closedBall hlam.1.1, fun hb => hlam.1.2 (ball_subset_closedBall hb)⟩

/-! ## Idempotence

The two-contour argument.  For `lam` on the small circle and `mu` on the large one the resolvent
identity turns the product `R(lam) R(mu)` into a difference of Cauchy kernels; integrating over the
large circle produces `2 pi i` times `R(lam)` plus the Cauchy transform of the resolvent, and the
latter is holomorphic inside the large circle, so its integral over the small one vanishes.  No
Fubini theorem for the operator-valued double circle integral is needed. -/

/-- **The Cauchy transform of the resolvent** along a circle. -/
noncomputable def resolventCauchyTransform (a : A) (c : ℂ) (R : ℝ) (w : ℂ) : A :=
  ∮ mu in C(c, R), (mu - w)⁻¹ • resolvent a mu

/-- **The Cauchy transform of the resolvent is holomorphic inside the circle**, even where the
resolvent itself does not extend. -/
theorem differentiableOn_resolventCauchyTransform (a : A) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (h : ∀ mu ∈ sphere c R, mu ∈ resolventSet ℂ a) :
    DifferentiableOn ℂ (resolventCauchyTransform a c R) (ball c R) := by
  have hci : CircleIntegrable (resolvent a) c R := circleIntegrable_resolvent hR.le h
  obtain ⟨Rn, hRn⟩ : ∃ Rn : NNReal, (Rn : ℝ) = R := ⟨⟨R, hR.le⟩, rfl⟩
  have hpos : 0 < Rn := by rw [← NNReal.coe_pos, hRn]; exact hR
  have hdiff := (hasFPowerSeriesOn_cauchy_integral (f := resolvent a) (c := c) (R := Rn)
    (by rw [hRn]; exact hci) hpos).differentiableOn
  rw [Metric.eball_coe, hRn] at hdiff
  have hfe : resolventCauchyTransform a c R
      = (2 * Real.pi * Complex.I : ℂ) •
        fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • resolvent a z := by
    funext w
    show (∮ mu in C(c, R), (mu - w)⁻¹ • resolvent a mu) = _
    simp only [Pi.smul_apply, smul_smul, mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_smul]
  rw [hfe]
  exact hdiff.const_smul _

/-- **The resolvent identity, integrated over the outer circle.**  For `lam` on the inner circle,
`∮ R(lam) R(mu) dmu = 2 pi i · R(lam) − (Cauchy transform of the resolvent at `lam`)`. -/
theorem circleIntegral_resolvent_mul (a : A) {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hrR : r < R)
    (h : ∀ lam ∈ closedBall c R \ ball c r, lam ∈ resolventSet ℂ a)
    {lam : ℂ} (hlam : lam ∈ sphere c r) :
    (∮ mu in C(c, R), resolvent a lam * resolvent a mu)
      = (2 * Real.pi * Complex.I : ℂ) • resolvent a lam - resolventCauchyTransform a c R lam := by
  have hR : 0 < R := lt_trans h0 hrR
  have hdl : dist lam c = r := hlam
  have hres_R : ∀ mu ∈ sphere c R, mu ∈ resolventSet ℂ a := by
    intro mu hmu
    have hd : dist mu c = R := hmu
    refine h mu ⟨?_, ?_⟩
    · rw [mem_closedBall, hd]
    · intro hb; rw [mem_ball, hd] at hb; linarith
  have hres_lam : lam ∈ resolventSet ℂ a := by
    refine h lam ⟨?_, ?_⟩
    · rw [mem_closedBall, hdl]; linarith
    · intro hb; rw [mem_ball, hdl] at hb; linarith
  have hlamball : lam ∈ ball c R := by rw [mem_ball, hdl]; exact hrR
  have hne : ∀ mu ∈ sphere c R, mu - lam ≠ 0 := by
    intro mu hmu he
    have hd : dist mu c = R := hmu
    rw [sub_eq_zero.mp he, hdl] at hd
    linarith
  have hpt : ∀ mu ∈ sphere c R, resolvent a lam * resolvent a mu
      = (mu - lam)⁻¹ • resolvent a lam - (mu - lam)⁻¹ • resolvent a mu := by
    intro mu hmu
    rw [← smul_sub, resolvent_sub_resolvent hres_lam (hres_R mu hmu), smul_smul,
      inv_mul_cancel₀ (hne mu hmu), one_smul]
  have hkern : ContinuousOn (fun mu : ℂ => (mu - lam)⁻¹) (sphere c R) :=
    ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) hne
  have hci1 : CircleIntegrable (fun mu => (mu - lam)⁻¹ • resolvent a lam) c R :=
    ContinuousOn.circleIntegrable hR.le (hkern.smul continuousOn_const)
  have hci2 : CircleIntegrable (fun mu => (mu - lam)⁻¹ • resolvent a mu) c R :=
    ContinuousOn.circleIntegrable hR.le (hkern.smul fun mu hmu =>
      ((spectrum.hasDerivAt_resolvent_const_left (hres_R mu hmu)).continuousAt).continuousWithinAt)
  rw [circleIntegral.integral_congr hR.le hpt, circleIntegral.integral_sub hci1 hci2,
    circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball hlamball]
  rfl

/-- **The Riesz projection is idempotent.** -/
theorem rieszProjection_mul_self (a : A) {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hrR : r < R)
    (h : ∀ lam ∈ closedBall c R \ ball c r, lam ∈ resolventSet ℂ a) :
    rieszProjection a c r * rieszProjection a c r = rieszProjection a c r := by
  have hR : 0 < R := lt_trans h0 hrR
  have hres_r : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ a := by
    intro lam hlam
    have hd : dist lam c = r := hlam
    refine h lam ⟨?_, ?_⟩
    · rw [mem_closedBall, hd]; linarith
    · intro hb; rw [mem_ball, hd] at hb; linarith
  have hres_R : ∀ mu ∈ sphere c R, mu ∈ resolventSet ℂ a := by
    intro mu hmu
    have hd : dist mu c = R := hmu
    refine h mu ⟨?_, ?_⟩
    · rw [mem_closedBall, hd]
    · intro hb; rw [mem_ball, hd] at hb; linarith
  have hci_r : CircleIntegrable (resolvent a) c r := circleIntegrable_resolvent h0.le hres_r
  have hci_R : CircleIntegrable (resolvent a) c R := circleIntegrable_resolvent hR.le hres_R
  have hcont_r : ContinuousOn (resolvent a) (sphere c r) := fun lam hlam =>
    ((spectrum.hasDerivAt_resolvent_const_left (hres_r lam hlam)).continuousAt).continuousWithinAt
  have hcia : CircleIntegrable
      (fun lam => (2 * Real.pi * Complex.I : ℂ) • resolvent a lam) c r :=
    ContinuousOn.circleIntegrable h0.le (continuousOn_const.smul hcont_r)
  have hG : DifferentiableOn ℂ (resolventCauchyTransform a c R) (ball c R) :=
    differentiableOn_resolventCauchyTransform a hR hres_R
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hciG : CircleIntegrable (resolventCauchyTransform a c R) c r :=
    ContinuousOn.circleIntegrable h0.le
      ((hG.mono hsub).continuousOn.mono sphere_subset_closedBall)
  have hG0 : (∮ lam in C(c, r), resolventCauchyTransform a c R lam) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable h0.le
      Set.countable_empty ((hG.mono hsub).continuousOn) (fun z hz => ?_)
    exact hG.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hz.1))
  have hcancel : ∀ Y : A,
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) • Y) = Y := by
    intro Y; rw [smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]
  have key : ∀ lam ∈ sphere c r, resolvent a lam * rieszProjection a c R
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ((2 * Real.pi * Complex.I : ℂ) • resolvent a lam
          - resolventCauchyTransform a c R lam) := by
    intro lam hlam
    rw [rieszProjection, Algebra.mul_smul_comm, circleIntegral_mul_left hci_R,
      circleIntegral_resolvent_mul a h0 hrR h hlam]
  have e1 : rieszProjection a c r * rieszProjection a c R
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ lam in C(c, r), resolvent a lam * rieszProjection a c R := by
    rw [show rieszProjection a c r
        = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ lam in C(c, r), resolvent a lam from rfl,
      Algebra.smul_mul_assoc, circleIntegral_mul_right hci_r]
  have e2 : (∮ lam in C(c, r), resolvent a lam * rieszProjection a c R)
      = ∮ lam in C(c, r), resolvent a lam := by
    rw [circleIntegral.integral_congr h0.le key, circleIntegral.integral_smul,
      circleIntegral.integral_sub hcia hciG, circleIntegral.integral_smul, hG0, sub_zero, hcancel]
  have hPeq : rieszProjection a c R = rieszProjection a c r :=
    rieszProjection_eq_of_annulus a h0 hrR.le h
  have main : rieszProjection a c r * rieszProjection a c R = rieszProjection a c r := by
    rw [e1, e2]; rfl
  rwa [hPeq] at main

end GaloisForLFunctions.HTGeometry
