import GaloisForLFunctions.RHTower.CCMUnitRieszCesaroFiniteApertureReporter

/-!
# Exact signed symbol of the limiting CCM-FU Cesàro reporter

The limiting CCM-FU curvature reporter has one positive region before the four-unit wall and one
negative region after it.  Estimating those regions separately destroys its cancellation.  This
module keeps both channels and the boundary atom in one completed symbol

```text
M(a) = ∫₀∞ exp(-a u) K(u) du - 3/64.
```

For every real exponent `a > -1/2`, the exact joint-channel transfer law is

```text
M(a) = -3 a² / (32 (a + 1) (2a + 1)).
```

Thus equal mass and barycenter appear as the double zero at the affine mode `a = 0`; no other
real exponential mode in the critical strip is lost.  In particular, every nonzero off-critical
real exponent has strictly negative signed gain.  All integrals retain the literal fast-minus-slow
FU kernel and its boundary counterterm.

The complex critical-Mellin symbol is the same rational function with `a` replaced by `z`; its
only zero on `Re z > -1/2` is the double affine zero `z = 0`.  Thus vertical oscillation cannot
hide a nonzero mode through cancellation of the reporter's two sign regions.
-/

open Set MeasureTheory Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Completed Laplace symbol of the limiting FU reporter, including its boundary atom. -/
def unitRieszCesaroCompletedReporterSymbol (a : ℝ) : ℝ :=
  (∫ u in Ioi (0 : ℝ),
    Real.exp (-(a * u)) * unitRieszCesaroCurvatureKernel u) - 3 / 64

/-- Contribution before the exact four-unit wall, where the FU kernel is nonnegative. -/
def unitRieszCesaroPositiveRegionSymbol (a : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) (4 * Real.log 2),
    Real.exp (-(a * u)) * unitRieszCesaroCurvatureKernel u

/-- Magnitude of the contribution after the exact four-unit wall, where the FU kernel is
nonpositive. -/
def unitRieszCesaroNegativeRegionSymbol (a : ℝ) : ℝ :=
  ∫ u in Ioi (4 * Real.log 2),
    -(Real.exp (-(a * u)) * unitRieszCesaroCurvatureKernel u)

theorem integrableOn_exp_mul_unitRieszCesaroCurvatureKernel
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    IntegrableOn (fun u : ℝ =>
      Real.exp (-(a * u)) * unitRieszCesaroCurvatureKernel u)
      (Ioi (0 : ℝ)) := by
  have hslow : 0 < a + 1 / 2 := by linarith
  have hfast : 0 < a + 1 := by linarith
  have hpoint : (fun u : ℝ =>
      Real.exp (-(a * u)) * unitRieszCesaroCurvatureKernel u) =
      (fun u : ℝ =>
        (3 / 32 : ℝ) * Real.exp (-((a + 1) * u)) -
          (3 / 128 : ℝ) * Real.exp (-((a + 1 / 2) * u))) := by
    funext u
    rw [unitRieszCesaroCurvatureKernel]
    have hfastProd : Real.exp (-(a * u)) * Real.exp (-u) =
        Real.exp (-((a + 1) * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hslowProd : Real.exp (-(a * u)) * Real.exp (-u / 2) =
        Real.exp (-((a + 1 / 2) * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-(a * u)) *
          (3 / 32 * (Real.exp (-u) - 1 / 4 * Real.exp (-u / 2))) =
          (3 / 32) * (Real.exp (-(a * u)) * Real.exp (-u)) -
            (3 / 128) * (Real.exp (-(a * u)) * Real.exp (-u / 2)) := by ring
      _ = _ := by rw [hfastProd, hslowProd]
  rw [hpoint]
  change Integrable
    ((fun u : ℝ => (3 / 32 : ℝ) * Real.exp (-((a + 1) * u))) -
      (fun u : ℝ => (3 / 128 : ℝ) * Real.exp (-((a + 1 / 2) * u))))
    (volume.restrict (Ioi (0 : ℝ)))
  simpa only [neg_mul] using
    ((exp_neg_integrableOn_Ioi (b := a + 1) 0 hfast).const_mul (3 / 32 : ℝ)).sub
      ((exp_neg_integrableOn_Ioi (b := a + 1 / 2) 0 hslow).const_mul (3 / 128 : ℝ))

theorem unitRieszCesaroPositiveRegionSymbol_nonneg (a : ℝ) :
    0 ≤ unitRieszCesaroPositiveRegionSymbol a := by
  rw [unitRieszCesaroPositiveRegionSymbol]
  refine setIntegral_nonneg measurableSet_Ioc fun u hu => ?_
  have hk : 0 ≤ unitRieszCesaroCurvatureKernel u := by
    by_cases heq : u = 4 * Real.log 2
    · rw [heq, unitRieszCesaroCurvatureKernel_fourUnitWall]
    · exact (unitRieszCesaroCurvatureKernel_pos_iff u).2
        (lt_of_le_of_ne hu.2 heq) |>.le
  exact mul_nonneg (Real.exp_pos _).le hk

theorem unitRieszCesaroNegativeRegionSymbol_nonneg (a : ℝ) :
    0 ≤ unitRieszCesaroNegativeRegionSymbol a := by
  rw [unitRieszCesaroNegativeRegionSymbol]
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hk : unitRieszCesaroCurvatureKernel u < 0 :=
    (unitRieszCesaroCurvatureKernel_neg_iff u).2 hu
  have he := Real.exp_pos (-(a * u))
  nlinarith

/-- Literal Jordan-region decomposition.  Neither FU region is replaced by absolute value; the
negative region and boundary atom retain their forced signs. -/
theorem unitRieszCesaroCompletedReporterSymbol_eq_positive_sub_negative
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    unitRieszCesaroCompletedReporterSymbol a =
      unitRieszCesaroPositiveRegionSymbol a -
        unitRieszCesaroNegativeRegionSymbol a - 3 / 64 := by
  let f : ℝ → ℝ := fun u =>
    Real.exp (-(a * u)) * unitRieszCesaroCurvatureKernel u
  have hw : 0 ≤ 4 * Real.log 2 := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hglobal : IntegrableOn f (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_unitRieszCesaroCurvatureKernel ha
  have hleft : IntegrableOn f (Ioc (0 : ℝ) (4 * Real.log 2)) :=
    hglobal.mono_set Ioc_subset_Ioi_self
  have hright : IntegrableOn f (Ioi (4 * Real.log 2)) :=
    hglobal.mono_set (Ioi_subset_Ioi hw)
  have hsplit : Ioi (0 : ℝ) =
      Ioc (0 : ℝ) (4 * Real.log 2) ∪ Ioi (4 * Real.log 2) :=
    (Ioc_union_Ioi_eq_Ioi hw).symm
  rw [unitRieszCesaroCompletedReporterSymbol,
    unitRieszCesaroPositiveRegionSymbol,
    unitRieszCesaroNegativeRegionSymbol]
  change (∫ u in Ioi (0 : ℝ), f u) - 3 / 64 =
    (∫ u in Ioc (0 : ℝ) (4 * Real.log 2), f u) -
      (∫ u in Ioi (4 * Real.log 2), -f u) - 3 / 64
  rw [hsplit,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hleft hright,
    integral_neg]
  ring

/-- Exact joint-channel transfer factor.  The `a²` numerator is precisely the reporter's
mass-and-barycenter cancellation. -/
theorem unitRieszCesaroCompletedReporterSymbol_eq
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    unitRieszCesaroCompletedReporterSymbol a =
      -(3 / 32 : ℝ) * a ^ 2 / ((a + 1) * (2 * a + 1)) := by
  have hslow : 0 < a + 1 / 2 := by linarith
  have hfast : 0 < a + 1 := by linarith
  have hslow' : 0 < 2 * a + 1 := by linarith
  have hfastne : a + 1 ≠ 0 := ne_of_gt hfast
  have hslowHalfne : a + 1 / 2 ≠ 0 := ne_of_gt hslow
  have hslowne : 2 * a + 1 ≠ 0 := ne_of_gt hslow'
  have hslowne' : 1 + a * 2 ≠ 0 := by linarith
  have hpoint : (fun u : ℝ =>
      Real.exp (-(a * u)) * unitRieszCesaroCurvatureKernel u) =
      (fun u : ℝ =>
        (3 / 32 : ℝ) * Real.exp (-((a + 1) * u)) -
          (3 / 128 : ℝ) * Real.exp (-((a + 1 / 2) * u))) := by
    funext u
    rw [unitRieszCesaroCurvatureKernel]
    have hfastProd : Real.exp (-(a * u)) * Real.exp (-u) =
        Real.exp (-((a + 1) * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hslowProd : Real.exp (-(a * u)) * Real.exp (-u / 2) =
        Real.exp (-((a + 1 / 2) * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-(a * u)) *
          (3 / 32 * (Real.exp (-u) - 1 / 4 * Real.exp (-u / 2))) =
          (3 / 32) * (Real.exp (-(a * u)) * Real.exp (-u)) -
            (3 / 128) * (Real.exp (-(a * u)) * Real.exp (-u / 2)) := by ring
      _ = _ := by rw [hfastProd, hslowProd]
  rw [unitRieszCesaroCompletedReporterSymbol, hpoint]
  have hfastInt : IntegrableOn
      (fun u : ℝ => (3 / 32 : ℝ) * Real.exp (-((a + 1) * u)))
      (Ioi (0 : ℝ)) := by
    change Integrable
      (fun u : ℝ => (3 / 32 : ℝ) * Real.exp (-((a + 1) * u)))
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [neg_mul] using
      (exp_neg_integrableOn_Ioi (b := a + 1) 0 hfast).const_mul (3 / 32 : ℝ)
  have hslowInt : IntegrableOn
      (fun u : ℝ => (3 / 128 : ℝ) * Real.exp (-((a + 1 / 2) * u)))
      (Ioi (0 : ℝ)) := by
    change Integrable
      (fun u : ℝ => (3 / 128 : ℝ) * Real.exp (-((a + 1 / 2) * u)))
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [neg_mul] using
      (exp_neg_integrableOn_Ioi (b := a + 1 / 2) 0 hslow).const_mul (3 / 128 : ℝ)
  rw [integral_sub hfastInt hslowInt,
    integral_const_mul, integral_const_mul,
    integral_Ioi_rexp_neg_mul_shift hfast 0,
    integral_Ioi_rexp_neg_mul_shift hslow 0]
  norm_num only [mul_zero, neg_zero, Real.exp_zero]
  field_simp [hfastne, hslowHalfne, hslowne, hslowne']
  have hunit : (1 + a * 2) * (1 + a * 2)⁻¹ = (1 : ℝ) :=
    mul_inv_cancel₀ hslowne'
  linear_combination -4096 * (1 - a) * hunit

/-- The completed signed reporter loses exactly the affine exponential mode and no other real
mode in its domain of convergence. -/
theorem unitRieszCesaroCompletedReporterSymbol_eq_zero_iff
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    unitRieszCesaroCompletedReporterSymbol a = 0 ↔ a = 0 := by
  constructor
  · intro hzero
    by_contra ha0
    have hneg := unitRieszCesaroCompletedReporterSymbol_eq (a := a) ha
    rw [hzero] at hneg
    have hfast : 0 < a + 1 := by linarith
    have hslow : 0 < 2 * a + 1 := by linarith
    have hstrict : -(3 / 32 : ℝ) * a ^ 2 / ((a + 1) * (2 * a + 1)) < 0 :=
      div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero ha0))
        (mul_pos hfast hslow)
    linarith
  · intro hzero
    subst a
    rw [unitRieszCesaroCompletedReporterSymbol_eq (by norm_num)]
    norm_num

/-- Every non-affine real exponential mode has strict negative joint-channel gain. -/
theorem unitRieszCesaroCompletedReporterSymbol_neg
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≠ 0) :
    unitRieszCesaroCompletedReporterSymbol a < 0 := by
  rw [unitRieszCesaroCompletedReporterSymbol_eq ha]
  have hfast : 0 < a + 1 := by linarith
  have hslow : 0 < 2 * a + 1 := by linarith
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero ha0))
    (mul_pos hfast hslow)

/-! ## Exact finite-aperture signed symbol -/

/-- Completed full-aperture symbol of the finite FU reporter, with lower wall at zero.  The
source-relative symbol below retains the actual positive lower wall. -/
def unitRieszCesaroFiniteCompletedReporterSymbol (t a : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..t,
    Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u) - 3 / 64

/-- Contribution from the positive side of the finite reporter's unique moving wall. -/
def unitRieszCesaroFinitePositiveRegionSymbol (t a : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..unitRieszCesaroWall t,
    Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u

/-- Magnitude of the contribution from the negative side of the finite reporter's unique moving
wall. -/
def unitRieszCesaroFiniteNegativeRegionSymbol (t a : ℝ) : ℝ :=
  ∫ u in unitRieszCesaroWall t..t,
    -(Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u)

/-- Exact full-aperture moving-wall Jordan decomposition.  This equality retains cancellation
between the two sign regions and the boundary atom rather than bounding either region separately. -/
theorem unitRieszCesaroFiniteCompletedReporterSymbol_eq_positive_sub_negative
    (t a : ℝ) :
    unitRieszCesaroFiniteCompletedReporterSymbol t a =
      unitRieszCesaroFinitePositiveRegionSymbol t a -
        unitRieszCesaroFiniteNegativeRegionSymbol t a - 3 / 64 := by
  let f : ℝ → ℝ := fun u =>
    Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u
  have hcont : Continuous f := by
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-(a * u)))).mul
      (continuous_unitRieszCesaroApertureKernel t)
  have hleft : IntervalIntegrable f volume 0 (unitRieszCesaroWall t) :=
    hcont.intervalIntegrable _ _
  have hright : IntervalIntegrable f volume (unitRieszCesaroWall t) t :=
    hcont.intervalIntegrable _ _
  rw [unitRieszCesaroFiniteCompletedReporterSymbol,
    unitRieszCesaroFinitePositiveRegionSymbol,
    unitRieszCesaroFiniteNegativeRegionSymbol]
  change (∫ u in (0 : ℝ)..t, f u) - 3 / 64 =
    (∫ u in (0 : ℝ)..unitRieszCesaroWall t, f u) -
      (∫ u in unitRieszCesaroWall t..t, -f u) - 3 / 64
  rw [intervalIntegral.integral_neg,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  ring

/-- Full-aperture cancellation identity.  After reflecting the reporter and integrating twice,
the endpoint derivative cancels the completed-source atom exactly.  The zero lower wall kills the
escaped boundary jet.  The source-relative theorem below shows the jet retained at `b > 0`. -/
theorem unitRieszCesaroFiniteCompletedReporterSymbol_eq
    {t : ℝ} (ht : 0 < t) (a : ℝ) :
    unitRieszCesaroFiniteCompletedReporterSymbol t a =
      -(Real.exp (t / 2) / t ^ 3) * a ^ 2 *
        ∫ s in (0 : ℝ)..t,
          Real.exp (-(a * (t - s))) * unitRieszCesaroTest t s := by
  let f : ℝ → ℝ := fun s => Real.exp (-(a * (t - s)))
  let G : ℝ → ℝ := unitRieszCesaroTest t
  let G' : ℝ → ℝ := unitRieszCesaroTestDeriv t
  let G'' : ℝ → ℝ := unitRieszCesaroTestSecondDeriv t
  have hf (s : ℝ) : HasDerivAt f (a * f s) s := by
    have hlin : HasDerivAt (fun x : ℝ => t - x) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have hinner : HasDerivAt (fun x : ℝ => -(a * (t - x))) a s := by
      simpa only [neg_mul, mul_neg, neg_neg, mul_one] using hlin.const_mul (-a)
    simpa only [f, Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (-(a * (t - s)))).comp s hinner
  have hG (s : ℝ) : HasDerivAt G (G' s) s := by
    exact hasDerivAt_unitRieszCesaroTest t s
  have hG' (s : ℝ) : HasDerivAt G' (G'' s) s := by
    exact hasDerivAt_unitRieszCesaroTestDeriv t s
  let F : ℝ → ℝ := fun s => f s * G' s - a * f s * G s
  have hF (s : ℝ) : HasDerivAt F
      (f s * G'' s - a ^ 2 * f s * G s) s := by
    have hleft := (hf s).mul (hG' s)
    have hright := ((hf s).mul (hG s)).const_mul a
    have hraw := hleft.sub hright
    have hderiv :
        a * f s * G' s + f s * G'' s -
            a * (a * f s * G s + f s * G' s) =
          f s * G'' s - a ^ 2 * f s * G s := by
      ring
    have hraw' := hraw.congr_deriv hderiv
    change HasDerivAt
      (fun x => f x * G' x - a * f x * G x)
      (f s * G'' s - a ^ 2 * f s * G s) s
    apply hraw'.congr_of_eventuallyEq
    filter_upwards with x
    simp only [Pi.mul_apply, Pi.sub_apply, mul_assoc]
  have hfirstInt : IntervalIntegrable (fun s : ℝ => f s * G'' s) volume 0 t := by
    apply Continuous.intervalIntegrable
    dsimp only [f, G'']
    exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (-(a * (t - s))))).mul
      (continuous_unitRieszCesaroTestSecondDeriv t)
  have hsecondInt : IntervalIntegrable
      (fun s : ℝ => a ^ 2 * f s * G s) volume 0 t := by
    apply Continuous.intervalIntegrable
    dsimp only [f, G]
    have hc := ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-(a * (t - s))))).mul
      (continuous_unitRieszCesaroTest t)).const_mul (a ^ 2)
    simpa only [Pi.mul_apply, mul_assoc] using hc
  have hderivInt : IntervalIntegrable
      (fun s : ℝ => f s * G'' s - a ^ 2 * f s * G s) volume 0 t :=
    hfirstInt.sub hsecondInt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hF s) hderivInt
  rw [intervalIntegral.integral_sub hfirstInt hsecondInt] at hftc
  have hsecondEq :
      (∫ s in (0 : ℝ)..t, a ^ 2 * f s * G s) =
        a ^ 2 * ∫ s in (0 : ℝ)..t, f s * G s := by
    rw [show (fun s : ℝ => a ^ 2 * f s * G s) =
        fun s : ℝ => a ^ 2 * (f s * G s) by funext s; ring,
      intervalIntegral.integral_const_mul]
  rw [hsecondEq] at hftc
  have hGt : G t = 0 := by exact unitRieszCesaroTest_self t
  have hG0 : G 0 = 0 := by exact unitRieszCesaroTest_zero t
  have hG'0 : G' 0 = 0 := by exact unitRieszCesaroTestDeriv_zero t
  have hG't : G' t = -(3 / 64) * t ^ 3 * Real.exp (-t / 2) := by
    exact unitRieszCesaroTestDeriv_endpoint t
  have hft : f t = 1 := by
    simp [f]
  have hftc' :
      (∫ s in (0 : ℝ)..t, f s * G'' s) =
        -(3 / 64) * t ^ 3 * Real.exp (-t / 2) +
          a ^ 2 * ∫ s in (0 : ℝ)..t, f s * G s := by
    dsimp only [F] at hftc
    rw [hGt, hG0, hG'0, hG't, hft] at hftc
    simp only [mul_zero, sub_zero] at hftc
    linarith
  let H : ℝ → ℝ := fun u =>
    Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u
  have hcv : (∫ u in (0 : ℝ)..t, H u) =
      ∫ s in (0 : ℝ)..t, H (t - s) := by
    simpa using (intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := t) H t).symm
  have hkernel : ∀ s : ℝ,
      H (t - s) = -(Real.exp (t / 2) / t ^ 3) * (f s * G'' s) := by
    intro s
    dsimp only [H, f, G'']
    rw [unitRieszCesaroApertureKernel_eq_secondDeriv]
    rw [show t - (t - s) = s by ring]
    ring
  rw [unitRieszCesaroFiniteCompletedReporterSymbol]
  change (∫ u in (0 : ℝ)..t, H u) - 3 / 64 = _
  rw [hcv]
  simp_rw [hkernel]
  rw [intervalIntegral.integral_const_mul, hftc']
  have ht3 : t ^ 3 ≠ 0 := by positivity
  have hexp : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add, show t / 2 + -t / 2 = (0 : ℝ) by ring, Real.exp_zero]
  dsimp only [f, G]
  have hboundary :
      -(Real.exp (t / 2) / t ^ 3) *
          (-(3 / 64) * t ^ 3 * Real.exp (-t / 2)) = 3 / 64 := by
    calc
      _ = (3 / 64 : ℝ) *
          (Real.exp (t / 2) * Real.exp (-t / 2)) * (t ^ 3 / t ^ 3) := by ring
      _ = _ := by rw [hexp, div_self ht3]; ring
  rw [mul_add, hboundary]
  ring

/-- Every non-affine real exponential has strictly negative gain already at each finite aperture.
This is a lossless signed reporter law, not an estimate of the two sign regions. -/
theorem unitRieszCesaroFiniteCompletedReporterSymbol_neg
    {t a : ℝ} (ht : 0 < t) (ha : a ≠ 0) :
    unitRieszCesaroFiniteCompletedReporterSymbol t a < 0 := by
  rw [unitRieszCesaroFiniteCompletedReporterSymbol_eq ht]
  have hweight : 0 < Real.exp (t / 2) / t ^ 3 := by positivity
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hint : 0 < ∫ s in (0 : ℝ)..t,
      Real.exp (-(a * (t - s))) * unitRieszCesaroTest t s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (((by fun_prop : Continuous (fun s : ℝ => Real.exp (-(a * (t - s))))).mul
        (continuous_unitRieszCesaroTest t)).intervalIntegrable _ _) ?_ ht
    intro s hs
    exact mul_pos (Real.exp_pos _) (unitRieszCesaroTest_pos hs.1 hs.2)
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hweight) ha2) hint

/-! ## Complex critical-Mellin symbol -/

/-- Completed complex Laplace symbol of the limiting signed FU reporter. -/
def unitRieszCesaroComplexCompletedReporterSymbol (z : ℂ) : ℂ :=
  (∫ u in Ioi (0 : ℝ),
    Complex.exp (-(z * (u : ℂ))) * (unitRieszCesaroCurvatureKernel u : ℂ)) - 3 / 64

/-- Exact complex transfer factor.  This is the mode law relevant to oscillatory Xi-zero
contributions, not merely the real-exponent restriction. -/
theorem unitRieszCesaroComplexCompletedReporterSymbol_eq
    {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    unitRieszCesaroComplexCompletedReporterSymbol z =
      -(3 / 32 : ℂ) * z ^ 2 / ((z + 1) * (2 * z + 1)) := by
  have hslow : 0 < (z + 1 / 2).re := by
    norm_num [Complex.add_re, Complex.div_re]
    linarith
  have hfast : 0 < (z + 1).re := by
    change 0 < z.re + 1
    linarith
  have hfastne : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at hre
    linarith
  have hslowHalfne : z + 1 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have hslowne : 2 * z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re] at hre
    linarith
  have hslowne' : 1 + z * 2 ≠ 0 := by
    intro h
    apply hslowne
    linear_combination h
  have hpoint : (fun u : ℝ =>
      Complex.exp (-(z * (u : ℂ))) * (unitRieszCesaroCurvatureKernel u : ℂ)) =
      (fun u : ℝ =>
        (3 / 32 : ℂ) * Complex.exp (-((z + 1) * (u : ℂ))) -
          (3 / 128 : ℂ) * Complex.exp (-((z + 1 / 2) * (u : ℂ)))) := by
    funext u
    rw [unitRieszCesaroCurvatureKernel]
    push_cast
    have hfastProd : Complex.exp (-(z * (u : ℂ))) * Complex.exp (-(u : ℂ)) =
        Complex.exp (-((z + 1) * (u : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hslowProd : Complex.exp (-(z * (u : ℂ))) *
        Complex.exp (-(u : ℂ) / 2) =
        Complex.exp (-((z + 1 / 2) * (u : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      Complex.exp (-(z * (u : ℂ))) *
          ((3 / 32 : ℂ) * (Complex.exp (-(u : ℂ)) -
            (1 / 4 : ℂ) * Complex.exp (-(u : ℂ) / 2))) =
          (3 / 32 : ℂ) *
              (Complex.exp (-(z * (u : ℂ))) * Complex.exp (-(u : ℂ))) -
            (3 / 128 : ℂ) *
              (Complex.exp (-(z * (u : ℂ))) *
                Complex.exp (-(u : ℂ) / 2)) := by ring
      _ = _ := by rw [hfastProd, hslowProd]
  rw [unitRieszCesaroComplexCompletedReporterSymbol, hpoint]
  have hfastInt : IntegrableOn
      (fun u : ℝ => (3 / 32 : ℂ) * Complex.exp (-((z + 1) * (u : ℂ))))
      (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_cexp_neg_mul hfast).const_mul (3 / 32 : ℂ)
  have hslowInt : IntegrableOn
      (fun u : ℝ => (3 / 128 : ℂ) * Complex.exp (-((z + 1 / 2) * (u : ℂ))))
      (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_cexp_neg_mul hslow).const_mul (3 / 128 : ℂ)
  rw [integral_sub hfastInt hslowInt,
    integral_const_mul, integral_const_mul,
    integral_Ioi_cexp_neg_mul hfast,
    integral_Ioi_cexp_neg_mul hslow]
  field_simp [hfastne, hslowHalfne, hslowne, hslowne']
  have hunit : (1 + z * 2) * (1 + z * 2)⁻¹ = (1 : ℂ) :=
    mul_inv_cancel₀ hslowne'
  linear_combination -4096 * (1 - z) * hunit

/-- The complex reporter erases only the affine mode.  In particular, no nonzero oscillatory or
off-critical exponential in the critical-Mellin half-plane is hidden by FU sign cancellation. -/
theorem unitRieszCesaroComplexCompletedReporterSymbol_eq_zero_iff
    {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    unitRieszCesaroComplexCompletedReporterSymbol z = 0 ↔ z = 0 := by
  rw [unitRieszCesaroComplexCompletedReporterSymbol_eq hz]
  have hfastne : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at hre
    linarith
  have hslowne : 2 * z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re] at hre
    linarith
  simp [hfastne, hslowne]

/-- Positive singular graph multiplier obtained by squaring only after the two signed FU regions
and boundary atom have cancelled jointly. -/
def unitRieszCesaroJointReporterEnergySymbol (z : ℂ) : ℝ :=
  Complex.normSq (unitRieszCesaroComplexCompletedReporterSymbol z)

theorem unitRieszCesaroJointReporterEnergySymbol_nonneg (z : ℂ) :
    0 ≤ unitRieszCesaroJointReporterEnergySymbol z :=
  Complex.normSq_nonneg _

/-- The joint reporter graph energy is strictly coercive on every non-affine complex mode in the
critical-Mellin half-plane.  Positivity is applied after, not before, FU sign cancellation. -/
theorem unitRieszCesaroJointReporterEnergySymbol_pos_iff
    {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    0 < unitRieszCesaroJointReporterEnergySymbol z ↔ z ≠ 0 := by
  rw [unitRieszCesaroJointReporterEnergySymbol, Complex.normSq_pos]
  exact not_congr (unitRieszCesaroComplexCompletedReporterSymbol_eq_zero_iff hz)

end GaloisForLFunctions.RHTower
