import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCesaroSignedReporterSymbol

/-!
# Source-relative finite CCM-FU reporter

The actual FU transport has a positive lower source wall `b`, so its lag integral stops at `t-b`.
Replacing that aperture by `t` falsely erases a boundary jet.  This module retains the literal
aperture and proves the exact exponential-mode law

```text
R_{b,t}(a)
  = c_t exp(-a(t-b)) (G_t'(b) - a G_t(b))
      - c_t a² ∫_b^t exp(-a(t-s)) G_t(s) ds.
```

Here `c_t = exp(t/2)/t³` and `G_t` is strictly positive in the open aperture.  The endpoint atom
still cancels exactly, while the escaped lower-wall value and first jet remain visible.  Thus the
full-aperture negative symbol is source-faithful only after this coefficient-bearing boundary jet
is transported or cancelled; discarding it would not be a valid CCM-FU mechanism.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Completed reporter symbol on the literal source-relative aperture `[0, t-b]`. -/
def unitRieszCesaroSourceRelativeCompletedReporterSymbol (b t a : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..(t - b),
    Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u) - 3 / 64

/-- Coefficient-bearing value/first-jet term escaping through the positive lower source wall. -/
def unitRieszCesaroSourceRelativeEscapedJet (b t a : ℝ) : ℝ :=
  Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-(a * (t - b))) *
    (unitRieszCesaroTestDeriv t b - a * unitRieszCesaroTest t b)

/-- Literal contribution before the finite reporter's unique moving wall. -/
def unitRieszCesaroSourceRelativePositiveRegionSymbol (t a : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..unitRieszCesaroWall t,
    Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u

/-- Magnitude of the literal contribution after the moving wall and before the actual source
aperture `t-b`. -/
def unitRieszCesaroSourceRelativeNegativeRegionSymbol (b t a : ℝ) : ℝ :=
  ∫ u in unitRieszCesaroWall t..(t - b),
    -(Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u)

theorem unitRieszCesaroSourceRelativePositiveRegionSymbol_nonneg
    {t : ℝ} (ht : 0 < t) (a : ℝ) :
    0 ≤ unitRieszCesaroSourceRelativePositiveRegionSymbol t a := by
  rw [unitRieszCesaroSourceRelativePositiveRegionSymbol]
  refine intervalIntegral.integral_nonneg (unitRieszCesaroWall_pos ht).le ?_
  intro u hu
  by_cases huw : u = unitRieszCesaroWall t
  · subst u
    rw [unitRieszCesaroApertureKernel_wall ht]
    simp
  · exact mul_nonneg (Real.exp_pos _).le
      (unitRieszCesaroApertureKernel_pos_of_lt_wall ht hu.1
        (lt_of_le_of_ne hu.2 huw)).le

theorem unitRieszCesaroSourceRelativeNegativeRegionSymbol_nonneg
    {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (hwall : unitRieszCesaroWall t ≤ t - b) (a : ℝ) :
    0 ≤ unitRieszCesaroSourceRelativeNegativeRegionSymbol b t a := by
  rw [unitRieszCesaroSourceRelativeNegativeRegionSymbol]
  refine intervalIntegral.integral_nonneg hwall ?_
  intro u hu
  by_cases huw : u = unitRieszCesaroWall t
  · subst u
    rw [unitRieszCesaroApertureKernel_wall ht]
    simp
  · have hwu : unitRieszCesaroWall t < u := lt_of_le_of_ne hu.1 (Ne.symm huw)
    have hut : u < t := lt_of_le_of_lt hu.2 (by linarith)
    have hk := unitRieszCesaroApertureKernel_neg_of_wall_lt ht hwu hut
    have he := Real.exp_pos (-(a * u))
    nlinarith

/-- Beyond the explicit `b + log 16` threshold, the actual source aperture contains both sides of
the moving reporter wall, and both Jordan masses are nonnegative. -/
theorem unitRieszCesaroSourceRelative_regionSymbols_nonneg_of_cofinal
    {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (hcofinal : b + Real.log 16 ≤ t) (a : ℝ) :
    0 ≤ unitRieszCesaroSourceRelativePositiveRegionSymbol t a ∧
      0 ≤ unitRieszCesaroSourceRelativeNegativeRegionSymbol b t a := by
  have hwall : unitRieszCesaroWall t ≤ t - b := by
    have hw := unitRieszCesaroWall_lt_log_sixteen ht
    linarith
  exact ⟨unitRieszCesaroSourceRelativePositiveRegionSymbol_nonneg ht a,
    unitRieszCesaroSourceRelativeNegativeRegionSymbol_nonneg hb ht hwall a⟩

/-- Literal source-relative Jordan decomposition.  Positive and negative reporter regions stay in
one signed identity; neither is estimated by an absolute envelope. -/
theorem unitRieszCesaroSourceRelativeCompletedReporterSymbol_eq_regions
    (b t a : ℝ) :
    unitRieszCesaroSourceRelativeCompletedReporterSymbol b t a =
      unitRieszCesaroSourceRelativePositiveRegionSymbol t a -
        unitRieszCesaroSourceRelativeNegativeRegionSymbol b t a - 3 / 64 := by
  let f : ℝ → ℝ := fun u =>
    Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u
  have hcont : Continuous f := by
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-(a * u)))).mul
      (continuous_unitRieszCesaroApertureKernel t)
  have hleft : IntervalIntegrable f volume 0 (unitRieszCesaroWall t) :=
    hcont.intervalIntegrable _ _
  have hright : IntervalIntegrable f volume (unitRieszCesaroWall t) (t - b) :=
    hcont.intervalIntegrable _ _
  rw [unitRieszCesaroSourceRelativeCompletedReporterSymbol,
    unitRieszCesaroSourceRelativePositiveRegionSymbol,
    unitRieszCesaroSourceRelativeNegativeRegionSymbol]
  change (∫ u in (0 : ℝ)..(t - b), f u) - 3 / 64 =
    (∫ u in (0 : ℝ)..unitRieszCesaroWall t, f u) -
      (∫ u in unitRieszCesaroWall t..(t - b), -f u) - 3 / 64
  rw [intervalIntegral.integral_neg,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  ring

/-- Exact source-relative cancellation law.  The top endpoint derivative cancels the completed
boundary atom, but the value/first-jet pair at the actual lower source wall survives. -/
theorem unitRieszCesaroSourceRelativeCompletedReporterSymbol_eq
    {t : ℝ} (ht : 0 < t) (b a : ℝ) :
    unitRieszCesaroSourceRelativeCompletedReporterSymbol b t a =
      Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-(a * (t - b))) *
          (unitRieszCesaroTestDeriv t b - a * unitRieszCesaroTest t b) -
        Real.exp (t / 2) / t ^ (3 : ℕ) * a ^ (2 : ℕ) *
          ∫ s in b..t,
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
  have hG (s : ℝ) : HasDerivAt G (G' s) s :=
    hasDerivAt_unitRieszCesaroTest t s
  have hG' (s : ℝ) : HasDerivAt G' (G'' s) s :=
    hasDerivAt_unitRieszCesaroTestDeriv t s
  let F : ℝ → ℝ := fun s => f s * G' s - a * f s * G s
  have hF (s : ℝ) : HasDerivAt F
      (f s * G'' s - a ^ (2 : ℕ) * f s * G s) s := by
    have hleft := (hf s).mul (hG' s)
    have hright := ((hf s).mul (hG s)).const_mul a
    have hraw := hleft.sub hright
    have hderiv :
        a * f s * G' s + f s * G'' s -
            a * (a * f s * G s + f s * G' s) =
          f s * G'' s - a ^ (2 : ℕ) * f s * G s := by
      ring
    have hraw' := hraw.congr_deriv hderiv
    change HasDerivAt
      (fun x => f x * G' x - a * f x * G x)
      (f s * G'' s - a ^ (2 : ℕ) * f s * G s) s
    apply hraw'.congr_of_eventuallyEq
    filter_upwards with x
    simp only [Pi.mul_apply, Pi.sub_apply, mul_assoc]
  have hfirstInt : IntervalIntegrable (fun s : ℝ => f s * G'' s) volume b t := by
    apply Continuous.intervalIntegrable
    dsimp only [f, G'']
    exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (-(a * (t - s))))).mul
      (continuous_unitRieszCesaroTestSecondDeriv t)
  have hsecondInt : IntervalIntegrable
      (fun s : ℝ => a ^ (2 : ℕ) * f s * G s) volume b t := by
    apply Continuous.intervalIntegrable
    dsimp only [f, G]
    have hc := ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-(a * (t - s))))).mul
      (continuous_unitRieszCesaroTest t)).const_mul (a ^ (2 : ℕ))
    simpa only [Pi.mul_apply, mul_assoc] using hc
  have hderivInt : IntervalIntegrable
      (fun s : ℝ => f s * G'' s - a ^ (2 : ℕ) * f s * G s) volume b t :=
    hfirstInt.sub hsecondInt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hF s) hderivInt
  rw [intervalIntegral.integral_sub hfirstInt hsecondInt] at hftc
  have hsecondEq :
      (∫ s in b..t, a ^ (2 : ℕ) * f s * G s) =
        a ^ (2 : ℕ) * ∫ s in b..t, f s * G s := by
    rw [show (fun s : ℝ => a ^ (2 : ℕ) * f s * G s) =
        fun s : ℝ => a ^ (2 : ℕ) * (f s * G s) by funext s; ring,
      intervalIntegral.integral_const_mul]
  rw [hsecondEq] at hftc
  have hGt : G t = 0 := unitRieszCesaroTest_self t
  have hG't : G' t = -(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2) :=
    unitRieszCesaroTestDeriv_endpoint t
  have hft : f t = 1 := by simp [f]
  have hftc' :
      (∫ s in b..t, f s * G'' s) =
        -(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2) -
            f b * G' b + a * f b * G b +
          a ^ (2 : ℕ) * ∫ s in b..t, f s * G s := by
    dsimp only [F] at hftc
    rw [hGt, hG't, hft] at hftc
    simp only [mul_zero, sub_zero] at hftc
    linarith
  let H : ℝ → ℝ := fun u =>
    Real.exp (-(a * u)) * unitRieszCesaroApertureKernel t u
  have hcv : (∫ u in (0 : ℝ)..(t - b), H u) =
      ∫ s in b..t, H (t - s) := by
    simpa using (intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := t - b) H t).symm
  have hkernel : ∀ s : ℝ,
      H (t - s) = -(Real.exp (t / 2) / t ^ (3 : ℕ)) * (f s * G'' s) := by
    intro s
    dsimp only [H, f, G'']
    rw [unitRieszCesaroApertureKernel_eq_secondDeriv]
    rw [show t - (t - s) = s by ring]
    ring
  rw [unitRieszCesaroSourceRelativeCompletedReporterSymbol]
  change (∫ u in (0 : ℝ)..(t - b), H u) - 3 / 64 = _
  rw [hcv]
  simp_rw [hkernel]
  rw [intervalIntegral.integral_const_mul, hftc']
  have ht3 : t ^ (3 : ℕ) ≠ 0 := by positivity
  have hexp : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add, show t / 2 + -t / 2 = (0 : ℝ) by ring, Real.exp_zero]
  dsimp only [f, G, G']
  have hboundary :
      -(Real.exp (t / 2) / t ^ (3 : ℕ)) *
          (-(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2)) = 3 / 64 := by
    calc
      _ = (3 / 64 : ℝ) *
          (Real.exp (t / 2) * Real.exp (-t / 2)) * (t ^ (3 : ℕ) / t ^ (3 : ℕ)) := by ring
      _ = _ := by rw [hexp, div_self ht3]; ring
  linear_combination hboundary

/-- Source-relative symbol as escaped boundary jet minus positive-test curvature response. -/
theorem unitRieszCesaroSourceRelativeCompletedReporterSymbol_eq_escapedJet_sub
    {t : ℝ} (ht : 0 < t) (b a : ℝ) :
    unitRieszCesaroSourceRelativeCompletedReporterSymbol b t a =
      unitRieszCesaroSourceRelativeEscapedJet b t a -
        Real.exp (t / 2) / t ^ (3 : ℕ) * a ^ (2 : ℕ) *
          ∫ s in b..t,
            Real.exp (-(a * (t - s))) * unitRieszCesaroTest t s := by
  rw [unitRieszCesaroSourceRelativeCompletedReporterSymbol_eq ht,
    unitRieszCesaroSourceRelativeEscapedJet]

/-- Exact two-rate formula for the escaped lower-wall jet. -/
theorem unitRieszCesaroSourceRelativeEscapedJet_eq (b t a : ℝ) :
    unitRieszCesaroSourceRelativeEscapedJet b t a =
      (3 / 32 : ℝ) / t ^ (3 : ℕ) *
        ((3 * b ^ (2 : ℕ) + (1 / 2 - a) * b ^ (3 : ℕ)) *
            Real.exp (-((a + 1 / 2) * (t - b))) -
          (3 * b ^ (2 : ℕ) + (1 - a) * b ^ (3 : ℕ)) *
            Real.exp (-((a + 1) * (t - b)))) := by
  rw [unitRieszCesaroSourceRelativeEscapedJet,
    unitRieszCesaroTestDeriv, unitRieszCesaroTest]
  have hslow : Real.exp (t / 2) * Real.exp (-(a * (t - b))) *
        Real.exp (-t + b / 2) =
      Real.exp (-((a + 1 / 2) * (t - b))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hfast : Real.exp (t / 2) * Real.exp (-(a * (t - b))) *
        Real.exp (-3 * t / 2 + b) =
      Real.exp (-((a + 1) * (t - b))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-(a * (t - b))) =
      (Real.exp (t / 2) * Real.exp (-(a * (t - b)))) / t ^ (3 : ℕ) by ring]
  rw [show (Real.exp (t / 2) * Real.exp (-(a * (t - b)))) / t ^ (3 : ℕ) *
      ((3 / 32) *
        (3 * b ^ (2 : ℕ) * (Real.exp (-t + b / 2) - Real.exp (-3 * t / 2 + b)) +
          b ^ (3 : ℕ) * ((1 / 2) * Real.exp (-t + b / 2) -
            Real.exp (-3 * t / 2 + b))) -
        a * ((3 / 32) *
          (b ^ (3 : ℕ) * (Real.exp (-t + b / 2) - Real.exp (-3 * t / 2 + b))))) =
      (3 / 32 : ℝ) / t ^ (3 : ℕ) *
        ((3 * b ^ (2 : ℕ) + (1 / 2 - a) * b ^ (3 : ℕ)) *
            ((Real.exp (t / 2) * Real.exp (-(a * (t - b)))) *
              Real.exp (-t + b / 2)) -
          (3 * b ^ (2 : ℕ) + (1 - a) * b ^ (3 : ℕ)) *
            ((Real.exp (t / 2) * Real.exp (-(a * (t - b)))) *
              Real.exp (-3 * t / 2 + b))) by ring]
  rw [hslow, hfast]

/-- The actual lower-wall jet vanishes cofinally throughout the real critical-Mellin half-plane.
Thus positive-wall source fidelity does not weaken the asymptotic `-a²` detector. -/
theorem tendsto_unitRieszCesaroSourceRelativeEscapedJet_zero
    (b : ℝ) {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    Tendsto (fun t : ℝ => unitRieszCesaroSourceRelativeEscapedJet b t a)
      atTop (nhds 0) := by
  rw [show (fun t : ℝ => unitRieszCesaroSourceRelativeEscapedJet b t a) = fun t =>
      (3 / 32 : ℝ) / t ^ (3 : ℕ) *
        ((3 * b ^ (2 : ℕ) + (1 / 2 - a) * b ^ (3 : ℕ)) *
            Real.exp (-((a + 1 / 2) * (t - b))) -
          (3 * b ^ (2 : ℕ) + (1 - a) * b ^ (3 : ℕ)) *
            Real.exp (-((a + 1) * (t - b)))) by
    funext t
    exact unitRieszCesaroSourceRelativeEscapedJet_eq b t a]
  have hslowPos : 0 < a + 1 / 2 := by linarith
  have hfastPos : 0 < a + 1 := by linarith
  have hdecay (c : ℝ) (hc : 0 < c) :
      Tendsto (fun t : ℝ => Real.exp (-(c * (t - b)))) atTop (nhds 0) := by
    have hscale : Tendsto (fun t : ℝ => c * (t - b)) atTop atTop :=
      Filter.tendsto_atTop_atTop_of_monotone
        (fun x y hxy => by nlinarith)
        (fun y => ⟨y / c + b, by field_simp; nlinarith⟩)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hslow := hdecay (a + 1 / 2) hslowPos
  have hfast := hdecay (a + 1) hfastPos
  have hbracket : Tendsto (fun t : ℝ =>
      (3 * b ^ (2 : ℕ) + (1 / 2 - a) * b ^ (3 : ℕ)) *
          Real.exp (-((a + 1 / 2) * (t - b))) -
        (3 * b ^ (2 : ℕ) + (1 - a) * b ^ (3 : ℕ)) *
          Real.exp (-((a + 1) * (t - b)))) atTop (nhds 0) := by
    convert hslow.const_mul (3 * b ^ (2 : ℕ) + (1 / 2 - a) * b ^ (3 : ℕ)) |>.sub
      (hfast.const_mul (3 * b ^ (2 : ℕ) + (1 - a) * b ^ (3 : ℕ))) using 1 <;> ring
  have hinv : Tendsto (fun t : ℝ => (3 / 32 : ℝ) / t ^ (3 : ℕ))
      atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero ( 𝕜 := ℝ)).pow 3 |>.const_mul (3 / 32 : ℝ)
    simpa [div_eq_mul_inv] using h
  convert hinv.mul hbracket using 1 <;> ring

end GaloisForLFunctions.RHTower
