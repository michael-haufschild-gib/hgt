import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWindowGramSquare

/-!
# Cubic Ward primitive spectral-floor tail obstruction

P-G186 places the primitive Burnol-window columns and completed-Xi conormal columns in the same
unweighted radial `L²(dL)` space.  Their real decay rates nevertheless occupy disjoint chambers:
every primitive Euler rate is at least `log 2`, while every strict-right Xi centered rate is below
`1/2`.

This module proves the exact cubic tail integral and the resulting exponential-rate separation.
In particular, no finite scalar multiple of the primitive spectral-floor tail can dominate even
one strict-right Xi conormal tail.  This is the analytic core of the bare primitive
Douglas-range no-go: a completed source-to-divisor construction must introduce a genuine signed
polar--Gamma boundary transport before comparing Grams; it cannot identify target columns with
the uncompleted primitive synthesis range.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Exact squared `L²(dL)` tail of the cubic conormal aperture column with real decay
`lambda`. -/
def xiWardCubicConormalTailEnergy (lambda R : ℝ) : ℝ :=
  Real.exp (-2 * lambda * R) *
    (R ^ 2 / (2 * lambda) + R / (2 * lambda ^ 2) + 1 / (4 * lambda ^ 3))

/-- Exact tail integral of one cubic conormal radial profile. -/
theorem integral_Ioi_sq_mul_exp_neg_two_mul
    {lambda R : ℝ} (hlambda : 0 < lambda) (hR : 0 ≤ R) :
    (∫ L : ℝ in Set.Ioi R, L ^ 2 * Real.exp (-2 * lambda * L)) =
      xiWardCubicConormalTailEnergy lambda R := by
  let F : ℝ → ℝ :=
    -((fun L : ℝ => Real.exp (-2 * lambda * L)) *
      (fun L : ℝ =>
        L ^ 2 / (2 * lambda) + L / (2 * lambda ^ 2) + 1 / (4 * lambda ^ 3)))
  have hderiv : ∀ L ∈ Set.Ioi R,
      HasDerivAt F (L ^ 2 * Real.exp (-2 * lambda * L)) L := by
    intro L _hL
    have he : HasDerivAt (fun x : ℝ => Real.exp (-2 * lambda * x))
        ((-2 * lambda) * Real.exp (-2 * lambda * L)) L := by
      have hlin := (hasDerivAt_id L).const_mul (-2 * lambda)
      simpa [mul_comm] using hlin.exp
    have hp : HasDerivAt
        (fun x : ℝ => x ^ 2 / (2 * lambda) + x / (2 * lambda ^ 2) +
          1 / (4 * lambda ^ 3))
        (2 * L / (2 * lambda) + 1 / (2 * lambda ^ 2)) L := by
      have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * L) L := by
        simpa using (hasDerivAt_pow 2 L)
      exact ((hsq.div_const (2 * lambda)).add
        ((hasDerivAt_id L).div_const (2 * lambda ^ 2))).add_const
          (1 / (4 * lambda ^ 3))
    have hraw := (he.mul hp).neg
    have hgood := hraw.congr_deriv
      (g' := L ^ 2 * Real.exp (-2 * lambda * L)) (by
      field_simp [hlambda.ne']
      ring)
    simpa only [F] using hgood
  have hfull : MeasureTheory.IntegrableOn
      (fun L : ℝ => L ^ 2 * Real.exp (-2 * lambda * L)) (Set.Ioi 0) := by
    have hvalue := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (3 : ℝ)) (r := 2 * lambda) (by norm_num) (by positivity)
    have hne :
        (∫ L : ℝ in Set.Ioi 0,
          L ^ ((3 : ℝ) - 1) * Real.exp (-((2 * lambda) * L))) ≠ 0 := by
      rw [hvalue]
      positivity
    have hi : MeasureTheory.IntegrableOn
        (fun L : ℝ => L ^ ((3 : ℝ) - 1) * Real.exp (-((2 * lambda) * L)))
        (Set.Ioi 0) := .of_integral_ne_zero hne
    convert hi using 1
    funext L
    norm_num
  have hint : MeasureTheory.IntegrableOn
      (fun L : ℝ => L ^ 2 * Real.exp (-2 * lambda * L)) (Set.Ioi R) :=
    hfull.mono_set (by intro L hL; exact lt_of_le_of_lt hR hL)
  have h0 : Tendsto (fun L : ℝ => Real.exp (-(2 * lambda) * L)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2 * lambda) (by positivity))
  have h1 : Tendsto (fun L : ℝ => L * Real.exp (-(2 * lambda) * L)) atTop
      (nhds 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 * lambda) (by positivity))
  have h2 : Tendsto (fun L : ℝ => L ^ 2 * Real.exp (-(2 * lambda) * L)) atTop
      (nhds 0) := by
    simpa only [Real.rpow_two] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (2 * lambda) (by positivity))
  have hF : Tendsto F atTop (nhds 0) := by
    have hsum := (((h2.const_mul (1 / (2 * lambda))).add
      (h1.const_mul (1 / (2 * lambda ^ 2)))).add
        (h0.const_mul (1 / (4 * lambda ^ 3)))).neg
    have heq : (∀ᶠ L : ℝ in atTop,
        F L = -(1 / (2 * lambda) * (L ^ 2 * Real.exp (-(2 * lambda) * L)) +
          1 / (2 * lambda ^ 2) * (L * Real.exp (-(2 * lambda) * L)) +
          1 / (4 * lambda ^ 3) * Real.exp (-(2 * lambda) * L))) := by
      filter_upwards with L
      dsimp [F]
      ring
    simpa using hsum.congr' (Filter.EventuallyEq.symm heq)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (f' := fun L : ℝ => L ^ 2 * Real.exp (-2 * lambda * L))
    (a := R) (m := 0) (by dsimp [F]; fun_prop) hderiv hint hF
  rw [h]
  dsimp [F, xiWardCubicConormalTailEnergy]
  ring

/-- Squared exponential tail rate of a cubic conormal column. -/
def xiWardCubicConormalExponentialTail (lambda R : ℝ) : ℝ :=
  Real.exp (-2 * lambda * R)

/-- A slower conormal exponential dominates a faster one by an unbounded ratio. -/
theorem xiWardCubicConormalExponentialTail_ratio_tendsto_atTop
    {a lambda : ℝ} (hgap : a < lambda) :
    Tendsto
      (fun R : ℝ =>
        xiWardCubicConormalExponentialTail a R /
          xiWardCubicConormalExponentialTail lambda R)
      atTop atTop := by
  have hrate : 0 < 2 * (lambda - a) := by linarith
  have hlinear : Tendsto (fun R : ℝ => 2 * (lambda - a) * R) atTop atTop :=
    tendsto_id.const_mul_atTop hrate
  have hexp := Real.tendsto_exp_atTop.comp hlinear
  convert hexp using 1
  funext R
  rw [xiWardCubicConormalExponentialTail,
    xiWardCubicConormalExponentialTail, ← Real.exp_sub]
  congr 1
  ring

/-- No finite scalar can dominate the slower conormal tail by the faster tail. -/
theorem not_exists_uniform_xiWardCubicConormalExponentialTail_domination
    {a lambda : ℝ} (hgap : a < lambda) :
    ¬ ∃ C : ℝ, ∀ R : ℝ,
      xiWardCubicConormalExponentialTail a R ≤
        C * xiWardCubicConormalExponentialTail lambda R := by
  rintro ⟨C, hC⟩
  have hratio := xiWardCubicConormalExponentialTail_ratio_tendsto_atTop hgap
  have hlarge := hratio.eventually_ge_atTop (C + 1)
  obtain ⟨R, hR⟩ := hlarge.exists
  have hbound := hC R
  have hpos : 0 < xiWardCubicConormalExponentialTail lambda R :=
    Real.exp_pos _
  have hquot :
      xiWardCubicConormalExponentialTail a R /
          xiWardCubicConormalExponentialTail lambda R ≤ C := by
    exact (div_le_iff₀ hpos).2 hbound
  linarith

/-- Every strict-right Xi copy has a slower cubic-conormal tail than the primitive Euler
spectral floor `log 2`. -/
theorem xiWardCubicStrictRightZero_tail_ratio_tendsto_atTop
    (q : XiRightZeroCopy) :
    Tendsto
      (fun R : ℝ =>
        xiWardCubicConormalExponentialTail (xiRightCenteredZero q).re R /
          xiWardCubicConormalExponentialTail (Real.log 2) R)
      atTop atTop := by
  apply xiWardCubicConormalExponentialTail_ratio_tendsto_atTop
  have hhalf : (xiRightCenteredZero q).re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  have hlog : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  linarith

/-- The primitive spectral-floor exponential cannot uniformly dominate even one strict-right Xi
conormal exponential. -/
theorem not_exists_uniform_primitiveFloor_domination_of_strictRightZero
    (q : XiRightZeroCopy) :
    ¬ ∃ C : ℝ, ∀ R : ℝ,
      xiWardCubicConormalExponentialTail (xiRightCenteredZero q).re R ≤
        C * xiWardCubicConormalExponentialTail (Real.log 2) R := by
  apply not_exists_uniform_xiWardCubicConormalExponentialTail_domination
  have hhalf : (xiRightCenteredZero q).re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  have hlog : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  linarith

end

end RHTower
