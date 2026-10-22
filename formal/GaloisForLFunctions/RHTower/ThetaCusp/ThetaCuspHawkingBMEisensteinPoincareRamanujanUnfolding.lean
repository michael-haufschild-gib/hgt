import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinPoincareAbsoluteConvergence
import GaloisForLFunctions.HTGeometry.LogWeightedPoisson
import GaloisForLFunctions.RHTower.ChenGuptaLiRamanujanFourier
import GaloisForLFunctions.RHTower.ChenGuptaLiAffinePoisson
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

/-!
# Ramanujan--Fourier unfolding of each primitive Eisenstein cusp slice

The convergence module constructs the actual primitive-pair Poincare series.  This module proves
the next quotient-sensitive step.  For each certified positive denominator `c`, its primitive
translation tail is the finite reduced-residue sum of the `L¹` periodization of

`t |-> (y^(2 : ℕ)+t^(2 : ℕ))^(-s)`.

Lean proves the kernel integrable throughout `Re(s)>1`, then unfolds its exact `m`-th unit-circle
Fourier coefficient.  The coefficient is the genuine finite Ramanujan sum `c_c(m)` times the
Euclidean Fourier transform of the one Cauchy-power kernel, with the exact Poincare scaling
`y^s c^(-2s)`.  This uses the corpus `L¹` periodization theorem, so no Schwartz or pointwise
Poisson-summation assumption is inserted.

This closes the reduced-residue/translation part of the Poincare--Fourier equality.  Remaining
analytic core is the exact Gamma--Bessel evaluation of the displayed Euclidean Fourier transform,
followed by summation over `c` and the divisor-series identity.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [RAMANUJAN FOURIER UNFOLDING]`
-/

open Complex Real Finset Filter Topology MeasureTheory Set
open scoped BigOperators NNReal FourierTransform

namespace RHTower
noncomputable section

def d4BMCauchyPowerKernel
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (t : ℝ) : ℂ :=
  ((z.y ^ 2 + t ^ 2 : ℝ) : ℂ) ^ (-s)

def d4BMCauchyPowerCoercivityConstant (z : D4BMUpperHalfPlaneCoordinate) : ℝ :=
  2 * (1 + z.y ^ 2) / z.y ^ 2

lemma d4BMCauchyPowerCoercivityConstant_pos (z : D4BMUpperHalfPlaneCoordinate) :
    0 < d4BMCauchyPowerCoercivityConstant z := by
  unfold d4BMCauchyPowerCoercivityConstant
  exact div_pos (mul_pos (by norm_num) (by positivity)) (sq_pos_of_pos z.y_pos)

lemma d4BM_one_add_abs_sq_le_cauchy_coercivity
    (z : D4BMUpperHalfPlaneCoordinate) (t : ℝ) :
    (1 + |t|) ^ 2 ≤
      d4BMCauchyPowerCoercivityConstant z * (z.y ^ 2 + t ^ 2) := by
  have hy2 : 0 < z.y ^ 2 := sq_pos_of_pos z.y_pos
  have habs2 : |t| ^ 2 = t ^ 2 := sq_abs t
  rw [d4BMCauchyPowerCoercivityConstant, div_mul_eq_mul_div]
  apply (le_div_iff₀ hy2).2
  nlinarith [sq_nonneg (|t| - 1), sq_nonneg z.y,
    sq_nonneg t, mul_nonneg (sq_nonneg z.y) (sq_nonneg t)]

lemma d4BMCauchyPower_rpow_majorized
    (z : D4BMUpperHalfPlaneCoordinate) (sigma : ℝ) (hsigma : 0 ≤ sigma) (t : ℝ) :
    (z.y ^ 2 + t ^ 2) ^ (-sigma) ≤
      d4BMCauchyPowerCoercivityConstant z ^ sigma *
        (1 + |t|) ^ (-(2 * sigma)) := by
  let A : ℝ := 1 + |t|
  let D : ℝ := d4BMCauchyPowerCoercivityConstant z
  let Q : ℝ := z.y ^ 2 + t ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := d4BMCauchyPowerCoercivityConstant_pos z
  have hQ : 0 < Q := by
    dsimp [Q]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg t)
  have hbound : A ^ 2 ≤ D * Q := d4BM_one_add_abs_sq_le_cauchy_coercivity z t
  have hanti : (D * Q) ^ (-sigma) ≤ (A ^ 2) ^ (-sigma) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hA) hbound (by linarith)
  have hfactor : D ^ sigma * (D * Q) ^ (-sigma) = Q ^ (-sigma) := by
    rw [Real.mul_rpow hD.le hQ.le, Real.rpow_neg hD.le,
      Real.rpow_neg hQ.le]
    have hDr : D ^ sigma ≠ 0 := (Real.rpow_pos_of_pos hD sigma).ne'
    have hQr : Q ^ sigma ≠ 0 := (Real.rpow_pos_of_pos hQ sigma).ne'
    field_simp
  have hsquare : (A ^ 2) ^ (-sigma) = A ^ (-(2 * sigma)) := by
    rw [← Real.rpow_natCast A 2, ← Real.rpow_mul hA.le]
    norm_num
  change Q ^ (-sigma) ≤ D ^ sigma * A ^ (-(2 * sigma))
  calc
    Q ^ (-sigma) = D ^ sigma * (D * Q) ^ (-sigma) := hfactor.symm
    _ ≤ D ^ sigma * (A ^ 2) ^ (-sigma) :=
      mul_le_mul_of_nonneg_left hanti (Real.rpow_nonneg hD.le _)
    _ = D ^ sigma * A ^ (-(2 * sigma)) := by rw [hsquare]

theorem norm_d4BMCauchyPowerKernel
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (t : ℝ) :
    ‖d4BMCauchyPowerKernel z s t‖ = (z.y ^ 2 + t ^ 2) ^ (-s.re) := by
  have hQ : 0 < z.y ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg t)
  rw [d4BMCauchyPowerKernel,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

theorem integrable_d4BMCauchyPowerKernel
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Integrable (d4BMCauchyPowerKernel z P.s) := by
  have hsigma : 0 ≤ P.s.re := by linarith [P.re_gt_one]
  have hmaj :=
    GaloisForLFunctions.HTGeometry.integrable_one_add_abs_rpow_three_halves.const_mul
    (d4BMCauchyPowerCoercivityConstant z ^ P.s.re)
  refine hmaj.mono' ?_ ?_
  · have hbase : Continuous (fun t : ℝ => ((z.y ^ 2 + t ^ 2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.pow 2))
    have hcont : Continuous (d4BMCauchyPowerKernel z P.s) := by
      unfold d4BMCauchyPowerKernel
      apply hbase.cpow continuous_const
      intro t
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by
        simp only [ofReal_re]
        exact add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg t))
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    rw [norm_d4BMCauchyPowerKernel]
    refine le_trans (d4BMCauchyPower_rpow_majorized z P.s.re hsigma t) ?_
    refine mul_le_mul_of_nonneg_left ?_
      (Real.rpow_nonneg (d4BMCauchyPowerCoercivityConstant_pos z).le _)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t] : 1 ≤ 1 + |t|) (by
      linarith [P.re_gt_one])

def d4BMReducedResidueCauchyPeriodization
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) (x : ℝ) : ℂ :=
  ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
    GaloisForLFunctions.HTGeometry.l1Periodization
      (d4BMCauchyPowerKernel z P.s) (x + (a.val : ℝ) / Q.value)

lemma d4BM_l1Periodization_add_eq_translated
    (f : ℝ → ℂ) (x a : ℝ) :
    GaloisForLFunctions.HTGeometry.l1Periodization f (x + a) =
      GaloisForLFunctions.HTGeometry.l1Periodization (fun t => f (t + a)) x := by
  unfold GaloisForLFunctions.HTGeometry.l1Periodization
  apply tsum_congr
  intro k
  congr 1
  ring

theorem d4BM_reducedResidue_single_fourierCoefficient
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) (a : ZMod Q.value) (m : ℤ) :
    ∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) *
        GaloisForLFunctions.HTGeometry.l1Periodization
          (d4BMCauchyPowerKernel z P.s) (x + (a.val : ℝ) / Q.value) =
      ZMod.stdAddChar (a * (m : ZMod Q.value)) *
        𝓕 (d4BMCauchyPowerKernel z P.s) (m : ℝ) := by
  let shift : ℝ := (a.val : ℝ) / Q.value
  let g : ℝ → ℂ := fun t => d4BMCauchyPowerKernel z P.s (t + shift)
  have hf := integrable_d4BMCauchyPowerKernel z P
  have hg : Integrable g := hf.comp_add_right shift
  have hcoeff := GaloisForLFunctions.HTGeometry.integral_unit_l1Periodization_mul_fourier_eq
    hg m
  have hperiod : ∀ x : ℝ,
      GaloisForLFunctions.HTGeometry.l1Periodization
          (d4BMCauchyPowerKernel z P.s) (x + shift) =
        GaloisForLFunctions.HTGeometry.l1Periodization g x := by
    intro x
    exact d4BM_l1Periodization_add_eq_translated _ _ _
  rw [show (a.val : ℝ) / Q.value = shift by rfl]
  simp_rw [hperiod]
  rw [hcoeff]
  rw [show g = fun t : ℝ => d4BMCauchyPowerKernel z P.s (t + shift) by rfl,
    GaloisForLFunctions.HTGeometry.fourierIntegral_comp_add_right]
  rw [cglAffineFourierPhase_eq_stdAddChar_mul]
  simp [smul_eq_mul]

theorem d4BM_reducedResiduePeriodization_fourierCoefficient
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) (m : ℤ) :
    ∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) *
        d4BMReducedResidueCauchyPeriodization z P Q x =
      cglRamanujanAdditiveSum Q (m : ZMod Q.value) *
        𝓕 (d4BMCauchyPowerKernel z P.s) (m : ℝ) := by
  let S : Finset (ZMod Q.value) := Finset.univ.filter IsUnit
  let F : ZMod Q.value → ℝ → ℂ := fun a x =>
    fourier (-m) (x : UnitAddCircle) *
      GaloisForLFunctions.HTGeometry.l1Periodization
        (d4BMCauchyPowerKernel z P.s) (x + (a.val : ℝ) / Q.value)
  have hFint : ∀ a ∈ S, Integrable (F a) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro a ha
    let shift : ℝ := (a.val : ℝ) / Q.value
    let g : ℝ → ℂ := fun t => d4BMCauchyPowerKernel z P.s (t + shift)
    have hg : Integrable g := (integrable_d4BMCauchyPowerKernel z P).comp_add_right shift
    have hp := GaloisForLFunctions.HTGeometry.integrableOn_Ioc_l1Periodization hg
    have hecont : Continuous (fun x : ℝ => fourier (-m) (x : UnitAddCircle)) := by fun_prop
    have henorm : ∀ x : ℝ, ‖fourier (-m) (x : UnitAddCircle)‖ ≤ 1 := by
      intro x
      rw [fourier_coe_apply, Complex.norm_exp]
      simp
    have hperiod : ∀ x : ℝ,
        GaloisForLFunctions.HTGeometry.l1Periodization
            (d4BMCauchyPowerKernel z P.s) (x + shift) =
          GaloisForLFunctions.HTGeometry.l1Periodization g x := by
      intro x
      exact d4BM_l1Periodization_add_eq_translated _ _ _
    have hprod := hp.bdd_mul hecont.aestronglyMeasurable.restrict
      (Eventually.of_forall henorm)
    change Integrable (F a) (volume.restrict (Set.Ioc (0 : ℝ) 1))
    apply hprod.congr
    filter_upwards with x
    simp only [F]
    rw [show (a.val : ℝ) / Q.value = shift by rfl, hperiod]
  change (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) *
        (∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
          GaloisForLFunctions.HTGeometry.l1Periodization
            (d4BMCauchyPowerKernel z P.s) (x + (a.val : ℝ) / Q.value))) = _
  have hfun : (fun x : ℝ => fourier (-m) (x : UnitAddCircle) *
      ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
        GaloisForLFunctions.HTGeometry.l1Periodization
          (d4BMCauchyPowerKernel z P.s) (x + (a.val : ℝ) / Q.value)) =
      fun x : ℝ => ∑ a ∈ S, F a x := by
    funext x
    dsimp [S, F]
    rw [Finset.mul_sum]
  rw [hfun]
  change (∫ x : ℝ, ∑ a ∈ S, F a x ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) = _
  rw [MeasureTheory.integral_finsetSum S hFint]
  unfold cglRamanujanAdditiveSum
  change (∑ a ∈ S, ∫ x in Set.Ioc (0 : ℝ) 1, F a x) =
    (∑ a ∈ S, ZMod.stdAddChar (a * (m : ZMod Q.value))) *
      𝓕 (d4BMCauchyPowerKernel z P.s) (m : ℝ)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  exact d4BM_reducedResidue_single_fourierCoefficient z P Q a m

def d4BMPositivePrimitiveCuspSlice
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) (x : ℝ) : ℂ :=
  (z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s)) *
    d4BMReducedResidueCauchyPeriodization z P Q x

theorem d4BM_positivePrimitiveCuspSlice_fourierCoefficient
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) (m : ℤ) :
    ∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) * d4BMPositivePrimitiveCuspSlice z P Q x =
      ((z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s))) *
        cglRamanujanAdditiveSum Q (m : ZMod Q.value) *
          𝓕 (d4BMCauchyPowerKernel z P.s) (m : ℝ) := by
  let C : ℂ := (z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s))
  have hcoeff := d4BM_reducedResiduePeriodization_fourierCoefficient z P Q m
  change (∫ x in Set.Ioc (0 : ℝ) 1,
    fourier (-m) (x : UnitAddCircle) *
      (C * d4BMReducedResidueCauchyPeriodization z P Q x)) = _
  rw [show (fun x : ℝ => fourier (-m) (x : UnitAddCircle) *
      (C * d4BMReducedResidueCauchyPeriodization z P Q x)) =
      fun x : ℝ => C * (fourier (-m) (x : UnitAddCircle) *
        d4BMReducedResidueCauchyPeriodization z P Q x) by
    funext x
    ring]
  rw [MeasureTheory.integral_const_mul]
  change C * (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) *
        d4BMReducedResidueCauchyPeriodization z P Q x) = _
  rw [hcoeff]
  ring

end
end RHTower
