import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.FuchsProlateScale
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenCurvatureGap
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenPopescuCorrection
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodGapCumulantRiccati
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

open Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

def thetaCuspResidualScale (a : ℝ) : ℝ := Real.pi * Real.exp (2 * a)

def thetaCuspHalfDensityTailPlus (a : ℝ) : ℝ :=
  ∫ x in Ici a, Real.exp (x / 2) * thetaCuspSourceTerm x 1

def thetaCuspHalfDensityTailMinus (a : ℝ) : ℝ :=
  ∫ x in Ici a, Real.exp (-x / 2) * thetaCuspSourceTerm x 1

def thetaCuspHalfDensityTailPlusPrimitive (a : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (3 * a) * Real.exp (-thetaCuspResidualScale a)

def thetaCuspHalfDensityTailMinusPrimitive (a : ℝ) : ℝ :=
  (2 * thetaCuspResidualScale a - 1) * Real.exp (-thetaCuspResidualScale a)

theorem hasDerivAt_thetaCuspHalfDensityTailPlusPrimitive (a : ℝ) :
    HasDerivAt thetaCuspHalfDensityTailPlusPrimitive
      (-Real.exp (a / 2) * thetaCuspSourceTerm a 1) a := by
  have he2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x))
      (2 * Real.exp (2 * a)) a := by
    change HasDerivAt (Real.exp ∘ fun x : ℝ => 2 * x) _ a
    apply ((Real.hasDerivAt_exp (2 * a)).comp a ((hasDerivAt_id a).const_mul 2)).congr_deriv
    ring
  have hq : HasDerivAt (fun x : ℝ => Real.pi * Real.exp (2 * x))
      (2 * Real.pi * Real.exp (2 * a)) a := by
    exact (he2.const_mul Real.pi).congr_deriv (by ring)
  have he3 : HasDerivAt (fun x : ℝ => Real.exp (3 * x))
      (3 * Real.exp (3 * a)) a := by
    change HasDerivAt (Real.exp ∘ fun x : ℝ => 3 * x) _ a
    apply ((Real.hasDerivAt_exp (3 * a)).comp a ((hasDerivAt_id a).const_mul 3)).congr_deriv
    ring
  have heneg : HasDerivAt (fun x : ℝ => Real.exp (-(Real.pi * Real.exp (2 * x))))
      (-(2 * Real.pi * Real.exp (2 * a)) * Real.exp (-(Real.pi * Real.exp (2 * a)))) a := by
    change HasDerivAt (Real.exp ∘ fun x : ℝ => -(Real.pi * Real.exp (2 * x))) _ a
    exact ((Real.hasDerivAt_exp _).comp a hq.neg).congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hhalf2 : Real.exp (a * (1 / 2)) ^ 2 = Real.exp a := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ha2 : Real.exp a ^ 2 = Real.exp (a * 2) := by
    rw [← Real.exp_nat_mul]
    ring
  have ha3 : Real.exp a ^ 3 = Real.exp (a * 3) := by
    rw [← Real.exp_nat_mul]
    ring
  have ha4 : Real.exp a ^ 4 = Real.exp (a * 4) := by
    rw [← Real.exp_nat_mul]
    ring
  have h12 : Real.exp a * Real.exp (a * 2) = Real.exp (a * 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h32 : Real.exp (a * 3) * Real.exp (a * 2) = Real.exp (a * 5) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h14 : Real.exp a * Real.exp (a * 4) = Real.exp (a * 5) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp (a * 3) * Real.exp (a * 2) =
      Real.exp a * Real.exp (a * 4) := h32.trans h14.symm
  unfold thetaCuspHalfDensityTailPlusPrimitive thetaCuspResidualScale
  change HasDerivAt
    ((fun x : ℝ => 2 * Real.pi * Real.exp (3 * x)) *
      fun x : ℝ => Real.exp (-(Real.pi * Real.exp (2 * x)))) _ a
  apply ((he3.const_mul (2 * Real.pi)).mul heneg).congr_deriv
  unfold thetaCuspSourceTerm thetaCuspSeed
  ring_nf
  rw [hhalf2, ha2, ha4]
  have hfirst : Real.pi * Real.exp (a * 3) * Real.exp (-(Real.pi * Real.exp (a * 2))) * 6 =
      Real.pi * Real.exp a * Real.exp (a * 2) *
        Real.exp (-(Real.pi * Real.exp (a * 2))) * 6 := by
    calc
      _ = (Real.pi * Real.exp (-(Real.pi * Real.exp (a * 2))) * 6) *
          Real.exp (a * 3) := by ring
      _ = (Real.pi * Real.exp (-(Real.pi * Real.exp (a * 2))) * 6) *
          (Real.exp a * Real.exp (a * 2)) := by rw [h12]
      _ = _ := by ring
  have hsecond : Real.pi ^ 2 * Real.exp (a * 3) * Real.exp (a * 2) *
        Real.exp (-(Real.pi * Real.exp (a * 2))) * 4 =
      Real.pi ^ 2 * Real.exp a * Real.exp (a * 4) *
        Real.exp (-(Real.pi * Real.exp (a * 2))) * 4 := by
    calc
      _ = (Real.pi ^ 2 * Real.exp (-(Real.pi * Real.exp (a * 2))) * 4) *
          (Real.exp (a * 3) * Real.exp (a * 2)) := by ring
      _ = (Real.pi ^ 2 * Real.exp (-(Real.pi * Real.exp (a * 2))) * 4) *
          (Real.exp a * Real.exp (a * 4)) := by rw [hprod]
      _ = _ := by ring
  rw [hfirst, hsecond]

theorem hasDerivAt_thetaCuspHalfDensityTailMinusPrimitive (a : ℝ) :
    HasDerivAt thetaCuspHalfDensityTailMinusPrimitive
      (-Real.exp (-a / 2) * thetaCuspSourceTerm a 1) a := by
  have he2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x))
      (2 * Real.exp (2 * a)) a := by
    change HasDerivAt (Real.exp ∘ fun x : ℝ => 2 * x) _ a
    apply ((Real.hasDerivAt_exp (2 * a)).comp a ((hasDerivAt_id a).const_mul 2)).congr_deriv
    ring
  have hq : HasDerivAt (fun x : ℝ => Real.pi * Real.exp (2 * x))
      (2 * Real.pi * Real.exp (2 * a)) a := by
    exact (he2.const_mul Real.pi).congr_deriv (by ring)
  have heneg : HasDerivAt (fun x : ℝ => Real.exp (-(Real.pi * Real.exp (2 * x))))
      (-(2 * Real.pi * Real.exp (2 * a)) * Real.exp (-(Real.pi * Real.exp (2 * a)))) a := by
    change HasDerivAt (Real.exp ∘ fun x : ℝ => -(Real.pi * Real.exp (2 * x))) _ a
    exact ((Real.hasDerivAt_exp _).comp a hq.neg).congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hfac : HasDerivAt (fun x : ℝ => 2 * (Real.pi * Real.exp (2 * x)) - 1)
      (4 * Real.pi * Real.exp (2 * a)) a := by
    exact ((hq.const_mul 2).sub_const 1).congr_deriv (by ring)
  have hhalf : Real.exp (-a / 2) * Real.exp (a / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero
    ring
  have ha2 : Real.exp a ^ 2 = Real.exp (a * 2) := by
    rw [← Real.exp_nat_mul]
    ring
  have ha4 : Real.exp a ^ 4 = Real.exp (a * 4) := by
    rw [← Real.exp_nat_mul]
    ring
  unfold thetaCuspHalfDensityTailMinusPrimitive thetaCuspResidualScale
  change HasDerivAt
    ((fun x : ℝ => 2 * (Real.pi * Real.exp (2 * x)) - 1) *
      fun x : ℝ => Real.exp (-(Real.pi * Real.exp (2 * x)))) _ a
  apply (hfac.mul heneg).congr_deriv
  unfold thetaCuspSourceTerm thetaCuspSeed
  ring_nf
  rw [ha2, ha4]
  have hhalf' : Real.exp (a * (-1 / 2)) * Real.exp (a * (1 / 2)) = 1 := by
    convert hhalf using 1
    all_goals congr 1
    all_goals ring
  have hh2 : Real.exp (a * (-1 / 2)) * Real.exp (a * (1 / 2)) * Real.exp (a * 2) =
      Real.exp (a * 2) := by rw [hhalf', one_mul]
  have hh4 : Real.exp (a * (-1 / 2)) * Real.exp (a * (1 / 2)) * Real.exp (a * 4) =
      Real.exp (a * 4) := by rw [hhalf', one_mul]
  have h22 : Real.exp (a * 2) ^ 2 = Real.exp (a * 4) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hfirst : Real.pi * Real.exp (a * 2) *
        Real.exp (-(Real.pi * Real.exp (a * 2))) * 6 =
      Real.pi * Real.exp (a * (-1 / 2)) * Real.exp (a * (1 / 2)) * Real.exp (a * 2) *
        Real.exp (-(Real.pi * Real.exp (a * 2))) * 6 := by
    calc
      _ = (Real.pi * Real.exp (-(Real.pi * Real.exp (a * 2))) * 6) *
          Real.exp (a * 2) := by ring
      _ = (Real.pi * Real.exp (-(Real.pi * Real.exp (a * 2))) * 6) *
          (Real.exp (a * (-1 / 2)) * Real.exp (a * (1 / 2)) * Real.exp (a * 2)) := by
            rw [hh2]
      _ = _ := by ring
  have hsecond : Real.pi ^ 2 * Real.exp (a * 2) ^ 2 *
        Real.exp (-(Real.pi * Real.exp (a * 2))) * 4 =
      Real.pi ^ 2 * Real.exp (a * (-1 / 2)) * Real.exp (a * (1 / 2)) * Real.exp (a * 4) *
        Real.exp (-(Real.pi * Real.exp (a * 2))) * 4 := by
    calc
      _ = (Real.pi ^ 2 * Real.exp (-(Real.pi * Real.exp (a * 2))) * 4) *
          Real.exp (a * 4) := by rw [h22]; ring
      _ = (Real.pi ^ 2 * Real.exp (-(Real.pi * Real.exp (a * 2))) * 4) *
          (Real.exp (a * (-1 / 2)) * Real.exp (a * (1 / 2)) * Real.exp (a * 4)) := by
            rw [hh4]
      _ = _ := by ring
  rw [hfirst, hsecond]

theorem tendsto_thetaCuspHalfDensityTailPlusPrimitive_atTop :
    Tendsto thetaCuspHalfDensityTailPlusPrimitive atTop (nhds 0) := by
  have h := (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero 3 Real.pi_pos).comp
    Real.tendsto_exp_atTop
  have hcst : Tendsto (fun _ : ℝ => (2 * Real.pi : ℝ)) atTop (nhds (2 * Real.pi)) :=
    tendsto_const_nhds
  have hc : Tendsto (fun a : ℝ => (2 * Real.pi) *
      (Real.exp a ^ 3 * Real.exp (-(Real.pi * Real.exp a ^ 2)))) atTop (nhds 0) :=
    by simpa only [Function.comp_apply, mul_zero] using hcst.mul h
  convert hc using 1
  · funext a
    unfold thetaCuspHalfDensityTailPlusPrimitive thetaCuspResidualScale
    have h3 : Real.exp (3 * a) = Real.exp a ^ 3 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul a 3
    have h2 : Real.exp (2 * a) = Real.exp a ^ 2 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul a 2
    rw [h3, h2]
    ring

theorem tendsto_thetaCuspHalfDensityTailMinusPrimitive_atTop :
    Tendsto thetaCuspHalfDensityTailMinusPrimitive atTop (nhds 0) := by
  have h2 := (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero 2 Real.pi_pos).comp
    Real.tendsto_exp_atTop
  have h0 := (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero 0 Real.pi_pos).comp
    Real.tendsto_exp_atTop
  have hcst : Tendsto (fun _ : ℝ => (2 * Real.pi : ℝ)) atTop (nhds (2 * Real.pi)) :=
    tendsto_const_nhds
  have h : Tendsto (fun a : ℝ =>
      (2 * Real.pi) * (Real.exp a ^ 2 * Real.exp (-(Real.pi * Real.exp a ^ 2))) -
        (Real.exp a ^ 0 * Real.exp (-(Real.pi * Real.exp a ^ 2)))) atTop (nhds 0) :=
    by simpa only [Function.comp_apply, mul_zero, sub_zero] using (hcst.mul h2).sub h0
  convert h using 1
  · funext a
    unfold thetaCuspHalfDensityTailMinusPrimitive thetaCuspResidualScale
    have h2a : Real.exp (2 * a) = Real.exp a ^ 2 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul a 2
    rw [h2a]
    simp only [pow_zero, one_mul]
    ring

theorem integrableOn_thetaCuspHalfDensityTailPlus_Ioi {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => Real.exp (x / 2) * thetaCuspSourceTerm x 1) (Ioi a) := by
  have hbase := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    (n := 1) (z := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hbase' : IntegrableOn
      (fun x : ℝ => Real.exp (x / 2) * thetaCuspSourceTerm x 1) (Ioi 0) := by
    apply hbase.congr
    filter_upwards with x
    congr 2
    ring
  exact hbase'.mono_set fun x hx => lt_of_le_of_lt ha hx

theorem integrableOn_thetaCuspHalfDensityTailMinus_Ioi {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => Real.exp (-x / 2) * thetaCuspSourceTerm x 1) (Ioi a) := by
  have hbase := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    (n := 1) (z := (-1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hbase' : IntegrableOn
      (fun x : ℝ => Real.exp (-x / 2) * thetaCuspSourceTerm x 1) (Ioi 0) := by
    apply hbase.congr
    filter_upwards with x
    congr 2
    ring
  exact hbase'.mono_set fun x hx => lt_of_le_of_lt ha hx

theorem thetaCuspHalfDensityTailPlus_eq_primitive {a : ℝ} (ha : 0 ≤ a) :
    thetaCuspHalfDensityTailPlus a = thetaCuspHalfDensityTailPlusPrimitive a := by
  have hg := integrableOn_thetaCuspHalfDensityTailPlus_Ioi ha
  have hneg := hg.neg
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := thetaCuspHalfDensityTailPlusPrimitive)
    (f' := fun x : ℝ => -(Real.exp (x / 2) * thetaCuspSourceTerm x 1))
    (a := a) (m := 0) (fun x _ => by
      simpa only [neg_mul] using hasDerivAt_thetaCuspHalfDensityTailPlusPrimitive x)
    hneg tendsto_thetaCuspHalfDensityTailPlusPrimitive_atTop
  have hIoi : (∫ x : ℝ in Ioi a,
      Real.exp (x / 2) * thetaCuspSourceTerm x 1) =
      thetaCuspHalfDensityTailPlusPrimitive a := by
    rw [MeasureTheory.integral_neg] at hftc
    linarith
  rw [thetaCuspHalfDensityTailPlus]
  rw [← MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi a =ᵐ[volume] Ici a)]
  exact hIoi

theorem thetaCuspHalfDensityTailMinus_eq_primitive {a : ℝ} (ha : 0 ≤ a) :
    thetaCuspHalfDensityTailMinus a = thetaCuspHalfDensityTailMinusPrimitive a := by
  have hg := integrableOn_thetaCuspHalfDensityTailMinus_Ioi ha
  have hneg := hg.neg
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := thetaCuspHalfDensityTailMinusPrimitive)
    (f' := fun x : ℝ => -(Real.exp (-x / 2) * thetaCuspSourceTerm x 1))
    (a := a) (m := 0) (fun x _ => by
      simpa only [neg_mul] using hasDerivAt_thetaCuspHalfDensityTailMinusPrimitive x)
    hneg tendsto_thetaCuspHalfDensityTailMinusPrimitive_atTop
  have hIoi : (∫ x : ℝ in Ioi a,
      Real.exp (-x / 2) * thetaCuspSourceTerm x 1) =
      thetaCuspHalfDensityTailMinusPrimitive a := by
    rw [MeasureTheory.integral_neg] at hftc
    linarith
  rw [thetaCuspHalfDensityTailMinus]
  rw [← MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi a =ᵐ[volume] Ici a)]
  exact hIoi

def thetaCuspResidualEvenHalfDensity (a : ℝ) : ℝ :=
  ∫ x in Ici a, Real.cosh ((x - a) / 2) * thetaCuspSourceTerm x 1

def thetaCuspResidualOddHalfDensity (a : ℝ) : ℝ :=
  ∫ x in Ici a, Real.sinh ((x - a) / 2) * thetaCuspSourceTerm x 1

theorem integrableOn_thetaCuspHalfDensityTailPlus_Ici {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => Real.exp (x / 2) * thetaCuspSourceTerm x 1) (Ici a) := by
  change Integrable (fun x : ℝ => Real.exp (x / 2) * thetaCuspSourceTerm x 1)
    (volume.restrict (Ici a))
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi a =ᵐ[volume] Ici a)]
  exact integrableOn_thetaCuspHalfDensityTailPlus_Ioi ha

theorem integrableOn_thetaCuspHalfDensityTailMinus_Ici {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => Real.exp (-x / 2) * thetaCuspSourceTerm x 1) (Ici a) := by
  change Integrable (fun x : ℝ => Real.exp (-x / 2) * thetaCuspSourceTerm x 1)
    (volume.restrict (Ici a))
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi a =ᵐ[volume] Ici a)]
  exact integrableOn_thetaCuspHalfDensityTailMinus_Ioi ha

theorem two_mul_cosh_residual_mul_thetaCuspSourceTerm_eq (a x : ℝ) :
    2 * (Real.cosh ((x - a) / 2) * thetaCuspSourceTerm x 1) =
      Real.exp (-a / 2) * (Real.exp (x / 2) * thetaCuspSourceTerm x 1) +
      Real.exp (a / 2) * (Real.exp (-x / 2) * thetaCuspSourceTerm x 1) := by
  have hp : Real.exp ((x - a) / 2) =
      Real.exp (-a / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (-((x - a) / 2)) =
      Real.exp (a / 2) * Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.cosh_eq, hp, hm]
  ring

theorem two_mul_sinh_residual_mul_thetaCuspSourceTerm_eq (a x : ℝ) :
    2 * (Real.sinh ((x - a) / 2) * thetaCuspSourceTerm x 1) =
      Real.exp (-a / 2) * (Real.exp (x / 2) * thetaCuspSourceTerm x 1) -
      Real.exp (a / 2) * (Real.exp (-x / 2) * thetaCuspSourceTerm x 1) := by
  have hp : Real.exp ((x - a) / 2) =
      Real.exp (-a / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (-((x - a) / 2)) =
      Real.exp (a / 2) * Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, hp, hm]
  ring

theorem two_mul_thetaCuspResidualEvenHalfDensity_eq_tails {a : ℝ} (ha : 0 ≤ a) :
    2 * thetaCuspResidualEvenHalfDensity a =
      Real.exp (-a / 2) * thetaCuspHalfDensityTailPlus a +
      Real.exp (a / 2) * thetaCuspHalfDensityTailMinus a := by
  have hp := integrableOn_thetaCuspHalfDensityTailPlus_Ici ha
  have hm := integrableOn_thetaCuspHalfDensityTailMinus_Ici ha
  rw [thetaCuspResidualEvenHalfDensity, ← MeasureTheory.integral_const_mul]
  calc
    (∫ x : ℝ in Ici a,
        2 * (Real.cosh ((x - a) / 2) * thetaCuspSourceTerm x 1)) =
        ∫ x : ℝ in Ici a,
          (Real.exp (-a / 2) * (Real.exp (x / 2) * thetaCuspSourceTerm x 1) +
            Real.exp (a / 2) * (Real.exp (-x / 2) * thetaCuspSourceTerm x 1)) := by
              apply integral_congr_ae
              filter_upwards with x
              exact two_mul_cosh_residual_mul_thetaCuspSourceTerm_eq a x
    _ = Real.exp (-a / 2) *
          (∫ x : ℝ in Ici a, Real.exp (x / 2) * thetaCuspSourceTerm x 1) +
        Real.exp (a / 2) *
          (∫ x : ℝ in Ici a, Real.exp (-x / 2) * thetaCuspSourceTerm x 1) := by
            rw [MeasureTheory.integral_add (hp.const_mul _) (hm.const_mul _),
              MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = _ := rfl

theorem two_mul_thetaCuspResidualOddHalfDensity_eq_tails {a : ℝ} (ha : 0 ≤ a) :
    2 * thetaCuspResidualOddHalfDensity a =
      Real.exp (-a / 2) * thetaCuspHalfDensityTailPlus a -
      Real.exp (a / 2) * thetaCuspHalfDensityTailMinus a := by
  have hp := integrableOn_thetaCuspHalfDensityTailPlus_Ici ha
  have hm := integrableOn_thetaCuspHalfDensityTailMinus_Ici ha
  rw [thetaCuspResidualOddHalfDensity, ← MeasureTheory.integral_const_mul]
  calc
    (∫ x : ℝ in Ici a,
        2 * (Real.sinh ((x - a) / 2) * thetaCuspSourceTerm x 1)) =
        ∫ x : ℝ in Ici a,
          (Real.exp (-a / 2) * (Real.exp (x / 2) * thetaCuspSourceTerm x 1) -
            Real.exp (a / 2) * (Real.exp (-x / 2) * thetaCuspSourceTerm x 1)) := by
              apply integral_congr_ae
              filter_upwards with x
              exact two_mul_sinh_residual_mul_thetaCuspSourceTerm_eq a x
    _ = Real.exp (-a / 2) *
          (∫ x : ℝ in Ici a, Real.exp (x / 2) * thetaCuspSourceTerm x 1) -
        Real.exp (a / 2) *
          (∫ x : ℝ in Ici a, Real.exp (-x / 2) * thetaCuspSourceTerm x 1) := by
            rw [MeasureTheory.integral_sub (hp.const_mul _) (hm.const_mul _),
              MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = _ := rfl

theorem exp_neg_half_mul_thetaCuspHalfDensityTailPlusPrimitive (a : ℝ) :
    Real.exp (-a / 2) * thetaCuspHalfDensityTailPlusPrimitive a =
      Real.exp (a / 2) * (2 * thetaCuspResidualScale a) *
        Real.exp (-thetaCuspResidualScale a) := by
  have he : Real.exp (-a / 2) * Real.exp (3 * a) =
      Real.exp (a / 2) * Real.exp (2 * a) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold thetaCuspHalfDensityTailPlusPrimitive thetaCuspResidualScale
  calc
    _ = 2 * Real.pi * (Real.exp (-a / 2) * Real.exp (3 * a)) *
        Real.exp (-(Real.pi * Real.exp (2 * a))) := by ring
    _ = 2 * Real.pi * (Real.exp (a / 2) * Real.exp (2 * a)) *
        Real.exp (-(Real.pi * Real.exp (2 * a))) := by rw [he]
    _ = _ := by ring

theorem exp_half_mul_thetaCuspHalfDensityTailMinusPrimitive (a : ℝ) :
    Real.exp (a / 2) * thetaCuspHalfDensityTailMinusPrimitive a =
      Real.exp (a / 2) * (2 * thetaCuspResidualScale a - 1) *
        Real.exp (-thetaCuspResidualScale a) := by
  unfold thetaCuspHalfDensityTailMinusPrimitive
  ring

theorem two_mul_thetaCuspResidualEvenHalfDensity_eq {a : ℝ} (ha : 0 ≤ a) :
    2 * thetaCuspResidualEvenHalfDensity a =
      Real.exp (a / 2) * (4 * thetaCuspResidualScale a - 1) *
        Real.exp (-thetaCuspResidualScale a) := by
  rw [two_mul_thetaCuspResidualEvenHalfDensity_eq_tails ha,
    thetaCuspHalfDensityTailPlus_eq_primitive ha,
    thetaCuspHalfDensityTailMinus_eq_primitive ha,
    exp_neg_half_mul_thetaCuspHalfDensityTailPlusPrimitive,
    exp_half_mul_thetaCuspHalfDensityTailMinusPrimitive]
  ring

theorem two_mul_thetaCuspResidualOddHalfDensity_eq {a : ℝ} (ha : 0 ≤ a) :
    2 * thetaCuspResidualOddHalfDensity a =
      Real.exp (a / 2) * Real.exp (-thetaCuspResidualScale a) := by
  rw [two_mul_thetaCuspResidualOddHalfDensity_eq_tails ha,
    thetaCuspHalfDensityTailPlus_eq_primitive ha,
    thetaCuspHalfDensityTailMinus_eq_primitive ha,
    exp_neg_half_mul_thetaCuspHalfDensityTailPlusPrimitive,
    exp_half_mul_thetaCuspHalfDensityTailMinusPrimitive]
  ring

def thetaCuspOrdinarySurvival (a : ℝ) : ℝ :=
  ∫ x in Ici a, thetaCuspSourceTerm x 1

def thetaCuspSurvivalLower (a : ℝ) : ℝ :=
  Real.exp (a / 2) * (2 * thetaCuspResidualScale a - 1) *
    Real.exp (-thetaCuspResidualScale a)

def thetaCuspSurvivalUpper (a : ℝ) : ℝ :=
  2 * thetaCuspResidualScale a * Real.exp (a / 2) *
    Real.exp (-thetaCuspResidualScale a)

theorem integrableOn_thetaCuspOrdinarySurvival_Ioi {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x 1) (Ioi a) := by
  have hbase := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    (n := 1) (z := (0 : ℝ)) (by norm_num) (by norm_num)
  have hbase' : IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x 1) (Ioi 0) := by
    apply hbase.congr
    filter_upwards with x
    simp
  exact hbase'.mono_set fun x hx => lt_of_le_of_lt ha hx

theorem integrableOn_thetaCuspOrdinarySurvival_Ici {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x 1) (Ici a) := by
  change Integrable (fun x : ℝ => thetaCuspSourceTerm x 1) (volume.restrict (Ici a))
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi a =ᵐ[volume] Ici a)]
  exact integrableOn_thetaCuspOrdinarySurvival_Ioi ha

theorem thetaCuspSourceTerm_one_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspSourceTerm x 1 := by
  have hexp : (1 : ℝ) ≤ Real.exp x := by
    simpa using Real.exp_le_exp.mpr hx
  have hseed : 0 < thetaCuspSeed (Real.exp x) := by
    apply thetaCuspSeed_pos
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.exp x - 1)]
  unfold thetaCuspSourceTerm
  norm_num
  exact (mul_pos (Real.exp_pos _) hseed).le

theorem thetaCuspHalfDensityTailMinus_le_exp_neg_half_mul_survival
    {a : ℝ} (ha : 0 ≤ a) :
    thetaCuspHalfDensityTailMinus a ≤
      Real.exp (-a / 2) * thetaCuspOrdinarySurvival a := by
  have hm := integrableOn_thetaCuspHalfDensityTailMinus_Ici ha
  have hs := integrableOn_thetaCuspOrdinarySurvival_Ici ha
  rw [thetaCuspHalfDensityTailMinus, thetaCuspOrdinarySurvival,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono_ae hm (hs.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
  simp only [mem_Ici] at hxa
  have hsx := thetaCuspSourceTerm_one_nonneg_of_nonneg (ha.trans hxa)
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith [hxa])) hsx

theorem exp_half_mul_survival_le_thetaCuspHalfDensityTailPlus
    {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (a / 2) * thetaCuspOrdinarySurvival a ≤
      thetaCuspHalfDensityTailPlus a := by
  have hp := integrableOn_thetaCuspHalfDensityTailPlus_Ici ha
  have hs := integrableOn_thetaCuspOrdinarySurvival_Ici ha
  rw [thetaCuspHalfDensityTailPlus, thetaCuspOrdinarySurvival,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono_ae (hs.const_mul _) hp
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
  simp only [mem_Ici] at hxa
  have hsx := thetaCuspSourceTerm_one_nonneg_of_nonneg (ha.trans hxa)
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith [hxa])) hsx

theorem thetaCuspOrdinarySurvival_lower {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (a / 2) * (2 * thetaCuspResidualScale a - 1) *
        Real.exp (-thetaCuspResidualScale a) ≤
      thetaCuspOrdinarySurvival a := by
  have h := thetaCuspHalfDensityTailMinus_le_exp_neg_half_mul_survival ha
  have he : Real.exp (a / 2) * Real.exp (-a / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero
    ring
  calc
    _ = Real.exp (a / 2) * thetaCuspHalfDensityTailMinus a := by
      rw [thetaCuspHalfDensityTailMinus_eq_primitive ha,
        exp_half_mul_thetaCuspHalfDensityTailMinusPrimitive]
    _ ≤ Real.exp (a / 2) *
        (Real.exp (-a / 2) * thetaCuspOrdinarySurvival a) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = thetaCuspOrdinarySurvival a := by rw [← mul_assoc, he, one_mul]

theorem thetaCuspOrdinarySurvival_upper {a : ℝ} (ha : 0 ≤ a) :
    thetaCuspOrdinarySurvival a ≤
      2 * thetaCuspResidualScale a * Real.exp (a / 2) *
        Real.exp (-thetaCuspResidualScale a) := by
  have h := exp_half_mul_survival_le_thetaCuspHalfDensityTailPlus ha
  have he : Real.exp (-a / 2) * Real.exp (a / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero
    ring
  calc
    thetaCuspOrdinarySurvival a = Real.exp (-a / 2) *
        (Real.exp (a / 2) * thetaCuspOrdinarySurvival a) := by
      rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (-a / 2) * thetaCuspHalfDensityTailPlus a :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp (a / 2) * (2 * thetaCuspResidualScale a) *
        Real.exp (-thetaCuspResidualScale a) := by
      rw [thetaCuspHalfDensityTailPlus_eq_primitive ha,
        exp_neg_half_mul_thetaCuspHalfDensityTailPlusPrimitive]
    _ = _ := by ring

theorem thetaCuspOrdinarySurvival_corridor {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (a / 2) * (2 * thetaCuspResidualScale a - 1) *
        Real.exp (-thetaCuspResidualScale a) ≤ thetaCuspOrdinarySurvival a ∧
      thetaCuspOrdinarySurvival a ≤
        2 * thetaCuspResidualScale a * Real.exp (a / 2) *
          Real.exp (-thetaCuspResidualScale a) :=
  ⟨thetaCuspOrdinarySurvival_lower ha, thetaCuspOrdinarySurvival_upper ha⟩

theorem thetaCuspSurvivalUpper_sub_lower (a : ℝ) :
    thetaCuspSurvivalUpper a - thetaCuspSurvivalLower a =
      Real.exp (a / 2) * Real.exp (-thetaCuspResidualScale a) := by
  unfold thetaCuspSurvivalUpper thetaCuspSurvivalLower
  ring

theorem thetaCuspSurvival_relativeWidth {a : ℝ} (ha : 0 ≤ a) :
    (thetaCuspSurvivalUpper a - thetaCuspSurvivalLower a) /
        thetaCuspSurvivalLower a =
      1 / (2 * thetaCuspResidualScale a - 1) := by
  have hexp : 1 ≤ Real.exp (2 * a) := by
    simpa using Real.exp_le_exp.mpr (by linarith)
  have hq : 1 < thetaCuspResidualScale a := by
    unfold thetaCuspResidualScale
    nlinarith [Real.pi_gt_three]
  have hden : 2 * thetaCuspResidualScale a - 1 ≠ 0 := by nlinarith
  rw [thetaCuspSurvivalUpper_sub_lower]
  unfold thetaCuspSurvivalLower
  field_simp [hden, Real.exp_ne_zero]

theorem thetaCuspResidualScale_log_nat {n : ℕ} (hn : 1 ≤ n) :
    thetaCuspResidualScale (Real.log (n : ℝ)) = Real.pi * (n : ℝ) ^ 2 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  unfold thetaCuspResidualScale
  rw [show 2 * Real.log (n : ℝ) = Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
    Real.exp_add, Real.exp_log hnpos]
  ring

theorem thetaCuspOrdinarySurvival_log_nat_corridor {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) * (2 * Real.pi * (n : ℝ) ^ 2 - 1) *
        Real.exp (-(Real.pi * (n : ℝ) ^ 2)) ≤
      thetaCuspOrdinarySurvival (Real.log (n : ℝ)) ∧
    thetaCuspOrdinarySurvival (Real.log (n : ℝ)) ≤
      2 * Real.pi * (n : ℝ) ^ (5 / 2 : ℝ) *
        Real.exp (-(Real.pi * (n : ℝ) ^ 2)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnle : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnle
  have hsquare : Real.exp (Real.log (n : ℝ) / 2) ^ 2 = (n : ℝ) := by
    rw [← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * (Real.log (n : ℝ) / 2) = Real.log (n : ℝ) by
        push_cast
        ring,
      Real.exp_log hnpos]
  have hsqrt : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt (n : ℝ) := by
    have h := congrArg Real.sqrt hsquare
    rw [Real.sqrt_sq (Real.exp_pos _).le] at h
    exact h
  have hrpow : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
      Real.rpow_add hnpos, ← Real.sqrt_eq_rpow]
    exact congrArg (fun z : ℝ => z * Real.sqrt (n : ℝ))
      (Real.rpow_natCast (n : ℝ) 2)
  have h := thetaCuspOrdinarySurvival_corridor hlog
  rw [thetaCuspResidualScale_log_nat hn, hsqrt] at h
  constructor
  · convert h.1 using 1
    all_goals ring
  · calc
      _ ≤ 2 * (Real.pi * (n : ℝ) ^ 2) * Real.sqrt (n : ℝ) *
          Real.exp (-(Real.pi * (n : ℝ) ^ 2)) := h.2
      _ = _ := by rw [hrpow]; ring

theorem thetaCuspNaturalSurvivalCorridor_exactGap {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.pi * (n : ℝ) ^ (5 / 2 : ℝ) *
          Real.exp (-(Real.pi * (n : ℝ) ^ 2)) -
        Real.sqrt (n : ℝ) * (2 * Real.pi * (n : ℝ) ^ 2 - 1) *
          Real.exp (-(Real.pi * (n : ℝ) ^ 2)) =
      Real.sqrt (n : ℝ) * Real.exp (-(Real.pi * (n : ℝ) ^ 2)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [show (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
      Real.rpow_add hnpos, ← Real.sqrt_eq_rpow]
    exact congrArg (fun z : ℝ => z * Real.sqrt (n : ℝ))
      (Real.rpow_natCast (n : ℝ) 2)]
  ring

def thetaCuspResidualMoment (k : ℕ) (a : ℝ) : ℝ :=
  ∫ x in Ici a, (x - a) ^ k * thetaCuspSourceTerm x 1

def thetaCuspUpperTailMoment (k : ℕ) (a : ℝ) : ℝ :=
  ∫ x in Ici a, x ^ k * thetaCuspSourceTerm x 1

def thetaCuspTotalMoment (k : ℕ) : ℝ :=
  thetaCuspUpperTailMoment k 0

def thetaCuspLowerMoment (k : ℕ) (a : ℝ) : ℝ :=
  thetaCuspTotalMoment k - thetaCuspUpperTailMoment k a

theorem integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * thetaCuspSourceTerm x 1) (Ioi 0) := by
  have hzero : IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x 1) (Ioi 0) := by
    simpa using integrableOn_pow_mul_thetaCuspSourceTerm 0 1
  have heven := integrableOn_pow_mul_thetaCuspSourceTerm k 1
  have hsum := hzero.add heven
  apply MeasureTheory.Integrable.mono hsum
  · exact ((by
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (fun x : ℝ => x ^ k * thetaCuspSourceTerm x 1))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hsource : 0 ≤ thetaCuspSourceTerm x 1 :=
      (thetaCuspSourceTerm_nonneg_of_pos hx 1)
    have hpow : x ^ k ≤ 1 + x ^ (2 * k) := by
      by_cases hxone : x ≤ 1
      · exact (pow_le_one₀ hx.le hxone).trans
          (le_add_of_nonneg_right (pow_nonneg hx.le (2 * k)))
      · have hone : 1 ≤ x := (lt_of_not_ge hxone).le
        have hsq : x ^ k ≤ (x ^ k) ^ 2 := by
          nlinarith [one_le_pow₀ (n := k) hone]
        calc
          x ^ k ≤ (x ^ k) ^ 2 := hsq
          _ = x ^ (2 * k) := by rw [← pow_mul]; congr 1; omega
          _ ≤ 1 + x ^ (2 * k) := le_add_of_nonneg_left (by norm_num)
    change ‖x ^ k * thetaCuspSourceTerm x 1‖ ≤
      ‖thetaCuspSourceTerm x 1 + x ^ (2 * k) * thetaCuspSourceTerm x 1‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg hx.le k) hsource),
      abs_of_nonneg (add_nonneg hsource
        (mul_nonneg (pow_nonneg hx.le (2 * k)) hsource))]
    calc
      x ^ k * thetaCuspSourceTerm x 1 ≤
          (1 + x ^ (2 * k)) * thetaCuspSourceTerm x 1 :=
        mul_le_mul_of_nonneg_right hpow hsource
      _ = thetaCuspSourceTerm x 1 +
          x ^ (2 * k) * thetaCuspSourceTerm x 1 := by ring

theorem integrableOn_natPow_mul_thetaCuspSourceTerm_Ici
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * thetaCuspSourceTerm x 1) (Ici a) := by
  have hIoi := (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k).mono_set
    (fun x hx => lt_of_le_of_lt ha hx)
  change Integrable (fun x : ℝ => x ^ k * thetaCuspSourceTerm x 1)
    (volume.restrict (Ici a))
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi a =ᵐ[volume] Ici a)]
  exact hIoi

theorem integrableOn_thetaCuspResidualMoment
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    IntegrableOn (fun x : ℝ => (x - a) ^ k * thetaCuspSourceTerm x 1) (Ici a) := by
  have hupper := integrableOn_natPow_mul_thetaCuspSourceTerm_Ici ha k
  apply MeasureTheory.Integrable.mono hupper
  · exact ((by
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous
        (fun x : ℝ => (x - a) ^ k * thetaCuspSourceTerm x 1))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
    have hx : 0 ≤ x := ha.trans hxa
    have ht : 0 ≤ x - a := sub_nonneg.mpr hxa
    have hsource := thetaCuspSourceTerm_one_nonneg_of_nonneg hx
    have hpow : (x - a) ^ k ≤ x ^ k := by
      gcongr
      linarith [ha]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg ht k) hsource),
      abs_of_nonneg (mul_nonneg (pow_nonneg hx k) hsource)]
    exact mul_le_mul_of_nonneg_right hpow hsource

theorem thetaCuspUpperTailMoment_eq_sum_residual
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    thetaCuspUpperTailMoment k a =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ) * a ^ (k - r) * thetaCuspResidualMoment r a := by
  unfold thetaCuspUpperTailMoment
  calc
    (∫ x : ℝ in Ici a, x ^ k * thetaCuspSourceTerm x 1) =
        ∫ x : ℝ in Ici a,
          ∑ r ∈ Finset.range (k + 1),
            ((Nat.choose k r : ℝ) * a ^ (k - r)) *
              ((x - a) ^ r * thetaCuspSourceTerm x 1) := by
      apply integral_congr_ae
      filter_upwards with x
      calc
        x ^ k * thetaCuspSourceTerm x 1 =
            ((x - a) + a) ^ k * thetaCuspSourceTerm x 1 := by ring
        _ = (∑ r ∈ Finset.range (k + 1),
              (Nat.choose k r : ℝ) * (x - a) ^ r * a ^ (k - r)) *
              thetaCuspSourceTerm x 1 := by
          rw [add_pow]
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = ∑ r ∈ Finset.range (k + 1),
          ∫ x : ℝ in Ici a,
            ((Nat.choose k r : ℝ) * a ^ (k - r)) *
              ((x - a) ^ r * thetaCuspSourceTerm x 1) := by
      rw [MeasureTheory.integral_finsetSum]
      intro r hr
      exact (integrableOn_thetaCuspResidualMoment ha r).const_mul _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [MeasureTheory.integral_const_mul]
      rfl

theorem thetaCusp_evenTaylorTerm_le_cosh {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    (t / 2) ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) ≤ Real.cosh (t / 2) := by
  have h := (Real.hasSum_cosh (t / 2)).summable.le_tsum j (fun k hk => by
    exact div_nonneg (pow_nonneg (by positivity) _) (by positivity))
  rw [(Real.hasSum_cosh (t / 2)).tsum_eq] at h
  exact h

theorem thetaCusp_oddTaylorTerm_le_sinh {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    (t / 2) ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℝ) ≤
      Real.sinh (t / 2) := by
  have h := (Real.hasSum_sinh (t / 2)).summable.le_tsum j (fun k hk => by
    exact div_nonneg (pow_nonneg (by positivity) _) (by positivity))
  rw [(Real.hasSum_sinh (t / 2)).tsum_eq] at h
  exact h

theorem thetaCusp_evenTaylorScale (t : ℝ) (j : ℕ) :
    (4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ) *
        ((t / 2) ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)) =
      t ^ (2 * j) := by
  have hfac : (Nat.factorial (2 * j) : ℝ) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ (2 * j) = (4 : ℝ) ^ j := by
    calc
      (2 : ℝ) ^ (2 * j) = ((2 : ℝ) ^ 2) ^ j := by rw [pow_mul]
      _ = (4 : ℝ) ^ j := by norm_num
  field_simp
  rw [div_pow, pow_mul]
  rw [hpow]
  field_simp

theorem thetaCusp_oddTaylorScale (t : ℝ) (j : ℕ) :
    2 * (4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ) *
        ((t / 2) ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℝ)) =
      t ^ (2 * j + 1) := by
  have hfac : (Nat.factorial (2 * j + 1) : ℝ) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ (2 * j) = (4 : ℝ) ^ j := by
    calc
      (2 : ℝ) ^ (2 * j) = ((2 : ℝ) ^ 2) ^ j := by rw [pow_mul]
      _ = (4 : ℝ) ^ j := by norm_num
  have hpow' : (2 : ℝ) ^ (2 * j + 1) = 2 * (4 : ℝ) ^ j := by
    rw [pow_succ, hpow]
    ring
  field_simp
  rw [div_pow, pow_succ, pow_mul]
  rw [hpow']
  field_simp

theorem integrableOn_thetaCuspResidualEvenHalfDensity
    {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn
      (fun x : ℝ => Real.cosh ((x - a) / 2) * thetaCuspSourceTerm x 1) (Ici a) := by
  have hp := integrableOn_thetaCuspHalfDensityTailPlus_Ici ha
  have hm := integrableOn_thetaCuspHalfDensityTailMinus_Ici ha
  have hsum := (hp.const_mul (Real.exp (-a / 2))).add
    (hm.const_mul (Real.exp (a / 2)))
  have htwo : IntegrableOn
      (fun x : ℝ => 2 * (Real.cosh ((x - a) / 2) * thetaCuspSourceTerm x 1))
      (Ici a) := hsum.congr (by
    filter_upwards with x
    exact (two_mul_cosh_residual_mul_thetaCuspSourceTerm_eq a x).symm)
  have hhalf := htwo.const_mul (1 / 2 : ℝ)
  exact hhalf.congr (by
    filter_upwards with x
    ring)

theorem integrableOn_thetaCuspResidualOddHalfDensity
    {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn
      (fun x : ℝ => Real.sinh ((x - a) / 2) * thetaCuspSourceTerm x 1) (Ici a) := by
  have hp := integrableOn_thetaCuspHalfDensityTailPlus_Ici ha
  have hm := integrableOn_thetaCuspHalfDensityTailMinus_Ici ha
  have hdiff := (hp.const_mul (Real.exp (-a / 2))).sub
    (hm.const_mul (Real.exp (a / 2)))
  have htwo : IntegrableOn
      (fun x : ℝ => 2 * (Real.sinh ((x - a) / 2) * thetaCuspSourceTerm x 1))
      (Ici a) := hdiff.congr (by
    filter_upwards with x
    exact (two_mul_sinh_residual_mul_thetaCuspSourceTerm_eq a x).symm)
  have hhalf := htwo.const_mul (1 / 2 : ℝ)
  exact hhalf.congr (by
    filter_upwards with x
    ring)

theorem thetaCuspResidualMoment_even_le
    {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    thetaCuspResidualMoment (2 * j) a ≤
      (4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ) / 2 *
        Real.exp (a / 2) * (4 * thetaCuspResidualScale a - 1) *
          Real.exp (-thetaCuspResidualScale a) := by
  let C : ℝ := (4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ)
  have hf := integrableOn_thetaCuspResidualMoment ha (2 * j)
  have hg := integrableOn_thetaCuspResidualEvenHalfDensity ha
  have hpoint : ∀ᵐ x ∂volume.restrict (Ici a),
      (x - a) ^ (2 * j) * thetaCuspSourceTerm x 1 ≤
        C * (Real.cosh ((x - a) / 2) * thetaCuspSourceTerm x 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
    have ht : 0 ≤ x - a := sub_nonneg.mpr hxa
    have hx : 0 ≤ x := ha.trans hxa
    have hsource := thetaCuspSourceTerm_one_nonneg_of_nonneg hx
    have hterm := thetaCusp_evenTaylorTerm_le_cosh ht j
    have hscaled : C *
        (((x - a) / 2) ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)) ≤
      C * Real.cosh ((x - a) / 2) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    calc
      (x - a) ^ (2 * j) * thetaCuspSourceTerm x 1 =
          (C * (((x - a) / 2) ^ (2 * j) /
            (Nat.factorial (2 * j) : ℝ))) * thetaCuspSourceTerm x 1 := by
              rw [thetaCusp_evenTaylorScale]
      _ ≤ (C * Real.cosh ((x - a) / 2)) * thetaCuspSourceTerm x 1 :=
        mul_le_mul_of_nonneg_right hscaled hsource
      _ = _ := by ring
  have hint := MeasureTheory.integral_mono_ae hf (hg.const_mul C) hpoint
  have hineq : thetaCuspResidualMoment (2 * j) a ≤
      C * thetaCuspResidualEvenHalfDensity a := by
    simpa [thetaCuspResidualMoment, thetaCuspResidualEvenHalfDensity,
      MeasureTheory.integral_const_mul] using hint
  have he := two_mul_thetaCuspResidualEvenHalfDensity_eq ha
  have he' : thetaCuspResidualEvenHalfDensity a =
      (Real.exp (a / 2) * (4 * thetaCuspResidualScale a - 1) *
        Real.exp (-thetaCuspResidualScale a)) / 2 := by linarith
  calc
    thetaCuspResidualMoment (2 * j) a ≤
        C * thetaCuspResidualEvenHalfDensity a := hineq
    _ = _ := by rw [he']; dsimp [C]; ring

theorem thetaCuspResidualMoment_odd_le
    {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    thetaCuspResidualMoment (2 * j + 1) a ≤
      (4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ) *
        Real.exp (a / 2) * Real.exp (-thetaCuspResidualScale a) := by
  let C : ℝ := 2 * (4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ)
  have hf := integrableOn_thetaCuspResidualMoment ha (2 * j + 1)
  have hg := integrableOn_thetaCuspResidualOddHalfDensity ha
  have hpoint : ∀ᵐ x ∂volume.restrict (Ici a),
      (x - a) ^ (2 * j + 1) * thetaCuspSourceTerm x 1 ≤
        C * (Real.sinh ((x - a) / 2) * thetaCuspSourceTerm x 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
    have ht : 0 ≤ x - a := sub_nonneg.mpr hxa
    have hx : 0 ≤ x := ha.trans hxa
    have hsource := thetaCuspSourceTerm_one_nonneg_of_nonneg hx
    have hterm := thetaCusp_oddTaylorTerm_le_sinh ht j
    have hscaled : C *
        (((x - a) / 2) ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℝ)) ≤
      C * Real.sinh ((x - a) / 2) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    calc
      (x - a) ^ (2 * j + 1) * thetaCuspSourceTerm x 1 =
          (C * (((x - a) / 2) ^ (2 * j + 1) /
            (Nat.factorial (2 * j + 1) : ℝ))) * thetaCuspSourceTerm x 1 := by
              rw [thetaCusp_oddTaylorScale]
      _ ≤ (C * Real.sinh ((x - a) / 2)) * thetaCuspSourceTerm x 1 :=
        mul_le_mul_of_nonneg_right hscaled hsource
      _ = _ := by ring
  have hint := MeasureTheory.integral_mono_ae hf (hg.const_mul C) hpoint
  have hineq : thetaCuspResidualMoment (2 * j + 1) a ≤
      C * thetaCuspResidualOddHalfDensity a := by
    simpa [thetaCuspResidualMoment, thetaCuspResidualOddHalfDensity,
      MeasureTheory.integral_const_mul] using hint
  have ho := two_mul_thetaCuspResidualOddHalfDensity_eq ha
  have ho' : thetaCuspResidualOddHalfDensity a =
      (Real.exp (a / 2) * Real.exp (-thetaCuspResidualScale a)) / 2 := by
    linarith
  calc
    thetaCuspResidualMoment (2 * j + 1) a ≤
        C * thetaCuspResidualOddHalfDensity a := hineq
    _ = _ := by rw [ho']; dsimp [C]; ring

theorem integral_tsum_of_nonneg_hasSum
    (μ : Measure ℝ) (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hFnonneg : ∀ᵐ x ∂μ, ∀ n, 0 ≤ F n x)
    (hsum : ∀ᵐ x ∂μ, HasSum (fun n => F n x) (G x))
    (hG : Integrable G μ) :
    (∫ x, G x ∂μ) = ∑' n, ∫ x, F n x ∂μ := by
  have hnormsumE : ∀ᵐ x ∂μ,
      (∑' n : ℕ, ‖F n x‖ₑ) = ‖G x‖ₑ := by
    filter_upwards [hFnonneg, hsum] with x hxnonneg hxsum
    have hsumF : Summable (fun n => F n x) := hxsum.summable
    have hGnonneg : 0 ≤ G x := by
      rw [← hxsum.tsum_eq]
      exact tsum_nonneg fun n => hxnonneg n
    have hnormsum : (∑' n : ℕ, ‖F n x‖₊) = ‖G x‖₊ := by
      apply NNReal.eq
      rw [NNReal.coe_tsum]
      · simp only [coe_nnnorm, Real.norm_eq_abs]
        simp_rw [abs_of_nonneg (hxnonneg _)]
        rw [abs_of_nonneg hGnonneg, hxsum.tsum_eq]
    have hnorm : Summable (fun n : ℕ => ‖F n x‖₊) :=
      NNReal.summable_coe.mp (by
        simpa only [coe_nnnorm] using hsumF.norm)
    calc
      (∑' n : ℕ, ‖F n x‖ₑ) =
          ((∑' n : ℕ, ‖F n x‖₊ : NNReal) : ENNReal) := by
            exact (ENNReal.coe_tsum hnorm).symm
      _ = (‖G x‖₊ : ENNReal) := by rw [hnormsum]
      _ = ‖G x‖ₑ := rfl
  have hfinite : (∑' n : ℕ, ∫⁻ x, ‖F n x‖ₑ ∂μ) ≠ ⊤ := by
    rw [← lintegral_tsum (fun n => (hFmeas n).enorm)]
    rw [lintegral_congr_ae hnormsumE]
    exact ne_of_lt hG.hasFiniteIntegral
  have hswap := integral_tsum hFmeas hfinite
  calc
    (∫ x, G x ∂μ) = ∫ x, ∑' n, F n x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hsum] with x hxsum
      exact hxsum.tsum_eq.symm
    _ = ∑' n, ∫ x, F n x ∂μ := hswap

theorem thetaCusp_two_mul_evenTaylorTerm_eq (t : ℝ) (j : ℕ) :
    2 * ((t / 2) ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)) =
      2 * t ^ (2 * j) /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ)) := by
  have hfac : (Nat.factorial (2 * j) : ℝ) ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ j ≠ 0 := by positivity
  have hs := thetaCusp_evenTaylorScale t j
  field_simp at hs ⊢
  nlinarith

theorem thetaCusp_two_mul_oddTaylorTerm_eq (t : ℝ) (j : ℕ) :
    2 * ((t / 2) ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℝ)) =
      t ^ (2 * j + 1) /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ)) := by
  have hfac : (Nat.factorial (2 * j + 1) : ℝ) ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ j ≠ 0 := by positivity
  have hs := thetaCusp_oddTaylorScale t j
  field_simp at hs ⊢
  nlinarith

theorem thetaCuspResidualEvenMoment_series {a : ℝ} (ha : 0 ≤ a) :
    2 * (∑' j : ℕ,
      thetaCuspResidualMoment (2 * j) a /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) =
      Real.exp (a / 2) * (4 * thetaCuspResidualScale a - 1) *
        Real.exp (-thetaCuspResidualScale a) := by
  let μ : Measure ℝ := volume.restrict (Ici a)
  let F : ℕ → ℝ → ℝ := fun j x =>
    2 * (((x - a) / 2) ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)) *
      thetaCuspSourceTerm x 1
  let G : ℝ → ℝ := fun x =>
    2 * (Real.cosh ((x - a) / 2) * thetaCuspSourceTerm x 1)
  have hFmeas : ∀ j, AEStronglyMeasurable (F j) μ := by
    intro j
    exact ((by
      dsimp [F]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (F j))).aestronglyMeasurable
  have hFnonneg : ∀ᵐ x ∂μ, ∀ j, 0 ≤ F j x := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
    intro j
    have ht : 0 ≤ x - a := sub_nonneg.mpr hxa
    have hx : 0 ≤ x := ha.trans hxa
    exact mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (pow_nonneg (by positivity) _) (by positivity)))
      (thetaCuspSourceTerm_one_nonneg_of_nonneg hx)
  have hsum : ∀ᵐ x ∂μ, HasSum (fun j => F j x) (G x) := by
    filter_upwards with x
    have h := (Real.hasSum_cosh ((x - a) / 2)).mul_left
      (2 * thetaCuspSourceTerm x 1)
    simpa [F, G, mul_assoc, mul_comm, mul_left_comm] using h
  have hG : Integrable G μ := by
    exact (integrableOn_thetaCuspResidualEvenHalfDensity ha).const_mul 2
  have hswap := integral_tsum_of_nonneg_hasSum μ F G hFmeas hFnonneg hsum hG
  have hterm (j : ℕ) :
      (∫ x, F j x ∂μ) =
        2 * thetaCuspResidualMoment (2 * j) a /
          ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ)) := by
    change (∫ x : ℝ in Ici a,
      2 * (((x - a) / 2) ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)) *
        thetaCuspSourceTerm x 1) = _
    calc
      _ = ∫ x : ℝ in Ici a,
          (2 / ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) *
            ((x - a) ^ (2 * j) * thetaCuspSourceTerm x 1) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [thetaCusp_two_mul_evenTaylorTerm_eq]
        ring
      _ = _ := by
        rw [MeasureTheory.integral_const_mul]
        unfold thetaCuspResidualMoment
        ring
  calc
    2 * (∑' j : ℕ,
        thetaCuspResidualMoment (2 * j) a /
          ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) =
        ∑' j : ℕ, 2 *
          (thetaCuspResidualMoment (2 * j) a /
            ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) := by
              rw [tsum_mul_left]
    _ = ∑' j : ℕ, ∫ x, F j x ∂μ := by
      apply tsum_congr
      intro j
      rw [hterm]
      ring
    _ = ∫ x, G x ∂μ := hswap.symm
    _ = 2 * thetaCuspResidualEvenHalfDensity a := by
      change (∫ x : ℝ in Ici a,
        2 * (Real.cosh ((x - a) / 2) * thetaCuspSourceTerm x 1)) = _
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = _ := two_mul_thetaCuspResidualEvenHalfDensity_eq ha

theorem thetaCuspResidualOddMoment_series {a : ℝ} (ha : 0 ≤ a) :
    (∑' j : ℕ,
      thetaCuspResidualMoment (2 * j + 1) a /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ))) =
      Real.exp (a / 2) * Real.exp (-thetaCuspResidualScale a) := by
  let μ : Measure ℝ := volume.restrict (Ici a)
  let F : ℕ → ℝ → ℝ := fun j x =>
    2 * (((x - a) / 2) ^ (2 * j + 1) /
      (Nat.factorial (2 * j + 1) : ℝ)) * thetaCuspSourceTerm x 1
  let G : ℝ → ℝ := fun x =>
    2 * (Real.sinh ((x - a) / 2) * thetaCuspSourceTerm x 1)
  have hFmeas : ∀ j, AEStronglyMeasurable (F j) μ := by
    intro j
    exact ((by
      dsimp [F]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (F j))).aestronglyMeasurable
  have hFnonneg : ∀ᵐ x ∂μ, ∀ j, 0 ≤ F j x := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
    intro j
    have ht : 0 ≤ x - a := sub_nonneg.mpr hxa
    have hx : 0 ≤ x := ha.trans hxa
    exact mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (pow_nonneg (by positivity) _) (by positivity)))
      (thetaCuspSourceTerm_one_nonneg_of_nonneg hx)
  have hsum : ∀ᵐ x ∂μ, HasSum (fun j => F j x) (G x) := by
    filter_upwards with x
    have h := (Real.hasSum_sinh ((x - a) / 2)).mul_left
      (2 * thetaCuspSourceTerm x 1)
    simpa [F, G, mul_assoc, mul_comm, mul_left_comm] using h
  have hG : Integrable G μ := by
    exact (integrableOn_thetaCuspResidualOddHalfDensity ha).const_mul 2
  have hswap := integral_tsum_of_nonneg_hasSum μ F G hFmeas hFnonneg hsum hG
  have hterm (j : ℕ) :
      (∫ x, F j x ∂μ) =
        thetaCuspResidualMoment (2 * j + 1) a /
          ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ)) := by
    change (∫ x : ℝ in Ici a,
      2 * (((x - a) / 2) ^ (2 * j + 1) /
        (Nat.factorial (2 * j + 1) : ℝ)) * thetaCuspSourceTerm x 1) = _
    calc
      _ = ∫ x : ℝ in Ici a,
          (1 / ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ))) *
            ((x - a) ^ (2 * j + 1) * thetaCuspSourceTerm x 1) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [thetaCusp_two_mul_oddTaylorTerm_eq]
        ring
      _ = _ := by
        rw [MeasureTheory.integral_const_mul]
        unfold thetaCuspResidualMoment
        ring
  calc
    (∑' j : ℕ,
        thetaCuspResidualMoment (2 * j + 1) a /
          ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ))) =
        ∑' j : ℕ, ∫ x, F j x ∂μ := by
      apply tsum_congr
      intro j
      exact (hterm j).symm
    _ = ∫ x, G x ∂μ := hswap.symm
    _ = 2 * thetaCuspResidualOddHalfDensity a := by
      change (∫ x : ℝ in Ici a,
        2 * (Real.sinh ((x - a) / 2) * thetaCuspSourceTerm x 1)) = _
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = _ := two_mul_thetaCuspResidualOddHalfDensity_eq ha

def thetaCuspPositiveCrossingWindow (m : ℕ) (a : ℝ) : ℝ :=
  thetaCuspLowerMoment (2 * m) a * thetaCuspUpperTailMoment (2 * m + 2) a -
    thetaCuspLowerMoment (2 * m + 2) a * thetaCuspUpperTailMoment (2 * m) a

theorem thetaCuspPositiveCrossingWindow_eq_total_upper (m : ℕ) (a : ℝ) :
    thetaCuspPositiveCrossingWindow m a =
      thetaCuspTotalMoment (2 * m) * thetaCuspUpperTailMoment (2 * m + 2) a -
        thetaCuspTotalMoment (2 * m + 2) * thetaCuspUpperTailMoment (2 * m) a := by
  unfold thetaCuspPositiveCrossingWindow thetaCuspLowerMoment
  ring

theorem thetaCuspResidualOrientationRatio {a : ℝ} (ha : 0 ≤ a) :
    thetaCuspResidualOddHalfDensity a / thetaCuspResidualEvenHalfDensity a =
      1 / (4 * thetaCuspResidualScale a - 1) := by
  have hq : 1 < thetaCuspResidualScale a := by
    have hexp : 1 ≤ Real.exp (2 * a) := by
      simpa using Real.exp_le_exp.mpr (by linarith)
    unfold thetaCuspResidualScale
    nlinarith [Real.pi_gt_three]
  have hden : 4 * thetaCuspResidualScale a - 1 ≠ 0 := by nlinarith
  have he := two_mul_thetaCuspResidualEvenHalfDensity_eq ha
  have ho := two_mul_thetaCuspResidualOddHalfDensity_eq ha
  have he' : thetaCuspResidualEvenHalfDensity a =
      (Real.exp (a / 2) * (4 * thetaCuspResidualScale a - 1) *
        Real.exp (-thetaCuspResidualScale a)) / 2 := by linarith
  have ho' : thetaCuspResidualOddHalfDensity a =
      (Real.exp (a / 2) * Real.exp (-thetaCuspResidualScale a)) / 2 := by
    linarith
  rw [he', ho']
  field_simp [hden, Real.exp_ne_zero]

theorem thetaCuspOrdinarySurvival_nonneg {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ thetaCuspOrdinarySurvival a := by
  unfold thetaCuspOrdinarySurvival
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
  exact thetaCuspSourceTerm_one_nonneg_of_nonneg (ha.trans hxa)

theorem thetaCuspHalfDensityTailPlus_le_exp_neg {a : ℝ} (ha : 0 ≤ a) :
    thetaCuspHalfDensityTailPlus a ≤ 2 * Real.pi * Real.exp (-a) := by
  have hexp : 1 + 2 * a ≤ Real.exp (2 * a) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * a)
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hq : 3 + 6 * a ≤ thetaCuspResidualScale a := by
    unfold thetaCuspResidualScale
    have hmul : 3 * Real.exp (2 * a) ≤ Real.pi * Real.exp (2 * a) :=
      mul_le_mul_of_nonneg_right hpi (Real.exp_pos _).le
    nlinarith
  have harg : 3 * a - thetaCuspResidualScale a ≤ -a := by linarith
  rw [thetaCuspHalfDensityTailPlus_eq_primitive ha]
  unfold thetaCuspHalfDensityTailPlusPrimitive
  calc
    2 * Real.pi * Real.exp (3 * a) * Real.exp (-thetaCuspResidualScale a) =
        2 * Real.pi *
          (Real.exp (3 * a) * Real.exp (-thetaCuspResidualScale a)) := by ring
    _ =
        2 * Real.pi * Real.exp (3 * a - thetaCuspResidualScale a) := by
      rw [← Real.exp_add]
      congr 2
    _ ≤ 2 * Real.pi * Real.exp (-a) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)

theorem thetaCuspOrdinarySurvival_le_exp_neg {a : ℝ} (ha : 0 ≤ a) :
    thetaCuspOrdinarySurvival a ≤ 2 * Real.pi * Real.exp (-a) := by
  have hhalf := exp_half_mul_survival_le_thetaCuspHalfDensityTailPlus ha
  have hone : 1 ≤ Real.exp (a / 2) := by
    simpa using Real.exp_le_exp.mpr (by linarith)
  have hS := thetaCuspOrdinarySurvival_nonneg ha
  calc
    thetaCuspOrdinarySurvival a ≤
        Real.exp (a / 2) * thetaCuspOrdinarySurvival a := by
      nlinarith
    _ ≤ thetaCuspHalfDensityTailPlus a := hhalf
    _ ≤ 2 * Real.pi * Real.exp (-a) := thetaCuspHalfDensityTailPlus_le_exp_neg ha

theorem integral_Ioi_eq_sub_real {f : ℝ → ℝ} {c u : ℝ} (hcu : c ≤ u)
    (hint : IntegrableOn f (Ioi c) volume) :
    (∫ t in Ioi u, f t) = (∫ t in Ioi c, f t) - ∫ t in c..u, f t := by
  have hsplit : Ioi c = Ioc c u ∪ Ioi u := by
    ext t
    constructor
    · intro ht
      rcases le_or_gt t u with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · exact lt_of_le_of_lt hcu h
  have hdisj : Disjoint (Ioc c u) (Ioi u) := by
    rw [Set.disjoint_left]
    rintro t ⟨_, ht2⟩ ht3
    exact absurd ht3 (not_lt.mpr ht2)
  have hunion : (∫ t in Ioi c, f t) =
      (∫ t in Ioc c u, f t) + ∫ t in Ioi u, f t := by
    rw [hsplit]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set (by rw [hsplit]; exact Set.subset_union_left))
      (hint.mono_set (by rw [hsplit]; exact Set.subset_union_right))
  rw [intervalIntegral.integral_of_le hcu, hunion]
  ring

theorem hasDerivAt_thetaCuspOrdinarySurvival {a : ℝ} (ha : 0 < a) :
    HasDerivAt thetaCuspOrdinarySurvival (-thetaCuspSourceTerm a 1) a := by
  let f : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  have hint : IntegrableOn f (Ioi 0) := by
    simpa [f] using integrableOn_thetaCuspOrdinarySurvival_Ioi (a := (0 : ℝ)) (by norm_num)
  have hfcont : Continuous f := by
    dsimp [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hII : IntervalIntegrable f volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have hd : HasDerivAt
      (fun u : ℝ => (∫ t in Ioi (0 : ℝ), f t) - ∫ t in (0 : ℝ)..u, f t)
      (-f a) a := by
    have hbase := intervalIntegral.integral_hasDerivAt_right hII
      (hfcont.stronglyMeasurableAtFilter volume (𝓝 a)) hfcont.continuousAt
    simpa using hbase.const_sub (∫ t in Ioi (0 : ℝ), f t)
  have htail : HasDerivAt (fun u : ℝ => ∫ t in Ioi u, f t) (-f a) a := by
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ha] with u hu
    have hsplit := integral_Ioi_eq_sub_real (c := (0 : ℝ)) (u := u) hu.le hint
    exact hsplit
  apply htail.congr_of_eventuallyEq
  filter_upwards with u
  unfold thetaCuspOrdinarySurvival
  rw [← MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi u =ᵐ[volume] Ici u)]

theorem continuousOn_thetaCuspOrdinarySurvival_Ioi :
    ContinuousOn thetaCuspOrdinarySurvival (Ioi 0) := by
  intro a ha
  exact (hasDerivAt_thetaCuspOrdinarySurvival ha).continuousAt.continuousWithinAt

theorem integrableOn_pow_mul_exp_neg_Ioi_zero (m : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-x)) (Ioi 0) := by
  have hm : (-1 : ℝ) < (m : ℝ) :=
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg m)
  convert integrableOn_rpow_mul_exp_neg_rpow
    (p := (1 : ℝ)) (s := (m : ℝ)) hm (by norm_num) using 1
  ext x
  rw [Real.rpow_natCast, Real.rpow_one]

theorem integrableOn_pow_mul_thetaCuspOrdinarySurvival (m : ℕ) :
    IntegrableOn
      (fun a : ℝ => a ^ m * thetaCuspOrdinarySurvival a) (Ioi 0) := by
  have hmajor := (integrableOn_pow_mul_exp_neg_Ioi_zero m).const_mul (2 * Real.pi)
  apply MeasureTheory.Integrable.mono hmajor
  · have hcont : ContinuousOn
        (fun a : ℝ => a ^ m * thetaCuspOrdinarySurvival a) (Ioi 0) :=
      (continuousOn_id.pow m).mul continuousOn_thetaCuspOrdinarySurvival_Ioi
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hS := thetaCuspOrdinarySurvival_nonneg ha.le
    have hbound := thetaCuspOrdinarySurvival_le_exp_neg ha.le
    have hpow : 0 ≤ a ^ m := pow_nonneg ha.le m
    change ‖a ^ m * thetaCuspOrdinarySurvival a‖ ≤
      ‖2 * Real.pi * (a ^ m * Real.exp (-a))‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hpow hS),
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * (a ^ m * Real.exp (-a)))]
    nlinarith [mul_le_mul_of_nonneg_left hbound hpow]

theorem tendsto_pow_mul_thetaCuspOrdinarySurvival_atTop_zero (k : ℕ) :
    Tendsto (fun a : ℝ => a ^ k * thetaCuspOrdinarySurvival a) atTop (𝓝 0) := by
  have hupper : ∀ᶠ a : ℝ in atTop,
      a ^ k * thetaCuspOrdinarySurvival a ≤
        2 * Real.pi * (a ^ k * Real.exp (-a)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    have hpow : 0 ≤ a ^ k := pow_nonneg ha k
    exact (mul_le_mul_of_nonneg_left
      (thetaCuspOrdinarySurvival_le_exp_neg ha) hpow).trans_eq (by ring)
  have hlower : ∀ᶠ a : ℝ in atTop,
      0 ≤ a ^ k * thetaCuspOrdinarySurvival a := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    exact mul_nonneg (pow_nonneg ha k) (thetaCuspOrdinarySurvival_nonneg ha)
  have hzero : Tendsto (fun a : ℝ =>
      2 * Real.pi * (a ^ k * Real.exp (-a))) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul
      (2 * Real.pi) using 1
    all_goals simp
  exact squeeze_zero' hlower hupper hzero

theorem tendsto_pow_mul_thetaCuspOrdinarySurvival_at_zero
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun a : ℝ => a ^ k * thetaCuspOrdinarySurvival a)
      (𝓝[>] 0) (𝓝 0) := by
  have hupper : ∀ᶠ a : ℝ in 𝓝[>] 0,
      a ^ k * thetaCuspOrdinarySurvival a ≤
        2 * Real.pi * (a ^ k * Real.exp (-a)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hpow : 0 ≤ a ^ k := pow_nonneg ha.le k
    exact (mul_le_mul_of_nonneg_left
      (thetaCuspOrdinarySurvival_le_exp_neg ha.le) hpow).trans_eq (by ring)
  have hlower : ∀ᶠ a : ℝ in 𝓝[>] 0,
      0 ≤ a ^ k * thetaCuspOrdinarySurvival a := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact mul_nonneg (pow_nonneg ha.le k)
      (thetaCuspOrdinarySurvival_nonneg ha.le)
  have hcontinuous : ContinuousAt
      (fun a : ℝ => 2 * Real.pi * (a ^ k * Real.exp (-a))) 0 := by
    fun_prop
  have hzero : Tendsto (fun a : ℝ =>
      2 * Real.pi * (a ^ k * Real.exp (-a))) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun a : ℝ =>
        2 * Real.pi * (a ^ k * Real.exp (-a))) (𝓝[>] 0)
        (𝓝 (2 * Real.pi * ((0 : ℝ) ^ k * Real.exp (-0)))) :=
      hcontinuous.tendsto.mono_left inf_le_left
    simpa [zero_pow (Nat.ne_of_gt (Nat.zero_lt_of_lt hk))] using h
  exact squeeze_zero' hlower hupper hzero

theorem thetaCuspTotalMoment_layerCake {k : ℕ} (hk : 1 ≤ k) :
    thetaCuspTotalMoment k =
      (k : ℝ) * ∫ a : ℝ in Ioi 0,
        a ^ (k - 1) * thetaCuspOrdinarySurvival a := by
  let u : ℝ → ℝ := fun x => x ^ k
  let u' : ℝ → ℝ := fun x => (k : ℝ) * x ^ (k - 1)
  let v : ℝ → ℝ := thetaCuspOrdinarySurvival
  let v' : ℝ → ℝ := fun x => -thetaCuspSourceTerm x 1
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    simpa [u, u'] using hasDerivAt_pow k x
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    simpa [v, v'] using hasDerivAt_thetaCuspOrdinarySurvival hx
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    have h := (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k).neg
    convert h using 1
    funext x
    dsimp [u, v']
    ring
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspOrdinarySurvival (k - 1)).const_mul
      (k : ℝ)
    exact h.congr (by
      filter_upwards with x
      dsimp [u', v]
      ring)
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    change Tendsto (fun x : ℝ => x ^ k * thetaCuspOrdinarySurvival x)
      (𝓝[>] 0) (𝓝 0)
    exact tendsto_pow_mul_thetaCuspOrdinarySurvival_at_zero hk
  have htop : Tendsto (u * v) atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun x : ℝ => x ^ k * thetaCuspOrdinarySurvival x)
      atTop (𝓝 0)
    exact tendsto_pow_mul_thetaCuspOrdinarySurvival_atTop_zero k
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hu hv huv' hu'v hzero htop
  have hleft : (∫ x : ℝ in Ioi 0, u x * v' x) =
      -∫ x : ℝ in Ioi 0, x ^ k * thetaCuspSourceTerm x 1 := by
    rw [← MeasureTheory.integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [u, v']
    ring
  have hright : (∫ x : ℝ in Ioi 0, u' x * v x) =
      (k : ℝ) * ∫ x : ℝ in Ioi 0,
        x ^ (k - 1) * thetaCuspOrdinarySurvival x := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [u', v]
    ring
  rw [hleft, hright] at hibp
  have hmom : thetaCuspTotalMoment k =
      ∫ x : ℝ in Ioi 0, x ^ k * thetaCuspSourceTerm x 1 := by
    unfold thetaCuspTotalMoment thetaCuspUpperTailMoment
    rw [← MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici : Ioi (0 : ℝ) =ᵐ[volume] Ici 0)]
  rw [hmom]
  linarith

theorem thetaCuspSurvivalLower_nonneg {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ thetaCuspSurvivalLower a := by
  have hq : 1 < thetaCuspResidualScale a := by
    have hexp : 1 ≤ Real.exp (2 * a) := by
      simpa using Real.exp_le_exp.mpr (by linarith)
    unfold thetaCuspResidualScale
    nlinarith [Real.pi_gt_three]
  unfold thetaCuspSurvivalLower
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by nlinarith))
    (Real.exp_pos _).le

theorem thetaCuspSurvivalUpper_nonneg (a : ℝ) :
    0 ≤ thetaCuspSurvivalUpper a := by
  unfold thetaCuspSurvivalUpper thetaCuspResidualScale
  positivity

theorem thetaCuspSurvivalUpper_le_exp_neg {a : ℝ} (ha : 0 ≤ a) :
    thetaCuspSurvivalUpper a ≤ 2 * Real.pi * Real.exp (-a) := by
  have htail : 0 ≤ thetaCuspHalfDensityTailPlus a := by
    unfold thetaCuspHalfDensityTailPlus
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hxa
    exact mul_nonneg (Real.exp_pos _).le
      (thetaCuspSourceTerm_one_nonneg_of_nonneg (ha.trans hxa))
  have hexp : Real.exp (-a / 2) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (by linarith)
  have heq : thetaCuspSurvivalUpper a =
      Real.exp (-a / 2) * thetaCuspHalfDensityTailPlus a := by
    rw [thetaCuspHalfDensityTailPlus_eq_primitive ha,
      exp_neg_half_mul_thetaCuspHalfDensityTailPlusPrimitive]
    unfold thetaCuspSurvivalUpper
    ring
  rw [heq]
  calc
    Real.exp (-a / 2) * thetaCuspHalfDensityTailPlus a ≤
        thetaCuspHalfDensityTailPlus a := by nlinarith
    _ ≤ 2 * Real.pi * Real.exp (-a) := thetaCuspHalfDensityTailPlus_le_exp_neg ha

theorem integrableOn_pow_mul_thetaCuspSurvivalUpper (m : ℕ) :
    IntegrableOn (fun a : ℝ => a ^ m * thetaCuspSurvivalUpper a) (Ioi 0) := by
  have hmajor := (integrableOn_pow_mul_exp_neg_Ioi_zero m).const_mul (2 * Real.pi)
  apply MeasureTheory.Integrable.mono hmajor
  · have hcontUpper : ContinuousOn thetaCuspSurvivalUpper (Ioi 0) := by
      unfold thetaCuspSurvivalUpper thetaCuspResidualScale
      fun_prop
    have hcont := (continuousOn_id.pow m).mul hcontUpper
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hpow : 0 ≤ a ^ m := pow_nonneg ha.le m
    have hU := thetaCuspSurvivalUpper_nonneg a
    change ‖a ^ m * thetaCuspSurvivalUpper a‖ ≤
      ‖2 * Real.pi * (a ^ m * Real.exp (-a))‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hpow hU),
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * (a ^ m * Real.exp (-a)))]
    nlinarith [mul_le_mul_of_nonneg_left
      (thetaCuspSurvivalUpper_le_exp_neg ha.le) hpow]

theorem integrableOn_pow_mul_thetaCuspSurvivalLower (m : ℕ) :
    IntegrableOn (fun a : ℝ => a ^ m * thetaCuspSurvivalLower a) (Ioi 0) := by
  have hupper := integrableOn_pow_mul_thetaCuspSurvivalUpper m
  apply MeasureTheory.Integrable.mono hupper
  · have hcontLower : ContinuousOn thetaCuspSurvivalLower (Ioi 0) := by
      unfold thetaCuspSurvivalLower thetaCuspResidualScale
      fun_prop
    have hcont := (continuousOn_id.pow m).mul hcontLower
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hpow : 0 ≤ a ^ m := pow_nonneg ha.le m
    have hL := thetaCuspSurvivalLower_nonneg ha.le
    have hU := thetaCuspSurvivalUpper_nonneg a
    have hLU : thetaCuspSurvivalLower a ≤ thetaCuspSurvivalUpper a := by
      calc
        thetaCuspSurvivalLower a ≤ thetaCuspOrdinarySurvival a := by
          simpa [thetaCuspSurvivalLower] using thetaCuspOrdinarySurvival_lower ha.le
        _ ≤ thetaCuspSurvivalUpper a := by
          simpa [thetaCuspSurvivalUpper] using thetaCuspOrdinarySurvival_upper ha.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hpow hL), abs_of_nonneg (mul_nonneg hpow hU)]
    exact mul_le_mul_of_nonneg_left hLU hpow

theorem thetaCuspTotalMoment_corridor {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * ∫ a : ℝ in Ioi 0,
        a ^ (k - 1) * thetaCuspSurvivalLower a ≤ thetaCuspTotalMoment k ∧
      thetaCuspTotalMoment k ≤
        (k : ℝ) * ∫ a : ℝ in Ioi 0,
          a ^ (k - 1) * thetaCuspSurvivalUpper a := by
  have hL := integrableOn_pow_mul_thetaCuspSurvivalLower (k - 1)
  have hS := integrableOn_pow_mul_thetaCuspOrdinarySurvival (k - 1)
  have hU := integrableOn_pow_mul_thetaCuspSurvivalUpper (k - 1)
  have hLS : (∫ a : ℝ in Ioi 0,
      a ^ (k - 1) * thetaCuspSurvivalLower a) ≤
      ∫ a : ℝ in Ioi 0,
        a ^ (k - 1) * thetaCuspOrdinarySurvival a := by
    apply MeasureTheory.integral_mono_ae hL hS
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_le_mul_of_nonneg_left (by
      simpa [thetaCuspSurvivalLower] using thetaCuspOrdinarySurvival_lower ha.le)
      (pow_nonneg ha.le (k - 1))
  have hSU : (∫ a : ℝ in Ioi 0,
      a ^ (k - 1) * thetaCuspOrdinarySurvival a) ≤
      ∫ a : ℝ in Ioi 0,
        a ^ (k - 1) * thetaCuspSurvivalUpper a := by
    apply MeasureTheory.integral_mono_ae hS hU
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_le_mul_of_nonneg_left (by
      simpa [thetaCuspSurvivalUpper] using thetaCuspOrdinarySurvival_upper ha.le)
      (pow_nonneg ha.le (k - 1))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [thetaCuspTotalMoment_layerCake hk]
  exact ⟨mul_le_mul_of_nonneg_left hLS hk0, mul_le_mul_of_nonneg_left hSU hk0⟩

theorem thetaCuspTotalMoment_explicitCorridor {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * ∫ a : ℝ in Ioi 0,
        a ^ (k - 1) *
          (Real.exp (a / 2) * (2 * thetaCuspResidualScale a - 1) *
            Real.exp (-thetaCuspResidualScale a)) ≤ thetaCuspTotalMoment k ∧
      thetaCuspTotalMoment k ≤
        (k : ℝ) * ∫ a : ℝ in Ioi 0,
          a ^ (k - 1) *
            (2 * thetaCuspResidualScale a * Real.exp (a / 2) *
              Real.exp (-thetaCuspResidualScale a)) := by
  simpa [thetaCuspSurvivalLower, thetaCuspSurvivalUpper] using
    thetaCuspTotalMoment_corridor hk

theorem thetaCuspTotalMomentCorridor_width {k : ℕ} (_hk : 1 ≤ k) :
    (k : ℝ) * (∫ a : ℝ in Ioi 0,
          a ^ (k - 1) * thetaCuspSurvivalUpper a) -
        (k : ℝ) * (∫ a : ℝ in Ioi 0,
          a ^ (k - 1) * thetaCuspSurvivalLower a) =
      (k : ℝ) * ∫ a : ℝ in Ioi 0,
        a ^ (k - 1) * Real.exp (a / 2) *
          Real.exp (-thetaCuspResidualScale a) := by
  have hU := integrableOn_pow_mul_thetaCuspSurvivalUpper (k - 1)
  have hL := integrableOn_pow_mul_thetaCuspSurvivalLower (k - 1)
  calc
    _ = (k : ℝ) *
        ((∫ a : ℝ in Ioi 0, a ^ (k - 1) * thetaCuspSurvivalUpper a) -
          ∫ a : ℝ in Ioi 0, a ^ (k - 1) * thetaCuspSurvivalLower a) := by ring
    _ = (k : ℝ) * ∫ a : ℝ in Ioi 0,
        (a ^ (k - 1) * thetaCuspSurvivalUpper a -
          a ^ (k - 1) * thetaCuspSurvivalLower a) := by
      rw [MeasureTheory.integral_sub hU hL]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with a
      rw [← mul_sub, thetaCuspSurvivalUpper_sub_lower]
      ring

/-! ### Source curvature and all-order moment recurrence -/

/-- First-atom logarithmic-potential slope `V'`. -/
def thetaCuspFirstLogPotentialSlope (x : ℝ) : ℝ :=
  2 * thetaCuspBornWittenSuperpotential 1 x

theorem thetaCuspFirstLogPotentialSlope_zero :
    thetaCuspFirstLogPotentialSlope 0 = -thetaCuspFirstAtomBoundaryLogSlope := by
  rw [thetaCuspFirstLogPotentialSlope,
    two_thetaCuspBornWittenSuperpotential_eq_readoutProfile
      (n := 1) (by norm_num) (by norm_num)]
  have hweight : thetaCuspBornWittenWeight 1 0 = Real.pi - 3 / 2 := by
    rw [thetaCuspBornWittenWeight_eq]
    simp [thetaCuspMorseScale]
  rw [hweight]
  have hden : Real.pi - 3 / 2 ≠ 0 := by nlinarith [Real.pi_gt_three]
  have hden' : 2 * Real.pi - 3 ≠ 0 := by nlinarith [Real.pi_gt_three]
  have hfrac : 3 / (Real.pi - 3 / 2) = 6 / (2 * Real.pi - 3) := by
    field_simp [hden, hden']
    ring
  rw [hfrac]
  unfold thetaCuspFirstAtomBoundaryLogSlope
  ring

theorem thetaCuspFirstLogPotentialSlope_affine_lower
    {x : ℝ} (hx : 0 ≤ x) :
    19 * x - thetaCuspFirstAtomBoundaryLogSlope ≤
      thetaCuspFirstLogPotentialSlope x := by
  let Vp : ℝ → ℝ := thetaCuspFirstLogPotentialSlope
  have hcontinuous : ContinuousOn Vp (Ici 0) := by
    intro y hy
    exact ((hasDerivAt_two_thetaCuspBornWittenSuperpotential
      (n := 1) (by norm_num) hy).continuousAt).continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ Vp (interior (Ici 0)) := by
    intro y hy
    rw [interior_Ici] at hy
    exact (hasDerivAt_two_thetaCuspBornWittenSuperpotential
      (n := 1) (by norm_num) hy.le).differentiableAt.differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Ici 0),
      (19 : ℝ) ≤ deriv Vp y := by
    intro y hy
    rw [interior_Ici] at hy
    change (19 : ℝ) ≤
      deriv (fun z : ℝ => 2 * thetaCuspBornWittenSuperpotential 1 z) y
    rw [(hasDerivAt_two_thetaCuspBornWittenSuperpotential
      (n := 1) (by norm_num) hy.le).deriv]
    exact nineteen_le_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hy.le
  have hslope := (convex_Ici 0).mul_sub_le_image_sub_of_le_deriv
    hcontinuous hdifferentiable hderiv 0 (by simp) x hx hx
  dsimp only [Vp] at hslope
  rw [thetaCuspFirstLogPotentialSlope_zero] at hslope
  linarith

theorem thetaCuspFirstAtomBoundaryLogSlope_bounds :
    0 < thetaCuspFirstAtomBoundaryLogSlope ∧
      thetaCuspFirstAtomBoundaryLogSlope < 1 / 2 :=
  ⟨thetaCuspFirstAtomBoundaryLogSlope_pos,
    thetaCuspFirstAtomBoundaryLogSlope_lt_one_half⟩

theorem thetaCuspTotalMoment_eq_integral_Ioi (k : ℕ) :
    thetaCuspTotalMoment k =
      ∫ x : ℝ in Ioi 0, x ^ k * thetaCuspSourceTerm x 1 := by
  unfold thetaCuspTotalMoment thetaCuspUpperTailMoment
  rw [← MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi (0 : ℝ) =ᵐ[volume] Ici 0)]

theorem integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source
    (k : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ k * thetaCuspFirstLogPotentialSlope x * thetaCuspSourceTerm x 1)
      (Ioi 0) := by
  have h :=
    (integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
      k (n := 1) (by norm_num)).const_mul (2 * Real.pi)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
    (n := 1) (by norm_num) hx.le]
  unfold thetaCuspFirstLogPotentialSlope
  ring

theorem thetaCuspSourcePotentialSlope_moment_eq
    {k : ℕ} (hk : 1 ≤ k) :
    (∫ x : ℝ in Ioi 0,
      x ^ k * thetaCuspFirstLogPotentialSlope x * thetaCuspSourceTerm x 1) =
      (k : ℝ) * thetaCuspTotalMoment (k - 1) := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hk)
  have hward := thetaCuspBornWitten_monomial_anomalousSteinWard
    k (n := 1) (by norm_num)
  simp only [if_neg hk0, zero_add] at hward
  rw [show (fun x : ℝ =>
      (k : ℝ) * x ^ (k - 1) * thetaCuspBornWittenAmplitude 1 x ^ 2) =
      fun x : ℝ => (k : ℝ) *
        (x ^ (k - 1) * thetaCuspBornWittenAmplitude 1 x ^ 2) by
        funext x
        ring,
    MeasureTheory.integral_const_mul] at hward
  have hleft :
      (∫ x : ℝ in Ioi 0,
        x ^ k * thetaCuspFirstLogPotentialSlope x * thetaCuspSourceTerm x 1) =
        2 * Real.pi *
          ∫ x : ℝ in Ioi 0,
            x ^ k * thetaCuspBornWittenSuperpotential 1 x *
              thetaCuspBornWittenAmplitude 1 x ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
      (n := 1) (by norm_num) hx.le]
    unfold thetaCuspFirstLogPotentialSlope
    ring
  have hright : thetaCuspTotalMoment (k - 1) =
      Real.pi * ∫ x : ℝ in Ioi 0,
        x ^ (k - 1) * thetaCuspBornWittenAmplitude 1 x ^ 2 := by
    rw [thetaCuspTotalMoment_eq_integral_Ioi,
      ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
      (n := 1) (by norm_num) hx.le]
    ring
  rw [hleft, hright, hward]
  ring

theorem thetaCuspTotalMoment_curvature_recurrence
    {k : ℕ} (hk : 1 ≤ k) :
    19 * thetaCuspTotalMoment (k + 1) ≤
      thetaCuspFirstAtomBoundaryLogSlope * thetaCuspTotalMoment k +
        (k : ℝ) * thetaCuspTotalMoment (k - 1) := by
  have hleft : IntegrableOn (fun x : ℝ =>
      19 * (x ^ (k + 1) * thetaCuspSourceTerm x 1)) (Ioi 0) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)).const_mul 19
  have hright : IntegrableOn (fun x : ℝ =>
      thetaCuspFirstAtomBoundaryLogSlope *
          (x ^ k * thetaCuspSourceTerm x 1) +
        x ^ k * thetaCuspFirstLogPotentialSlope x *
          thetaCuspSourceTerm x 1) (Ioi 0) :=
    ((integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k).const_mul
      thetaCuspFirstAtomBoundaryLogSlope).add
        (integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source k)
  have hmono :
      (∫ x : ℝ in Ioi 0,
        19 * (x ^ (k + 1) * thetaCuspSourceTerm x 1)) ≤
      ∫ x : ℝ in Ioi 0,
        thetaCuspFirstAtomBoundaryLogSlope *
            (x ^ k * thetaCuspSourceTerm x 1) +
          x ^ k * thetaCuspFirstLogPotentialSlope x *
            thetaCuspSourceTerm x 1 := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hf : 0 ≤ thetaCuspSourceTerm x 1 :=
      thetaCuspSourceTerm_nonneg_of_pos hx 1
    have hweight : 0 ≤ x ^ k * thetaCuspSourceTerm x 1 :=
      mul_nonneg (pow_nonneg hx.le k) hf
    have hslope := thetaCuspFirstLogPotentialSlope_affine_lower hx.le
    have hmul := mul_le_mul_of_nonneg_right hslope hweight
    nlinarith [show x ^ (k + 1) = x ^ k * x by rw [pow_succ]]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add
      ((integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k).const_mul
        thetaCuspFirstAtomBoundaryLogSlope)
      (integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source k),
    MeasureTheory.integral_const_mul,
    ← thetaCuspTotalMoment_eq_integral_Ioi,
    ← thetaCuspTotalMoment_eq_integral_Ioi,
    thetaCuspSourcePotentialSlope_moment_eq hk] at hmono
  exact hmono

theorem thetaCuspTotalMoment_pos (k : ℕ) :
    0 < thetaCuspTotalMoment k := by
  let f : ℝ → ℝ := fun x => x ^ k * thetaCuspSourceTerm x 1
  have hfcont : Continuous f := by
    dsimp [f]
    exact (continuous_id.pow k).mul continuous_thetaCuspSourceTerm_one
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa [f] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le k)
      (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  rw [thetaCuspTotalMoment_eq_integral_Ioi]
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  exact ne_of_gt (mul_pos (by positivity)
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos (by norm_num) (by norm_num)))

theorem thetaCuspTotalMoment_cauchySchwarz (a b : ℕ) :
    thetaCuspTotalMoment (a + b) ^ 2 ≤
      thetaCuspTotalMoment (2 * a) * thetaCuspTotalMoment (2 * b) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let ρ : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  let f : ℝ → ℝ := fun x => x ^ a * Real.sqrt (ρ x)
  let g : ℝ → ℝ := fun x => x ^ b * Real.sqrt (ρ x)
  have hρcont : Continuous ρ := by
    dsimp [ρ]
    exact continuous_thetaCuspSourceTerm_one
  have hfmeas : AEStronglyMeasurable f μ := by
    exact ((continuous_id.pow a).mul
      (Real.continuous_sqrt.comp hρcont)).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g μ := by
    exact ((continuous_id.pow b).mul
      (Real.continuous_sqrt.comp hρcont)).aestronglyMeasurable
  have hf2 : Integrable (fun x => f x ^ 2) μ := by
    apply (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (2 * a)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hρ : 0 ≤ ρ x := by
      exact thetaCuspSourceTerm_nonneg_of_pos hx 1
    dsimp [f, ρ] at hρ ⊢
    rw [mul_pow, Real.sq_sqrt hρ, ← pow_mul]
    congr 2
    omega
  have hg2 : Integrable (fun x => g x ^ 2) μ := by
    apply (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (2 * b)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hρ : 0 ≤ ρ x := by
      exact thetaCuspSourceTerm_nonneg_of_pos hx 1
    dsimp [g, ρ] at hρ ⊢
    rw [mul_pow, Real.sq_sqrt hρ, ← pow_mul]
    congr 2
    omega
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    hfmeas hgmeas hf2 hg2
  have hcross : (∫ x, f x * g x ∂μ) = thetaCuspTotalMoment (a + b) := by
    rw [thetaCuspTotalMoment_eq_integral_Ioi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hρ : 0 ≤ ρ x := thetaCuspSourceTerm_nonneg_of_pos hx 1
    dsimp [f, g, ρ] at hρ ⊢
    calc
      x ^ a * Real.sqrt (thetaCuspSourceTerm x 1) *
          (x ^ b * Real.sqrt (thetaCuspSourceTerm x 1)) =
          (x ^ a * x ^ b) *
            (Real.sqrt (thetaCuspSourceTerm x 1) *
              Real.sqrt (thetaCuspSourceTerm x 1)) := by ring
      _ = (x ^ a * x ^ b) * thetaCuspSourceTerm x 1 := by
        rw [Real.mul_self_sqrt hρ]
      _ = x ^ (a + b) * thetaCuspSourceTerm x 1 := by rw [pow_add]
  have hf2eq : (∫ x, f x ^ 2 ∂μ) = thetaCuspTotalMoment (2 * a) := by
    rw [thetaCuspTotalMoment_eq_integral_Ioi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hρ : 0 ≤ ρ x := thetaCuspSourceTerm_nonneg_of_pos hx 1
    dsimp [f, ρ] at hρ ⊢
    rw [mul_pow, Real.sq_sqrt hρ, ← pow_mul]
    congr 2
    omega
  have hg2eq : (∫ x, g x ^ 2 ∂μ) = thetaCuspTotalMoment (2 * b) := by
    rw [thetaCuspTotalMoment_eq_integral_Ioi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hρ : 0 ≤ ρ x := thetaCuspSourceTerm_nonneg_of_pos hx 1
    dsimp [g, ρ] at hρ ⊢
    rw [mul_pow, Real.sq_sqrt hρ, ← pow_mul]
    congr 2
    omega
  rwa [hcross, hf2eq, hg2eq] at hcs

/-- Location of the positive crossing-window peak of order `m`. -/
def thetaCuspCrossingPeak (m : ℕ) : ℝ :=
  Real.sqrt
    (thetaCuspTotalMoment (2 * m + 2) / thetaCuspTotalMoment (2 * m))

theorem thetaCuspCrossingPeak_pos (m : ℕ) :
    0 < thetaCuspCrossingPeak m := by
  unfold thetaCuspCrossingPeak
  exact Real.sqrt_pos.2
    (div_pos (thetaCuspTotalMoment_pos (2 * m + 2))
      (thetaCuspTotalMoment_pos (2 * m)))

theorem thetaCuspCrossingPeak_sq (m : ℕ) :
    thetaCuspCrossingPeak m ^ 2 =
      thetaCuspTotalMoment (2 * m + 2) / thetaCuspTotalMoment (2 * m) := by
  unfold thetaCuspCrossingPeak
  exact Real.sq_sqrt
    (div_nonneg (thetaCuspTotalMoment_pos (2 * m + 2)).le
      (thetaCuspTotalMoment_pos (2 * m)).le)

theorem thetaCuspOddMoment_le_crossingPeak_mul_even (m : ℕ) :
    thetaCuspTotalMoment (2 * m + 1) ≤
      thetaCuspCrossingPeak m * thetaCuspTotalMoment (2 * m) := by
  have hcs : thetaCuspTotalMoment (2 * m + 1) ^ 2 ≤
      thetaCuspTotalMoment (2 * m) * thetaCuspTotalMoment (2 * m + 2) := by
    simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      thetaCuspTotalMoment_cauchySchwarz m (m + 1)
  have hM := thetaCuspTotalMoment_pos (2 * m)
  have hodd := thetaCuspTotalMoment_pos (2 * m + 1)
  have htau := thetaCuspCrossingPeak_pos m
  have hsq := thetaCuspCrossingPeak_sq m
  have htarget :
      (thetaCuspCrossingPeak m * thetaCuspTotalMoment (2 * m)) ^ 2 =
        thetaCuspTotalMoment (2 * m) * thetaCuspTotalMoment (2 * m + 2) := by
    rw [mul_pow, hsq]
    field_simp [hM.ne']
  rw [← htarget] at hcs
  exact (sq_le_sq₀ hodd.le (mul_nonneg htau.le hM.le)).mp hcs

theorem thetaCuspCrossingPeak_quadratic (m : ℕ) :
    19 * thetaCuspCrossingPeak m ^ 2 ≤
      thetaCuspFirstAtomBoundaryLogSlope * thetaCuspCrossingPeak m +
        (2 * m + 1 : ℕ) := by
  have hM := thetaCuspTotalMoment_pos (2 * m)
  have hrec := thetaCuspTotalMoment_curvature_recurrence
    (k := 2 * m + 1) (by omega)
  have hodd := thetaCuspOddMoment_le_crossingPeak_mul_even m
  have hs0 := thetaCuspFirstAtomBoundaryLogSlope_pos.le
  have hs0odd := mul_le_mul_of_nonneg_left hodd hs0
  have hsq := thetaCuspCrossingPeak_sq m
  have hmul :
      (19 * thetaCuspCrossingPeak m ^ 2) * thetaCuspTotalMoment (2 * m) ≤
        (thetaCuspFirstAtomBoundaryLogSlope * thetaCuspCrossingPeak m +
          ((2 * m + 1 : ℕ) : ℝ)) * thetaCuspTotalMoment (2 * m) := by
    calc
    (19 * thetaCuspCrossingPeak m ^ 2) * thetaCuspTotalMoment (2 * m) =
        19 * thetaCuspTotalMoment (2 * m + 2) := by
      rw [hsq]
      field_simp [hM.ne']
    _ ≤ thetaCuspFirstAtomBoundaryLogSlope *
          thetaCuspTotalMoment (2 * m + 1) +
        ((2 * m + 1 : ℕ) : ℝ) * thetaCuspTotalMoment (2 * m) := by
      simpa [Nat.add_assoc] using hrec
    _ ≤ thetaCuspFirstAtomBoundaryLogSlope *
          (thetaCuspCrossingPeak m * thetaCuspTotalMoment (2 * m)) +
        ((2 * m + 1 : ℕ) : ℝ) * thetaCuspTotalMoment (2 * m) := by
      exact add_le_add hs0odd (le_refl _)
    _ = (thetaCuspFirstAtomBoundaryLogSlope * thetaCuspCrossingPeak m +
          ((2 * m + 1 : ℕ) : ℝ)) * thetaCuspTotalMoment (2 * m) := by ring
  by_contra hnot
  have hstrict :
      thetaCuspFirstAtomBoundaryLogSlope * thetaCuspCrossingPeak m +
          ((2 * m + 1 : ℕ) : ℝ) < 19 * thetaCuspCrossingPeak m ^ 2 :=
    lt_of_not_ge hnot
  have := mul_lt_mul_of_pos_right hstrict hM
  exact (not_lt_of_ge hmul) this

theorem thetaCuspCrossingPeak_one_lt_two_thirds :
    thetaCuspCrossingPeak 1 < 2 / 3 := by
  have hq := thetaCuspCrossingPeak_quadratic 1
  have ht := thetaCuspCrossingPeak_pos 1
  have hs0 := thetaCuspFirstAtomBoundaryLogSlope_lt_one_half
  norm_num at hq ⊢
  by_contra hnot
  have hlower : (2 / 3 : ℝ) ≤ thetaCuspCrossingPeak 1 := le_of_not_gt hnot
  nlinarith [sq_nonneg (thetaCuspCrossingPeak 1 - 2 / 3)]

theorem thetaCuspCrossingPeak_two_lt_two_thirds :
    thetaCuspCrossingPeak 2 < 2 / 3 := by
  have hq := thetaCuspCrossingPeak_quadratic 2
  have ht := thetaCuspCrossingPeak_pos 2
  have hs0 := thetaCuspFirstAtomBoundaryLogSlope_lt_one_half
  norm_num at hq ⊢
  by_contra hnot
  have hlower : (2 / 3 : ℝ) ≤ thetaCuspCrossingPeak 2 := le_of_not_gt hnot
  nlinarith [sq_nonneg (thetaCuspCrossingPeak 2 - 2 / 3)]

theorem thetaCuspCrossingPeak_one_le_two :
    thetaCuspCrossingPeak 1 ≤ thetaCuspCrossingPeak 2 := by
  have hcs : thetaCuspTotalMoment 4 ^ 2 ≤
      thetaCuspTotalMoment 2 * thetaCuspTotalMoment 6 := by
    simpa using thetaCuspTotalMoment_cauchySchwarz 1 3
  have hM2 := thetaCuspTotalMoment_pos 2
  have hM4 := thetaCuspTotalMoment_pos 4
  have hratio : thetaCuspTotalMoment 4 / thetaCuspTotalMoment 2 ≤
      thetaCuspTotalMoment 6 / thetaCuspTotalMoment 4 := by
    apply (div_le_div_iff₀ hM2 hM4).2
    nlinarith
  have hsq1 := thetaCuspCrossingPeak_sq 1
  have hsq2 := thetaCuspCrossingPeak_sq 2
  norm_num at hsq1 hsq2
  have ht1 := thetaCuspCrossingPeak_pos 1
  have ht2 := thetaCuspCrossingPeak_pos 2
  nlinarith [sq_nonneg (thetaCuspCrossingPeak 1 + thetaCuspCrossingPeak 2)]

theorem two_thirds_lt_log_two : (2 / 3 : ℝ) < Real.log 2 := by
  exact lt_trans (by norm_num) Real.log_two_gt_d9

theorem thetaCuspLivePeaks_before_firstArithmeticShift :
    thetaCuspCrossingPeak 1 ≤ thetaCuspCrossingPeak 2 ∧
      thetaCuspCrossingPeak 2 < 2 / 3 ∧
        (2 / 3 : ℝ) < Real.log 2 :=
  ⟨thetaCuspCrossingPeak_one_le_two,
    thetaCuspCrossingPeak_two_lt_two_thirds, two_thirds_lt_log_two⟩

/-! ### One-seam regular curvature -/

def thetaCuspFirstLogThirdDerivative (x : ℝ) : ℝ :=
  thetaCuspBornWittenLogThirdDerivative 1 x

def thetaCuspThirdDerivativeCoordinate (x : ℝ) : ℝ :=
  2 * thetaCuspBornWittenWeight 1 x

def thetaCuspThirdDerivativeCubic (y : ℝ) : ℝ :=
  y ^ 3 - 6 * y - 36

theorem thetaCuspFirstLogThirdDerivative_eq_cubic
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFirstLogThirdDerivative x =
      4 * (thetaCuspThirdDerivativeCoordinate x + 3) *
          thetaCuspThirdDerivativeCubic (thetaCuspThirdDerivativeCoordinate x) /
        thetaCuspThirdDerivativeCoordinate x ^ 3 := by
  have hq := thetaCuspBornWittenWeight_pos
    (n := 1) (by norm_num) hx
  unfold thetaCuspFirstLogThirdDerivative
    thetaCuspThirdDerivativeCoordinate thetaCuspThirdDerivativeCubic
    thetaCuspBornWittenLogThirdDerivative
  field_simp [hq.ne']
  ring

theorem thetaCuspBornWittenLogFourthDerivative_one_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenLogFourthDerivative 1 x := by
  have hq := thetaCuspBornWittenWeight_pos
    (n := 1) (by norm_num) hx
  unfold thetaCuspBornWittenLogFourthDerivative
  positivity

theorem hasDerivAt_thetaCuspFirstLogThirdDerivative
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspFirstLogThirdDerivative
      (thetaCuspBornWittenLogFourthDerivative 1 x) x := by
  change HasDerivAt (thetaCuspBornWittenLogThirdDerivative 1)
    (thetaCuspBornWittenLogFourthDerivative 1 x) x
  exact hasDerivAt_thetaCuspBornWittenLogThirdDerivative
    (n := 1) (by norm_num) hx

theorem thetaCuspFirstLogThirdDerivative_strictMonoOn_Ici :
    StrictMonoOn thetaCuspFirstLogThirdDerivative (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspFirstLogThirdDerivative hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_thetaCuspFirstLogThirdDerivative hx.le).deriv]
    exact thetaCuspBornWittenLogFourthDerivative_one_pos hx.le

theorem thetaCuspThirdDerivativeCoordinate_zero :
    thetaCuspThirdDerivativeCoordinate 0 = 2 * Real.pi - 3 := by
  unfold thetaCuspThirdDerivativeCoordinate
  rw [thetaCuspBornWittenWeight_eq]
  simp [thetaCuspMorseScale]
  ring

theorem thetaCuspBornWittenWeight_log_two :
    thetaCuspBornWittenWeight 1 (Real.log 2) = 4 * Real.pi - 3 / 2 := by
  rw [thetaCuspBornWittenWeight_eq]
  unfold thetaCuspMorseScale
  norm_num only [Nat.cast_one, one_mul, one_pow]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

theorem thetaCuspThirdDerivativeCoordinate_log_two :
    thetaCuspThirdDerivativeCoordinate (Real.log 2) = 8 * Real.pi - 3 := by
  unfold thetaCuspThirdDerivativeCoordinate
  rw [thetaCuspBornWittenWeight_log_two]
  ring

theorem thetaCuspFirstLogThirdDerivative_zero_neg :
    thetaCuspFirstLogThirdDerivative 0 < 0 := by
  let y : ℝ := thetaCuspThirdDerivativeCoordinate 0
  have hy : y = 2 * Real.pi - 3 := thetaCuspThirdDerivativeCoordinate_zero
  have hy3 : 3 < y := by rw [hy]; nlinarith [Real.pi_gt_three]
  have hyUpper : y < 23 / 7 := by
    rw [hy]
    nlinarith [Real.pi_lt_d4]
  have hyCube : y ^ 3 < (23 / 7 : ℝ) ^ 3 := by
    exact pow_lt_pow_left₀ hyUpper
      (le_trans (by norm_num : (0 : ℝ) ≤ 3) hy3.le) (by norm_num)
  have hcubic : thetaCuspThirdDerivativeCubic y < 0 := by
    unfold thetaCuspThirdDerivativeCubic
    nlinarith
  rw [thetaCuspFirstLogThirdDerivative_eq_cubic (by norm_num)]
  change 4 * (y + 3) * thetaCuspThirdDerivativeCubic y / y ^ 3 < 0
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos (by norm_num) (by linarith)) hcubic)
    (pow_pos (lt_trans (by norm_num) hy3) 3)

theorem thetaCuspFirstLogThirdDerivative_log_two_pos :
    0 < thetaCuspFirstLogThirdDerivative (Real.log 2) := by
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  let y : ℝ := thetaCuspThirdDerivativeCoordinate (Real.log 2)
  have hy : y = 8 * Real.pi - 3 := thetaCuspThirdDerivativeCoordinate_log_two
  have hy4 : 4 < y := by rw [hy]; nlinarith [Real.pi_gt_three]
  have hfactor : 0 < y ^ 2 + 4 * y + 10 := by nlinarith [sq_nonneg y]
  have hcubic : 0 < thetaCuspThirdDerivativeCubic y := by
    unfold thetaCuspThirdDerivativeCubic
    have hprod := mul_pos (sub_pos.mpr hy4) hfactor
    nlinarith
  rw [thetaCuspFirstLogThirdDerivative_eq_cubic hlog]
  change 0 < 4 * (y + 3) * thetaCuspThirdDerivativeCubic y / y ^ 3
  exact div_pos
    (mul_pos (mul_pos (by norm_num) (by linarith)) hcubic)
    (pow_pos (lt_trans (by norm_num) hy4) 3)

theorem existsUnique_thetaCuspThirdDerivativeSeam :
    ∃! d : ℝ, 0 < d ∧ d < Real.log 2 ∧
      thetaCuspFirstLogThirdDerivative d = 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : ContinuousOn thetaCuspFirstLogThirdDerivative
      (Icc (0 : ℝ) (Real.log 2)) := by
    intro x hx
    exact (hasDerivAt_thetaCuspFirstLogThirdDerivative hx.1).continuousAt.continuousWithinAt
  have hzeroMem : (0 : ℝ) ∈ Icc
      (thetaCuspFirstLogThirdDerivative 0)
      (thetaCuspFirstLogThirdDerivative (Real.log 2)) :=
    ⟨thetaCuspFirstLogThirdDerivative_zero_neg.le,
      thetaCuspFirstLogThirdDerivative_log_two_pos.le⟩
  rcases (intermediate_value_Icc hlog.le hcont hzeroMem) with
    ⟨d, hdIcc, hd0⟩
  have hdpos : 0 < d := by
    rcases hdIcc.1.eq_or_lt with h | h
    · subst d
      linarith [thetaCuspFirstLogThirdDerivative_zero_neg]
    · exact h
  have hdlt : d < Real.log 2 := by
    rcases hdIcc.2.eq_or_lt with h | h
    · subst d
      linarith [thetaCuspFirstLogThirdDerivative_log_two_pos]
    · exact h
  refine ⟨d, ⟨hdpos, hdlt, hd0⟩, ?_⟩
  intro e he
  exact (thetaCuspFirstLogThirdDerivative_strictMonoOn_Ici.injOn
    hdpos.le he.1.le (hd0.trans he.2.2.symm)).symm

noncomputable def thetaCuspThirdDerivativeSeam : ℝ :=
  Classical.choose existsUnique_thetaCuspThirdDerivativeSeam

theorem thetaCuspThirdDerivativeSeam_spec :
    0 < thetaCuspThirdDerivativeSeam ∧
      thetaCuspThirdDerivativeSeam < Real.log 2 ∧
        thetaCuspFirstLogThirdDerivative thetaCuspThirdDerivativeSeam = 0 :=
  (Classical.choose_spec existsUnique_thetaCuspThirdDerivativeSeam).1

def thetaCuspRegularCurvatureNumerator (x : ℝ) : ℝ :=
  x * thetaCuspBornWittenLogCurvature 1 x -
    (thetaCuspFirstLogPotentialSlope x - thetaCuspFirstLogPotentialSlope 0)

def thetaCuspRegularSlopeCurvature (x : ℝ) : ℝ :=
  thetaCuspRegularCurvatureNumerator x / x ^ 2

def thetaCuspRegularSlopeQuotient (x : ℝ) : ℝ :=
  (thetaCuspFirstLogPotentialSlope x - thetaCuspFirstLogPotentialSlope 0) / x

theorem hasDerivAt_thetaCuspRegularSlopeQuotient
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspRegularSlopeQuotient
      (thetaCuspRegularSlopeCurvature x) x := by
  have hslope := hasDerivAt_two_thetaCuspBornWittenSuperpotential
    (n := 1) (by norm_num) hx.le
  have hnum := hslope.sub_const (thetaCuspFirstLogPotentialSlope 0)
  have hquot := hnum.div (hasDerivAt_id x) hx.ne'
  change HasDerivAt
    (fun y : ℝ =>
      (2 * thetaCuspBornWittenSuperpotential 1 y -
        thetaCuspFirstLogPotentialSlope 0) / y)
    (thetaCuspRegularSlopeCurvature x) x
  exact hquot.congr_deriv (by
    simp only [id_eq]
    unfold thetaCuspRegularSlopeCurvature
      thetaCuspRegularCurvatureNumerator
      thetaCuspFirstLogPotentialSlope
    field_simp [hx.ne'])

theorem thetaCuspRegularCurvatureNumerator_zero :
    thetaCuspRegularCurvatureNumerator 0 = 0 := by
  simp [thetaCuspRegularCurvatureNumerator]

theorem hasDerivAt_thetaCuspRegularCurvatureNumerator
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspRegularCurvatureNumerator
      (x * thetaCuspFirstLogThirdDerivative x) x := by
  have hcurv := hasDerivAt_thetaCuspBornWittenLogCurvature
    (n := 1) (by norm_num) hx
  have hslope := hasDerivAt_two_thetaCuspBornWittenSuperpotential
    (n := 1) (by norm_num) hx
  have hraw := (hasDerivAt_id x).mul hcurv
  have hsub := hraw.sub (hslope.sub_const (thetaCuspFirstLogPotentialSlope 0))
  have hsub' := hsub.congr_deriv
    (g' := x * thetaCuspFirstLogThirdDerivative x) (by
      simp only [id_eq, one_mul, thetaCuspFirstLogThirdDerivative]
      ring)
  change HasDerivAt
    (fun y : ℝ => y * thetaCuspBornWittenLogCurvature 1 y -
      ((2 * thetaCuspBornWittenSuperpotential 1 y) -
        thetaCuspFirstLogPotentialSlope 0))
    (x * thetaCuspFirstLogThirdDerivative x) x
  apply hsub'.congr_of_eventuallyEq
  filter_upwards with y
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq]

theorem thetaCuspFirstLogThirdDerivative_neg_before_seam
    {x : ℝ} (hx : 0 ≤ x) (hxd : x < thetaCuspThirdDerivativeSeam) :
    thetaCuspFirstLogThirdDerivative x < 0 := by
  have h := thetaCuspFirstLogThirdDerivative_strictMonoOn_Ici
    hx thetaCuspThirdDerivativeSeam_spec.1.le hxd
  simpa [thetaCuspThirdDerivativeSeam_spec.2.2] using h

theorem thetaCuspFirstLogThirdDerivative_pos_after_seam
    {x : ℝ} (hdx : thetaCuspThirdDerivativeSeam < x) :
    0 < thetaCuspFirstLogThirdDerivative x := by
  have h := thetaCuspFirstLogThirdDerivative_strictMonoOn_Ici
    thetaCuspThirdDerivativeSeam_spec.1.le
    (thetaCuspThirdDerivativeSeam_spec.1.trans hdx).le hdx
  simpa [thetaCuspThirdDerivativeSeam_spec.2.2] using h

theorem thetaCuspBornWittenLogCurvature_log_two_gt :
    16 * Real.pi <
      thetaCuspBornWittenLogCurvature 1 (Real.log 2) := by
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile
    (n := 1) (by norm_num) hlog,
    thetaCuspBornWittenWeight_log_two]
  have hq : 0 < 4 * Real.pi - 3 / 2 := by nlinarith [Real.pi_gt_three]
  have hdiv1 : 0 < 6 / (4 * Real.pi - 3 / 2) := div_pos (by norm_num) hq
  have hdiv2 : 0 < 9 / (4 * Real.pi - 3 / 2) ^ 2 := by positivity
  nlinarith

theorem thetaCuspFirstLogPotentialSlope_log_two_sub_zero_lt :
    thetaCuspFirstLogPotentialSlope (Real.log 2) -
      thetaCuspFirstLogPotentialSlope 0 < 6 * Real.pi + 2 := by
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [thetaCuspFirstLogPotentialSlope,
    two_thetaCuspBornWittenSuperpotential_eq_readoutProfile
      (n := 1) (by norm_num) hlog,
    thetaCuspFirstLogPotentialSlope,
    two_thetaCuspBornWittenSuperpotential_eq_readoutProfile
      (n := 1) (by norm_num) (by norm_num),
    thetaCuspBornWittenWeight_log_two]
  have hq0 : thetaCuspBornWittenWeight 1 0 = Real.pi - 3 / 2 := by
    rw [thetaCuspBornWittenWeight_eq]
    simp [thetaCuspMorseScale]
  rw [hq0]
  have hq0pos : 0 < Real.pi - 3 / 2 := by nlinarith [Real.pi_gt_three]
  have hqLpos : 0 < 4 * Real.pi - 3 / 2 := by nlinarith [Real.pi_gt_three]
  have hfrac0 : 3 / (Real.pi - 3 / 2) < 2 := by
    exact (div_lt_iff₀ hq0pos).2 (by nlinarith [Real.pi_gt_three])
  have hfracL : 0 < 3 / (4 * Real.pi - 3 / 2) := div_pos (by norm_num) hqLpos
  nlinarith

theorem thetaCuspRegularCurvatureNumerator_log_two_pos :
    0 < thetaCuspRegularCurvatureNumerator (Real.log 2) := by
  have hlog := two_thirds_lt_log_two
  have hcurv := thetaCuspBornWittenLogCurvature_log_two_gt
  have hslope := thetaCuspFirstLogPotentialSlope_log_two_sub_zero_lt
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hprod : (2 / 3 : ℝ) * (16 * Real.pi) <
      Real.log 2 * thetaCuspBornWittenLogCurvature 1 (Real.log 2) := by
    exact (mul_lt_mul_of_pos_right hlog (by positivity)).trans
      (mul_lt_mul_of_pos_left hcurv (Real.log_pos (by norm_num)))
  unfold thetaCuspRegularCurvatureNumerator
  nlinarith

theorem continuousOn_thetaCuspRegularCurvatureNumerator_Ici :
    ContinuousOn thetaCuspRegularCurvatureNumerator (Ici 0) := by
  intro x hx
  exact (hasDerivAt_thetaCuspRegularCurvatureNumerator hx).continuousAt.continuousWithinAt

theorem thetaCuspRegularCurvatureNumerator_strictAntiOn_initial :
    StrictAntiOn thetaCuspRegularCurvatureNumerator
      (Icc 0 thetaCuspThirdDerivativeSeam) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 thetaCuspThirdDerivativeSeam)
  · exact continuousOn_thetaCuspRegularCurvatureNumerator_Ici.mono
      (fun x hx => hx.1)
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_thetaCuspRegularCurvatureNumerator hx.1.le).deriv]
    exact mul_neg_of_pos_of_neg hx.1
      (thetaCuspFirstLogThirdDerivative_neg_before_seam hx.1.le hx.2)

theorem thetaCuspRegularCurvatureNumerator_seam_neg :
    thetaCuspRegularCurvatureNumerator thetaCuspThirdDerivativeSeam < 0 := by
  have hanti := thetaCuspRegularCurvatureNumerator_strictAntiOn_initial
    (show (0 : ℝ) ∈ Icc 0 thetaCuspThirdDerivativeSeam by
      exact ⟨le_rfl, thetaCuspThirdDerivativeSeam_spec.1.le⟩)
    (show thetaCuspThirdDerivativeSeam ∈ Icc 0 thetaCuspThirdDerivativeSeam by
      exact ⟨thetaCuspThirdDerivativeSeam_spec.1.le, le_rfl⟩)
    thetaCuspThirdDerivativeSeam_spec.1
  rw [thetaCuspRegularCurvatureNumerator_zero] at hanti
  exact hanti

theorem thetaCuspRegularCurvatureNumerator_strictMonoOn_afterThirdSeam :
    StrictMonoOn thetaCuspRegularCurvatureNumerator
      (Ici thetaCuspThirdDerivativeSeam) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici thetaCuspThirdDerivativeSeam)
  · exact continuousOn_thetaCuspRegularCurvatureNumerator_Ici.mono
      (fun x hx => thetaCuspThirdDerivativeSeam_spec.1.le.trans hx)
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_thetaCuspRegularCurvatureNumerator
      (thetaCuspThirdDerivativeSeam_spec.1.trans hx).le).deriv]
    exact mul_pos (thetaCuspThirdDerivativeSeam_spec.1.trans hx)
      (thetaCuspFirstLogThirdDerivative_pos_after_seam hx)

theorem existsUnique_thetaCuspRegularCurvatureSeam :
    ∃! c : ℝ, 0 < c ∧ c < Real.log 2 ∧
      thetaCuspRegularCurvatureNumerator c = 0 := by
  let d := thetaCuspThirdDerivativeSeam
  let L := Real.log 2
  have hdpos : 0 < d := thetaCuspThirdDerivativeSeam_spec.1
  have hdL : d < L := thetaCuspThirdDerivativeSeam_spec.2.1
  have hNd : thetaCuspRegularCurvatureNumerator d < 0 :=
    thetaCuspRegularCurvatureNumerator_seam_neg
  have hNL : 0 < thetaCuspRegularCurvatureNumerator L :=
    thetaCuspRegularCurvatureNumerator_log_two_pos
  have hcont : ContinuousOn thetaCuspRegularCurvatureNumerator (Icc d L) :=
    continuousOn_thetaCuspRegularCurvatureNumerator_Ici.mono
      (fun x hx => hdpos.le.trans hx.1)
  have hzeroMem : (0 : ℝ) ∈ Icc
      (thetaCuspRegularCurvatureNumerator d)
      (thetaCuspRegularCurvatureNumerator L) := ⟨hNd.le, hNL.le⟩
  rcases (intermediate_value_Icc hdL.le hcont hzeroMem) with
    ⟨c, hcIcc, hc0⟩
  have hdc : d < c := by
    rcases hcIcc.1.eq_or_lt with h | h
    · subst c
      linarith
    · exact h
  have hcL : c < L := by
    rcases hcIcc.2.eq_or_lt with h | h
    · subst c
      linarith
    · exact h
  have hcpos : 0 < c := hdpos.trans hdc
  refine ⟨c, ⟨hcpos, hcL, hc0⟩, ?_⟩
  intro e he
  have hde : d < e := by
    by_contra hnot
    have hed : e ≤ d := le_of_not_gt hnot
    have heIcc : e ∈ Icc (0 : ℝ) d := ⟨he.1.le, hed⟩
    have hanti := thetaCuspRegularCurvatureNumerator_strictAntiOn_initial
      (show (0 : ℝ) ∈ Icc 0 d by exact ⟨le_rfl, hdpos.le⟩)
      heIcc he.1
    rw [thetaCuspRegularCurvatureNumerator_zero, he.2.2] at hanti
    linarith
  exact (thetaCuspRegularCurvatureNumerator_strictMonoOn_afterThirdSeam.injOn
    hdc.le hde.le (hc0.trans he.2.2.symm)).symm

noncomputable def thetaCuspRegularCurvatureSeam : ℝ :=
  Classical.choose existsUnique_thetaCuspRegularCurvatureSeam

theorem thetaCuspRegularCurvatureSeam_spec :
    0 < thetaCuspRegularCurvatureSeam ∧
      thetaCuspRegularCurvatureSeam < Real.log 2 ∧
        thetaCuspRegularCurvatureNumerator thetaCuspRegularCurvatureSeam = 0 :=
  (Classical.choose_spec existsUnique_thetaCuspRegularCurvatureSeam).1

theorem thetaCuspRegularCurvatureNumerator_neg_before_seam
    {x : ℝ} (hx : 0 < x) (hxc : x < thetaCuspRegularCurvatureSeam) :
    thetaCuspRegularCurvatureNumerator x < 0 := by
  by_cases hxd : x ≤ thetaCuspThirdDerivativeSeam
  · have hanti := thetaCuspRegularCurvatureNumerator_strictAntiOn_initial
      (show (0 : ℝ) ∈ Icc 0 thetaCuspThirdDerivativeSeam by
        exact ⟨le_rfl, thetaCuspThirdDerivativeSeam_spec.1.le⟩)
      (show x ∈ Icc 0 thetaCuspThirdDerivativeSeam by exact ⟨hx.le, hxd⟩) hx
    rw [thetaCuspRegularCurvatureNumerator_zero] at hanti
    exact hanti
  · have hdx : thetaCuspThirdDerivativeSeam < x := lt_of_not_ge hxd
    have hmono := thetaCuspRegularCurvatureNumerator_strictMonoOn_afterThirdSeam
      hdx.le
      (hdx.trans hxc).le hxc
    rw [thetaCuspRegularCurvatureSeam_spec.2.2] at hmono
    exact hmono

theorem thetaCuspRegularCurvatureNumerator_pos_after_seam
    {x : ℝ} (hcx : thetaCuspRegularCurvatureSeam < x) :
    0 < thetaCuspRegularCurvatureNumerator x := by
  have hdc : thetaCuspThirdDerivativeSeam < thetaCuspRegularCurvatureSeam := by
    by_contra hnot
    have hcd := le_of_not_gt hnot
    have hcIcc : thetaCuspRegularCurvatureSeam ∈
        Icc (0 : ℝ) thetaCuspThirdDerivativeSeam :=
      ⟨thetaCuspRegularCurvatureSeam_spec.1.le, hcd⟩
    have hanti := thetaCuspRegularCurvatureNumerator_strictAntiOn_initial
      (show (0 : ℝ) ∈ Icc 0 thetaCuspThirdDerivativeSeam by
        exact ⟨le_rfl, thetaCuspThirdDerivativeSeam_spec.1.le⟩)
      hcIcc thetaCuspRegularCurvatureSeam_spec.1
    rw [thetaCuspRegularCurvatureNumerator_zero,
      thetaCuspRegularCurvatureSeam_spec.2.2] at hanti
    linarith
  have hmono := thetaCuspRegularCurvatureNumerator_strictMonoOn_afterThirdSeam
    hdc.le (hdc.trans hcx).le hcx
  rw [thetaCuspRegularCurvatureSeam_spec.2.2] at hmono
  exact hmono

theorem thetaCuspRegularSlopeCurvature_signLaw :
    (∀ x : ℝ, 0 < x → x < thetaCuspRegularCurvatureSeam →
      thetaCuspRegularSlopeCurvature x < 0) ∧
    thetaCuspRegularSlopeCurvature thetaCuspRegularCurvatureSeam = 0 ∧
    (∀ x : ℝ, thetaCuspRegularCurvatureSeam < x →
      0 < thetaCuspRegularSlopeCurvature x) := by
  constructor
  · intro x hx hxc
    exact div_neg_of_neg_of_pos
      (thetaCuspRegularCurvatureNumerator_neg_before_seam hx hxc)
      (sq_pos_of_pos hx)
  constructor
  · unfold thetaCuspRegularSlopeCurvature
    rw [thetaCuspRegularCurvatureSeam_spec.2.2, zero_div]
  · intro x hcx
    exact div_pos
      (thetaCuspRegularCurvatureNumerator_pos_after_seam hcx)
      (sq_pos_of_pos (thetaCuspRegularCurvatureSeam_spec.1.trans hcx))

theorem thetaCuspRegularCurvatureSeam_before_arithmeticTranslate
    {n : ℕ} (hn : 2 ≤ n) :
    thetaCuspRegularCurvatureSeam < Real.log (n : ℝ) := by
  have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hcast
  exact thetaCuspRegularCurvatureSeam_spec.2.1.trans_le hlog

end RHTower
