import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.FuchsProlateScale

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
    convert hhalf using 1 <;> congr 1 <;> ring
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

end RHTower
