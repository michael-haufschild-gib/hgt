import GaloisForLFunctions.HTGeometry.EvenHermitianCanonicalFactor
import GaloisForLFunctions.HTGeometry.EvenHermitianAxisMultiplicity
import GaloisForLFunctions.HTGeometry.CanonicalProductSubquadraticType
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.HTGeometry.EvenEntireAxisType

/-!
# Exact even Hermitian factorization from axis positivity

The origin and axis multiplicities are discharged from positivity. The output
is an actual entire even factor, not a divisor or square-root assumption.
-/

open Complex Filter Topology Set RHTower
open scoped ComplexConjugate
open GaloisForLFunctions.CountableDivisor GaloisForLFunctions.EntireZeroDivisor

noncomputable section
namespace GaloisForLFunctions.HTGeometry.EvenHermitianFactor

theorem orderOne_growth_of_power_factor {f g : ℂ → ℂ} {n : ℕ} {C : ℝ}
    (hC : 0≤C) (hg : Continuous g) (hfg : ∀ z,f z=z^n*g z)
    (hb : ∀ z,‖f z‖≤Real.exp (C*(1+‖z‖)*Real.log (2+‖z‖))) :
    ∃ D : ℝ,0≤D ∧ ∀ z,‖g z‖≤Real.exp (D*(1+‖z‖)*Real.log (2+‖z‖)) := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hg.continuousOn
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let D := C+|M|/Real.log 2
  have hDC : C≤D := by
    dsimp [D]
    linarith [div_nonneg (abs_nonneg M) hl2.le]
  have hD : 0≤D := hC.trans hDC
  refine ⟨D,hD,fun z => ?_⟩
  have hl : Real.log 2≤Real.log (2+‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  have hw : Real.log 2≤(1+‖z‖)*Real.log (2+‖z‖) := by
    nlinarith [norm_nonneg z,mul_nonneg (norm_nonneg z) hl2.le]
  have hmono : C*(1+‖z‖)*Real.log (2+‖z‖)≤D*(1+‖z‖)*Real.log (2+‖z‖) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC (by positivity)) (hl2.le.trans hl)
  by_cases hz : ‖z‖≤1
  · have hm : ‖g z‖≤|M| := (hM z (mem_closedBall_zero_iff.mpr hz)).trans (le_abs_self M)
    apply hm.trans
    apply (show |M|≤Real.exp |M| by linarith [Real.add_one_le_exp |M|]).trans
    apply Real.exp_le_exp.mpr
    have hd : |M|/Real.log 2≤D := by dsimp [D]; linarith
    have hdw := mul_le_mul_of_nonneg_right hd (hl2.le.trans hw)
    have hmw := mul_le_mul_of_nonneg_left hw (div_nonneg (abs_nonneg M) hl2.le)
    rw [div_mul_cancel₀ _ hl2.ne'] at hmw
    nlinarith
  · have hp : 1≤‖z‖^n := one_le_pow₀ (le_of_not_ge hz)
    have hn : ‖g z‖≤‖f z‖ := by
      rw [hfg z,norm_mul,norm_pow]
      nlinarith [norm_nonneg (g z)]
    exact hn.trans ((hb z).trans (Real.exp_le_exp.mpr hmono))

theorem schwarz_of_axisNonnegative {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (ha : AxisNonnegative f) : ∀ z,f (conj z)=conj (f z) := by
  have hr : ∀ x : ℝ,conj (f x)=f x := by
    intro x
    have hi : (f (x : ℂ)).im=0 := (ha (x : ℂ) (Or.inr (by simp))).1
    apply Complex.ext
    · rfl
    · simp only [Complex.conj_im,hi,neg_zero]
  have hd := RHTower.differentiable_conj_reflect hf
  have heq : (fun z => conj (f (conj z)))=f := by
    funext z
    apply sub_eq_zero.mp
    exact entire_eq_zero_of_vanishing_on_real_interval (hd.sub hf)
      (t₀ := 0) (r := 1) (by norm_num)
      (fun x _ => by simp [hr]) z
  intro z
  have hh := congrArg conj (congrFun heq z)
  simpa only [Complex.conj_conj] using hh

/-- Exact even spectral factorization, including zero functions and origin
zeros. Both axis multiplicity conditions are proved from axis positivity. -/
theorem exists_even_entire_factor_subquadratic {f : ℂ → ℂ} {C : ℝ} (hC : 0≤C)
    (hf : Differentiable ℂ f) (he : Function.Even f) (ha : AxisNonnegative f)
    (hb : ∀ z,‖f z‖≤Real.exp (C*(1+‖z‖)*Real.log (2+‖z‖))) :
    ∃ q : ℂ → ℂ,Differentiable ℂ q ∧ Function.Even q ∧
      (∀ z,f z=q z*conj (q (conj z))) ∧ SubquadraticType q := by
  by_cases hn : ∃ z,f z≠0
  · obtain ⟨k,g,hg,hge,hga,hgim,hgpos,hfg⟩ := exists_origin_four_power_factor hf he ha hn
    obtain ⟨D,hD,hgb⟩ := orderOne_growth_of_power_factor hC hg.continuous hfg hb
    have hgan : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
    have hg0 : g 0≠0 := fun h => by simp [h] at hgpos
    have hgr := schwarz_of_axisNonnegative hg hga
    have hmult (z : ℂ) (hz : z.re=0 ∨ z.im=0) : Even (multiplicity g z) := by
      have hfin := GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hg hg0
      have hh := congrArg ENat.toNat (multiplicity_cast_eq_order hgan hfin z)
      simp only [ENat.toNat_coe] at hh
      rw [hh]
      exact even_order_axis hg hga z hz
    have hidentity := eq_origin_mul_factor_mul_sharp hD hgan hg0 hge hgr hmult hgb
    have hs := RHTower.OrderOneHadamard.summable_inv_sq_zeroCopyPoint hD hgan hg0 hgb
    have hQ := factor_analytic hgan hg0 hs
    let a : ℂ := Real.sqrt (g 0).re
    let q := fun z : ℂ => a*z^(2*k)*factor g z
    have ha2 : a*a=g 0 := by
      dsimp [a]
      rw [← Complex.ofReal_mul,← pow_two,Real.sq_sqrt hgpos.le]
      exact Complex.ext (by simp) (by simpa using hgim.symm)
    refine ⟨q,?_,?_,?_,?_⟩
    · exact (((differentiable_const a).mul (by fun_prop)).mul
        (fun z => (hQ z (mem_univ _)).differentiableAt))
    · intro z
      simp only [q,Even.neg_pow (even_two_mul k),factor_even hgan hge]
    · intro z
      rw [hfg z,hidentity z]
      simp only [q,map_mul,map_pow,Complex.conj_conj,show conj a=a by simp [a],sharpFactor]
      calc
        z^(4*k)*(g 0*(factor g z*conj (factor g (conj z)))) =
            (a*a)*(z^(2*k)*z^(2*k))*(factor g z*conj (factor g (conj z))) := by
          rw [ha2,← pow_add,show 2*k+2*k=4*k by omega]
          ring
        _ = _ := by ring
    · apply SubquadraticType.const_mul_pow (a := a) (n := 2*k)
      have hd := orderOneDensityIdx_zeroCopyPoint hD hgan hg0 hgb
      have hsp := summable_rpow_neg_of_orderOneDensity (locallyFinite_zeroCopyPoint hgan) hd
        (p := (3/2 : ℝ)) (by norm_num)
      have hsp' : Summable fun i : SelectedCopy g => ‖selectedPoint g i‖^(-(3/2 : ℝ)) := hsp.subtype _
      refine ⟨3/2,by norm_num,by norm_num,1,2*∑' i : SelectedCopy g,‖selectedPoint g i‖^(-(3/2 : ℝ)),
        zero_le_one,by positivity,fun z => ?_⟩
      simpa only [one_mul,factor] using canonicalProduct_norm_le_exp_rpow (selectedPoint g)
        (selectedPoint_ne_zero hgan hg0) (summable_selectedPoint_inv_sq hs)
        (by norm_num : (1:ℝ)≤3/2) (by norm_num : (3/2:ℝ)≤2) hsp' z
  · push Not at hn
    exact ⟨fun _ => 0,differentiable_const 0,fun _ => rfl,fun z => by simp [hn z],
      1,le_rfl,by norm_num,0,0,le_rfl,le_rfl,by simp⟩

theorem exists_even_entire_factor {f : ℂ → ℂ} {C : ℝ} (hC : 0≤C)
    (hf : Differentiable ℂ f) (he : Function.Even f) (ha : AxisNonnegative f)
    (hb : ∀ z,‖f z‖≤Real.exp (C*(1+‖z‖)*Real.log (2+‖z‖))) :
    ∃ q : ℂ → ℂ,Differentiable ℂ q ∧ Function.Even q ∧
      (∀ z,f z=q z*conj (q (conj z))) := by
  obtain ⟨q,hq,he,hid,_⟩ := exists_even_entire_factor_subquadratic hC hf he ha hb
  exact ⟨q,hq,he,hid⟩

end GaloisForLFunctions.HTGeometry.EvenHermitianFactor
