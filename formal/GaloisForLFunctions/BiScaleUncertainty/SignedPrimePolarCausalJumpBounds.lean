import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceJumpUpper
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalEnergy

/-! Quantitative cancellation of the actual signed archimedean contrast. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem abs_sourceFactorialCausal_linear {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) :
    |sourceFactorialCausal N x| ≤ 20000*(N : ℝ)^4*x := by
  let δ := sourceFactorialWidth N
  have hδ := sourceFactorialWidth_pos hN
  have he : Real.exp δ ≤ 2 :=
    (Real.exp_le_exp.mpr (by dsimp [δ]; linarith)).trans (exp_four_sourceFactorialWidth_le_two hN)
  have hc : Continuous (fun t => exponentialTentDensity δ t*
      (Real.exp (t/2)*sourceFactorialRamp N (x-t))) :=
    (continuous_exponentialTentDensity δ).mul
      ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
        ((continuous_sourceFactorialRamp N).comp (continuous_const.sub continuous_id)))
  calc
    _ ≤ ∫ t in Icc 0 (2*δ), |exponentialTentDensity δ t*(Real.exp (t/2)*sourceFactorialRamp N (x-t))| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Icc 0 (2*δ), exponentialTentDensity δ t*(20000*(N : ℝ)^4*x) := by
      apply setIntegral_mono_on hc.abs.integrableOn_Icc
        (((continuous_exponentialTentDensity δ).mul continuous_const).integrableOn_Icc) measurableSet_Icc
      intro t ht
      have hb := sourceFactorialRamp_abs_sub_le hN (x-t) (-t)
      rw [sourceFactorialRamp_zero_of_nonpos hN (by linarith [ht.1]), sub_zero,
        show x-t-(-t) = x by ring, abs_of_nonneg hx] at hb
      have het : Real.exp (t/2) ≤ 2 := (Real.exp_le_exp.mpr (by linarith [ht.2])).trans he
      rw [abs_mul, abs_mul, abs_of_nonneg (exponentialTentDensity_nonneg δ t), abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (exponentialTentDensity_nonneg δ t)
      have hh := mul_le_mul het hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    _ = _ := by rw [integral_mul_const, integral_Icc_exponentialTentDensity hδ, one_mul]

theorem abs_sourceFactorialCausal_linear_scale {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) :
    |sourceFactorialCausal N x| ≤ (factorialJumpScale N/Real.sqrt N)*x := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt (N : ℝ) := by positivity
  have hs : (Real.sqrt (N : ℝ))^2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hrN : Real.sqrt (N : ℝ) ≤ N := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ N by positivity) (show (0 : ℝ) ≤ (N : ℝ)-1 by linarith)]
  have hcoef : 20000*(N : ℝ)^4 ≤ factorialJumpScale N/Real.sqrt N := by
    apply (le_div_iff₀ hr).2
    calc
      _ ≤ (20000*(N : ℝ)^4)*(N : ℝ) := mul_le_mul_of_nonneg_left hrN (by positivity)
      _ = 20000*(N : ℝ)^5 := by ring
      _ ≤ _ := by unfold factorialJumpScale; nlinarith [show 0 ≤ (N : ℝ)^5 by positivity]
  exact (abs_sourceFactorialCausal_linear hN hx).trans (mul_le_mul_of_nonneg_right hcoef hx)

theorem abs_sourceFactorialCausal_archWeight_le {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    |sourceFactorialCausal N x*archLevySinhWeight x| ≤ (4+2*(1/x))/Real.sqrt N := by
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hexp : Real.exp (x/2)*Real.exp (-(1/2*x)) = 1 := by
    rw [← Real.exp_add, show x/2 + -(1/2*x) = 0 by ring, Real.exp_zero]
  rw [abs_mul, abs_of_pos (archLevySinhWeight_pos hx)]
  calc
    _ ≤ (2*Real.exp (x/2)/Real.sqrt N)*archLevySinhWeight x :=
      mul_le_mul_of_nonneg_right (abs_sourceFactorialCausal_le hN x) (archLevySinhWeight_pos hx).le
    _ = (2*Real.exp (x/2)/(Real.sqrt N*x))*(x*archLevySinhWeight x) := by field_simp; ring
    _ ≤ (2*Real.exp (x/2)/(Real.sqrt N*x))*((2*x+1)*Real.exp (-(1/2*x))) :=
      mul_le_mul_of_nonneg_left (mul_archLevySinhWeight_le hx) (by positivity)
    _ = (2*(2*x+1)/(Real.sqrt N*x))*(Real.exp (x/2)*Real.exp (-(1/2*x))) := by ring
    _ = _ := by rw [hexp]; field_simp; ring

def factorialSourceJumpError (n : ℕ) : ℝ :=
  (6*Real.log (4*((n+1 : ℕ) : ℝ)+1)+7+2*Real.log (factorialJumpScale (n+1)))/Real.sqrt (n+1 : ℕ)

theorem abs_integral_sourceFactorialCausal_archWeight_le (n : ℕ) :
    |∫ x in Ioi 0, sourceFactorialCausal (n+1) x*archLevySinhWeight x| ≤ factorialSourceJumpError n := by
  let Q := factorialJumpScale (n+1)
  let r := Real.sqrt (n+1 : ℕ)
  let L := Real.log (4*((n+1 : ℕ) : ℝ)+1)
  let a := 1/Q
  let b := L+1
  let J := fun x => |sourceFactorialCausal (n+1) x*archLevySinhWeight x|
  have hN : 1 ≤ n+1 := by omega
  have hQ1 : 1 ≤ Q := factorialJumpScale_one_le hN
  have hQ : 0 < Q := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (div_le_iff₀ hQ).2 (by simpa using hQ1)
  have hL : 0 ≤ L := Real.log_nonneg (by have hh := Nat.cast_nonneg (α := ℝ) (n+1); linarith)
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a ≤ b := by dsimp [b]; linarith
  have hi : IntegrableOn J (Ioi 0) := (integrableOn_sourceFactorialCausal_archWeight n).abs
  have hi0 : IntegrableOn J (Ioc 0 a) := hi.mono_set (fun _ hx => hx.1)
  have hia : IntegrableOn J (Ioi a) := hi.mono_set (fun _ hx => ha.trans hx)
  have hnear : (∫ x in Ioc 0 a, J x) ≤ 3/r := by
    calc
      _ ≤ ∫ _x in Ioc 0 a, (3*Q/r) := by
        apply setIntegral_mono_on hi0 (integrableOn_const (by simp)) measurableSet_Ioc
        intro x hx
        have hw : x*archLevySinhWeight x ≤ 3 := by
          calc
            _ ≤ (2*x+1)*Real.exp (-(1/2*x)) := mul_archLevySinhWeight_le hx.1
            _ ≤ (2*x+1)*1 := mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by linarith [hx.1])) (by linarith [hx.1])
            _ ≤ 3 := by linarith [hx.2.trans ha1]
        dsimp only [J]
        rw [abs_mul, abs_of_pos (archLevySinhWeight_pos hx.1)]
        calc
          _ ≤ ((Q/r)*x)*archLevySinhWeight x :=
            mul_le_mul_of_nonneg_right (abs_sourceFactorialCausal_linear_scale hN hx.1.le)
              (archLevySinhWeight_pos hx.1).le
          _ = (Q/r)*(x*archLevySinhWeight x) := by ring
          _ ≤ (Q/r)*3 := mul_le_mul_of_nonneg_left hw (by positivity)
          _ = _ := by ring
      _ = _ := by
        rw [← intervalIntegral.integral_of_le ha.le, intervalIntegral.integral_const]
        dsimp [a]
        simp only [sub_zero, smul_eq_mul]
        field_simp
  have htruncate : (∫ x in Ioi a, J x) = ∫ x in Ioc a b, J x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ hx => hx.1)
    intro x hx
    have hbx : b ≤ x := by
      by_contra! hh
      exact hx.2 ⟨hx.1,hh.le⟩
    have hLx : L ≤ x := by dsimp [b] at hbx; linarith
    dsimp only [J]
    rw [sourceFactorialCausal_tail hN hLx, zero_mul, abs_zero]
  have hci : ContinuousOn (fun x : ℝ => 1/x) (Icc a b) :=
    continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
  have hii := hci.intervalIntegrable_of_Icc hab
  have hiJ : IntervalIntegrable J volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (hi.mono_set (fun _ hx => ha.trans hx.1))
  have hfar : (∫ x in Ioi a, J x) ≤ (6*L+4+2*Real.log Q)/r := by
    rw [htruncate, ← intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ x in a..b, (4+2*(1/x))/r := by
        apply intervalIntegral.integral_mono_on hab hiJ
          (((continuous_const.intervalIntegrable a b).add (hii.const_mul 2)).div_const r)
        intro x hx
        exact abs_sourceFactorialCausal_archWeight_le hN (ha.trans_le hx.1)
      _ = (4*(b-a)+2*Real.log (b/a))/r := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_add (continuous_const.intervalIntegrable a b) (hii.const_mul 2),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          integral_one_div_of_pos ha hb]
        simp only [smul_eq_mul]
        ring
      _ ≤ _ := by
        rw [Real.log_div hb.ne' ha.ne']
        have hloga : Real.log a = -Real.log Q := by
          dsimp [a]
          rw [Real.log_div one_ne_zero hQ.ne', Real.log_one, zero_sub]
        rw [hloga]
        have hlogb : Real.log b ≤ L := by
          have hh := Real.log_le_sub_one_of_pos hb
          dsimp [b] at hh
          linarith
        apply div_le_div_of_nonneg_right _ hr.le
        dsimp [b]
        linarith
  have hsplit : (∫ x in Ioi 0, J x) = (∫ x in Ioc 0 a, J x)+(∫ x in Ioi a, J x) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi0 hia
  calc
    _ ≤ ∫ x in Ioi 0, J x := abs_integral_le_integral_abs
    _ ≤ 3/r+(6*L+4+2*Real.log Q)/r := by rw [hsplit]; exact add_le_add hnear hfar
    _ = factorialSourceJumpError n := by dsimp [factorialSourceJumpError,Q,r,L]; ring

theorem factorialSource_jump_energy_difference_bound (n : ℕ) :
    |biScaleLevyEnergy (factorialSourcePlus n)-biScaleLevyEnergy (factorialSourceMinus n)| ≤
      2*factorialSourceJumpError n := by
  rw [factorialSource_jump_energy_difference, abs_mul]
  rw [show |(-2 : ℝ)| = 2 by norm_num]
  exact mul_le_mul_of_nonneg_left (abs_integral_sourceFactorialCausal_archWeight_le n) (by norm_num)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
