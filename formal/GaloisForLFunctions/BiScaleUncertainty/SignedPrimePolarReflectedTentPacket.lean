import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialAtomicPacket
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarTentRegularity

/-! The reflected narrow factorial factor has no prime translates in the local
window. Its remaining polar packet has a shrinking squared-norm budget. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

def factorialReflectedTent (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => exponentialTentSource (sourceFactorialWidth (n+1)) (-u),
    (continuous_exponentialTentSource _).comp continuous_neg⟩,
    (hasCompactSupport_exponentialTentSource _).comp_homeomorph (Homeomorph.neg ℝ)⟩

theorem factorialReflectedTent_nonneg (n : ℕ) (u : ℝ) : 0 ≤ factorialReflectedTent n u :=
  mul_nonneg (Real.exp_pos _).le (exponentialTentDensity_nonneg _ _)

theorem factorialReflectedTent_zero_right (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    factorialReflectedTent n u = 0 := by
  change exponentialTentSource (sourceFactorialWidth (n+1)) (-u) = 0
  simp only [exponentialTentSource, exponentialTentDensity,
    causalTent_zero_left _ (show -u ≤ 0 by linarith), mul_zero, zero_div]

theorem factorialReflectedTent_zero_left (n : ℕ) {u : ℝ}
    (hu : u ≤ -2*sourceFactorialWidth (n+1)) : factorialReflectedTent n u = 0 := by
  change exponentialTentSource (sourceFactorialWidth (n+1)) (-u) = 0
  simp only [exponentialTentSource, exponentialTentDensity,
    causalTent_zero_right _ (show 2*sourceFactorialWidth (n+1) ≤ -u by linarith), mul_zero, zero_div]

theorem integral_factorialReflectedTent_le (n : ℕ) : (∫ u, factorialReflectedTent n u) ≤ 2 := by
  have he : (∫ u, factorialReflectedTent n u) = ∫ u, |factorialReflectedTent n u| := by
    congr 1 with u
    exact (abs_of_nonneg (factorialReflectedTent_nonneg n u)).symm
  rw [he]
  change (∫ u, |exponentialTentSource (sourceFactorialWidth (n+1)) (-u)|) ≤ 2
  rw [integral_neg_eq_self (fun u => |exponentialTentSource (sourceFactorialWidth (n+1)) u|)]
  exact integral_abs_exponentialTentSource_factorial_le (by omega)

theorem atomicSource_factorialReflectedTent_zero (n K : ℕ) {u : ℝ}
    (hu : -3*sourceFactorialWidth (n+1) ≤ u) :
    atomicSource (factorialReflectedTent n) K u = 0 := by
  change (∑ m ∈ Finset.Icc 1 (K+2), primeWeight m*factorialReflectedTent n (u+Real.log m)) = 0
  apply Finset.sum_eq_zero
  intro m hm
  by_cases hm1 : m = 1
  · simp [hm1, primeWeight]
  have hm2 : 2 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
  have hR2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have he := (factorial_packet_collar_bounds (by omega : 1 ≤ n+1) hu).1
  have hlog : -u < Real.log (m : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos (-u)) (show Real.exp (-u) < (m : ℝ) by linarith)
    rwa [Real.log_exp] at h
  rw [factorialReflectedTent_zero_right n (by linarith), mul_zero]

private theorem polarDensity_factorial_collar_le {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Icc 0 (3*sourceFactorialWidth N)) : polarDensity t ≤ 3 := by
  have hd := sourceFactorialWidth_pos hN
  have hp : Real.exp (t/2) ≤ 2 :=
    (Real.exp_le_exp.mpr (by linarith [ht.2])).trans (exp_four_sourceFactorialWidth_le_two hN)
  have hm : Real.exp (-(t/2)) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show -(t/2) ≤ 0 by linarith [ht.1])
    simpa only [Real.exp_zero] using h
  unfold polarDensity
  rw [Real.cosh_eq]
  linarith

theorem abs_signedSource_factorialReflectedTent_le (n K : ℕ) {u : ℝ}
    (hu : -3*sourceFactorialWidth (n+1) ≤ u) :
    |signedSource (factorialReflectedTent n) K u| ≤ 6 := by
  have hshift : Continuous (fun t => factorialReflectedTent n (u+t)) := by fun_prop
  have hi : Integrable (fun t => factorialReflectedTent n (u+t)) := by
    have hc : HasCompactSupport (fun t => factorialReflectedTent n (u+t)) := by
      simpa only [add_comm u] using
        hasCompactSupport_comp_add (factorialReflectedTent n).hasCompactSupport u
    exact hshift.integrable_of_hasCompactSupport hc
  have htint : (∫ t, factorialReflectedTent n (u+t)) ≤ 2 := by
    rw [integral_add_left_eq_self]
    exact integral_factorialReflectedTent_le n
  have hnonneg : 0 ≤ polarSource (factorialReflectedTent n) K u := by
    apply setIntegral_nonneg measurableSet_Icc
    intro t _
    exact mul_nonneg (polarDensity_nonneg t) (factorialReflectedTent_nonneg n _)
  have hpolar : polarSource (factorialReflectedTent n) K u ≤ 6 := by
    change (∫ t in Icc 0 (cutoff K), polarDensity t*factorialReflectedTent n (u+t)) ≤ 6
    calc
      _ ≤ ∫ t in Icc 0 (cutoff K), 3*factorialReflectedTent n (u+t) := by
        apply setIntegral_mono_on ((continuous_polarDensity.mul hshift).integrableOn_Icc)
          ((continuous_const.mul hshift).integrableOn_Icc) measurableSet_Icc
        intro t ht
        by_cases hz : factorialReflectedTent n (u+t) = 0
        · simp [hz]
        have htt : t ≤ 3*sourceFactorialWidth (n+1) := by
          by_contra! h
          exact hz (factorialReflectedTent_zero_right n (by linarith))
        exact mul_le_mul_of_nonneg_right
          (polarDensity_factorial_collar_le (by omega : 1 ≤ n+1) ⟨ht.1, htt⟩)
          (factorialReflectedTent_nonneg n _)
      _ = 3*(∫ t in Icc 0 (cutoff K), factorialReflectedTent n (u+t)) := integral_const_mul _ _
      _ ≤ 3*(∫ t, factorialReflectedTent n (u+t)) := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hi (Filter.Eventually.of_forall fun t => factorialReflectedTent_nonneg n _))
        (by norm_num)
      _ ≤ 6 := by linarith
  change |atomicSource (factorialReflectedTent n) K u-polarSource (factorialReflectedTent n) K u| ≤ 6
  rw [atomicSource_factorialReflectedTent_zero n K hu, zero_sub, abs_neg, abs_of_nonneg hnonneg]
  exact hpolar

theorem signedSource_factorialReflectedTent_zero_right (n K : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    signedSource (factorialReflectedTent n) K u = 0 := by
  have hd := sourceFactorialWidth_pos (by omega : 1 ≤ n+1)
  change atomicSource (factorialReflectedTent n) K u-polarSource (factorialReflectedTent n) K u = 0
  rw [atomicSource_factorialReflectedTent_zero n K (by linarith)]
  have hp : polarSource (factorialReflectedTent n) K u = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    rw [factorialReflectedTent_zero_right n (by linarith [ht.1]), mul_zero]
  rw [hp, sub_self]

/-- The actual narrow packet has a budget of order `1/N`, at every cutoff. -/
theorem integral_signedSource_factorialReflectedTent_sq_le (n K : ℕ) :
    (∫ u in Icc (-3*sourceFactorialWidth (n+1)) (Real.log (4*((n+1 : ℕ) : ℝ)+1)),
      signedSource (factorialReflectedTent n) K u ^ 2) ≤ 9/((n+1 : ℕ) : ℝ) := by
  let a := -3*sourceFactorialWidth (n+1)
  let L := Real.log (4*((n+1 : ℕ) : ℝ)+1)
  have hd := sourceFactorialWidth_pos (by omega : 1 ≤ n+1)
  have ha : a ≤ 0 := by dsimp [a]; linarith
  have hL : 0 ≤ L := Real.log_nonneg (by
    have hn : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _
    linarith)
  have hc : Continuous (fun u => signedSource (factorialReflectedTent n) K u^2) :=
    (signedSource (factorialReflectedTent n) K).continuous.pow 2
  have hz : (∫ u in (0 : ℝ)..L, signedSource (factorialReflectedTent n) K u ^ 2) = 0 := by
    calc
      _ = ∫ _u in (0 : ℝ)..L, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hL] at hu
        change signedSource (factorialReflectedTent n) K u^2 = 0
        rw [signedSource_factorialReflectedTent_zero_right n K hu.1, zero_pow (by omega)]
      _ = 0 := by simp
  change (∫ u in Icc a L, signedSource (factorialReflectedTent n) K u^2) ≤ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (ha.trans hL),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a 0) (hc.intervalIntegrable 0 L),
    hz, add_zero]
  calc
    _ ≤ ∫ _u in a..(0 : ℝ), (36 : ℝ) := by
      apply intervalIntegral.integral_mono_on ha (hc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      intro u hu
      have h := abs_le.mp (abs_signedSource_factorialReflectedTent_le n K hu.1)
      nlinarith
    _ = 108*sourceFactorialWidth (n+1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      dsimp [a]
      ring
    _ ≤ 9/((n+1 : ℕ) : ℝ) := by
      have h := (sourceFactorialWidth_bounds (by omega : 1 ≤ n+1)).2
      calc
        _ ≤ 108*(1/(12*((n+1 : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h (by norm_num)
        _ = _ := by ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
