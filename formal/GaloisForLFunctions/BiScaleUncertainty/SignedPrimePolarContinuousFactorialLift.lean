import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialProducer
import GaloisForLFunctions.BiScaleUncertainty.ClampedExponentialRamp

/-! Continuous real-ratio factorial lifts preserve the arithmetic grid and have an exact polar correction. -/

open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

def smoothFactorialLift (ε : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  Real.exp (x/2) * ∑ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)*Real.exp x/(K : ℝ))

theorem continuous_smoothFactorialLift (ε : ℝ) (K : ℕ) :
    Continuous (smoothFactorialLift ε K) := by
  unfold smoothFactorialLift
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
    (continuous_finsetSum _ fun j _ => (continuous_clampedRamp ε).comp
      ((continuous_const.mul Real.continuous_exp).div_const K))

theorem smoothFactorialLift_of_nonpos {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ 0) (K : ℕ) :
    smoothFactorialLift ε K x = Real.exp (x/2)*(K : ℝ) := by
  by_cases hK : K = 0
  · simp [smoothFactorialLift, hK]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hexp : Real.exp x ≤ 1 := by simpa using Real.exp_le_exp.mpr hx
  have ht : ∀ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)*Real.exp x/(K : ℝ)) = 1 := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjK : (j : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    apply clampedRamp_eq_one hε
    apply (div_le_iff₀ hK0).2
    nlinarith
  unfold smoothFactorialLift
  rw [Finset.sum_congr rfl ht]
  simp [Nat.card_Icc]

theorem smoothFactorialLift_eq_zero {ε x : ℝ} {K : ℕ} (hε : 0 < ε)
    (hK : 1 ≤ K) (hx : (K : ℝ)*(1+ε) ≤ Real.exp x) :
    smoothFactorialLift ε K x = 0 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have ht : ∀ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)*Real.exp x/(K : ℝ)) = 0 := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    apply clampedRamp_eq_zero hε
    apply (le_div_iff₀ hK0).2
    nlinarith [Real.exp_pos x]
  unfold smoothFactorialLift
  rw [Finset.sum_congr rfl ht]
  simp

theorem smoothFactorialLift_eq_exp_half {ε x : ℝ} {K : ℕ} (hε : 0 < ε)
    (hK : 1 ≤ K) (hlo : (K : ℝ)*(1+ε) ≤ 2*Real.exp x)
    (hhi : Real.exp x ≤ K) : smoothFactorialLift ε K x = Real.exp (x/2) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : (∑ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)*Real.exp x/(K : ℝ))) = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp only [Nat.cast_one, one_mul]
      exact clampedRamp_eq_one hε ((div_le_iff₀ hK0).2 (by simpa using hhi))
    · intro j hj hj1
      have hj2 : (2 : ℝ) ≤ j := by
        exact_mod_cast (show 2 ≤ j by have := (Finset.mem_Icc.mp hj).1; omega)
      apply clampedRamp_eq_zero hε
      apply (le_div_iff₀ hK0).2
      nlinarith [Real.exp_pos x]
    · simp [Finset.mem_Icc, hK]
  simp [smoothFactorialLift, hs]

/-- The right collar cannot cross any additional integer product. -/
theorem smoothFactorialLift_at_log {ε : ℝ} {K n : ℕ} (hε : 0 < ε)
    (hεK : ε*(K : ℝ) ≤ 1) (hn : 1 ≤ n) :
    smoothFactorialLift ε K (Real.log n) = factorialLift K (Real.log n) := by
  by_cases hK : K = 0
  · simp [smoothFactorialLift, factorialLift, hK]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold smoothFactorialLift factorialLift
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hmem : Real.log (n : ℝ) ∈ Icc 0 (Real.log ((K : ℝ)/(j : ℝ))) ↔ n*j ≤ K := by
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    simp only [mem_Icc, hlogn, true_and]
    rw [Real.log_le_log_iff hn0 (div_pos hK0 hj0), le_div_iff₀ hj0]
    exact_mod_cast (Iff.rfl : n*j ≤ K ↔ n*j ≤ K)
  rw [Real.exp_log hn0]
  by_cases hc : n*j ≤ K
  · have hp : (j : ℝ)*(n : ℝ) ≤ K := by exact_mod_cast (show j*n ≤ K by simpa [Nat.mul_comm] using hc)
    rw [clampedRamp_eq_one hε ((div_le_iff₀ hK0).2 (by simpa using hp)), mul_one]
    exact (Set.indicator_of_mem (hmem.mpr hc) (fun t : ℝ => Real.exp (t/2))).symm
  · have hpNat : K+1 ≤ n*j := by omega
    have hpNat2 : K+1 ≤ j*n := by simpa only [Nat.mul_comm] using hpNat
    have hp : (K : ℝ)+1 ≤ (j : ℝ)*(n : ℝ) := by exact_mod_cast hpNat2
    rw [clampedRamp_eq_zero hε ((le_div_iff₀ hK0).2 (by nlinarith)), mul_zero]
    exact (Set.indicator_of_notMem (fun h => hc (hmem.mp h)) (fun t : ℝ => Real.exp (t/2))).symm

theorem polarDensity_mul_exp_half (x : ℝ) :
    polarDensity x * Real.exp (x/2) = Real.exp x+1 := by
  unfold polarDensity
  rw [Real.cosh_eq]
  have hp : Real.exp (x/2)*Real.exp (x/2) = Real.exp x := by
    rw [← Real.exp_add]; congr 1; ring
  have hm : Real.exp (-(x/2))*Real.exp (x/2) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

private theorem polar_smoothFactorialLift (ε : ℝ) (K : ℕ) (x : ℝ) :
    polarDensity x * smoothFactorialLift ε K x =
      ∑ j ∈ Finset.Icc 1 K, (Real.exp x+1)*clampedRamp ε (Real.exp x/((K : ℝ)/(j : ℝ))) := by
  unfold smoothFactorialLift
  rw [← mul_assoc, polarDensity_mul_exp_half, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  have hj0 : (j : ℝ) ≠ 0 := by
    exact_mod_cast (show j ≠ 0 by have := (Finset.mem_Icc.mp hj).1; omega)
  field_simp

theorem integrableOn_polar_smoothFactorialLift {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    IntegrableOn (fun x => polarDensity x*smoothFactorialLift ε K x) (Ici 0) := by
  simp_rw [polar_smoothFactorialLift]
  apply integrable_finsetSum
  intro j hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  apply integrableOn_ramp_polar hε
  apply (le_div_iff₀ hj0).2
  simpa only [one_mul] using (show (j : ℝ) ≤ K by exact_mod_cast (Finset.mem_Icc.mp hj).2)

/-- Smoothing changes the polar integral by an explicit harmonic term and a linear term. -/
theorem integral_polar_smoothFactorialLift {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    (∫ x in Ici (0 : ℝ), polarDensity x*smoothFactorialLift ε K x) =
      (∫ x in Ici (0 : ℝ), polarDensity x*factorialLift K x) +
        ε/2*(K : ℝ)*realHarmonic K+(K : ℝ)*rampLogCorrection ε := by
  have hjpos (j : ℕ) (hj : j ∈ Finset.Icc 1 K) : (0 : ℝ) < j := by
    exact_mod_cast (Finset.mem_Icc.mp hj).1
  have ha (j : ℕ) (hj : j ∈ Finset.Icc 1 K) : 1 ≤ (K : ℝ)/(j : ℝ) := by
    apply (le_div_iff₀ (hjpos j hj)).2
    simpa only [one_mul] using (show (j : ℝ) ≤ K by exact_mod_cast (Finset.mem_Icc.mp hj).2)
  simp_rw [polar_smoothFactorialLift]
  rw [integral_finsetSum _ (fun j hj => integrableOn_ramp_polar hε (ha j hj)),
    integral_polar_factorialLift]
  have hs : ∀ j ∈ Finset.Icc 1 K,
      (∫ x in Ici (0 : ℝ), (Real.exp x+1)*clampedRamp ε (Real.exp x/((K : ℝ)/(j : ℝ)))) =
      ((K : ℝ)/(j : ℝ)-1+Real.log ((K : ℝ)/(j : ℝ)))+
        (ε/2*(K : ℝ))*(1/(j : ℝ))+rampLogCorrection ε := by
    intro j hj
    rw [integral_ramp_polar hε (ha j hj)]
    ring
  rw [Finset.sum_congr rfl hs]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, realHarmonic]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
