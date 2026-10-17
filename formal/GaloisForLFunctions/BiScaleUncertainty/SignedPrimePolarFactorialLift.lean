import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHalfLineDomain
import GaloisForLFunctions.BiScaleUncertainty.ExplicitNyquistPolarAndChebyshevFactorialProducer

/-! Real-ratio rectangles lift the factorial sum to the actual critical
von Mangoldt measure and retain both branches of the polar density. -/

open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

/-- A compact measurable test, with the endpoint included for the atomic measure. -/
def polarRectangle (L x : ℝ) : ℝ := (Icc 0 L).indicator (fun t => Real.exp (t/2)) x

/-- Real division is essential: the continuum cutoff is never floored. -/
def factorialLift (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 K, polarRectangle (Real.log ((K : ℝ)/(j : ℝ))) x

private theorem polar_mul_rectangle (L x : ℝ) :
    polarDensity x * polarRectangle L x =
      (Icc 0 L).indicator (fun t => Real.exp t+1) x := by
  rw [polarRectangle, ← Set.indicator_mul_right]
  congr 1
  funext t
  unfold polarDensity
  rw [Real.cosh_eq]
  have hp : Real.exp (t/2) * Real.exp (t/2) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  have hm : Real.exp (-(t/2)) * Real.exp (t/2) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

theorem integrable_polar_rectangle (L : ℝ) :
    Integrable (fun x => polarDensity x * polarRectangle L x) := by
  simp_rw [polar_mul_rectangle]
  exact (Real.continuous_exp.add continuous_const).integrableOn_Icc.integrable_indicator
    measurableSet_Icc

theorem integral_polar_rectangle {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in Ici (0 : ℝ), polarDensity x * polarRectangle L x) = Real.exp L-1+L := by
  simp_rw [polar_mul_rectangle]
  rw [setIntegral_indicator measurableSet_Icc]
  have hs : Ici (0 : ℝ) ∩ Icc 0 L = Icc 0 L := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    tauto
  rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_add (Real.continuous_exp.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), integral_exp, intervalIntegral.integral_const]
  simp

theorem integrable_polar_factorialLift (K : ℕ) :
    Integrable (fun x => polarDensity x * factorialLift K x) := by
  unfold factorialLift
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ fun j _ => integrable_polar_rectangle _

private theorem ratio_log_nonneg {K j : ℕ} (hj : j ∈ Finset.Icc 1 K) :
    0 ≤ Real.log ((K : ℝ)/(j : ℝ)) := by
  obtain ⟨hj1,hjK⟩ := Finset.mem_Icc.mp hj
  apply Real.log_nonneg
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < j by omega))).mpr
  simpa using (show (j : ℝ) ≤ K by exact_mod_cast hjK)

theorem factorialLift_eq_zero_of_log_lt (K : ℕ) {x : ℝ} (hx : Real.log (K : ℝ) < x) :
    factorialLift K x = 0 := by
  unfold factorialLift
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hj1,hjK⟩ := Finset.mem_Icc.mp hj
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hratio : (K : ℝ)/(j : ℝ) ≤ K := by
    apply (div_le_iff₀ hjpos).mpr
    nlinarith
  have hlog := Real.log_le_log (div_pos hKpos hjpos) hratio
  unfold polarRectangle
  apply Set.indicator_of_notMem
  intro hm
  exact (not_lt_of_ge (mem_Icc.mp hm).2) (lt_of_le_of_lt hlog hx)

theorem factorialLift_at_log {K n : ℕ} (hn : 1 ≤ n) :
    factorialLift K (Real.log (n : ℝ)) = Real.sqrt n * ((K/n : ℕ) : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hterm : ∀ j ∈ Finset.Icc 1 K,
      polarRectangle (Real.log ((K : ℝ)/(j : ℝ))) (Real.log (n : ℝ)) =
        if j ≤ K/n then Real.sqrt n else 0 := by
    intro j hj
    obtain ⟨hj1,hjK⟩ := Finset.mem_Icc.mp hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hc : Real.log (n : ℝ) ∈ Icc 0 (Real.log ((K : ℝ)/(j : ℝ))) ↔ j ≤ K/n := by
      rw [mem_Icc, and_iff_right hlogn, Real.log_le_log_iff hnpos (div_pos hKpos hjpos),
        le_div_iff₀ hjpos, Nat.le_div_iff_mul_le (by omega : 0 < n)]
      constructor <;> intro h
      · exact_mod_cast (show (j : ℝ)*n ≤ K by nlinarith)
      · have h' : (j : ℝ)*n ≤ K := by exact_mod_cast h
        nlinarith
    simp only [polarRectangle, Set.indicator, hc, exp_half_log_eq_sqrt hnpos]
  unfold factorialLift
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hs : (Finset.Icc 1 K).filter (fun j => j ≤ K/n) = Finset.Icc 1 (K/n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hd : K/n ≤ K := Nat.div_le_self K n
    omega
  rw [hs]
  simp [Nat.card_Icc, mul_comm]

theorem primeTerm_factorialLift_tail (K n : ℕ) (hn : n ∉ Finset.Icc 1 K) :
    primeTerm (factorialLift K) n = 0 := by
  by_cases h2 : 2 ≤ n
  · have hKn : K < n := by simp only [Finset.mem_Icc] at hn; omega
    rw [primeTerm, if_pos h2, factorialLift_at_log (by omega), Nat.div_eq_of_lt hKn]
    simp
  · simp [primeTerm, h2]

theorem factorialLift_admissible (K : ℕ) :
    (Function.support (primeTerm (factorialLift K))).Finite ∧
      Summable (fun n => |primeTerm (factorialLift K) n|) ∧
      IntegrableOn (fun x => polarDensity x * factorialLift K x) (Ici 0) := by
  refine ⟨?_, ?_, (integrable_polar_factorialLift K).integrableOn⟩
  · apply (Finset.finite_toSet (Finset.Icc 1 K)).subset
    intro n hn
    by_contra hout
    exact hn (primeTerm_factorialLift_tail K n hout)
  · apply summable_of_ne_finset_zero (s := Finset.Icc 1 K)
    intro n hn
    rw [primeTerm_factorialLift_tail K n hn, abs_zero]

theorem tsum_primeTerm_factorialLift (K : ℕ) :
    (∑' n : ℕ, primeTerm (factorialLift K) n) = floorSummatory chebyshevPsi K := by
  rw [tsum_eq_sum (primeTerm_factorialLift_tail K),
    floorSummatory_chebyshevPsi_eq_sum_vonMangoldt_mul_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  by_cases h2 : 2 ≤ n
  · rw [primeTerm, if_pos h2, factorialLift_at_log hn1, primeWeight]
    have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast (show 0 < n by omega)))
    field_simp
  · have h1 : n = 1 := by omega
    simp [primeTerm, h1]

theorem integral_polar_factorialLift (K : ℕ) :
    (∫ x in Ici (0 : ℝ), polarDensity x * factorialLift K x) =
      ∑ j ∈ Finset.Icc 1 K,
        ((K : ℝ)/(j : ℝ)-1+Real.log ((K : ℝ)/(j : ℝ))) := by
  unfold factorialLift
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => (integrable_polar_rectangle _).integrableOn)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_polar_rectangle (ratio_log_nonneg hj)]
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjK := (Finset.mem_Icc.mp hj).2
  rw [Real.exp_log (div_pos (by exact_mod_cast (show 0 < K by omega))
    (by exact_mod_cast (show 0 < j by omega)))]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
