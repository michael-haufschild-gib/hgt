import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryCosts
import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# The positive base moment model and exact geometric moment changes

The squared normalized wedge costs are the moments of the product of two
uniform interval variables divided by four. The exact double-integral identity
proves strict positivity on every nonzero polynomial square. The protected
geometric prefix transfers this positivity, and a finite coefficient identity
isolates the first altered moment.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set MeasureTheory
open _root_.HTGeometry

def recoveryWedgeMoment (k : ℕ) : ℝ := 1 / ((4 : ℝ)^k*(k+1 : ℝ)^(2 : ℕ))

def recoverySurgeryMoment (n k : ℕ) : ℝ := (recoverySurgeryGap n k / recoverySurgeryGap n 0)^(2 : ℕ)

theorem recoveryWedgeMoment_positive (k : ℕ) : 0 < recoveryWedgeMoment k := by
  unfold recoveryWedgeMoment
  positivity

theorem recoveryWedgeMoment_normalized (k : ℕ) :
    (recoveryWedgeGap k / recoveryWedgeGap 0)^(2 : ℕ) = recoveryWedgeMoment k := by
  have hk : (k+1 : ℝ) ≠ 0 := by positivity
  have ht : (2 : ℝ)^k ≠ 0 := by positivity
  have hp : (4 : ℝ)^k = ((2 : ℝ)^k)^(2 : ℕ) := by rw [← pow_mul, mul_comm k 2, pow_mul]; congr 1; ring
  unfold recoveryWedgeGap recoveryWedgeMoment
  simp only [Nat.cast_zero, zero_add, pow_succ, hp]
  field_simp

theorem recoverySurgeryMoment_prefix (n : ℕ) (k : Fin (n+1)) :
    recoverySurgeryMoment n k.val = recoveryWedgeMoment k.val := by
  rw [recoverySurgeryMoment, recoverySurgeryGap_prefix n k,
    recoverySurgeryGap_prefix n ⟨0,by omega⟩, recoveryWedgeMoment_normalized]

theorem recoverySurgeryMoment_drop_upper (n : ℕ) :
    recoverySurgeryMoment n (n+1) ≤ (recoverySurgeryHeight n)^(2 : ℕ)*recoveryWedgeMoment (n+1) := by
  have hb := (div_le_div_iff_of_pos_right (recoverySurgeryGap_positive n 0)).mpr
    (recoverySurgeryGap_drop_upper n)
  rw [recoverySurgeryGap_prefix n ⟨0,by omega⟩] at hb
  have hpos : 0 ≤ recoverySurgeryGap n (n+1) / recoveryWedgeGap 0 := by
    exact le_of_lt (div_pos (recoverySurgeryGap_positive n (n+1)) (recoveryWedgeGap_positive 0))
  have h := sq_le_sq₀ hpos (le_trans hpos hb) |>.mpr hb
  rw [mul_div_assoc, mul_pow, recoveryWedgeMoment_normalized] at h
  simpa only [recoverySurgeryMoment, recoverySurgeryGap_prefix n ⟨0,by omega⟩] using h

theorem recoveryPolynomial_inner_integral (P : ℝ[X]) (s : ℝ) :
    (∫ t in (0 : ℝ)..1, P.eval (s*t/4)) =
      ∑ k ∈ P.support, P.coeff k * (s/4)^k / (k+1 : ℝ) := by
  simp_rw [eval_eq_sum, Polynomial.sum_def]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    simp_rw [show ∀ t : ℝ, s*t/4=(s/4)*t by intro t; ring, mul_pow, ← mul_assoc]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
    ring
  · intro k hk
    exact (show Continuous (fun t : ℝ => P.coeff k*(s*t/4)^k) by fun_prop).intervalIntegrable _ _

theorem recoveryPolynomial_inner_continuous (P : ℝ[X]) :
    Continuous (fun s : ℝ => ∫ t in (0 : ℝ)..1, P.eval (s*t/4)) := by
  simp_rw [recoveryPolynomial_inner_integral]
  fun_prop

theorem recoveryWedgeMoment_integral (P : ℝ[X]) :
    momentFunctional recoveryWedgeMoment P =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, P.eval (s*t/4) := by
  simp_rw [recoveryPolynomial_inner_integral]
  rw [intervalIntegral.integral_finsetSum]
  · rw [momentFunctional_eq_support_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hf : (fun s : ℝ => P.coeff k*(s/4)^k/(k+1 : ℝ)) =
        (fun s : ℝ => (P.coeff k/((4 : ℝ)^k*(k+1 : ℝ)))*s^k) := by
      funext s
      rw [div_pow]
      field_simp
    rw [hf, intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
    unfold recoveryWedgeMoment
    field_simp
  · intro k hk
    exact (show Continuous (fun s : ℝ => P.coeff k*(s/4)^k/(k+1 : ℝ)) by fun_prop).intervalIntegrable _ _

theorem recoveryWedgeMoment_eval_nonneg (P : ℝ[X])
    (hP : ∀ x ∈ Icc (0 : ℝ) (1/4), 0 ≤ P.eval x) :
    0 ≤ momentFunctional recoveryWedgeMoment P := by
  rw [recoveryWedgeMoment_integral]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro s hs
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  apply hP
  have hp : s*t ≤ 1 := (mul_le_mul hs.2 ht.2 ht.1 zero_le_one).trans_eq (one_mul 1)
  constructor
  · exact div_nonneg (mul_nonneg hs.1 ht.1) (by linarith)
  · linarith

theorem recoveryWedgeMoment_eval_le (P : ℝ[X]) (b : ℝ)
    (hP : ∀ x ∈ Icc (0 : ℝ) (1/4), P.eval x ≤ b) :
    momentFunctional recoveryWedgeMoment P ≤ b := by
  rw [recoveryWedgeMoment_integral]
  have hinner : ∀ s ∈ Icc (0 : ℝ) 1, (∫ t in (0 : ℝ)..1, P.eval (s*t/4)) ≤ b := by
    intro s hs
    have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      ((P.continuous.comp (show Continuous (fun t : ℝ => s*t/4) by fun_prop)).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1) (g := fun _ : ℝ => b) (by
        intro t ht
        apply hP
        have hp : s*t ≤ 1 := (mul_le_mul hs.2 ht.2 ht.1 zero_le_one).trans_eq (one_mul 1)
        constructor
        · exact div_nonneg (mul_nonneg hs.1 ht.1) (by linarith)
        · linarith)
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul, Function.comp_apply] using h
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((recoveryPolynomial_inner_continuous P).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1) hinner
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using h

theorem recoveryWedgeMoment_square_positive (P : ℝ[X]) (hP : P ≠ 0) :
    0 < momentFunctional recoveryWedgeMoment (P^(2 : ℕ)) := by
  have hex : ∃ x ∈ Icc (0 : ℝ) (1/4), P.eval x ≠ 0 := by
    by_contra! he
    apply hP
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Set.Icc_infinite (show (0 : ℝ)<1/4 by linarith)).mono (fun x hx => he x hx)
  obtain ⟨x,hx,he⟩ := hex
  rw [recoveryWedgeMoment_integral]
  apply intervalIntegral.integral_pos zero_lt_one
    (recoveryPolynomial_inner_continuous (P^(2 : ℕ))).continuousOn
  · intro s hs
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t ht
    rw [eval_pow]
    exact sq_nonneg _
  · refine ⟨1,⟨zero_le_one,le_refl _⟩,?_⟩
    apply intervalIntegral.integral_pos zero_lt_one
      ((P^(2 : ℕ)).continuous.comp (show Continuous (fun t : ℝ => 1*t/4) by fun_prop)).continuousOn
    · intro t ht
      simp only [Function.comp_apply, eval_pow]
      exact sq_nonneg _
    · refine ⟨4*x,⟨by linarith [hx.1],by linarith [hx.2]⟩,?_⟩
      simp only [Function.comp_apply]
      rw [show (1 : ℝ)*(4*x)/4=x by ring, eval_pow]
      exact sq_pos_of_ne_zero he

theorem recoveryMomentFunctional_range (a : ℕ → ℝ) (P : ℝ[X]) (k : ℕ)
    (hP : P.natDegree ≤ k) :
    momentFunctional a P = ∑ i ∈ Finset.range (k+1), P.coeff i*a i := by
  apply Polynomial.sum_eq_of_subset _ (fun i => zero_mul _)
  intro i hi
  apply Finset.mem_range.mpr
  have h := le_natDegree_of_ne_zero (mem_support_iff.mp hi)
  omega

theorem recoverySurgeryMomentFunctional_prefix (n : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ n) :
    momentFunctional (recoverySurgeryMoment n) P = momentFunctional recoveryWedgeMoment P := by
  rw [recoveryMomentFunctional_range _ P n hP, recoveryMomentFunctional_range _ P n hP]
  apply Finset.sum_congr rfl
  intro i hi
  rw [recoverySurgeryMoment_prefix n ⟨i,Finset.mem_range.mp hi⟩]

theorem recoverySurgeryMomentFunctional_top_change (n : ℕ) (P : ℝ[X])
    (hP : P.natDegree ≤ n+1) :
    momentFunctional (recoverySurgeryMoment n) P = momentFunctional recoveryWedgeMoment P +
      P.coeff (n+1)*(recoverySurgeryMoment n (n+1)-recoveryWedgeMoment (n+1)) := by
  rw [recoveryMomentFunctional_range _ P (n+1) hP,
    recoveryMomentFunctional_range _ P (n+1) hP,
    Finset.sum_range_succ (fun i => P.coeff i*recoverySurgeryMoment n i) (n+1),
    Finset.sum_range_succ (fun i => P.coeff i*recoveryWedgeMoment i) (n+1)]
  have he : (∑ i ∈ Finset.range (n+1), P.coeff i*recoverySurgeryMoment n i) =
      ∑ i ∈ Finset.range (n+1), P.coeff i*recoveryWedgeMoment i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [recoverySurgeryMoment_prefix n ⟨i,Finset.mem_range.mp hi⟩]
  rw [he]
  ring

theorem recoverySurgeryMoment_square_prefix_positive (n : ℕ) (P : ℝ[X])
    (hP : P ≠ 0) (hd : 2*P.natDegree ≤ n) :
    0 < momentFunctional (recoverySurgeryMoment n) (P^(2 : ℕ)) := by
  rw [recoverySurgeryMomentFunctional_prefix n (P^(2 : ℕ)) (by rw [natDegree_pow]; omega)]
  exact recoveryWedgeMoment_square_positive P hP

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
