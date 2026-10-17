import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRampCore
import GaloisForLFunctions.BiScaleUncertainty.ClampedExponentialBranchMoments

open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

private theorem exp_half_mul_lift (ε : ℝ) (K : ℕ) (x : ℝ) :
    Real.exp (x/2)*smoothFactorialLift ε K x =
      ∑ j ∈ Finset.Icc 1 K, Real.exp x*clampedRamp ε (Real.exp x/((K : ℝ)/(j : ℝ))) := by
  have he : Real.exp (x/2)*Real.exp (x/2) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold smoothFactorialLift
  rw [← mul_assoc, he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by have := (Finset.mem_Icc.mp hj).1; omega)
  field_simp

private theorem exp_neg_half_mul_lift (ε : ℝ) (K : ℕ) (x : ℝ) :
    Real.exp (-(x/2))*smoothFactorialLift ε K x =
      ∑ j ∈ Finset.Icc 1 K, clampedRamp ε (Real.exp x/((K : ℝ)/(j : ℝ))) := by
  have he : Real.exp (-(x/2))*Real.exp (x/2) = 1 := by rw [← Real.exp_add]; simp
  unfold smoothFactorialLift
  rw [← mul_assoc, he, one_mul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by have := (Finset.mem_Icc.mp hj).1; omega)
  field_simp

private theorem ratio_ge_one {K j : ℕ} (hj : j ∈ Finset.Icc 1 K) : 1 ≤ (K : ℝ)/(j : ℝ) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  apply (le_div_iff₀ hj0).2
  simpa only [one_mul] using (show (j : ℝ) ≤ K by exact_mod_cast (Finset.mem_Icc.mp hj).2)

theorem integrableOn_exp_half_lift {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    IntegrableOn (fun x => Real.exp (x/2)*smoothFactorialLift ε K x) (Ici 0) := by
  simp_rw [exp_half_mul_lift]
  exact integrable_finsetSum _ (fun j hj => integrableOn_ramp_exp hε (ratio_ge_one hj))

theorem integrableOn_exp_neg_half_lift {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    IntegrableOn (fun x => Real.exp (-(x/2))*smoothFactorialLift ε K x) (Ici 0) := by
  simp_rw [exp_neg_half_mul_lift]
  exact integrable_finsetSum _ (fun j hj => integrableOn_ramp_plain hε (ratio_ge_one hj))

theorem integral_exp_half_lift {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    (∫ x in Ici (0 : ℝ), Real.exp (x/2)*smoothFactorialLift ε K x) =
      (1+ε/2)*(K : ℝ)*realHarmonic K-K := by
  simp_rw [exp_half_mul_lift]
  rw [integral_finsetSum _ (fun j hj => integrableOn_ramp_exp hε (ratio_ge_one hj))]
  have hs : ∀ j ∈ Finset.Icc 1 K,
      (∫ x in Ici (0 : ℝ), Real.exp x*clampedRamp ε (Real.exp x/((K : ℝ)/(j : ℝ)))) =
        ((1+ε/2)*(K : ℝ))*(1/(j : ℝ))-1 := by
    intro j hj
    rw [integral_ramp_exp hε (ratio_ge_one hj)]
    ring
  rw [Finset.sum_congr rfl hs]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, realHarmonic, mul_one]

theorem integral_exp_neg_half_lift {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    (∫ x in Ici (0 : ℝ), Real.exp (-(x/2))*smoothFactorialLift ε K x) =
      (K : ℝ)*Real.log K-floorSummatory chebyshevPsi K+(K : ℝ)*rampLogCorrection ε := by
  by_cases hK : K = 0
  · simp [hK, smoothFactorialLift, floorSummatory]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  simp_rw [exp_neg_half_mul_lift]
  rw [integral_finsetSum _ (fun j hj => integrableOn_ramp_plain hε (ratio_ge_one hj)),
    floorSummatory_chebyshevPsi]
  have hs : ∀ j ∈ Finset.Icc 1 K,
      (∫ x in Ici (0 : ℝ), clampedRamp ε (Real.exp x/((K : ℝ)/(j : ℝ)))) =
        Real.log (K : ℝ)-Real.log j+rampLogCorrection ε := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    rw [integral_ramp_plain hε (ratio_ge_one hj), Real.log_div hK0.ne' hj0.ne']
  rw [Finset.sum_congr rfl hs]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

theorem integral_weight_rampBiNull_eq_halfLine {ε : ℝ} (hε : 0 < ε) (N : ℕ) (w : ℝ → ℝ) :
    (∫ x : ℝ, w x*rampBiNull ε N x) = ∫ x in Ici 0, w x*rampBiNull ε N x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hneg : x ≤ 0 := by
    by_contra! hh
    exact hx hh.le
  rw [rampBiNull_zero_of_nonpos hε N hneg, mul_zero]

private theorem integral_weight_rampBiNull (ε : ℝ) (N : ℕ) (w : ℝ → ℝ)
    (hi : ∀ K, IntegrableOn (fun x => w x*smoothFactorialLift ε K x) (Ici 0)) :
    (∫ x in Ici (0 : ℝ), w x*rampBiNull ε N x) =
      ((∫ x in Ici (0 : ℝ), w x*smoothFactorialLift ε (4*N) x)-
        4*(∫ x in Ici (0 : ℝ), w x*smoothFactorialLift ε (2*N) x)+
        4*(∫ x in Ici (0 : ℝ), w x*smoothFactorialLift ε N x))/Real.sqrt N := by
  have hi2 : IntegrableOn (fun x => 4*(w x*smoothFactorialLift ε (2*N) x)) (Ici 0) :=
    (hi (2*N)).const_mul 4
  have hi1 : IntegrableOn (fun x => 4*(w x*smoothFactorialLift ε N x)) (Ici 0) := (hi N).const_mul 4
  have his : IntegrableOn (fun x => w x*smoothFactorialLift ε (4*N) x-
      4*(w x*smoothFactorialLift ε (2*N) x)) (Ici 0) := (hi (4*N)).sub hi2
  have he : (fun x => w x*rampBiNull ε N x) = fun x =>
      (w x*smoothFactorialLift ε (4*N) x-4*(w x*smoothFactorialLift ε (2*N) x)+
        4*(w x*smoothFactorialLift ε N x))/Real.sqrt N := by funext x; unfold rampBiNull; ring
  rw [he, integral_div, integral_add his hi1, integral_sub (hi (4*N)) hi2,
    integral_const_mul, integral_const_mul]

theorem integral_exp_half_rampBiNull {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    (∫ x : ℝ, Real.exp (x/2)*rampBiNull ε N x) =
      ((1+ε/2)*harmonicCorrection N)/Real.sqrt N := by
  rw [integral_weight_rampBiNull_eq_halfLine hε,
    integral_weight_rampBiNull ε N _ (integrableOn_exp_half_lift hε)]
  simp_rw [integral_exp_half_lift hε]
  unfold harmonicCorrection
  push_cast
  ring

theorem integral_exp_neg_half_rampBiNull {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N) :
    (∫ x : ℝ, Real.exp (-(x/2))*rampBiNull ε N x) =
      -chebyshevBiNullProducer N/Real.sqrt N := by
  rw [integral_weight_rampBiNull_eq_halfLine hε,
    integral_weight_rampBiNull ε N _ (integrableOn_exp_neg_half_lift hε)]
  simp_rw [integral_exp_neg_half_lift hε]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlog2 : Real.log (2*(N : ℝ)) = Real.log 2+Real.log N := Real.log_mul (by norm_num) hn
  have hlog4 : Real.log (4*(N : ℝ)) = 2*Real.log 2+Real.log N := by
    rw [Real.log_mul (by norm_num) hn]
    have hh : Real.log (4 : ℝ) = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hh]
  unfold chebyshevBiNullProducer
  push_cast
  rw [hlog2,hlog4]
  ring

theorem tsum_primeTerm_factorialBiNull (N : ℕ) :
    (∑' n, primeTerm (factorialBiNull N) n) = chebyshevBiNullProducer N/Real.sqrt N := by
  have hs (K : ℕ) : Summable (primeTerm (factorialLift K)) := (factorialLift_admissible K).2.1.of_abs
  have hp (n : ℕ) : primeTerm (factorialBiNull N) n =
      (primeTerm (factorialLift (4*N)) n-4*primeTerm (factorialLift (2*N)) n+
        4*primeTerm (factorialLift N) n)/Real.sqrt N := by
    unfold primeTerm factorialBiNull
    split_ifs <;> ring
  simp_rw [hp]
  rw [tsum_div_const, Summable.tsum_add ((hs (4*N)).sub ((hs (2*N)).mul_left 4)) ((hs N).mul_left 4),
    Summable.tsum_sub (hs (4*N)) ((hs (2*N)).mul_left 4), tsum_mul_left, tsum_mul_left]
  simp_rw [tsum_primeTerm_factorialLift]
  rfl

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
