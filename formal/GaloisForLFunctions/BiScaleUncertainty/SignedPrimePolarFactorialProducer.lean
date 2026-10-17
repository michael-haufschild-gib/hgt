import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialLift
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHarmonicCorrection

/-! An explicit, unconditional producer for the actual signed prime–polar measure.
The test is a fixed bi-null combination of real-ratio factorial rectangles;
its literal full pairing is O(log N / sqrt N). No discrepancy hypothesis occurs. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

theorem integral_polar_factorialLift_eq (K : ℕ) :
    (∫ x in Ici (0 : ℝ), polarDensity x * factorialLift K x) =
      (K : ℝ)*realHarmonic K - K + K*Real.log K - floorSummatory chebyshevPsi K := by
  rw [integral_polar_factorialLift, floorSummatory_chebyshevPsi]
  by_cases hK : K = 0
  · simp [hK, realHarmonic]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (Nat.pos_of_ne_zero hK)
  have heq : ∀ j ∈ Finset.Icc 1 K,
      (K : ℝ)/(j : ℝ)-1+Real.log ((K : ℝ)/(j : ℝ)) =
        (K : ℝ)*(1/(j : ℝ))-1+Real.log K-Real.log j := by
    intro j hj
    have hjpos : (0 : ℝ) < j := by
      exact_mod_cast (show 0 < j from (Finset.mem_Icc.mp hj).1)
    rw [Real.log_div hKpos.ne' hjpos.ne']
    ring
  rw [Finset.sum_congr rfl heq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, realHarmonic]
  ring

/-- Exact signed evaluation; the harmonic and logarithmic terms include both
polar exponential branches. -/
theorem fullPairing_factorialLift_eq (K : ℕ) :
    fullPairing (factorialLift K) =
      2*floorSummatory chebyshevPsi K - K*Real.log K - K*realHarmonic K + K := by
  rw [fullPairing, tsum_primeTerm_factorialLift, integral_polar_factorialLift_eq]
  ring

/-- The coefficients and normalization are fixed explicitly, not existential. -/
def factorialBiNull (N : ℕ) (x : ℝ) : ℝ :=
  (factorialLift (4*N) x - 4*factorialLift (2*N) x + 4*factorialLift N x) /
    Real.sqrt N

theorem factorialBiNull_zero (N : ℕ) : factorialBiNull N 0 = 0 := by
  have hz (K : ℕ) : factorialLift K 0 = K := by
    simpa using (factorialLift_at_log (K := K) (n := 1) (by omega))
  unfold factorialBiNull
  rw [hz, hz, hz]
  push_cast
  ring

/-- Fixed amplitude at the top atom: normalization does not make the test trivial. -/
theorem factorialBiNull_top {N : ℕ} (hN : 1 ≤ N) :
    factorialBiNull N (Real.log (4*(N : ℝ))) = 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (4*(N : ℝ)) = 2*Real.sqrt N := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 4*(N : ℝ)),
      Real.sq_sqrt hn.le, Real.sqrt_nonneg (4*(N : ℝ)), Real.sqrt_nonneg (N : ℝ)]
  have hdiv1 : N/(4*N) = 0 := Nat.div_eq_of_lt (by omega)
  have hdiv2 : (2*N)/(4*N) = 0 := Nat.div_eq_of_lt (by omega)
  have hdiv4 : (4*N)/(4*N) = 1 := Nat.div_self (by omega)
  have hcast : 4*(N : ℝ) = ((4*N : ℕ) : ℝ) := by push_cast; rfl
  unfold factorialBiNull
  rw [hcast, factorialLift_at_log (by omega : 1 ≤ 4*N),
    factorialLift_at_log (by omega : 1 ≤ 4*N),
    factorialLift_at_log (by omega : 1 ≤ 4*N), hdiv4, hdiv2, hdiv1]
  push_cast
  rw [hs]
  have hsn : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  field_simp

/-- This producer does not masquerade as an autocorrelation receiver. -/
theorem factorialBiNull_ne_autocorr (n : ℕ) (f : C_c(ℝ, ℝ)) :
    factorialBiNull (n+1) ≠ RHTower.ArchimedeanAnomaly.autocorr f := by
  intro heq
  have hz := congrFun heq 0
  rw [factorialBiNull_zero] at hz
  have ht := congrFun heq (Real.log (4*((n+1 : ℕ) : ℝ)))
  rw [factorialBiNull_top (by omega)] at ht
  have hc := autocorr_eq_zero_of_zero_eq_zero f.hasCompactSupport f.continuous hz.symm
    (Real.log (4*((n+1 : ℕ) : ℝ)))
  linarith

private theorem primeTerm_factorialBiNull (N n : ℕ) :
    primeTerm (factorialBiNull N) n =
      (primeTerm (factorialLift (4*N)) n - 4*primeTerm (factorialLift (2*N)) n +
        4*primeTerm (factorialLift N) n) / Real.sqrt N := by
  unfold primeTerm factorialBiNull
  split_ifs <;> ring

private theorem primeTerm_factorialBiNull_tail (N n : ℕ) (hn : n ∉ Finset.Icc 1 (4*N)) :
    primeTerm (factorialBiNull N) n = 0 := by
  have h2 : n ∉ Finset.Icc 1 (2*N) := by simp only [Finset.mem_Icc] at *; omega
  have h1 : n ∉ Finset.Icc 1 N := by simp only [Finset.mem_Icc] at *; omega
  rw [primeTerm_factorialBiNull, primeTerm_factorialLift_tail _ _ hn,
    primeTerm_factorialLift_tail _ _ h2, primeTerm_factorialLift_tail _ _ h1]
  simp

theorem integrable_polar_factorialBiNull (N : ℕ) :
    Integrable (fun x => polarDensity x * factorialBiNull N x) := by
  have heq : (fun x => polarDensity x * factorialBiNull N x) =
      fun x => ((polarDensity x * factorialLift (4*N) x) -
        4*(polarDensity x * factorialLift (2*N) x) +
        4*(polarDensity x * factorialLift N x))/Real.sqrt N := by
    funext x
    unfold factorialBiNull
    ring
  rw [heq]
  exact (((integrable_polar_factorialLift (4*N)).sub
    ((integrable_polar_factorialLift (2*N)).const_mul 4)).add
    ((integrable_polar_factorialLift N).const_mul 4)).div_const _

/-- Actual domain admission, including absolute convergence of the literal atoms. -/
theorem factorialBiNull_admissible (N : ℕ) :
    (Function.support (primeTerm (factorialBiNull N))).Finite ∧
      Summable (fun n => |primeTerm (factorialBiNull N) n|) ∧
      IntegrableOn (fun x => polarDensity x * factorialBiNull N x) (Ici 0) := by
  refine ⟨?_, ?_, (integrable_polar_factorialBiNull N).integrableOn⟩
  · apply (Finset.finite_toSet (Finset.Icc 1 (4*N))).subset
    intro n hn
    by_contra hout
    exact hn (primeTerm_factorialBiNull_tail N n hout)
  · apply summable_of_ne_finset_zero (s := Finset.Icc 1 (4*N))
    intro n hn
    rw [primeTerm_factorialBiNull_tail N n hn, abs_zero]

private theorem fullPairing_factorialBiNull_linear (N : ℕ) :
    fullPairing (factorialBiNull N) =
      (fullPairing (factorialLift (4*N)) - 4*fullPairing (factorialLift (2*N)) +
        4*fullPairing (factorialLift N))/Real.sqrt N := by
  have hs (K : ℕ) : Summable (primeTerm (factorialLift K)) :=
    (factorialLift_admissible K).2.1.of_abs
  have hi (K : ℕ) : IntegrableOn (fun x => polarDensity x * factorialLift K x) (Ici 0) :=
    (factorialLift_admissible K).2.2
  have hi2 : IntegrableOn (fun x => 4*(polarDensity x * factorialLift (2*N) x)) (Ici 0) :=
    (hi (2*N)).const_mul 4
  have hi1 : IntegrableOn (fun x => 4*(polarDensity x * factorialLift N x)) (Ici 0) :=
    (hi N).const_mul 4
  have hsub : IntegrableOn (fun x => polarDensity x * factorialLift (4*N) x -
      4*(polarDensity x * factorialLift (2*N) x)) (Ici 0) := (hi (4*N)).sub hi2
  have hp : (fun x => polarDensity x * factorialBiNull N x) =
      fun x => ((polarDensity x * factorialLift (4*N) x) -
        4*(polarDensity x * factorialLift (2*N) x) +
        4*(polarDensity x * factorialLift N x))/Real.sqrt N := by
    funext x
    unfold factorialBiNull
    ring
  unfold fullPairing
  simp_rw [primeTerm_factorialBiNull]
  rw [tsum_div_const, Summable.tsum_add ((hs (4*N)).sub ((hs (2*N)).mul_left 4))
    ((hs N).mul_left 4), Summable.tsum_sub (hs (4*N)) ((hs (2*N)).mul_left 4),
    tsum_mul_left, tsum_mul_left, hp, integral_div,
    integral_add hsub hi1, integral_sub (hi (4*N)) hi2,
    integral_const_mul, integral_const_mul]
  ring

/-- Both factorial poles cancel before the bounded harmonic correction is estimated. -/
theorem fullPairing_factorialBiNull_eq {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (factorialBiNull N) =
      (2*chebyshevBiNullProducer N - harmonicCorrection N)/Real.sqrt N := by
  rw [fullPairing_factorialBiNull_linear]
  simp_rw [fullPairing_factorialLift_eq]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlog2 : Real.log (2*(N : ℝ)) = Real.log 2+Real.log N :=
    Real.log_mul (by norm_num) hn
  have hlog4 : Real.log (4*(N : ℝ)) = 2*Real.log 2+Real.log N := by
    rw [Real.log_mul (by norm_num) hn]
    have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
      rw [show (4 : ℝ)=2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [h4]
  unfold chebyshevBiNullProducer harmonicCorrection
  push_cast
  rw [hlog2, hlog4]
  ring

theorem abs_fullPairing_factorialBiNull_le {N : ℕ} (hN : 1 ≤ N) :
    |fullPairing (factorialBiNull N)| ≤
      (10*Real.log (4*(N : ℝ)+1)+3)/Real.sqrt N := by
  rw [fullPairing_factorialBiNull_eq hN, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hb := abs_chebyshevBiNullProducer_le hN
  obtain ⟨hc0,hc1⟩ := harmonicCorrection_bounds hN
  calc
    _ ≤ |2*chebyshevBiNullProducer N| + |harmonicCorrection N| := abs_sub _ _
    _ = 2*|chebyshevBiNullProducer N| + harmonicCorrection N := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hc0]
    _ ≤ _ := by linarith

/-- Public unconditional endpoint: only an integer index is supplied. -/
theorem factorialBiNull_producer (n : ℕ) :
    (Function.support (primeTerm (factorialBiNull (n+1)))).Finite ∧
      Summable (fun m => |primeTerm (factorialBiNull (n+1)) m|) ∧
      IntegrableOn (fun x => polarDensity x * factorialBiNull (n+1) x) (Ici 0) ∧
      |fullPairing (factorialBiNull (n+1))| ≤
        (10*Real.log (4*((n+1 : ℕ) : ℝ)+1)+3)/Real.sqrt (n+1 : ℕ) := by
  obtain ⟨hf,hs,hi⟩ := factorialBiNull_admissible (n+1)
  exact ⟨hf,hs,hi,abs_fullPairing_factorialBiNull_le (by omega)⟩

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
