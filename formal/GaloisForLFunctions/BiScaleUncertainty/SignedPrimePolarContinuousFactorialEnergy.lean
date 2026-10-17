import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarContinuousFactorialProducer
import GaloisForLFunctions.BiScaleUncertainty.AntitoneDyadicStencil

/-! Uniform and nonvanishing L² size of the concrete continuous factorial producer.
Finite antitone cancellation controls the upper bound; a full top band supplies the lower bound. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

private theorem smoothFactorialBiNull_stencil {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    let f := fun j : ℕ => clampedRamp (factorialCollar N) ((j : ℝ)*Real.exp x/(4*(N : ℝ)));
    smoothFactorialBiNull N x = Real.exp (x/2)*
      ((∑ j ∈ Finset.Icc 1 (4*N), f j)-4*(∑ j ∈ Finset.Icc 1 (2*N), f (2*j))+
        4*(∑ j ∈ Finset.Icc 1 N, f (4*j)))/Real.sqrt N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h2 (j : ℕ) : ((2*j : ℕ) : ℝ)*Real.exp x/(4*(N : ℝ)) =
      (j : ℝ)*Real.exp x/((2*N : ℕ) : ℝ) := by push_cast; field_simp; ring
  have h4 (j : ℕ) : ((4*j : ℕ) : ℝ)*Real.exp x/(4*(N : ℝ)) =
      (j : ℝ)*Real.exp x/(N : ℝ) := by push_cast; field_simp
  dsimp
  simp_rw [h2, h4]
  unfold smoothFactorialBiNull smoothFactorialLift
  push_cast
  ring

/-- Pointwise square control follows from finite antitone cancellation. -/
theorem smoothFactorialBiNull_sq_le {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    (smoothFactorialBiNull N x)^2 ≤ 4*Real.exp x/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let f := fun j : ℕ => clampedRamp (factorialCollar N) ((j : ℝ)*Real.exp x/(4*(N : ℝ)))
  have hf : Antitone f := by
    intro a b hab
    apply antitone_clampedRamp (factorialCollar_pos hN)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (Real.exp_pos x).le
  have hb := antitone_dyadic_stencil_bounds hf
    (fun j => clampedRamp_nonneg _ _) (fun j => clampedRamp_le_one _ _) N
  dsimp at hb
  let D := (∑ j ∈ Finset.Icc 1 (4*N), f j)-4*(∑ j ∈ Finset.Icc 1 (2*N), f (2*j))+
    4*(∑ j ∈ Finset.Icc 1 N, f (4*j))
  have hD : D^2 ≤ 4 := by
    have hp := mul_nonneg (show 0 ≤ D+2 by dsimp [D]; linarith)
      (show 0 ≤ 2-D by dsimp [D]; linarith)
    nlinarith
  have he : Real.exp (x/2)^2 = Real.exp x := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hs : smoothFactorialBiNull N x = Real.exp (x/2)*D/Real.sqrt N :=
    smoothFactorialBiNull_stencil hN x
  rw [hs, div_pow, mul_pow, he, Real.sq_sqrt hn.le]
  apply div_le_div_of_nonneg_right _ hn.le
  nlinarith [mul_le_mul_of_nonneg_left hD (Real.exp_pos x).le]

theorem integrable_smoothFactorialBiNull_sq {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x => (smoothFactorialBiNull N x)^2) := by
  apply ((continuous_smoothFactorialBiNull N).pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using
    (hasCompactSupport_smoothFactorialBiNull hN).mul_left (f := smoothFactorialBiNull N)

/-- The squared L² norm is bounded uniformly, without a discrepancy assumption. -/
theorem integral_smoothFactorialBiNull_sq_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ x : ℝ, (smoothFactorialBiNull N x)^2) ≤ 16 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (4*(N : ℝ)+1) := Real.log_nonneg (by have h : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have he : (∫ x : ℝ, (smoothFactorialBiNull N x)^2) =
      ∫ x in Icc 0 (Real.log (4*(N : ℝ)+1)), (smoothFactorialBiNull N x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_cases h0 : 0 ≤ x
    · have ht : Real.log (4*(N : ℝ)+1) ≤ x := by
        by_contra! h
        exact hx ⟨h0, h.le⟩
      rw [smoothFactorialBiNull_tail hN ht, zero_pow (by omega)]
    · rw [smoothFactorialBiNull_of_nonpos hN (by linarith), zero_pow (by omega)]
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
  have hc : Continuous (fun x : ℝ => 4*Real.exp x/(N : ℝ)) := by fun_prop
  calc
    _ ≤ ∫ x in (0 : ℝ)..Real.log (4*(N : ℝ)+1), 4*Real.exp x/(N : ℝ) :=
      intervalIntegral.integral_mono_on hL
        (((continuous_smoothFactorialBiNull N).pow 2).intervalIntegrable _ _)
        (hc.intervalIntegrable _ _) (fun x _ => smoothFactorialBiNull_sq_le hN x)
    _ = 16 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_exp,
        Real.exp_log (by positivity : 0 < 4*(N : ℝ)+1), Real.exp_zero]
      field_simp
      ring

/-- On a full logarithmic interval the smoothed producer retains one rectangle. -/
theorem smoothFactorialBiNull_on_top_band {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : x ∈ Icc (Real.log (2*(N : ℝ)+1)) (Real.log (4*(N : ℝ)))) :
    smoothFactorialBiNull N x = Real.exp (x/2)/Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := Real.exp_le_exp.mpr hx.1
  have hhi := Real.exp_le_exp.mpr hx.2
  rw [Real.exp_log (by positivity : 0 < 2*(N : ℝ)+1)] at hlo
  rw [Real.exp_log (by positivity : 0 < 4*(N : ℝ))] at hhi
  have hb4 := factorialCollar_mul_le_one hN (by omega : 4*N ≤ 4*N)
  have hb2 := factorialCollar_mul_le_one hN (by omega : 2*N ≤ 4*N)
  have hb1 := factorialCollar_mul_le_one hN (by omega : N ≤ 4*N)
  have h4 : smoothFactorialLift (factorialCollar N) (4*N) x = Real.exp (x/2) := by
    apply smoothFactorialLift_eq_exp_half (factorialCollar_pos hN) (by omega)
    · push_cast at hb4 ⊢
      nlinarith
    · push_cast
      exact hhi
  have h2 : smoothFactorialLift (factorialCollar N) (2*N) x = 0 := by
    apply smoothFactorialLift_eq_zero (factorialCollar_pos hN) (by omega)
    push_cast at hb2 ⊢
    nlinarith
  have h1 : smoothFactorialLift (factorialCollar N) N x = 0 := by
    apply smoothFactorialLift_eq_zero (factorialCollar_pos hN) hN
    nlinarith
  simp [smoothFactorialBiNull, h4, h2, h1]

/-- Small signed pairing is not obtained by letting the L² norm vanish. -/
theorem one_le_integral_smoothFactorialBiNull_sq {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ ∫ x : ℝ, (smoothFactorialBiNull N x)^2 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hL : Real.log (2*(N : ℝ)+1) ≤ Real.log (4*(N : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have he : (∫ x in Icc (Real.log (2*(N : ℝ)+1)) (Real.log (4*(N : ℝ))),
      (smoothFactorialBiNull N x)^2) = (4*(N : ℝ)-(2*(N : ℝ)+1))/(N : ℝ) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
    have heq : (∫ x in Real.log (2*(N : ℝ)+1)..Real.log (4*(N : ℝ)),
        (smoothFactorialBiNull N x)^2) =
        ∫ x in Real.log (2*(N : ℝ)+1)..Real.log (4*(N : ℝ)), Real.exp x/(N : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL] at hx
      dsimp only
      rw [smoothFactorialBiNull_on_top_band hN hx, div_pow, Real.sq_sqrt hn.le]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq, intervalIntegral.integral_div, integral_exp,
      Real.exp_log (by positivity : 0 < 4*(N : ℝ)),
      Real.exp_log (by positivity : 0 < 2*(N : ℝ)+1)]
  have hmono := setIntegral_le_integral (s := Icc (Real.log (2*(N : ℝ)+1)) (Real.log (4*(N : ℝ))))
    (integrable_smoothFactorialBiNull_sq hN)
    (Filter.Eventually.of_forall (fun x => sq_nonneg (smoothFactorialBiNull N x)))
  rw [he] at hmono
  exact le_trans ((le_div_iff₀ hn).2 (by linarith)) hmono

/-- An unconditional compact continuous producer preserving every positive integer atom,
with a vanishing quantitative pairing bound and a nonvanishing uniformly bounded L² norm. -/
theorem continuousFactorialProducer_certificate (n : ℕ) :
    (∀ m : ℕ, 1 ≤ m → continuousFactorialProducer n (Real.log m) = factorialBiNull (n+1) (Real.log m)) ∧
      |fullPairing (continuousFactorialProducer n)| ≤
        (10*Real.log (4*((n+1 : ℕ) : ℝ)+1)+3+1/(8*((n+1 : ℕ) : ℝ)))/Real.sqrt (n+1 : ℕ) ∧
      1 ≤ (∫ x : ℝ, (continuousFactorialProducer n x)^2) ∧
      (∫ x : ℝ, (continuousFactorialProducer n x)^2) ≤ 16 := by
  exact ⟨fun m hm => smoothFactorialBiNull_at_log (by omega) hm,
    abs_fullPairing_smoothFactorialBiNull_le (by omega),
    one_le_integral_smoothFactorialBiNull_sq (by omega),
    integral_smoothFactorialBiNull_sq_le (by omega)⟩

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
