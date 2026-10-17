import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarContinuousFactorialEnergy

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def rampBiNull (ε : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (smoothFactorialLift ε (4*N) x-4*smoothFactorialLift ε (2*N) x+
    4*smoothFactorialLift ε N x)/Real.sqrt N

theorem continuous_rampBiNull (ε : ℝ) (N : ℕ) : Continuous (rampBiNull ε N) :=
  (((continuous_smoothFactorialLift _ _).sub
    (continuous_const.mul (continuous_smoothFactorialLift _ _))).add
    (continuous_const.mul (continuous_smoothFactorialLift _ _))).div_const _

theorem rampBiNull_zero_of_nonpos {ε x : ℝ} (hε : 0 < ε) (N : ℕ) (hx : x ≤ 0) :
    rampBiNull ε N x = 0 := by
  unfold rampBiNull
  rw [smoothFactorialLift_of_nonpos hε hx, smoothFactorialLift_of_nonpos hε hx,
    smoothFactorialLift_of_nonpos hε hx]
  push_cast
  ring

theorem rampBiNull_tail_exp {ε x : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hx : 4*(N : ℝ)*(1+ε) ≤ Real.exp x) : rampBiNull ε N x = 0 := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hz (K : ℕ) (hK0 : 1 ≤ K) (hK : K ≤ 4*N) : smoothFactorialLift ε K x = 0 := by
    apply smoothFactorialLift_eq_zero hε hK0
    have hk : (K : ℝ) ≤ 4*(N : ℝ) := by exact_mod_cast hK
    nlinarith
  simp [rampBiNull, hz (4*N) (by omega) (by omega),
    hz (2*N) (by omega) (by omega), hz N hN (by omega)]

theorem rampBiNull_tail {ε x : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hbudget : ε*(4*(N : ℝ)) ≤ 1) (hx : Real.log (4*(N : ℝ)+1) ≤ x) :
    rampBiNull ε N x = 0 := by
  apply rampBiNull_tail_exp hε hN
  have he := Real.exp_le_exp.mpr hx
  rw [Real.exp_log (by positivity : 0 < 4*(N : ℝ)+1)] at he
  nlinarith

theorem hasCompactSupport_rampBiNull {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hbudget : ε*(4*(N : ℝ)) ≤ 1) : HasCompactSupport (rampBiNull ε N) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc 0 (Real.log (4*(N : ℝ)+1))) isCompact_Icc
  intro x hx
  constructor
  · by_contra! hn
    exact hx (rampBiNull_zero_of_nonpos hε N hn.le)
  · by_contra! hn
    exact hx (rampBiNull_tail hε hN hbudget hn.le)

/-- A whole top band is unchanged by any admissible positive collar. -/
theorem rampBiNull_on_top_band {ε x : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hlo : 2*(N : ℝ)*(1+ε) ≤ Real.exp x) (hhi : Real.exp x ≤ 4*(N : ℝ)) :
    rampBiNull ε N x = Real.exp (x/2)/Real.sqrt N := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h4 : smoothFactorialLift ε (4*N) x = Real.exp (x/2) := by
    apply smoothFactorialLift_eq_exp_half hε (by omega)
    · push_cast
      nlinarith
    · push_cast
      exact hhi
  have h2 : smoothFactorialLift ε (2*N) x = 0 := by
    apply smoothFactorialLift_eq_zero hε (by omega)
    push_cast
    exact hlo
  have h1 : smoothFactorialLift ε N x = 0 := by
    apply smoothFactorialLift_eq_zero hε hN
    nlinarith
  simp [rampBiNull, h4, h2, h1]

private theorem rampBiNull_stencil {ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    let f := fun j : ℕ => clampedRamp ε ((j : ℝ)*Real.exp x/(4*(N : ℝ)));
    rampBiNull ε N x = Real.exp (x/2)*
      ((∑ j ∈ Finset.Icc 1 (4*N), f j)-4*(∑ j ∈ Finset.Icc 1 (2*N), f (2*j))+
        4*(∑ j ∈ Finset.Icc 1 N, f (4*j)))/Real.sqrt N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h2 (j : ℕ) : ((2*j : ℕ) : ℝ)*Real.exp x/(4*(N : ℝ)) =
      (j : ℝ)*Real.exp x/((2*N : ℕ) : ℝ) := by push_cast; field_simp; ring
  have h4 (j : ℕ) : ((4*j : ℕ) : ℝ)*Real.exp x/(4*(N : ℝ)) =
      (j : ℝ)*Real.exp x/(N : ℝ) := by push_cast; field_simp
  dsimp
  simp_rw [h2, h4]
  unfold rampBiNull smoothFactorialLift
  push_cast
  ring

theorem rampBiNull_sq_le {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N) (x : ℝ) :
    (rampBiNull ε N x)^2 ≤ 4*Real.exp x/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let f := fun j : ℕ => clampedRamp ε ((j : ℝ)*Real.exp x/(4*(N : ℝ)))
  have hf : Antitone f := by
    intro a b hab
    apply antitone_clampedRamp hε
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
  have hs : rampBiNull ε N x = Real.exp (x/2)*D/Real.sqrt N := rampBiNull_stencil hN x
  rw [hs, div_pow, mul_pow, he, Real.sq_sqrt hn.le]
  apply div_le_div_of_nonneg_right _ hn.le
  nlinarith [mul_le_mul_of_nonneg_left hD (Real.exp_pos x).le]

theorem abs_rampBiNull_le {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N) (x : ℝ) :
    |rampBiNull ε N x| ≤ 2*Real.exp (x/2)/Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := rampBiNull_sq_le hε hN x
  have he : (2*Real.exp (x/2)/Real.sqrt N)^2 = 4*Real.exp x/(N : ℝ) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hn.le]
    have hp : Real.exp (x/2)^2 = Real.exp x := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hp]
    norm_num
  have hpos : 0 ≤ 2*Real.exp (x/2)/Real.sqrt N := by positivity
  have ha : |rampBiNull ε N x|^2 = (rampBiNull ε N x)^2 := sq_abs _
  nlinarith [abs_nonneg (rampBiNull ε N x)]

theorem integral_rampBiNull_sq_le {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hbudget : ε*(4*(N : ℝ)) ≤ 1) : (∫ x : ℝ, (rampBiNull ε N x)^2) ≤ 16 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (4*(N : ℝ)+1) := Real.log_nonneg (by have h : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have he : (∫ x : ℝ, (rampBiNull ε N x)^2) =
      ∫ x in Icc 0 (Real.log (4*(N : ℝ)+1)), (rampBiNull ε N x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_cases h0 : 0 ≤ x
    · have ht : Real.log (4*(N : ℝ)+1) ≤ x := by
        by_contra! h
        exact hx ⟨h0, h.le⟩
      rw [rampBiNull_tail hε hN hbudget ht, zero_pow (by omega)]
    · rw [rampBiNull_zero_of_nonpos hε N (by linarith), zero_pow (by omega)]
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
  have hc : Continuous (fun x : ℝ => 4*Real.exp x/(N : ℝ)) := by fun_prop
  calc
    _ ≤ ∫ x in (0 : ℝ)..Real.log (4*(N : ℝ)+1), 4*Real.exp x/(N : ℝ) :=
      intervalIntegral.integral_mono_on hL (((continuous_rampBiNull ε N).pow 2).intervalIntegrable _ _)
        (hc.intervalIntegrable _ _) (fun x _ => rampBiNull_sq_le hε hN x)
    _ = 16 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_exp,
        Real.exp_log (by positivity : 0 < 4*(N : ℝ)+1), Real.exp_zero]
      field_simp
      ring

/-- Integer separation leaves every ramp value unchanged throughout a small dilation collar. -/
theorem smoothFactorialLift_shift_at_log {ε t : ℝ} {K n : ℕ}
    (hε : 0 < ε) (hεK : ε*(K : ℝ) ≤ 1) (hn : 1 ≤ n) (ht : 0 ≤ t)
    (hbudget : (K : ℝ)*(1+ε)*Real.exp t ≤ (K : ℝ)+1) :
    Real.exp (t/2)*smoothFactorialLift ε K (Real.log n-t) = factorialLift K (Real.log n) := by
  by_cases hK : K = 0
  · simp [smoothFactorialLift, factorialLift, hK]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hshift : Real.exp (Real.log (n : ℝ)-t) ≤ n := by
    have h := Real.exp_le_exp.mpr (show Real.log (n : ℝ)-t ≤ Real.log n by linarith)
    simpa only [Real.exp_log hn0] using h
  have hprod : Real.exp (Real.log (n : ℝ)-t)*Real.exp t = n := by
    rw [← Real.exp_add, sub_add_cancel, Real.exp_log hn0]
  have hh : Real.exp (t/2)*Real.exp ((Real.log (n : ℝ)-t)/2) = Real.exp (Real.log n/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← smoothFactorialLift_at_log hε hεK hn]
  unfold smoothFactorialLift
  rw [← mul_assoc, hh]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [Real.exp_log hn0]
  by_cases hjn : j*n ≤ K
  · have hjn' : (j : ℝ)*(n : ℝ) ≤ K := by exact_mod_cast hjn
    rw [clampedRamp_eq_one hε ((div_le_iff₀ hK0).2 (by nlinarith)),
      clampedRamp_eq_one hε ((div_le_iff₀ hK0).2 (by simpa using hjn'))]
  · have hjn' : (K : ℝ)+1 ≤ (j : ℝ)*(n : ℝ) := by
      exact_mod_cast (show K+1 ≤ j*n by omega)
    have hlo : (K : ℝ)*(1+ε) ≤ (j : ℝ)*Real.exp (Real.log (n : ℝ)-t) := by
      apply (mul_le_mul_iff_left₀ (Real.exp_pos t)).mp
      calc
        _ ≤ (K : ℝ)+1 := hbudget
        _ ≤ (j : ℝ)*(n : ℝ) := hjn'
        _ = _ := by rw [mul_assoc, hprod]
    rw [clampedRamp_eq_zero hε ((le_div_iff₀ hK0).2 (by nlinarith)),
      clampedRamp_eq_zero hε ((le_div_iff₀ hK0).2 (by nlinarith))]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
