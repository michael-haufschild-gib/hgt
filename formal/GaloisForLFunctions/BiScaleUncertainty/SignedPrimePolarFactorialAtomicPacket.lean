import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarClampedPrimeSum
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalSource
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarPacket

/-! A logarithmic envelope for the actual translated prime packet of the
factorial ramp, including a small negative physical collar. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower ArithmeticFunction
noncomputable section
set_option autoImplicit false

def factorialRampSource (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨sourceFactorialRamp (n+1), continuous_sourceFactorialRamp _⟩,
    hasCompactSupport_sourceFactorialRamp (by omega)⟩

theorem atomic_smoothFactorialLift_eq {K : ℕ} (hK : 1 ≤ K)
    (ε u : ℝ) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, primeWeight m*smoothFactorialLift ε K (u+Real.log m)) =
      Real.exp (u/2)*clampedPrimeFactorialSum ε K M ((K : ℝ)*Real.exp (-u)) := by
  unfold clampedPrimeFactorialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have he : Real.exp ((u+Real.log (m : ℝ))/2) = Real.exp (u/2)*Real.sqrt m := by
    rw [show (u+Real.log (m : ℝ))/2 = u/2+Real.log (m : ℝ)/2 by ring,
      Real.exp_add, exp_half_log_eq_sqrt hm0]
  have ht (j : ℕ) : (j : ℝ)*Real.exp (u+Real.log (m : ℝ))/(K : ℝ) =
      (j : ℝ)*(m : ℝ)/((K : ℝ)*Real.exp (-u)) := by
    rw [Real.exp_add, Real.exp_log hm0, Real.exp_neg]
    field_simp
  unfold primeWeight smoothFactorialLift
  rw [he]
  simp_rw [ht]
  have hs : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
  field_simp
  simp only [mul_comm]

private theorem clamped_stencil_bound {ε v : ℝ} {N M : ℕ}
    (hε : 0 < ε) (hv : 0 < v) (hcap : v ≤ 2*(N : ℝ))
    (hM : (1+ε)*(4*v) ≤ M) (hwidth : ε*(4*v) ≤ 2) :
    |clampedPrimeFactorialSum ε (4*N) M (4*v)-
        4*clampedPrimeFactorialSum ε (2*N) M (2*v)+
        4*clampedPrimeFactorialSum ε N M v| ≤
      19*Real.log (4*(1+ε)*v+1)+1 := by
  have h4 := clampedPrimeFactorialSum_error hε (by positivity : 0 < 4*v)
    (show 4*v ≤ 2*((4*N : ℕ) : ℝ) by push_cast; linarith) hM hwidth
  have h2 := clampedPrimeFactorialSum_error hε (by positivity : 0 < 2*v)
    (show 2*v ≤ 2*((2*N : ℕ) : ℝ) by push_cast; linarith)
    (show (1+ε)*(2*v) ≤ M by nlinarith) (show ε*(2*v) ≤ 2 by nlinarith)
  have h1 := clampedPrimeFactorialSum_error hε hv hcap
    (show (1+ε)*v ≤ M by nlinarith) (show ε*v ≤ 2 by nlinarith)
  have hlog (a : ℝ) (ha : a ∈ Icc 0 (4*(1+ε)*v)) :
      Real.log (a+1) ≤ Real.log (4*(1+ε)*v+1) :=
    Real.log_le_log (by linarith [ha.1]) (by linarith [ha.2])
  have hl4 : Real.log ((1+ε)*(4*v)+1) = Real.log (4*(1+ε)*v+1) := by congr 1; ring
  have hl2 := hlog ((1+ε)*(2*v)) ⟨by positivity, by nlinarith⟩
  have hl1 := hlog ((1+ε)*v) ⟨by positivity, by nlinarith⟩
  have hl0 := hlog (4*v) ⟨by positivity, by nlinarith⟩
  have hln : 0 ≤ Real.log (4*(1+ε)*v+1) := Real.log_nonneg (by nlinarith)
  have ha := abs_le.mp (abs_realFactorialBiNull_le hv.le)
  unfold realFactorialBiNull at ha
  rw [hl4] at h4
  rw [abs_le]
  constructor <;> linarith [h4.1, h4.2, h2.1, h2.2, h1.1, h1.2]

/-- The collar admits all divisor products needed by the factorial identity. -/
theorem factorial_packet_collar_bounds {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (hu : -3*sourceFactorialWidth N ≤ u) :
    Real.exp (-u) ≤ 5/4 ∧
      (1+sourceFactorialCollar N)*Real.exp (-u) ≤ 2 ∧
      sourceFactorialCollar N*(4*(N : ℝ)*Real.exp (-u)) ≤ 2 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd := sourceFactorialWidth_pos hN
  have h3 : Real.exp (-u) ≤ Real.exp (3*sourceFactorialWidth N) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [exp_three_sourceFactorialWidth] at h3
  have hinv : 1/(4*(N : ℝ)) ≤ 1/4 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
    linarith
  have he : Real.exp (-u) ≤ 5/4 := by linarith
  have h4 : (1+sourceFactorialCollar N)*Real.exp (-u) ≤ 2 := by
    unfold sourceFactorialCollar
    rw [show 1+(Real.exp (sourceFactorialWidth N)-1) = Real.exp (sourceFactorialWidth N) by ring,
      ← Real.exp_add]
    exact (Real.exp_le_exp.mpr (show sourceFactorialWidth N+-u ≤ 4*sourceFactorialWidth N by
      linarith)).trans (exp_four_sourceFactorialWidth_le_two hN)
  have hb := sourceFactorialCollar_budget hN
  have hmul := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-u)).le
  exact ⟨he, h4, by nlinarith⟩

theorem atomicSource_factorialRamp_eq (n : ℕ) (u : ℝ) (K : ℕ) :
    atomicSource (factorialRampSource n) K u =
      Real.exp (u/2)/Real.sqrt (n+1 : ℕ) *
        (clampedPrimeFactorialSum (sourceFactorialCollar (n+1)) (4*(n+1)) (K+2)
            (4*((n+1 : ℕ) : ℝ)*Real.exp (-u))-
          4*clampedPrimeFactorialSum (sourceFactorialCollar (n+1)) (2*(n+1)) (K+2)
            (2*((n+1 : ℕ) : ℝ)*Real.exp (-u))+
          4*clampedPrimeFactorialSum (sourceFactorialCollar (n+1)) (n+1) (K+2)
            (((n+1 : ℕ) : ℝ)*Real.exp (-u))) := by
  have hadd (a b c : ℝ) : a*(b+c) = a*b+a*c := mul_add a b c
  change (∑ m ∈ Finset.Icc 1 (K+2), primeWeight m*sourceFactorialRamp (n+1) (u+Real.log m)) = _
  simp only [sourceFactorialRamp, rampBiNull, ← mul_div_assoc, hadd, mul_sub,
    ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he (a b : ℝ) : a*(4*b) = 4*(a*b) := by ring
  simp only [he, ← Finset.mul_sum]
  rw [atomic_smoothFactorialLift_eq (by omega : 1 ≤ 4*(n+1)),
    atomic_smoothFactorialLift_eq (by omega : 1 ≤ 2*(n+1)),
    atomic_smoothFactorialLift_eq (by omega : 1 ≤ n+1)]
  push_cast
  ring

theorem factorial_packet_log_bound {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (hu : u ≤ Real.log (4*(N : ℝ)+1)) :
    Real.log (4*(1+sourceFactorialCollar N)*((N : ℝ)*Real.exp (-u))+1) ≤
      Real.log (13*(N : ℝ))-u := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hε := sourceFactorialCollar_pos hN
  have hb := sourceFactorialCollar_budget hN
  have hsmall : sourceFactorialCollar N ≤ 1 := by nlinarith
  have hexp : Real.exp u ≤ 5*(N : ℝ) := by
    have h := Real.exp_le_exp.mpr hu
    rw [Real.exp_log (by positivity : 0 < 4*(N : ℝ)+1)] at h
    linarith
  have he : Real.exp u*Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hunit : 1 ≤ 5*(N : ℝ)*Real.exp (-u) := by
    have h := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-u)).le
    rwa [he] at h
  have hcoef : 4*(1+sourceFactorialCollar N)*(N : ℝ) ≤ 8*(N : ℝ) := by nlinarith
  have harg : 4*(1+sourceFactorialCollar N)*((N : ℝ)*Real.exp (-u))+1 ≤
      (13*(N : ℝ))*Real.exp (-u) := by
    have h := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-u)).le
    nlinarith
  have hl := Real.log_le_log (by positivity :
    0 < 4*(1+sourceFactorialCollar N)*((N : ℝ)*Real.exp (-u))+1) harg
  rwa [Real.log_mul (by positivity : 13*(N : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp, ← sub_eq_add_neg] at hl

/-- An explicit bound on the actual prime packet, not an assumed discrepancy budget. -/
theorem abs_atomicSource_factorialRamp_le (n : ℕ) {u : ℝ}
    (hlo : -3*sourceFactorialWidth (n+1) ≤ u)
    (hhi : u ≤ Real.log (4*((n+1 : ℕ) : ℝ)+1)) :
    |atomicSource (factorialRampSource n) (10*(n+1)) u| ≤
      19*Real.exp (u/2)/Real.sqrt (n+1 : ℕ) *
        (1+Real.log (13*((n+1 : ℕ) : ℝ))-u) := by
  let N := n+1
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hc := factorial_packet_collar_bounds hN hlo
  have hv : 0 < (N : ℝ)*Real.exp (-u) := by positivity
  have hcap : (N : ℝ)*Real.exp (-u) ≤ 2*(N : ℝ) := by nlinarith [hc.1]
  have hM : (1+sourceFactorialCollar N)*(4*((N : ℝ)*Real.exp (-u))) ≤
      ((10*N+2 : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hc.2.1 (by positivity : 0 ≤ 4*(N : ℝ))
    push_cast
    nlinarith
  have hw : sourceFactorialCollar N*(4*((N : ℝ)*Real.exp (-u))) ≤ 2 := by
    nlinarith [hc.2.2]
  have hs := clamped_stencil_bound (sourceFactorialCollar_pos hN) hv hcap hM hw
  have hl := factorial_packet_log_bound hN hhi
  have he : 0 ≤ Real.exp (u/2)/Real.sqrt (N : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs he
  rw [atomicSource_factorialRamp_eq, abs_mul, abs_of_nonneg he]
  change Real.exp (u/2)/Real.sqrt (N : ℝ) *
      |clampedPrimeFactorialSum (sourceFactorialCollar N) (4*N) (10*N+2)
          (4*(N : ℝ)*Real.exp (-u))-
        4*clampedPrimeFactorialSum (sourceFactorialCollar N) (2*N) (10*N+2)
          (2*(N : ℝ)*Real.exp (-u))+
        4*clampedPrimeFactorialSum (sourceFactorialCollar N) N (10*N+2)
          ((N : ℝ)*Real.exp (-u))| ≤ _
  have heq4 : 4*((N : ℝ)*Real.exp (-u)) = 4*(N : ℝ)*Real.exp (-u) := by ring
  have heq2 : 2*((N : ℝ)*Real.exp (-u)) = 2*(N : ℝ)*Real.exp (-u) := by ring
  rw [heq4, heq2] at hh
  calc
    _ ≤ _ := hh
    _ ≤ (Real.exp (u/2)/Real.sqrt (N : ℝ)) *
        (19*(1+Real.log (13*(N : ℝ))-u)) :=
      mul_le_mul_of_nonneg_left (by linarith) he
    _ = _ := by ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
