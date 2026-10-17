import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialAtomicPacket
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRampMoments

/-! Partial polar moments of the actual factorial ramp.
The positive branch uses its full harmonic cancellation before estimating its head. -/

open MeasureTheory Set
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem factorialRampSource_zero_of_nonpos (n : ℕ) {u : ℝ} (hu : u ≤ 0) :
    factorialRampSource n u = 0 := sourceFactorialRamp_zero_of_nonpos (by omega) hu

theorem factorialRampSource_tail (n : ℕ) {u : ℝ}
    (hu : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ u) : factorialRampSource n u = 0 :=
  rampBiNull_tail (sourceFactorialCollar_pos (by omega : 1 ≤ n+1)) (by omega)
    (sourceFactorialCollar_budget (by omega)) hu

theorem factorial_packet_cutoff {N K : ℕ} (hN : 1 ≤ N) (hK : 10*N ≤ K) :
    Real.log (4*(N : ℝ)+1)+3*sourceFactorialWidth N ≤ cutoff K := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : 10*(N : ℝ) ≤ K := by exact_mod_cast hK
  have he := (factorial_packet_collar_bounds hN (u := -3*sourceFactorialWidth N) le_rfl).1
  rw [show -(-3*sourceFactorialWidth N) = 3*sourceFactorialWidth N by ring] at he
  have hx : Real.exp (Real.log (4*(N : ℝ)+1)+3*sourceFactorialWidth N) ≤ (K+2 : ℕ) := by
    rw [Real.exp_add, Real.exp_log (by positivity : 0 < 4*(N : ℝ)+1)]
    have h := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4*(N : ℝ)+1)
    push_cast
    nlinarith
  have h := Real.log_le_log (Real.exp_pos _) hx
  rwa [Real.log_exp] at h

theorem factorialRamp_integral_eq_interval (n : ℕ) (w : ℝ → ℝ) :
    (∫ x, w x*factorialRampSource n x) =
      ∫ x in (0 : ℝ)..Real.log (4*((n+1 : ℕ) : ℝ)+1), w x*factorialRampSource n x := by
  have hL : 0 ≤ Real.log (4*((n+1 : ℕ) : ℝ)+1) := Real.log_nonneg (by
    have hn : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _
    linarith)
  rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_cases hx0 : x ≤ 0
  · rw [factorialRampSource_zero_of_nonpos n hx0, mul_zero]
  · have hxL : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ x := by
      by_contra! h
      exact hx ⟨by linarith, h.le⟩
    rw [factorialRampSource_tail n hxL, mul_zero]

theorem factorialRamp_full_moments (n : ℕ) :
    |∫ x in (0 : ℝ)..Real.log (4*((n+1 : ℕ) : ℝ)+1),
      Real.exp (x/2)*factorialRampSource n x| ≤ 2/Real.sqrt (n+1 : ℕ) ∧
    |∫ x in (0 : ℝ)..Real.log (4*((n+1 : ℕ) : ℝ)+1),
      Real.exp (-(x/2))*factorialRampSource n x| ≤
        (5*Real.log (4*((n+1 : ℕ) : ℝ)+1)+1)/Real.sqrt (n+1 : ℕ) := by
  rw [← factorialRamp_integral_eq_interval, ← factorialRamp_integral_eq_interval]
  change |∫ x, Real.exp (x/2)*rampBiNull (sourceFactorialCollar (n+1)) (n+1) x| ≤ _ ∧
    |∫ x, Real.exp (-(x/2))*rampBiNull (sourceFactorialCollar (n+1)) (n+1) x| ≤ _
  have hN : 1 ≤ n+1 := by omega
  have hε := sourceFactorialCollar_pos hN
  have hc := harmonicCorrection_bounds hN
  have hb := sourceFactorialCollar_budget hN
  have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hε1 : sourceFactorialCollar (n+1) ≤ 1 := by nlinarith
  rw [integral_exp_half_rampBiNull hε, integral_exp_neg_half_rampBiNull hε hN,
    abs_div, abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
  constructor
  · rw [abs_of_nonneg (mul_nonneg (by positivity) hc.1)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    nlinarith
  · exact div_le_div_of_nonneg_right (abs_chebyshevBiNullProducer_le hN) (Real.sqrt_nonneg _)

theorem factorialRamp_weighted_abs (n : ℕ) (x : ℝ) :
    |Real.exp (x/2)*factorialRampSource n x| ≤ 2*Real.exp x/Real.sqrt (n+1 : ℕ) ∧
    |Real.exp (-(x/2))*factorialRampSource n x| ≤ 2/Real.sqrt (n+1 : ℕ) := by
  have hr : |factorialRampSource n x| ≤ 2*Real.exp (x/2)/Real.sqrt (n+1 : ℕ) :=
    abs_rampBiNull_le (sourceFactorialCollar_pos (by omega : 1 ≤ n+1)) (by omega) x
  have he1 : Real.exp (x/2)*Real.exp (x/2) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-(x/2))*Real.exp (x/2) = 1 := by rw [← Real.exp_add]; simp
  simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
  constructor
  · calc
      _ ≤ Real.exp (x/2)*(2*Real.exp (x/2)/Real.sqrt (n+1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
      _ = 2*(Real.exp (x/2)*Real.exp (x/2))/Real.sqrt (n+1 : ℕ) := by ring
      _ = _ := by rw [he1]
  · calc
      _ ≤ Real.exp (-(x/2))*(2*Real.exp (x/2)/Real.sqrt (n+1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
      _ = 2*(Real.exp (-(x/2))*Real.exp (x/2))/Real.sqrt (n+1 : ℕ) := by ring
      _ = _ := by rw [he2, mul_one]

private theorem factorialRamp_interval_tail (n : ℕ) (w : ℝ → ℝ) (hw : Continuous w)
    (u b : ℝ) (hb : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ b) :
    (∫ x in u..b, w x*factorialRampSource n x) =
      ∫ x in u..Real.log (4*((n+1 : ℕ) : ℝ)+1), w x*factorialRampSource n x := by
  have hc : Continuous (fun x => w x*factorialRampSource n x) :=
    hw.mul (factorialRampSource n).continuous
  have hz : (∫ x in Real.log (4*((n+1 : ℕ) : ℝ)+1)..b,
      w x*factorialRampSource n x) = 0 := by
    calc
      _ = ∫ _x in Real.log (4*((n+1 : ℕ) : ℝ)+1)..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hb] at hx
        change w x*factorialRampSource n x = 0
        rw [factorialRampSource_tail n hx.1, mul_zero]
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable u (Real.log (4*((n+1 : ℕ) : ℝ)+1)))
    (hc.intervalIntegrable (Real.log (4*((n+1 : ℕ) : ℝ)+1)) b)
  rw [hz, add_zero] at h
  exact h.symm

/-- Both polar branches, with the true finite cutoff removed by support. -/
theorem polarSource_factorialRamp_eq (n K : ℕ) {u : ℝ}
    (hcut : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ u+cutoff K) :
    polarSource (factorialRampSource n) K u =
      Real.exp (-(u/2)) *
        (∫ x in u..Real.log (4*((n+1 : ℕ) : ℝ)+1), Real.exp (x/2)*factorialRampSource n x) +
      Real.exp (u/2) *
        (∫ x in u..Real.log (4*((n+1 : ℕ) : ℝ)+1), Real.exp (-(x/2))*factorialRampSource n x) := by
  have hp : Continuous (fun x => Real.exp (x/2)) := by fun_prop
  have hm : Continuous (fun x => Real.exp (-(x/2))) := by fun_prop
  have he (t : ℝ) : polarDensity t*factorialRampSource n (u+t) =
      Real.exp (-(u/2))*(Real.exp ((u+t)/2)*factorialRampSource n (u+t))+
      Real.exp (u/2)*(Real.exp (-((u+t)/2))*factorialRampSource n (u+t)) := by
    have he1 : Real.exp (-(u/2))*Real.exp ((u+t)/2) = Real.exp (t/2) := by
      rw [← Real.exp_add]; congr 1; ring
    have he2 : Real.exp (u/2)*Real.exp (-((u+t)/2)) = Real.exp (-(t/2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← mul_assoc, ← mul_assoc, he1, he2]
    unfold polarDensity
    rw [Real.cosh_eq]
    ring
  change (∫ t in Icc 0 (cutoff K), polarDensity t*factorialRampSource n (u+t)) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (cutoff_nonneg K)]
  simp_rw [he]
  have hcp : Continuous (fun t => Real.exp (-(u/2)) *
      (Real.exp ((u+t)/2)*factorialRampSource n (u+t))) := by fun_prop
  have hcm : Continuous (fun t => Real.exp (u/2) *
      (Real.exp (-((u+t)/2))*factorialRampSource n (u+t))) := by fun_prop
  rw [intervalIntegral.integral_add (hcp.intervalIntegrable _ _) (hcm.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_left (fun x => Real.exp (x/2)*factorialRampSource n x),
    intervalIntegral.integral_comp_add_left (fun x => Real.exp (-(x/2))*factorialRampSource n x),
    add_zero, factorialRamp_interval_tail n _ hp u (u+cutoff K) hcut,
    factorialRamp_interval_tail n _ hm u (u+cutoff K) hcut]

theorem factorialRamp_partial_moments (n : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (huL : u ≤ Real.log (4*((n+1 : ℕ) : ℝ)+1)) :
    |∫ x in u..Real.log (4*((n+1 : ℕ) : ℝ)+1), Real.exp (x/2)*factorialRampSource n x| ≤
        2*Real.exp u/Real.sqrt (n+1 : ℕ) ∧
    |∫ x in u..Real.log (4*((n+1 : ℕ) : ℝ)+1), Real.exp (-(x/2))*factorialRampSource n x| ≤
        2*(Real.log (4*((n+1 : ℕ) : ℝ)+1)-u)/Real.sqrt (n+1 : ℕ) := by
  let L := Real.log (4*((n+1 : ℕ) : ℝ)+1)
  let r := Real.sqrt (n+1 : ℕ)
  have hp : Continuous (fun x => Real.exp (x/2)*factorialRampSource n x) := by fun_prop
  have hm : Continuous (fun x => Real.exp (-(x/2))*factorialRampSource n x) := by fun_prop
  have hhead : |∫ x in (0 : ℝ)..u, Real.exp (x/2)*factorialRampSource n x| ≤
      2*(Real.exp u-1)/r := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..u, |Real.exp (x/2)*factorialRampSource n x| :=
        intervalIntegral.abs_integral_le_integral_abs hu0
      _ ≤ ∫ x in (0 : ℝ)..u, 2*Real.exp x/r :=
        intervalIntegral.integral_mono_on hu0 (hp.abs.intervalIntegrable _ _)
          ((show Continuous (fun x => 2*Real.exp x/r) by fun_prop).intervalIntegrable _ _)
          (fun x _ => (factorialRamp_weighted_abs n x).1)
      _ = _ := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_exp,
          Real.exp_zero]
  constructor
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hp.intervalIntegrable 0 u) (hp.intervalIntegrable u L)
    have heq : (∫ x in u..L, Real.exp (x/2)*factorialRampSource n x) =
        (∫ x in (0 : ℝ)..L, Real.exp (x/2)*factorialRampSource n x)-
        (∫ x in (0 : ℝ)..u, Real.exp (x/2)*factorialRampSource n x) := by linarith
    change |∫ x in u..L, Real.exp (x/2)*factorialRampSource n x| ≤ 2*Real.exp u/r
    rw [heq]
    calc
      _ ≤ |∫ x in (0 : ℝ)..L, Real.exp (x/2)*factorialRampSource n x|+
          |∫ x in (0 : ℝ)..u, Real.exp (x/2)*factorialRampSource n x| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          (∫ x in (0 : ℝ)..L, Real.exp (x/2)*factorialRampSource n x) 0
          (∫ x in (0 : ℝ)..u, Real.exp (x/2)*factorialRampSource n x)
      _ ≤ 2/r+2*(Real.exp u-1)/r := add_le_add (factorialRamp_full_moments n).1 hhead
      _ = _ := by ring
  · calc
      _ ≤ ∫ x in u..L, |Real.exp (-(x/2))*factorialRampSource n x| :=
        intervalIntegral.abs_integral_le_integral_abs huL
      _ ≤ ∫ _x in u..L, 2/r :=
        intervalIntegral.integral_mono_on huL (hm.abs.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun x _ => (factorialRamp_weighted_abs n x).2)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

private theorem factorialRamp_interval_head (n : ℕ) (w : ℝ → ℝ) (hw : Continuous w)
    {u : ℝ} (hu : u ≤ 0) :
    (∫ x in u..Real.log (4*((n+1 : ℕ) : ℝ)+1), w x*factorialRampSource n x) =
      ∫ x in (0 : ℝ)..Real.log (4*((n+1 : ℕ) : ℝ)+1), w x*factorialRampSource n x := by
  have hc : Continuous (fun x => w x*factorialRampSource n x) :=
    hw.mul (factorialRampSource n).continuous
  have hz : (∫ x in u..(0 : ℝ), w x*factorialRampSource n x) = 0 := by
    calc
      _ = ∫ _x in u..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hu] at hx
        change w x*factorialRampSource n x = 0
        rw [factorialRampSource_zero_of_nonpos n hx.2, mul_zero]
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable u 0) (hc.intervalIntegrable 0 (Real.log (4*((n+1 : ℕ) : ℝ)+1)))
  rw [hz, zero_add] at h
  exact h.symm

/-- Full moment cancellation bounds the actual partial polar packet. -/
theorem abs_polarSource_factorialRamp_le (n : ℕ) {u : ℝ}
    (hlo : -3*sourceFactorialWidth (n+1) ≤ u)
    (hhi : u ≤ Real.log (4*((n+1 : ℕ) : ℝ)+1)) :
    |polarSource (factorialRampSource n) (10*(n+1)) u| ≤
      5*Real.exp (u/2)/Real.sqrt (n+1 : ℕ) *
        (1+Real.log (13*((n+1 : ℕ) : ℝ))-u) := by
  let L := Real.log (4*((n+1 : ℕ) : ℝ)+1)
  let B := 1+Real.log (13*((n+1 : ℕ) : ℝ))
  let r := Real.sqrt (n+1 : ℕ)
  let A := Real.exp (u/2)/r
  have hA : 0 ≤ A := by dsimp [A, r]; positivity
  have hL : L+1 ≤ B := by
    have h := Real.log_le_log (by positivity : 0 < 4*((n+1 : ℕ) : ℝ)+1)
      (show 4*((n+1 : ℕ) : ℝ)+1 ≤ 13*((n+1 : ℕ) : ℝ) by
        have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
        linarith)
    dsimp [L, B]
    linarith
  have hBu : 0 ≤ B-u := by change u ≤ L at hhi; linarith
  have hcut := factorial_packet_cutoff (by omega : 1 ≤ n+1) (by omega : 10*(n+1) ≤ 10*(n+1))
  rw [polarSource_factorialRamp_eq n (10*(n+1)) (by linarith)]
  calc
    _ ≤ Real.exp (-(u/2))*
          |∫ x in u..L, Real.exp (x/2)*factorialRampSource n x|+
        Real.exp (u/2)*|∫ x in u..L, Real.exp (-(x/2))*factorialRampSource n x| := by
      simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using abs_add_le
        (Real.exp (-(u/2))*(∫ x in u..L, Real.exp (x/2)*factorialRampSource n x))
        (Real.exp (u/2)*(∫ x in u..L, Real.exp (-(x/2))*factorialRampSource n x))
    _ ≤ 5*A*(B-u) := by
      by_cases hu : 0 ≤ u
      · have hm := factorialRamp_partial_moments n hu hhi
        have h := add_le_add (mul_le_mul_of_nonneg_left hm.1 (Real.exp_pos (-(u/2))).le)
          (mul_le_mul_of_nonneg_left hm.2 (Real.exp_pos (u/2)).le)
        have he : Real.exp (-(u/2))*Real.exp u = Real.exp (u/2) := by
          rw [← Real.exp_add]; congr 1; ring
        have heq : Real.exp (-(u/2))*(2*Real.exp u/r)+Real.exp (u/2)*(2*(L-u)/r) =
            2*A*(1+L-u) := by
          dsimp [A]
          calc
            _ = 2*(Real.exp (-(u/2))*Real.exp u)/r+
                2*(Real.exp (u/2)/r)*(L-u) := by ring
            _ = _ := by rw [he]; ring
        change _ ≤ Real.exp (-(u/2))*(2*Real.exp u/r)+Real.exp (u/2)*(2*(L-u)/r) at h
        rw [heq] at h
        have hmono := mul_le_mul_of_nonneg_left (show 1+L-u ≤ B-u by linarith) hA
        exact h.trans (by nlinarith [mul_nonneg hA hBu])
      · have hu0 : u ≤ 0 := by linarith
        rw [factorialRamp_interval_head n _ (by fun_prop) hu0,
          factorialRamp_interval_head n _ (by fun_prop) hu0]
        have hm := factorialRamp_full_moments n
        have h := add_le_add (mul_le_mul_of_nonneg_left hm.1 (Real.exp_pos (-(u/2))).le)
          (mul_le_mul_of_nonneg_left hm.2 (Real.exp_pos (u/2)).le)
        have he : Real.exp (-(u/2)) = Real.exp (u/2)*Real.exp (-u) := by
          rw [← Real.exp_add]; congr 1; ring
        have heq : Real.exp (-(u/2))*(2/r)+Real.exp (u/2)*((5*L+1)/r) =
            A*(2*Real.exp (-u)+5*L+1) := by rw [he]; dsimp [A]; ring
        change _ ≤ Real.exp (-(u/2))*(2/r)+Real.exp (u/2)*((5*L+1)/r) at h
        rw [heq] at h
        have hc := (factorial_packet_collar_bounds (by omega : 1 ≤ n+1) hlo).1
        calc
          _ ≤ A*(2*Real.exp (-u)+5*L+1) := h
          _ ≤ A*(5*(B-u)) := mul_le_mul_of_nonneg_left (by linarith) hA
          _ = _ := by ring
    _ = _ := by dsimp [A, B, r]; ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
