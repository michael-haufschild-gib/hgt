import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalSource

/-! An integrable exponential–logarithmic envelope on the factorial source window. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def factorialPacketEnvelope (N : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u/2)/Real.sqrt N * (1+Real.log (13*(N : ℝ))-u)

theorem continuous_factorialPacketEnvelope (N : ℕ) : Continuous (factorialPacketEnvelope N) := by
  unfold factorialPacketEnvelope
  fun_prop

theorem factorialPacketEnvelope_nonneg {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (hu : u ≤ Real.log (4*(N : ℝ)+1)) : 0 ≤ factorialPacketEnvelope N u := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : Real.log (4*(N : ℝ)+1) ≤ Real.log (13*(N : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  unfold factorialPacketEnvelope
  exact mul_nonneg (by positivity) (by linarith)

theorem factorialPacketEnvelope_sq (N : ℕ) (u : ℝ) :
    factorialPacketEnvelope N u ^ 2 =
      Real.exp u/(N : ℝ)*(1+Real.log (13*(N : ℝ))-u)^2 := by
  have he : Real.exp (u/2)^2 = Real.exp u := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold factorialPacketEnvelope
  rw [mul_pow, div_pow, he, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The window grows logarithmically, but the normalized squared envelope has a fixed budget. -/
theorem integral_factorialPacketEnvelope_sq_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ u in Icc (-3*sourceFactorialWidth N) (Real.log (4*(N : ℝ)+1)),
      factorialPacketEnvelope N u ^ 2) ≤ 130 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  let B := 1+Real.log (13*(N : ℝ))
  let L := Real.log (4*(N : ℝ)+1)
  let P : ℝ → ℝ := fun u => Real.exp u/(N : ℝ)*((B-u)^2+2*(B-u)+2)
  have hd (x : ℝ) : HasDerivAt P (Real.exp x/(N : ℝ)*(B-x)^2) x := by
    have hD := (hasDerivAt_id x).const_sub B
    have hQ := ((hD.pow 2).add (hD.const_mul 2)).add_const 2
    convert (((Real.hasDerivAt_exp x).mul hQ).div_const (N : ℝ)) using 1 <;>
      first
      | rfl
      | (funext y; dsimp [P]; ring)
      | (dsimp; ring)
  have hL : 0 ≤ L := Real.log_nonneg (by change 1 ≤ 4*(N : ℝ)+1; linarith)
  have hδ := sourceFactorialWidth_pos hN
  have ha : -3*sourceFactorialWidth N ≤ L := by linarith
  have heq : (∫ u in Icc (-3*sourceFactorialWidth N) L,
      factorialPacketEnvelope N u ^ 2) = P L-P (-3*sourceFactorialWidth N) := by
    simp_rw [factorialPacketEnvelope_sq N]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((show Continuous (fun x => Real.exp x/(N : ℝ)*(B-x)^2) by fun_prop).intervalIntegrable _ _)
  have hP (u : ℝ) : 0 ≤ P u := by
    apply mul_nonneg (by positivity)
    nlinarith [sq_nonneg (B-u+1)]
  have hden : 0 < 4*(N : ℝ)+1 := by positivity
  have hr0 : 0 < 13*(N : ℝ)/(4*(N : ℝ)+1) := by positivity
  have hr1 : 1 ≤ 13*(N : ℝ)/(4*(N : ℝ)+1) := by
    apply (le_div_iff₀ hden).2
    linarith
  have hr4 : 13*(N : ℝ)/(4*(N : ℝ)+1) ≤ 4 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hD : B-L = 1+Real.log (13*(N : ℝ)/(4*(N : ℝ)+1)) := by
    rw [Real.log_div (by positivity : 13*(N : ℝ) ≠ 0) hden.ne']
    dsimp [B, L]
    ring
  have hD0 : 0 ≤ B-L := by rw [hD]; linarith [Real.log_nonneg hr1]
  have hD4 : B-L ≤ 4 := by rw [hD]; linarith [Real.log_le_sub_one_of_pos hr0]
  have hQ : (B-L)^2+2*(B-L)+2 ≤ 26 := by nlinarith
  have hQ0 : 0 ≤ (B-L)^2+2*(B-L)+2 := by positivity
  have hrN : (4*(N : ℝ)+1)/(N : ℝ) ≤ 5 := by
    apply (div_le_iff₀ hn0).2
    linarith
  have hPL : P L ≤ 130 := by
    calc
      _ = ((4*(N : ℝ)+1)/(N : ℝ))*((B-L)^2+2*(B-L)+2) := by
        dsimp only [P]
        rw [show Real.exp L = 4*(N : ℝ)+1 by exact Real.exp_log hden]
      _ ≤ 5*26 := mul_le_mul hrN hQ hQ0 (by norm_num)
      _ = 130 := by norm_num
  change (∫ u in Icc (-3*sourceFactorialWidth N) L, factorialPacketEnvelope N u^2) ≤ 130
  rw [heq]
  linarith [hP (-3*sourceFactorialWidth N)]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
