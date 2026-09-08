import GaloisForLFunctions.HTGeometry.HypergeometricParameterBounds

/-! A single summable majorant for all Gauss coefficients in a pole-separated parameter neighborhood. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A finite prefix absorbs all possible small denominators; the remaining tail has a positive Gauss majorant. -/
theorem hypergeometricCoefficient_tail_bound {a b c : ℂ} {B δ : ℝ} (hB : 0 < B)
    (hδ : 0 < δ) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (hsep : ∀ j : ℕ, δ ≤ ‖c+j‖) (N : ℕ) (hN : B+1 ≤ N) (m : ℕ) :
    ‖ordinaryHypergeometricCoefficient a b c (N+m)‖ ≤
      ((ascPochhammer ℝ N).eval B)^2/δ^N * positiveGaussCoefficient (B+N) m := by
  have hcN : 1 ≤ (c+(N : ℂ)).re := by
    have hh := (neg_le_of_abs_le ((Complex.abs_re_le_norm c).trans hc))
    simp only [Complex.add_re,Complex.natCast_re]
    linarith
  have hl : δ^N*(m.factorial : ℝ) ≤ ‖(ascPochhammer ℂ (N+m)).eval c‖ := by
    rw [pochhammer_eval_add,norm_mul]
    exact mul_le_mul (pochhammer_norm_lower hδ hsep N) (pochhammer_norm_factorial hcN m)
      (Nat.cast_nonneg _) (norm_nonneg _)
  have hf : (m.factorial : ℝ) ≤ ((N+m).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show m ≤ N+m by omega)
  have hd : δ^N*(m.factorial : ℝ)^2 ≤
      ((N+m).factorial : ℝ)*‖(ascPochhammer ℂ (N+m)).eval c‖ := by
    have hh := mul_le_mul hf hl (by positivity : (0 : ℝ) ≤ δ^N*(m.factorial : ℝ)) (Nat.cast_nonneg _)
    nlinarith
  have hu : ‖(ascPochhammer ℂ (N+m)).eval a‖*‖(ascPochhammer ℂ (N+m)).eval b‖ ≤
      ((ascPochhammer ℝ N).eval B)^2*((ascPochhammer ℝ m).eval (B+N))^2 := by
    have hh := mul_le_mul (pochhammer_norm_le hB ha (N+m)) (pochhammer_norm_le hB hb (N+m))
      (norm_nonneg _) (ascPochhammer_pos (N+m) B hB).le
    rw [pochhammer_eval_add (K := ℝ) B N m] at hh
    nlinarith
  rw [hypergeometricCoefficient_norm]
  calc
    _ ≤ (((ascPochhammer ℝ N).eval B)^2*((ascPochhammer ℝ m).eval (B+N))^2)/
        (((N+m).factorial : ℝ)*‖(ascPochhammer ℂ (N+m)).eval c‖) :=
      div_le_div_of_nonneg_right hu (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    _ ≤ (((ascPochhammer ℝ N).eval B)^2*((ascPochhammer ℝ m).eval (B+N))^2)/
        (δ^N*(m.factorial : ℝ)^2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = _ := by rw [positiveGaussCoefficient_eq]; ring

def gaussParameterMajorant (B δ : ℝ) (N n : ℕ) : ℝ :=
  if n < N then ((ascPochhammer ℝ n).eval B)^2/((n.factorial : ℝ)*δ^n)
  else ((ascPochhammer ℝ N).eval B)^2/δ^N * positiveGaussCoefficient (B+N) (n-N)

theorem gaussParameterMajorant_bound {a b c : ℂ} {B δ : ℝ} (hB : 0 < B)
    (hδ : 0 < δ) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (hsep : ∀ j : ℕ, δ ≤ ‖c+j‖) (N : ℕ) (hN : B+1 ≤ N) (n : ℕ) :
    ‖ordinaryHypergeometricCoefficient a b c n‖ ≤ gaussParameterMajorant B δ N n := by
  by_cases hn : n < N
  · rw [gaussParameterMajorant,if_pos hn,hypergeometricCoefficient_norm]
    have hu : ‖(ascPochhammer ℂ n).eval a‖*‖(ascPochhammer ℂ n).eval b‖ ≤
        ((ascPochhammer ℝ n).eval B)^2 := by
      simpa only [pow_two] using mul_le_mul (pochhammer_norm_le hB ha n) (pochhammer_norm_le hB hb n)
        (norm_nonneg _) (ascPochhammer_pos n B hB).le
    have hd := mul_le_mul_of_nonneg_left (pochhammer_norm_lower hδ hsep n) (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ n.factorial)
    exact (div_le_div_of_nonneg_right hu (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hd)
  · rw [gaussParameterMajorant,if_neg hn]
    have hh := hypergeometricCoefficient_tail_bound hB hδ ha hb hc hsep N hN (n-N)
    simpa only [Nat.add_sub_of_le (by omega : N ≤ n)] using hh

/-- The uniform coefficient bound is summable throughout every strict interior spatial disk. -/
theorem gaussParameterMajorant_summable {B δ r : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) : Summable (fun n => gaussParameterMajorant B δ N n*r^n) := by
  apply (summable_nat_add_iff N).mp
  have hs := (positiveGaussCoefficient_summable (by positivity : 0 < B+N) hr hr1).mul_left
    ((((ascPochhammer ℝ N).eval B)^2/δ^N)*r^N)
  apply hs.congr
  intro n
  simp only [gaussParameterMajorant,show ¬ n+N < N by omega,if_false,Nat.add_sub_cancel,pow_add]
  ring

end
end GaloisForLFunctions.HTGeometry
