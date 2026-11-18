import GaloisForLFunctions.RHTower.HurwitzZetaSmallShift
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# The symbol of the last quotient class

The successive jumps of the last residue class are a positive jump at
`-1 mod q` and a negative jump at `0 mod q`. Their rescaled Dirichlet
symbol is a difference quotient of Hurwitz zeta in the shift variable.
It tends to `s ζ(s+1)`, nonzero in the open right half-plane.
-/

noncomputable section

open Complex Finset Filter Topology HurwitzZeta

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Successive jumps of the last class modulo `q`. -/
def lastClassJumps {q : ℕ} (a : ZMod q) : ℂ :=
  (if a = -1 then 1 else 0) - (if a = 0 then 1 else 0)

/-- Dirichlet symbol of the last quotient class, expressed through a Hurwitz difference. -/
def lastQuotientClassSymbol (q : ℕ) (s : ℂ) : ℂ :=
  (q:ℂ)^(-s) * (hurwitzZeta ((-(1/(q:ℝ)) : ℝ) : UnitAddCircle) s - riemannZeta s)

private theorem symbol_eq_modLFunction (q : ℕ) [NeZero q] :
    lastQuotientClassSymbol q = ZMod.LFunction (lastClassJumps (q := q)) := by
  funext s
  have hshift : ZMod.toAddCircle (-1 : ZMod q) = ((-(1/(q:ℝ)) : ℝ) : UnitAddCircle) := by
    simpa only [Int.cast_neg,Int.cast_one,neg_div] using ZMod.toAddCircle_intCast (N := q) (-1)
  simp [lastQuotientClassSymbol,ZMod.LFunction,lastClassJumps,sub_mul,ite_mul,sum_sub_distrib,
    hshift,hurwitzZeta_zero]

theorem differentiable_lastQuotientClassSymbol (q : ℕ) [NeZero q] :
    Differentiable ℂ (lastQuotientClassSymbol q) := by
  rw [symbol_eq_modLFunction]
  exact ZMod.differentiable_LFunction_of_sum_zero (by simp [lastClassJumps,sum_sub_distrib])

theorem lastQuotientClassSymbol_eq_LSeries (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    lastQuotientClassSymbol q s = LSeries (fun n : ℕ => lastClassJumps (n : ZMod q)) s := by
  rw [symbol_eq_modLFunction,ZMod.LFunction_eq_LSeries _ hs]

/-- Uniform first-order expansion in the inverse modulus for each fixed frequency. -/
theorem lastQuotientClassSymbol_scaled_error {s : ℂ} (hs : 0 < s.re) :
    ∃ C : ℝ, ∀ q : ℕ, 2 ≤ q →
      ‖(q:ℂ)^(s+1) * lastQuotientClassSymbol q s - s * riemannZeta (s+1)‖ ≤ C/q := by
  let C := (‖s‖ * (‖s+1‖ * 2^(s.re+2))) * (∑' n : ℕ, ((n:ℝ)+1)^(-s.re-2))
  refine ⟨C,fun q hq => ?_⟩
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hp : 0 < (q:ℝ) := by linarith only [hqR]
  have hc : (q:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  let t := 1/(q:ℝ)
  have ht : 0 < t := one_div_pos.mpr hp
  have hhalf : t ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hqR
  have he := _root_.RHTower.norm_shiftDiffSeries_add_linear_le (b := -t)
    (by rw [abs_neg,abs_of_pos ht]; exact hhalf) hs
  rw [abs_neg,abs_of_pos ht] at he
  rw [lastQuotientClassSymbol,← mul_assoc,← Complex.cpow_add _ _ hc,
    show s+1+-s = 1 by ring,Complex.cpow_one,_root_.RHTower.hurwitzZeta_neg_sub_riemannZeta_eq ht hhalf hs]
  let A := _root_.RHTower.shiftDiffSeries (-t) s
  have hm : (q:ℂ)*A-s*riemannZeta (s+1) =
      (q:ℂ)*(A + (s*((-t:ℝ):ℂ))*riemannZeta (s+1)) := by
    dsimp only [t]
    push_cast
    field_simp [hc]
    ring
  change ‖(q:ℂ)*A - s*riemannZeta (s+1)‖ ≤ _
  rw [hm,norm_mul,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left he hp.le).trans_eq (by
    change (q:ℝ)*(C*(1/(q:ℝ))^2) = C/q
    field_simp [hp.ne'])

/-- Every fixed frequency of positive real part is seen at every sufficiently large modulus. -/
theorem eventually_lastQuotientClassSymbol_ne_zero {s : ℂ} (hs : 0 < s.re) :
    ∀ᶠ q : ℕ in atTop, lastQuotientClassSymbol q s ≠ 0 := by
  have hsn : s ≠ 0 := fun h => by simp [h] at hs
  have hzn := riemannZeta_ne_zero_of_one_lt_re (show 1 < (s+1).re by simpa using hs)
  let A := ‖s*riemannZeta (s+1)‖
  have hA : 0 < A := norm_pos_iff.mpr (mul_ne_zero hsn hzn)
  obtain ⟨C,h⟩ := lastQuotientClassSymbol_scaled_error hs
  obtain ⟨B,hB⟩ := exists_nat_gt (C/A)
  filter_upwards [eventually_ge_atTop B,eventually_ge_atTop 2] with q hq h2
  have hg := h q h2
  intro hz
  rw [hz,mul_zero,zero_sub,norm_neg] at hg
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hBq : (B:ℝ) ≤ q := by exact_mod_cast hq
  have hbig := (div_lt_iff₀ hA).mp (hB.trans_le hBq)
  change A ≤ C/(q:ℝ) at hg
  rw [mul_comm] at hbig
  exact (not_lt_of_ge ((le_div_iff₀ hq0).mp hg)) hbig

/-- The first derivative in the shift still detects every frequency on the dyadic subsequence. -/
theorem eventually_dyadicQuotientSymbol_ne_zero {s : ℂ} (hs : 0 < s.re) :
    ∀ᶠ j : ℕ in atTop, lastQuotientClassSymbol (2^(j+1)) s ≠ 0 := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp (eventually_lastQuotientClassSymbol_ne_zero hs)
  filter_upwards [eventually_ge_atTop Q] with j hj
  exact hQ _ (hj.trans (by have := Nat.lt_two_pow_self (n := j+1); omega))

#print axioms lastQuotientClassSymbol_eq_LSeries
#print axioms lastQuotientClassSymbol_scaled_error
#print axioms eventually_dyadicQuotientSymbol_ne_zero

end GaloisForLFunctions.ExceptionalLayerTheory
