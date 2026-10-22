import GaloisForLFunctions.RHTower.Deninger.DeningerHarmonicPartial
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelSummation

/-!
# The Möbius Dirichlet series is an Abel average

Abel summation applied to `∑ μ(n) n^{-1-σ}` moves the weight onto the harmonic partial sums.  The
boundary term vanishes, and the `n = 0` increment is killed by `μ(0) = 0`, so what remains is
exactly the Abel average of the partial sums against the increments `(m+1)^{-σ} - (m+2)^{-σ}`.

`∑_n μ(n) n^{-1-σ} = ∑_m A_{m+1} w_σ(m)`

Together with the Abelian limit theorem this identifies `lim_{σ ↓ 0} 1/ζ(1+σ)` with `∑ μ(n)/n`.

* `deningerMobiusDirichlet_summable` : the Dirichlet series converges absolutely.
* `deningerMobiusDirichlet_eq_abel` : **the Dirichlet series is the Abel average.**
-/

namespace RHTower

open ArithmeticFunction Filter Topology

noncomputable section

/-- The Dirichlet term `μ(n) n^{-1-σ}`, written as a harmonic coefficient times a weight. -/
def deningerDirichletTerm (σ : ℝ) (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ) / (n : ℝ) * ((n : ℝ) ^ (-σ))

theorem deningerDirichletTerm_zero (σ : ℝ) : deningerDirichletTerm σ 0 = 0 := by
  rw [deningerDirichletTerm]
  simp

/-- The Dirichlet series converges absolutely for every positive exponent. -/
theorem deningerMobiusDirichlet_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (deningerDirichletTerm σ) := by
  have hp : Summable fun n : ℕ => (((n : ℝ) ^ (1 + σ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine Summable.of_norm_bounded hp fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [deningerDirichletTerm_zero, norm_zero]
    positivity
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      rcases moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num
    rw [deningerDirichletTerm, Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (Real.rpow_pos_of_pos hnr _), abs_of_pos hnr]
    have hsplit : ((n : ℝ) ^ (1 + σ))⁻¹ = (n : ℝ)⁻¹ * ((n : ℝ) ^ (-σ)) := by
      rw [Real.rpow_add hnr, Real.rpow_one, Real.rpow_neg hnr.le, mul_inv]
    rw [hsplit]
    have hstep : |((moebius n : ℤ) : ℝ)| / (n : ℝ) ≤ (n : ℝ)⁻¹ := by
      rw [div_le_iff₀ hnr, inv_mul_cancel₀ (ne_of_gt hnr)]
      exact hmu
    calc |((moebius n : ℤ) : ℝ)| / (n : ℝ) * ((n : ℝ) ^ (-σ))
        ≤ (n : ℝ)⁻¹ * ((n : ℝ) ^ (-σ)) :=
          mul_le_mul_of_nonneg_right hstep (Real.rpow_pos_of_pos hnr _).le
      _ = (n : ℝ)⁻¹ * ((n : ℝ) ^ (-σ)) := rfl

/-- The harmonic partial sums are exactly the partial sums of the harmonic coefficients. -/
theorem deningerHarmonicPartial_eq (N : ℕ) :
    deningerPartialSum (fun n : ℕ => ((moebius n : ℤ) : ℝ) / (n : ℝ)) N
      = deningerHarmonicPartial N := rfl

/-- **Abel summation for the Dirichlet series.**  The `n = 0` increment is killed by `μ(0) = 0`, so
the remaining sum is the Abel average of the shifted partial sums. -/
theorem deningerDirichlet_abelSum {σ : ℝ} (N : ℕ) :
    (∑ n ∈ Finset.range (N + 2), deningerDirichletTerm σ n)
      = deningerHarmonicPartial (N + 1) * (((N : ℝ) + 1) ^ (-σ))
        + ∑ m ∈ Finset.range N, deningerHarmonicPartial (m + 1) * deningerAbelWeight σ m := by
  have habel := deningerAbelSummation
    (fun n : ℕ => ((moebius n : ℤ) : ℝ) / (n : ℝ)) (fun n : ℕ => ((n : ℝ) ^ (-σ))) (N + 1)
  have hterm : ∀ n : ℕ, ((moebius n : ℤ) : ℝ) / (n : ℝ) * ((n : ℝ) ^ (-σ))
      = deningerDirichletTerm σ n := fun n => rfl
  rw [Finset.sum_congr rfl (fun n _ => hterm n)] at habel
  rw [habel, deningerHarmonicPartial_eq]
  have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  congr 1
  rw [Finset.sum_range_succ']
  have hzero : deningerPartialSum (fun n : ℕ => ((moebius n : ℤ) : ℝ) / (n : ℝ)) 0 *
      (((0 : ℕ) : ℝ) ^ (-σ) - ((0 + 1 : ℕ) : ℝ) ^ (-σ)) = 0 := by
    rw [deningerPartialSum_zero]
    simp
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [deningerHarmonicPartial_eq, deningerAbelWeight]
  congr 2 <;> push_cast <;> ring

end

end RHTower
