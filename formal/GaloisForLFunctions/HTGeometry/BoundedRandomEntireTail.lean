import GaloisForLFunctions.HTGeometry.BoundedRandomEntireStructure

/-!
# The tail of the bounded random entire series

Beyond any index the clamped series is a monomial factor times another clamped series, whose
coefficients obey the same factorial bound.  The tail is therefore entire and depends only on the
shifted coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The shifted coefficients of the tail. -/
def randomTailCoeff (N : ℕ) (y : ℕ → ℂ) (n : ℕ) : ℂ :=
  clampComplexSquare (y n) / ((4 : ℂ) * ((Nat.factorial (n + N) : ℕ) : ℂ))

theorem norm_randomTailCoeff_le (N : ℕ) (y : ℕ → ℂ) (n : ℕ) :
    ‖randomTailCoeff N y n‖ ≤ 1 / ((Nat.factorial n : ℕ) : ℝ) := by
  have hfac : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by positivity
  have hfacN : (0 : ℝ) < ((Nat.factorial (n + N) : ℕ) : ℝ) := by positivity
  have hle : ((Nat.factorial n : ℕ) : ℝ) ≤ ((Nat.factorial (n + N) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right n N)
  rw [randomTailCoeff, norm_div, norm_mul, Complex.norm_natCast, show ‖(4 : ℂ)‖ = 4 by norm_num]
  rw [div_le_div_iff₀ (by positivity) hfac]
  have hc := norm_clampComplexSquare_le_four (y n)
  nlinarith [norm_nonneg (clampComplexSquare (y n))]

theorem randomTailCoeff_orderTwo (N : ℕ) (y : ℕ → ℂ) :
    ∀ R : ℝ, 0 < R → ∀ n, ‖randomTailCoeff N y n‖ ≤ Real.exp (R ^ (2 : ℕ) * 2 / 2) / R ^ n :=
  orderTwo_bound_of_factorial_bound (norm_randomTailCoeff_le N y)

theorem boundedRandomEntireTail_eq (N : ℕ) (y : ℕ → ℂ) (z : ℂ) :
    boundedRandomEntireTail N y z = z ^ N * entireOfCoeffs (randomTailCoeff N y) z := by
  rw [boundedRandomEntireTail, entireOfCoeffs, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [randomTailCoeff, pow_add]
  ring

theorem differentiable_boundedRandomEntireTail (N : ℕ) (y : ℕ → ℂ) :
    Differentiable ℂ (boundedRandomEntireTail N y) := by
  have heq : boundedRandomEntireTail N y
      = fun z => z ^ N * entireOfCoeffs (randomTailCoeff N y) z :=
    funext (boundedRandomEntireTail_eq N y)
  rw [heq]
  exact (differentiable_pow N).mul (differentiable_entireOfCoeffs (randomTailCoeff_orderTwo N y))

theorem summable_randomTailCoeff_term (L : ℕ) (y : ℕ → ℂ) (z : ℂ) :
    Summable (fun n : ℕ => randomTailCoeff L y n * z ^ (n + L)) := by
  have hbase : Summable (fun n : ℕ => randomTailCoeff L y n * z ^ n) :=
    summable_of_orderTwo_bound (randomTailCoeff_orderTwo L y) z
  have := hbase.mul_left (z ^ L)
  refine this.congr fun n => ?_
  rw [pow_add]
  ring

/-- The tail splits again at every further index. -/
theorem boundedRandomEntireTail_split (N L : ℕ) (y : ℕ → ℂ) (z : ℂ) :
    boundedRandomEntireTail L y z
      = (∑ n ∈ Finset.range N, randomTailCoeff L y n * z ^ (n + L))
        + boundedRandomEntireTail (N + L) (fun k => y (k + N)) z := by
  have hsum := summable_randomTailCoeff_term L y z
  have hsplit := (hsum.sum_add_tsum_nat_add N).symm
  have hL : boundedRandomEntireTail L y z = ∑' n : ℕ, randomTailCoeff L y n * z ^ (n + L) := rfl
  have hR : boundedRandomEntireTail (N + L) (fun k => y (k + N)) z
      = ∑' n : ℕ, randomTailCoeff L y (n + N) * z ^ (n + N + L) := by
    rw [boundedRandomEntireTail]
    refine tsum_congr fun n => ?_
    rw [randomTailCoeff, show n + (N + L) = n + N + L by omega]
  rw [hL, hR, hsplit]

end

end GaloisForLFunctions.HTGeometry
