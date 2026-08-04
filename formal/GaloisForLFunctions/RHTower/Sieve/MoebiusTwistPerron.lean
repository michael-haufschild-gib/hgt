import GaloisForLFunctions.RHTower.Sieve.MoebiusPerron

/-!
# The twisted Möbius sum under the Perron formula

The smoothed Perron formula holds for every coefficient sequence of modulus at most one, and the
`1/ζ` bound it is paired with is uniform in the height of the line.  Both facts survive the twist
`μ(n) ↦ μ(n)·n^{-iτ}`: the twisted coefficients still have modulus at most one, their Dirichlet
series is the same one evaluated at `s + iτ`, and the uniform bound does not see the shift.  Hence

`‖∑' μ(n)n^{-iτ}·w(n)‖ ≤ e^{11/2}(1 + 1/(σ−1))·∫‖mellin w(σ+iy)‖ dy / 2π`

with the *same* constant for every twist `τ`.  The twisted sum is what a frequency average of the
Möbius function is built from, and this is its Perron side.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The Möbius function twisted by the character `n ↦ n^{-iτ}`. -/
noncomputable def moebiusTwist (τ : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))

@[simp] theorem moebiusTwist_zero (τ : ℝ) : moebiusTwist τ 0 = 0 := by
  simp [moebiusTwist]

/-- The twist does not change the modulus: the twisted coefficients are still bounded by one. -/
theorem norm_moebiusTwist_le_one (τ : ℝ) (n : ℕ) : ‖moebiusTwist τ n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    have h1 : ‖((n : ℕ) : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ = 1 := by
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp
    rw [moebiusTwist, norm_mul, h1, mul_one, ← Complex.ofReal_intCast, Complex.norm_real,
      Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- The Dirichlet series of the twisted Möbius function is the untwisted one, shifted. -/
theorem tsum_moebiusTwist_cpow (τ : ℝ) (s : ℂ) :
    (∑' n : ℕ, moebiusTwist τ n * (n : ℂ) ^ (-s))
      = LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (s + (τ : ℂ) * Complex.I) := by
  rw [← tsum_cpow_neg_eq_LSeries (a := fun n => (ArithmeticFunction.moebius n : ℂ)) (by simp)
    (s + (τ : ℂ) * Complex.I)]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [moebiusTwist, mul_assoc, ← Complex.cpow_add _ _ hn0,
      show -((τ : ℂ) * Complex.I) + -s = -(s + (τ : ℂ) * Complex.I) by ring]

/-- **The twisted smoothed Möbius sum, bounded uniformly in the twist.**  The Perron formula against
the uniform `1/ζ` bound, which does not see the vertical shift. -/
theorem norm_tsum_moebiusTwist_smoothWeight_le {N H σ : ℝ} (hN : 0 < N) (hH : 0 < H) (hσ : 1 < σ)
    (τ : ℝ) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1))
          * ∫ y : ℝ, ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((σ : ℂ) + (y : ℝ) * Complex.I)‖ := by
  have hperron := tsum_mul_smoothWeight_eq_integral (a := moebiusTwist τ)
    (norm_moebiusTwist_le_one τ) (moebiusTwist_zero τ) hN hH hσ
  rw [hperron]
  have hpt : ∀ y : ℝ,
      ‖(∑' n : ℕ, moebiusTwist τ n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I)))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1))
          * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((σ : ℂ) + (y : ℝ) * Complex.I)‖ := by
    intro y
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [tsum_moebiusTwist_cpow,
      show (σ : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I
        = (σ : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact norm_LSeries_moebius_le_uniform hσ
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hInt : Integrable (fun y : ℝ =>
      Real.exp (22 / 4) * (1 + 1 / (σ - 1))
        * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I)‖) :=
    ((verticalIntegrable_mellin_smoothWeight hN hH (by linarith)).norm).const_mul _
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    hInt (Filter.Eventually.of_forall hpt)) ?_
  rw [integral_const_mul]

end RHTower.Sieve
