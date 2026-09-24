import GaloisForLFunctions.RHTower.Sieve.DirichletMVTWindow

/-!
# The mean-square floor of a normalized detector

A detector Dirichlet polynomial whose first coefficient is `1` has coefficient energy at least `1`,
so the mean value theorem forces its window mean square to be at least the window length minus the
mean-value error.  Normalized by the window length the mean square is therefore at least `1 - ε`
once the window is long compared with the error, and `log` of the normalized mean square is at least
`log (1 - ε)`.

This is a floor, not an estimate: no choice of mollifier can push the normalized mean square of a
detector with leading coefficient `1` below `1`.  In the off-line displacement chain the mean square
enters through `(T₂ - T₁)/2 · log (Msq / (T₂ - T₁))`, so that term is bounded below by
`(T₂ - T₁)/2 · log (1 - ε)` and can never supply the negativity needed to force the
multiplicity-weighted horizontal displacement to vanish.
-/

open Finset MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-- A normalized coefficient family has energy at least one. -/
theorem one_le_coeff_energy {N : ℕ} (hN : 0 < N) (a : Fin N → ℂ) (ha : a ⟨0, hN⟩ = 1) :
    (1 : ℝ) ≤ ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  have hterm : ‖a (⟨0, hN⟩ : Fin N)‖ ^ (2 : ℕ) = 1 := by
    rw [ha]
    simp
  calc (1 : ℝ) = ‖a (⟨0, hN⟩ : Fin N)‖ ^ (2 : ℕ) := hterm.symm
    _ ≤ ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun m : Fin N => ‖a m‖ ^ (2 : ℕ))
          (fun m _ => by positivity) (Finset.mem_univ _)

/-- **The mean-square floor.**  A detector with leading coefficient `1` has window mean square at
least the window length minus the mean-value error. -/
theorem dirPoly_meanSquare_floor {N : ℕ} (hN : 0 < N) (a : Fin N → ℂ) (ha : a ⟨0, hN⟩ = 1)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (T₂ - T₁) - 8 * (N : ℝ) * (1 + Real.log N)
      ≤ ∫ t in T₁..T₂, ‖Sieve.dirPoly N a t‖ ^ (2 : ℕ) := by
  have hS1 : (1 : ℝ) ≤ ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := one_le_coeff_energy hN a ha
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hC : 0 ≤ 8 * (N : ℝ) * (1 + Real.log N) := by positivity
  have hmvt := Sieve.dirichlet_meanValue_window N a T₁ T₂
  have hlow : (T₂ - T₁) * (∑ m : Fin N, ‖a m‖ ^ (2 : ℕ))
        - 8 * (N : ℝ) * (1 + Real.log N) * (∑ m : Fin N, ‖a m‖ ^ (2 : ℕ))
      ≤ ∫ t in T₁..T₂, ‖Sieve.dirPoly N a t‖ ^ (2 : ℕ) := by
    have habs := abs_le.mp hmvt
    linarith [habs.1]
  have hnonneg : 0 ≤ ∫ t in T₁..T₂, ‖Sieve.dirPoly N a t‖ ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg hT (fun t _ => by positivity)
  rcases le_or_gt (8 * (N : ℝ) * (1 + Real.log N)) (T₂ - T₁) with hcase | hcase
  · have hfac : (T₂ - T₁) - 8 * (N : ℝ) * (1 + Real.log N)
        ≤ ((T₂ - T₁) - 8 * (N : ℝ) * (1 + Real.log N)) * (∑ m : Fin N, ‖a m‖ ^ (2 : ℕ)) := by
      nlinarith [hS1, hcase]
    nlinarith [hlow, hfac]
  · linarith [hnonneg, hcase]

/-- The normalized mean square is at least `1 - ε` on a window long compared with the
mean-value error. -/
theorem one_sub_mul_le_dirPoly_meanSquare {N : ℕ} (hN : 0 < N) (a : Fin N → ℂ)
    (ha : a ⟨0, hN⟩ = 1) {ε T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hwin : 8 * (N : ℝ) * (1 + Real.log N) ≤ ε * (T₂ - T₁)) :
    (1 - ε) * (T₂ - T₁) ≤ ∫ t in T₁..T₂, ‖Sieve.dirPoly N a t‖ ^ (2 : ℕ) := by
  have h := dirPoly_meanSquare_floor hN a ha hT
  nlinarith [h, hwin]

/-- **The logarithmic floor.**  The logarithm of the normalized mean square is at least
`log (1 - ε)`; it never becomes a useful negative quantity. -/
theorem log_one_sub_le_log_dirPoly_meanSquare_div {N : ℕ} (hN : 0 < N) (a : Fin N → ℂ)
    (ha : a ⟨0, hN⟩ = 1) {ε T₁ T₂ : ℝ} (hT : T₁ < T₂) (hε1 : ε < 1)
    (hwin : 8 * (N : ℝ) * (1 + Real.log N) ≤ ε * (T₂ - T₁)) :
    Real.log (1 - ε)
      ≤ Real.log ((∫ t in T₁..T₂, ‖Sieve.dirPoly N a t‖ ^ (2 : ℕ)) / (T₂ - T₁)) := by
  have hD : 0 < T₂ - T₁ := by linarith
  have h := one_sub_mul_le_dirPoly_meanSquare hN a ha hT.le hwin
  have hdiv : 1 - ε ≤ (∫ t in T₁..T₂, ‖Sieve.dirPoly N a t‖ ^ (2 : ℕ)) / (T₂ - T₁) := by
    rw [le_div_iff₀ hD]
    linarith
  exact Real.log_le_log (by linarith) hdiv

end

end RHTower
