import GaloisForLFunctions.RHTower.JointAncestryHalfPlaneExistence
import GaloisForLFunctions.RHTower.JointAncestryRouteCapstone

/-!
# A zero-free form of the JAS capstone

The arithmetic Fejér forms `jasArithmeticForm P K τ` are built from `ψ`, the partial sums of
`Λ(n)/n`, `γ`, `log 2π` and the trivial-zero series alone.  Combining them with the chain
exclusion under a half-plane bound and with the abscissa form of half-plane bounds:

`RH ⟺ (every arithmetic Fejér form has nonnegative real part)
        ∧ (∃ θ < 1, Σ (Λ(n) − 1) n^{−σ} converges for every real σ > θ)`

(`riemannHypothesis_iff_arithmetic_and_vonMangoldtMinusOne_abscissa`).  Both conditions involve
only the primes.  The second alone is a zero-free half-plane `Re s > θ`; the first alone is JAS
positivity at `σ = 1`.  Also `RH ⟺ ∃ σ < ½, JasDressedPSD σ` (`riemannHypothesis_iff_exists_lt_half`).
-/

open Complex Filter Topology

namespace RHTower

/-- The arithmetic Fejér forms are JAS positivity at `σ = 1`. -/
theorem jasDressedPSD_one_of_arithmetic
    (h : ∀ (P : Finset Nat.Primes) (K : ℕ) (τ : ℝ), 0 ≤ (jasArithmeticForm P K τ).re) :
    JasDressedPSD 1 := by
  have hpsd := (jasDressedPSD_iff_vertical (by norm_num : (0 : ℝ) < 1 / 2)).mpr fun P τ =>
    re_tsum_prod_jasHoloLocal_nonneg_of_fejer (by norm_num) P _
      (fun i => norm_jasVerticalPoint τ i) fun K => by
        rw [← jasArithmeticForm_eq]
        exact h P K τ
  norm_num at hpsd
  exact hpsd

/-- **RH from arithmetic positivity and a half-plane bound.** -/
theorem riemannHypothesis_iff_arithmetic_and_halfPlane :
    RiemannHypothesis ↔ (∀ (P : Finset Nat.Primes) (K : ℕ) (τ : ℝ),
      0 ≤ (jasArithmeticForm P K τ).re) ∧
        ∃ alpha : ℝ, 0 ≤ alpha ∧ alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha := by
  constructor
  · intro hRH
    exact ⟨re_jasArithmeticForm_nonneg_of_riemannHypothesis hRH, 0, le_rfl, by norm_num,
      riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH⟩
  · rintro ⟨ha, hq⟩
    exact riemannHypothesis_iff_jasDressedPSD_one_and_quasi.mpr
      ⟨jasDressedPSD_one_of_arithmetic ha, hq⟩

/-- **The zero-free capstone.**  RH holds iff every arithmetic Fejér form is nonnegative and the
series `Σ (Λ(n) − 1) n^{−σ}` has some abscissa of convergence `θ < 1`. -/
theorem riemannHypothesis_iff_arithmetic_and_vonMangoldtMinusOne_abscissa :
    RiemannHypothesis ↔ (∀ (P : Finset Nat.Primes) (K : ℕ) (τ : ℝ),
      0 ≤ (jasArithmeticForm P K τ).re) ∧
        ∃ θ : ℝ, θ < 1 ∧ ∀ σ : ℝ, θ < σ → ∃ L : ℂ, Tendsto (fun N =>
          ∑ n ∈ Finset.range N,
            ((vonMangoldtMinusOne n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ)))
            atTop (𝓝 L) := by
  rw [riemannHypothesis_iff_arithmetic_and_halfPlane]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨alpha, h0, h1, hXi⟩
    refine ⟨1 / 2 + alpha, by linarith, fun σ hσ => ?_⟩
    exact (xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges h0).mp hXi σ hσ
  · rintro ⟨θ, hθ, hconv⟩
    refine ⟨max (θ - 1 / 2) 0, le_max_right _ _, max_lt (by linarith) (by norm_num), ?_⟩
    refine (xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges (le_max_right _ _)).mpr
      fun σ hσ => hconv σ ?_
    have := le_max_left (θ - 1 / 2) 0
    linarith

/-- **RH ⟺ JAS positivity at some dressing below `½`.** -/
theorem riemannHypothesis_iff_exists_lt_half :
    RiemannHypothesis ↔ ∃ σ : ℝ, σ < 1 / 2 ∧ JasDressedPSD σ := by
  rw [riemannHypothesis_iff_jasAbscissa_lt_half]
  constructor
  · intro h
    exact ⟨jasAbscissa, h, jasDressedPSD_jasAbscissa⟩
  · rintro ⟨σ, hσ, hpsd⟩
    exact lt_of_le_of_lt (jasDressedPSD_iff_jasAbscissa_le.mp hpsd) hσ

end RHTower
