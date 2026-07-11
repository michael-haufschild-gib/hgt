import Mathlib.Analysis.PSeries

/-!
# The diagonal Hilbert-rigging barrier for Dirichlet superpositions

Suppose the coefficient state with magnitudes `(n+1)^(-sigma)` is placed in a weighted coefficient
Hilbert space with squared basis norms `w n`.  The formal summation vector `(1,1,...)` is a bounded
dual vector exactly when `sum (w n)^(-1)` converges, while the Dirichlet state belongs to the
Hilbert space exactly when `sum w n * (n+1)^(-2 sigma)` converges.

This file proves that some positive diagonal weight can satisfy both requirements if and only if
`sigma > 1`.  Thus no choice of positive diagonal rigging turns analytic continuation in the
critical strip into a normal Hilbert-space matrix coefficient.  Changing finitely many signs, as
in a diagonal Pontryagin/Krein superspace, does not alter this underlying Hilbert-topology barrier.
-/

noncomputable section

namespace GaloisForLFunctions

/-- Magnitude of the `n`th Dirichlet coefficient, indexed from `n+1`. -/
def dirichletMagnitude (sigma : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ (-sigma)

/-- Existence of a positive diagonal Hilbert rigging in which both the Dirichlet coefficient state
and the all-ones summation covector are normal. -/
def AdmitsDiagonalHilbertRigging (sigma : ℝ) : Prop :=
  ∃ w : ℕ → ℝ,
    (∀ n, 0 < w n) ∧
    Summable (fun n => (w n)⁻¹) ∧
    Summable (fun n => w n * dirichletMagnitude sigma n ^ 2)

private theorem two_mul_le_weighted_sq_add_inv
    {w a : ℝ} (hw : 0 < w) :
    2 * a ≤ w * a ^ 2 + w⁻¹ := by
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  have hsquare := sq_nonneg (w * a - 1)
  apply (mul_le_mul_iff_of_pos_right hw).1
  nlinarith

/-- Weighted `ℓ²` membership of a state and its all-ones dual forces the coefficient sequence into
`ℓ¹`.  This is the exact Cauchy--Schwarz obstruction behind the rigging barrier. -/
theorem summable_of_weighted_rigging
    (a w : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hw : ∀ n, 0 < w n)
    (hdual : Summable fun n => (w n)⁻¹)
    (hstate : Summable fun n => w n * a n ^ 2) :
    Summable a := by
  have hmajor : Summable (fun n => w n * a n ^ 2 + (w n)⁻¹) := hstate.add hdual
  have htwo : Summable (fun n => 2 * a n) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (by norm_num) (ha n)
    · intro n
      exact two_mul_le_weighted_sq_add_inv (hw n)
    · exact hmajor
  exact (summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)).mp htwo

/-- The coefficient magnitudes themselves are summable exactly to the right of the classical
Dirichlet abscissa `sigma = 1`. -/
theorem summable_dirichletMagnitude_iff (sigma : ℝ) :
    Summable (dirichletMagnitude sigma) ↔ 1 < sigma := by
  have heq : dirichletMagnitude sigma =
      fun n : ℕ => 1 / |(n : ℝ) + 1| ^ sigma := by
    funext n
    change ((n : ℝ) + 1) ^ (-sigma) = 1 / |(n : ℝ) + 1| ^ sigma
    rw [Real.rpow_neg (by positivity)]
    rw [abs_of_pos (by positivity)]
    simp [one_div]
  rw [heq]
  exact Real.summable_one_div_nat_add_rpow 1 sigma

/-- **Sharp rigging barrier.** A positive diagonal Hilbert scale can make both the Dirichlet state
and the all-ones summation covector normal if and only if `sigma > 1`. -/
theorem admitsDiagonalHilbertRigging_iff (sigma : ℝ) :
    AdmitsDiagonalHilbertRigging sigma ↔ 1 < sigma := by
  constructor
  · rintro ⟨w, hw, hdual, hstate⟩
    apply (summable_dirichletMagnitude_iff sigma).mp
    exact summable_of_weighted_rigging (dirichletMagnitude sigma) w
      (fun n => by unfold dirichletMagnitude; positivity) hw hdual hstate
  · intro hsigma
    let w : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ sigma
    refine ⟨w, ?_, ?_, ?_⟩
    · intro n
      dsimp [w]
      positivity
    · have hsum := (summable_dirichletMagnitude_iff sigma).2 hsigma
      apply hsum.congr
      intro n
      dsimp [w, dirichletMagnitude]
      rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ))]
    · have hsum := (summable_dirichletMagnitude_iff sigma).2 hsigma
      apply hsum.congr
      intro n
      dsimp [w, dirichletMagnitude]
      have hn : 0 < (n + 1 : ℝ) := by positivity
      rw [← Real.rpow_mul_natCast hn.le]
      rw [← Real.rpow_add hn]
      congr 1
      ring

end GaloisForLFunctions
