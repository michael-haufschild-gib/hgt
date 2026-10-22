import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeReflectionDirichletBudget

/-!
# The infrared/ultraviolet marginal compatibility model

The extracted one-source spectral laws constrain each parity marginal at both ends of the scale,
but they never see the off-diagonal geometry.  An explicit atomic realization shows that they
cannot be contradictory: a low atom carrying almost all the mass, plus an ultraviolet block of
total mass `O(1/a)` placed at heights `2a m_γ`, has

* weak collapse onto the hard edge, because the low atom tends to zero and the high mass vanishes;
* a prescribed Stieltjes ratio `R` at the selected scale, because the low atoms sit at `ηr` and
  `[R(1+η) - 1]r` and the high block contributes `O(r/a)`;
* an exactly prescribed first moment from the ultraviolet block alone.

The Stieltjes value of such a measure is a finite sum, and the whole computation is arithmetic:
`r/(r + ηr) = 1/(1+η)` and `r/(r + [R(1+η)-1]r) = 1/(R(1+η))`, so the ratio is exactly
`R(1-p_e)/(1-p_o)` up to the ultraviolet remainder.
-/

open Finset

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-- The Stieltjes value at scale `r` of a finite atomic measure with weights `p` at locations
`u`, together with one distinguished low atom of mass `1 - ∑ p` at `s`. -/
def atomicStieltjes (r s : ℝ) (p : ι → ℝ) (u : ι → ℝ) : ℝ :=
  (1 - ∑ i, p i) * (r / (r + s)) + ∑ i, p i * (r / (r + u i))

/-- The low atom of the even marginal sits at `ηr`, so it contributes exactly `1/(1+η)`. -/
theorem even_low_value {r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η) :
    r / (r + η * r) = 1 / (1 + η) := by
  have h1 : (0 : ℝ) < 1 + η := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr
  have h1ne : (1 : ℝ) + η ≠ 0 := ne_of_gt h1
  rw [show r + η * r = r * (1 + η) by ring]
  field_simp

/-- The low atom of the odd marginal sits at `[R(1+η) - 1]r`, so it contributes exactly
`1/(R(1+η))`. -/
theorem odd_low_value {r η R : ℝ} (hr : 0 < r) (hη : 0 ≤ η) (hR : 0 < R) :
    r / (r + (R * (1 + η) - 1) * r) = 1 / (R * (1 + η)) := by
  have h1 : (0 : ℝ) < R * (1 + η) := by positivity
  have hrne : r ≠ 0 := ne_of_gt hr
  have h1ne : R * (1 + η) ≠ 0 := ne_of_gt h1
  rw [show r + (R * (1 + η) - 1) * r = r * (R * (1 + η)) by ring]
  field_simp

/-- The ultraviolet block contributes at most the total ultraviolet mass times `r/U`. -/
theorem ultraviolet_tail_le {r U : ℝ} {p u : ι → ℝ} (hr : 0 < r) (hU : 0 < U)
    (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, U ≤ u i) :
    ∑ i, p i * (r / (r + u i)) ≤ (∑ i, p i) * (r / U) := by
  have hterm : ∀ i : ι, p i * (r / (r + u i)) ≤ p i * (r / U) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (hp i)
    have hui : (0 : ℝ) < r + u i := by
      have := hu i
      linarith
    exact div_le_div_of_nonneg_left hr.le hU (by linarith [hu i])
  calc ∑ i, p i * (r / (r + u i)) ≤ ∑ i, p i * (r / U) := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, p i) * (r / U) := by rw [Finset.sum_mul]

/-- The ultraviolet block contributes nonnegatively. -/
theorem ultraviolet_tail_nonneg {r : ℝ} {p u : ι → ℝ} (hr : 0 ≤ r)
    (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, 0 ≤ u i) :
    0 ≤ ∑ i, p i * (r / (r + u i)) := by
  refine Finset.sum_nonneg fun i _ => mul_nonneg (hp i) ?_
  have hui : (0 : ℝ) ≤ r + u i := by linarith [hu i]
  exact div_nonneg hr hui

/-- **The exact low-scale Stieltjes values of the model marginals.**  The even value is between
`(1-p)/(1+η)` and `(1-p)/(1+η) + p r/U`, and likewise for the odd value with `R(1+η)`. -/
theorem even_stieltjes_bounds {r η U : ℝ} {p u : ι → ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hU : 0 < U)
    (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, U ≤ u i) :
    (1 - ∑ i, p i) * (1 / (1 + η)) ≤ atomicStieltjes r (η * r) p u ∧
      atomicStieltjes r (η * r) p u
        ≤ (1 - ∑ i, p i) * (1 / (1 + η)) + (∑ i, p i) * (r / U) := by
  have hu0 : ∀ i, (0 : ℝ) ≤ u i := fun i => le_trans hU.le (hu i)
  constructor
  · rw [atomicStieltjes, even_low_value hr hη]
    have := ultraviolet_tail_nonneg (r := r) hr.le hp hu0
    linarith
  · rw [atomicStieltjes, even_low_value hr hη]
    have := ultraviolet_tail_le hr hU hp hu
    linarith

theorem odd_stieltjes_bounds {r η R U : ℝ} {p u : ι → ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hR : 0 < R) (hU : 0 < U)
    (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, U ≤ u i) :
    (1 - ∑ i, p i) * (1 / (R * (1 + η))) ≤ atomicStieltjes r ((R * (1 + η) - 1) * r) p u ∧
      atomicStieltjes r ((R * (1 + η) - 1) * r) p u
        ≤ (1 - ∑ i, p i) * (1 / (R * (1 + η))) + (∑ i, p i) * (r / U) := by
  have hu0 : ∀ i, (0 : ℝ) ≤ u i := fun i => le_trans hU.le (hu i)
  constructor
  · rw [atomicStieltjes, odd_low_value hr hη hR]
    have := ultraviolet_tail_nonneg (r := r) hr.le hp hu0
    linarith
  · rw [atomicStieltjes, odd_low_value hr hη hR]
    have := ultraviolet_tail_le hr hU hp hu
    linarith

/-- **`(362)`: the prescribed Stieltjes ratio.**  With vanishing ultraviolet mass and vanishing
`η`, the ratio of the two low-scale values is exactly the prescribed `R`. -/
theorem stieltjes_ratio_eq {η R pe po : ℝ} (hη : 0 ≤ η) (hR : 0 < R)
    (hpo : po < 1) :
    ((1 - pe) * (1 / (1 + η))) / ((1 - po) * (1 / (R * (1 + η))))
      = R * ((1 - pe) / (1 - po)) := by
  have h1 : (0 : ℝ) < 1 + η := by linarith
  have h2 : (0 : ℝ) < 1 - po := by linarith
  have h3 : (0 : ℝ) < R * (1 + η) := by positivity
  field_simp

/-- The odd low atom lies strictly above the selected scale whenever `R(1+η) > 2`. -/
theorem odd_low_atom_gt {r η R : ℝ} (hr : 0 < r) (hRη : 2 < R * (1 + η)) :
    r < (R * (1 + η) - 1) * r := by
  nlinarith

end RHTower
