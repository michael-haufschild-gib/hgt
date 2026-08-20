/-
# Closed finite-modulus Dirichlet L zero-density boxes

This module turns the existing Jensen disc count into a literal vertical
zero-count carrier.  It counts zeros of a completed nonprincipal Dirichlet
L-function in the source-style box `σ ≤ Re(s) ≤ 1`, `|Im(s)| ≤ H`, then
encloses that box in a common compact disc.  The resulting bound is only a
fixed-modulus height envelope; it is not the conductor-uniform density
exponent required by Bondarenko--Heap Proposition 2.

No RH, GRH, exceptional zero, or zero-density premise is used.
-/
import GaloisForLFunctions.RHTower.DirichletLZeroCount

open Complex Metric

noncomputable section

namespace RHTower

/-- The vertical zero-counting box with real part between `σ` and `1` and height at most `H`. -/
def completedLFunctionZeroDensityBox (σ H : ℝ) : Set ℂ :=
  {z | σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ H}

/-- The source-style zero box lies in an explicit closed disc centered at the common Jensen
anchor `2`. -/
theorem completedLFunction_zeroDensityBox_subset_disc (σ H : ℝ) :
    completedLFunctionZeroDensityBox σ H ⊆ closedBall (2 : ℂ) (4 + |σ| + |H|) := by
  intro z hz
  change σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ H at hz
  have hre : |z.re| ≤ |σ| + 1 := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le σ, hz.1]
    · linarith [abs_nonneg σ, hz.2.1]
  have him : |z.im| ≤ |H| := le_trans hz.2.2 (le_abs_self H)
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖z - 2‖ ≤ ‖z‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
    _ ≤ (|z.re| + |z.im|) + 2 := by
      gcongr
      exact Complex.norm_le_abs_re_add_abs_im z
      norm_num
    _ ≤ 4 + |σ| + |H| := by linarith

/-- The divisor count in the vertical zero box is bounded by the count in its explicit enclosing
disc.  The comparison is pointwise and uses analytic nonnegativity of the divisor outside the box. -/
theorem completedLFunction_divisor_sum_zeroDensityBox_le_disc
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ H : ℝ) :
    ∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
      (completedLFunctionZeroDensityBox σ H) u ≤
    ∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
      (closedBall (2 : ℂ) (4 + |σ| + |H|)) u := by
  let f := DirichletCharacter.completedLFunction χ.1
  let U := closedBall (2 : ℂ) (4 + |σ| + |H|)
  let V := completedLFunctionZeroDensityBox σ H
  have hVU : V ⊆ U := completedLFunction_zeroDensityBox_subset_disc σ H
  have hf : AnalyticOnNhd ℂ f Set.univ := completedLFunction_analyticOnNhd n χ
  have hfU : AnalyticOnNhd ℂ f U := hf.mono (Set.subset_univ U)
  have hfV : AnalyticOnNhd ℂ f V := hf.mono (Set.subset_univ V)
  refine finsum_le_finsum' ?_ ?_ fun u => ?_
  · exact hfU.meromorphicOn.divisor_support_finite_of_subset (isCompact_closedBall ..) hVU
  · exact hfU.meromorphicOn.divisor_support_finite_of_subset
      (isCompact_closedBall ..) (Set.Subset.rfl)
  · change (MeromorphicOn.divisor f V) u ≤ (MeromorphicOn.divisor f U) u
    by_cases hu : u ∈ V
    · rw [MeromorphicOn.divisor_apply hfV.meromorphicOn hu,
        MeromorphicOn.divisor_apply hfU.meromorphicOn (hVU hu)]
    · simp only [MeromorphicOn.divisor_def, hu, and_false, ite_false]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfU u

/-- Multiplicity-weighted count of zeros of one completed nonprincipal Dirichlet L-function in
the vertical zero-density box. -/
def completedLFunctionZeroDensityBoxCount
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ H : ℝ) : ℝ :=
  (↑(∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
    (completedLFunctionZeroDensityBox σ H) u) : ℝ)

/-- The literal vertical box count is bounded by the enclosing-disc divisor count. -/
theorem completedLFunction_zeroDensityBoxCount_le_disc
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ H : ℝ) :
    completedLFunctionZeroDensityBoxCount n χ σ H ≤
      (↑(∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
        (closedBall (2 : ℂ) (4 + |σ| + |H|)) u) : ℝ) := by
  change (↑(∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
    (completedLFunctionZeroDensityBox σ H) u) : ℝ) ≤ _
  exact_mod_cast completedLFunction_divisor_sum_zeroDensityBox_le_disc n χ σ H

/-- Every completed nonprincipal Dirichlet L-function has a fully closed source-style vertical
zero-box count bound.  Its constant may depend on the certified character; this is groundwork,
not a conductor-uniform density theorem. -/
theorem completedLFunction_zeroDensityBoxCount_growth
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ H : ℝ,
      completedLFunctionZeroDensityBoxCount n χ σ H ≤
        C * (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
  obtain ⟨C, hC, hbound⟩ := completedLFunction_zeroCount_growth_at_two n χ
  refine ⟨C, hC, ?_⟩
  intro σ H
  have hR : 1 ≤ 4 + |σ| + |H| := by linarith [abs_nonneg σ, abs_nonneg H]
  calc
    _ ≤ (↑(∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
        (closedBall (2 : ℂ) (4 + |σ| + |H|)) u) : ℝ) :=
      completedLFunction_zeroDensityBoxCount_le_disc n χ σ H
    _ ≤ C * (1 + (4 + |σ| + |H|)) * Real.log (2 + (4 + |σ| + |H|)) :=
      hbound _ hR
    _ = _ := by ring_nf

/-- Total completed-L zero count over the finite nonprincipal character family at one modulus,
inside the literal vertical zero-density box. -/
def completedLFunctionFamilyZeroDensityBoxCount (n : ℕ) (σ H : ℝ) : ℝ :=
  ∑ χ : NonprincipalDirichletCharacter n,
    completedLFunctionZeroDensityBoxCount n χ σ H

/-- Fixed-modulus aggregation of the closed vertical zero-box count.  The proof internally
chooses every character constant and sums them; no density conjecture is an input. -/
theorem completedLFunction_family_zeroDensityBoxCount_growth
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ σ H : ℝ,
      completedLFunctionFamilyZeroDensityBoxCount n σ H ≤
        C * (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
  choose C hCpos hCbound using completedLFunction_zeroDensityBoxCount_growth (n := n)
  have hCsum : 0 ≤ ∑ χ : NonprincipalDirichletCharacter n, C χ :=
    Finset.sum_nonneg (fun χ _ ↦ (hCpos χ).le)
  refine ⟨1 + ∑ χ : NonprincipalDirichletCharacter n, C χ, by linarith, ?_⟩
  intro σ H
  have hshape : 0 ≤ (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by linarith [abs_nonneg σ, abs_nonneg H])
  rw [completedLFunctionFamilyZeroDensityBoxCount]
  calc
    _ ≤ ∑ χ : NonprincipalDirichletCharacter n,
        C χ * (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
      exact Finset.sum_le_sum (fun χ _ ↦ hCbound χ σ H)
    _ = (∑ χ : NonprincipalDirichletCharacter n, C χ) *
        ((5 + |σ| + |H|) * Real.log (6 + |σ| + |H|)) := by
      simp_rw [mul_assoc]
      rw [Finset.sum_mul]
    _ ≤ (1 + ∑ χ : NonprincipalDirichletCharacter n, C χ) *
        ((5 + |σ| + |H|) * Real.log (6 + |σ| + |H|)) := by
      nlinarith [mul_le_mul_of_nonneg_right (by linarith :
        (∑ χ : NonprincipalDirichletCharacter n, C χ) ≤ 1 + ∑ χ, C χ) hshape]
    _ = _ := by ring

end RHTower
