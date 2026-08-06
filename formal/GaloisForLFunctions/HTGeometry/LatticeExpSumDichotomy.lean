import GaloisForLFunctions.HTGeometry.BohrFejerConcentration

/-!
# The exponential-sum dichotomy of the degree-one spectrum

The additive character sums `∑_{k ≤ N} e(αk)` behave in exactly two ways.  On
the lattice, every term is one and the sum is `N+1`, which diverges.  Off the
lattice the character is not one, the sum is geometric, and it is bounded by
`2/‖e(α) − 1‖` uniformly in `N`.

This is the mechanism behind the degree-one entries of the cusp--spectrum
verification table: the standard twist is entire off its spectrum precisely
because these sums stay bounded there, and it carries the pole of the underlying
`L`-function at the lattice points, where they do not.

The geometric estimate itself already exists in the Fejér-kernel layer; it is
extracted here as a statement in its own right.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **The Dirichlet-sum bound.**  A character different from one has geometric
partial sums bounded independently of the length. -/
theorem norm_fejerSum_le (β : ℝ) (N : ℕ) {u : ℝ} (hne : expChar β u ≠ 1) :
    ‖fejerSum β N u‖ ≤ 2 / ‖expChar β u - 1‖ := by
  have hznorm : ‖expChar β u‖ = 1 := norm_expChar β u
  have hdennorm : (0 : ℝ) < ‖expChar β u - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero_of_ne hne
  have hgeom : fejerSum β N u
      = ((expChar β u) ^ (N + 1) - 1) / (expChar β u - 1) := by
    rw [fejerSum_eq_geom]
    exact geom_sum_eq hne (N + 1)
  have hnum : ‖(expChar β u) ^ (N + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hznorm, one_pow, norm_one]
    norm_num
  rw [hgeom, norm_div]
  exact div_le_div₀ (by norm_num) hnum hdennorm le_rfl

/-- The additive character of the shift lattice. -/
noncomputable def latticeChar (α : ℝ) : ℂ := expChar (2 * Real.pi * α) 1

theorem latticeChar_eq (α : ℝ) :
    latticeChar α = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℝ)) := by
  rw [latticeChar, expChar]
  push_cast
  ring_nf

/-- **Off the lattice the character is not one.** -/
theorem latticeChar_ne_one {α : ℝ} (hα : ∀ m : ℤ, α ≠ (m : ℝ)) :
    latticeChar α ≠ 1 := by
  rw [latticeChar_eq]
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hval : ((α : ℝ) : ℂ) = (n : ℂ) := by
    field_simp at hn
    exact hn
  exact hα n (by exact_mod_cast hval)

/-- **Bounded exponential sums off the degree-one spectrum.** -/
theorem norm_latticeExpSum_le {α : ℝ} (hα : ∀ m : ℤ, α ≠ (m : ℝ)) (N : ℕ) :
    ‖∑ k ∈ Finset.range (N + 1), (latticeChar α) ^ k‖
      ≤ 2 / ‖latticeChar α - 1‖ := by
  have h := norm_fejerSum_le (2 * Real.pi * α) N (latticeChar_ne_one hα)
  rwa [fejerSum_eq_geom] at h

/-- **On the lattice the exponential sums diverge.**  Every term is one, so the
sum of length `N+1` is `N+1`. -/
theorem latticeExpSum_at_integer (m : ℤ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (latticeChar (m : ℝ)) ^ k = ((N : ℂ) + 1) := by
  have hone : latticeChar ((m : ℤ) : ℝ) = 1 := by
    rw [latticeChar_eq]
    refine Complex.exp_eq_one_iff.mpr ⟨m, ?_⟩
    push_cast
    ring
  rw [hone]
  simp

end GaloisForLFunctions.HTGeometry
