import GaloisForLFunctions.RHTower.Sieve.FejerSymmBound
import GaloisForLFunctions.RHTower.Sieve.FejerLocalisation

/-!
# The triangular kernel and its transform

The overlap kernel of two windows of common length `δ` is the triangular function
`tri δ t = (δ - |t|)₊`.  It is continuous, supported in `[-δ, δ]`, and its transform against a phase
is the corpus's symmetric Fejér weight:

    ∫_ℝ (δ - |t|)₊ e^{itL} dt = δ · fejerWeightAt δ L = 2(1 - cos δL)/L² .

So the transform is explicit, real and nonnegative, and decays like `L^{-2}`.  This is the pair that
turns the exact overlap identity of `LogWindowKernel.lean` into a bound by a Dirichlet polynomial.
-/

namespace RHTower.Sieve

open Complex MeasureTheory intervalIntegral

/-- The triangular kernel of width `δ`. -/
noncomputable def tri (δ t : ℝ) : ℝ := max (δ - |t|) 0

theorem tri_nonneg (δ t : ℝ) : 0 ≤ tri δ t := le_max_right _ _

theorem tri_even (δ t : ℝ) : tri δ (-t) = tri δ t := by
  rw [tri, tri, abs_neg]

theorem tri_eq_zero {δ t : ℝ} (h : δ ≤ |t|) : tri δ t = 0 := max_eq_right (by linarith)

theorem tri_eq_sub {δ t : ℝ} (h : |t| ≤ δ) : tri δ t = δ - |t| := max_eq_left (by linarith)

theorem continuous_tri (δ : ℝ) : Continuous (tri δ) := by
  unfold tri
  exact (continuous_const.sub continuous_abs).max continuous_const

theorem continuous_triPhase (δ L : ℝ) :
    Continuous fun t : ℝ => ((tri δ t : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) := by
  refine (Complex.continuous_ofReal.comp (continuous_tri δ)).mul ?_
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul continuous_const)

/-- **The transform of the triangular kernel is the Fejér weight.** -/
theorem integral_tri_phase {δ : ℝ} (hδ : 0 < δ) (L : ℝ) :
    (∫ t : ℝ, ((tri δ t : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      = (δ : ℂ) * fejerWeightAt δ L := by
  set f : ℝ → ℂ := fun t => ((tri δ t : ℝ) : ℂ)
    * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) with hfdef
  have hfc : Continuous f := continuous_triPhase δ L
  have hδC : (δ : ℂ) ≠ 0 := by
    simpa using hδ.ne'
  -- the integrand vanishes outside the support
  have hzero : ∀ t : ℝ, t ∉ Set.Ioc (-δ) δ → f t = 0 := by
    intro t ht
    have habs : δ ≤ |t| := by
      rw [Set.mem_Ioc] at ht
      push Not at ht
      rcases le_or_gt t (-δ) with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have := ht h
        rw [abs_of_nonneg (by linarith)]
        linarith
    rw [hfdef]
    simp [tri_eq_zero habs]
  have hset : (∫ t : ℝ in Set.Ioc (-δ) δ, f t) = ∫ t : ℝ, f t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hint : (∫ t : ℝ, f t) = ∫ t : ℝ in (-δ)..δ, f t := by
    rw [← hset, intervalIntegral.integral_of_le (by linarith)]
  -- split at the origin
  have hsplit : (∫ t : ℝ in (-δ)..(0 : ℝ), f t) + ∫ t : ℝ in (0 : ℝ)..δ, f t
      = ∫ t : ℝ in (-δ)..δ, f t :=
    integral_add_adjacent_intervals (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)
  -- the left half is the reflected right half
  have hrefl : (∫ t : ℝ in (0 : ℝ)..δ, f (-t)) = ∫ t : ℝ in (-δ)..(0 : ℝ), f t := by
    rw [integral_comp_neg f]
    simp
  -- both halves are the corpus's Fejér half-integrals
  have hright : (∫ t : ℝ in (0 : ℝ)..δ, f t)
      = (δ : ℂ) * ∫ t in (0 : ℝ)..δ, ((1 - t / δ : ℝ) : ℂ)
          * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hδ.le, Set.mem_Icc] at ht
    have habs : |t| = t := abs_of_nonneg ht.1
    rw [hfdef]
    simp only
    rw [tri_eq_sub (by rw [habs]; exact ht.2), habs, ← mul_assoc]
    congr 1
    push_cast
    field_simp
  have hleft : (∫ t : ℝ in (-δ)..(0 : ℝ), f t)
      = (δ : ℂ) * ∫ t in (0 : ℝ)..δ, ((1 - t / δ : ℝ) : ℂ)
          * Complex.exp (((t * (-L) : ℝ) : ℂ) * Complex.I) := by
    rw [← hrefl, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hδ.le, Set.mem_Icc] at ht
    have habs : |(-t)| = t := by rw [abs_neg, abs_of_nonneg ht.1]
    rw [hfdef]
    simp only
    rw [tri_eq_sub (by rw [habs]; exact ht.2), habs, ← mul_assoc]
    congr 1
    · push_cast
      field_simp
    · congr 1
      push_cast
      ring
  rw [hint, ← hsplit, hleft, hright, fejerWeightAt]
  ring

end RHTower.Sieve
