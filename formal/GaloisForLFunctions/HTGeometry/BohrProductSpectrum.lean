import GaloisForLFunctions.HTGeometry.LinearOdeBohrSpectrum

/-!
# Modulation and the spectrum of a product with a trigonometric polynomial

The finite-phase argument needs to know how the Bohr spectrum behaves under multiplication.  For a
factor that is a trigonometric polynomial the answer is exact and elementary: multiplying by
`e^{iμt}` translates the whole coefficient function by `μ`, so

`a_{f·g}(λ) = ∑_i c_i · a_f(λ − μ_i)`   for `g = ∑_i c_i e^{iμ_i t}`.

Consequently `spec(f·g) ⊆ spec f + {μ_i}`, and the frequency module of the product is contained in
the frequency module of `f` joined with the `ℚ`-span of the finitely many frequencies of `g`:
multiplying by a trigonometric polynomial enlarges the frequency module by at most finitely many
generators.  That is exactly the mechanism the finite-rank conclusion of eq. (9) rests on.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- Multiplying a character by a conjugate character translates the frequency. -/
theorem expChar_mul_bohrChar (a lam t : ℝ) :
    expChar a t * bohrChar lam t = bohrChar (lam - a) t := by
  simp only [expChar, bohrChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Modulation translates the Bohr coefficient.** -/
theorem bohrCoefficient_mul_expChar (f : ℝ → ℂ) (mu lam : ℝ) :
    bohrCoefficient (fun t => f t * expChar mu t) lam = bohrCoefficient f (lam - mu) := by
  have hfun : (fun t : ℝ => (f t * expChar mu t) * bohrChar lam t)
      = fun t : ℝ => f t * bohrChar (lam - mu) t := by
    funext t
    rw [mul_assoc, expChar_mul_bohrChar]
  rw [bohrCoefficient, hfun]
  rfl

/-- **The convolution formula against a trigonometric polynomial.** -/
theorem bohrCoefficient_mul_trigPoly {ι : Type*} (s : Finset ι) (cg : ι → ℂ) (mu : ι → ℝ)
    {f : ℝ → ℂ} (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f) (lam : ℝ) :
    bohrCoefficient (fun t => f t * ∑ i ∈ s, cg i * expChar (mu i) t) lam
      = ∑ i ∈ s, cg i * bohrCoefficient f (lam - mu i) := by
  have hfun : (fun t : ℝ => (f t * ∑ i ∈ s, cg i * expChar (mu i) t) * bohrChar lam t)
      = fun t : ℝ => ∑ i ∈ s, cg i * (f t * bohrChar (lam - mu i) t) := by
    funext t
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show f t * (cg i * expChar (mu i) t) * bohrChar lam t
        = cg i * (f t * (expChar (mu i) t * bohrChar lam t)) from by ring,
      expChar_mul_bohrChar]
  rw [bohrCoefficient, hfun,
    bohrMean_sum (F := fun i => fun t => cg i * (f t * bohrChar (lam - mu i) t)) s
      (fun i _ => continuous_const.mul (hfc.mul (continuous_bohrChar _)))
      (fun i _ => isBohrAlmostPeriodic_const_mul _
        (isBohrAlmostPeriodic_mul_bohrChar hfc hfa _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bohrMean_const_mul (f := fun t => f t * bohrChar (lam - mu i) t) (cg i)
    (hfc.mul (continuous_bohrChar _)) (isBohrAlmostPeriodic_mul_bohrChar hfc hfa _)]
  rfl

/-- **The spectrum of a product with a trigonometric polynomial.** -/
theorem bohrSpectrum_mul_trigPoly_subset {ι : Type*} (s : Finset ι) (cg : ι → ℂ) (mu : ι → ℝ)
    {f : ℝ → ℂ} (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f) :
    bohrSpectrum (fun t => f t * ∑ i ∈ s, cg i * expChar (mu i) t)
      ⊆ {lam : ℝ | ∃ i ∈ s, lam - mu i ∈ bohrSpectrum f} := by
  intro lam hlam
  by_contra hnot
  apply hlam
  rw [bohrCoefficient_mul_trigPoly s cg mu hfc hfa lam]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hz : bohrCoefficient f (lam - mu i) = 0 := by
    by_contra h
    exact hnot ⟨i, hi, h⟩
  rw [hz, mul_zero]

/-- **Multiplying by a trigonometric polynomial adds only finitely many generators.**  The frequency
module of the product lies in the frequency module of `f` joined with the `ℚ`-span of the finite
frequency set of the polynomial. -/
theorem bohrFrequencyModule_mul_trigPoly_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (cg : ι → ℂ) (mu : ι → ℝ) {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) :
    bohrFrequencyModule (fun t => f t * ∑ i ∈ s, cg i * expChar (mu i) t)
      ≤ bohrFrequencyModule f ⊔ Submodule.span ℚ ((s.image mu : Finset ℝ) : Set ℝ) := by
  rw [bohrFrequencyModule]
  refine Submodule.span_le.mpr ?_
  intro lam hlam
  obtain ⟨i, hi, hmem⟩ := bohrSpectrum_mul_trigPoly_subset s cg mu hfc hfa hlam
  have h1 : (lam - mu i) ∈ bohrFrequencyModule f := Submodule.subset_span hmem
  have h2 : mu i ∈ Submodule.span ℚ ((s.image mu : Finset ℝ) : Set ℝ) :=
    Submodule.subset_span (by simpa using Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hsplit : lam = (lam - mu i) + mu i := by ring
  rw [SetLike.mem_coe, hsplit]
  exact Submodule.add_mem_sup h1 h2

end

end GaloisForLFunctions
