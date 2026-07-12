import GaloisForLFunctions.HTGeometry.UpperEndDifferentialIndependence
import GaloisForLFunctions.HTGeometry.RationalIndependentWeights

/-!
# A universal countable facet-orbit palette

One countable rationally independent real weight family encodes all finite vertex lattices.
Finite subsets of `N` provide universal facet labels, and finitely supported integral vectors
provide every finite Laurent orbit.  An injective imaginary facet tag makes the resulting complex
shift palette collision-free.  The countable-shift upper-end theorem then chooses one positive
prime-log Herglotz gauge whose entire universal palette is differentially independent.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

/-- Embed `N` into the chosen Hamel basis of `R` over `Q`. -/
def universalRationalBasisEmbedding :
    ℕ ↪ Module.Free.ChooseBasisIndex ℚ ℝ := by
  apply Classical.choice
  rw [← Cardinal.lift_mk_le']
  rw [← Module.Free.rank_eq_card_chooseBasisIndex, Real.rank_rat_real,
    Cardinal.mk_nat]
  simpa only [Cardinal.lift_aleph0, Cardinal.lift_continuum] using
    Cardinal.aleph0_le_continuum

/-- One fixed countable family of rationally independent real translation weights. -/
def universalRationalIndependentWeights : ℕ → ℝ :=
  (Module.Free.chooseBasis ℚ ℝ) ∘ universalRationalBasisEmbedding

/-- The universal real weight family is rationally linearly independent. -/
theorem universalRationalIndependentWeights_linearIndependent :
    LinearIndependent ℚ universalRationalIndependentWeights := by
  exact (Module.Free.chooseBasis ℚ ℝ).linearIndependent.comp
    universalRationalBasisEmbedding universalRationalBasisEmbedding.injective

/-- Real displacement of a finitely supported universal integral exponent vector. -/
def universalIntegerWeightSum (m : ℕ →₀ ℤ) : ℝ :=
  m.sum fun n c => (c : ℝ) * universalRationalIndependentWeights n

/-- Rational independence makes the universal integral displacement encoding injective. -/
theorem universalIntegerWeightSum_injective :
    Function.Injective universalIntegerWeightSum := by
  intro m n hmn
  let mq : ℕ →₀ ℚ := m.mapRange (fun z : ℤ => (z : ℚ)) (by simp)
  let nq : ℕ →₀ ℚ := n.mapRange (fun z : ℤ => (z : ℚ)) (by simp)
  have hlin : Finsupp.linearCombination ℚ universalRationalIndependentWeights mq =
      Finsupp.linearCombination ℚ universalRationalIndependentWeights nq := by
    simp only [mq, nq, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_mapRange_index
        (fun i => zero_smul ℚ (universalRationalIndependentWeights i)),
      Finsupp.sum_mapRange_index
        (fun i => zero_smul ℚ (universalRationalIndependentWeights i))]
    simpa [universalIntegerWeightSum, Rat.smul_def] using hmn
  have hq : mq = nq :=
    universalRationalIndependentWeights_linearIndependent.finsuppLinearCombination_injective hlin
  apply Finsupp.ext
  intro i
  have hi := Finsupp.ext_iff.mp hq i
  change ((m i : ℤ) : ℚ) = ((n i : ℤ) : ℚ) at hi
  exact_mod_cast hi

/-- Every finite facet label and every finitely supported integral orbit exponent occur in this
one countable type. -/
abbrev UniversalFacetOrbitIndex := Finset ℕ × (ℕ →₀ ℤ)

/-- Canonical injective natural tag of a finite subset of `N`. -/
def universalFacetTag (A : Finset ℕ) : ℕ := Encodable.encode A

theorem universalFacetTag_injective : Function.Injective universalFacetTag :=
  Encodable.encode_injective

/-- The universal complex shift: real integral displacement plus imaginary facet tag. -/
def universalFacetOrbitShift : UniversalFacetOrbitIndex → ℂ := fun q =>
  Complex.ofReal (universalIntegerWeightSum q.2) +
    Complex.ofReal (universalFacetTag q.1 : ℝ) * Complex.I

/-- **Universal collision-free facet palette.** Distinct finite facets or distinct finitely
supported integral orbit exponents always give distinct complex shifts. -/
theorem universalFacetOrbitShift_injective :
    Function.Injective universalFacetOrbitShift := by
  rintro ⟨A, m⟩ ⟨B, n⟩ h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [universalFacetOrbitShift, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero] at him
  simp only [universalFacetOrbitShift, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero,
    add_zero] at hre
  have htagReal : (universalFacetTag A : ℝ) = (universalFacetTag B : ℝ) := by
    simpa using him
  have htag : universalFacetTag A = universalFacetTag B := by
    exact_mod_cast htagReal
  have hA : A = B := universalFacetTag_injective htag
  subst B
  have hm : m = n := universalIntegerWeightSum_injective hre
  subst n
  rfl

/-- **One-source universal facet-orbit freedom.** There is one bounded positive prime-log gauge
whose translated upper-end source is differentially independent on the complete universal palette
of every finite facet and every finite integral orbit. -/
theorem exists_universalFacetOrbit_upperEnd_differentialIndependent :
    ∃ u : PrimeLogBoundedGauge,
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent (RatFunc ℂ)
        (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u) :=
  exists_upperEndShift_differentialIndependent
    universalFacetOrbitShift universalFacetOrbitShift_injective

end

end GaloisForLFunctions.HTGeometry
