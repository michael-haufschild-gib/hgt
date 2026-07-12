import GaloisForLFunctions.HTGeometry.RationalIndependentWeights
import GaloisForLFunctions.HTGeometry.LocalizedStanleyReisnerDifferentialMatroid

/-!
# Collision-free facet orbit shifts

Rationally independent real vertex weights encode every integral orbit exponent injectively.
Distinct rational imaginary facet tags separate different facets.  Their sum gives one globally
injective complex shift palette for all facet--Laurent orbit coordinates, with no cross-facet or
within-facet collisions.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real displacement encoded by an integral vertex exponent vector. -/
def integerWeightSum
    {α : Type*} [Fintype α] (omega : α → ℝ) (n : α → ℤ) : ℝ :=
  ∑ v, (n v : ℝ) * omega v

/-- Rational independence of the weights makes integral displacement encoding injective. -/
theorem integerWeightSum_injective_of_linearIndependent
    {α : Type*} [Fintype α]
    (omega : α → ℝ) (homega : LinearIndependent ℚ omega) :
    Function.Injective (integerWeightSum omega) := by
  classical
  intro n m hnm
  have hrel : ∑ v, ((n v - m v : ℤ) : ℚ) • omega v = 0 := by
    calc
      ∑ v, ((n v - m v : ℤ) : ℚ) • omega v =
          ∑ v, ((n v : ℝ) - (m v : ℝ)) * omega v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Rat.smul_def]
        congr 1
        norm_cast
      ∑ v, ((n v : ℝ) - (m v : ℝ)) * omega v =
          integerWeightSum omega n - integerWeightSum omega m := by
        simp only [sub_mul, integerWeightSum, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hnm
  have hcoeff := Fintype.linearIndependent_iff.mp homega
    (fun v => ((n v - m v : ℤ) : ℚ)) hrel
  funext v
  have hv := hcoeff v
  change ((n v - m v : ℤ) : ℚ) = 0 at hv
  have hvz : n v - m v = 0 := by exact_mod_cast hv
  exact sub_eq_zero.mp hvz

/-- A distinct rational tag for each facet. -/
def facetTag
    {α : Type*} (facets : Finset (Finset α)) (F : facets) : ℚ :=
  (Fintype.equivFin facets F : ℕ)

/-- Distinct facets have distinct rational tags. -/
theorem facetTag_injective
    {α : Type*} (facets : Finset (Finset α)) :
    Function.Injective (facetTag facets) := by
  intro F G h
  apply (Fintype.equivFin facets).injective
  apply Fin.ext
  change (((Fintype.equivFin facets F : ℕ) : ℚ)) =
    (((Fintype.equivFin facets G : ℕ) : ℚ)) at h
  exact_mod_cast h

/-- The complex shift with real Laurent displacement and imaginary facet tag. -/
def facetOrbitShift
    {α : Type*} [Fintype α]
    (facets : Finset (Finset α)) (omega : α → ℝ) :
    (facets × (α → ℤ)) → ℂ :=
  fun q => Complex.ofReal (integerWeightSum omega q.2) +
    Complex.ofReal (facetTag facets q.1 : ℝ) * Complex.I

/-- **Collision-free facet orbit law.**  Facet tags and rationally independent vertex weights make
the complete facet--integral-orbit shift palette injective. -/
theorem facetOrbitShift_injective
    {α : Type*} [Fintype α]
    (facets : Finset (Finset α)) (omega : α → ℝ)
    (homega : LinearIndependent ℚ omega) :
    Function.Injective (facetOrbitShift facets omega) := by
  rintro ⟨F, n⟩ ⟨G, m⟩ h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [facetOrbitShift, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero] at him
  simp only [facetOrbitShift, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero,
    add_zero] at hre
  have htagReal : (facetTag facets F : ℝ) = (facetTag facets G : ℝ) := by
    simpa using him
  have htag : facetTag facets F = facetTag facets G := by exact_mod_cast htagReal
  have hF : F = G := facetTag_injective facets htag
  subst G
  have hn : n = m := integerWeightSum_injective_of_linearIndependent omega homega hre
  subst m
  rfl

end

end GaloisForLFunctions.HTGeometry
