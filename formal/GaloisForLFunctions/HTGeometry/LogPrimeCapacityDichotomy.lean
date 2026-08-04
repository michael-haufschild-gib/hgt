import GaloisForLFunctions.HTGeometry.PaletteJetGerms
import GaloisForLFunctions.HTGeometry.OrbitLagrangeCapacity
import GaloisForLFunctions.HTGeometry.ProductPaletteIndependence

/-!
# The capacity dichotomy, with an explicit palette of every size

Every ingredient of the capacity dichotomy is now unconditional: the log-prime block carriers give,
for every size, a palette whose jets are algebraically independent over the constants; the slice
criterion lifts that independence from the constants to the first-factor meromorphic field; the
translation orbit of a Lagrange interpolator gives an observation packet which is the identity at the
base point, hence invertible; and no family of more observations than sources is ever differentially
independent.

So for every `n` there is a differentially independent family of `n` sources in the two-variable
meromorphic field, an explicit invertible packet of `n` observations mixed from it which is again
differentially independent, and no packet of `n + 1` observations from it that is.  The capacity
spectrum is unbounded and never attained, on the card's own object, with no classical input.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Matrix

noncomputable section

/-- The log-prime palette of `n + 1` sources, pulled back to the second factor of a product domain
and read in its meromorphic field. -/
def logPrimePaletteSources (V : Set ℂ) (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (n : ℕ) : Fin (n + 1) → dirMeroField ((Set.univ : Set ℂ) ×ˢ V) :=
  letI := isDomain_analyticGermSubringOn ((Set.univ : Set ℂ) ×ˢ V) (isOpen_univ.prod hVo)
    (isPreconnected_univ.prod hVc) (Set.univ_nonempty.prod hVne)
  fun k => algebraMap (analyticGermSubringOn ((Set.univ : Set ℂ) ×ˢ V))
    (dirMeroField ((Set.univ : Set ℂ) ×ˢ V))
    (analyticGermPullbackSnd (Set.univ : Set ℂ) V
      (blockCarrierGerm V (expSeriesNormallySummable_logPrimeBlock n) k))

/-- **The capacity dichotomy with an explicit palette.**  For every size there is a differentially
independent family of that many sources in the two-variable meromorphic field, an explicit invertible
packet of that many observations mixed from it which is again differentially independent, and no
packet of one more observation from it that is. -/
theorem logPrimePalette_capacity_dichotomy {V : Set ℂ} (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hVne : V.Nonempty) (n : ℕ) {a : ℂ} (ha : a ≠ 0) (x₀ : ℂ) :
    letI := isDomain_analyticGermSubringOn (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
      Set.univ_nonempty
    letI := isDomain_analyticGermSubringOn ((Set.univ : Set ℂ) ×ˢ V) (isOpen_univ.prod hVo)
      (isPreconnected_univ.prod hVc) (Set.univ_nonempty.prod hVne)
    letI := dirMeroFieldDifferential (isOpen_univ.prod hVo) (isPreconnected_univ.prod hVc)
      (Set.univ_nonempty.prod hVne) ((0 : ℂ), (1 : ℂ))
    letI : Algebra (dirMeroField (Set.univ : Set ℂ)) (dirMeroField ((Set.univ : Set ℂ) ×ˢ V)) :=
      (meroPullbackFst isOpen_univ isPreconnected_univ Set.univ_nonempty (isOpen_univ.prod hVo)
        (isPreconnected_univ.prod hVc) (Set.univ_nonempty.prod hVne) hVne).toAlgebra
    DifferentialIndependent (dirMeroField (Set.univ : Set ℂ))
        (logPrimePaletteSources V hVo hVc hVne n)
      ∧ DifferentialIndependent (dirMeroField (Set.univ : Set ℂ))
        (matrixLinearForms ((orbitLagrangeMatrix x₀ a (n + 1)).map
          (algebraMap (analyticGermSubringOn (Set.univ : Set ℂ))
            (dirMeroField (Set.univ : Set ℂ)))) (logPrimePaletteSources V hVo hVc hVne n))
      ∧ ∀ A : Matrix (Fin (n + 2)) (Fin (n + 1)) (analyticGermSubringOn (Set.univ : Set ℂ)),
        ¬ DifferentialIndependent (dirMeroField (Set.univ : Set ℂ))
          (matrixLinearForms (A.map (algebraMap (analyticGermSubringOn (Set.univ : Set ℂ))
            (dirMeroField (Set.univ : Set ℂ)))) (logPrimePaletteSources V hVo hVc hVne n)) := by
  letI := isDomain_analyticGermSubringOn (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  letI := isDomain_analyticGermSubringOn ((Set.univ : Set ℂ) ×ˢ V) (isOpen_univ.prod hVo)
    (isPreconnected_univ.prod hVc) (Set.univ_nonempty.prod hVne)
  letI := dirMeroFieldDifferential (isOpen_univ.prod hVo) (isPreconnected_univ.prod hVc)
    (Set.univ_nonempty.prod hVne) ((0 : ℂ), (1 : ℂ))
  letI : Algebra (dirMeroField (Set.univ : Set ℂ)) (dirMeroField ((Set.univ : Set ℂ) ×ˢ V)) :=
    (meroPullbackFst isOpen_univ isPreconnected_univ Set.univ_nonempty (isOpen_univ.prod hVo)
      (isPreconnected_univ.prod hVc) (Set.univ_nonempty.prod hVne) hVne).toAlgebra
  have hsources : DifferentialIndependent (dirMeroField (Set.univ : Set ℂ))
      (logPrimePaletteSources V hVo hVc hVne n) :=
    differentialIndependent_pullbackSnd_of_slice isOpen_univ isPreconnected_univ Set.univ_nonempty
      hVo hVc hVne (1 : ℂ) (blockCarrierGerm V (expSeriesNormallySummable_logPrimeBlock n))
      (algebraicIndependent_jetGerm_logPrimePalette hVo hVne n)
  refine ⟨hsources, ?_, ?_⟩
  · exact orbitLagrange_capacity_realization hVo hVc hVne (1 : ℂ) ha x₀ _ hsources
  · intro A
    exact productCapacity_nonconcentration isOpen_univ isPreconnected_univ Set.univ_nonempty
      hVo hVc hVne (1 : ℂ) A _ hsources

end

end GaloisForLFunctions.HTGeometry
