import GaloisForLFunctions.HTGeometry.TranslationCocycleAnomaly

/-!
# The two-shift Koszul cochain of a meromorphic element

For two commuting translations the multiplicative cochain complex of the free rank-two translation
group is the Koszul complex: a degree-one cochain is a pair, and its coboundary is the mixed
quotient of the two entries.

The canonical degree-one cochain of an element -- the pair of its two shift quotients -- has trivial
coboundary, because the two translations commute.  That is the algebraic content behind the relative
class of the bi-anomaly: the cochain is a cocycle before any coefficient quotient is taken, so its
class in every quotient of coefficients is again a cocycle.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The shift quotient of an element: one component of its canonical degree-one cochain. -/
def shiftQuotient (q : ℂ) (g : meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv q g / g

theorem shiftQuotient_ne_zero {q : ℂ} {g : meroField (Set.univ : Set ℂ)} (hg : g ≠ 0) :
    shiftQuotient q g ≠ 0 := by
  rw [shiftQuotient]
  refine div_ne_zero ?_ hg
  intro h0
  exact hg ((addTranslationMeroEquiv q).injective (by rw [h0, map_zero]))

/-- The Koszul coboundary of a degree-one cochain for two commuting shifts. -/
def koszulCoboundary (sigma tau : ℂ) (p : meroField (Set.univ : Set ℂ)
    × meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) :=
  shiftQuotient tau p.1 / shiftQuotient sigma p.2

/-- **The canonical degree-one cochain is a Koszul cocycle.**  The two translations commute, so the
mixed quotient of the two shift quotients is one. -/
theorem koszulCoboundary_shiftQuotient (sigma tau : ℂ) {g : meroField (Set.univ : Set ℂ)}
    (hg : g ≠ 0) :
    koszulCoboundary sigma tau (shiftQuotient sigma g, shiftQuotient tau g) = 1 := by
  have hgs : addTranslationMeroEquiv sigma g ≠ 0 := by
    intro h0
    exact hg ((addTranslationMeroEquiv sigma).injective (by rw [h0, map_zero]))
  have hgt : addTranslationMeroEquiv tau g ≠ 0 := by
    intro h0
    exact hg ((addTranslationMeroEquiv tau).injective (by rw [h0, map_zero]))
  have hmix : addTranslationMeroEquiv tau (addTranslationMeroEquiv sigma g)
      = addTranslationMeroEquiv sigma (addTranslationMeroEquiv tau g) := by
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  rw [koszulCoboundary, shiftQuotient, shiftQuotient, shiftQuotient, shiftQuotient,
    map_div₀, map_div₀, hmix]
  have hgts : addTranslationMeroEquiv sigma (addTranslationMeroEquiv tau g) ≠ 0 := by
    intro h0
    exact hgt ((addTranslationMeroEquiv sigma).injective (by rw [h0, map_zero]))
  field_simp

/-- **The relative class is a cocycle.**  Whatever the coefficient quotient, the image of the
canonical degree-one cochain has trivial Koszul coboundary, because the coboundary is already
trivial upstairs. -/
theorem koszulCoboundary_shiftQuotient_mem_of_one_mem (sigma tau : ℂ)
    {g : meroField (Set.univ : Set ℂ)} (hg : g ≠ 0)
    {A : Set (meroField (Set.univ : Set ℂ))} (hA : (1 : meroField (Set.univ : Set ℂ)) ∈ A) :
    koszulCoboundary sigma tau (shiftQuotient sigma g, shiftQuotient tau g) ∈ A := by
  rw [koszulCoboundary_shiftQuotient sigma tau hg]
  exact hA

/-- **The degree-one anomaly of the elliptic gamma, in cochain form.**  Its canonical cochain is a
Koszul cocycle, yet no differentially algebraic element makes it a coboundary. -/
theorem ellipticGamma_koszul_cocycle_not_daCoboundary {sigma tau : ℂ}
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    koszulCoboundary sigma tau
        (shiftQuotient sigma (multipleEllipticGammaMero (ellipticPeriodPair sigma tau)
          (ellipticPeriodPair_im_pos hsigma htau)),
        shiftQuotient tau (multipleEllipticGammaMero (ellipticPeriodPair sigma tau)
          (ellipticPeriodPair_im_pos hsigma htau))) = 1
      ∧ ∀ b ∈ daSector, b ≠ 0 →
        ¬ (∀ q ∈ Submodule.span ℤ (Set.range (ellipticGammaSourcePeriods sigma tau)),
          addTranslationMeroEquiv q
              (multipleEllipticGammaMero (ellipticPeriodPair sigma tau)
                (ellipticPeriodPair_im_pos hsigma htau)) * b
            = multipleEllipticGammaMero (ellipticPeriodPair sigma tau)
                (ellipticPeriodPair_im_pos hsigma htau) * addTranslationMeroEquiv q b) := by
  have hGne : multipleEllipticGammaMero (ellipticPeriodPair sigma tau)
      (ellipticPeriodPair_im_pos hsigma htau) ≠ 0 :=
    multipleEllipticGammaMero_ne_zero _ _
  refine ⟨koszulCoboundary_shiftQuotient sigma tau hGne, fun b hbB hb0 hcob => ?_⟩
  exact ellipticGamma_cocycle_not_daCoboundary hsigma htau hindep hbB hb0 hcob

end

end GaloisForLFunctions.HTGeometry
