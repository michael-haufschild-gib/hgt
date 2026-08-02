import GaloisForLFunctions.HTGeometry.JetRelationIndependence
import GaloisForLFunctions.HTGeometry.ZetaGammaFieldFieldCoefficients
import GaloisForLFunctions.HTGeometry.UpperEndRatfuncDifferentialAlgebra
import GaloisForLFunctions.HTGeometry.DirichletLFunctionGammaField
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The reciprocal of zeta over the Gamma field

`1/ζ` is not an element of the upper-end *analytic* carrier — its poles are the zeros of `ζ`, which
have arbitrarily large imaginary part — so the finite phase law does not apply to it directly.  It is
however the inverse of the `ζ` element in the meromorphic carrier, and differential transcendence is
invariant under inversion.

So `1/ζ` satisfies no differential relation with coefficients in `ℂ(s)⟨Γ⟩` either: the exclusion
transfers from `ζ`, where it was proved analytically through the frequency rank.
-/

open Filter Set Topology Function

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance zetaInvDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance zetaInvIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance zetaInvDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance zetaInvComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance zetaInvRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance zetaInvRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance zetaInvRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- The coefficient field of the law is a differential algebra over the carrier: its derivation is
the restriction of the ambient one. -/
local instance gammaFieldDifferentialAlgebra :
    DifferentialAlgebra
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
      upperEndMeroField where
  deriv_algebraMap _ := rfl

/-- Zeta is not the zero germ at the upper end: it has no zeros to the right of `1`. -/
theorem zetaUpperAnalytic_ne_zero : zetaUpperAnalytic ≠ 0 := by
  intro h
  have hgerm : (Germ.coeRingHom upperEndFilter riemannZeta : Germ upperEndFilter ℂ) = 0 :=
    congrArg Subtype.val h
  rw [← Germ.coe_zero] at hgerm
  have hev : ∀ᶠ z : ℂ in upperEndFilter, riemannZeta z = (0 : ℂ → ℂ) z :=
    Filter.Germ.coe_eq.mp hgerm
  rw [upperEndFilter_basis.eventually_iff] at hev
  obtain ⟨H, -, hH⟩ := hev
  have hmem : ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I) ∈ upperTail H := by
    show H < ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I).im
    simp
  have hzero : riemannZeta ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I) = 0 := hH hmem
  have hre : (1 : ℝ) < ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I).re := by
    simp
  exact riemannZeta_ne_zero_of_one_lt_re hre hzero

/-- Zeta is a nonzero element of the meromorphic carrier, hence invertible there. -/
theorem zetaMero_ne_zero :
    algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic ≠ 0 := by
  intro h
  refine zetaUpperAnalytic_ne_zero ?_
  refine IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField ?_
  rw [h, map_zero]

/-- **The reciprocal of zeta is differentially transcendental over the Gamma field.**  On any vertical
line to the right of `1` the reciprocal of zeta satisfies no nontrivial differential relation whose
coefficients are nonzero elements of `ℂ(s)⟨Γ⟩`. -/
theorem zetaInv_no_gammaField_field_relation {σ : ℝ} (hσ : 1 < σ) {n N : ℕ} (hN : 0 < N)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0) :
    ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          ((algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic)⁻¹)) ^ (e α i)
      ≠ 0 := by
  classical
  -- the hypothesis of the abstract transfer, from the analytic exclusion for zeta
  have H : ∀ (m M : ℕ), 0 < M → ∀ d : Fin M → Fin (m + 1) → ℕ, Function.Injective d →
      ∀ a : Fin M → ↥(differentialAdjoin (RatFunc ℂ)
        ({gammaUpperMero} : Set upperEndMeroField)), (∀ α, a α ≠ 0) →
        ∑ α : Fin M, algebraMap
            ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
            upperEndMeroField (a α)
          * ∏ i : Fin (m + 1), (differentialJet (i : ℕ)
            (algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic)) ^ (d α i)
          ≠ 0 := by
    intro m M hM d hd a ha
    refine zeta_no_gammaField_field_relation hσ hM d hd
      (fun α => algebraMap ↥(differentialAdjoin (RatFunc ℂ)
        ({gammaUpperMero} : Set upperEndMeroField)) upperEndMeroField (a α))
      (fun α => (a α).2) (fun α h0 => ?_)
    exact ha α (Subtype.ext h0)
  -- the coefficients, as elements of the coefficient field
  have hne : ∀ α, (⟨x α, hxmem α⟩ :
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))) ≠ 0 := by
    intro α h0
    exact hx0 α (congrArg Subtype.val h0)
  have hmain := sum_jet_inv_monomials_ne_zero_of_no_jet_relation
    (F := ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField)))
    zetaMero_ne_zero H hN e he (fun α => ⟨x α, hxmem α⟩) hne
  intro hzero
  exact hmain hzero

variable {q : ℕ} [NeZero q]

/-- A Dirichlet `L`-function is not the zero germ at the upper end: it has no zeros on the line
`Re s = 1` or to its right. -/
theorem lfunctionUpperAnalytic_ne_zero (χ : DirichletCharacter ℂ q) :
    lfunctionUpperAnalytic χ ≠ 0 := by
  intro h
  have hgerm : (Germ.coeRingHom upperEndFilter (DirichletCharacter.LFunction χ) :
      Germ upperEndFilter ℂ) = 0 := congrArg Subtype.val h
  rw [← Germ.coe_zero] at hgerm
  have hev : ∀ᶠ z : ℂ in upperEndFilter,
      DirichletCharacter.LFunction χ z = (0 : ℂ → ℂ) z := Filter.Germ.coe_eq.mp hgerm
  rw [upperEndFilter_basis.eventually_iff] at hev
  obtain ⟨H, -, hH⟩ := hev
  have hmem : ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I) ∈ upperTail H := by
    show H < ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I).im
    simp
  have hzero : DirichletCharacter.LFunction χ ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I) = 0 :=
    hH hmem
  have hne1 : ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro h1
    have hre : ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I).re = (1 : ℂ).re := by rw [h1]
    simp at hre
  have hre : (1 : ℝ) ≤ ((2 : ℂ) + ((H + 1 : ℝ) : ℂ) * Complex.I).re := by
    simp
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne1) hre hzero

/-- A Dirichlet `L`-function is a nonzero element of the meromorphic carrier. -/
theorem lfunctionMero_ne_zero (χ : DirichletCharacter ℂ q) :
    algebraMap upperEndAnalyticSubring upperEndMeroField (lfunctionUpperAnalytic χ) ≠ 0 := by
  intro h
  refine lfunctionUpperAnalytic_ne_zero χ ?_
  refine IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField ?_
  rw [h, map_zero]

/-- **The reciprocal of a Dirichlet `L`-function is differentially transcendental over the Gamma
field.**  For every Dirichlet character the reciprocal of its `L`-function satisfies no nontrivial
differential relation whose coefficients are nonzero elements of `ℂ(s)⟨Γ⟩`. -/
theorem lfunctionInv_no_gammaField_field_relation (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) {n N : ℕ} (hN : 0 < N)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0) :
    ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          ((algebraMap upperEndAnalyticSubring upperEndMeroField
            (lfunctionUpperAnalytic χ))⁻¹)) ^ (e α i)
      ≠ 0 := by
  classical
  have H : ∀ (m M : ℕ), 0 < M → ∀ d : Fin M → Fin (m + 1) → ℕ, Function.Injective d →
      ∀ a : Fin M → ↥(differentialAdjoin (RatFunc ℂ)
        ({gammaUpperMero} : Set upperEndMeroField)), (∀ α, a α ≠ 0) →
        ∑ α : Fin M, algebraMap
            ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
            upperEndMeroField (a α)
          * ∏ i : Fin (m + 1), (differentialJet (i : ℕ)
            (algebraMap upperEndAnalyticSubring upperEndMeroField
              (lfunctionUpperAnalytic χ))) ^ (d α i)
          ≠ 0 := by
    intro m M hM d hd a ha
    refine lfunction_no_gammaField_field_relation χ hσ hM d hd
      (fun α => algebraMap ↥(differentialAdjoin (RatFunc ℂ)
        ({gammaUpperMero} : Set upperEndMeroField)) upperEndMeroField (a α))
      (fun α => (a α).2) (fun α h0 => ?_)
    exact ha α (Subtype.ext h0)
  have hne : ∀ α, (⟨x α, hxmem α⟩ :
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))) ≠ 0 := by
    intro α h0
    exact hx0 α (congrArg Subtype.val h0)
  exact sum_jet_inv_monomials_ne_zero_of_no_jet_relation
    (F := ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField)))
    (lfunctionMero_ne_zero χ) H hN e he (fun α => ⟨x α, hxmem α⟩) hne

end

end GaloisForLFunctions.HTGeometry
