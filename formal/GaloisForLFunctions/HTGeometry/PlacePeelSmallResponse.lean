import GaloisForLFunctions.HTGeometry.PlacePeelColumn

/-!
# Place-level peel with a small response

When the response is one place-degree smaller than the newest coordinate, the general
place-derivation estimate sends the logarithmic factor two degrees down automatically.  This file
packages the border and below-border conclusions without a separate Wronskian premise.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)
variable {A : Type*} [CommRing A] [Algebra A K] (D : Derivation A K K)
variable {F : Subfield K} {x c : K} {p : Polynomial K}

/-- A border-shaped entry remains two place-degrees small when the response is one place-degree
small. -/
theorem placeDegLE_placeShift_of_borderShape_of_small_response
    (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hDF : ∀ a ∈ F, D a = 0) (hDxv : v.valuation K (D x) ≤ 1)
    (hcv : v.valuation K c ≤ (v.valuation K x)⁻¹)
    (hp : CoeffsIn F p) (hdeg : 1 ≤ p.natDegree)
    {u : K} (hu : u ∈ RatIn F x)
    (hshape : PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (u - (Polynomial.derivative p).eval x / p.eval x)) :
    PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (placeShift D c u) := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  exact placeDegLE_placeShift_of_borderShape v D hF hx hDF hDxv
    (hcv.trans (inv_valuation_le_one v hx)) hp hp0 hu hshape
    (placeDegLE_placeShift_logFactor v D hF hx hDF hDxv hp hdeg hcv)

/-- Under the same small-response condition, every iterated entry below the peel border has zero
scaled value at the place. -/
theorem placeLim_below_of_borderShape_of_small_response
    (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hDF : ∀ a ∈ F, D a = 0) (hDx : D x ∈ RatIn F x)
    (hDxv : v.valuation K (D x) ≤ 1) (hc : c ∈ RatIn F x)
    (hcv : v.valuation K c ≤ (v.valuation K x)⁻¹)
    (hp : CoeffsIn F p) (hdeg : 1 ≤ p.natDegree)
    {u : K} (hu : u ∈ RatIn F x)
    (hshape : PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (u - (Polynomial.derivative p).eval x / p.eval x))
    (r : ℕ) :
    PlaceLim v (v.valuation K x)⁻¹
      (x * ((placeShift D c)^[r] (placeShift D c u))) 0 := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  exact placeLim_below_of_borderShape v D hF hx hDF hDx hDxv hc
    (hcv.trans (inv_valuation_le_one v hx)) hp hp0 hu le_rfl hshape
    (placeDegLE_placeShift_logFactor v D hF hx hDF hDxv hp hdeg hcv) r

end GaloisForLFunctions.HTGeometry
