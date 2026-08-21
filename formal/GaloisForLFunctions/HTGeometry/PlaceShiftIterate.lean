import GaloisForLFunctions.HTGeometry.PlaceRationalDerivationDrop

/-!
# The shifted operator does not raise the degree at a place

The peel iterates the operator `E g = D g + c·g`, where `D` is the model's derivation and `c` the
response at the newest coordinate.  In the coordinate model `topShift_topDegLE` says that `E`
does not raise the degree at infinity: the derivation lowers it and the response is coordinate-free.

At a place the same two ingredients are a drop inequality for `D` on the class the peel stays in,
and a unit bound for `c`.  The class has to be closed under `E`, which is what `lowSub`'s closure
supplies in the coordinate model.

* `placeShift`, `placeDegLE_placeShift`;
* `placeDegLE_iterate_placeShift` — **every entry below the border keeps the degree**;
* `placeDegLE_placeShift_of_split` — the border-shape step: a leading term whose own image is
  small, plus a small remainder;
* `placeLim_mul_of_split`, `placeLim_mul_zero_of_placeDegLE` — the value of the scaled column at
  the place: the residue at the border, zero below it.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- The peel's shifted operator: the derivation plus the response. -/
def placeShift (D : K → K) (c : K) : K → K := fun g => D g + c * g

theorem placeShift_apply (D : K → K) (c g : K) : placeShift D c g = D g + c * g := rfl

/-- **The shifted operator does not raise the degree at the place.** -/
theorem placeDegLE_placeShift {D : K → K} {x c : K} (hx : 1 ≤ v.valuation K x)
    (hc : v.valuation K c ≤ 1) {γ : ℤᵐ⁰} {f : K}
    (hdrop : v.valuation K (D f) * v.valuation K x ≤ v.valuation K f)
    (hf : PlaceDegLE v γ f) : PlaceDegLE v γ (placeShift D c f) := by
  refine PlaceDegLE.add v ?_ ?_
  · refine le_trans (le_trans ?_ hdrop) hf
    calc v.valuation K (D f) = v.valuation K (D f) * 1 := (mul_one _).symm
      _ ≤ v.valuation K (D f) * v.valuation K x := mul_le_mul' (le_refl _) hx
  · have h := PlaceDegLE.mul v (γ := 1) (f := c) hc hf
    rwa [one_mul] at h

/-- **Every iterate of the shifted operator keeps the degree**, on a class closed under it and on
which the derivation drops. -/
theorem placeDegLE_iterate_placeShift {D : K → K} {x c : K} (hx : 1 ≤ v.valuation K x)
    (hc : v.valuation K c ≤ 1) {S : Set K} (hclosed : ∀ g ∈ S, placeShift D c g ∈ S)
    (hdrop : ∀ g ∈ S, v.valuation K (D g) * v.valuation K x ≤ v.valuation K g)
    {γ : ℤᵐ⁰} {f : K} (hfS : f ∈ S) (hf : PlaceDegLE v γ f) (r : ℕ) :
    PlaceDegLE v γ ((placeShift D c)^[r] f) := by
  induction r generalizing f with
  | zero => simpa using hf
  | succ r ih =>
      rw [Function.iterate_succ_apply]
      exact ih (hclosed f hfS) (placeDegLE_placeShift v hx hc (hdrop f hfS) hf)

/-- The border-shape step: the operator is additive, so a vector whose leading term has a small
image and whose remainder is small has a small image. -/
theorem placeDegLE_placeShift_of_split {D : K → K}
    (hDadd : ∀ a b : K, D (a + b) = D a + D b) {x c : K} (hx : 1 ≤ v.valuation K x)
    (hc : v.valuation K c ≤ 1) {γ : ℤᵐ⁰} {f ℓ : K}
    (hlead : PlaceDegLE v γ (placeShift D c ℓ))
    (hdrop : v.valuation K (D (f - ℓ)) * v.valuation K x ≤ v.valuation K (f - ℓ))
    (hrem : PlaceDegLE v γ (f - ℓ)) : PlaceDegLE v γ (placeShift D c f) := by
  have hsplit : placeShift D c f = placeShift D c ℓ + placeShift D c (f - ℓ) := by
    have hf : f = ℓ + (f - ℓ) := by ring
    rw [placeShift_apply, placeShift_apply, placeShift_apply]
    conv_lhs => rw [hf]
    rw [hDadd]
    ring
  rw [hsplit]
  exact PlaceDegLE.add v hlead (placeDegLE_placeShift v hx hc hdrop hrem)

/-! ## The value of the scaled column at the place -/

/-- **The residue survives the border shape.**  If the leading term already has the value `a` after
scaling by the coordinate, and the remainder stays small after scaling, so does the whole entry. -/
theorem placeLim_mul_of_split {γ : ℤᵐ⁰} {x f ℓ a : K}
    (hlead : PlaceLim v γ (x * ℓ) a) (hrem : PlaceDegLE v γ (x * (f - ℓ))) :
    PlaceLim v γ (x * f) a := by
  have hsplit : x * f - a = (x * ℓ - a) + x * (f - ℓ) := by ring
  rw [PlaceLim, hsplit]
  exact PlaceDegLE.add v hlead hrem

/-- **The entries below the border have value zero after scaling.**  An entry one place-degree
below the accuracy is still below it after multiplication by the coordinate. -/
theorem placeLim_mul_zero_of_placeDegLE {γ : ℤᵐ⁰} {x g : K} (hx0 : v.valuation K x ≠ 0)
    (hg : PlaceDegLE v (γ * (v.valuation K x)⁻¹) g) : PlaceLim v γ (x * g) 0 := by
  rw [PlaceLim, sub_zero, PlaceDegLE, Valuation.map_mul]
  have h := mul_le_mul' (le_refl (v.valuation K x)) hg
  refine le_trans h (le_of_eq ?_)
  rw [← mul_assoc, mul_comm (v.valuation K x) γ, mul_assoc, mul_inv_cancel₀ hx0, mul_one]

end GaloisForLFunctions.HTGeometry
