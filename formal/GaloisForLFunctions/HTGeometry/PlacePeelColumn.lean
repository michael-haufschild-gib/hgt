import GaloisForLFunctions.HTGeometry.PlaceRationalClass

/-!
# The peel's newest column at a place

Assembling the place-level layers: on a border-shaped vector — one whose newest entry agrees with
the logarithmic factor of the newest polynomial to two place-degrees — the scaled newest column has
value `(deg p, 0, …, 0)` at the place, exactly as `topLim_fx_mul_of_borderShape` and
`topDegLE_iterate_of_borderShape` give in the coordinate model.

Every hypothesis is one the model supplies: the coefficients lie in a trivially valued subfield, the
derivation kills that subfield and moves the coordinate inside the rational class, the response is
of unit size, and the operator sends the logarithmic factor two degrees down — which is the
Wronskian identity of the law.

* `ratIn_logFactor`, `ratIn_placeShift`;
* `placeDegLE_placeShift_of_borderShape`;
* `placeLim_border_of_borderShape` — **the border entry has the degree as its value**;
* `placeLim_below_of_borderShape` — **every entry below the border has value zero**;
* `placeDegLE_placeShift_logFactor` — the leading hypothesis, discharged for a small response.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

section Column

variable {A : Type*} [CommRing A] [Algebra A K] (D : Derivation A K K)
variable {F : Subfield K} {x c : K} {p : Polynomial K}

/-- The logarithmic factor lies in the rational class. -/
theorem ratIn_logFactor (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hp : CoeffsIn F p) (hp0 : p ≠ 0) :
    (Polynomial.derivative p).eval x / p.eval x ∈ RatIn F x :=
  ⟨Polynomial.derivative p, p, hp.derivative, hp,
    eval_ne_zero_of_valuation v hF hp hx hp0, rfl⟩

/-- The rational class is closed under the peel's operator. -/
theorem ratIn_placeShift (hDF : ∀ a ∈ F, D a = 0) (hDx : D x ∈ RatIn F x)
    (hc : c ∈ RatIn F x) {g : K} (hg : g ∈ RatIn F x) : placeShift D c g ∈ RatIn F x :=
  ratIn_add (ratIn_derivation D hDF hDx hg) (ratIn_mul hc hg)

/-- **The operator keeps a border-shaped vector at its degree.** -/
theorem placeDegLE_placeShift_of_borderShape (hF : PlaceTrivialOn v F)
    (hx : 1 < v.valuation K x) (hDF : ∀ a ∈ F, D a = 0) (hDxv : v.valuation K (D x) ≤ 1)
    (hcv : v.valuation K c ≤ 1) (hp : CoeffsIn F p) (hp0 : p ≠ 0)
    {u : K} (hu : u ∈ RatIn F x) {γ : ℤᵐ⁰}
    (hshape : PlaceDegLE v γ (u - (Polynomial.derivative p).eval x / p.eval x))
    (hlead : PlaceDegLE v γ (placeShift D c ((Polynomial.derivative p).eval x / p.eval x))) :
    PlaceDegLE v γ (placeShift D c u) := by
  have hmem : u - (Polynomial.derivative p).eval x / p.eval x ∈ RatIn F x :=
    ratIn_sub hu (ratIn_logFactor v hF hx hp hp0)
  have hdrop : v.valuation K (D (u - (Polynomial.derivative p).eval x / p.eval x))
      * v.valuation K x
      ≤ v.valuation K (u - (Polynomial.derivative p).eval x / p.eval x) :=
    valuation_derivation_mul_le_of_ratIn v D hF hDF hx hDxv hmem
  exact placeDegLE_placeShift_of_split v (D := ⇑D) (fun a b => map_add D a b)
    (x := x) (c := c) (le_of_lt hx) hcv (γ := γ) (f := u)
    (ℓ := (Polynomial.derivative p).eval x / p.eval x) hlead hdrop hshape

/-- **The border entry of a border-shaped vector has the degree of the newest factor as its value
at the place.** -/
theorem placeLim_border_of_borderShape (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hp : CoeffsIn F p) (hdeg : 1 ≤ p.natDegree) {u : K} {γ : ℤᵐ⁰}
    (hγ : γ ≤ (v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
    (hshape : PlaceDegLE v γ (u - (Polynomial.derivative p).eval x / p.eval x)) :
    PlaceLim v (v.valuation K x)⁻¹ (x * u) ((p.natDegree : K)) := by
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlead : PlaceLim v (v.valuation K x)⁻¹
      (x * ((Polynomial.derivative p).eval x / p.eval x)) ((p.natDegree : K)) := by
    have h := placeLim_mul_logFactor v hF hp hx hdeg
    rwa [mul_div_assoc] at h
  refine placeLim_mul_of_split v hlead ?_
  rw [PlaceDegLE, Valuation.map_mul]
  refine le_trans (mul_le_mul' (le_refl _) (le_trans hshape hγ)) (le_of_eq ?_)
  rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]

/-- **Every entry below the border has value zero at the place.** -/
theorem placeLim_below_of_borderShape (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hDF : ∀ a ∈ F, D a = 0) (hDx : D x ∈ RatIn F x) (hDxv : v.valuation K (D x) ≤ 1)
    (hc : c ∈ RatIn F x) (hcv : v.valuation K c ≤ 1)
    (hp : CoeffsIn F p) (hp0 : p ≠ 0) {u : K} (hu : u ∈ RatIn F x) {γ : ℤᵐ⁰}
    (hγ : γ ≤ (v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
    (hshape : PlaceDegLE v γ (u - (Polynomial.derivative p).eval x / p.eval x))
    (hlead : PlaceDegLE v γ (placeShift D c ((Polynomial.derivative p).eval x / p.eval x)))
    (r : ℕ) :
    PlaceLim v (v.valuation K x)⁻¹ (x * ((placeShift D c)^[r] (placeShift D c u))) 0 := by
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hbase : PlaceDegLE v γ (placeShift D c u) :=
    placeDegLE_placeShift_of_borderShape v D hF hx hDF hDxv hcv hp hp0 hu hshape hlead
  have hmem : placeShift D c u ∈ RatIn F x := ratIn_placeShift D hDF hDx hc hu
  have hiter : PlaceDegLE v γ ((placeShift D c)^[r] (placeShift D c u)) :=
    placeDegLE_iterate_placeShift v (le_of_lt hx) hcv
      (fun g hg => ratIn_placeShift D hDF hDx hc hg)
      (fun g hg => valuation_derivation_mul_le_of_ratIn v D hF hDF hx hDxv hg) hmem hbase r
  exact placeLim_mul_zero_of_placeDegLE v hx0 (le_trans hiter hγ)

/-- **A response one place-degree down already sends the logarithmic factor two degrees down.**
This discharges the leading hypothesis of the border-shape lemmas whenever the response is small;
when the response is only of unit size the same conclusion is the law's Wronskian cancellation. -/
theorem placeDegLE_placeShift_logFactor (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hDF : ∀ a ∈ F, D a = 0) (hDxv : v.valuation K (D x) ≤ 1)
    (hp : CoeffsIn F p) (hdeg : 1 ≤ p.natDegree)
    (hcv : v.valuation K c ≤ (v.valuation K x)⁻¹) :
    PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (placeShift D c ((Polynomial.derivative p).eval x / p.eval x)) := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hmem : (Polynomial.derivative p).eval x / p.eval x ∈ RatIn F x :=
    ratIn_logFactor v hF hx hp hp0
  have hell : v.valuation K ((Polynomial.derivative p).eval x / p.eval x)
      ≤ (v.valuation K x)⁻¹ := placeDegLE_logFactor v hF hp hx hdeg
  refine PlaceDegLE.add v ?_ ?_
  · have hdrop := valuation_derivation_mul_le_of_ratIn v D hF hDF hx hDxv hmem
    have hstep : v.valuation K (D ((Polynomial.derivative p).eval x / p.eval x))
        * v.valuation K x ≤ (v.valuation K x)⁻¹ := le_trans hdrop hell
    have hmul := mul_le_mul' hstep (le_refl ((v.valuation K x)⁻¹))
    rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one] at hmul
    exact hmul
  · have h := PlaceDegLE.mul v (f := c) hcv (g := (Polynomial.derivative p).eval x / p.eval x) hell
    exact h

end Column

end GaloisForLFunctions.HTGeometry
