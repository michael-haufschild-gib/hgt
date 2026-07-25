import GaloisForLFunctions.HTGeometry.StanleyReisnerHollowSimplexRank

/-!
# Squarefree multigrading of the Stanley–Reisner ring

Toward the multigraded exhaust of Hochster's formula (`Tor_{1,σ}` is the *whole* degree-`σ` homology,
not just the syzygy summand), this file records the degree-`J` graded piece of the Stanley–Reisner ring
for a face `J`: it is the free rank-one `R`-module `R · ∏_{v∈J} x_v`, with the face detector
`srFaceDetector J` as the coordinate.

- `srFaceDetector_smul_prod` — the detector is a retraction: `srFaceDetector J (r · ∏_J x) = r`.
- `srMk_homogeneous_eq` — a degree-`J`-homogeneous Stanley–Reisner element (lift supported on the single
  squarefree exponent `indicatorExponent J`) equals `(srFaceDetector J p) · ∏_J x` — so the degree-`J`
  part is spanned by `∏_J x`, the fine-grading fact mathlib does not provide.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {R α : Type*} [CommRing R] [DecidableEq α]

omit [DecidableEq α] in
/-- The Stanley–Reisner quotient map is `R`-linear (via the `R`-algebra structure). -/
theorem srMk_smul (facets : Finset (Finset α)) (r : R) (Q : MvPolynomial α R) :
    (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) (r • Q) : stanleyReisnerRing R facets)
      = r • Ideal.Quotient.mk (stanleyReisnerIdeal R facets) Q := by
  rw [Algebra.smul_def, map_mul]
  exact (Algebra.smul_def r (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) Q)).symm

/-- **The face detector is a retraction onto `R · ∏_J x`.**  Reading the `∏_J x`-coordinate of a scalar
multiple returns the scalar. -/
theorem srFaceDetector_smul_prod (facets : Finset (Finset α)) {J : Finset α}
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J) (r : R) :
    srFaceDetector R facets J hJ (r • ∏ v ∈ J, srVertexX R facets v) = r := by
  rw [map_smul, srFaceDetector_prod, smul_eq_mul, mul_one]

/-- **Degree-`J`-homogeneous Stanley–Reisner elements are scalar multiples of `∏_J x`.**  If a lift `P`
is supported on the single squarefree exponent `indicatorExponent J` (i.e. `P` is homogeneous of
multidegree `J`), then its class equals `(srFaceDetector J ⟦P⟧) · ∏_J x`.  Hence the degree-`J` part of
the Stanley–Reisner ring is the free rank-one `R`-module `R · ∏_J x`. -/
theorem srMk_homogeneous_eq (facets : Finset (Finset α)) {J : Finset α}
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J) (P : MvPolynomial α R)
    (hP : P.support ⊆ {indicatorExponent J}) :
    (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P : stanleyReisnerRing R facets)
      = srFaceDetector R facets J hJ (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P)
          • ∏ v ∈ J, srVertexX R facets v := by
  rw [srFaceDetector_mk]
  have hPeq : P = monomial (indicatorExponent J) (coeff (indicatorExponent J) P) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.sum_subset hP (fun x _ hx => by
        simp only [MvPolynomial.mem_support_iff, not_not] at hx; rw [hx, monomial_zero]),
      Finset.sum_singleton]
  conv_lhs => rw [hPeq]
  rw [show (monomial (indicatorExponent J) (coeff (indicatorExponent J) P) : MvPolynomial α R)
        = (coeff (indicatorExponent J) P) • monomial (indicatorExponent J) 1 from by
      rw [smul_monomial, smul_eq_mul, mul_one], srMk_smul]
  congr 1
  rw [show (indicatorExponent J : α →₀ ℕ) = ∑ j ∈ J, Finsupp.single j 1 from rfl,
    ← GaloisForLFunctions.VeroneseIdeal.prod_X_eq_monomial, map_prod]
  exact Finset.prod_congr rfl fun v _ => rfl

/-- **Exhaust given componentwise homogeneity.**  A `1`-chain supported on `σ` whose every component
`a_v` (for `v ∈ σ`) is homogeneous of squarefree multidegree `σ ∖ v` — i.e. lifts to a polynomial
supported on the single exponent `indicatorExponent (σ.erase v)` — is exactly the hollow-simplex syzygy
read off by the face detectors.  This is the multigraded exhaust modulo the free-module grading: every
multidegree-`σ` `1`-chain is a syzygy, so the syzygy submodule is the *whole* degree-`σ` part of the
Koszul `1`-chains. -/
theorem srHollowSimplexSyzygyVec_of_homogeneous (facets : Finset (Finset α)) (σ : Finset α)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i))
    (a : α → stanleyReisnerRing R facets)
    (hom : ∀ v ∈ σ, ∃ A : MvPolynomial α R,
      a v = Ideal.Quotient.mk (stanleyReisnerIdeal R facets) A
        ∧ A.support ⊆ {indicatorExponent (σ.erase v)})
    (haout : ∀ v, v ∉ σ → a v = 0) :
    a = srHollowSimplexSyzygyVec R facets σ (fun v => if h : v ∈ σ then
      srFaceDetector R facets (σ.erase v) (hface v h) (a v) else 0) := by
  funext v
  by_cases hv : v ∈ σ
  · obtain ⟨A, hAeq, hAsupp⟩ := hom v hv
    simp only [srHollowSimplexSyzygyVec, if_pos hv, dif_pos hv]
    rw [hAeq]
    exact srMk_homogeneous_eq facets (hface v hv) A hAsupp
  · rw [haout v hv]
    simp only [srHollowSimplexSyzygyVec, if_neg hv]

/-- **Multigraded exhaust at degree 1.**  The class of any multidegree-`σ` `1`-chain (componentwise
homogeneous of degree `σ∖v`) in the first Koszul homology is a scalar multiple of the base syzygy class
— the scalar being the sum of its face-detector coordinates.  Since every such chain is a syzygy
(`srHollowSimplexSyzygyVec_of_homogeneous`) and syzygy classes are determined by their coefficient sum
(`srHollowSimplexSyzygy_mk_eq_iff`), the entire degree-`σ` part of `Tor₁` is `R·[base]`; combined with
the injective base embedding this is the full `Tor_{1,σ} ≅ R`. -/
theorem srHollowExhaust_class [Fintype α] (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : σ.Nonempty)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i))
    {i₀ : α} (hi₀ : i₀ ∈ σ) (a : α → stanleyReisnerRing R facets)
    (hom : ∀ v ∈ σ, ∃ A : MvPolynomial α R,
      a v = Ideal.Quotient.mk (stanleyReisnerIdeal R facets) A
        ∧ A.support ⊆ {indicatorExponent (σ.erase v)})
    (haout : ∀ v, v ∉ σ → a v = 0) :
    (Submodule.Quotient.mk a :
        (α → stanleyReisnerRing R facets) ⧸ srKoszulBoundaries facets)
      = (∑ v ∈ σ, if h : v ∈ σ then
            srFaceDetector R facets (σ.erase v) (hface v h) (a v) else 0)
          • srHollowBaseClass R facets σ i₀ := by
  conv_lhs => rw [srHollowSimplexSyzygyVec_of_homogeneous facets σ hface a hom haout]
  simp only [srHollowBaseClass]
  rw [← Submodule.Quotient.mk_smul, srHollowSimplexSyzygyVec_smul,
    srHollowSimplexSyzygy_mk_eq_iff facets σ hσ hface]
  simp only [Pi.smul_apply]
  rw [← Finset.smul_sum, Finset.sum_ite_eq' σ i₀ (fun _ => (1 : R)), if_pos hi₀, smul_eq_mul, mul_one]

end GaloisForLFunctions.HTGeometry
