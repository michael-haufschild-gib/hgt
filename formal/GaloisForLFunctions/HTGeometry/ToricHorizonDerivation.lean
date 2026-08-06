import GaloisForLFunctions.HTGeometry.EigenvolumePointwiseLaw
import GaloisForLFunctions.HTGeometry.MonomialMapInjective
import GaloisForLFunctions.HTGeometry.RamificationPoleFixedPoint

/-!
# The toric horizon derived from the general local law

The order of the logarithmic volume form along a coordinate divisor can be computed directly, but
it can also be *derived*: the general local order law applies at that divisor with the ramification
index, the Jacobian order and the eigenvolume condition supplied by the monomial map, and the
expansion fixed-point argument then forces the order to be `-1`.

Running the general machinery on a model where the answer is independently known is a test of the
machinery, not a new computation of the answer.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial IsDiscreteValuationRing

variable {k : Type*} [Field k] {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem prod_X_ne_zero : (∏ j : σ, (X j : MvPolynomial σ k)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => (MvPolynomial.X_prime (R := k) (i := j)).ne_zero

theorem det_jacobian_monomialMap_ne_zero (e : σ → ℕ) (hu : ∀ i, IsUnit ((e i : k))) (i : σ) :
    (jacobian k σ (monomialMap k σ e)).det ≠ 0 := by
  intro h
  have hord := orderAt_coordDivisor_det_jacobian (k := k) e hu i
  rw [h, show orderAt (coordDivisor (k := k) i) (0 : MvPolynomial σ k) = ⊤ by
    simp only [orderAt, map_zero, AddValuation.map_zero]] at hord
  exact (ENat.top_ne_coe _) hord

/-- **The local order law at a coordinate divisor, obtained from the general law.** -/
theorem toric_shiftLaw (e : σ → ℕ) (he : ∀ i, 1 ≤ e i) (hu : ∀ i, IsUnit ((e i : k))) (i : σ) :
    formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j) (coordDivisor (k := k) i) + 1 =
      (e i : ℤ) *
        (formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j) (coordDivisor (k := k) i) + 1) := by
  set φ := (monomialMap k σ e).toRingHom with hφ
  set P := coordDivisor (k := k) i with hP
  have hQ : P.1 = Ideal.comap φ P.1 := (comap_monomialMap_span_X e he i).symm
  have hπ := irreducible_algebraMap_X (k := k) i
  have hram : addVal (Localization.AtPrime P.1)
      (localMapAt φ P P hQ
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime P.1) (X i))) = ((e i : ℕ) : ℕ∞) := by
    rw [localMapAt_algebraMap]
    exact orderAt_coordDivisor_monomialMap_X e i
  have hb : (∏ j : σ, (X j : MvPolynomial σ k)) ≠ 0 := prod_X_ne_zero
  have hJ := orderAt_coordDivisor_det_jacobian (k := k) e hu i
  have hJ0 := det_jacobian_monomialMap_ne_zero (k := k) e hu i
  obtain ⟨u, hunit⟩ := exists_unit_det_jacobian_mul_prod (R := k) e he hu
  have hφb : φ (∏ j : σ, (X j : MvPolynomial σ k)) ≠ 0 := by
    intro h
    refine hb (monomialMap_injective e he ?_)
    show monomialMap k σ e (∏ j : σ, X j) = monomialMap k σ e 0
    rw [map_zero]
    exact h
  have hφaJ : φ (1 : MvPolynomial σ k) * (jacobian k σ (monomialMap k σ e)).det ≠ 0 := by
    rw [map_one, one_mul]
    exact hJ0
  have hcross : φ (1 : MvPolynomial σ k) * (jacobian k σ (monomialMap k σ e)).det *
      (∏ j : σ, (X j : MvPolynomial σ k)) =
      ((u : MvPolynomial σ k) * 1) * φ (∏ j : σ, (X j : MvPolynomial σ k)) := by
    rw [map_one, one_mul, mul_one]
    exact hunit
  have heig := eigenvolume_condition_of_unit φ one_ne_zero hb hφaJ hφb u hcross P
  exact formOrder_eigen_shiftLaw_at φ P P hQ hπ (e i) (he i) hram one_ne_zero hb hJ heig

/-- **The horizon of the toric eigenvolume is reduced, derived from the general law.**  With every
exponent strictly larger than one the shifted law has the unique integral solution `-1`. -/
theorem toric_formOrder_eq_neg_one (e : σ → ℕ) (he : ∀ i, 1 < e i)
    (hu : ∀ i, IsUnit ((e i : k))) (i : σ) :
    formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j) (coordDivisor (k := k) i) = -1 :=
  ramificationShift_fixed_eq_neg_one (he i) (toric_shiftLaw e (fun j => (he j).le) hu i)

end GaloisForLFunctions.HTGeometry
