import GaloisForLFunctions.RHTower.XiUnitDoubleCompletedBalancedResponseCoupling
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureHilbertMetric

/-!
# Pointed Dirichlet decomposition of the balanced completed response

The completed unit-to-double response was previously equipped with its unique finite balanced
coupling, but the quadratic pairing with the true physical aperture carrier was left unspecified.
Symmetry and the exact row marginals force that pairing: in the fine-minus-coarse orientation it
is an anchored marginal energy minus one half of a signed prime-ratio Dirichlet energy.

The anchor is essential.  Removing it leaves only pairwise differences and therefore loses the
common mode identified by the HTGeometry obstruction.  The result here is an unconditional exact
decomposition, not the still-open cofinal upper bound on the indefinite Dirichlet term.
-/

open scoped BigOperators RealInnerProductSpace

namespace RHTower

noncomputable section

/-! ## Generic finite pointed decomposition -/

/-- A symmetric finite coupling is determined in quadratic pairing by its row marginals and its
signed Dirichlet energy. -/
theorem finite_symmetric_coupling_inner_eq_marginal_sub_half_dirichlet
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Finset ι) (C : ι → ι → ℝ) (m : ι → ℝ) (φ : ι → E)
    (hsymm : ∀ p ∈ P, ∀ q ∈ P, C p q = C q p)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, C p q = m p) :
    (∑ p ∈ P, ∑ q ∈ P, C p q * inner ℝ (φ p) (φ q)) =
      (∑ p ∈ P, m p * ‖φ p‖ ^ 2) -
        (1 / 2 : ℝ) *
          ∑ p ∈ P, ∑ q ∈ P, C p q * ‖φ p - φ q‖ ^ 2 := by
  let L : ℝ := ∑ p ∈ P, ∑ q ∈ P, C p q * inner ℝ (φ p) (φ q)
  let A : ℝ := ∑ p ∈ P, m p * ‖φ p‖ ^ 2
  let D : ℝ := ∑ p ∈ P, ∑ q ∈ P, C p q * ‖φ p - φ q‖ ^ 2
  have hleft :
      (∑ p ∈ P, ∑ q ∈ P, C p q * ‖φ p‖ ^ 2) = A := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_mul, hrow p hp]
  have hright :
      (∑ p ∈ P, ∑ q ∈ P, C p q * ‖φ q‖ ^ 2) = A := by
    dsimp [A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    have hcol : (∑ p ∈ P, C p q) = m q := by
      calc
        (∑ p ∈ P, C p q) = ∑ p ∈ P, C q p := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hsymm p hp q hq
        _ = m q := hrow q hq
    rw [← Finset.sum_mul, hcol]
  have hD : D = 2 * A - 2 * L := by
    dsimp [D, L]
    calc
      (∑ p ∈ P, ∑ q ∈ P, C p q * ‖φ p - φ q‖ ^ 2) =
          (∑ p ∈ P, ∑ q ∈ P,
            ((C p q * ‖φ p‖ ^ 2 + C p q * ‖φ q‖ ^ 2) -
              2 * (C p q * inner ℝ (φ p) (φ q)))) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [norm_sub_sq_real]
        ring
      _ = (∑ p ∈ P, ∑ q ∈ P, C p q * ‖φ p‖ ^ 2) +
          (∑ p ∈ P, ∑ q ∈ P, C p q * ‖φ q‖ ^ 2) -
            2 * (∑ p ∈ P, ∑ q ∈ P,
              C p q * inner ℝ (φ p) (φ q)) := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
      _ = 2 * A - 2 *
          (∑ p ∈ P, ∑ q ∈ P,
            C p q * inner ℝ (φ p) (φ q)) := by
        rw [hleft, hright]
        ring
  change L = A - (1 / 2 : ℝ) * D
  rw [hD]
  ring

/-! ## Source-forced refinement coupling -/

/-- The fine-minus-coarse orientation of the existing completed balanced coupling. -/
def xiUnitDoubleCompletedRefinementCoupling
    (P : Finset Nat.Primes) (p q : Nat.Primes) : ℝ :=
  -xiUnitDoubleCompletedBalancedResponseCoupling P p q

/-- Its positive row marginal is the negative of the coarse-minus-fine fused current. -/
def xiUnitDoubleCompletedRefinementMarginal (p : Nat.Primes) : ℝ :=
  -xiUnitDoubleFusedPrimeResponseCurrent p

theorem xiUnitDoubleCompletedRefinementCoupling_symm
    (P : Finset Nat.Primes) (p q : Nat.Primes) :
    xiUnitDoubleCompletedRefinementCoupling P p q =
      xiUnitDoubleCompletedRefinementCoupling P q p := by
  rw [xiUnitDoubleCompletedRefinementCoupling,
    xiUnitDoubleCompletedRefinementCoupling,
    xiUnitDoubleCompletedBalancedResponseCoupling_symm]

theorem sum_xiUnitDoubleCompletedRefinementCoupling
    (P : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ P) :
    ∑ q ∈ P, xiUnitDoubleCompletedRefinementCoupling P p q =
      xiUnitDoubleCompletedRefinementMarginal p := by
  simp_rw [xiUnitDoubleCompletedRefinementCoupling]
  rw [Finset.sum_neg_distrib,
    sum_xiUnitDoubleCompletedBalancedResponseCoupling P p hp,
    xiUnitDoubleCompletedRefinementMarginal]

theorem xiUnitDoubleCompletedRefinementMarginal_eq
    (p : Nat.Primes) :
    xiUnitDoubleCompletedRefinementMarginal p =
      Real.log (p : ℝ) / ((p : ℝ) + 1) := by
  rw [xiUnitDoubleCompletedRefinementMarginal,
    xiUnitDoubleFusedPrimeResponseCurrent_eq]
  ring

/-- The physical endpoint marginal is the refinement marginal plus the valuation-resolved
trace-class correction after fusion. -/
theorem physicalPrimeEndpointWeight_eq_refinementMarginal_add_remainder
    (p : Nat.Primes) :
    physicalPrimeEndpointWeight p =
      xiUnitDoubleCompletedRefinementMarginal p +
        xiPhysicalEndpointResponseWeightRemainder p := by
  rw [xiUnitDoubleCompletedRefinementMarginal,
    physicalPrimeEndpointWeight_eq_neg_fusedResponse_add_remainder]

/-! ## The actual physical-aperture pairing -/

/-- Quadratic pairing of the refinement-oriented balanced completed response with the true
centered physical aperture carrier. -/
def xiUnitDoubleCompletedRefinementAperturePairing
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    xiUnitDoubleCompletedRefinementCoupling P p q *
      inner ℝ (xiPhysicalPrimeLogCenteredApertureCarrier A m k p)
        (xiPhysicalPrimeLogCenteredApertureCarrier A m k q)

/-- The signed prime-ratio Dirichlet energy forced by the same completed response. -/
def xiUnitDoubleCompletedRefinementApertureDirichletEnergy
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    xiUnitDoubleCompletedRefinementCoupling P p q *
      ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p -
        xiPhysicalPrimeLogCenteredApertureCarrier A m k q‖ ^ 2

/-- **Forced pointed Dirichlet decomposition.** The previously unspecified completed response
pairing is exactly its anchored source marginal minus half its indefinite prime-ratio energy. -/
theorem xiUnitDoubleCompletedRefinementAperturePairing_eq_marginal_sub_half_dirichlet
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiUnitDoubleCompletedRefinementAperturePairing P A m k =
      (∑ p ∈ P, xiUnitDoubleCompletedRefinementMarginal p *
        ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ ^ 2) -
      (1 / 2 : ℝ) *
        xiUnitDoubleCompletedRefinementApertureDirichletEnergy P A m k := by
  exact finite_symmetric_coupling_inner_eq_marginal_sub_half_dirichlet
    P (xiUnitDoubleCompletedRefinementCoupling P)
    xiUnitDoubleCompletedRefinementMarginal
    (xiPhysicalPrimeLogCenteredApertureCarrier A m k)
    (fun p _hp q _hq =>
      xiUnitDoubleCompletedRefinementCoupling_symm P p q)
    (sum_xiUnitDoubleCompletedRefinementCoupling P)

end

end RHTower
