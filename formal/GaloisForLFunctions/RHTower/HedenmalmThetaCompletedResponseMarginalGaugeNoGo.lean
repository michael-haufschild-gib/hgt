import GaloisForLFunctions.RHTower.HedenmalmThetaPhysicalEndpointCompletedResponseWardBridge

/-!
# Route P completed-response marginal gauge no-go

The completed physical-endpoint coupling gave an exact decomposition of every Route P packet into
response pairing plus one half signed Dirichlet energy.  That decomposition does not by itself use
the completed endpoint kernel: for every symmetric finite coupling, the same combination depends
only on its row marginal.

This file isolates the resulting gauge law.  The completed coupling differs from the diagonal
physical-marginal coupling by a symmetric zero-marginal response.  Its quadratic pairing and
Dirichlet energy cancel exactly in the Ward budget.  Thus the endpoint kernel can prove Route P
only through a separate sign or coercivity theorem for one summand; bounding the combined budget
merely restates the marginal harmonic-energy problem.
-/

open scoped BigOperators RealInnerProductSpace

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- The pairing-plus-half-Dirichlet budget of a symmetric coupling is fixed entirely by its row
marginal. -/
theorem finite_symmetric_coupling_budget_eq_marginal
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Finset ι) (C : ι → ι → ℝ) (m : ι → ℝ) (φ : ι → E)
    (hsymm : ∀ p ∈ P, ∀ r ∈ P, C p r = C r p)
    (hrow : ∀ p ∈ P, ∑ r ∈ P, C p r = m p) :
    (∑ p ∈ P, ∑ r ∈ P, C p r * inner ℝ (φ p) (φ r)) +
        (1 / 2 : ℝ) *
          ∑ p ∈ P, ∑ r ∈ P, C p r * ‖φ p - φ r‖ ^ (2 : ℕ) =
      ∑ p ∈ P, m p * ‖φ p‖ ^ (2 : ℕ) := by
  rw [finite_symmetric_coupling_inner_eq_marginal_sub_half_dirichlet
    P C m φ hsymm hrow]
  ring

/-- Two symmetric couplings with the same finite row marginal have identical
pairing-plus-half-Dirichlet budgets. -/
theorem finite_symmetric_same_marginal_budget_eq
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Finset ι) (C D : ι → ι → ℝ) (m : ι → ℝ) (φ : ι → E)
    (hCsymm : ∀ p ∈ P, ∀ r ∈ P, C p r = C r p)
    (hCrow : ∀ p ∈ P, ∑ r ∈ P, C p r = m p)
    (hDsymm : ∀ p ∈ P, ∀ r ∈ P, D p r = D r p)
    (hDrow : ∀ p ∈ P, ∑ r ∈ P, D p r = m p) :
    (∑ p ∈ P, ∑ r ∈ P, C p r * inner ℝ (φ p) (φ r)) +
        (1 / 2 : ℝ) *
          ∑ p ∈ P, ∑ r ∈ P, C p r * ‖φ p - φ r‖ ^ (2 : ℕ) =
      (∑ p ∈ P, ∑ r ∈ P, D p r * inner ℝ (φ p) (φ r)) +
        (1 / 2 : ℝ) *
          ∑ p ∈ P, ∑ r ∈ P, D p r * ‖φ p - φ r‖ ^ (2 : ℕ) := by
  rw [finite_symmetric_coupling_budget_eq_marginal P C m φ hCsymm hCrow,
    finite_symmetric_coupling_budget_eq_marginal P D m φ hDsymm hDrow]

/-- Purely diagonal coupling carrying the same physical endpoint marginal as the completed
response. -/
def thetaPhysicalEndpointDiagonalCoupling
    (p r : Nat.Primes) : ℝ :=
  if p = r then physicalPrimeEndpointWeight p else 0

theorem thetaPhysicalEndpointDiagonalCoupling_symm
    (p r : Nat.Primes) :
    thetaPhysicalEndpointDiagonalCoupling p r =
      thetaPhysicalEndpointDiagonalCoupling r p := by
  by_cases hpr : p = r
  · subst r
    rfl
  · rw [thetaPhysicalEndpointDiagonalCoupling, if_neg hpr,
      thetaPhysicalEndpointDiagonalCoupling, if_neg (Ne.symm hpr)]

theorem sum_thetaPhysicalEndpointDiagonalCoupling
    (P : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ P) :
    ∑ r ∈ P, thetaPhysicalEndpointDiagonalCoupling p r =
      physicalPrimeEndpointWeight p := by
  simp [thetaPhysicalEndpointDiagonalCoupling, hp]

/-- The completed response relative to its diagonal marginal representative. -/
def thetaPhysicalEndpointCompletedGaugeCoupling
    (P : Finset Nat.Primes) (p r : Nat.Primes) : ℝ :=
  xiPhysicalEndpointCompletedBalancedCoupling P p r -
    thetaPhysicalEndpointDiagonalCoupling p r

theorem thetaPhysicalEndpointCompletedGaugeCoupling_symm
    (P : Finset Nat.Primes) (p r : Nat.Primes) :
    thetaPhysicalEndpointCompletedGaugeCoupling P p r =
      thetaPhysicalEndpointCompletedGaugeCoupling P r p := by
  rw [thetaPhysicalEndpointCompletedGaugeCoupling,
    thetaPhysicalEndpointCompletedGaugeCoupling,
    xiPhysicalEndpointCompletedBalancedCoupling_symm P p r,
    thetaPhysicalEndpointDiagonalCoupling_symm p r]

/-- Completed non-diagonal response has zero row marginal after its physical diagonal
representative is removed. -/
theorem sum_thetaPhysicalEndpointCompletedGaugeCoupling
    (P : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ P) :
    ∑ r ∈ P, thetaPhysicalEndpointCompletedGaugeCoupling P p r = 0 := by
  simp_rw [thetaPhysicalEndpointCompletedGaugeCoupling, Finset.sum_sub_distrib]
  rw [sum_xiPhysicalEndpointCompletedBalancedCoupling P p hp,
    sum_thetaPhysicalEndpointDiagonalCoupling P p hp]
  ring

/-- Quadratic pairing of the zero-marginal completed response gauge. -/
def thetaPhysicalEndpointCompletedGaugePairing
    (P : Finset Nat.Primes) (q : XiZeroCopy) : ℝ :=
  ∑ p ∈ P, ∑ r ∈ P,
    thetaPhysicalEndpointCompletedGaugeCoupling P p r *
      thetaPhysicalEndpointNormalizedHalfDensity p q *
      thetaPhysicalEndpointNormalizedHalfDensity r q

/-- Signed Dirichlet energy of the zero-marginal completed response gauge. -/
def thetaPhysicalEndpointCompletedGaugeDirichletEnergy
    (P : Finset Nat.Primes) (q : XiZeroCopy) : ℝ :=
  ∑ p ∈ P, ∑ r ∈ P,
    thetaPhysicalEndpointCompletedGaugeCoupling P p r *
      (thetaPhysicalEndpointNormalizedHalfDensity p q -
        thetaPhysicalEndpointNormalizedHalfDensity r q) ^ (2 : ℕ)

/-- **Marginal-gauge no-go.**  The entire completed response beyond its physical row marginal
cancels from the Route P Ward budget. -/
theorem thetaPhysicalEndpointCompletedGaugePairing_add_half_dirichlet_eq_zero
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedGaugePairing P q +
        (1 / 2 : ℝ) *
          thetaPhysicalEndpointCompletedGaugeDirichletEnergy P q = 0 := by
  have h := finite_symmetric_coupling_budget_eq_marginal
    P (thetaPhysicalEndpointCompletedGaugeCoupling P) (fun _ : Nat.Primes => 0)
    (fun p : Nat.Primes => thetaPhysicalEndpointNormalizedHalfDensity p q)
    (fun p _hp r _hr => thetaPhysicalEndpointCompletedGaugeCoupling_symm P p r)
    (sum_thetaPhysicalEndpointCompletedGaugeCoupling P)
  simpa [thetaPhysicalEndpointCompletedGaugePairing,
    thetaPhysicalEndpointCompletedGaugeDirichletEnergy,
    real_inner_comm, Real.norm_eq_abs, sq_abs,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- Equivalently, gauge pairing is forced to be negative one half of gauge Dirichlet energy. -/
theorem thetaPhysicalEndpointCompletedGaugePairing_eq_neg_half_dirichlet
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedGaugePairing P q =
      -(1 / 2 : ℝ) *
        thetaPhysicalEndpointCompletedGaugeDirichletEnergy P q := by
  have h :=
    thetaPhysicalEndpointCompletedGaugePairing_add_half_dirichlet_eq_zero P q
  linarith

/-- The completed endpoint Ward budget is identical to the budget of the diagonal marginal
coupling.  Therefore the combined budget contains no source-specific off-diagonal information. -/
theorem thetaPhysicalEndpointCompletedResponseBudget_eq_diagonalMarginalBudget
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedResponsePairing P q +
        (1 / 2 : ℝ) * thetaPhysicalEndpointCompletedResponseDirichletEnergy P q =
      ∑ p ∈ P, ∑ r ∈ P,
        thetaPhysicalEndpointDiagonalCoupling p r *
          thetaPhysicalEndpointNormalizedHalfDensity p q *
          thetaPhysicalEndpointNormalizedHalfDensity r q := by
  rw [← thetaMobiusPrimeNormalProfilePacketEnergy_eq_completedResponseBudget]
  rw [thetaMobiusPrimeNormalProfilePacketEnergy]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single p]
  · rw [thetaPhysicalEndpointDiagonalCoupling, if_pos rfl]
    calc
      thetaMobiusPrimeNormalProfilePositiveGauge p q *
          thetaMobiusPrimeNormalReflectionProfile p q ^ (2 : ℕ) =
        thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ (2 : ℕ) :=
          (thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq p q).symm
      _ = physicalPrimeEndpointWeight p *
          thetaPhysicalEndpointNormalizedHalfDensity p q ^ (2 : ℕ) :=
        (physicalPrimeEndpointWeight_mul_normalizedHalfDensity_sq p q).symm
      _ = physicalPrimeEndpointWeight p *
          thetaPhysicalEndpointNormalizedHalfDensity p q *
            thetaPhysicalEndpointNormalizedHalfDensity p q := by ring
  · intro r hr hrp
    rw [thetaPhysicalEndpointDiagonalCoupling, if_neg (fun h => hrp h.symm)]
    simp
  · exact fun h => (h hp).elim

end

end RHTower.HedenmalmThetaSource
