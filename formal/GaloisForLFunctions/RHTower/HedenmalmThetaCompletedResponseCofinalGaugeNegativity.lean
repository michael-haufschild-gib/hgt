import GaloisForLFunctions.RHTower.HedenmalmThetaCompletedResponseMarginalGaugeNoGo
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointCofinalHolonomy

/-!
# Route P cofinal completed-gauge negativity

The completed endpoint coupling contains genuine off-diagonal information only in its
zero-marginal gauge.  On a two-prime packet that gauge is exactly the signed graph Laplacian

```text
[-c  c]
[ c -c],
```

where `c` is the completed pair response.  Its quadratic pairing is
`-c (phi_p - phi_r)^2`, while its signed Dirichlet form is
`2 c (phi_p - phi_r)^2`.

The source corpus supplies positive completed pair responses on arbitrarily late adjacent-prime
packets.  Hence the gauge has strict negative quadratic directions and strict positive Dirichlet
directions cofinally.  Universal positivity of the gauge pairing and universal negativity of its
Dirichlet term are therefore impossible producer signs.  Any surviving estimate must use a more
specific theta/entire cancellation than a sign of the completed endpoint response.
-/

open scoped BigOperators RealInnerProductSpace

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Quadratic form of the completed zero-marginal endpoint gauge on a finite prime packet. -/
def thetaPhysicalEndpointCompletedGaugeQuadraticForm
    (P : Finset Nat.Primes) (phi : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ r ∈ P,
    thetaPhysicalEndpointCompletedGaugeCoupling P p r * phi p * phi r

/-- Signed Dirichlet form of the same zero-marginal gauge. -/
def thetaPhysicalEndpointCompletedGaugeDirichletForm
    (P : Finset Nat.Primes) (phi : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ r ∈ P,
    thetaPhysicalEndpointCompletedGaugeCoupling P p r * (phi p - phi r) ^ 2

theorem thetaPhysicalEndpointCompletedGaugeCoupling_pair_left_self
    (p r : Nat.Primes) (hpr : p ≠ r) :
    thetaPhysicalEndpointCompletedGaugeCoupling {p, r} p p =
      -xiPhysicalEndpointCompletedPairResponse p r := by
  rw [thetaPhysicalEndpointCompletedGaugeCoupling,
    xiPhysicalEndpointCompletedBalancedCoupling,
    if_pos rfl, thetaPhysicalEndpointDiagonalCoupling, if_pos rfl]
  simp [hpr]

theorem thetaPhysicalEndpointCompletedGaugeCoupling_pair_right_self
    (p r : Nat.Primes) (hpr : p ≠ r) :
    thetaPhysicalEndpointCompletedGaugeCoupling {p, r} r r =
      -xiPhysicalEndpointCompletedPairResponse p r := by
  rw [thetaPhysicalEndpointCompletedGaugeCoupling,
    xiPhysicalEndpointCompletedBalancedCoupling,
    if_pos rfl, thetaPhysicalEndpointDiagonalCoupling, if_pos rfl]
  rw [show ({p, r} : Finset Nat.Primes).erase r = {p} by
    ext s
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hps | hrs⟩
      · exact hps
      · contradiction
    · intro hps
      subst s
      exact ⟨hpr, Or.inl rfl⟩]
  simp [xiPhysicalEndpointCompletedPairResponse_symm]

theorem thetaPhysicalEndpointCompletedGaugeCoupling_pair_offDiagonal
    (p r : Nat.Primes) (hpr : p ≠ r) :
    thetaPhysicalEndpointCompletedGaugeCoupling {p, r} p r =
      xiPhysicalEndpointCompletedPairResponse p r := by
  rw [thetaPhysicalEndpointCompletedGaugeCoupling,
    xiPhysicalEndpointCompletedBalancedCoupling, if_neg hpr,
    thetaPhysicalEndpointDiagonalCoupling, if_neg hpr]
  ring

/-- Exact negative graph-Laplacian law for a two-prime completed gauge packet. -/
theorem thetaPhysicalEndpointCompletedGaugeQuadraticForm_pair
    (p r : Nat.Primes) (hpr : p ≠ r) (phi : Nat.Primes → ℝ) :
    thetaPhysicalEndpointCompletedGaugeQuadraticForm {p, r} phi =
      -xiPhysicalEndpointCompletedPairResponse p r * (phi p - phi r) ^ 2 := by
  rw [thetaPhysicalEndpointCompletedGaugeQuadraticForm]
  simp only [Finset.sum_insert, Finset.mem_singleton, not_false_eq_true,
    Finset.sum_singleton, hpr]
  rw [thetaPhysicalEndpointCompletedGaugeCoupling_pair_left_self p r hpr,
    thetaPhysicalEndpointCompletedGaugeCoupling_pair_right_self p r hpr,
    thetaPhysicalEndpointCompletedGaugeCoupling_pair_offDiagonal p r hpr,
    thetaPhysicalEndpointCompletedGaugeCoupling_symm {p, r} r p,
    thetaPhysicalEndpointCompletedGaugeCoupling_pair_offDiagonal p r hpr]
  ring

/-- Exact positive graph-Dirichlet law dual to the preceding negative pairing. -/
theorem thetaPhysicalEndpointCompletedGaugeDirichletForm_pair
    (p r : Nat.Primes) (hpr : p ≠ r) (phi : Nat.Primes → ℝ) :
    thetaPhysicalEndpointCompletedGaugeDirichletForm {p, r} phi =
      2 * xiPhysicalEndpointCompletedPairResponse p r * (phi p - phi r) ^ 2 := by
  rw [thetaPhysicalEndpointCompletedGaugeDirichletForm]
  simp only [Finset.sum_insert, Finset.mem_singleton, not_false_eq_true,
    Finset.sum_singleton, hpr]
  rw [thetaPhysicalEndpointCompletedGaugeCoupling_pair_offDiagonal p r hpr,
    thetaPhysicalEndpointCompletedGaugeCoupling_symm {p, r} r p,
    thetaPhysicalEndpointCompletedGaugeCoupling_pair_offDiagonal p r hpr]
  ring

theorem thetaPhysicalEndpointCompletedGaugeQuadraticForm_pair_neg
    (p r : Nat.Primes) (hpr : p ≠ r)
    (hresponse : 0 < xiPhysicalEndpointCompletedPairResponse p r)
    (phi : Nat.Primes → ℝ) (hphi : phi p ≠ phi r) :
    thetaPhysicalEndpointCompletedGaugeQuadraticForm {p, r} phi < 0 := by
  rw [thetaPhysicalEndpointCompletedGaugeQuadraticForm_pair p r hpr phi]
  simpa only [neg_mul] using neg_neg_of_pos
    (mul_pos hresponse (sq_pos_of_ne_zero (sub_ne_zero.mpr hphi)))

theorem thetaPhysicalEndpointCompletedGaugeDirichletForm_pair_pos
    (p r : Nat.Primes) (hpr : p ≠ r)
    (hresponse : 0 < xiPhysicalEndpointCompletedPairResponse p r)
    (phi : Nat.Primes → ℝ) (hphi : phi p ≠ phi r) :
    0 < thetaPhysicalEndpointCompletedGaugeDirichletForm {p, r} phi := by
  rw [thetaPhysicalEndpointCompletedGaugeDirichletForm_pair p r hpr phi]
  exact mul_pos (mul_pos (by norm_num) hresponse)
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hphi))

/-- **Cofinal sign no-go.**  Beyond every prime index, an adjacent two-prime source packet has a
strictly negative completed-gauge quadratic direction and a strictly positive gauge Dirichlet
direction. -/
theorem exists_cofinal_thetaPhysicalEndpointCompletedGauge_negativeDirection
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      ∃ phi : Nat.Primes → ℝ,
        thetaPhysicalEndpointCompletedGaugeQuadraticForm
            {nthPrimeSubtype n, nthPrimeSubtype (n + 1)} phi < 0 ∧
          0 < thetaPhysicalEndpointCompletedGaugeDirichletForm
            {nthPrimeSubtype n, nthPrimeSubtype (n + 1)} phi := by
  obtain ⟨n, hn, hpq, _⟩ :=
    exists_cofinal_positive_physicalEndpoint_pair_triangle N
  let p := nthPrimeSubtype n
  let r := nthPrimeSubtype (n + 1)
  have hpr : p ≠ r := nthPrimeSubtype_injective.ne (by omega)
  refine ⟨n, hn, fun s => if s = p then 1 else 0, ?_, ?_⟩
  · change thetaPhysicalEndpointCompletedGaugeQuadraticForm {p, r} _ < 0
    apply thetaPhysicalEndpointCompletedGaugeQuadraticForm_pair_neg p r hpr hpq
    simp [Ne.symm hpr]
  · change 0 < thetaPhysicalEndpointCompletedGaugeDirichletForm {p, r} _
    apply thetaPhysicalEndpointCompletedGaugeDirichletForm_pair_pos p r hpr hpq
    simp [Ne.symm hpr]

end

end RHTower.HedenmalmThetaSource
