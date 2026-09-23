import GaloisForLFunctions.HTGeometry.AnharmonicMeromorphicSubstitution

/-!
# Anharmonic Chebyshev baseline and orientation Casimir

The first section formalizes the rational algebra used by Rouyea--Bourgeois (2026),
Lemmas 2.1--2.2 and equation (39): the order-three anharmonic invariant, reflection sign,
critical-value identity, and one-node Koebe factorization.  It does not assume their analytic
descent or RH equivalence theorem.

The second section attacks the orientation information discarded by the scalar invariant descent.
For cyclic-orbit values `(a,b,c)`, the standard coordinates are `p=a-b`, `q=b-c`.  Every
holomorphic quadratic form invariant under the cyclic action `(p,q) ↦ (q,-p-q)` is a scalar
multiple of `p²+pq+q²`.  That unique Casimir is isotropic over `ℂ`, so no scalar holomorphic
quadratic invariant can be a positive-definite orientation detector.  The positive survivor is the
doubled Hermitian energy

`‖a-b‖² + ‖b-c‖² + ‖c-a‖²`,

which is invariant under the full orbit permutation, nonnegative, and vanishes exactly when the
orbit collapses.  Thus an orientation-positive anharmonic Xi channel must retain a conjugate/doubled
standard sector; trivial-sector scalar compression cannot supply it.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Degree-three anharmonic quotient used in the Chebyshev-trace descent. -/
def chebyshevAnharmonicQ (s : ℂ) : ℂ :=
  ((s - 2) * (s + 1) * (2 * s - 1)) / (2 * s * (s - 1))

/-- Order-three generator `s ↦ (s-1)/s`. -/
def chebyshevAnharmonicW (s : ℂ) : ℂ := (s - 1) / s

/-- Functional-equation reflection. -/
def chebyshevAnharmonicSigma (s : ℂ) : ℂ := 1 - s

/-- The quotient is invariant under the order-three generator. -/
theorem chebyshevAnharmonicQ_w
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    chebyshevAnharmonicQ (chebyshevAnharmonicW s) = chebyshevAnharmonicQ s := by
  simp only [chebyshevAnharmonicQ, chebyshevAnharmonicW]
  field_simp [hs0, hs1]
  ring

/-- Reflection reverses the quotient orientation. -/
theorem chebyshevAnharmonicQ_sigma
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    chebyshevAnharmonicQ (chebyshevAnharmonicSigma s) = -chebyshevAnharmonicQ s := by
  simp only [chebyshevAnharmonicQ, chebyshevAnharmonicSigma]
  field_simp [hs0, hs1]
  ring

/-- Exact quotient identity with the unique nonzero finite critical value `27/4`. -/
theorem chebyshevAnharmonicQ_sq_add_criticalValue
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    chebyshevAnharmonicQ s ^ (2 : ℕ) + 27 / 4 =
      (s ^ (2 : ℕ) - s + 1) ^ (3 : ℕ) / (s ^ (2 : ℕ) * (s - 1) ^ (2 : ℕ)) := by
  simp only [chebyshevAnharmonicQ]
  field_simp [hs0, hs1]
  ring

/-- Endpoint-scaled Koebe map used by the trace generating function. -/
def chebyshevTraceKoebeMap (v : ℂ) : ℂ := 27 * v / (1 - v) ^ (2 : ℕ)

/-- One-node Koebe factorization: denominator poles are exactly preimages of descended zeros. -/
theorem chebyshevTraceKoebe_oneNode_factorization
    {v x : ℂ} (hv : v ≠ 1) (hx : x ≠ 0) :
    1 - 2 * v * (1 + 2 * (27 / 4) / x) + v ^ (2 : ℕ) =
      (1 - v) ^ (2 : ℕ) * (1 - chebyshevTraceKoebeMap v / x) := by
  simp only [chebyshevTraceKoebeMap]
  field_simp [hv, hx]
  ring

/-- Trivial isotypic coordinate of a cyclic orbit. -/
def anharmonicOrbitTrace (a b c : ℂ) : ℂ := a + b + c

/-- First standard-sector difference coordinate. -/
def anharmonicOrbitFirstDifference (a b : ℂ) : ℂ := a - b

/-- Second standard-sector difference coordinate. -/
def anharmonicOrbitSecondDifference (b c : ℂ) : ℂ := b - c

/-- Unique holomorphic quadratic Casimir on the standard sector, up to scale. -/
def anharmonicOrbitHolomorphicCasimir (a b c : ℂ) : ℂ :=
  let p := anharmonicOrbitFirstDifference a b
  let q := anharmonicOrbitSecondDifference b c
  p ^ (2 : ℕ) + p * q + q ^ (2 : ℕ)

/-- Cubic cyclic orientation: invariant under the cycle and odd under reflection. -/
def anharmonicOrbitChirality (a b c : ℂ) : ℂ :=
  let p := anharmonicOrbitFirstDifference a b
  let q := anharmonicOrbitSecondDifference b c
  p * q * (p + q)

/-- A general holomorphic quadratic form on the two standard difference coordinates. -/
def anharmonicStandardQuadratic (A B C p q : ℂ) : ℂ :=
  A * p ^ (2 : ℕ) + B * p * q + C * q ^ (2 : ℕ)

/-- Cyclic invariance classifies every holomorphic quadratic form on the standard sector:
its three coefficients must coincide. -/
theorem anharmonicStandardQuadratic_coefficients_of_cyclic
    {A B C : ℂ}
    (hcycle : ∀ p q : ℂ,
      anharmonicStandardQuadratic A B C q (-p - q) =
        anharmonicStandardQuadratic A B C p q) :
    A = B ∧ B = C := by
  have h10 := hcycle 1 0
  have h01 := hcycle 0 1
  simp only [anharmonicStandardQuadratic] at h10 h01
  constructor
  · linear_combination h01
  · linear_combination -h01 - h10

/-- Consequently the holomorphic Casimir is the unique cyclic-invariant quadratic form, up to
scale. -/
theorem anharmonicStandardQuadratic_eq_casimir_of_cyclic
    {A B C : ℂ}
    (hcycle : ∀ p q : ℂ,
      anharmonicStandardQuadratic A B C q (-p - q) =
        anharmonicStandardQuadratic A B C p q)
    (p q : ℂ) :
    anharmonicStandardQuadratic A B C p q = A * (p ^ (2 : ℕ) + p * q + q ^ (2 : ℕ)) := by
  obtain ⟨hAB, hBC⟩ := anharmonicStandardQuadratic_coefficients_of_cyclic hcycle
  subst B
  subst C
  simp only [anharmonicStandardQuadratic]
  ring

theorem anharmonicOrbitHolomorphicCasimir_cyclic (a b c : ℂ) :
    anharmonicOrbitHolomorphicCasimir b c a =
      anharmonicOrbitHolomorphicCasimir a b c := by
  simp only [anharmonicOrbitHolomorphicCasimir,
    anharmonicOrbitFirstDifference, anharmonicOrbitSecondDifference]
  ring

theorem anharmonicOrbitHolomorphicCasimir_reflection (a b c : ℂ) :
    anharmonicOrbitHolomorphicCasimir a c b =
      anharmonicOrbitHolomorphicCasimir a b c := by
  simp only [anharmonicOrbitHolomorphicCasimir,
    anharmonicOrbitFirstDifference, anharmonicOrbitSecondDifference]
  ring

theorem anharmonicOrbitChirality_cyclic (a b c : ℂ) :
    anharmonicOrbitChirality b c a = anharmonicOrbitChirality a b c := by
  simp only [anharmonicOrbitChirality,
    anharmonicOrbitFirstDifference, anharmonicOrbitSecondDifference]
  ring

theorem anharmonicOrbitChirality_reflection (a b c : ℂ) :
    anharmonicOrbitChirality a c b = -anharmonicOrbitChirality a b c := by
  simp only [anharmonicOrbitChirality,
    anharmonicOrbitFirstDifference, anharmonicOrbitSecondDifference]
  ring

theorem anharmonicOrbit_reconstruct_first (a b c : ℂ) :
    a = (anharmonicOrbitTrace a b c +
        2 * anharmonicOrbitFirstDifference a b +
        anharmonicOrbitSecondDifference b c) / 3 := by
  simp only [anharmonicOrbitTrace, anharmonicOrbitFirstDifference,
    anharmonicOrbitSecondDifference]
  ring

theorem anharmonicOrbit_reconstruct_second (a b c : ℂ) :
    b = (anharmonicOrbitTrace a b c -
        anharmonicOrbitFirstDifference a b +
        anharmonicOrbitSecondDifference b c) / 3 := by
  simp only [anharmonicOrbitTrace, anharmonicOrbitFirstDifference,
    anharmonicOrbitSecondDifference]
  ring

theorem anharmonicOrbit_reconstruct_third (a b c : ℂ) :
    c = (anharmonicOrbitTrace a b c -
        anharmonicOrbitFirstDifference a b -
        2 * anharmonicOrbitSecondDifference b c) / 3 := by
  simp only [anharmonicOrbitTrace, anharmonicOrbitFirstDifference,
    anharmonicOrbitSecondDifference]
  ring

/-- Positive doubled-sector energy, retaining conjugate information discarded by holomorphic
scalar compression. -/
def anharmonicOrbitHermitianEnergy (a b c : ℂ) : ℝ :=
  ‖a - b‖ ^ (2 : ℕ) + ‖b - c‖ ^ (2 : ℕ) + ‖c - a‖ ^ (2 : ℕ)

theorem anharmonicOrbitHermitianEnergy_cyclic (a b c : ℂ) :
    anharmonicOrbitHermitianEnergy b c a = anharmonicOrbitHermitianEnergy a b c := by
  simp only [anharmonicOrbitHermitianEnergy]
  ring

theorem anharmonicOrbitHermitianEnergy_reflection (a b c : ℂ) :
    anharmonicOrbitHermitianEnergy a c b = anharmonicOrbitHermitianEnergy a b c := by
  simp only [anharmonicOrbitHermitianEnergy, norm_sub_rev]
  ring

theorem anharmonicOrbitHermitianEnergy_nonneg (a b c : ℂ) :
    0 ≤ anharmonicOrbitHermitianEnergy a b c := by
  simp only [anharmonicOrbitHermitianEnergy]
  positivity

theorem anharmonicOrbitHermitianEnergy_eq_zero_iff (a b c : ℂ) :
    anharmonicOrbitHermitianEnergy a b c = 0 ↔ a = b ∧ b = c := by
  constructor
  · intro h
    have hab : ‖a - b‖ ^ (2 : ℕ) = 0 := by
      simp only [anharmonicOrbitHermitianEnergy] at h
      nlinarith [sq_nonneg ‖b - c‖, sq_nonneg ‖c - a‖]
    have hbc : ‖b - c‖ ^ (2 : ℕ) = 0 := by
      simp only [anharmonicOrbitHermitianEnergy] at h
      nlinarith [sq_nonneg ‖a - b‖, sq_nonneg ‖c - a‖]
    constructor
    · exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hab))
    · exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hbc))
  · rintro ⟨rfl, rfl⟩
    simp [anharmonicOrbitHermitianEnergy]

/-- One primitive cubic direction exhibiting isotropy of the holomorphic Casimir. -/
def anharmonicIsotropicRoot : ℂ := (-1 + Complex.I * Real.sqrt 3) / 2

theorem anharmonicIsotropicRoot_sq_add_self_add_one :
    anharmonicIsotropicRoot ^ (2 : ℕ) + anharmonicIsotropicRoot + 1 = 0 := by
  have hsqrt : (Real.sqrt 3) ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  rw [anharmonicIsotropicRoot]
  field_simp
  ring_nf
  have hsqrtC : ((Real.sqrt 3 : ℂ) ^ (2 : ℕ)) = 3 := by exact_mod_cast hsqrt
  all_goals rw [hsqrtC]
  all_goals norm_num

theorem anharmonicIsotropicRoot_ne_zero : anharmonicIsotropicRoot ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [anharmonicIsotropicRoot] at hre

/-- Every cyclic-invariant holomorphic quadratic form is isotropic on a nonzero standard vector.
Thus no scalar holomorphic quadratic invariant can be a positive-definite orientation energy. -/
theorem exists_nonzero_standardPair_anharmonicStandardQuadratic_eq_zero
    {A B C : ℂ}
    (hcycle : ∀ p q : ℂ,
      anharmonicStandardQuadratic A B C q (-p - q) =
        anharmonicStandardQuadratic A B C p q) :
    ∃ p q : ℂ, (p ≠ 0 ∨ q ≠ 0) ∧ anharmonicStandardQuadratic A B C p q = 0 := by
  refine ⟨anharmonicIsotropicRoot, 1, Or.inr one_ne_zero, ?_⟩
  rw [anharmonicStandardQuadratic_eq_casimir_of_cyclic hcycle]
  rw [show anharmonicIsotropicRoot ^ (2 : ℕ) + anharmonicIsotropicRoot * 1 + 1 ^ (2 : ℕ) = 0 by
    simpa using anharmonicIsotropicRoot_sq_add_self_add_one]
  simp

theorem exists_noncollapsed_anharmonicOrbit_holomorphicCasimir_eq_zero :
    ∃ a b c : ℂ,
      ¬ (a = b ∧ b = c) ∧ anharmonicOrbitHolomorphicCasimir a b c = 0 := by
  let p := anharmonicIsotropicRoot
  refine ⟨1 + p, 1, 0, ?_, ?_⟩
  · intro h
    have hp : p = 0 := by linear_combination h.1
    exact anharmonicIsotropicRoot_ne_zero hp
  · simp only [anharmonicOrbitHolomorphicCasimir,
      anharmonicOrbitFirstDifference, anharmonicOrbitSecondDifference]
    dsimp only [p]
    convert anharmonicIsotropicRoot_sq_add_self_add_one using 1
    ring

end

end RHTower
