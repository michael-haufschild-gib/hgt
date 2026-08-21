import GaloisForLFunctions.RHTower.EulerSquarefreeWickBinaryGaugeTower
import GaloisForLFunctions.Bottcher.DyadicMonodromy

/-!
# Orientation and auxiliary-tensor no-go for the Euler--Wick binary gauge tower

The arbitrary-rank EWQ source tower does not by itself produce divisor quantization.  Its full
interaction character has order two and already acts on one complex dimension at every rank.
Tensoring an arbitrary multiplicity space with the `2^r`-cell regular orbit makes the extended
dimension divisible by `2^r` tautologically, while imposing no divisibility on the original
multiplicity.  This separates a genuine completed cell landing from an auxiliary representation
enlargement.

The positive Hermitian shadow also erases every common unit phase.  In particular it cannot choose
between opposite even roots, and it erases the actual unbounded-order Böttcher dyadic phases.  Thus
the positive opposite-cell crossing from `EulerSquarefreeWickBinaryGaugeTower` cannot supply the
missing completed-root orientation.  Any surviving EWQ descent must act freely and
dimension-preservingly on the original Xi divisor module, rather than on an adjoined regular
representation.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Complex Hilbert energy of a finite binary regular-orbit coordinate vector. -/
def binaryGaugeHermitianEnergy {I : Type*} [Fintype I]
    (A : Finset I → ℂ) : ℝ :=
  ∑ S : Finset I, Complex.normSq (A S)

/-- The positive regular-orbit energy erases a common unit phase. -/
theorem binaryGaugeHermitianEnergy_phase_invariant
    {I : Type*} [Fintype I] (u : ℂ) (hu : Complex.normSq u = 1)
    (A : Finset I → ℂ) :
    binaryGaugeHermitianEnergy (fun S => u * A S) =
      binaryGaugeHermitianEnergy A := by
  classical
  rw [binaryGaugeHermitianEnergy, binaryGaugeHermitianEnergy]
  apply Finset.sum_congr rfl
  intro S hS
  rw [map_mul, hu, one_mul]

/-- In particular, opposite root orientations have identical positive source energy. -/
theorem binaryGaugeHermitianEnergy_neg
    {I : Type*} [Fintype I] (A : Finset I → ℂ) :
    binaryGaugeHermitianEnergy (fun S => -A S) = binaryGaugeHermitianEnergy A := by
  rw [binaryGaugeHermitianEnergy, binaryGaugeHermitianEnergy]
  apply Finset.sum_congr rfl
  intro S hS
  simp

/-- At every positive binary rank, negating a candidate cell root leaves its `2^r`-th power
unchanged. -/
theorem binaryGauge_evenRoot_neg_ambiguity
    {I : Type*} [Fintype I] [Nonempty I]
    (G : Finset I → ℂ) :
    (fun S => (-G S) ^ (2 ^ Fintype.card I)) =
      fun S => (G S) ^ (2 ^ Fintype.card I) := by
  funext S
  have hcard : 0 < Fintype.card I := Fintype.card_pos
  have heven : Even (2 ^ Fintype.card I) := by
    exact Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt hcard⟩
  rw [Even.neg_pow heven]

/-- The rank-`r` regular orbit tensored with an arbitrary multiplicity space has dimension
`2^r m`. -/
def binaryGaugeTensorLandingDimension (r m : ℕ) : ℕ :=
  2 ^ r * m

/-- Divisibility of the tensor-extended dimension is automatic for every original multiplicity. -/
theorem pow_two_dvd_binaryGaugeTensorLandingDimension (r m : ℕ) :
    2 ^ r ∣ binaryGaugeTensorLandingDimension r m := by
  exact dvd_mul_right _ _

/-- The automatic extended-space divisibility constrains no original multiplicity: multiplicity
one survives at every positive rank. -/
theorem binaryGaugeTensorLandingDimension_one_does_not_descend
    {r : ℕ} (hr : 0 < r) :
    2 ^ r ∣ binaryGaugeTensorLandingDimension r 1 ∧
      ¬2 ^ r ∣ 1 := by
  refine ⟨pow_two_dvd_binaryGaugeTensorLandingDimension r 1, ?_⟩
  intro h
  have hle := Nat.le_of_dvd (by omega : 0 < 1) h
  have hpow : 2 ≤ 2 ^ r := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    rw [pow_succ]
    omega
  omega

/-- Every binary gauge tower has only order-two scalar character values, independently of rank. -/
theorem binaryGaugeWalshCharacter_order_two
    {I : Type*} (B : Finset I) (x : I → Bool) :
    binaryGaugeWalshCharacter B x ^ 2 = 1 := by
  rw [pow_two, binaryGaugeWalshCharacter_sq]

/-- The full interaction character is already realized on one complex dimension at every rank.
Thus nontriviality or faithfulness of this character cannot force regular-orbit dimension. -/
def binaryGaugeTopCharacterOneDimensional {I : Type*} [Fintype I]
    (x : I → Bool) : ℂ →ₗ[ℂ] ℂ :=
  (GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x) • LinearMap.id

@[simp]
theorem binaryGaugeTopCharacterOneDimensional_apply
    {I : Type*} [Fintype I] (x : I → Bool) (z : ℂ) :
    binaryGaugeTopCharacterOneDimensional x z =
      GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x * z := by
  simp [binaryGaugeTopCharacterOneDimensional]

/-- Actual top-character translation is an involution even though it acts on a one-dimensional
space. -/
theorem binaryGaugeTopCharacterOneDimensional_sq
    {I : Type*} [Fintype I] (x : I → Bool) :
    (binaryGaugeTopCharacterOneDimensional x).comp
      (binaryGaugeTopCharacterOneDimensional x) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply,
    binaryGaugeTopCharacterOneDimensional_apply,
    binaryGaugeTopCharacterOneDimensional_apply,
    LinearMap.id_apply]
  have hsq :
      GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x *
        GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x = 1 := by
    classical
    rw [GaloisForLFunctions.HTGeometry.orientationWalshCharacter,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    cases x i <;>
      norm_num [GaloisForLFunctions.HTGeometry.primeDirichletSign]
  calc
    GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x *
        (GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x * z) =
      (GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x *
        GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x) * z := by ring
    _ = z := by rw [hsq]; simp

/-- At every dyadic depth, the positive shadow also erases the genuinely higher-order root
phase. -/
theorem binaryGaugeHermitianEnergy_dyadicPhase_invariant
    {I : Type*} [Fintype I] (k : ℕ) (A : Finset I → ℂ) :
    binaryGaugeHermitianEnergy
      (fun S => Bottcher.dyadicRoot k * A S) = binaryGaugeHermitianEnergy A := by
  apply binaryGaugeHermitianEnergy_phase_invariant
  have hpow : Bottcher.dyadicRoot k ^ (2 ^ k) = 1 := by
    rw [← Bottcher.orderOf_dyadicRoot_named k]
    exact pow_orderOf_eq_one _
  have hnorm : ‖Bottcher.dyadicRoot k‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow (pow_ne_zero k (by norm_num))
  rw [Complex.normSq_eq_norm_sq, hnorm]
  norm_num

end

end GaloisForLFunctions.RHTower
