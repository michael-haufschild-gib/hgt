import GaloisForLFunctions.RHTower.EulerSquarefreeWickBinaryGaugeTower

/-!
# External dynamics no-go laws for the Euler--Wick gauge tower

Two recent dynamical mechanisms suggest possible EWQ landings: support localization by a
nonnegative Lyapunov coboundary, and a meromorphic dynamical zeta built from a positive-entropy
full shift.  Both fail for exact structural reasons.

* EWQ all-negative translation is an involution.  Every everywhere nonnegative coboundary of an
  involution vanishes pointwise, whereas the EWQ opposite-cell crossing is strictly positive on
  every nonzero literal cell.
* A full shift uses ordered words.  Already at quadratic order its two distinct mixed words `xy`
  and `yx` collapse to the same commutative integer, giving mixed coefficient two instead of the
  Euler product's coefficient one.

Thus neither dynamical support localization nor transfer-zeta meromorphy supplies a
coefficient-faithful completed Xi landing.  The results do not exclude a non-involutive arithmetic
flow with an independently proved exact commutative Euler quotient.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Coboundary of a real observable along a self-map. -/
def dynamicalCoboundary {X : Type*} (T : X → X) (L : X → ℝ) (x : X) : ℝ :=
  L (T x) - L x

/-- An everywhere nonnegative coboundary of an involution vanishes pointwise. -/
theorem involutive_nonnegative_coboundary_eq_zero
    {X : Type*} {T : X → X} (hT : Function.Involutive T)
    (L : X → ℝ) (hnonneg : ∀ x, 0 ≤ dynamicalCoboundary T L x) (x : X) :
    dynamicalCoboundary T L x = 0 := by
  have hx := hnonneg x
  have hTx := hnonneg (T x)
  rw [dynamicalCoboundary, hT x] at hTx
  rw [dynamicalCoboundary] at hx ⊢
  linarith

/-- EWQ all-negative translation is an involution on the full regular orbit. -/
theorem binaryGaugeDoubleNegativeTranslation_functionInvolutive
    {I : Type*} :
    Function.Involutive
      (binaryGaugeDoubleNegativeTranslation : (Finset I → ℝ) → Finset I → ℝ) := by
  intro A
  exact binaryGaugeDoubleNegativeTranslation_involutive A

/-- No Lyapunov observable can realize the strictly positive EWQ opposite-cell crossing as an
everywhere nonnegative coboundary of the actual all-negative translation. -/
theorem no_nonnegativeCoboundary_realizes_binaryGaugeOppositeCrossing
    {I : Type*} [Fintype I] [Nonempty I] :
    ¬ ∃ L : (Finset I → ℝ) → ℝ,
      (∀ A, 0 ≤ dynamicalCoboundary binaryGaugeDoubleNegativeTranslation L A) ∧
      (∀ A, dynamicalCoboundary binaryGaugeDoubleNegativeTranslation L A =
        binaryGaugeKreinForm A (binaryGaugeDoubleNegativeTranslation A)) := by
  rintro ⟨L, hnonneg, hrealize⟩
  let A : Finset I → ℝ := binaryGaugePureCoordinates 1 (fun _ => false)
  have hzero : dynamicalCoboundary binaryGaugeDoubleNegativeTranslation L A = 0 :=
    involutive_nonnegative_coboundary_eq_zero
      binaryGaugeDoubleNegativeTranslation_functionInvolutive L hnonneg A
  have hpos : 0 < binaryGaugeKreinForm A (binaryGaugeDoubleNegativeTranslation A) := by
    exact binaryGaugeKreinForm_pure_doubleNegative_pos (by norm_num) (fun _ => false)
  rw [hrealize A] at hzero
  linarith

/-- Quadratic truncation of the full-shift/free-word zeta packet on two nonzero branches. -/
def freeWordQuadraticPacket (x y : ℂ) : ℂ :=
  1 + (x + y) + (x + y) ^ (2 : ℕ)

/-- Quadratic truncation of the commutative two-prime Euler packet. -/
def commutativeEulerQuadraticPacket (x y : ℂ) : ℂ :=
  1 + x + y + x ^ (2 : ℕ) + x * y + y ^ (2 : ℕ)

/-- The free-word packet has one extra mixed word: ordered words `xy` and `yx` collapse to the
same commutative integer, doubling its coefficient. -/
theorem freeWordQuadraticPacket_sub_commutativeEulerQuadraticPacket
    (x y : ℂ) :
    freeWordQuadraticPacket x y - commutativeEulerQuadraticPacket x y = x * y := by
  simp [freeWordQuadraticPacket, commutativeEulerQuadraticPacket]
  ring

/-- Therefore a full-shift transfer zeta cannot agree coefficient-faithfully with a two-prime
Euler product when both branch weights are nonzero. -/
theorem freeWordQuadraticPacket_ne_commutativeEulerQuadraticPacket
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    freeWordQuadraticPacket x y ≠ commutativeEulerQuadraticPacket x y := by
  intro heq
  have hzero : freeWordQuadraticPacket x y - commutativeEulerQuadraticPacket x y = 0 :=
    sub_eq_zero.mpr heq
  rw [freeWordQuadraticPacket_sub_commutativeEulerQuadraticPacket] at hzero
  exact (mul_ne_zero hx hy) hzero

end

end GaloisForLFunctions.RHTower
