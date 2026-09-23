import GaloisForLFunctions.RHTower.FormationBlowupProjectiveKinkBarrierTransgression
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.RHTower.SoninResidualApertureHilbertSchmidtContinuity
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant
import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound
import GaloisForLFunctions.RHTower.DirectSubunitEscapeCapacityFusion
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed

/-!
# Reciprocal four-channel Krein--nuclear renormalization

The compact theta frame and phase-matched split frame use reciprocal prime coordinates.  This
module constructs their literal four-channel synthesis over every finite history--prime packet.
Its indefinite Gram is exactly the finite compression of the fixed positive trace-one source,
and these Grams recover the source in trace norm along every cofinal packet exhaustion.

Every declaration is unconditional.  No divisor, zero, ordinate, or RH hypothesis occurs here.
-/

open Filter Topology BigOperators
open scoped InnerProductSpace ComplexOrder

namespace RHTower

open ContinuousLinearMap

noncomputable section

/-- Source rates used by the reciprocal frame are fixed before any divisor data. -/
structure ReciprocalFormationRate where
  value : ℝ
  pos : 0 < value
  lt_half : value < 1 / 2

instance : Coe ReciprocalFormationRate ℝ := ⟨ReciprocalFormationRate.value⟩

theorem reciprocalFormationRate_ne_zero (δ : ReciprocalFormationRate) :
    (δ : ℝ) ≠ 0 := δ.pos.ne'

def reciprocalPrimeLog (p : Nat.Primes) : ℝ := Real.log (p : ℝ)

def reciprocalCompactCoordinate (δ : ℝ) (p : Nat.Primes) : ℝ :=
  δ * reciprocalPrimeLog p

def reciprocalSplitCoordinate (δ : ℝ) (p : Nat.Primes) : ℝ :=
  reciprocalPrimeLog p / δ

def reciprocalVisibility (δ : ℝ) (p : Nat.Primes) : ℝ :=
  formationVisibility (2 * reciprocalCompactCoordinate δ p)

def reciprocalContrast (δ : ℝ) (p : Nat.Primes) : ℝ :=
  formationContrast (2 * reciprocalCompactCoordinate δ p)

def reciprocalHyperbolic (δ : ℝ) (p : Nat.Primes) : ℝ :=
  reciprocalSplitCoordinate δ p ^ (2 : ℕ)

def reciprocalKreinCompanion (δ : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (reciprocalHyperbolic δ p ^ (2 : ℕ) - 1)

/-- The two reciprocal coordinates multiply to the square of the prime clock. -/
theorem reciprocalCompact_mul_split
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalCompactCoordinate δ p * reciprocalSplitCoordinate δ p =
      reciprocalPrimeLog p ^ (2 : ℕ) := by
  rw [reciprocalCompactCoordinate, reciprocalSplitCoordinate]
  field_simp [reciprocalFormationRate_ne_zero δ]

theorem two_thirds_lt_reciprocalPrimeLog (p : Nat.Primes) :
    (2 / 3 : ℝ) < reciprocalPrimeLog p := by
  simpa [reciprocalPrimeLog, xiGammaEulerPrimitiveLogFrequency,
    xiGammaEulerValuationNat] using
    two_thirds_lt_xiGammaEulerPrimitiveLogFrequency (p, 0)

theorem one_lt_reciprocalSplitCoordinate
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    1 < reciprocalSplitCoordinate δ p := by
  rw [reciprocalSplitCoordinate, one_lt_div δ.pos]
  have hp := two_thirds_lt_reciprocalPrimeLog p
  exact δ.lt_half.trans (by linarith)

/-- Compact theta polarization. -/
theorem reciprocalVisibility_sq_add_contrast_sq
    (δ : ℝ) (p : Nat.Primes) :
    reciprocalVisibility δ p ^ (2 : ℕ) + reciprocalContrast δ p ^ (2 : ℕ) = 1 := by
  simpa [reciprocalVisibility, reciprocalContrast] using
    formationVisibility_sq_add_contrast_sq
      (2 * reciprocalCompactCoordinate δ p)

theorem one_lt_reciprocalHyperbolic
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    1 < reciprocalHyperbolic δ p := by
  rw [reciprocalHyperbolic]
  nlinarith [one_lt_reciprocalSplitCoordinate δ p]

theorem reciprocalKreinCompanion_sq
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalKreinCompanion δ p ^ (2 : ℕ) = reciprocalHyperbolic δ p ^ (2 : ℕ) - 1 := by
  rw [reciprocalKreinCompanion, Real.sq_sqrt]
  nlinarith [one_lt_reciprocalHyperbolic δ p]

/-- Split completion polarization. -/
theorem reciprocalHyperbolic_sq_sub_kreinCompanion_sq
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalHyperbolic δ p ^ (2 : ℕ) - reciprocalKreinCompanion δ p ^ (2 : ℕ) = 1 := by
  rw [reciprocalKreinCompanion_sq]
  ring

/-- The local four-channel vector has exact `J = diag(1,1,-1,-1)` charge one. -/
theorem reciprocalFourChannel_charge
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    (reciprocalVisibility δ p * reciprocalHyperbolic δ p) ^ (2 : ℕ) +
        (reciprocalContrast δ p * reciprocalHyperbolic δ p) ^ (2 : ℕ) -
        (reciprocalVisibility δ p * reciprocalKreinCompanion δ p) ^ (2 : ℕ) -
        (reciprocalContrast δ p * reciprocalKreinCompanion δ p) ^ (2 : ℕ) = 1 := by
  have hc := reciprocalVisibility_sq_add_contrast_sq (δ : ℝ) p
  have hh := reciprocalHyperbolic_sq_sub_kreinCompanion_sq δ p
  nlinarith

/-- Ordinary positive four-channel energy is the split factor `2h²-1`. -/
theorem reciprocalFourChannel_positiveEnergy
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    (reciprocalVisibility δ p * reciprocalHyperbolic δ p) ^ (2 : ℕ) +
        (reciprocalContrast δ p * reciprocalHyperbolic δ p) ^ (2 : ℕ) +
        (reciprocalVisibility δ p * reciprocalKreinCompanion δ p) ^ (2 : ℕ) +
        (reciprocalContrast δ p * reciprocalKreinCompanion δ p) ^ (2 : ℕ) =
      2 * reciprocalHyperbolic δ p ^ (2 : ℕ) - 1 := by
  have hc := reciprocalVisibility_sq_add_contrast_sq (δ : ℝ) p
  have hh := reciprocalHyperbolic_sq_sub_kreinCompanion_sq δ p
  nlinarith

/-! ### Reflection and the scalar anomaly shadow -/

theorem reciprocalCompactCoordinate_neg (δ : ℝ) (p : Nat.Primes) :
    reciprocalCompactCoordinate (-δ) p = -reciprocalCompactCoordinate δ p := by
  simp [reciprocalCompactCoordinate]

theorem reciprocalSplitCoordinate_neg (δ : ℝ) (p : Nat.Primes) :
    reciprocalSplitCoordinate (-δ) p = -reciprocalSplitCoordinate δ p := by
  rw [reciprocalSplitCoordinate, reciprocalSplitCoordinate, div_neg]

theorem reciprocalVisibility_neg (δ : ℝ) (p : Nat.Primes) :
    reciprocalVisibility (-δ) p = reciprocalVisibility δ p := by
  simp [reciprocalVisibility, reciprocalCompactCoordinate,
    formationVisibility_neg]

theorem reciprocalContrast_neg (δ : ℝ) (p : Nat.Primes) :
    reciprocalContrast (-δ) p = -reciprocalContrast δ p := by
  simp [reciprocalContrast, reciprocalCompactCoordinate,
    formationContrast_neg]

theorem reciprocalHyperbolic_neg (δ : ℝ) (p : Nat.Primes) :
    reciprocalHyperbolic (-δ) p = reciprocalHyperbolic δ p := by
  rw [reciprocalHyperbolic, reciprocalHyperbolic,
    reciprocalSplitCoordinate_neg]
  ring

theorem reciprocalKreinCompanion_neg (δ : ℝ) (p : Nat.Primes) :
    reciprocalKreinCompanion (-δ) p = reciprocalKreinCompanion δ p := by
  simp [reciprocalKreinCompanion, reciprocalHyperbolic_neg]

def reciprocalPrimitiveCubicWeight (p : Nat.Primes) : ℝ :=
  115 / (864 * (p : ℝ) * reciprocalPrimeLog p ^ (2 : ℕ))

theorem reciprocalPrimitiveCubicWeight_eq_corpus (p : Nat.Primes) :
    reciprocalPrimitiveCubicWeight p =
      xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0) := by
  rw [xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero]
  simp [reciprocalPrimitiveCubicWeight, reciprocalPrimeLog]
  ring

theorem reciprocalPrimitiveCubicWeight_mul_hyperbolic_sq
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalPrimitiveCubicWeight p * reciprocalHyperbolic δ p ^ (2 : ℕ) =
      115 * reciprocalPrimeLog p ^ (2 : ℕ) / (864 * (δ : ℝ) ^ (4 : ℕ) * (p : ℝ)) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hl : reciprocalPrimeLog p ≠ 0 :=
    (lt_trans (by norm_num) (two_thirds_lt_reciprocalPrimeLog p)).ne'
  rw [reciprocalPrimitiveCubicWeight, reciprocalHyperbolic,
    reciprocalSplitCoordinate]
  field_simp [reciprocalFormationRate_ne_zero δ, hp, hl]

theorem reciprocalPrimitiveCubicWeight_mul_kreinCompanion_sq
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalPrimitiveCubicWeight p * reciprocalKreinCompanion δ p ^ (2 : ℕ) =
      reciprocalPrimitiveCubicWeight p *
        (reciprocalHyperbolic δ p ^ (2 : ℕ) - 1) := by
  rw [reciprocalKreinCompanion_sq]

theorem reciprocalCubicAnomaly_sub_companion
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalPrimitiveCubicWeight p * reciprocalHyperbolic δ p ^ (2 : ℕ) -
        reciprocalPrimitiveCubicWeight p * reciprocalKreinCompanion δ p ^ (2 : ℕ) =
      reciprocalPrimitiveCubicWeight p := by
  rw [reciprocalKreinCompanion_sq]
  ring

/-- Existing Route-P theorem independently certifies the same anomaly/companion/source split. -/
theorem reciprocalCubicAnomaly_corpus_certificate
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    xiWardCubicFormationMetricAnomalyTraceWeight q p =
      xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0) +
        xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0) :=
  xiWardCubicFormationMetricAnomalyTraceWeight_eq_companion_add_source q p

/-! ### Finite coordinate packets and diagonal channels -/

def reciprocalFinitePacketSymbol
    (E : Finset PrimeHodgeHistoryIndex)
    (f : PrimeHodgeHistoryIndex → ℝ) (outside : ℝ)
    (i : PrimeHodgeHistoryIndex) : ℂ :=
  ((if i ∈ E then f i else outside : ℝ) : ℂ)

def reciprocalFinitePacketBound
    (E : Finset PrimeHodgeHistoryIndex)
    (f : PrimeHodgeHistoryIndex → ℝ) (outside : ℝ) : ℝ :=
  |outside| + ∑ i ∈ E, |f i|

theorem norm_reciprocalFinitePacketSymbol_le
    (E : Finset PrimeHodgeHistoryIndex)
    (f : PrimeHodgeHistoryIndex → ℝ) (outside : ℝ)
    (i : PrimeHodgeHistoryIndex) :
    ‖reciprocalFinitePacketSymbol E f outside i‖ ≤
      reciprocalFinitePacketBound E f outside := by
  classical
  by_cases hi : i ∈ E
  · rw [reciprocalFinitePacketSymbol, if_pos hi, Complex.norm_real,
      Real.norm_eq_abs]
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (f j)) hi).trans
      (le_add_of_nonneg_left (abs_nonneg outside))
  · rw [reciprocalFinitePacketSymbol, if_neg hi, Complex.norm_real,
      Real.norm_eq_abs, reciprocalFinitePacketBound]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

def reciprocalFinitePacketDiagonal
    (E : Finset PrimeHodgeHistoryIndex)
    (f : PrimeHodgeHistoryIndex → ℝ) (outside : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  HTGeometry.ellTwoDiagonal (reciprocalFinitePacketSymbol E f outside)
    (norm_reciprocalFinitePacketSymbol_le E f outside)

@[simp] theorem reciprocalFinitePacketDiagonal_apply
    (E : Finset PrimeHodgeHistoryIndex)
    (f : PrimeHodgeHistoryIndex → ℝ) (outside : ℝ)
    (x : PrimeHodgeHistoryHilbert) (i : PrimeHodgeHistoryIndex) :
    reciprocalFinitePacketDiagonal E f outside x i =
      ((if i ∈ E then f i else outside : ℝ) : ℂ) * x i := by
  rw [reciprocalFinitePacketDiagonal, HTGeometry.ellTwoDiagonal_apply]
  rfl

theorem reciprocalFinitePacketDiagonal_isSelfAdjoint
    (E : Finset PrimeHodgeHistoryIndex)
    (f : PrimeHodgeHistoryIndex → ℝ) (outside : ℝ) :
    IsSelfAdjoint (reciprocalFinitePacketDiagonal E f outside) := by
  change ContinuousLinearMap.adjoint
      (reciprocalFinitePacketDiagonal E f outside) =
    reciprocalFinitePacketDiagonal E f outside
  rw [reciprocalFinitePacketDiagonal, HTGeometry.adjoint_ellTwoDiagonal]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp [HTGeometry.ellTwoDiagonal_apply, reciprocalFinitePacketSymbol]

def reciprocalPacketProjection (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  HTGeometry.ellTwoDiagonal
    (fun i : PrimeHodgeHistoryIndex => if i ∈ E then (1 : ℂ) else 0)
    (C := 1) (fun i => by
      classical
      by_cases hi : i ∈ E <;> simp [hi])

@[simp] theorem reciprocalPacketProjection_apply
    (E : Finset PrimeHodgeHistoryIndex) (x : PrimeHodgeHistoryHilbert)
    (i : PrimeHodgeHistoryIndex) :
    reciprocalPacketProjection E x i = if i ∈ E then x i else 0 := by
  classical
  by_cases hi : i ∈ E <;>
    simp [reciprocalPacketProjection, hi]

theorem reciprocalPacketProjection_isSelfAdjoint
    (E : Finset PrimeHodgeHistoryIndex) :
    IsSelfAdjoint (reciprocalPacketProjection E) := by
  change ContinuousLinearMap.adjoint (reciprocalPacketProjection E) =
    reciprocalPacketProjection E
  rw [reciprocalPacketProjection, HTGeometry.adjoint_ellTwoDiagonal]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  classical
  simp [HTGeometry.ellTwoDiagonal_apply]

theorem norm_reciprocalPacketProjection_le_one
    (E : Finset PrimeHodgeHistoryIndex) :
    ‖reciprocalPacketProjection E‖ ≤ 1 := by
  rw [reciprocalPacketProjection]
  exact HTGeometry.norm_ellTwoDiagonal_le _ _ zero_le_one

theorem reciprocalPacketProjection_idempotent
    (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalPacketProjection E ∘L reciprocalPacketProjection E =
      reciprocalPacketProjection E := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i ∈ E <;>
    simp [ContinuousLinearMap.comp_apply, hi]

/-- Two-sided compression of the fixed integral--nuclear source to a finite coordinate packet. -/
def reciprocalPacketCompression (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalPacketProjection E ∘L
    primeHodgeHistoryIntegralNuclearDefectT ∘L reciprocalPacketProjection E

theorem reciprocalPacketCompression_isPositive
    (E : Finset PrimeHodgeHistoryIndex) :
    (reciprocalPacketCompression E).IsPositive := by
  have h := primeHodgeHistoryIntegralNuclearDefect_closed.1.conj_adjoint
    (reciprocalPacketProjection E)
  have hself : ContinuousLinearMap.adjoint (reciprocalPacketProjection E) =
      reciprocalPacketProjection E := reciprocalPacketProjection_isSelfAdjoint E
  rw [hself] at h
  simpa [reciprocalPacketCompression, ContinuousLinearMap.comp_assoc] using h

theorem reciprocalPacketCompression_memSchattenClass_one
    (E : Finset PrimeHodgeHistoryIndex) :
    MemSchattenClass 1 (reciprocalPacketCompression E) := by
  rw [reciprocalPacketCompression]
  exact memSchattenClass_one_comp_left
    (memSchattenClass_one_comp_right
      primeHodgeHistoryIntegralNuclearDefect_closed.2.1
      (reciprocalPacketProjection E))
    (reciprocalPacketProjection E)

/-- Positive square root of the finite compressed source. -/
def reciprocalPacketRoot (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  traceClassRoot (reciprocalPacketCompression E)

theorem reciprocalPacketRoot_isSelfAdjoint
    (E : Finset PrimeHodgeHistoryIndex) :
    IsSelfAdjoint (reciprocalPacketRoot E) :=
  isSelfAdjoint_traceClassRoot _

theorem reciprocalPacketRoot_comp_self
    (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalPacketRoot E ∘L reciprocalPacketRoot E =
      reciprocalPacketCompression E := by
  rw [reciprocalPacketRoot, traceClassRoot_comp_self]
  apply ContinuousLinearMap.absOp_of_nonneg
  rw [ContinuousLinearMap.le_def, sub_zero]
  exact reciprocalPacketCompression_isPositive E

theorem reciprocalPacketRoot_isHilbertSchmidt
    (E : Finset PrimeHodgeHistoryIndex) :
    (reciprocalPacketRoot E).IsHilbertSchmidt :=
  traceClassRoot_isHilbertSchmidt
    (reciprocalPacketCompression_memSchattenClass_one E)

def reciprocalVisiblePositiveChannel
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalFinitePacketDiagonal E
    (fun i => reciprocalVisibility δ i.2 * reciprocalHyperbolic δ i.2) 1

def reciprocalContrastPositiveChannel
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalFinitePacketDiagonal E
    (fun i => reciprocalContrast δ i.2 * reciprocalHyperbolic δ i.2) 0

def reciprocalVisibleNegativeChannel
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalFinitePacketDiagonal E
    (fun i => reciprocalVisibility δ i.2 * reciprocalKreinCompanion δ i.2) 0

def reciprocalContrastNegativeChannel
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalFinitePacketDiagonal E
    (fun i => reciprocalContrast δ i.2 * reciprocalKreinCompanion δ i.2) 0

theorem reciprocalChannels_isSelfAdjoint
    (δ : ReciprocalFormationRate) (E : Finset PrimeHodgeHistoryIndex) :
    IsSelfAdjoint (reciprocalVisiblePositiveChannel δ E) ∧
      IsSelfAdjoint (reciprocalContrastPositiveChannel δ E) ∧
      IsSelfAdjoint (reciprocalVisibleNegativeChannel δ E) ∧
      IsSelfAdjoint (reciprocalContrastNegativeChannel δ E) :=
  ⟨reciprocalFinitePacketDiagonal_isSelfAdjoint _ _ _,
    reciprocalFinitePacketDiagonal_isSelfAdjoint _ _ _,
    reciprocalFinitePacketDiagonal_isSelfAdjoint _ _ _,
    reciprocalFinitePacketDiagonal_isSelfAdjoint _ _ _⟩

/-- The diagonal four-channel `J` charge is the identity operator. -/
theorem reciprocalChannelKreinCharge_eq_one
    (δ : ReciprocalFormationRate) (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalVisiblePositiveChannel δ E ∘L reciprocalVisiblePositiveChannel δ E +
        reciprocalContrastPositiveChannel δ E ∘L reciprocalContrastPositiveChannel δ E -
        reciprocalVisibleNegativeChannel δ E ∘L reciprocalVisibleNegativeChannel δ E -
        reciprocalContrastNegativeChannel δ E ∘L reciprocalContrastNegativeChannel δ E =
      ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i ∈ E
  · simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply,
      reciprocalVisiblePositiveChannel, reciprocalContrastPositiveChannel,
      reciprocalVisibleNegativeChannel, reciprocalContrastNegativeChannel,
      reciprocalFinitePacketDiagonal_apply, if_pos hi,
      ContinuousLinearMap.id_apply, lp.coeFn_add, lp.coeFn_sub,
      Pi.add_apply, Pi.sub_apply]
    calc
      _ = (((reciprocalVisibility δ i.2 * reciprocalHyperbolic δ i.2) ^ (2 : ℕ) +
              (reciprocalContrast δ i.2 * reciprocalHyperbolic δ i.2) ^ (2 : ℕ) -
              (reciprocalVisibility δ i.2 * reciprocalKreinCompanion δ i.2) ^ (2 : ℕ) -
              (reciprocalContrast δ i.2 * reciprocalKreinCompanion δ i.2) ^ (2 : ℕ) : ℝ) : ℂ) *
            x i := by push_cast; ring
      _ = x i := by rw [reciprocalFourChannel_charge]; simp
  · simp [reciprocalVisiblePositiveChannel,
      reciprocalContrastPositiveChannel, reciprocalVisibleNegativeChannel,
      reciprocalContrastNegativeChannel, ContinuousLinearMap.comp_apply, hi]

def reciprocalHyperbolicEnergyDiagonal
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalFinitePacketDiagonal E
    (fun i => 2 * reciprocalHyperbolic δ i.2 ^ (2 : ℕ) - 1) 1

/-- The diagonal ordinary energy is exactly `2H²-I`. -/
theorem reciprocalChannelPositiveEnergy_eq
    (δ : ReciprocalFormationRate) (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalVisiblePositiveChannel δ E ∘L reciprocalVisiblePositiveChannel δ E +
        reciprocalContrastPositiveChannel δ E ∘L reciprocalContrastPositiveChannel δ E +
        reciprocalVisibleNegativeChannel δ E ∘L reciprocalVisibleNegativeChannel δ E +
        reciprocalContrastNegativeChannel δ E ∘L reciprocalContrastNegativeChannel δ E =
      reciprocalHyperbolicEnergyDiagonal δ E := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i ∈ E
  · simp only [add_apply, ContinuousLinearMap.comp_apply,
      reciprocalVisiblePositiveChannel, reciprocalContrastPositiveChannel,
      reciprocalVisibleNegativeChannel, reciprocalContrastNegativeChannel,
      reciprocalHyperbolicEnergyDiagonal,
      reciprocalFinitePacketDiagonal_apply, if_pos hi,
      lp.coeFn_add, Pi.add_apply]
    calc
      _ = (((reciprocalVisibility δ i.2 * reciprocalHyperbolic δ i.2) ^ (2 : ℕ) +
              (reciprocalContrast δ i.2 * reciprocalHyperbolic δ i.2) ^ (2 : ℕ) +
              (reciprocalVisibility δ i.2 * reciprocalKreinCompanion δ i.2) ^ (2 : ℕ) +
              (reciprocalContrast δ i.2 * reciprocalKreinCompanion δ i.2) ^ (2 : ℕ) : ℝ) : ℂ) *
            x i := by push_cast; ring
      _ = ((2 * reciprocalHyperbolic δ i.2 ^ (2 : ℕ) - 1 : ℝ) : ℂ) * x i := by
        rw [reciprocalFourChannel_positiveEnergy]
  · simp [reciprocalVisiblePositiveChannel,
      reciprocalContrastPositiveChannel, reciprocalVisibleNegativeChannel,
      reciprocalContrastNegativeChannel, reciprocalHyperbolicEnergyDiagonal,
      ContinuousLinearMap.comp_apply, hi]

/-! ### Literal four-channel synthesis and its two Gram operators -/

abbrev ReciprocalChannelPair :=
  WithLp 2 (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert)

abbrev ReciprocalFourChannelSpace :=
  WithLp 2 (ReciprocalChannelPair × ReciprocalChannelPair)

private def reciprocalPairToProd :
    ReciprocalChannelPair →L[ℂ]
      PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
    PrimeHodgeHistoryHilbert).toContinuousLinearMap

private def reciprocalPairOfProd :
    (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert) →L[ℂ]
      ReciprocalChannelPair :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
    PrimeHodgeHistoryHilbert).symm.toContinuousLinearMap

private def reciprocalFourToProd :
    ReciprocalFourChannelSpace →L[ℂ]
      ReciprocalChannelPair × ReciprocalChannelPair :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ReciprocalChannelPair
    ReciprocalChannelPair).toContinuousLinearMap

private def reciprocalFourOfProd :
    (ReciprocalChannelPair × ReciprocalChannelPair) →L[ℂ]
      ReciprocalFourChannelSpace :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ReciprocalChannelPair
    ReciprocalChannelPair).symm.toContinuousLinearMap

def reciprocalPairFst :
    ReciprocalChannelPair →L[ℂ] PrimeHodgeHistoryHilbert :=
  ContinuousLinearMap.fst ℂ PrimeHodgeHistoryHilbert PrimeHodgeHistoryHilbert ∘L
    reciprocalPairToProd

def reciprocalPairSnd :
    ReciprocalChannelPair →L[ℂ] PrimeHodgeHistoryHilbert :=
  ContinuousLinearMap.snd ℂ PrimeHodgeHistoryHilbert PrimeHodgeHistoryHilbert ∘L
    reciprocalPairToProd

def reciprocalFourFst :
    ReciprocalFourChannelSpace →L[ℂ] ReciprocalChannelPair :=
  ContinuousLinearMap.fst ℂ ReciprocalChannelPair ReciprocalChannelPair ∘L
    reciprocalFourToProd

def reciprocalFourSnd :
    ReciprocalFourChannelSpace →L[ℂ] ReciprocalChannelPair :=
  ContinuousLinearMap.snd ℂ ReciprocalChannelPair ReciprocalChannelPair ∘L
    reciprocalFourToProd

def reciprocalChannelOne :
    ReciprocalFourChannelSpace →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalPairFst ∘L reciprocalFourFst

def reciprocalChannelTwo :
    ReciprocalFourChannelSpace →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalPairSnd ∘L reciprocalFourFst

def reciprocalChannelThree :
    ReciprocalFourChannelSpace →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalPairFst ∘L reciprocalFourSnd

def reciprocalChannelFour :
    ReciprocalFourChannelSpace →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalPairSnd ∘L reciprocalFourSnd

@[simp] theorem reciprocalChannelOne_apply (z : ReciprocalFourChannelSpace) :
    reciprocalChannelOne z = z.fst.fst := rfl

@[simp] theorem reciprocalChannelTwo_apply (z : ReciprocalFourChannelSpace) :
    reciprocalChannelTwo z = z.fst.snd := rfl

@[simp] theorem reciprocalChannelThree_apply (z : ReciprocalFourChannelSpace) :
    reciprocalChannelThree z = z.snd.fst := rfl

@[simp] theorem reciprocalChannelFour_apply (z : ReciprocalFourChannelSpace) :
    reciprocalChannelFour z = z.snd.snd := rfl

/-- `J = diag(1,1,-1,-1)` on the nested four-channel Hilbert sum. -/
def reciprocalKreinMetric :
    ReciprocalFourChannelSpace →L[ℂ] ReciprocalFourChannelSpace :=
  reciprocalFourOfProd ∘L reciprocalFourFst.prod (-reciprocalFourSnd)

@[simp] theorem reciprocalKreinMetric_fst (z : ReciprocalFourChannelSpace) :
    (reciprocalKreinMetric z).fst = z.fst := rfl

@[simp] theorem reciprocalKreinMetric_snd (z : ReciprocalFourChannelSpace) :
    (reciprocalKreinMetric z).snd = -z.snd := rfl

@[simp] theorem reciprocalChannelOne_kreinMetric (z : ReciprocalFourChannelSpace) :
    reciprocalChannelOne (reciprocalKreinMetric z) = reciprocalChannelOne z := rfl

@[simp] theorem reciprocalChannelTwo_kreinMetric (z : ReciprocalFourChannelSpace) :
    reciprocalChannelTwo (reciprocalKreinMetric z) = reciprocalChannelTwo z := rfl

@[simp] theorem reciprocalChannelThree_kreinMetric (z : ReciprocalFourChannelSpace) :
    reciprocalChannelThree (reciprocalKreinMetric z) = -reciprocalChannelThree z := rfl

@[simp] theorem reciprocalChannelFour_kreinMetric (z : ReciprocalFourChannelSpace) :
    reciprocalChannelFour (reciprocalKreinMetric z) = -reciprocalChannelFour z := rfl

theorem reciprocalKreinMetric_involution :
    reciprocalKreinMetric ∘L reciprocalKreinMetric =
      ContinuousLinearMap.id ℂ ReciprocalFourChannelSpace := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ ReciprocalChannelPair
    ReciprocalChannelPair).injective
  apply Prod.ext <;> simp

theorem reciprocalKreinMetric_isSelfAdjoint :
    IsSelfAdjoint reciprocalKreinMetric := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro z w
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp [inner_neg_left, inner_neg_right]

/-- Column `(VH, CH, VK, CK) T_E¹ᐚ²`, extended by zero from the finite packet. -/
def reciprocalFourChannelSynthesis
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] ReciprocalFourChannelSpace :=
  reciprocalFourOfProd ∘L
    ((reciprocalPairOfProd ∘L
        ((reciprocalVisiblePositiveChannel δ E ∘L reciprocalPacketRoot E).prod
          (reciprocalContrastPositiveChannel δ E ∘L reciprocalPacketRoot E))).prod
      (reciprocalPairOfProd ∘L
        ((reciprocalVisibleNegativeChannel δ E ∘L reciprocalPacketRoot E).prod
          (reciprocalContrastNegativeChannel δ E ∘L reciprocalPacketRoot E))))

@[simp] theorem reciprocalFourChannelSynthesis_one
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) (x : PrimeHodgeHistoryHilbert) :
    (reciprocalFourChannelSynthesis δ E x).fst.fst =
      reciprocalVisiblePositiveChannel δ E (reciprocalPacketRoot E x) := rfl

@[simp] theorem reciprocalFourChannelSynthesis_two
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) (x : PrimeHodgeHistoryHilbert) :
    (reciprocalFourChannelSynthesis δ E x).fst.snd =
      reciprocalContrastPositiveChannel δ E (reciprocalPacketRoot E x) := rfl

@[simp] theorem reciprocalFourChannelSynthesis_three
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) (x : PrimeHodgeHistoryHilbert) :
    (reciprocalFourChannelSynthesis δ E x).snd.fst =
      reciprocalVisibleNegativeChannel δ E (reciprocalPacketRoot E x) := rfl

@[simp] theorem reciprocalFourChannelSynthesis_four
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) (x : PrimeHodgeHistoryHilbert) :
    (reciprocalFourChannelSynthesis δ E x).snd.snd =
      reciprocalContrastNegativeChannel δ E (reciprocalPacketRoot E x) := rfl

def reciprocalFourChannelAnalysis
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    ReciprocalFourChannelSpace →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalPacketRoot E ∘L
      reciprocalVisiblePositiveChannel δ E ∘L reciprocalChannelOne +
    reciprocalPacketRoot E ∘L
      reciprocalContrastPositiveChannel δ E ∘L reciprocalChannelTwo +
    reciprocalPacketRoot E ∘L
      reciprocalVisibleNegativeChannel δ E ∘L reciprocalChannelThree +
    reciprocalPacketRoot E ∘L
      reciprocalContrastNegativeChannel δ E ∘L reciprocalChannelFour

@[simp] theorem reciprocalFourChannelAnalysis_apply
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex)
    (z : ReciprocalFourChannelSpace) :
    reciprocalFourChannelAnalysis δ E z =
      reciprocalPacketRoot E
          (reciprocalVisiblePositiveChannel δ E (reciprocalChannelOne z)) +
        reciprocalPacketRoot E
          (reciprocalContrastPositiveChannel δ E (reciprocalChannelTwo z)) +
        reciprocalPacketRoot E
          (reciprocalVisibleNegativeChannel δ E (reciprocalChannelThree z)) +
        reciprocalPacketRoot E
          (reciprocalContrastNegativeChannel δ E (reciprocalChannelFour z)) := rfl

theorem reciprocalFourChannelAnalysis_eq_adjoint
    (δ : ReciprocalFormationRate) (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalFourChannelAnalysis δ E =
      ContinuousLinearMap.adjoint (reciprocalFourChannelSynthesis δ E) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z x
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (reciprocalPacketRoot_isSelfAdjoint E)
  have hB := reciprocalChannels_isSelfAdjoint δ E
  have h1 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB.1
  have h2 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB.2.1
  have h3 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB.2.2.1
  have h4 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB.2.2.2
  have ht1 : inner ℂ
      (reciprocalPacketRoot E
        (reciprocalVisiblePositiveChannel δ E (reciprocalChannelOne z))) x =
      inner ℂ (reciprocalChannelOne z)
        (reciprocalVisiblePositiveChannel δ E (reciprocalPacketRoot E x)) :=
    (hS _ _).trans (h1 _ _)
  have ht2 : inner ℂ
      (reciprocalPacketRoot E
        (reciprocalContrastPositiveChannel δ E (reciprocalChannelTwo z))) x =
      inner ℂ (reciprocalChannelTwo z)
        (reciprocalContrastPositiveChannel δ E (reciprocalPacketRoot E x)) :=
    (hS _ _).trans (h2 _ _)
  have ht3 : inner ℂ
      (reciprocalPacketRoot E
        (reciprocalVisibleNegativeChannel δ E (reciprocalChannelThree z))) x =
      inner ℂ (reciprocalChannelThree z)
        (reciprocalVisibleNegativeChannel δ E (reciprocalPacketRoot E x)) :=
    (hS _ _).trans (h3 _ _)
  have ht4 : inner ℂ
      (reciprocalPacketRoot E
        (reciprocalContrastNegativeChannel δ E (reciprocalChannelFour z))) x =
      inner ℂ (reciprocalChannelFour z)
        (reciprocalContrastNegativeChannel δ E (reciprocalPacketRoot E x)) :=
    (hS _ _).trans (h4 _ _)
  rw [reciprocalFourChannelAnalysis_apply, inner_add_left, inner_add_left,
    inner_add_left, ht1, ht2, ht3, ht4]
  rw [WithLp.prod_inner_apply z (reciprocalFourChannelSynthesis δ E x)]
  change _ =
    (inner ℂ (reciprocalChannelOne z)
        (reciprocalVisiblePositiveChannel δ E (reciprocalPacketRoot E x)) +
      inner ℂ (reciprocalChannelTwo z)
        (reciprocalContrastPositiveChannel δ E (reciprocalPacketRoot E x))) +
    (inner ℂ (reciprocalChannelThree z)
        (reciprocalVisibleNegativeChannel δ E (reciprocalPacketRoot E x)) +
      inner ℂ (reciprocalChannelFour z)
        (reciprocalContrastNegativeChannel δ E (reciprocalPacketRoot E x)))
  ring

/-- Exact coefficient-faithful finite-packet `J`-Gram reconstruction. -/
theorem reciprocalFourChannel_adjoint_krein_synthesis
    (δ : ReciprocalFormationRate) (E : Finset PrimeHodgeHistoryIndex) :
    ContinuousLinearMap.adjoint (reciprocalFourChannelSynthesis δ E) ∘L
        reciprocalKreinMetric ∘L reciprocalFourChannelSynthesis δ E =
      reciprocalPacketCompression E := by
  rw [← reciprocalFourChannelAnalysis_eq_adjoint δ E]
  apply ContinuousLinearMap.ext
  intro x
  have hcharge := congrArg
    (fun A : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert =>
      A (reciprocalPacketRoot E x))
    (reciprocalChannelKreinCharge_eq_one δ E)
  have hroot := congrArg
    (fun A : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert => A x)
    (reciprocalPacketRoot_comp_self E)
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hcharge hroot ⊢
  rw [reciprocalFourChannelAnalysis_apply]
  simp only [reciprocalChannelOne_kreinMetric,
    reciprocalChannelTwo_kreinMetric, reciprocalChannelThree_kreinMetric,
    reciprocalChannelFour_kreinMetric]
  simp only [reciprocalChannelOne_apply,
    reciprocalChannelTwo_apply, reciprocalChannelThree_apply,
    reciprocalChannelFour_apply, reciprocalFourChannelSynthesis_one,
    reciprocalFourChannelSynthesis_two, reciprocalFourChannelSynthesis_three,
    reciprocalFourChannelSynthesis_four, map_neg]
  rw [show
      reciprocalPacketRoot E
            (reciprocalVisiblePositiveChannel δ E
                (reciprocalVisiblePositiveChannel δ E (reciprocalPacketRoot E x))) +
          reciprocalPacketRoot E
            (reciprocalContrastPositiveChannel δ E
                (reciprocalContrastPositiveChannel δ E (reciprocalPacketRoot E x))) +
          -reciprocalPacketRoot E
            (reciprocalVisibleNegativeChannel δ E
                (reciprocalVisibleNegativeChannel δ E (reciprocalPacketRoot E x))) +
          -reciprocalPacketRoot E
            (reciprocalContrastNegativeChannel δ E
                (reciprocalContrastNegativeChannel δ E (reciprocalPacketRoot E x))) =
        reciprocalPacketRoot E
          (reciprocalVisiblePositiveChannel δ E
                (reciprocalVisiblePositiveChannel δ E (reciprocalPacketRoot E x)) +
            reciprocalContrastPositiveChannel δ E
                (reciprocalContrastPositiveChannel δ E (reciprocalPacketRoot E x)) -
            reciprocalVisibleNegativeChannel δ E
                (reciprocalVisibleNegativeChannel δ E (reciprocalPacketRoot E x)) -
            reciprocalContrastNegativeChannel δ E
                (reciprocalContrastNegativeChannel δ E (reciprocalPacketRoot E x))) by
          simp only [map_add, map_sub]
          abel,
      hcharge, hroot]

/-- Ordinary positive Gram keeps the exact divergent middle factor `2H²-I`. -/
theorem reciprocalFourChannel_adjoint_synthesis
    (δ : ReciprocalFormationRate) (E : Finset PrimeHodgeHistoryIndex) :
    ContinuousLinearMap.adjoint (reciprocalFourChannelSynthesis δ E) ∘L
        reciprocalFourChannelSynthesis δ E =
      reciprocalPacketRoot E ∘L reciprocalHyperbolicEnergyDiagonal δ E ∘L
        reciprocalPacketRoot E := by
  rw [← reciprocalFourChannelAnalysis_eq_adjoint δ E]
  apply ContinuousLinearMap.ext
  intro x
  have henergy := congrArg
    (fun A : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert =>
      A (reciprocalPacketRoot E x))
    (reciprocalChannelPositiveEnergy_eq δ E)
  simp only [add_apply, ContinuousLinearMap.comp_apply] at henergy ⊢
  rw [reciprocalFourChannelAnalysis_apply]
  simp only [reciprocalChannelOne_apply, reciprocalChannelTwo_apply,
    reciprocalChannelThree_apply, reciprocalChannelFour_apply,
    reciprocalFourChannelSynthesis_one,
    reciprocalFourChannelSynthesis_two, reciprocalFourChannelSynthesis_three,
    reciprocalFourChannelSynthesis_four]
  rw [show
      reciprocalPacketRoot E
            (reciprocalVisiblePositiveChannel δ E
                (reciprocalVisiblePositiveChannel δ E (reciprocalPacketRoot E x))) +
          reciprocalPacketRoot E
            (reciprocalContrastPositiveChannel δ E
                (reciprocalContrastPositiveChannel δ E (reciprocalPacketRoot E x))) +
          reciprocalPacketRoot E
            (reciprocalVisibleNegativeChannel δ E
                (reciprocalVisibleNegativeChannel δ E (reciprocalPacketRoot E x))) +
          reciprocalPacketRoot E
            (reciprocalContrastNegativeChannel δ E
                (reciprocalContrastNegativeChannel δ E (reciprocalPacketRoot E x))) =
        reciprocalPacketRoot E
          (reciprocalVisiblePositiveChannel δ E
                (reciprocalVisiblePositiveChannel δ E (reciprocalPacketRoot E x)) +
            reciprocalContrastPositiveChannel δ E
                (reciprocalContrastPositiveChannel δ E (reciprocalPacketRoot E x)) +
            reciprocalVisibleNegativeChannel δ E
                (reciprocalVisibleNegativeChannel δ E (reciprocalPacketRoot E x)) +
            reciprocalContrastNegativeChannel δ E
                (reciprocalContrastNegativeChannel δ E (reciprocalPacketRoot E x))) by
          simp only [map_add],
      henergy]

/-! ### Coefficient faithfulness and fixed reflection gauge -/

theorem reciprocalPacketProjection_lpBasis_of_mem
    {E : Finset PrimeHodgeHistoryIndex} {i : PrimeHodgeHistoryIndex}
    (hi : i ∈ E) :
    reciprocalPacketProjection E (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i) =
      HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i := by
  classical
  change reciprocalPacketProjection E
      (HTGeometry.ellTwoCoordinateBasis PrimeHodgeHistoryIndex i) =
    HTGeometry.ellTwoCoordinateBasis PrimeHodgeHistoryIndex i
  rw [reciprocalPacketProjection,
    HTGeometry.ellTwoDiagonal_coordinateBasis]
  simp [hi]

theorem reciprocalPacketProjection_lpBasis
    (E : Finset PrimeHodgeHistoryIndex) (i : PrimeHodgeHistoryIndex) :
    reciprocalPacketProjection E (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i) =
      if i ∈ E then HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i else 0 := by
  classical
  by_cases hi : i ∈ E
  · rw [if_pos hi, reciprocalPacketProjection_lpBasis_of_mem hi]
  · apply lp.ext
    funext j
    rw [reciprocalPacketProjection_apply]
    by_cases hj : j ∈ E
    · have hji : j ≠ i := by
        intro h
        apply hi
        simpa [h] using hj
      simp [hi, hj, HilbertSchmidt.lpBasis_apply, lp.single_apply,
        Pi.single_eq_of_ne hji]
    · simp [hi, hj]

/-- Every retained unsquared matrix coefficient is literally the original source coefficient. -/
theorem inner_lpBasis_reciprocalPacketCompression
    {E : Finset PrimeHodgeHistoryIndex} {i j : PrimeHodgeHistoryIndex}
    (hi : i ∈ E) (hj : j ∈ E) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
        (reciprocalPacketCompression E
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)) =
      primeHodgeHistoryDefectKernel 1 (i, j) := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (reciprocalPacketProjection_isSelfAdjoint E)
  rw [reciprocalPacketCompression]
  simp only [ContinuousLinearMap.comp_apply]
  calc
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
        (reciprocalPacketProjection E
          (primeHodgeHistoryIntegralNuclearDefectT
            (reciprocalPacketProjection E
              (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)))) =
      inner ℂ
        (reciprocalPacketProjection E
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i))
        (primeHodgeHistoryIntegralNuclearDefectT
          (reciprocalPacketProjection E
            (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j))) :=
      (hsym _ _).symm
    _ = inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
        (primeHodgeHistoryIntegralNuclearDefectT
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)) := by
      rw [reciprocalPacketProjection_lpBasis_of_mem hi,
        reciprocalPacketProjection_lpBasis_of_mem hj]
    _ = primeHodgeHistoryDefectKernel 1 (i, j) :=
      inner_lpBasis_primeHodgeHistoryIntegralNuclearDefectT i j

theorem reciprocalPacketCompression_sameHistory_ne_zero
    {E : Finset PrimeHodgeHistoryIndex} {n : ℕ} {p q : Nat.Primes}
    (hp : (n, p) ∈ E) (hq : (n, q) ∈ E) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (reciprocalPacketCompression E
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 := by
  rw [inner_lpBasis_reciprocalPacketCompression hp hq]
  exact primeHodgeHistoryIntegralNuclearDefect_closed.2.2.2.2.1 n p q

/-- Full finite-compression coefficient formula, including the zero rows and columns off packet. -/
theorem inner_lpBasis_reciprocalPacketCompression_eq_indicator
    (E : Finset PrimeHodgeHistoryIndex) (i j : PrimeHodgeHistoryIndex) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
        (reciprocalPacketCompression E
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)) =
      if i ∈ E ∧ j ∈ E then primeHodgeHistoryDefectKernel 1 (i, j) else 0 := by
  classical
  by_cases hi : i ∈ E
  · by_cases hj : j ∈ E
    · simpa [hi, hj] using inner_lpBasis_reciprocalPacketCompression hi hj
    · rw [if_neg (fun h => hj h.2), reciprocalPacketCompression]
      simp [ContinuousLinearMap.comp_apply, reciprocalPacketProjection_lpBasis,
        hj]
  · rw [if_neg (fun h => hi h.1), reciprocalPacketCompression]
    simp only [ContinuousLinearMap.comp_apply]
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (reciprocalPacketProjection_isSelfAdjoint E)
    calc
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
          (reciprocalPacketProjection E
            (primeHodgeHistoryIntegralNuclearDefectT
              (reciprocalPacketProjection E
                (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)))) =
        inner ℂ
          (reciprocalPacketProjection E
            (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i))
          (primeHodgeHistoryIntegralNuclearDefectT
            (reciprocalPacketProjection E
              (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j))) :=
        (hsym _ _).symm
      _ = 0 := by
        rw [reciprocalPacketProjection_lpBasis, if_neg hi, inner_zero_left]

theorem reciprocalVisiblePositiveChannel_neg
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalVisiblePositiveChannel (-δ) E =
      reciprocalVisiblePositiveChannel δ E := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i ∈ E <;>
    simp [reciprocalVisiblePositiveChannel, hi,
      reciprocalVisibility_neg, reciprocalHyperbolic_neg]

theorem reciprocalContrastPositiveChannel_neg
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalContrastPositiveChannel (-δ) E =
      -reciprocalContrastPositiveChannel δ E := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i ∈ E <;>
    simp [reciprocalContrastPositiveChannel, hi,
      reciprocalContrast_neg, reciprocalHyperbolic_neg]

theorem reciprocalVisibleNegativeChannel_neg
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalVisibleNegativeChannel (-δ) E =
      reciprocalVisibleNegativeChannel δ E := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i ∈ E <;>
    simp [reciprocalVisibleNegativeChannel, hi,
      reciprocalVisibility_neg, reciprocalKreinCompanion_neg]

theorem reciprocalContrastNegativeChannel_neg
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalContrastNegativeChannel (-δ) E =
      -reciprocalContrastNegativeChannel δ E := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i ∈ E <;>
    simp [reciprocalContrastNegativeChannel, hi,
      reciprocalContrast_neg, reciprocalKreinCompanion_neg]

def reciprocalPairContrastGauge :
    ReciprocalChannelPair →L[ℂ] ReciprocalChannelPair :=
  reciprocalPairOfProd ∘L reciprocalPairFst.prod (-reciprocalPairSnd)

@[simp] theorem reciprocalPairContrastGauge_fst (z : ReciprocalChannelPair) :
    (reciprocalPairContrastGauge z).fst = z.fst := rfl

@[simp] theorem reciprocalPairContrastGauge_snd (z : ReciprocalChannelPair) :
    (reciprocalPairContrastGauge z).snd = -z.snd := rfl

/-- Fixed diagonal gauge changing signs of the two contrast channels. -/
def reciprocalContrastGauge :
    ReciprocalFourChannelSpace →L[ℂ] ReciprocalFourChannelSpace :=
  reciprocalFourOfProd ∘L
    ((reciprocalPairContrastGauge ∘L reciprocalFourFst).prod
      (reciprocalPairContrastGauge ∘L reciprocalFourSnd))

@[simp] theorem reciprocalContrastGauge_fst_fst (z : ReciprocalFourChannelSpace) :
    (reciprocalContrastGauge z).fst.fst = z.fst.fst := rfl

@[simp] theorem reciprocalContrastGauge_fst_snd (z : ReciprocalFourChannelSpace) :
    (reciprocalContrastGauge z).fst.snd = -z.fst.snd := rfl

@[simp] theorem reciprocalContrastGauge_snd_fst (z : ReciprocalFourChannelSpace) :
    (reciprocalContrastGauge z).snd.fst = z.snd.fst := rfl

@[simp] theorem reciprocalContrastGauge_snd_snd (z : ReciprocalFourChannelSpace) :
    (reciprocalContrastGauge z).snd.snd = -z.snd.snd := rfl

theorem reciprocalContrastGauge_involution :
    reciprocalContrastGauge ∘L reciprocalContrastGauge =
      ContinuousLinearMap.id ℂ ReciprocalFourChannelSpace := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ ReciprocalChannelPair
    ReciprocalChannelPair).injective
  apply Prod.ext
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
      PrimeHodgeHistoryHilbert).injective
    apply Prod.ext <;> simp
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
      PrimeHodgeHistoryHilbert).injective
    apply Prod.ext <;> simp

/-- Replacing the rate by its negative is exactly the fixed contrast-channel gauge. -/
theorem reciprocalFourChannelSynthesis_neg
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalFourChannelSynthesis (-δ) E =
      reciprocalContrastGauge ∘L reciprocalFourChannelSynthesis δ E := by
  apply ContinuousLinearMap.ext
  intro x
  apply GaloisForLFunctions.HTGeometry.LikelihoodJuliaDatum.withLp_prod_ext
  · apply GaloisForLFunctions.HTGeometry.LikelihoodJuliaDatum.withLp_prod_ext
    · change (reciprocalFourChannelSynthesis (-δ) E x).fst.fst =
        (reciprocalContrastGauge (reciprocalFourChannelSynthesis δ E x)).fst.fst
      rw [reciprocalFourChannelSynthesis_one,
        reciprocalContrastGauge_fst_fst, reciprocalFourChannelSynthesis_one,
        reciprocalVisiblePositiveChannel_neg]
    · change (reciprocalFourChannelSynthesis (-δ) E x).fst.snd =
        (reciprocalContrastGauge (reciprocalFourChannelSynthesis δ E x)).fst.snd
      rw [reciprocalFourChannelSynthesis_two,
        reciprocalContrastGauge_fst_snd, reciprocalFourChannelSynthesis_two,
        reciprocalContrastPositiveChannel_neg, neg_apply]
  · apply GaloisForLFunctions.HTGeometry.LikelihoodJuliaDatum.withLp_prod_ext
    · change (reciprocalFourChannelSynthesis (-δ) E x).snd.fst =
        (reciprocalContrastGauge (reciprocalFourChannelSynthesis δ E x)).snd.fst
      rw [reciprocalFourChannelSynthesis_three,
        reciprocalContrastGauge_snd_fst, reciprocalFourChannelSynthesis_three,
        reciprocalVisibleNegativeChannel_neg]
    · change (reciprocalFourChannelSynthesis (-δ) E x).snd.snd =
        (reciprocalContrastGauge (reciprocalFourChannelSynthesis δ E x)).snd.snd
      rw [reciprocalFourChannelSynthesis_four,
        reciprocalContrastGauge_snd_snd, reciprocalFourChannelSynthesis_four,
        reciprocalContrastNegativeChannel_neg, neg_apply]

/-! ### Cofinal trace-norm reconstruction -/

/-- An increasing sequence of finite coordinate packets which eventually contains every index. -/
structure ReciprocalPacketExhaustion where
  packet : ℕ → Finset PrimeHodgeHistoryIndex
  monotone : Monotone packet
  eventually_mem : ∀ i : PrimeHodgeHistoryIndex, ∃ N, ∀ n, N ≤ n → i ∈ packet n

theorem reciprocalPacketProjection_strong_tendsto_id
    (F : ReciprocalPacketExhaustion) (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun n => reciprocalPacketProjection (F.packet n) x)
      atTop (nhds x) := by
  let f : ℕ → PrimeHodgeHistoryIndex → ℝ := fun n i =>
    ‖(reciprocalPacketProjection (F.packet n) x - x) i‖ ^ (2 : ℕ)
  let bound : PrimeHodgeHistoryIndex → ℝ := fun i => ‖x i‖ ^ (2 : ℕ)
  have hbound : Summable bound := by
    simpa [bound] using (lp.memℓp x).summable (by norm_num)
  have hpoint : ∀ i, Tendsto (fun n => f n i) atTop (nhds 0) := by
    intro i
    obtain ⟨N, hN⟩ := F.eventually_mem i
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [f, reciprocalPacketProjection_apply, hN n hn]
  have hdom : ∀ᶠ n in atTop, ∀ i, ‖f n i‖ ≤ bound i := by
    refine Eventually.of_forall fun n i => ?_
    classical
    by_cases hi : i ∈ F.packet n
    · simp [f, bound, reciprocalPacketProjection_apply, hi]
    · simp [f, bound, reciprocalPacketProjection_apply, hi]
  have htsum : Tendsto (fun n => ∑' i, f n i) atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hsq : ∀ n,
      ‖reciprocalPacketProjection (F.packet n) x - x‖ ^ (2 : ℕ) = ∑' i, f n i := by
    intro n
    simpa [f] using HilbertSchmidt.lp_norm_sq_eq
      (reciprocalPacketProjection (F.packet n) x - x)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp htsum
  have hnorm : Tendsto
      (fun n => ‖reciprocalPacketProjection (F.packet n) x - x‖)
      atTop (nhds 0) := by
    have hsqrt' : Tendsto (fun n => Real.sqrt (∑' i, f n i))
        atTop (nhds 0) := by simpa [Function.comp_def] using hsqrt
    convert hsqrt' using 1
    funext n
    rw [← hsq n, Real.sqrt_sq (norm_nonneg _)]
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using hnorm

def reciprocalGlobalSourceRoot :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  traceClassRoot primeHodgeHistoryIntegralNuclearDefectT

theorem reciprocalGlobalSourceRoot_isSelfAdjoint :
    IsSelfAdjoint reciprocalGlobalSourceRoot :=
  isSelfAdjoint_traceClassRoot _

theorem reciprocalGlobalSourceRoot_isHilbertSchmidt :
    reciprocalGlobalSourceRoot.IsHilbertSchmidt :=
  traceClassRoot_isHilbertSchmidt
    primeHodgeHistoryIntegralNuclearDefect_closed.2.1

theorem reciprocalGlobalSourceRoot_comp_self :
    reciprocalGlobalSourceRoot ∘L reciprocalGlobalSourceRoot =
      primeHodgeHistoryIntegralNuclearDefectT := by
  rw [reciprocalGlobalSourceRoot, traceClassRoot_comp_self]
  apply ContinuousLinearMap.absOp_of_nonneg
  rw [ContinuousLinearMap.le_def, sub_zero]
  exact primeHodgeHistoryIntegralNuclearDefect_closed.1

def reciprocalPacketCutRoot (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalPacketProjection E ∘L reciprocalGlobalSourceRoot

theorem reciprocalPacketCutRoot_isHilbertSchmidt
    (E : Finset PrimeHodgeHistoryIndex) :
    (reciprocalPacketCutRoot E).IsHilbertSchmidt :=
  reciprocalGlobalSourceRoot_isHilbertSchmidt.comp_left
    (reciprocalPacketProjection E)

theorem reciprocalPacketCompression_eq_cutRootGram
    (E : Finset PrimeHodgeHistoryIndex) :
    reciprocalPacketCompression E =
      reciprocalPacketCutRoot E ∘L
        ContinuousLinearMap.adjoint (reciprocalPacketCutRoot E) := by
  rw [reciprocalPacketCutRoot, ContinuousLinearMap.adjoint_comp]
  change reciprocalPacketCompression E =
    (reciprocalPacketProjection E ∘L reciprocalGlobalSourceRoot) ∘L
      (ContinuousLinearMap.adjoint reciprocalGlobalSourceRoot ∘L
        ContinuousLinearMap.adjoint (reciprocalPacketProjection E))
  rw [show ContinuousLinearMap.adjoint reciprocalGlobalSourceRoot =
      reciprocalGlobalSourceRoot from reciprocalGlobalSourceRoot_isSelfAdjoint,
    show ContinuousLinearMap.adjoint (reciprocalPacketProjection E) =
      reciprocalPacketProjection E from reciprocalPacketProjection_isSelfAdjoint E,
    reciprocalPacketCompression, ← reciprocalGlobalSourceRoot_comp_self]
  simp only [ContinuousLinearMap.comp_assoc]

private theorem adjoint_sub_reciprocal
    (A B : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) :
    ContinuousLinearMap.adjoint (A - B) =
      ContinuousLinearMap.adjoint A - ContinuousLinearMap.adjoint B := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y x
  simp only [sub_apply, inner_sub_left, inner_sub_right]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]

private theorem traceNorm_reciprocalGram_sub_le
    {K L : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert}
    (hK : K.IsHilbertSchmidt) (hL : L.IsHilbertSchmidt) :
    traceNorm PrimeHodgeHistoryHilbert
        (K ∘L ContinuousLinearMap.adjoint K -
          L ∘L ContinuousLinearMap.adjoint L) ≤
      (K.hsNorm + L.hsNorm) * (K - L).hsNorm := by
  let D := K - L
  let A := D ∘L ContinuousLinearMap.adjoint K
  let B := L ∘L ContinuousLinearMap.adjoint D
  have hD : D.IsHilbertSchmidt := hK.sub hL
  have hArect : MemRectSchattenClass 1 A :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hK.adjoint hD
  have hBrect : MemRectSchattenClass 1 B :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hD.adjoint hL
  have hA : MemSchattenClass 1 A :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hArect
  have hB : MemSchattenClass 1 B :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hBrect
  have htri : traceNorm PrimeHodgeHistoryHilbert (A + B) ≤
      traceNorm PrimeHodgeHistoryHilbert A +
        traceNorm PrimeHodgeHistoryHilbert B :=
    traceNorm_add_le (hA.isCompactOperator one_pos)
      (hB.isCompactOperator one_pos) hA.one_summable_approxNumber
      hB.one_summable_approxNumber
  have hAbound : traceNorm PrimeHodgeHistoryHilbert A ≤ K.hsNorm * D.hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hK.adjoint hD
    simpa [A, ContinuousLinearMap.hsNorm, hK.hsNormSq_adjoint] using h
  have hBbound : traceNorm PrimeHodgeHistoryHilbert B ≤ D.hsNorm * L.hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hD.adjoint hL
    simpa [B, ContinuousLinearMap.hsNorm, hD.hsNormSq_adjoint, mul_comm] using h
  have hdecomp :
      K ∘L ContinuousLinearMap.adjoint K -
          L ∘L ContinuousLinearMap.adjoint L = A + B := by
    dsimp [A, B, D]
    rw [adjoint_sub_reciprocal]
    ext z
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hdecomp]
  calc
    traceNorm PrimeHodgeHistoryHilbert (A + B) ≤
        traceNorm PrimeHodgeHistoryHilbert A +
          traceNorm PrimeHodgeHistoryHilbert B := htri
    _ ≤ K.hsNorm * D.hsNorm + D.hsNorm * L.hsNorm :=
      add_le_add hAbound hBbound
    _ = (K.hsNorm + L.hsNorm) * D.hsNorm := by ring

theorem tendsto_hsNorm_reciprocalPacketCutRoot_sub
    (F : ReciprocalPacketExhaustion) :
    Tendsto (fun n =>
      (reciprocalPacketCutRoot (F.packet n) - reciprocalGlobalSourceRoot).hsNorm)
      atTop (nhds 0) := by
  let An : ℕ → PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
    fun n => reciprocalPacketProjection (F.packet n) -
      ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert
  have hstrong : ∀ x : PrimeHodgeHistoryHilbert,
      Tendsto (fun n => An n x) atTop (nhds 0) := by
    intro x
    have h := (reciprocalPacketProjection_strong_tendsto_id F x).sub_const x
    simpa [An] using h
  have hbound : ∀ n, ‖An n‖ ≤ 2 := by
    intro n
    have hid : ‖ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
    calc
      ‖An n‖ ≤ ‖reciprocalPacketProjection (F.packet n)‖ +
          ‖ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert‖ := by
        simpa [An] using norm_sub_le
          (reciprocalPacketProjection (F.packet n))
          (ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert)
      _ ≤ 1 + 1 := add_le_add
        (norm_reciprocalPacketProjection_le_one (F.packet n)) hid
      _ = 2 := by norm_num
  have hsq := tendsto_hsNormSq_comp_left_zero_of_strong An
    reciprocalGlobalSourceRoot reciprocalGlobalSourceRoot_isHilbertSchmidt
    hstrong (by norm_num : (0 : ℝ) ≤ 2) hbound
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm : Tendsto (fun n => (An n * reciprocalGlobalSourceRoot).hsNorm)
      atTop (nhds 0) := by
    simpa [ContinuousLinearMap.hsNorm, Function.comp_def] using hsqrt
  convert hnorm using 1
  funext n
  congr 1

/-- Every cofinal finite packet exhaustion recovers the source in trace norm. -/
theorem reciprocalPacketCompression_traceNorm_tendsto
    (F : ReciprocalPacketExhaustion) :
    Tendsto (fun n => traceNorm PrimeHodgeHistoryHilbert
      (reciprocalPacketCompression (F.packet n) -
        primeHodgeHistoryIntegralNuclearDefectT)) atTop (nhds 0) := by
  have hdiff := tendsto_hsNorm_reciprocalPacketCutRoot_sub F
  have hupper : Tendsto (fun n =>
      (2 * reciprocalGlobalSourceRoot.hsNorm) *
        (reciprocalPacketCutRoot (F.packet n) - reciprocalGlobalSourceRoot).hsNorm)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hdiff
  refine squeeze_zero' (Eventually.of_forall fun n => traceNorm_nonneg _) ?_ hupper
  refine Eventually.of_forall fun n => ?_
  rw [reciprocalPacketCompression_eq_cutRootGram,
    ← reciprocalGlobalSourceRoot_comp_self]
  have hK := reciprocalPacketCutRoot_isHilbertSchmidt (F.packet n)
  have hbound := reciprocalGlobalSourceRoot_isHilbertSchmidt.hsNorm_comp_left_le
    (reciprocalPacketProjection (F.packet n))
  have hKnorm : (reciprocalPacketCutRoot (F.packet n)).hsNorm ≤
      reciprocalGlobalSourceRoot.hsNorm := by
    rw [reciprocalPacketCutRoot]
    calc
      (reciprocalPacketProjection (F.packet n) ∘L reciprocalGlobalSourceRoot).hsNorm ≤
          ‖reciprocalPacketProjection (F.packet n)‖ *
            reciprocalGlobalSourceRoot.hsNorm := hbound
      _ ≤ 1 * reciprocalGlobalSourceRoot.hsNorm := by
        exact mul_le_mul_of_nonneg_right
          (norm_reciprocalPacketProjection_le_one (F.packet n))
          (ContinuousLinearMap.hsNorm_nonneg _)
      _ = reciprocalGlobalSourceRoot.hsNorm := one_mul _
  calc
    traceNorm PrimeHodgeHistoryHilbert
        (reciprocalPacketCutRoot (F.packet n) ∘L
            ContinuousLinearMap.adjoint (reciprocalPacketCutRoot (F.packet n)) -
          reciprocalGlobalSourceRoot ∘L reciprocalGlobalSourceRoot) ≤
      ((reciprocalPacketCutRoot (F.packet n)).hsNorm +
          reciprocalGlobalSourceRoot.hsNorm) *
        (reciprocalPacketCutRoot (F.packet n) - reciprocalGlobalSourceRoot).hsNorm := by
      have hself : ContinuousLinearMap.adjoint reciprocalGlobalSourceRoot =
          reciprocalGlobalSourceRoot := reciprocalGlobalSourceRoot_isSelfAdjoint
      simpa only [hself] using
        traceNorm_reciprocalGram_sub_le hK
          reciprocalGlobalSourceRoot_isHilbertSchmidt
    _ ≤ (2 * reciprocalGlobalSourceRoot.hsNorm) *
        (reciprocalPacketCutRoot (F.packet n) - reciprocalGlobalSourceRoot).hsNorm := by
      exact mul_le_mul_of_nonneg_right (by linarith [hKnorm])
        (ContinuousLinearMap.hsNorm_nonneg _)

theorem reciprocalPacketCompression_opTrace_tendsto_one
    (F : ReciprocalPacketExhaustion) :
    Tendsto (fun n => ContinuousLinearMap.opTrace
      (reciprocalPacketCompression (F.packet n))) atTop (nhds 1) := by
  have hdiff : ∀ n, MemSchattenClass 1
      (reciprocalPacketCompression (F.packet n) -
        primeHodgeHistoryIntegralNuclearDefectT) := fun n =>
    (reciprocalPacketCompression_memSchattenClass_one _).one_sub
      primeHodgeHistoryIntegralNuclearDefect_closed.2.1
  have h := opTrace_tendsto_of_traceNorm_tendsto
    (fun n => reciprocalPacketCompression_memSchattenClass_one _)
    hdiff (reciprocalPacketCompression_traceNorm_tendsto F)
  simpa [primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1] using h

theorem reciprocalPacketCompression_traceNorm_tendsto_one
    (F : ReciprocalPacketExhaustion) :
    Tendsto (fun n => traceNorm PrimeHodgeHistoryHilbert
      (reciprocalPacketCompression (F.packet n))) atTop (nhds 1) := by
  simpa [primeHodgeHistoryIntegralNuclearDefect_closed.2.2.2.1] using
    traceNorm_tendsto_of_traceNorm_sub_tendsto
      (fun n => reciprocalPacketCompression_memSchattenClass_one _)
      primeHodgeHistoryIntegralNuclearDefect_closed.2.1
      (reciprocalPacketCompression_traceNorm_tendsto F)

/-! ### The zero-rate homotopy defect -/

theorem reciprocalCompactFrame_tendsto_visibleWall (p : Nat.Primes) :
    Tendsto (fun δ : ℝ => (reciprocalVisibility δ p, reciprocalContrast δ p))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1, 0)) := by
  have hδ : Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hx : Tendsto (fun δ : ℝ => 2 * reciprocalCompactCoordinate δ p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [reciprocalCompactCoordinate, reciprocalPrimeLog] using
      tendsto_const_nhds.mul (hδ.mul_const (Real.log (p : ℝ)))
  have hv := (show ContinuousAt formationVisibility 0 by
      unfold formationVisibility
      exact (continuous_const.div
        (Real.continuous_cosh.comp (continuous_id.div_const 2))
        (fun u => (Real.cosh_pos (u / 2)).ne')).continuousAt).tendsto.comp hx
  have hc := (show ContinuousAt formationContrast 0 by
      unfold formationContrast
      rw [show (fun u : ℝ => Real.tanh (u / 2)) =
          (Real.sinh / Real.cosh) ∘ (fun u : ℝ => u / 2) by
        funext u
        exact Real.tanh_eq_sinh_div_cosh (u / 2)]
      exact ((Real.continuous_sinh.div Real.continuous_cosh
        (fun u => (Real.cosh_pos u).ne')).comp
        (continuous_id.div_const 2)).continuousAt).tendsto.comp hx
  rw [nhds_prod_eq]
  simpa [reciprocalVisibility, reciprocalContrast, formationVisibility,
    formationContrast] using hv.prodMk hc

theorem reciprocalSplitCoordinate_tendsto_atTop_zero
    (p : Nat.Primes) :
    Tendsto (fun δ : ℝ => reciprocalSplitCoordinate δ p)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hp : 0 < reciprocalPrimeLog p :=
    lt_trans (by norm_num) (two_thirds_lt_reciprocalPrimeLog p)
  have h := tendsto_inv_nhdsGT_zero.const_mul_atTop hp
  simpa [reciprocalSplitCoordinate, div_eq_mul_inv] using h

theorem reciprocalHyperbolic_tendsto_atTop_zero
    (p : Nat.Primes) :
    Tendsto (fun δ : ℝ => reciprocalHyperbolic δ p)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hsplit := reciprocalSplitCoordinate_tendsto_atTop_zero p
  have hge : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
      1 ≤ reciprocalSplitCoordinate δ p :=
    hsplit (eventually_ge_atTop 1)
  change Tendsto (fun δ : ℝ => reciprocalSplitCoordinate δ p ^ (2 : ℕ))
    (nhdsWithin 0 (Set.Ioi 0)) atTop
  refine tendsto_atTop_mono' (nhdsWithin 0 (Set.Ioi 0)) ?_ hsplit
  filter_upwards [hge] with δ hδ
  nlinarith [sq_nonneg (reciprocalSplitCoordinate δ p)]

theorem reciprocalKreinCompanion_tendsto_atTop_zero
    (p : Nat.Primes) :
    Tendsto (fun δ : ℝ => reciprocalKreinCompanion δ p)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hhyper := reciprocalHyperbolic_tendsto_atTop_zero p
  have hge : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
      1 ≤ reciprocalHyperbolic δ p := hhyper (eventually_ge_atTop 1)
  have hsq : Tendsto (fun δ : ℝ => reciprocalHyperbolic δ p ^ (2 : ℕ))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    refine tendsto_atTop_mono' (nhdsWithin 0 (Set.Ioi 0)) ?_ hhyper
    filter_upwards [hge] with δ hδ
    nlinarith [sq_nonneg (reciprocalHyperbolic δ p)]
  have hsub : Tendsto (fun δ : ℝ => reciprocalHyperbolic δ p ^ (2 : ℕ) - 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right (nhdsWithin 0 (Set.Ioi 0)) (-1) hsq
  unfold reciprocalKreinCompanion
  change Tendsto
    ((fun y : ℝ => Real.sqrt y) ∘
      fun δ : ℝ => reciprocalHyperbolic δ p ^ (2 : ℕ) - 1)
    (nhdsWithin 0 (Set.Ioi 0)) atTop
  exact Real.tendsto_sqrt_atTop.comp hsub

theorem reciprocalPositiveEnergy_tendsto_atTop_zero
    (p : Nat.Primes) :
    Tendsto (fun δ : ℝ => 2 * reciprocalHyperbolic δ p ^ (2 : ℕ) - 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hhyper := reciprocalHyperbolic_tendsto_atTop_zero p
  have hge : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
      1 ≤ reciprocalHyperbolic δ p := hhyper (eventually_ge_atTop 1)
  have hsq : Tendsto (fun δ : ℝ => reciprocalHyperbolic δ p ^ (2 : ℕ))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    refine tendsto_atTop_mono' (nhdsWithin 0 (Set.Ioi 0)) ?_ hhyper
    filter_upwards [hge] with δ hδ
    nlinarith [sq_nonneg (reciprocalHyperbolic δ p)]
  have hmul := hsq.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  simpa [sub_eq_add_neg] using
    tendsto_atTop_add_const_right (nhdsWithin 0 (Set.Ioi 0)) (-1) hmul

/-- Closed certificate for reciprocal compact/split conservation, coefficient-faithful finite
`J`-Gram reconstruction, cofinal nuclear recovery, reflection, anomaly splitting, and the
zero-rate homotopy defect. -/
theorem reciprocalFourChannelKreinNuclearRenormalization_closed :
    (∀ δ : ReciprocalFormationRate, ∀ p : Nat.Primes,
      reciprocalCompactCoordinate δ p * reciprocalSplitCoordinate δ p =
          reciprocalPrimeLog p ^ (2 : ℕ) ∧
        reciprocalVisibility δ p ^ (2 : ℕ) + reciprocalContrast δ p ^ (2 : ℕ) = 1 ∧
        reciprocalHyperbolic δ p ^ (2 : ℕ) - reciprocalKreinCompanion δ p ^ (2 : ℕ) = 1 ∧
        (reciprocalVisibility δ p * reciprocalHyperbolic δ p) ^ (2 : ℕ) +
            (reciprocalContrast δ p * reciprocalHyperbolic δ p) ^ (2 : ℕ) -
            (reciprocalVisibility δ p * reciprocalKreinCompanion δ p) ^ (2 : ℕ) -
            (reciprocalContrast δ p * reciprocalKreinCompanion δ p) ^ (2 : ℕ) = 1) ∧
    (∀ E : Finset PrimeHodgeHistoryIndex,
      IsSelfAdjoint (reciprocalPacketProjection E) ∧
        reciprocalPacketProjection E ∘L reciprocalPacketProjection E =
          reciprocalPacketProjection E ∧
        (reciprocalPacketCompression E).IsPositive ∧
        MemSchattenClass 1 (reciprocalPacketCompression E) ∧
        ∀ i j : PrimeHodgeHistoryIndex,
          inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
              (reciprocalPacketCompression E
                (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)) =
            if i ∈ E ∧ j ∈ E then primeHodgeHistoryDefectKernel 1 (i, j) else 0) ∧
    (∀ δ : ReciprocalFormationRate, ∀ E : Finset PrimeHodgeHistoryIndex,
      ContinuousLinearMap.adjoint (reciprocalFourChannelSynthesis δ E) ∘L
          reciprocalKreinMetric ∘L reciprocalFourChannelSynthesis δ E =
        reciprocalPacketCompression E ∧
      ContinuousLinearMap.adjoint (reciprocalFourChannelSynthesis δ E) ∘L
          reciprocalFourChannelSynthesis δ E =
        reciprocalPacketRoot E ∘L reciprocalHyperbolicEnergyDiagonal δ E ∘L
          reciprocalPacketRoot E) ∧
    (∀ δ : ℝ, ∀ E : Finset PrimeHodgeHistoryIndex,
      reciprocalFourChannelSynthesis (-δ) E =
        reciprocalContrastGauge ∘L reciprocalFourChannelSynthesis δ E) ∧
    (∀ F : ReciprocalPacketExhaustion,
      Tendsto (fun n => traceNorm PrimeHodgeHistoryHilbert
          (reciprocalPacketCompression (F.packet n) -
            primeHodgeHistoryIntegralNuclearDefectT)) atTop (nhds 0) ∧
        Tendsto (fun n => ContinuousLinearMap.opTrace
          (reciprocalPacketCompression (F.packet n))) atTop (nhds 1) ∧
        Tendsto (fun n => traceNorm PrimeHodgeHistoryHilbert
          (reciprocalPacketCompression (F.packet n))) atTop (nhds 1)) ∧
    (∀ δ : ReciprocalFormationRate, ∀ p : Nat.Primes,
      reciprocalPrimitiveCubicWeight p * reciprocalHyperbolic δ p ^ (2 : ℕ) =
          115 * reciprocalPrimeLog p ^ (2 : ℕ) / (864 * (δ : ℝ) ^ (4 : ℕ) * (p : ℝ)) ∧
        reciprocalPrimitiveCubicWeight p * reciprocalKreinCompanion δ p ^ (2 : ℕ) =
          reciprocalPrimitiveCubicWeight p *
            (reciprocalHyperbolic δ p ^ (2 : ℕ) - 1) ∧
        reciprocalPrimitiveCubicWeight p * reciprocalHyperbolic δ p ^ (2 : ℕ) -
            reciprocalPrimitiveCubicWeight p * reciprocalKreinCompanion δ p ^ (2 : ℕ) =
          reciprocalPrimitiveCubicWeight p) ∧
    (∀ p : Nat.Primes,
      Tendsto (fun δ : ℝ => (reciprocalVisibility δ p, reciprocalContrast δ p))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (1, 0)) ∧
        Tendsto (fun δ : ℝ => reciprocalSplitCoordinate δ p)
          (nhdsWithin 0 (Set.Ioi 0)) atTop ∧
        Tendsto (fun δ : ℝ => reciprocalKreinCompanion δ p)
          (nhdsWithin 0 (Set.Ioi 0)) atTop ∧
        Tendsto (fun δ : ℝ => 2 * reciprocalHyperbolic δ p ^ (2 : ℕ) - 1)
          (nhdsWithin 0 (Set.Ioi 0)) atTop) := by
  refine ⟨fun δ p => ⟨reciprocalCompact_mul_split δ p,
      reciprocalVisibility_sq_add_contrast_sq δ p,
      reciprocalHyperbolic_sq_sub_kreinCompanion_sq δ p,
      reciprocalFourChannel_charge δ p⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun E => ⟨reciprocalPacketProjection_isSelfAdjoint E,
      reciprocalPacketProjection_idempotent E,
      reciprocalPacketCompression_isPositive E,
      reciprocalPacketCompression_memSchattenClass_one E,
      inner_lpBasis_reciprocalPacketCompression_eq_indicator E⟩
  · exact fun δ E => ⟨reciprocalFourChannel_adjoint_krein_synthesis δ E,
      reciprocalFourChannel_adjoint_synthesis δ E⟩
  · exact reciprocalFourChannelSynthesis_neg
  · exact fun F => ⟨reciprocalPacketCompression_traceNorm_tendsto F,
      reciprocalPacketCompression_opTrace_tendsto_one F,
      reciprocalPacketCompression_traceNorm_tendsto_one F⟩
  · exact fun δ p => ⟨reciprocalPrimitiveCubicWeight_mul_hyperbolic_sq δ p,
      reciprocalPrimitiveCubicWeight_mul_kreinCompanion_sq δ p,
      reciprocalCubicAnomaly_sub_companion δ p⟩
  · exact fun p => ⟨reciprocalCompactFrame_tendsto_visibleWall p,
      reciprocalSplitCoordinate_tendsto_atTop_zero p,
      reciprocalKreinCompanion_tendsto_atTop_zero p,
      reciprocalPositiveEnergy_tendsto_atTop_zero p⟩

end
end RHTower
