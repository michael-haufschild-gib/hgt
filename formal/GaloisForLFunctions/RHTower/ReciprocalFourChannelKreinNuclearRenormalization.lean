import GaloisForLFunctions.RHTower.FormationBlowupProjectiveKinkBarrierTransgression
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.RHTower.SoninResidualApertureHilbertSchmidtContinuity
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
  reciprocalSplitCoordinate δ p ^ 2

def reciprocalKreinCompanion (δ : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (reciprocalHyperbolic δ p ^ 2 - 1)

/-- The two reciprocal coordinates multiply to the square of the prime clock. -/
theorem reciprocalCompact_mul_split
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalCompactCoordinate δ p * reciprocalSplitCoordinate δ p =
      reciprocalPrimeLog p ^ 2 := by
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
    reciprocalVisibility δ p ^ 2 + reciprocalContrast δ p ^ 2 = 1 := by
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
    reciprocalKreinCompanion δ p ^ 2 = reciprocalHyperbolic δ p ^ 2 - 1 := by
  rw [reciprocalKreinCompanion, Real.sq_sqrt]
  nlinarith [one_lt_reciprocalHyperbolic δ p]

/-- Split completion polarization. -/
theorem reciprocalHyperbolic_sq_sub_kreinCompanion_sq
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalHyperbolic δ p ^ 2 - reciprocalKreinCompanion δ p ^ 2 = 1 := by
  rw [reciprocalKreinCompanion_sq]
  ring

/-- The local four-channel vector has exact `J = diag(1,1,-1,-1)` charge one. -/
theorem reciprocalFourChannel_charge
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    (reciprocalVisibility δ p * reciprocalHyperbolic δ p) ^ 2 +
        (reciprocalContrast δ p * reciprocalHyperbolic δ p) ^ 2 -
        (reciprocalVisibility δ p * reciprocalKreinCompanion δ p) ^ 2 -
        (reciprocalContrast δ p * reciprocalKreinCompanion δ p) ^ 2 = 1 := by
  have hc := reciprocalVisibility_sq_add_contrast_sq (δ : ℝ) p
  have hh := reciprocalHyperbolic_sq_sub_kreinCompanion_sq δ p
  nlinarith

/-- Ordinary positive four-channel energy is the split factor `2h²-1`. -/
theorem reciprocalFourChannel_positiveEnergy
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    (reciprocalVisibility δ p * reciprocalHyperbolic δ p) ^ 2 +
        (reciprocalContrast δ p * reciprocalHyperbolic δ p) ^ 2 +
        (reciprocalVisibility δ p * reciprocalKreinCompanion δ p) ^ 2 +
        (reciprocalContrast δ p * reciprocalKreinCompanion δ p) ^ 2 =
      2 * reciprocalHyperbolic δ p ^ 2 - 1 := by
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
  115 / (864 * (p : ℝ) * reciprocalPrimeLog p ^ 2)

theorem reciprocalPrimitiveCubicWeight_eq_corpus (p : Nat.Primes) :
    reciprocalPrimitiveCubicWeight p =
      xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0) := by
  rw [xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero]
  simp [reciprocalPrimitiveCubicWeight, reciprocalPrimeLog]
  ring

theorem reciprocalPrimitiveCubicWeight_mul_hyperbolic_sq
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalPrimitiveCubicWeight p * reciprocalHyperbolic δ p ^ 2 =
      115 * reciprocalPrimeLog p ^ 2 / (864 * (δ : ℝ) ^ 4 * (p : ℝ)) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hl : reciprocalPrimeLog p ≠ 0 :=
    (lt_trans (by norm_num) (two_thirds_lt_reciprocalPrimeLog p)).ne'
  rw [reciprocalPrimitiveCubicWeight, reciprocalHyperbolic,
    reciprocalSplitCoordinate]
  field_simp [reciprocalFormationRate_ne_zero δ, hp, hl]

theorem reciprocalPrimitiveCubicWeight_mul_kreinCompanion_sq
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalPrimitiveCubicWeight p * reciprocalKreinCompanion δ p ^ 2 =
      reciprocalPrimitiveCubicWeight p *
        (reciprocalHyperbolic δ p ^ 2 - 1) := by
  rw [reciprocalKreinCompanion_sq]

theorem reciprocalCubicAnomaly_sub_companion
    (δ : ReciprocalFormationRate) (p : Nat.Primes) :
    reciprocalPrimitiveCubicWeight p * reciprocalHyperbolic δ p ^ 2 -
        reciprocalPrimitiveCubicWeight p * reciprocalKreinCompanion δ p ^ 2 =
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
      _ = (((reciprocalVisibility δ i.2 * reciprocalHyperbolic δ i.2) ^ 2 +
              (reciprocalContrast δ i.2 * reciprocalHyperbolic δ i.2) ^ 2 -
              (reciprocalVisibility δ i.2 * reciprocalKreinCompanion δ i.2) ^ 2 -
              (reciprocalContrast δ i.2 * reciprocalKreinCompanion δ i.2) ^ 2 : ℝ) : ℂ) *
            x i := by push_cast; ring
      _ = x i := by rw [reciprocalFourChannel_charge]; simp
  · simp [reciprocalVisiblePositiveChannel,
      reciprocalContrastPositiveChannel, reciprocalVisibleNegativeChannel,
      reciprocalContrastNegativeChannel, ContinuousLinearMap.comp_apply, hi]

def reciprocalHyperbolicEnergyDiagonal
    (δ : ℝ) (E : Finset PrimeHodgeHistoryIndex) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  reciprocalFinitePacketDiagonal E
    (fun i => 2 * reciprocalHyperbolic δ i.2 ^ 2 - 1) 1

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
      _ = (((reciprocalVisibility δ i.2 * reciprocalHyperbolic δ i.2) ^ 2 +
              (reciprocalContrast δ i.2 * reciprocalHyperbolic δ i.2) ^ 2 +
              (reciprocalVisibility δ i.2 * reciprocalKreinCompanion δ i.2) ^ 2 +
              (reciprocalContrast δ i.2 * reciprocalKreinCompanion δ i.2) ^ 2 : ℝ) : ℂ) *
            x i := by push_cast; ring
      _ = ((2 * reciprocalHyperbolic δ i.2 ^ 2 - 1 : ℝ) : ℂ) * x i := by
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
          simp only [map_add, map_sub, map_neg]
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

end
end RHTower
