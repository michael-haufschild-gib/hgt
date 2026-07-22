import GaloisForLFunctions.HTGeometry.CofiniteTailGramPolarization
import GaloisForLFunctions.RHTower.XiTransverseShiftAllValuationLayerRank

/-!
# A Hilbert metric for the transverse Xi prime-source aperture

The transverse differential-rank theorem has a concrete Hilbert realization. For every finite
family of distinct positive integral shifts, every finite logarithmic jet depth, and every finite
set of forbidden prime rays, one can evaluate the complete shift-jet rectangle on a square packet
of remaining primes so that its Hermitian Gram matrix is strictly positive definite.

Thus the aperture parameter is not only a differential-matroid coordinate: it carries a
deletion-robust positive Hilbert metric whose rank is exactly the number of shift-jet channels.
This is a source-side metric. It does not assert convergence of the separate constrained-prolate
CCM aperture Gram and does not constrain Xi zeros.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder Differential

local instance xiApertureUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiApertureUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiApertureUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiApertureUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiApertureCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiApertureCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiApertureAllValuationFieldDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiApertureAllValuationFieldDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- Prime coefficient of one transverse shift/logarithmic-jet channel. -/
def xiTransversePrimeJetApertureCoefficient
    {A : Type*} (shift : A → ℕ) (m : ℕ)
    (ak : A × Fin (m + 1)) (p : Nat.Primes) : ℂ :=
  primeProfileJetSource
    (fun a => xiTransverseShiftArithmetic (shift a)) m ak p

/-- Hermitian Hilbert Gram of a square transverse aperture packet outside a forbidden prime set. -/
def xiTransversePrimeJetApertureGram
    {A : Type*} [Fintype A] (shift : A → ℕ) (m : ℕ)
    (forbidden : Set Nat.Primes)
    (points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden}) :
    Matrix (A × Fin (m + 1)) (A × Fin (m + 1)) ℂ :=
  cofiniteEvaluationGram
    (xiTransversePrimeJetApertureCoefficient shift m) forbidden points

/-- **True transverse source-aperture Hilbert metric.** After deleting any finite prime packet,
distinct positive integral shifts and all jets through any prescribed order possess a square
strictly positive Hilbert Gram on the surviving prime source. -/
theorem exists_xiTransversePrimeJetApertureGram_posDef
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) (m : ℕ)
    (forbidden : Set Nat.Primes) (hfinite : forbidden.Finite) :
    ∃ points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden},
      (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef := by
  have htail : TailCoefficientIndependent
      (xiTransversePrimeJetApertureCoefficient shift m) := by
    simpa only [xiTransversePrimeJetApertureCoefficient] using
      xiTransverseShift_primeJets_tailIndependent shift hpos hinj m
  obtain ⟨points, hgram⟩ :=
    htail.exists_cofinite_posDef_evaluationGram
      (xiTransversePrimeJetApertureCoefficient shift m) forbidden hfinite
  exact ⟨points, hgram⟩

/-- Every such aperture packet has a strictly positive Gram determinant, so its Hilbert rank is
the full shift-times-jet cardinality. -/
theorem exists_xiTransversePrimeJetApertureGram_det_pos
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) (m : ℕ)
    (forbidden : Set Nat.Primes) (hfinite : forbidden.Finite) :
    ∃ points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden},
      0 < (xiTransversePrimeJetApertureGram shift m forbidden points).det := by
  obtain ⟨points, hgram⟩ :=
    exists_xiTransversePrimeJetApertureGram_posDef
      shift hpos hinj m forbidden hfinite
  exact ⟨points, hgram.det_pos⟩

/-- **Exact cofinite aperture classification.** At every fixed jet depth, deletion-robust strict
positivity of the transverse prime-source Gram is equivalent to the absence of the two literal
source collisions: no shift is zero and no two shifts coincide. The reverse implication is new:
the zero-jet slice of any positive aperture already detects both defects. -/
theorem xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (m : ℕ) :
    (∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden},
        (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef) ↔
      Function.Injective shift ∧ ∀ a, shift a ≠ 0 := by
  change (∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden},
        (cofiniteEvaluationGram
          (xiTransversePrimeJetApertureCoefficient shift m)
          forbidden points).PosDef) ↔ _
  rw [← tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram]
  constructor
  · intro htail
    have hlin := htail.linearIndependent_on_compl
      (xiTransversePrimeJetApertureCoefficient shift m) ∅ Set.finite_empty
    let k0 : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
    constructor
    · intro a b hab
      have hcoeff :
          (fun p : {p : Nat.Primes // p ∉ (∅ : Set Nat.Primes)} =>
            xiTransversePrimeJetApertureCoefficient shift m (a, k0) p) =
          fun p : {p : Nat.Primes // p ∉ (∅ : Set Nat.Primes)} =>
            xiTransversePrimeJetApertureCoefficient shift m (b, k0) p := by
        funext p
        simp only [xiTransversePrimeJetApertureCoefficient, primeProfileJetSource,
          primeProfileRotatedLogJet_apply, k0, pow_zero, one_mul, hab]
      exact congrArg Prod.fst (hlin.injective hcoeff)
    · intro a ha
      have hcoeff :
          (fun p : {p : Nat.Primes // p ∉ (∅ : Set Nat.Primes)} =>
            xiTransversePrimeJetApertureCoefficient shift m (a, k0) p) = 0 := by
        funext p
        simp [xiTransversePrimeJetApertureCoefficient, primeProfileJetSource,
          k0, ha, xiTransverseShiftArithmetic_apply, cpowWeight]
      exact hlin.ne_zero (a, k0) hcoeff
  · rintro ⟨hinj, hne⟩
    exact xiTransverseShift_primeJets_tailIndependent shift
      (fun a => Nat.pos_of_ne_zero (hne a)) hinj m

/-- **Analytic operator-tail/Hilbert-metric connector.** For every fixed jet depth, the actual Xi
shift carriers are differentially independent over all scalar valuation layers exactly when every
finite deletion of prime rays leaves a strictly positive square aperture Gram. Thus the positive
Hilbert realization and the analytic differential matroid have the same zero and parallel classes,
not merely the same rank on collision-free families. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_cofiniteApertureGram
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (m : ℕ) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun a => xiTransverseShiftUpperEndCarrier (shift a)) ↔
      ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden},
          (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef := by
  rw [xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero]
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun i : (Set.univ : Set A) => i.1) Subtype.val_injective
    have hcondition :=
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff
        shift Set.univ).mp hsub
    constructor
    · intro a b hab
      exact hcondition.1 (Set.mem_univ a) (Set.mem_univ b) hab
    · intro a
      exact hcondition.2 a (Set.mem_univ a)
  · rintro ⟨hinj, hne⟩
    have hsub :=
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff
        shift Set.univ).mpr ⟨
          fun a _ b _ hab => hinj hab,
          fun a _ => hne a⟩
    exact hsub.comp
      (fun a : A => ⟨a, Set.mem_univ a⟩)
      (fun _ _ hab => congrArg Subtype.val hab)

end

end RHTower
