import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction
import GaloisForLFunctions.RHTower.ArithmeticSchurRenormalizationLaw
import GaloisForLFunctions.RHTower.XiTransverseShiftAllValuationLayerRank
import GaloisForLFunctions.RHTower.XiTransverseValuationSzegoMetric

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
open Matrix
open scoped ComplexOrder Differential InnerProduct

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

/-- In the collision-free aperture phase, every finite prime deletion leaves distinct source
points with exact dual recovery of all shift-jet coefficients, strict Gram geometry, and positive
Hilbert volume. -/
theorem exists_injective_xiTransversePrimeJetApertureCofiniteHilbertReconstruction
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) (m : ℕ)
    (forbidden : Set Nat.Primes) (hfinite : forbidden.Finite) :
    ∃ (points : A × Fin (m + 1) →
          {p : Nat.Primes // p ∉ forbidden})
        (dual : A × Fin (m + 1) → A × Fin (m + 1) → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiTransversePrimeJetApertureCoefficient shift m r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : A × Fin (m + 1) → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiTransversePrimeJetApertureCoefficient shift m r (points i)) =
        a q) ∧
      (xiTransversePrimeJetApertureGram
        shift m forbidden points).PosDef ∧
      0 < (xiTransversePrimeJetApertureGram
        shift m forbidden points).det := by
  have htail : TailCoefficientIndependent
      (xiTransversePrimeJetApertureCoefficient shift m) := by
    simpa only [xiTransversePrimeJetApertureCoefficient] using
      xiTransverseShift_primeJets_tailIndependent shift hpos hinj m
  simpa only [xiTransversePrimeJetApertureGram] using
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
      (xiTransversePrimeJetApertureCoefficient shift m)
      htail forbidden hfinite

/-- Complete deletion-robust exact reconstruction phase of the transverse prime-source
shift-jet aperture. -/
def XiTransversePrimeJetApertureCofiniteHilbertReconstruction
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (m : ℕ) : Prop :=
  CofiniteEvaluationHilbertReconstruction
    (xiTransversePrimeJetApertureCoefficient shift m)

/-- **Exact cofinite aperture reconstruction classification.** Full dual coefficient recovery,
strict Gram positivity, and positive volume survive every finite prime deletion exactly when the
integral shifts are nonzero and collision-free. -/
theorem
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (m : ℕ) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ↔
      Function.Injective shift ∧ ∀ a, shift a ≠ 0 := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiTransversePrimeJetApertureCoefficient shift m) :=
      cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
        (xiTransversePrimeJetApertureCoefficient shift m)
    _ ↔ (∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : A × Fin (m + 1) →
            {p : Nat.Primes // p ∉ forbidden},
          (cofiniteEvaluationGram
            (xiTransversePrimeJetApertureCoefficient shift m)
            forbidden points).PosDef) :=
      tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
        (xiTransversePrimeJetApertureCoefficient shift m)
    _ ↔ _ := by
      simpa only [xiTransversePrimeJetApertureGram] using
        xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero
          shift m

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

/-- **Analytic/exact-reconstruction connector.** Differential independence of the actual Xi shift
carriers over all scalar valuation layers is equivalent to deletion-robust exact recovery of every
prime-source shift-jet coefficient. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_cofiniteApertureHilbertReconstruction
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (m : ℕ) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun a => xiTransverseShiftUpperEndCarrier (shift a)) ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m := by
  calc
    _ ↔ (∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : A × Fin (m + 1) →
            {p : Nat.Primes // p ∉ forbidden},
          (xiTransversePrimeJetApertureGram
            shift m forbidden points).PosDef) :=
      xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_cofiniteApertureGram
        shift m
    _ ↔ Function.Injective shift ∧ ∀ a, shift a ≠ 0 :=
      xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero
        shift m
    _ ↔ _ :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift m).symm

/-- Complete one-prime valuation feature in the real Hardy space.  Its coordinates are the actual
successive transverse valuation increments. -/
def xiTransversePrimeValuationHardyFeature
    (a : ℕ) (p : Nat.Primes) (ha : 0 < a) : PrimeHardy :=
  let q := xiTransversePrimeApertureDiskNode a p
  (1 - q) • hardyKernel q (by
    rw [abs_of_pos (xiTransversePrimeApertureDiskNode_pos a p)]
    exact xiTransversePrimeApertureDiskNode_lt_one ha p)

/-- Matrix of the completed one-prime valuation--Szegő metric on a finite integral shift packet. -/
def xiTransversePrimeValuationSzegoGramMatrix
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiTransversePrimeValuationSzegoMetric (shift i) (shift j) p

/-- The completed valuation--Szegő matrix is literally the Gram matrix of the actual Hardy
valuation features. -/
theorem xiTransversePrimeValuationSzegoGramMatrix_eq_gram
    {N : ℕ} (shift : Fin N → ℕ) (hpos : ∀ j, 0 < shift j)
    (p : Nat.Primes) :
    xiTransversePrimeValuationSzegoGramMatrix shift p =
      Matrix.gram ℝ
        (fun j => xiTransversePrimeValuationHardyFeature (shift j) p (hpos j)) := by
  ext i j
  let qi := xiTransversePrimeApertureDiskNode (shift i) p
  let qj := xiTransversePrimeApertureDiskNode (shift j) p
  let hqi : |qi| < 1 := by
    simpa [qi, abs_of_pos (xiTransversePrimeApertureDiskNode_pos (shift i) p)] using
      xiTransversePrimeApertureDiskNode_lt_one (hpos i) p
  let hqj : |qj| < 1 := by
    simpa [qj, abs_of_pos (xiTransversePrimeApertureDiskNode_pos (shift j) p)] using
      xiTransversePrimeApertureDiskNode_lt_one (hpos j) p
  change xiTransversePrimeValuationSzegoMetric (shift i) (shift j) p =
    inner ℝ ((1 - qi) • hardyKernel qi hqi) ((1 - qj) • hardyKernel qj hqj)
  rw [real_inner_smul_left, real_inner_smul_right, inner_hardyKernel]
  simp only [xiTransversePrimeValuationSzegoMetric, qi, qj]
  ring

/-- Distinct positive integral apertures give linearly independent complete Hardy valuation
features.  Nonsingularity is already witnessed by their first matching number of coordinates. -/
theorem linearIndependent_xiTransversePrimeValuationHardyFeature
    {N : ℕ} (shift : Fin N → ℕ) (hinj : Function.Injective shift)
    (hpos : ∀ j, 0 < shift j) (p : Nat.Primes) :
    LinearIndependent ℝ
      (fun j => xiTransversePrimeValuationHardyFeature (shift j) p (hpos j)) := by
  let q : Fin N → ℝ := fun j => xiTransversePrimeApertureDiskNode (shift j) p
  let a : Fin N → ℝ := fun j => 1 - q j
  have hq : Function.Injective q :=
    (xiTransversePrimeApertureDiskNode_injective p).comp hinj
  have ha : ∀ j, a j ≠ 0 := by
    intro j
    exact sub_ne_zero.mpr (ne_of_gt
      (xiTransversePrimeApertureDiskNode_lt_one (hpos j) p))
  have hdet : (arithmeticSchurSamplingMatrix q a).det ≠ 0 :=
    arithmeticSchurSamplingMatrix_det_ne_zero hq ha
  have hmulVec : Function.Injective (arithmeticSchurSamplingMatrix q a).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    exact hdet
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc0 : c = 0 := hmulVec (by
    funext e
    have hcfn := congrArg (fun x : PrimeHardy => (x : ℕ → ℝ)) hc
    have hsum :
        (⇑(∑ x, c x •
            xiTransversePrimeValuationHardyFeature (shift x) p (hpos x)) : ℕ → ℝ) =
          ∑ x, (⇑(c x •
            xiTransversePrimeValuationHardyFeature (shift x) p (hpos x)) : ℕ → ℝ) := by
      simpa using (lp.coeFn_sum
        (fun x => c x •
          xiTransversePrimeValuationHardyFeature (shift x) p (hpos x)) Finset.univ)
    change
      (⇑(∑ x, c x •
          xiTransversePrimeValuationHardyFeature (shift x) p (hpos x)) : ℕ → ℝ) =
        (⇑(0 : PrimeHardy) : ℕ → ℝ) at hcfn
    rw [hsum] at hcfn
    have he := congrFun hcfn e
    simpa [arithmeticSchurSamplingMatrix, arithmeticSchurValuationCoordinate,
      xiTransversePrimeValuationHardyFeature, q, a, Matrix.mulVec, dotProduct,
      lp.coeFn_smul, mul_comm, mul_left_comm, mul_assoc] using he)
  exact fun i => congrFun hc0 i

/-- **Completed one-prime aperture classification.**  The full Hardy/Szegő valuation Gram is
strictly positive exactly when the actual integral shifts have neither a zero aperture nor a
collision.  Thus completion introduces no new metric radical beyond the finite valuation packet. -/
theorem xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef ↔
      Function.Injective shift ∧ ∀ j, shift j ≠ 0 := by
  constructor
  · intro hgram
    constructor
    · intro i j hij
      by_contra hne
      have hrows : xiTransversePrimeValuationSzegoGramMatrix shift p i =
          xiTransversePrimeValuationSzegoGramMatrix shift p j := by
        funext k
        simp [xiTransversePrimeValuationSzegoGramMatrix, hij]
      have hdetZero := Matrix.det_zero_of_row_eq hne hrows
      exact hgram.det_pos.ne' hdetZero
    · intro j hzero
      have hdiag := hgram.diag_pos (i := j)
      simp [xiTransversePrimeValuationSzegoGramMatrix,
        xiTransversePrimeValuationSzegoMetric, hzero,
        xiTransversePrimeApertureDiskNode] at hdiag
  · rintro ⟨hinj, hne⟩
    have hpos : ∀ j, 0 < shift j := fun j => Nat.pos_of_ne_zero (hne j)
    rw [xiTransversePrimeValuationSzegoGramMatrix_eq_gram shift hpos p]
    exact Matrix.posDef_gram_of_linearIndependent
      (linearIndependent_xiTransversePrimeValuationHardyFeature shift hinj hpos p)

/-- **Finite/completed valuation metric equivalence.**  The first matching number of valuation
increments and the complete Hardy/Szegő realization have exactly the same strict-positive phase. -/
theorem xiTransversePrimeValuationGramMatrix_posDef_iff_completedSzegoGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationGramMatrix shift p).PosDef ↔
      (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef := by
  rw [xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero]

/-- **Local/completed/cofinite Hilbert connector.**  Strict positivity of the complete valuation
metric at one prime is equivalent, at every fixed jet depth, to positive square realizability
after deleting any finite packet of prime rays.  The two Hilbert completions therefore realize the
same Xi differential collision matroid. -/
theorem xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_cofiniteApertureGram
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef ↔
      ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : Fin N × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
          (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef := by
  rw [xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero]

/-- **Completed/exact-cofinite Hilbert connector.** Strict positivity of the complete one-prime
valuation--Szegő metric is equivalent to deletion-robust exact recovery of every shift-jet
coefficient from the transverse prime source. -/
theorem
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_cofiniteApertureHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m := by
  rw [xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero]

/-- Strict positivity of the completed valuation metric is independent of the chosen prime. -/
theorem xiTransversePrimeValuationSzegoGramMatrix_posDef_prime_invariant
    {N : ℕ} (shift : Fin N → ℕ) (p r : Nat.Primes) :
    (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef ↔
      (xiTransversePrimeValuationSzegoGramMatrix shift r).PosDef := by
  rw [xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero]

/-- **One-prime local/global aperture equivalence.** For every finite integral shift packet and
every chosen prime, global differential independence of the actual upper-end Xi carriers is
equivalent to strict positivity of the Gram formed from only the first matching number of
valuation increments at that one prime. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_onePrimeValuationGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiTransversePrimeValuationGramMatrix shift p).PosDef := by
  rw [xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero]
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun i : (Set.univ : Set (Fin N)) => i.1) Subtype.val_injective
    have hcondition :=
      (xiTransverseShiftUpperEndCarrier_differentialIndependent_iff
        shift Set.univ).mp hsub
    constructor
    · intro i j hij
      exact hcondition.1 (Set.mem_univ i) (Set.mem_univ j) hij
    · intro i
      exact hcondition.2 i (Set.mem_univ i)
  · rintro ⟨hinjective, hnonzero⟩
    have hsub :=
      (xiTransverseShiftUpperEndCarrier_differentialIndependent_iff
        shift Set.univ).mpr ⟨
          fun i _ j _ hij => hinjective hij,
          fun i _ => hnonzero i⟩
    exact hsub.comp
      (fun i : Fin N => ⟨i, Set.mem_univ i⟩)
      (fun _ _ hij => congrArg Subtype.val hij)

/-- The same fixed-prime Gram exactly detects independence even after adjoining every scalar
prime-valuation layer to the differential base field. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_onePrimeValuationGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiTransversePrimeValuationGramMatrix shift p).PosDef := by
  rw [xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero]
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun i : (Set.univ : Set (Fin N)) => i.1) Subtype.val_injective
    have hcondition :=
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff
        shift Set.univ).mp hsub
    constructor
    · intro i j hij
      exact hcondition.1 (Set.mem_univ i) (Set.mem_univ j) hij
    · intro i
      exact hcondition.2 i (Set.mem_univ i)
  · rintro ⟨hinjective, hnonzero⟩
    have hsub :=
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff
        shift Set.univ).mpr ⟨
          fun i _ j _ hij => hinjective hij,
          fun i _ => hnonzero i⟩
    exact hsub.comp
      (fun i : Fin N => ⟨i, Set.mem_univ i⟩)
      (fun _ _ hij => congrArg Subtype.val hij)

/-- **Completed local/global aperture equivalence.**  Global differential independence of the
actual Xi shift carriers is exactly strict positivity of their complete Hardy/Szegő valuation
metric at any one chosen prime. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_onePrimeValuationSzegoGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef := by
  rw [
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_onePrimeValuationGram_posDef
      shift p,
    xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero shift p,
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero shift p]

/-- The completed one-prime Hardy metric also detects independence after adjoining every scalar
prime-valuation layer to the differential base. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_onePrimeValuationSzegoGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef := by
  rw [
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_onePrimeValuationGram_posDef
      shift p,
    xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero shift p,
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero shift p]

/-- **Finite Xi aperture base-invariance.** Adjoining all scalar prime-valuation layers neither
creates nor destroys a differential relation among a finite integral shift packet. The common
criterion is strict positivity of its one-prime valuation Gram. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialIndependent_base_iff_allValuation
    {N : ℕ} (shift : Fin N → ℕ) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  rw [
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_onePrimeValuationGram_posDef
      shift p,
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_onePrimeValuationGram_posDef
      shift p]

end

end RHTower
