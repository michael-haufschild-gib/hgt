import GaloisForLFunctions.HTGeometry.ExponentZeroIsodivisorialContinuation
import GaloisForLFunctions.HTGeometry.PrimeWalshClosedConstraint
import GaloisForLFunctions.HTGeometry.SparseCoherenceSelection
import Mathlib.NumberTheory.PrimeCounting

/-!
# Exponent-zero Prime-Walsh saturation

An exponentially sparse prime reservoir realizes every nonempty closed Boolean constraint as an
exact recurring-pattern chamber while remaining summable for every positive exponent.  The
resulting sign gauges preserve the complete divisor on the positive half-plane, and every finite
coordinate projection carries the exact Prime-Walsh differential basis and rank law.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

def exponentialPrimeEmbedding : ℕ ↪ Nat.Primes where
  toFun n := ⟨Nat.nth Nat.Prime (2 ^ n), Nat.prime_nth_prime _⟩
  inj' := by
    intro m n h
    have hnth : Nat.nth Nat.Prime (2 ^ m) = Nat.nth Nat.Prime (2 ^ n) :=
      congrArg Subtype.val h
    have hi : 2 ^ m = 2 ^ n :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hnth
    exact Nat.pow_right_injective (by omega : 2 ≤ 2) hi

theorem exponentialPrimeEmbedding_weight_le (sigma : PositiveExponent) (n : ℕ) :
    exponentZeroWeight natPrimeSize sigma (exponentialPrimeEmbedding n) ≤
      Real.exp (-sigma.1 * Real.log 2) ^ n := by
  have hnat : 2 ^ n ≤ Nat.nth Nat.Prime (2 ^ n) :=
    (Nat.le_add_right (2 ^ n) 2).trans (Nat.add_two_le_nth_prime (2 ^ n))
  have hcast : ((2 ^ n : ℕ) : ℝ) ≤
      ((exponentialPrimeEmbedding n : Nat.Primes) : ℝ) := by
    exact_mod_cast hnat
  have hlog : (n : ℝ) * Real.log 2 ≤
      Real.log ((exponentialPrimeEmbedding n : Nat.Primes) : ℝ) := by
    calc
      (n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ n) := by
        rw [Real.log_pow]
      _ ≤ Real.log ((exponentialPrimeEmbedding n : Nat.Primes) : ℝ) :=
        Real.log_le_log (by positivity) (by simpa using hcast)
  unfold exponentZeroWeight
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  dsimp only [natPrimeSize]
  calc
    -sigma.1 * Real.log ((exponentialPrimeEmbedding n : Nat.Primes) : ℝ) ≤
        -sigma.1 * ((n : ℝ) * Real.log 2) :=
      mul_le_mul_of_nonpos_left hlog (by linarith [sigma.2])
    _ = (n : ℝ) * (-sigma.1 * Real.log 2) := by ring

theorem summable_exponentZeroWeight_exponentialPrimeEmbedding
    (sigma : PositiveExponent) :
    Summable (fun n =>
      exponentZeroWeight natPrimeSize sigma (exponentialPrimeEmbedding n)) := by
  let q : ℝ := Real.exp (-sigma.1 * Real.log 2)
  have hqnonneg : 0 ≤ q := Real.exp_pos _ |>.le
  have hqone : q < 1 := by
    change Real.exp (-sigma.1 * Real.log 2) < 1
    rw [Real.exp_lt_one_iff]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [sigma.2]
  have hgeom : Summable (fun n : ℕ => q ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hqnonneg]
  exact Summable.of_nonneg_of_le
    (fun n => (exponentZeroWeight_pos natPrimeSize sigma _).le)
    (fun n => by simpa [q] using exponentialPrimeEmbedding_weight_le sigma n)
    hgeom

theorem summable_indicator_exponentialPrimeEmbedding_exponentZeroWeight
    (sigma : PositiveExponent) :
    Summable ((Set.range exponentialPrimeEmbedding).indicator
      (exponentZeroWeight natPrimeSize sigma)) :=
  (summable_indicator_embedding_range_iff exponentialPrimeEmbedding
    (exponentZeroWeight natPrimeSize sigma)).2
      (summable_exponentZeroWeight_exponentialPrimeEmbedding sigma)

noncomputable def sparseSequenceOrientation {J P : Type*}
    (e : ℕ ↪ P) (theta : ℕ → (J → Bool)) (j : J) (p : P) : Bool :=
  by
    classical
    exact if hp : p ∈ Set.range e then theta (Function.invFun e p) j else false

@[simp]
theorem sparseSequenceOrientation_apply_embedding {J P : Type*}
    (e : ℕ ↪ P) (theta : ℕ → (J → Bool)) (j : J) (n : ℕ) :
    sparseSequenceOrientation e theta j (e n) = theta n j := by
  rw [sparseSequenceOrientation, dif_pos ⟨n, rfl⟩]
  exact congrArg (fun k => theta k j) (Function.leftInverse_invFun e.injective n)

def boolOrientationPrimePhase {P : Type*} (epsilon : P → Bool) : PrimePhase P :=
  fun p => if epsilon p then -1 else 1

@[simp]
theorem boolOrientationPrimePhase_false {P : Type*} (epsilon : P → Bool) (p : P)
    (hp : epsilon p = false) :
    boolOrientationPrimePhase epsilon p = 1 := by
  simp [boolOrientationPrimePhase, hp]

theorem boolOrientationPrimePhase_isExponentZeroEulerGauge_of_support
    (epsilon : Nat.Primes → Bool)
    (hsupport : {p | epsilon p ≠ false} ⊆ Set.range exponentialPrimeEmbedding) :
    IsExponentZeroEulerGauge natPrimeSize (boolOrientationPrimePhase epsilon) := by
  intro sigma
  have hsum :=
    (summable_indicator_exponentialPrimeEmbedding_exponentZeroWeight sigma).mul_left 2
  apply Summable.of_nonneg_of_le
      (fun p => mul_nonneg (exponentZeroWeight_pos natPrimeSize sigma p).le (norm_nonneg _))
      (fun p => ?_) hsum
  by_cases hp : epsilon p = false
  · by_cases hprange : p ∈ Set.range exponentialPrimeEmbedding
    · simp [boolOrientationPrimePhase, hp, hprange,
        (exponentZeroWeight_pos natPrimeSize sigma p).le]
    · simp [boolOrientationPrimePhase, hp, hprange]
  · have hprange := hsupport hp
    rw [Set.indicator_of_mem hprange]
    have hptrue : epsilon p = true := Bool.eq_true_of_not_eq_false hp
    rw [boolOrientationPrimePhase, if_pos hptrue]
    norm_num [Complex.norm_real, (exponentZeroWeight_pos natPrimeSize sigma p).le]
    simp [mul_comm]

def sparseClosedConstraintPrimeOrientation
    {J : Type*} [Countable J] (K : Set (J → Bool)) [Nonempty K]
    (j : J) (p : Nat.Primes) : Bool :=
  sparseSequenceOrientation exponentialPrimeEmbedding (closedConstraintOrientation K) j p

@[simp]
theorem sparseClosedConstraintPrimeOrientation_apply_embedding
    {J : Type*} [Countable J] (K : Set (J → Bool)) [Nonempty K]
    (j : J) (n : ℕ) :
    sparseClosedConstraintPrimeOrientation K j (exponentialPrimeEmbedding n) =
      closedConstraintOrientation K n j :=
  sparseSequenceOrientation_apply_embedding _ _ _ _

theorem sparseClosedConstraintPrimeOrientation_support
    {J : Type*} [Countable J] (K : Set (J → Bool)) [Nonempty K]
    (j : J) :
    {p | sparseClosedConstraintPrimeOrientation K j p ≠ false} ⊆
      Set.range exponentialPrimeEmbedding := by
  intro p hp
  by_contra hprange
  apply hp
  simp [sparseClosedConstraintPrimeOrientation, sparseSequenceOrientation, hprange]

theorem sparseClosedConstraintPrimePhase_isExponentZeroEulerGauge
    {J : Type*} [Countable J] (K : Set (J → Bool)) [Nonempty K]
    (j : J) :
    IsExponentZeroEulerGauge natPrimeSize
      (boolOrientationPrimePhase (sparseClosedConstraintPrimeOrientation K j)) :=
  boolOrientationPrimePhase_isExponentZeroEulerGauge_of_support _
    (sparseClosedConstraintPrimeOrientation_support K j)

theorem exponentZeroEulerGaugeUnit_one_of_mem
    (eta : PrimePhase Nat.Primes) {s : ℂ} (hs : s ∈ positiveHalfPlane) :
    exponentZeroEulerGaugeUnit eta (1 : PrimePhase Nat.Primes) s = 1 := by
  rw [exponentZeroEulerGaugeUnit]
  convert tprod_one
  apply sub_eq_zero.mp
  rw [exponentZeroEulerGaugeFactor_sub_one eta (1 : PrimePhase Nat.Primes) _ hs]
  simp

theorem exponentZeroGaugeContinuedSource_one_of_mem
    (eta : PrimePhase Nat.Primes) (f : ℂ → ℂ)
    {s : ℂ} (hs : s ∈ positiveHalfPlane) :
    exponentZeroGaugeContinuedSource eta (1 : PrimePhase Nat.Primes) f s = f s := by
  simp [exponentZeroGaugeContinuedSource, exponentZeroEulerGaugeUnit_one_of_mem eta hs]

theorem sparseClosedConstraint_completePositiveHalfPlaneDivisor_eq
    {J : Type*} [Countable J] (K : Set (J → Bool)) [Nonempty K]
    (eta : PrimePhase Nat.Primes) (f : ℂ → ℂ) (j : J) :
    ∀ z ∈ positiveHalfPlane,
      meromorphicOrderAt
          (exponentZeroGaugeContinuedSource eta
            (boolOrientationPrimePhase (sparseClosedConstraintPrimeOrientation K j)) f) z =
        meromorphicOrderAt f z := by
  intro z hz
  exact exponentZeroGauge_completePositiveHalfPlaneDivisor_eq eta _
    (sparseClosedConstraintPrimePhase_isExponentZeroEulerGauge K j) f z hz

theorem sparseClosedConstraint_anchor_eq_base
    {J : Type*} [Countable J] (K : Set (J → Bool)) [Nonempty K]
    (anchor : J) (hanchor : ∀ x ∈ K, x anchor = false)
    (eta : PrimePhase Nat.Primes) (f : ℂ → ℂ) :
    ∀ z ∈ positiveHalfPlane,
      exponentZeroGaugeContinuedSource eta
          (boolOrientationPrimePhase
            (sparseClosedConstraintPrimeOrientation K anchor)) f z = f z := by
  have horientation : sparseClosedConstraintPrimeOrientation K anchor = fun _ => false := by
    funext p
    by_cases hp : p ∈ Set.range exponentialPrimeEmbedding
    · obtain ⟨n, rfl⟩ := hp
      rw [sparseClosedConstraintPrimeOrientation_apply_embedding]
      exact closedConstraintOrientation_eq_of_coordinate_eq K anchor false hanchor n
    · simp [sparseClosedConstraintPrimeOrientation, sparseSequenceOrientation, hp]
  have hphase : boolOrientationPrimePhase
      (sparseClosedConstraintPrimeOrientation K anchor) = 1 := by
    funext p
    simp [horientation, boolOrientationPrimePhase]
  intro z hz
  rw [hphase]
  exact exponentZeroGaugeContinuedSource_one_of_mem eta f hz

theorem primeRecurringPatternChamber_sparseClosedConstraint
    {J : Type*} [Countable J] (pi : ℕ ≃ Nat.Primes)
    (K : Set (J → Bool)) [Nonempty K] (hK : IsClosed K)
    (hall : allPositiveOrientationPattern ∈ K) :
    primeRecurringPatternChamber pi
        (sparseClosedConstraintPrimeOrientation K) = K := by
  let theta := closedConstraintOrientation K
  let epsilon := sparseClosedConstraintPrimeOrientation K
  have htheta : primeOrientationTailClusterSet theta = K :=
    tailCluster_infinitelyRepeatedDenseBooleanConstraint K hK
  ext x
  constructor
  · intro hx
    apply (mem_closedBooleanConstraint_iff_finitePatterns K hK x).2
    intro I
    have hrecur :=
      (mem_primeOrientationTailClusterSet_iff_all_finite_patterns_recur
        (fun n j => epsilon j (pi n)) x).1 hx I
    by_cases hzero : orientationRestriction I x =
        orientationRestriction I allPositiveOrientationPattern
    · obtain ⟨n, hn⟩ :=
        denseBooleanConstraintProfile_finitePattern K
          allPositiveOrientationPattern hall I
      exact ⟨n, hn.trans hzero.symm⟩
    · obtain ⟨n, hn⟩ := hrecur.nonempty
      have hprange : pi n ∈ Set.range exponentialPrimeEmbedding := by
        by_contra hp
        have hbackground :
            orientationRestriction I (fun j => epsilon j (pi n)) =
              orientationRestriction I allPositiveOrientationPattern := by
          funext j
          simp [epsilon, sparseClosedConstraintPrimeOrientation,
            sparseSequenceOrientation, hp, orientationRestriction,
            allPositiveOrientationPattern]
        exact hzero (hn.symm.trans hbackground)
      obtain ⟨m, hm⟩ := hprange
      change orientationRestriction I (fun j => epsilon j (pi n)) =
        orientationRestriction I x at hn
      rw [← hm] at hn
      simp only [epsilon, sparseClosedConstraintPrimeOrientation_apply_embedding] at hn
      refine ⟨(Nat.unpair m).1, ?_⟩
      simpa [theta, closedConstraintOrientation, infinitelyRepeatedOrientation] using hn
  · intro hx
    rw [primeRecurringPatternChamber]
    apply (mem_primeOrientationTailClusterSet_iff_all_finite_patterns_recur
      (fun n j => epsilon j (pi n)) x).2
    intro I
    have hxTheta : x ∈ primeOrientationTailClusterSet theta := by
      rwa [htheta]
    have hinf :=
      (mem_primeOrientationTailClusterSet_iff_all_finite_patterns_recur theta x).1 hxTheta I
    let f : ℕ → ℕ := fun m => pi.symm (exponentialPrimeEmbedding m)
    have hf : Function.Injective f :=
      pi.symm.injective.comp exponentialPrimeEmbedding.injective
    have himg : (f '' {m |
        orientationRestriction I (theta m) = orientationRestriction I x}).Infinite :=
      hinf.image hf.injOn
    apply himg.mono
    intro n hn
    obtain ⟨m, hm, rfl⟩ := hn
    change orientationRestriction I
        (fun j => epsilon j (pi (pi.symm (exponentialPrimeEmbedding m)))) =
      orientationRestriction I x
    simpa [epsilon, theta] using hm

theorem primeRecurringPatternChamber_sparseClosedConstraint_projection
    {J : Type*} [Countable J] (pi : ℕ ≃ Nat.Primes)
    (K : Set (J → Bool)) [Nonempty K] (hK : IsClosed K)
    (hall : allPositiveOrientationPattern ∈ K) (I : Finset J) :
    primeRecurringPatternChamber pi
        (fun i : I => sparseClosedConstraintPrimeOrientation K i.1) =
      orientationRestriction I '' K := by
  have himage := image_tailCluster_orientationRestriction
    (fun n j => sparseClosedConstraintPrimeOrientation K j (pi n)) I
  have hfull := primeRecurringPatternChamber_sparseClosedConstraint pi K hK hall
  unfold primeRecurringPatternChamber at hfull
  rw [hfull] at himage
  exact himage.symm

/-- **Sparse isodivisorial Prime-Walsh rank law.**  On every finite coordinate chamber, the
delta-pattern palette is a differential basis for the full Walsh field and has exactly the number
of generators prescribed by the projected closed constraint times the shift count. -/
theorem sparseClosedConstraintPrimeWalsh_differentialBasis_and_rank
    {J A : Type*} [Countable J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (pi : ℕ ≃ Nat.Primes) (K : Set (J → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K)
    (I : Finset J) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    let epsilon : I → Nat.Primes → Bool :=
      fun i => sparseClosedConstraintPrimeOrientation K i.1
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (primeTailPatternDeltaShiftPalette pi epsilon alpha) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (primeTailPatternDeltaShiftPalette pi epsilon alpha)) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (primeWalshShiftPalette epsilon alpha)) ∧
      Nat.card (primeRecurringPatternChamber pi epsilon × A) =
        Nat.card A * Nat.card (orientationRestriction I '' K) := by
  dsimp only
  have hbasis := primeWalshShiftPalette_differentialBasis pi
    (fun i : I => sparseClosedConstraintPrimeOrientation K i.1) alpha hdistinct
  refine ⟨hbasis.1, hbasis.2, ?_⟩
  rw [primeWalshDifferentialBasis_card,
    primeRecurringPatternChamber_sparseClosedConstraint_projection pi K hK hall I]

end

end GaloisForLFunctions.HTGeometry
