import GaloisForLFunctions.HTGeometry.PrimeWalshStoneReconstruction
import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField

/-!
# Exact differential rank of the Prime-Walsh palette

For a finite Boolean orientation family, the recurring prime patterns give a canonical delta
palette.  Those delta columns are independent modulo finite prime support.  Finite Walsh inversion
expresses every delta column exactly in the Walsh palette, while every Walsh column differs from
its recurring-pattern expansion only on finitely many primes.  Since finite-prime corrections
belong to the coefficient field, the two palettes generate the same differential field.

Consequently the recurring-pattern delta palette is an explicit differential transcendence basis
for the enriched Prime-Walsh carrier: one generator for every recurring pattern and every shift.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

local instance complexFinitePrimeRationalAmbientScalarTower :
    IsScalarTower ℂ finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  .of_algebraMap_eq fun c => by
    change algebraMap ℂ arithmeticFunctionRationalCoordinateField c =
      finitePrimeRationalCoefficientFieldToFormalRatFunc
        (algebraMap ℂ finitePrimeRationalCoefficientField c)
    rw [IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      finitePrimeRationalCoefficientField]
    rw [finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap]
    rw [← IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      arithmeticFunctionFractionField]
    rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField]

/-- A bounded prime coefficient column in the finite-abscissa algebra. -/
def boundedPrimeFiniteAbscissa (c : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨arithmeticOfPrimeColumn c, 1, ?_⟩
  change ∀ y : ℝ, 1 < y → LSeriesSummable (fun n => arithmeticOfPrimeColumn c n) (y : ℂ)
  intro y hy
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
  · intro n hn
    by_cases hp : n.Prime
    · simpa [arithmeticOfPrimeColumn_apply_prime c ⟨n, hp⟩] using hc ⟨n, hp⟩
    · simp [arithmeticOfPrimeColumn, hp]
  · simpa using hy

def boundedPrimeShiftedRotatedJet
    (c : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (a : ℂ) (k : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  finiteAbscissaDirichletShift a
    ((finiteAbscissaRotatedDeriv^[k]) (boundedPrimeFiniteAbscissa c hc))

theorem boundedPrimeShiftedRotatedJet_apply
    (c : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (a : ℂ) (k n : ℕ) :
    (boundedPrimeShiftedRotatedJet c hc a k).1 n =
      cpowWeight a n * (Complex.I * (Real.log n : ℂ)) ^ k *
        arithmeticOfPrimeColumn c n := by
  rw [boundedPrimeShiftedRotatedJet, finiteAbscissaDirichletShift_apply,
    finiteAbscissaRotatedDeriv_iterate_apply]
  change cpowWeight a n *
      ((Complex.I * (Real.log n : ℂ)) ^ k * arithmeticOfPrimeColumn c n) = _
  ring

theorem boundedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
    (c : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (a : ℂ) (k : ℕ) :
    (boundedPrimeShiftedRotatedJet c hc a k).1 =
      arithmeticOfPrimeColumn
        (fun p => c p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k) := by
  ext n
  by_cases hn : n.Prime
  · rw [boundedPrimeShiftedRotatedJet_apply,
      arithmeticOfPrimeColumn_apply_prime c ⟨n, hn⟩,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩,
      show cpowWeight a n = primeShiftFactor a ⟨n, hn⟩ by
        exact cpowWeight_prime_eq_primeShiftFactor a ⟨n, hn⟩]
    simp only [rotatedPrimeLogClock, primeLogClock]
    ring
  · rw [boundedPrimeShiftedRotatedJet_apply]
    simp [arithmeticOfPrimeColumn, hn]

theorem rotatedLogFractionDerivation_boundedPrimeShiftedRotatedJet
    (c : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (a : ℂ) (k : ℕ) :
    rotatedLogFractionDerivation
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (boundedPrimeShiftedRotatedJet c hc a k).1) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (boundedPrimeShiftedRotatedJet c hc a (k + 1)).1 := by
  rw [rotatedLogFractionDerivation_algebraMap]
  congr 1
  ext n
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, logWeight_apply,
    boundedPrimeShiftedRotatedJet_apply]
  ring

def boundedPrimeShiftCarrier
    (c : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (a : ℂ) :
    arithmeticFunctionRationalCoordinateField :=
  algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
    (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (boundedPrimeShiftedRotatedJet c hc a 0).1)

@[simp] theorem differentialJet_boundedPrimeShiftCarrier
    (c : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k (boundedPrimeShiftCarrier c hc a) =
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (boundedPrimeShiftedRotatedJet c hc a k).1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih,
        arithmeticFunctionRationalCoordinateField_deriv_algebraMap,
        arithmeticFunctionFractionField_deriv_apply,
        rotatedLogFractionDerivation_boundedPrimeShiftedRotatedJet]

theorem boundedPrimeShiftedRotatedJet_tailIndependent
    {J A : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (c : J → Nat.Primes → ℂ) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (hrange : (Set.range (coefficientPattern c)).Finite)
    (htail : TailCoefficientIndependent c) (m : ℕ) :
    TailCoefficientIndependent
      (fun jak : J × (A × Fin (m + 1)) => fun p =>
        c jak.1 p * primeShiftFactor (alpha jak.2.1) p *
          rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)) := by
  classical
  let raw := coefficientShiftJet c
    (fun a p => primeShiftFactor (alpha a) p) primeLogClock m
  have hraw : TailCoefficientIndependent raw :=
    ((primeCompleteShiftJetTailIndependent_iff c alpha hdistinct hrange).mpr htail) m
  let u : J × (A × Fin (m + 1)) → ℂ :=
    fun jak => Complex.I ^ (jak.2.2 : ℕ)
  have hu : ∀ jak, u jak ≠ 0 := fun jak => pow_ne_zero _ Complex.I_ne_zero
  have hscaled := tailCoefficientIndependent_scale_columns raw u hu hraw
  convert hscaled using 1
  funext jak p
  simp only [raw, u, coefficientShiftJet, rotatedPrimeLogClock]
  rw [mul_pow]
  ring

theorem boundedPrimeShiftedRotatedJets_algebraicIndependent
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (c : J → Nat.Primes → ℂ) (hc : ∀ j p, ‖c j p‖ ≤ 1)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re))
    (hrange : (Set.range (coefficientPattern c)).Finite)
    (htail : TailCoefficientIndependent c) (m : ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun jak : J × (A × Fin (m + 1)) =>
        algebraMap arithmeticFunctionFractionField
          arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (boundedPrimeShiftedRotatedJet
              (c jak.1) (hc jak.1) (alpha jak.2.1) jak.2.2).1)) := by
  let coeff : J × (A × Fin (m + 1)) → Nat.Primes → ℂ :=
    fun jak p => c jak.1 p * primeShiftFactor (alpha jak.2.1) p *
      rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)
  have hcoeff : TailCoefficientIndependent coeff :=
    boundedPrimeShiftedRotatedJet_tailIndependent c alpha hdistinct hrange htail m
  have hraw :=
    algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField coeff hcoeff
  have hbase :=
    algebraicIndependent_constants_over_finitePrimeRationalCoefficientField _ hraw
  convert hbase using 1
  funext jak
  congr 2
  exact boundedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
    (c jak.1) (hc jak.1) (alpha jak.2.1) jak.2.2

/-- A finite palette of bounded prime columns with finite joint range is differentially
independent after distinct shifts whenever the source columns are independent modulo finite prime
support. -/
theorem boundedPrimeShiftPalette_differentialIndependent
    {J A : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (c : J → Nat.Primes → ℂ) (hc : ∀ j p, ‖c j p‖ ≤ 1)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re))
    (hrange : (Set.range (coefficientPattern c)).Finite)
    (htail : TailCoefficientIndependent c) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun ja : J × A => boundedPrimeShiftCarrier
        (c ja.1) (hc ja.1) (alpha ja.2)) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [differentialJet_boundedPrimeShiftCarrier]
  let x : (J × A) → ℕ → arithmeticFunctionRationalCoordinateField := fun ja k =>
    algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
      (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (boundedPrimeShiftedRotatedJet (c ja.1) (hc ja.1) (alpha ja.2) k).1)
  apply algebraicIndependent_prod_nat_of_fin x
  intro m
  let f : (J × A) × Fin (m + 1) → J × (A × Fin (m + 1)) := fun jak =>
    (jak.1.1, (jak.1.2, jak.2))
  have hf : Function.Injective f := by
    rintro ⟨⟨j, a⟩, k⟩ ⟨⟨j', a'⟩, k'⟩ h
    simp only [f, Prod.mk.injEq] at h ⊢
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  have hrect := boundedPrimeShiftedRotatedJets_algebraicIndependent
    c hc alpha hdistinct hrange htail m
  have hsub := hrect.comp f hf
  simpa only [Function.comp_apply, f, x] using! hsub

/-- The recurring finite pattern chamber of a prime orientation family, relative to an explicit
enumeration of the primes. -/
def primeRecurringPatternChamber
    {I : Type*} (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool) : Set (I → Bool) :=
  primeOrientationTailClusterSet (fun n i => ε i (e n))

/-- The indicator coefficient column of one recurring pattern. -/
noncomputable def primeTailPatternDeltaCoefficient
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    (r : primeRecurringPatternChamber e ε) (p : Nat.Primes) : ℂ :=
  if (fun i => ε i p) = r.1 then 1 else 0

/-- The primewise Walsh coefficient attached to one finite coordinate subset. -/
def primeWalshCoefficient
    {I : Type*} (ε : I → Nat.Primes → Bool) (B : Finset I) (p : Nat.Primes) : ℂ :=
  orientationWalshCharacter B (fun i => ε i p)

theorem primeRecurringPatternChamber_fiber_infinite
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool) (r : primeRecurringPatternChamber e ε) :
    {p | (fun i => ε i p) = r.1}.Infinite := by
  classical
  have hn : {n | (fun i => ε i (e n)) = r.1}.Infinite := by
    have hrec :=
      (mem_primeOrientationTailClusterSet_iff_all_finite_patterns_recur
        (fun n i => ε i (e n)) r.1).1 r.2 Finset.univ
    simpa [orientationRestriction, funext_iff] using hrec
  have himg : (e '' {n | (fun i => ε i (e n)) = r.1}).Infinite :=
    hn.image e.injective.injOn
  apply himg.mono
  rintro p ⟨n, hn, rfl⟩
  exact hn

theorem primeTailPatternDeltaCoefficient_tailIndependent
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)] :
    TailCoefficientIndependent (primeTailPatternDeltaCoefficient e ε) := by
  classical
  intro c hsupp
  funext r
  simp only [Pi.zero_apply]
  by_contra hcr
  have hinf := primeRecurringPatternChamber_fiber_infinite e ε r
  apply (hinf.mono ?_) hsupp
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  have hsum : (∑ x, c x * primeTailPatternDeltaCoefficient e ε x p) = c r := by
    calc
      (∑ x, c x * primeTailPatternDeltaCoefficient e ε x p) =
          ∑ x ∈ Finset.univ, c x * primeTailPatternDeltaCoefficient e ε x p := by simp
      _ = c r * primeTailPatternDeltaCoefficient e ε r p := by
        apply Finset.sum_eq_single r
        · intro x _ hxr
          have hne : (fun i => ε i p) ≠ x.1 := by
            intro h
            apply hxr
            exact Subtype.ext (h.symm.trans hp)
          simp [primeTailPatternDeltaCoefficient, hne]
        · intro hr
          exact (hr (Finset.mem_univ r)).elim
      _ = c r := by simp [primeTailPatternDeltaCoefficient, hp]
  intro hzero
  exact hcr (hsum.symm.trans hzero)

theorem primeTailPatternDeltaCoefficient_norm_le_one
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    (r : primeRecurringPatternChamber e ε) (p : Nat.Primes) :
    ‖primeTailPatternDeltaCoefficient e ε r p‖ ≤ 1 := by
  classical
  rw [primeTailPatternDeltaCoefficient]
  split_ifs <;> norm_num

theorem primeTailPatternDeltaCoefficient_pattern_range_finite
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool) :
    (Set.range (coefficientPattern (primeTailPatternDeltaCoefficient e ε))).Finite := by
  classical
  let encode : (I → Bool) → (primeRecurringPatternChamber e ε → ℂ) := fun b r =>
    if b = r.1 then 1 else 0
  apply (Set.finite_range encode).subset
  rintro v ⟨p, rfl⟩
  exact ⟨fun i => ε i p, by
    funext r
    simp [encode, coefficientPattern, primeTailPatternDeltaCoefficient]⟩

/-- The recurring-pattern delta palette is differentially independent: one independent generator
for every recurring pattern and every distinct shift. -/
theorem primeTailPatternDelta_shiftPalette_differentialIndependent
    {I A : Type*} [Fintype I]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun ra : primeRecurringPatternChamber e ε × A =>
        boundedPrimeShiftCarrier
          (primeTailPatternDeltaCoefficient e ε ra.1)
          (primeTailPatternDeltaCoefficient_norm_le_one e ε ra.1)
          (alpha ra.2)) := by
  classical
  letI : Fintype (primeRecurringPatternChamber e ε) := Fintype.ofFinite _
  letI : DecidableEq (primeRecurringPatternChamber e ε) := Classical.decEq _
  letI : Nonempty (primeRecurringPatternChamber e ε) :=
    (primeOrientationTailClusterSet_nonempty (fun n i => ε i (e n))).to_subtype
  exact boundedPrimeShiftPalette_differentialIndependent
    (primeTailPatternDeltaCoefficient e ε)
    (fun r => primeTailPatternDeltaCoefficient_norm_le_one e ε r)
    alpha hdistinct
    (primeTailPatternDeltaCoefficient_pattern_range_finite e ε)
    (primeTailPatternDeltaCoefficient_tailIndependent e ε)

theorem primePattern_not_mem_recurringChamber_finite
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool) :
    {p | (fun i => ε i p) ∉ primeRecurringPatternChamber e ε}.Finite := by
  classical
  let f : LocallyConstant (I → Bool) ℂ :=
    ⟨fun x => if x ∈ primeRecurringPatternChamber e ε then 0 else 1,
      IsLocallyConstant.of_discrete _⟩
  have hn : {n | f (fun i => ε i (e n)) ≠ 0}.Finite :=
    (locallyConstant_eventuallyZero_iff_vanishes_tailCluster
      (fun n i => ε i (e n)) f).2 (by
        intro x hx
        simp [f, primeRecurringPatternChamber, hx])
  have himg : (e '' {n | f (fun i => ε i (e n)) ≠ 0}).Finite := hn.image e
  apply himg.subset
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hnBad : f (fun i => ε i (e (e.symm p))) ≠ 0 := by
    simp only [e.apply_symm_apply]
    change (if (fun i => ε i p) ∈ primeRecurringPatternChamber e ε then 0 else 1) ≠ 0
    rw [if_neg hp]
    norm_num
  exact ⟨e.symm p, hnBad, e.apply_symm_apply p⟩

def primeWalshDeltaApproxCoefficient
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)]
    (B : Finset I) (p : Nat.Primes) : ℂ :=
  ∑ r : primeRecurringPatternChamber e ε,
    orientationWalshCharacter B r.1 * primeTailPatternDeltaCoefficient e ε r p

theorem primeWalshDeltaApproxCoefficient_eq_of_mem
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)]
    (B : Finset I) (p : Nat.Primes)
    (hp : (fun i => ε i p) ∈ primeRecurringPatternChamber e ε) :
    primeWalshDeltaApproxCoefficient e ε B p =
      orientationWalshCharacter B (fun i => ε i p) := by
  classical
  let r : primeRecurringPatternChamber e ε := ⟨fun i => ε i p, hp⟩
  rw [primeWalshDeltaApproxCoefficient, Fintype.sum_eq_single r]
  · simp [r, primeTailPatternDeltaCoefficient]
  · intro x hxr
    have hne : (fun i => ε i p) ≠ x.1 := by
      intro h
      apply hxr
      exact Subtype.ext h.symm
    simp [primeTailPatternDeltaCoefficient, hne]

theorem primeWalshDeltaResidual_support_finite
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)] (B : Finset I) :
    {p | primeWalshCoefficient ε B p -
      primeWalshDeltaApproxCoefficient e ε B p ≠ 0}.Finite := by
  apply (primePattern_not_mem_recurringChamber_finite e ε).subset
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  intro hmem
  apply hp
  rw [primeWalshDeltaApproxCoefficient_eq_of_mem e ε B p hmem]
  simp [primeWalshCoefficient]

theorem primeTailPatternDeltaCoefficient_eq_walshSum
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool) (r : primeRecurringPatternChamber e ε)
    (p : Nat.Primes) :
    primeTailPatternDeltaCoefficient e ε r p =
      ∑ B : Finset I,
        inverseWalshCoefficient (fun x => if x = r.1 then 1 else 0) B *
          primeWalshCoefficient ε B p := by
  classical
  have h := orientationWalsh_inversion
    (fun x : I → Bool => if x = r.1 then 1 else 0) (fun i => ε i p)
  simpa [primeTailPatternDeltaCoefficient, primeWalshCoefficient] using h.symm

theorem primeWalshCoefficient_norm_le_one
    {I : Type*} (ε : I → Nat.Primes → Bool) (B : Finset I) (p : Nat.Primes) :
    ‖primeWalshCoefficient ε B p‖ ≤ 1 := by
  classical
  rw [primeWalshCoefficient, orientationWalshCharacter, norm_prod]
  have hfactor : ∀ i : I, ‖primeDirichletSign (ε i p)‖ = 1 := by
    intro i
    cases ε i p <;> norm_num [primeDirichletSign]
  simp_rw [hfactor]
  simp

theorem boundedPrimeShiftCarrier_linearCombination
    {J : Type*} [Fintype J]
    (c : J → Nat.Primes → ℂ) (hc : ∀ j p, ‖c j p‖ ≤ 1)
    (u : J → ℂ) (d : Nat.Primes → ℂ) (hd : ∀ p, ‖d p‖ ≤ 1)
    (hcoeff : ∀ p, d p = ∑ j, u j * c j p) (a : ℂ) :
    boundedPrimeShiftCarrier d hd a =
      ∑ j, algebraMap ℂ arithmeticFunctionRationalCoordinateField (u j) *
        boundedPrimeShiftCarrier (c j) (hc j) a := by
  simp only [boundedPrimeShiftCarrier]
  simp_rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
    arithmeticFunctionRationalCoordinateField, ← map_mul]
  rw [← map_sum]
  congr 1
  simp_rw [IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField, ← map_mul]
  rw [← map_sum]
  congr 1
  simp_rw [← Algebra.smul_def]
  ext n
  rw [boundedPrimeShiftedRotatedJet_apply]
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f => f n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  rw [show (∑ x, u x •
      (boundedPrimeShiftedRotatedJet (c x) (hc x) a 0).1) n =
      ∑ x, (u x •
        (boundedPrimeShiftedRotatedJet (c x) (hc x) a 0).1) n by
    exact map_sum ev _ Finset.univ]
  by_cases hn : n.Prime
  · rw [arithmeticOfPrimeColumn_apply_prime d ⟨n, hn⟩, hcoeff ⟨n, hn⟩]
    simp only [ArithmeticFunction.smul_map, smul_eq_mul,
      boundedPrimeShiftedRotatedJet_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp [arithmeticOfPrimeColumn, hn]
    ring
  · simp [ArithmeticFunction.smul_map, boundedPrimeShiftedRotatedJet_apply,
      arithmeticOfPrimeColumn, hn]

/-- The coefficientwise linear-combination law persists at every shifted differential jet. -/
theorem boundedPrimeShiftedRotatedJet_linearCombination
    {J : Type*} [Fintype J]
    (c : J → Nat.Primes → ℂ) (hc : ∀ j p, ‖c j p‖ ≤ 1)
    (u : J → ℂ) (d : Nat.Primes → ℂ) (hd : ∀ p, ‖d p‖ ≤ 1)
    (hcoeff : ∀ p, d p = ∑ j, u j * c j p) (a : ℂ) (k : ℕ) :
    algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (boundedPrimeShiftedRotatedJet d hd a k).1) =
      ∑ j, algebraMap ℂ arithmeticFunctionRationalCoordinateField (u j) *
        algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (boundedPrimeShiftedRotatedJet (c j) (hc j) a k).1) := by
  simp_rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
    arithmeticFunctionRationalCoordinateField, ← map_mul]
  rw [← map_sum]
  congr 1
  simp_rw [IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField, ← map_mul]
  rw [← map_sum]
  congr 1
  simp_rw [← Algebra.smul_def]
  ext n
  rw [boundedPrimeShiftedRotatedJet_apply]
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f => f n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  rw [show (∑ x, u x •
      (boundedPrimeShiftedRotatedJet (c x) (hc x) a k).1) n =
      ∑ x, (u x •
        (boundedPrimeShiftedRotatedJet (c x) (hc x) a k).1) n by
    exact map_sum ev _ Finset.univ]
  by_cases hn : n.Prime
  · rw [arithmeticOfPrimeColumn_apply_prime d ⟨n, hn⟩, hcoeff ⟨n, hn⟩]
    simp only [ArithmeticFunction.smul_map, smul_eq_mul,
      boundedPrimeShiftedRotatedJet_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp [arithmeticOfPrimeColumn, hn]
    ring
  · simp [ArithmeticFunction.smul_map, boundedPrimeShiftedRotatedJet_apply,
      arithmeticOfPrimeColumn, hn]

/-- The full finite Walsh palette at a finite family of distinct shifts. -/
def primeWalshShiftPalette
    {I A : Type*}
    (ε : I → Nat.Primes → Bool) (alpha : A → ℂ) (Ba : Finset I × A) :
    arithmeticFunctionRationalCoordinateField :=
  boundedPrimeShiftCarrier
    (primeWalshCoefficient ε Ba.1)
    (primeWalshCoefficient_norm_le_one ε Ba.1)
    (alpha Ba.2)

/-- The recurring-pattern delta palette at the same shifts. -/
noncomputable def primeTailPatternDeltaShiftPalette
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    (alpha : A → ℂ) (ra : primeRecurringPatternChamber e ε × A) :
    arithmeticFunctionRationalCoordinateField :=
  boundedPrimeShiftCarrier
    (primeTailPatternDeltaCoefficient e ε ra.1)
    (primeTailPatternDeltaCoefficient_norm_le_one e ε ra.1)
    (alpha ra.2)

theorem primeTailPatternDeltaShiftPalette_eq_walshSum
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    (alpha : A → ℂ) (r : primeRecurringPatternChamber e ε) (a : A) :
    primeTailPatternDeltaShiftPalette e ε alpha (r, a) =
      ∑ B : Finset I,
        algebraMap ℂ arithmeticFunctionRationalCoordinateField
            (inverseWalshCoefficient (fun x => if x = r.1 then 1 else 0) B) *
          primeWalshShiftPalette ε alpha (B, a) := by
  classical
  exact boundedPrimeShiftCarrier_linearCombination
    (fun B : Finset I => primeWalshCoefficient ε B)
    (fun B => primeWalshCoefficient_norm_le_one ε B)
    (fun B => inverseWalshCoefficient (fun x => if x = r.1 then 1 else 0) B)
    (primeTailPatternDeltaCoefficient e ε r)
    (primeTailPatternDeltaCoefficient_norm_le_one e ε r)
    (primeTailPatternDeltaCoefficient_eq_walshSum e ε r)
    (alpha a)

theorem differentialJet_primeTailPatternDeltaShiftPalette_eq_walshSum
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    (alpha : A → ℂ) (r : primeRecurringPatternChamber e ε) (a : A) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (primeTailPatternDeltaShiftPalette e ε alpha (r, a)) =
      ∑ B : Finset I,
        algebraMap ℂ arithmeticFunctionRationalCoordinateField
            (inverseWalshCoefficient (fun x => if x = r.1 then 1 else 0) B) *
          GaloisForLFunctions.differentialJet k
            (primeWalshShiftPalette ε alpha (B, a)) := by
  classical
  simp only [primeTailPatternDeltaShiftPalette, primeWalshShiftPalette,
    differentialJet_boundedPrimeShiftCarrier]
  exact boundedPrimeShiftedRotatedJet_linearCombination
    (fun B : Finset I => primeWalshCoefficient ε B)
    (fun B => primeWalshCoefficient_norm_le_one ε B)
    (fun B => inverseWalshCoefficient (fun x => if x = r.1 then 1 else 0) B)
    (primeTailPatternDeltaCoefficient e ε r)
    (primeTailPatternDeltaCoefficient_norm_le_one e ε r)
    (primeTailPatternDeltaCoefficient_eq_walshSum e ε r)
    (alpha a) k

theorem primeWalshDeltaApproxCoefficient_norm_le_one
    {I : Type*} [Fintype I] (e : ℕ ≃ Nat.Primes)
    (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)]
    (B : Finset I) (p : Nat.Primes) :
    ‖primeWalshDeltaApproxCoefficient e ε B p‖ ≤ 1 := by
  classical
  by_cases hp : (fun i => ε i p) ∈ primeRecurringPatternChamber e ε
  · rw [primeWalshDeltaApproxCoefficient_eq_of_mem e ε B p hp]
    exact primeWalshCoefficient_norm_le_one ε B p
  · have hzero : primeWalshDeltaApproxCoefficient e ε B p = 0 := by
      rw [primeWalshDeltaApproxCoefficient]
      apply Finset.sum_eq_zero
      intro r hr
      have hne : (fun i => ε i p) ≠ r.1 := by
        intro h
        apply hp
        exact h ▸ r.2
      simp [primeTailPatternDeltaCoefficient, hne]
    rw [hzero, norm_zero]
    norm_num

theorem primeWalshDeltaApproxShiftPalette_eq_deltaSum
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)]
    (alpha : A → ℂ) (B : Finset I) (a : A) :
    boundedPrimeShiftCarrier
        (primeWalshDeltaApproxCoefficient e ε B)
        (primeWalshDeltaApproxCoefficient_norm_le_one e ε B)
        (alpha a) =
      ∑ r : primeRecurringPatternChamber e ε,
        algebraMap ℂ arithmeticFunctionRationalCoordinateField
            (orientationWalshCharacter B r.1) *
          primeTailPatternDeltaShiftPalette e ε alpha (r, a) := by
  classical
  exact boundedPrimeShiftCarrier_linearCombination
    (primeTailPatternDeltaCoefficient e ε)
    (fun r => primeTailPatternDeltaCoefficient_norm_le_one e ε r)
    (fun r => orientationWalshCharacter B r.1)
    (primeWalshDeltaApproxCoefficient e ε B)
    (primeWalshDeltaApproxCoefficient_norm_le_one e ε B)
    (fun p => rfl)
    (alpha a)

theorem differentialJet_primeWalshDeltaApproxShiftPalette_eq_deltaSum
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)]
    (alpha : A → ℂ) (B : Finset I) (a : A) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (boundedPrimeShiftCarrier
          (primeWalshDeltaApproxCoefficient e ε B)
          (primeWalshDeltaApproxCoefficient_norm_le_one e ε B)
          (alpha a)) =
      ∑ r : primeRecurringPatternChamber e ε,
        algebraMap ℂ arithmeticFunctionRationalCoordinateField
            (orientationWalshCharacter B r.1) *
          GaloisForLFunctions.differentialJet k
            (primeTailPatternDeltaShiftPalette e ε alpha (r, a)) := by
  classical
  simp only [primeTailPatternDeltaShiftPalette,
    differentialJet_boundedPrimeShiftCarrier]
  exact boundedPrimeShiftedRotatedJet_linearCombination
    (primeTailPatternDeltaCoefficient e ε)
    (fun r => primeTailPatternDeltaCoefficient_norm_le_one e ε r)
    (fun r => orientationWalshCharacter B r.1)
    (primeWalshDeltaApproxCoefficient e ε B)
    (primeWalshDeltaApproxCoefficient_norm_le_one e ε B)
    (fun p => rfl)
    (alpha a) k

theorem boundedPrimeShiftedRotatedJet_sub_eq_arithmeticOfPrimeColumn
    (c d : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (hd : ∀ p, ‖d p‖ ≤ 1)
    (a : ℂ) (k : ℕ) :
    (boundedPrimeShiftedRotatedJet c hc a k).1 -
        (boundedPrimeShiftedRotatedJet d hd a k).1 =
      arithmeticOfPrimeColumn
        (fun p => (c p - d p) * primeShiftFactor a p * rotatedPrimeLogClock p ^ k) := by
  rw [boundedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn,
    boundedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn]
  ext n
  change arithmeticOfPrimeColumn
      (fun p => c p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k) n -
      arithmeticOfPrimeColumn
        (fun p => d p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k) n =
    arithmeticOfPrimeColumn
      (fun p => (c p - d p) * primeShiftFactor a p * rotatedPrimeLogClock p ^ k) n
  by_cases hn : n.Prime
  · rw [arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩]
    ring
  · simp [arithmeticOfPrimeColumn, hn]

theorem boundedPrimeShiftCarrier_sub_jet_mem_base_of_finiteSupport
    (c d : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (hd : ∀ p, ‖d p‖ ≤ 1)
    (hsupport : {p | c p - d p ≠ 0}.Finite) (a : ℂ) (k : ℕ) :
    ∃ b : finitePrimeRationalCoefficientField,
      GaloisForLFunctions.differentialJet k (boundedPrimeShiftCarrier c hc a) -
          GaloisForLFunctions.differentialJet k (boundedPrimeShiftCarrier d hd a) =
        algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField b := by
  let coeff : Nat.Primes → ℂ := fun p =>
    (c p - d p) * primeShiftFactor a p * rotatedPrimeLogClock p ^ k
  have hcoeff : {p | coeff p ≠ 0}.Finite := by
    apply hsupport.subset
    intro p hp
    simp only [Set.mem_setOf_eq, coeff] at hp ⊢
    intro hzero
    exact hp (by rw [hzero, zero_mul, zero_mul])
  let kF : finitePrimeCoefficientField :=
    ⟨algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn coeff),
      (arithmeticOfPrimeColumn_mem_finitePrimeCoefficientField_iff coeff).2 hcoeff⟩
  let b : finitePrimeRationalCoefficientField :=
    algebraMap finitePrimeCoefficientField finitePrimeRationalCoefficientField kF
  refine ⟨b, ?_⟩
  rw [differentialJet_boundedPrimeShiftCarrier,
    differentialJet_boundedPrimeShiftCarrier, ← map_sub, ← map_sub,
    boundedPrimeShiftedRotatedJet_sub_eq_arithmeticOfPrimeColumn]
  change algebraMap arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField kF.1 =
    algebraMap finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField b
  exact (finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap kF).symm

theorem primeWalshShiftPalette_sub_approx_mem_base
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)]
    (alpha : A → ℂ) (B : Finset I) (a : A) (k : ℕ) :
    ∃ b : finitePrimeRationalCoefficientField,
      GaloisForLFunctions.differentialJet k (primeWalshShiftPalette ε alpha (B, a)) -
          GaloisForLFunctions.differentialJet k
            (boundedPrimeShiftCarrier
              (primeWalshDeltaApproxCoefficient e ε B)
              (primeWalshDeltaApproxCoefficient_norm_le_one e ε B)
              (alpha a)) =
        algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField b := by
  unfold primeWalshShiftPalette
  apply boundedPrimeShiftCarrier_sub_jet_mem_base_of_finiteSupport
  simpa only [sub_ne_zero] using primeWalshDeltaResidual_support_finite e ε B

private theorem complexConstant_mem_differentialAdjoin
    {ι : Type*} (x : ι → arithmeticFunctionRationalCoordinateField) (z : ℂ) :
    algebraMap ℂ arithmeticFunctionRationalCoordinateField z ∈
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range x) := by
  rw [IsScalarTower.algebraMap_apply ℂ finitePrimeRationalCoefficientField
    arithmeticFunctionRationalCoordinateField]
  exact IntermediateField.algebraMap_mem _
    (algebraMap ℂ finitePrimeRationalCoefficientField z)

theorem primeTailPatternDeltaShiftPalette_jet_mem_walshDifferentialAdjoin
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    (alpha : A → ℂ) (r : primeRecurringPatternChamber e ε) (a : A) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (primeTailPatternDeltaShiftPalette e ε alpha (r, a)) ∈
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (primeWalshShiftPalette ε alpha)) := by
  classical
  rw [differentialJet_primeTailPatternDeltaShiftPalette_eq_walshSum]
  apply IntermediateField.sum_mem
  intro B hB
  apply IntermediateField.mul_mem
  · exact complexConstant_mem_differentialAdjoin _ _
  · exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin _
      (Set.mem_range_self (B, a)) k

theorem primeWalshShiftPalette_jet_mem_deltaDifferentialAdjoin
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    [Fintype (primeRecurringPatternChamber e ε)]
    (alpha : A → ℂ) (B : Finset I) (a : A) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (primeWalshShiftPalette ε alpha (B, a)) ∈
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (primeTailPatternDeltaShiftPalette e ε alpha)) := by
  classical
  let approxCarrier := boundedPrimeShiftCarrier
    (primeWalshDeltaApproxCoefficient e ε B)
    (primeWalshDeltaApproxCoefficient_norm_le_one e ε B)
    (alpha a)
  obtain ⟨b, hbase⟩ :=
    primeWalshShiftPalette_sub_approx_mem_base e ε alpha B a k
  have happ :=
    differentialJet_primeWalshDeltaApproxShiftPalette_eq_deltaSum e ε alpha B a k
  rw [show GaloisForLFunctions.differentialJet k
        (primeWalshShiftPalette ε alpha (B, a)) =
      (GaloisForLFunctions.differentialJet k
          (primeWalshShiftPalette ε alpha (B, a)) -
        GaloisForLFunctions.differentialJet k approxCarrier) +
          GaloisForLFunctions.differentialJet k approxCarrier by ring]
  change (GaloisForLFunctions.differentialJet k
      (primeWalshShiftPalette ε alpha (B, a)) -
      GaloisForLFunctions.differentialJet k
        (boundedPrimeShiftCarrier
          (primeWalshDeltaApproxCoefficient e ε B)
          (primeWalshDeltaApproxCoefficient_norm_le_one e ε B)
          (alpha a))) + GaloisForLFunctions.differentialJet k approxCarrier ∈ _
  rw [hbase]
  change algebraMap finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField b +
      GaloisForLFunctions.differentialJet k
        (boundedPrimeShiftCarrier
          (primeWalshDeltaApproxCoefficient e ε B)
          (primeWalshDeltaApproxCoefficient_norm_le_one e ε B)
          (alpha a)) ∈ _
  rw [happ]
  apply IntermediateField.add_mem
  · exact IntermediateField.algebraMap_mem _ b
  · apply IntermediateField.sum_mem
    intro r hr
    apply IntermediateField.mul_mem
    · exact complexConstant_mem_differentialAdjoin _ _
    · exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin _
        (Set.mem_range_self (r, a)) k

/-- The full Prime-Walsh shift palette and the recurring-pattern delta palette generate exactly
the same embedded differential field over the finite-prime rational coefficient field. -/
theorem primeWalshShiftPalette_differentialAdjoin_eq_delta
    {I A : Type*} [Fintype I]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool) (alpha : A → ℂ) :
    GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (primeWalshShiftPalette ε alpha)) =
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (primeTailPatternDeltaShiftPalette e ε alpha)) := by
  classical
  letI : Fintype (primeRecurringPatternChamber e ε) := Fintype.ofFinite _
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨_, ⟨⟨B, a⟩, rfl⟩, k, rfl⟩
    exact primeWalshShiftPalette_jet_mem_deltaDifferentialAdjoin
      e ε alpha B a k
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨_, ⟨⟨r, a⟩, rfl⟩, k, rfl⟩
    exact primeTailPatternDeltaShiftPalette_jet_mem_walshDifferentialAdjoin
      e ε alpha r a k

/-- **Exact Prime-Walsh differential rank certificate.**  The recurring-pattern delta family is
differentially independent and generates the full Walsh field.  Hence it is an explicit labelled
differential transcendence basis for that field. -/
theorem primeWalshShiftPalette_differentialBasis
    {I A : Type*} [Fintype I]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (primeTailPatternDeltaShiftPalette e ε alpha) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (primeTailPatternDeltaShiftPalette e ε alpha)) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (primeWalshShiftPalette ε alpha)) := by
  constructor
  · exact primeTailPatternDelta_shiftPalette_differentialIndependent
      e ε alpha hdistinct
  · exact (primeWalshShiftPalette_differentialAdjoin_eq_delta e ε alpha).symm

/-- The number of labelled differential-basis generators is exactly the number of shifts times
the number of recurring finite Boolean patterns.  Together with
`primeWalshShiftPalette_differentialBasis`, this is the card's exact differential rank law. -/
theorem primeWalshDifferentialBasis_card
    {I A : Type*} [Fintype I] [Fintype A]
    (e : ℕ ≃ Nat.Primes) (ε : I → Nat.Primes → Bool) :
    Nat.card (primeRecurringPatternChamber e ε × A) =
      Nat.card A * Nat.card (primeRecurringPatternChamber e ε) := by
  classical
  rw [Nat.card_prod, Nat.mul_comm]

end

end GaloisForLFunctions.HTGeometry
