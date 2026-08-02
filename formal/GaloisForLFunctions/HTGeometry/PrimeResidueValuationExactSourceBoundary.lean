import GaloisForLFunctions.HTGeometry.PrimeClockAnalyticExactCorrespondence
import GaloisForLFunctions.HTGeometry.PrimeResidueValuationPrimitiveBarrier

/-!
# Exact source boundary for residue--valuation completion

The complete residue--valuation family and a primitive source with infinitely many private
valuation layers form one free logarithmic-clock family.  Consequently the primitive analytic
carrier remains differentially independent after adjoining both every finite-prime Euler germ
and the full residue--valuation fusion completion.

This is an exact source statement, not only a one-way obstruction: analytic realization over the
local Euler base preserves the nonzero primitive quotient class.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

attribute [local instance]
  analyticObservableUpperEndAnalyticDomain
  analyticObservableUpperEndMeroComplexAlgebra
  analyticObservableUpperEndMeroDifferential

local instance exactBoundaryPulledCoordinateComplexAlgebra :
    Algebra ℂ analyticPulledFinitePrimeCoordinateField :=
  ((algebraMap finiteAbscissaFinitePrimeCoefficientField
      analyticPulledFinitePrimeCoordinateField).comp
    (algebraMap ℂ finiteAbscissaFinitePrimeCoefficientField)).toAlgebra

/-- A source with infinitely many nowhere-vanishing valuation layers remains clock-free jointly
with the complete residue--valuation family.  Every proposed relation has finite support, hence
misses a private layer of the primitive source. -/
theorem primeResidueValuationPrimitive_clockIndependent
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (F : finiteAbscissaArithmeticSubalgebra)
    (hinf : ¬ {e : Nat |
      ∀ p : Nat.Primes, F.1 ((p : Nat) ^ (e + 1)) ≠ 0}.Finite) :
    PrimeProfileClockIndependent
      (Sum.elim (fun _ : Unit => F.1)
        (fun x : ℕ × (∀ i, A i) =>
          (finiteAbscissaPrimePowerDilation x.1
            (primeResidueFiniteAbscissaSource A y x.2)).1)) := by
  classical
  let oldSource : (ℕ × (∀ i, A i)) → ArithmeticFunction ℂ := fun x =>
    (finiteAbscissaPrimePowerDilation x.1
      (primeResidueFiniteAbscissaSource A y x.2)).1
  let totalSource : Unit ⊕ (ℕ × (∀ i, A i)) → ArithmeticFunction ℂ :=
    Sum.elim (fun _ : Unit => F.1) oldSource
  have hOld : PrimeProfileClockIndependent oldSource := by
    simpa only [oldSource] using
      cofiniteTailDenseOn_primeResidueValuationAllLayerSource_clockIndependent
        A y hy
  unfold PrimeProfileClockIndependent
  rw [linearIndependent_iff']
  intro s c hsum q hq
  let usedOld : Finset (ℕ × (∀ i, A i)) :=
    s.biUnion fun z =>
      match z.1 with
      | Sum.inl _ => ∅
      | Sum.inr x => {x}
  let H := {x : ℕ × (∀ i, A i) // x ∈ usedOld}
  let usedDepth : Finset ℕ := usedOld.image Prod.fst
  obtain ⟨e₀, he₀nonzero, he₀unused⟩ :=
    exists_nonvanishing_layer_notMem F.1 hinf usedDepth
  have hHClock : PrimeProfileClockIndependent (fun z : H => oldSource z.1) := by
    unfold PrimeProfileClockIndependent at hOld ⊢
    let embedOld : H × ℕ → (ℕ × (∀ i, A i)) × ℕ :=
      fun z => (z.1.1, z.2)
    exact hOld.comp embedOld (by
      intro z w hzw
      have hzw' : (z.1.1, z.2) = (w.1.1, w.2) := hzw
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg
          (fun r : (ℕ × (∀ i, A i)) × ℕ => r.1) hzw'
      · exact congrArg
          (fun r : (ℕ × (∀ i, A i)) × ℕ => r.2) hzw')
  have hHzero : ∀ z : H, ∀ p : Nat.Primes,
      oldSource z ((p : ℕ) ^ (e₀ + 1)) = 0 := by
    intro z p
    have hzDepth : z.1.1 ≠ e₀ := by
      intro hze
      apply he₀unused
      apply Finset.mem_image.mpr
      exact ⟨z.1, z.2, hze⟩
    exact finiteAbscissaPrimePowerDilation_apply_primePower_of_ne
      z.1.1 e₀
      (primeResidueFiniteAbscissaSource A y z.1.2)
      (primeResidueInteractionCoefficient A y z.1.2)
      rfl hzDepth p
  have hLocal :
      PrimeProfileClockIndependent
        (Sum.elim (fun _ : Unit => F.1) (fun z : H => oldSource z.1)) :=
    privateLayerClockIndependence F.1 (fun z : H => oldSource z.1)
      hHClock e₀ hHzero he₀nonzero
  let lift :
      (z : (Unit ⊕ (ℕ × (∀ i, A i))) × ℕ) →
        z ∈ s → Unit ⊕ H
    | (Sum.inl u, _), _ => Sum.inl u
    | (Sum.inr x, n), hx => Sum.inr ⟨x, by
        apply Finset.mem_biUnion.mpr
        exact ⟨(Sum.inr x, n), hx, Finset.mem_singleton_self x⟩⟩
  let embed : s → (Unit ⊕ H) × ℕ := fun z =>
    (lift z.1 z.2, z.1.2)
  let project : (Unit ⊕ H) × ℕ →
      (Unit ⊕ (ℕ × (∀ i, A i))) × ℕ := fun z =>
    (match z.1 with
      | Sum.inl u => Sum.inl u
      | Sum.inr x => Sum.inr x.1,
      z.2)
  have hproject : ∀ z : s, project (embed z) = z.1 := by
    rintro ⟨⟨i, n⟩, hz⟩
    rcases i with u | x <;> rfl
  have hembed : Function.Injective embed := by
    intro z w hzw
    apply Subtype.ext
    rw [← hproject z, ← hproject w, hzw]
  have hsub := hLocal.comp embed hembed
  have hsum' :
      ∑ z : s, c z.1 •
        primeProfileClockJetFamily
          (Sum.elim (fun _ : Unit => F.1) (fun z : H => oldSource z.1))
          (embed z) = 0 := by
    have hsumAttach :
        ∑ z : s, c z.1 •
          primeProfileClockJetFamily totalSource z.1 = 0 := by
      rw [← s.sum_attach] at hsum
      simpa only [Finset.attach_eq_univ, totalSource, oldSource] using hsum
    calc
      ∑ z : s, c z.1 •
          primeProfileClockJetFamily
            (Sum.elim (fun _ : Unit => F.1) (fun z : H => oldSource z.1))
            (embed z) =
        ∑ z : s, c z.1 • primeProfileClockJetFamily totalSource z.1 := by
          apply Finset.sum_congr rfl
          intro z hz
          congr 1
          rcases z with ⟨⟨i, n⟩, hmem⟩
          rcases i with u | x <;> rfl
      _ = 0 := hsumAttach
  exact Fintype.linearIndependent_iff.mp hsub
    (fun z : s => c z.1) hsum' ⟨q, hq⟩

/-- The primitive source has a nonzero free clock orbit in the quotient by the complete
residue--valuation clock submodule. -/
theorem primeResidueValuationPrimitive_relativeClockIndependent
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (F : finiteAbscissaArithmeticSubalgebra)
    (hinf : ¬ {e : Nat |
      ∀ p : Nat.Primes, F.1 ((p : Nat) ^ (e + 1)) ≠ 0}.Finite) :
    PrimeProfileRelativeClockIndependent
      (fun x : ℕ × (∀ i, A i) =>
        (finiteAbscissaPrimePowerDilation x.1
          (primeResidueFiniteAbscissaSource A y x.2)).1)
      (fun _ : Unit => F.1) := by
  let oldSource : (ℕ × (∀ i, A i)) → ArithmeticFunction ℂ := fun x =>
    (finiteAbscissaPrimePowerDilation x.1
      (primeResidueFiniteAbscissaSource A y x.2)).1
  let newSource : Unit → ArithmeticFunction ℂ := fun _ => F.1
  have hcombined :
      PrimeProfileClockIndependent (Sum.elim newSource oldSource) := by
    simpa only [newSource, oldSource] using
      primeResidueValuationPrimitive_clockIndependent A y hy F hinf
  have hjoint :
      LinearIndependent ℂ
        (Sum.elim (primeProfileClockJetFamily newSource)
          (primeProfileClockJetFamily oldSource)) :=
    (primeProfileClockIndependent_sumElim_iff newSource oldSource).mp hcombined
  have hswap := hjoint.comp
    (Equiv.sumComm
      ((ℕ × (∀ i, A i)) × ℕ) (Unit × ℕ))
    (Equiv.sumComm
      ((ℕ × (∀ i, A i)) × ℕ) (Unit × ℕ)).injective
  have hfamily :
      (Sum.elim (primeProfileClockJetFamily newSource)
          (primeProfileClockJetFamily oldSource)) ∘
        (Equiv.sumComm
          ((ℕ × (∀ i, A i)) × ℕ) (Unit × ℕ)) =
      Sum.elim (primeProfileClockJetFamily oldSource)
        (primeProfileClockJetFamily newSource) := by
    funext z
    rcases z with z | z <;> rfl
  rw [hfamily] at hswap
  have hquot :=
    (linearIndependent_sumElim_iff_quotient
      (primeProfileClockJetFamily oldSource)
      (primeProfileClockJetFamily newSource)).mp hswap |>.2
  change PrimeProfileRelativeClockIndependent oldSource newSource
  exact hquot

/-- The local-Euler residue--valuation completion: adjoin every finite-prime Euler germ first,
then the complete depth--residue carrier family and all of its differential jets. -/
def primeResidueValuationLocalEulerFusionCompletionField
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) :
    IntermediateField analyticPulledFinitePrimeCoordinateField upperEndMeroField :=
  GaloisForLFunctions.differentialAdjoin
    analyticPulledFinitePrimeCoordinateField
    (Set.range (primeResidueValuationUpperEndAllLayerCarrier A y))

/-- **Exact local-Euler primitive boundary.** A positive-prime-power source with infinitely many
private valuation layers is differentially independent over the field containing the genuine
coordinate, every finite-prime Euler germ, and the complete residue--valuation fusion family.
Equivalently, none of these analytic completions absorbs its source-quotient direction. -/
theorem analyticPrimeProfileCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (F : finiteAbscissaArithmeticSubalgebra)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers F.1)
    (hinf : ¬ {e : Nat |
      ∀ p : Nat.Primes, F.1 ((p : Nat) ^ (e + 1)) ≠ 0}.Finite) :
    GaloisForLFunctions.DifferentialIndependent
      (primeResidueValuationLocalEulerFusionCompletionField A y)
      (fun _ : Unit => finiteAbscissaLSeriesToUpperEndMero F) := by
  let oldSource :
      (ℕ × (∀ i, A i)) → finiteAbscissaArithmeticSubalgebra := fun x =>
    finiteAbscissaPrimePowerDilation x.1
      (primeResidueFiniteAbscissaSource A y x.2)
  let newSource : Unit → finiteAbscissaArithmeticSubalgebra := fun _ => F
  have hOldSupport : ∀ x,
      PrimeProfileSupportedOnPositivePrimePowers (oldSource x).1 := by
    intro x
    apply finiteAbscissaPrimePowerDilation_supportedOnPositivePrimePowers
      x.1 (primeResidueFiniteAbscissaSource A y x.2)
      (primeResidueInteractionCoefficient A y x.2)
    rfl
  have hOldClock : PrimeProfileClockIndependent (fun x => (oldSource x).1) := by
    simpa only [oldSource] using
      cofiniteTailDenseOn_primeResidueValuationAllLayerSource_clockIndependent
        A y hy
  have hRelative :
      PrimeProfileRelativeClockIndependent
        (fun x => (oldSource x).1) (fun h => (newSource h).1) := by
    simpa only [oldSource, newSource] using
      primeResidueValuationPrimitive_relativeClockIndependent A y hy F hinf
  have hexact :=
    (differentialIndependent_finiteAbscissaPrimeProfiles_relative_iff_clockQuotient
      oldSource newSource hOldSupport (fun _ => hsupport) hOldClock).mpr hRelative
  change GaloisForLFunctions.DifferentialIndependent
    (GaloisForLFunctions.differentialAdjoin
      analyticPulledFinitePrimeCoordinateField
      (Set.range fun x : ℕ × (∀ i, A i) =>
        finiteAbscissaLSeriesToUpperEndMero
          (finiteAbscissaPrimePowerDilation x.1
            (primeResidueFiniteAbscissaSource A y x.2))))
    (fun _ : Unit => finiteAbscissaLSeriesToUpperEndMero F)
  simpa only [oldSource, newSource] using hexact

/-- The exact local-Euler primitive boundary is hypertranscendental. -/
theorem analyticPrimeProfileCarrier_hypertranscendentalOver_localEulerResidueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (F : finiteAbscissaArithmeticSubalgebra)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers F.1)
    (hinf : ¬ {e : Nat |
      ∀ p : Nat.Primes, F.1 ((p : Nat) ^ (e + 1)) ≠ 0}.Finite) :
    HypertranscendentalOver
      (primeResidueValuationLocalEulerFusionCompletionField A y)
      (finiteAbscissaLSeriesToUpperEndMero F) := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact
    analyticPrimeProfileCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
      A y hy F hsupport hinf

/-- Every jet of a rational coordinate gauge lies in the local-Euler fusion completion. -/
theorem differentialJet_mem_localEulerResidueFusionCompletion_of_mem_rationalCoordinate
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (x : upperEndMeroField) (hx : x ∈ upperEndRationalCoordinateField)
    (n : Nat) :
    GaloisForLFunctions.differentialJet n x ∈
      primeResidueValuationLocalEulerFusionCompletionField A y := by
  have hcoord : ∀ k : Nat, GaloisForLFunctions.differentialJet k x ∈
      upperEndRationalCoordinateField := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
        rw [GaloisForLFunctions.differentialJet_succ]
        exact upperEndRationalCoordinateField_derivationClosed ih
  have hpulled :
      GaloisForLFunctions.differentialJet n x ∈
        analyticPulledFinitePrimeCoordinateField :=
    upperEndRationalCoordinateField_le_pulledFinitePrimeCoordinate (hcoord n)
  exact IntermediateField.algebraMap_mem
    (primeResidueValuationLocalEulerFusionCompletionField A y)
    ⟨GaloisForLFunctions.differentialJet n x, hpulled⟩

/-- Rational coordinate calibration cannot remove the exact local-Euler primitive boundary. -/
theorem differentialIndependent_over_localEulerResidueFusionCompletion_add_rationalCoordinate
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    {J : Type*} {x : J → upperEndMeroField}
    (hx : GaloisForLFunctions.DifferentialIndependent
      (primeResidueValuationLocalEulerFusionCompletionField A y) x)
    (r : J → upperEndMeroField)
    (hr : ∀ j, r j ∈ upperEndRationalCoordinateField) :
    GaloisForLFunctions.DifferentialIndependent
      (primeResidueValuationLocalEulerFusionCompletionField A y)
      (fun j => x j + r j) := by
  apply hx.addOfJetsInBase
  intro j n
  exact ⟨⟨GaloisForLFunctions.differentialJet n (r j),
    differentialJet_mem_localEulerResidueFusionCompletion_of_mem_rationalCoordinate
      A y (r j) (hr j) n⟩, rfl⟩

end

end GaloisForLFunctions.HTGeometry
