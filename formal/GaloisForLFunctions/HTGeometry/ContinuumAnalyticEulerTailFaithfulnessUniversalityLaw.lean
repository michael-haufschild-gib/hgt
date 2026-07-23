import GaloisForLFunctions.HTGeometry.AnalyticEulerTailQuotientRealization
import GaloisForLFunctions.HTGeometry.ContinuumPrimeCoherenceSaturation

/-!
# Continuum analytic Euler-tail faithfulness universality

Sparse coherent Boolean orientations are tail-independent in every finite subfamily.  This file
places that statement in the corpus's canonical bounded prime-source quotient: the full Boolean
continuum becomes a linearly independent frame, so the quotient has rank at least continuum.

The canonical analytic all-jet Euler realization need not yet be known injective on its whole
domain.  On this universal frame, however, faithfulness has an exact answer: the analytic images
remain linearly independent if and only if the frame span is disjoint from the realization kernel.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A Boolean prime orientation, bundled as a uniformly bounded complex prime source. -/
def boundedPrimeOrientationSource (epsilon : Nat.Primes → Bool) :
    BoundedPrimeSource :=
  ⟨fun p => primeDirichletSign (epsilon p), ⟨1, by
    intro p
    cases h : epsilon p <;> simp [primeDirichletSign, h]⟩⟩

/-- The intrinsic cofinite-tail class of a Boolean prime orientation. -/
def boundedPrimeOrientationTailClass (epsilon : Nat.Primes → Bool) :
    BoundedPrimeTailSpace :=
  boundedPrimeFiniteSupportSubmodule.mkQ
    (boundedPrimeOrientationSource epsilon)

/-- Finite coefficientwise tail independence is exactly ordinary linear independence of the
corresponding classes in the bounded source quotient. -/
theorem primeOrientationTailIndependent_iff_linearIndependent_boundedTailClass
    {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon : I → Nat.Primes → Bool) :
    PrimeOrientationTailIndependent epsilon ↔
      LinearIndependent ℂ
        (fun i => boundedPrimeOrientationTailClass (epsilon i)) := by
  constructor
  · intro htail
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    apply congrFun (htail c ?_) i
    have hclass :
        boundedPrimeFiniteSupportSubmodule.mkQ
            (∑ i, c i • boundedPrimeOrientationSource (epsilon i)) = 0 := by
      simpa only [map_sum, map_smul, boundedPrimeOrientationTailClass] using hc
    have hmem :
        (∑ i, c i • boundedPrimeOrientationSource (epsilon i)) ∈
          boundedPrimeFiniteSupportSubmodule := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hclass
    change
      (Function.support
        (((∑ i, c i • boundedPrimeOrientationSource (epsilon i)) :
          BoundedPrimeSource) : Nat.Primes → ℂ)).Finite at hmem
    simpa only [Function.support, Set.mem_setOf_eq, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
      boundedPrimeOrientationSource] using hmem
  · intro hlinear c hfinite
    funext i
    exact Fintype.linearIndependent_iff.mp hlinear c (by
      have hmem :
          (∑ j, c j • boundedPrimeOrientationSource (epsilon j)) ∈
            boundedPrimeFiniteSupportSubmodule := by
        change
          (Function.support
            (((∑ j, c j • boundedPrimeOrientationSource (epsilon j)) :
              BoundedPrimeSource) : Nat.Primes → ℂ)).Finite
        simpa only [Function.support, Set.mem_setOf_eq, Submodule.coe_sum,
          Finset.sum_apply, Submodule.coe_smul_of_tower, Pi.smul_apply,
          smul_eq_mul, boundedPrimeOrientationSource] using hfinite
      have hclass :
          boundedPrimeFiniteSupportSubmodule.mkQ
              (∑ j, c j • boundedPrimeOrientationSource (epsilon j)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hmem
      simpa only [map_sum, map_smul, boundedPrimeOrientationTailClass] using hclass) i

/-- The whole sparse coherent Boolean continuum is linearly independent after quotienting bounded
prime sources by finite support. -/
theorem continuumSparsePrimeOrientation_boundedTailClass_linearIndependent
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) :
    LinearIndependent ℂ
      (fun z : ℕ → Bool =>
        boundedPrimeOrientationTailClass
          (continuumSparsePrimeOrientation base e z)) := by
  rw [linearIndependent_iff']
  intro s c hsum i hi
  letI : Fintype s := Fintype.ofFinset s (fun x => by simp)
  letI : DecidableEq s := Classical.decEq s
  let epsilon : s → Nat.Primes → Bool :=
    fun z => continuumSparsePrimeOrientation base e z.1
  have htail : PrimeOrientationTailIndependent epsilon := by
    exact basedSparsePrefixOrientation_tailIndependent base e
      (fun z : s => z.1) Subtype.val_injective
  have hlinear :
      LinearIndependent ℂ
        (fun z : s => boundedPrimeOrientationTailClass (epsilon z)) :=
    (primeOrientationTailIndependent_iff_linearIndependent_boundedTailClass
      epsilon).mp htail
  have hsum' :
      ∑ z : s, c z.1 • boundedPrimeOrientationTailClass (epsilon z) = 0 := by
    rw [← s.sum_attach] at hsum
    simpa only [Finset.attach_eq_univ, epsilon] using hsum
  exact Fintype.linearIndependent_iff.mp hlinear (fun z : s => c z.1)
    hsum' ⟨i, hi⟩

/-- The bounded prime-tail source quotient has complex module rank at least continuum. -/
theorem continuum_le_rank_boundedPrimeTailSpace
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) :
    Cardinal.continuum ≤ Module.rank ℂ BoundedPrimeTailSpace := by
  calc
    Cardinal.continuum = Cardinal.mk (ℕ → Bool) :=
      mk_boolSequence_eq_continuum.symm
    _ ≤ Module.rank ℂ BoundedPrimeTailSpace :=
      (continuumSparsePrimeOrientation_boundedTailClass_linearIndependent
        base e).cardinal_le_rank

/-- Exact analytic faithfulness criterion on the universal continuum source frame. -/
theorem continuumSparsePrime_analyticAllJetFaithful_iff
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) (a : ℂ) :
    LinearIndependent ℂ
        (fun z : ℕ → Bool =>
          analyticEulerTailAllJetRealization a
            (boundedPrimeOrientationTailClass
              (continuumSparsePrimeOrientation base e z))) ↔
      Disjoint
        (Submodule.span ℂ
          (Set.range fun z : ℕ → Bool =>
            boundedPrimeOrientationTailClass
              (continuumSparsePrimeOrientation base e z)))
        (LinearMap.ker (analyticEulerTailAllJetRealization a)) := by
  let v : (ℕ → Bool) → BoundedPrimeTailSpace :=
    fun z => boundedPrimeOrientationTailClass
      (continuumSparsePrimeOrientation base e z)
  let f := analyticEulerTailAllJetRealization a
  change LinearIndependent ℂ (f ∘ v) ↔
    Disjoint (Submodule.span ℂ (Set.range v)) (LinearMap.ker f)
  constructor
  · exact Submodule.range_ker_disjoint
  · intro hdisjoint
    exact (continuumSparsePrimeOrientation_boundedTailClass_linearIndependent
      base e).map hdisjoint

/-- **Continuum analytic Euler-tail faithfulness universality law.**  One sparse coherent Boolean
continuum is an intrinsic linearly independent frame in the bounded prime-tail quotient, forces
continuum source rank, and has analytically independent all-jet images exactly off the all-jet
kernel. -/
theorem continuumPrime_analyticEulerTailFaithfulnessUniversality
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) :
    LinearIndependent ℂ
        (fun z : ℕ → Bool =>
          boundedPrimeOrientationTailClass
            (continuumSparsePrimeOrientation base e z)) ∧
      Cardinal.continuum ≤ Module.rank ℂ BoundedPrimeTailSpace ∧
      ∀ a : ℂ,
        (LinearIndependent ℂ
            (fun z : ℕ → Bool =>
              analyticEulerTailAllJetRealization a
                (boundedPrimeOrientationTailClass
                  (continuumSparsePrimeOrientation base e z))) ↔
          Disjoint
            (Submodule.span ℂ
              (Set.range fun z : ℕ → Bool =>
                boundedPrimeOrientationTailClass
                  (continuumSparsePrimeOrientation base e z)))
            (LinearMap.ker (analyticEulerTailAllJetRealization a))) := by
  exact ⟨
    continuumSparsePrimeOrientation_boundedTailClass_linearIndependent base e,
    continuum_le_rank_boundedPrimeTailSpace base e,
    continuumSparsePrime_analyticAllJetFaithful_iff base e⟩

end

end GaloisForLFunctions.HTGeometry
