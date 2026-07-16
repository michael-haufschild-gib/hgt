import GaloisForLFunctions.HTGeometry.DirectionalProjectiveZeroLocusRealization
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# A linearity boundary for commuting cyclic horizons

For a cyclic module over the commutative law algebra `K[X_i]`, a direction `c` admits a finite
nilpotence rule exactly when its linear law form belongs to the radical of the annihilator ideal.
The pullback of that radical is a vector subspace of law space.  Consequently every such commuting
cyclic finite-rule horizon is linear.

This gives a sharp phase separation from the free noncommuting realization.  The nonlinear crossing
cone `c 0 * c 1 = 0` is the exact complete-jet algebraic-dependence horizon of one observable in the
free word field, but it cannot be a commuting cyclic nilpotence horizon.

The qualifier `cyclic nilpotence` is essential.  This file does not classify arbitrary commuting
differential-algebraic systems with nonlinear states, gauge constraints, or prolonged complexes.
It proves that any such enlargement is genuinely necessary before a nonlinear horizon can occur.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

variable {K : Type u} {ι : Type v} [Field K] [Fintype ι]

/-- The law direction `c` as a linear form in the commutative law algebra. -/
def lawLinearForm : (ι → K) →ₗ[K] MvPolynomial ι K :=
  Fintype.linearCombination K (X : ι → MvPolynomial ι K)

/-- Distinct law directions define distinct linear law forms. -/
theorem lawLinearForm_injective :
    Function.Injective (lawLinearForm (K := K) (ι := ι)) :=
  (MvPolynomial.linearIndependent_X (σ := ι) (R := K)).fintypeLinearCombination_injective

/-- Every directional law form is homogeneous of degree one. -/
theorem lawLinearForm_isHomogeneous (c : ι → K) :
    (lawLinearForm c).IsHomogeneous 1 := by
  change Fintype.linearCombination K (X : ι → MvPolynomial ι K) c ∈
    MvPolynomial.homogeneousSubmodule ι K 1
  rw [Fintype.linearCombination_apply]
  exact (MvPolynomial.homogeneousSubmodule ι K 1).sum_smul_mem c
    fun i _ => MvPolynomial.isHomogeneous_X K i

/-- Directions whose commutative cyclic action is nilpotent modulo `I`.  Taking the radical makes
the existential finite exponent intrinsic and exhibits the horizon as a linear subspace. -/
def commutingCyclicNilpotenceHorizon
    (I : Ideal (MvPolynomial ι K)) : Submodule K (ι → K) :=
  (I.radical.restrictScalars K).comap
    (lawLinearForm (K := K) (ι := ι))

/-- A direction lies on the cyclic finite-rule horizon exactly when some positive-or-zero power
of its law form lies in the annihilator ideal.  The zero exponent correctly makes the horizon total
when `I = ⊤`. -/
theorem mem_commutingCyclicNilpotenceHorizon_iff
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) :
    c ∈ commutingCyclicNilpotenceHorizon I ↔
      ∃ n : ℕ, (lawLinearForm c) ^ n ∈ I := by
  change lawLinearForm c ∈ I.radical ↔ _
  exact Ideal.mem_radical_iff

/-- A nontrivial finite linear relation among the powers of one cyclic law element, modulo `I`. -/
def HasFiniteCyclicLinearRelation
    (I : Ideal (MvPolynomial ι K)) (x : MvPolynomial ι K) : Prop :=
  ∃ s : Finset ℕ, ∃ a : ℕ → K,
    (∃ n ∈ s, a n ≠ 0) ∧
      (∑ n ∈ s, C (a n) * x ^ n) ∈ I

omit [Fintype ι] in
/-- **Graded cyclic relation collapse.**  In a homogeneous cyclic law module, an arbitrary finite
linear relation mixing different differential orders exists exactly when one pure power vanishes.
Homogeneity prevents cancellation between different jet orders. -/
theorem homogeneous_finiteCyclicRelation_iff_radical
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (x : MvPolynomial ι K) (hx : x.IsHomogeneous 1) :
    HasFiniteCyclicLinearRelation I x ↔ x ∈ I.radical := by
  constructor
  · rintro ⟨s, a, ⟨n, hn, han⟩, hrel⟩
    have hcomp := hI n hrel
    rw [← DirectSum.Decomposition.decompose'_eq,
      MvPolynomial.decomposition.decompose'_apply] at hcomp
    have hterm : ∀ k : ℕ,
        homogeneousComponent n (C (a k) * x ^ k) =
          if n = k then C (a k) * x ^ k else 0 := by
      intro k
      simpa only [one_mul] using
        homogeneousComponent_of_mem ((hx.pow k).C_mul (a k))
    simp only [map_sum, hterm] at hcomp
    have hisolate : C (a n) * x ^ n ∈ I := by
      simpa [Finset.sum_eq_single n, hn] using hcomp
    have hpower : x ^ n ∈ I := by
      have hmul := I.mul_mem_left (C ((a n)⁻¹)) hisolate
      simpa [han] using hmul
    exact ⟨n, hpower⟩
  · rintro ⟨n, hn⟩
    refine ⟨{n}, fun k => if k = n then 1 else 0, ?_, ?_⟩
    · exact ⟨n, Finset.mem_singleton_self n, by simp⟩
    · simpa using hn

/-- For a homogeneous annihilator, the complete finite linear-rule horizon of the directional law
form is exactly the radical subspace already defined by `commutingCyclicNilpotenceHorizon`. -/
theorem lawLinearForm_hasFiniteCyclicLinearRelation_iff
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (c : ι → K) :
    HasFiniteCyclicLinearRelation I (lawLinearForm c) ↔
      c ∈ commutingCyclicNilpotenceHorizon I := by
  rw [homogeneous_finiteCyclicRelation_iff_radical I hI _
    (lawLinearForm_isHomogeneous c)]
  rfl

/-- **Commuting cyclic linearity law.**  Finite-rule directions are closed under superposition. -/
theorem commutingCyclicNilpotenceHorizon_add_mem
    (I : Ideal (MvPolynomial ι K)) {c e : ι → K}
    (hc : c ∈ commutingCyclicNilpotenceHorizon I)
    (he : e ∈ commutingCyclicNilpotenceHorizon I) :
    c + e ∈ commutingCyclicNilpotenceHorizon I :=
  (commutingCyclicNilpotenceHorizon I).add_mem hc he

/-- The simplest reducible nonlinear cone: the union of the two coordinate law axes. -/
def crossingCone (K : Type u) [Field K] : Set (Fin 2 → K) :=
  {c | c 0 * c 1 = 0}

/-- The crossing cone is not the carrier of a vector subspace: it contains both axes but not their
generic superposition. -/
theorem crossingCone_not_submodule :
    ∀ H : Submodule K (Fin 2 → K), (H : Set (Fin 2 → K)) ≠ crossingCone K := by
  intro H hEq
  let e0 : Fin 2 → K := Pi.single 0 1
  let e1 : Fin 2 → K := Pi.single 1 1
  have he0 : e0 ∈ H := by
    change e0 ∈ (H : Set (Fin 2 → K))
    rw [hEq]
    simp [crossingCone, e0]
  have he1 : e1 ∈ H := by
    change e1 ∈ (H : Set (Fin 2 → K))
    rw [hEq]
    simp [crossingCone, e1]
  have hsum : e0 + e1 ∈ crossingCone K := by
    rw [← hEq]
    exact H.add_mem he0 he1
  simp [crossingCone, e0, e1] at hsum

/-- No annihilator ideal in the commutative cyclic law algebra has the crossing cone as its finite
nilpotence horizon. -/
theorem crossingCone_not_commutingCyclicNilpotenceHorizon
    (I : Ideal (MvPolynomial (Fin 2) K)) :
    ((commutingCyclicNilpotenceHorizon I : Submodule K (Fin 2 → K)) :
        Set (Fin 2 → K)) ≠ crossingCone K :=
  crossingCone_not_submodule _

/-- The homogeneous crossing equation. -/
def crossingEquation : Fin 1 → MvPolynomial (Fin 2) K :=
  fun _ ↦ X 0 * X 1

/-- The crossing equation has degree two. -/
theorem crossingEquation_isHomogeneous :
    ∀ j, (crossingEquation (K := K) j).IsHomogeneous 2 := by
  intro j
  simpa [crossingEquation] using
    (MvPolynomial.isHomogeneous_X K (0 : Fin 2)).mul
      (MvPolynomial.isHomogeneous_X K (1 : Fin 2))

/-- The same nonlinear crossing is an exact complete-jet dependence horizon for one observable in
the free noncommuting word field; away from it, the entire directional jet is algebraically
independent. -/
theorem exists_completeJet_crossingHorizon :
    ∃ a : CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2) →
        ProjectiveWordState (Fin 2) → K,
      ∀ (c : Fin 2 → K), (∃ i, c i ≠ 0) →
        ((¬ AlgebraicIndependent K
            (fun r : ℕ ↦ directionalJet
              (projectiveCompleteDerivation a 3) c r
              (projectiveCompleteRoot
                (K := K) (ι := Fin 2)
                (η := CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2))))) ↔
          c ∈ crossingCone K) := by
  obtain ⟨a, ha⟩ :=
    exists_completeJet_horizon_eq_finiteHomogeneousZeroLocus
      (crossingEquation (K := K)) (fun _ : Fin 1 ↦ 2)
      (crossingEquation_isHomogeneous (K := K))
  refine ⟨a, ?_⟩
  intro c hc
  simpa [crossingEquation, crossingCone] using ha c hc

/-- **Free/commuting phase separation.**  The crossing horizon is fully realizable by one
free-word observable, but is excluded from every commuting cyclic finite-annihilation model. -/
theorem crossingHorizon_free_realizable_commutingCyclic_impossible :
    (∃ a : CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2) →
        ProjectiveWordState (Fin 2) → K,
      ∀ (c : Fin 2 → K), (∃ i, c i ≠ 0) →
        ((¬ AlgebraicIndependent K
            (fun r : ℕ ↦ directionalJet
              (projectiveCompleteDerivation a 3) c r
              (projectiveCompleteRoot
                (K := K) (ι := Fin 2)
                (η := CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2))))) ↔
          c ∈ crossingCone K)) ∧
      (∀ I : Ideal (MvPolynomial (Fin 2) K),
        ((commutingCyclicNilpotenceHorizon I : Submodule K (Fin 2 → K)) :
            Set (Fin 2 → K)) ≠ crossingCone K) := by
  exact ⟨exists_completeJet_crossingHorizon,
    crossingCone_not_commutingCyclicNilpotenceHorizon⟩

end

end GaloisForLFunctions.HTGeometry
