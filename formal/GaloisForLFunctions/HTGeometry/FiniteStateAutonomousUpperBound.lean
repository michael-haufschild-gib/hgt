import GaloisForLFunctions.HTGeometry.AutonomousReciprocalAperture
import GaloisForLFunctions.HTGeometry.FiniteGeneratorDifferentialEscape
import GaloisForLFunctions.HTGeometry.StateFieldTrdeg
import GaloisForLFunctions.HTGeometry.JetHorizonTorsorTower
import GaloisForLFunctions.HTGeometry.ScalarDifferentialOrderUpperBound

/-!
# Order bound for observables of a finite-dimensional differential state

Let `K / F` be an extension of differential fields and `state : d → K` a finite family whose
derivatives lie in the field `F(state)` it generates, i.e. a finite-dimensional autonomous
first-order system over `F`. This module proves that every element `x` of `F(state)` satisfies an
algebraic differential equation of order at most `|d|` over `F`: the jets `x, x', …, x^(|d|)` are
algebraically dependent over `F`. The reason is that `F(state)` is closed under the derivation and
has transcendence degree at most `|d|` over `F`.

## Main results

- `not_algebraicIndependent_jets_of_mem_finite_derivationClosed_state`: if each `(state i)′` lies
  in `F(state)` and `x ∈ F(state)`, then the `|d| + 1` jets `x^(0), …, x^(|d|)` are not
  algebraically independent over `F`.

## Hypotheses

Unconditional. The theorem assumes only the closure hypothesis `hstate` (each derivative of a state
component lies in `F(state)`) and membership `x ∈ F(state)`; `d` is a finite type.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- If `state : d → K` is a finite family with every `(state i)′ ∈ F(state)` (`hstate`), then for
each `x ∈ F(state)` the jets `x, x', …, x^(|d|)` are algebraically dependent over `F`; that is,
`x` satisfies an algebraic differential equation of order at most `|d|`. -/
theorem not_algebraicIndependent_jets_of_mem_finite_derivationClosed_state
    {F K d : Type} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    [Fintype d]
    (state : d → K)
    (hstate : ∀ i, (state i)′ ∈
      IntermediateField.adjoin F (Set.range state))
    {x : K} (hx : x ∈ IntermediateField.adjoin F (Set.range state)) :
    ¬ AlgebraicIndependent F
      (fun i : Fin (Fintype.card d + 1) => differentialJet (i : ℕ) x) := by
  let M : IntermediateField F K :=
    IntermediateField.adjoin F (Set.range state)
  have hclosed : DerivationClosed M :=
    derivationClosed_adjoin_range_of_deriv_mem state hstate
  have hjets : ∀ i : Fin (Fintype.card d + 1),
      differentialJet (i : ℕ) x ∈ M := by
    intro i
    exact differentialJet_mem_of_derivationClosed_jetHorizonTorsorTower hclosed (i : ℕ) hx
  have htr : Algebra.trdeg F M ≤ ((Fintype.card d : ℕ) : Cardinal) := by
    have hbase := trdeg_intermediateFieldAdjoin_range_le
      (F := F) (E := K) (I := d) state
    change Algebra.trdeg F M ≤ Cardinal.mk d at hbase
    rw [Cardinal.mk_fintype] at hbase
    exact hbase
  let y : Fin (Fintype.card d + 1) → M := fun i =>
    ⟨differentialJet (i : ℕ) x, hjets i⟩
  have hdepM : ¬ AlgebraicIndependent F y :=
    not_algebraicIndependent_of_trdeg_le htr y
  rw [algebraicIndependent_iff_injective_aeval] at hdepM
  obtain ⟨Q₁, Q₂, hEq, hne⟩ := Function.not_injective_iff.mp hdepM
  let Q : MvPolynomial (Fin (Fintype.card d + 1)) F := Q₁ - Q₂
  have hQ0 : Q ≠ 0 := sub_ne_zero.mpr hne
  have hQy : MvPolynomial.aeval y Q = 0 := by
    simp only [Q, map_sub, hEq, sub_self]
  have hpush : MvPolynomial.aeval
      (fun i : Fin (Fintype.card d + 1) => differentialJet (i : ℕ) x) Q = 0 := by
    have hcomp := MvPolynomial.comp_aeval_apply y M.val Q
    rw [hQy, map_zero] at hcomp
    exact hcomp.symm
  rw [algebraicIndependent_iff]
  intro h
  exact hQ0 (h Q hpush)

end

end GaloisForLFunctions.HTGeometry
