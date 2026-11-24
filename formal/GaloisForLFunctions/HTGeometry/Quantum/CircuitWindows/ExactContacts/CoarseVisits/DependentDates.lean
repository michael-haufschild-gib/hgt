import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.PhasePolynomial
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.MvPolynomial.Tower

/-! # Algebraic relations between the phases of independent clocks -/

open Set MvPolynomial
namespace GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
noncomputable section

/-- For any countable coefficient field, the relative phases of
rationally independent clocks are algebraically independent outside
countably many dates. Each nonzero polynomial has finitely many zero
dates in any compact interval. -/
theorem countable_dependent_dates (K : Type) [Field K] [Countable K] [Algebra K ℂ]
    {I : Type} [Fintype I] {w : I → ℝ} (hw : RationallyIndependentFrequency w) :
    {t : ℝ | ¬ AlgebraicIndependent K (fun i => energyPhase (w i) t)}.Countable := by
  classical
  let B := MvPolynomial I K
  letI : Countable B := AddMonoidAlgebra.coeff_injective.countable
  let Z (p : {p : B // p≠0}) (n : ℕ) := {t ∈ Icc (-(n:ℝ)) (n:ℝ) |
    aeval (fun i => energyPhase (w i) t) p.val=0}
  have hz (p : {p : B // p≠0}) (n : ℕ) : (Z p n).Finite := by
    let q := MvPolynomial.map (algebraMap K ℂ) p.val
    have hn : q ≠ 0 := fun h => p.property ((MvPolynomial.map_injective
      (algebraMap K ℂ) (algebraMap K ℂ).injective) (h.trans (map_zero _).symm))
    exact (finite_phase_zeros hw hn (-(n:ℝ)) (n:ℝ)).subset fun t ht =>
      ⟨ht.1,(MvPolynomial.aeval_map_algebraMap ℂ _ p.val).trans ht.2⟩
  apply (countable_iUnion fun p => countable_iUnion fun n => (hz p n).countable).mono
  intro t ht
  by_contra h
  apply ht
  apply algebraicIndependent_iff.mpr
  intro p hp
  by_contra hn
  obtain ⟨n,hnt⟩ := exists_nat_gt |t|
  exact h (mem_iUnion.mpr ⟨⟨p,hn⟩,mem_iUnion.mpr ⟨n,abs_le.mp hnt.le,hp⟩⟩)

#print axioms countable_dependent_dates
end
end GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
