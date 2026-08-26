import GaloisForLFunctions.HTGeometry.LinearSpanBaseChange
import GaloisForLFunctions.HTGeometry.LatticeSpanFinite
import GaloisForLFunctions.RHTower.BakerGeneralConsequences

/-!
# Baker assembly for algebraic Schanuel-defect coefficients

This file isolates the arithmetic endgame of the algebraic-coefficient defect theorem.  If an
algebraic coefficient vector lies in the complex span of an integral character-relation lattice,
all corresponding exponential characters are algebraic, and the matching additive linear form is
algebraic, Baker's theorem forces the coefficient vector to vanish.

The proof descends span membership from `ℂ` to the algebraic numbers, extracts a rationally
independent basis consisting of actual integral characters, and applies the project's
unconditional Baker theorem to their logarithms.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open TorusCharacterCoLie LinearSpanBaseChange LatticeSpanFinite

noncomputable section

/-- Algebraic coefficients supported by an integral character lattice vanish once both the
character values and the corresponding additive form are algebraic. -/
theorem algebraic_coefficients_eq_zero_of_latticeSpan
    {n : ℕ} (x : Fin n → ℂ) (hx : LinearIndependent ℚ x)
    (L : AddSubgroup (Fin n →₀ ℤ))
    (c : Fin n → algebraicClosure ℚ ℂ)
    (hcSpan : (fun i => (c i : ℂ)) ∈ latticeSpan ℂ L)
    (hcharacters : ∀ m ∈ L,
      IsAlgebraic ℚ (∏ i, Complex.exp (x i) ^ (m i)))
    (hadditive : IsAlgebraic ℚ (∑ i, (c i : ℂ) * x i)) :
    c = 0 := by
  classical
  by_contra hc
  obtain ⟨r, m, gamma, hmQ, hmL, hrepresentation⟩ :=
    exists_independent_latticeSpan_representation ℂ L (fun i => (c i : ℂ)) hcSpan
  let A := algebraicClosure ℚ ℂ
  let vA : Fin r → (Fin n → A) := fun j => integralCast A (m j)
  have hvA : LinearIndependent A vA := by
    have h := linearIndependent_coordinate_algebraMap
      (L := A) (fun j => integralCast ℚ (m j)) hmQ
    simpa [vA, integralCast] using h
  have hcSpanBasis : (fun i => (c i : ℂ)) ∈
      Submodule.span ℂ
        (Set.range fun j => fun i => algebraMap A ℂ (vA j i)) := by
    rw [hrepresentation]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, by funext i; simp [vA, integralCast, A]⟩)
  have hcSpanA : c ∈ Submodule.span A (Set.range vA) :=
    (mem_span_coordinate_algebraMap_iff (L := ℂ) vA hvA c).mp hcSpanBasis
  obtain ⟨beta, hbeta⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hcSpanA
  have hbetaNonzero : ∃ j, beta j ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hb0 : beta = 0 := funext fun j => hzero j
    rw [hb0] at hbeta
    simp at hbeta
    exact hc hbeta.symm
  let lambda : Fin r → ℂ := fun j =>
    (Fintype.linearCombination ℂ x) (integralCast ℂ (m j))
  have hlambdaIndependent : LinearIndependent ℚ lambda := by
    have hmapped := hmQ.map' (Fintype.linearCombination ℚ x)
      (LinearMap.ker_eq_bot.mpr hx.fintypeLinearCombination_injective)
    simpa [lambda, Fintype.linearCombination_apply, integralCast,
      Function.comp_def, Algebra.smul_def] using hmapped
  have hlambdaAlgebraic (j : Fin r) : IsLogarithmOfAlgebraic (lambda j) := by
    change IsAlgebraic ℚ (Complex.exp (lambda j))
    rw [show Complex.exp (lambda j) = ∏ i, Complex.exp (x i) ^ (m j i) by
      simp only [lambda, Fintype.linearCombination_apply, integralCast_apply,
        smul_eq_mul, Complex.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [Complex.exp_int_mul]]
    exact hcharacters (m j) (hmL j)
  have hbetaAlgebraic (j : Fin r) : IsAlgebraic ℚ ((beta j : A) : ℂ) :=
    mem_algebraicClosure_iff.mp (beta j).2
  have hbetaC :
      (∑ j, ((beta j : A) : ℂ) • integralCast ℂ (m j)) =
        fun i => (c i : ℂ) := by
    funext i
    have hi := congrFun hbeta i
    simpa [vA, integralCast, A, Pi.smul_apply, Algebra.smul_def] using
      congrArg (fun z : A => (z : ℂ)) hi
  have hform :
      (∑ j, ((beta j : A) : ℂ) * lambda j) = ∑ i, (c i : ℂ) * x i := by
    have hmap := congrArg (Fintype.linearCombination ℂ x) hbetaC
    simpa [lambda, Fintype.linearCombination_apply, smul_eq_mul] using hmap
  have htrans := baker_linearForm_transcendental lambda
    (fun j => ((beta j : A) : ℂ)) hlambdaAlgebraic hlambdaIndependent
    hbetaAlgebraic (by
      obtain ⟨j, hj⟩ := hbetaNonzero
      exact ⟨j, fun h => hj (Subtype.ext h)⟩)
  exact htrans (hform.symm ▸ hadditive)

end
end GaloisForLFunctions.RHTower
