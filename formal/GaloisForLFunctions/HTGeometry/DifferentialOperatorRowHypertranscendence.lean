import GaloisForLFunctions.HTGeometry.DifferentialOperatorToeplitzRank

/-!
# Nonzero operator rows on an independent family are hypertranscendental

A single row of a constant-coefficient differential-operator matrix applied to a differentially
independent family produces a hypertranscendental element exactly when the row is nonzero.  This is
the one-output case of the operator-row independence criterion: a one-element family of rows is
linearly independent over `C[∂]` precisely when the row does not vanish.

Specializing to degree-zero rows gives the constant-coefficient statement: a nonzero linear
combination of a differentially independent family is hypertranscendental.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **A nonzero operator row on an independent family is hypertranscendental.** -/
theorem hypertranscendentalOver_differentialOperatorRow_of_ne_zero
    {C K κ : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype κ] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (v : κ → Polynomial C) (hv : v ≠ 0)
    (x : κ → K) (hx : DifferentialIndependent C x) :
    HypertranscendentalOver C (∑ j, differentialOperatorApply (v j) (x j)) := by
  have hrowIndep : LinearIndependent (Polynomial C) (fun _ : Unit => v) :=
    linearIndependent_unique_iff.mpr hv
  have hout : DifferentialIndependent C
      (differentialOperatorRowApply (fun _ : Unit => v) x) :=
    (differentialIndependent_differentialOperatorRows_iff hconst (fun _ : Unit => v) x hx).mpr
      hrowIndep
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact hout

/-- **A nonzero constant-coefficient linear combination of a differentially independent family is
hypertranscendental.** -/
theorem hypertranscendentalOver_linearCombination_of_ne_zero
    {C K κ : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype κ] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (c : κ → C) (hc : c ≠ 0)
    (x : κ → K) (hx : DifferentialIndependent C x) :
    HypertranscendentalOver C (∑ j, algebraMap C K (c j) * x j) := by
  have hv : (fun j => Polynomial.C (c j)) ≠ (0 : κ → Polynomial C) := by
    intro h
    apply hc
    funext j
    have := congrFun h j
    simpa using this
  have h := hypertranscendentalOver_differentialOperatorRow_of_ne_zero hconst _ hv x hx
  have hterm : ∀ j, differentialOperatorApply (Polynomial.C (c j)) (x j) =
      algebraMap C K (c j) * x j := by
    intro j
    simp [differentialOperatorApply, Polynomial.sum_C_index, differentialJet]
  simpa only [hterm] using h

end

end GaloisForLFunctions.HTGeometry
