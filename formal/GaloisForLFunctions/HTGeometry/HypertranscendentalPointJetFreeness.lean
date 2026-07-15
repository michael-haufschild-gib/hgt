import GaloisForLFunctions.HTGeometry.HypertranscendentalFunctionJetFreeness

/-!
# Hypertranscendence gives a free point-and-jet family

The definition of a hypertranscendental function excludes polynomial differential equations whose
first coordinate is the independent variable.  This file records the exact algebraic-independence
form of that statement: the point function together with every finite initial derivative jet is a
free family in the pointwise function ring.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The point coordinate followed by the initial derivative jet of `f`. -/
def pointJetFunctionTuple (f : ℂ → ℂ) (n : ℕ) : Fin (n + 2) → (ℂ → ℂ) :=
  Fin.cons id (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f)

/-- Hypertranscendence is precisely strong enough to make the point coordinate and every finite
initial derivative jet algebraically independent in the function ring. -/
theorem Hypertranscendental.algebraicIndependent_pointInitialJets
    {f : ℂ → ℂ} (hf : Hypertranscendental f) (n : ℕ) :
    AlgebraicIndependent ℂ (pointJetFunctionTuple f n) := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  apply hf
  refine ⟨n, P, hP0, ?_⟩
  intro z
  have hz : MvPolynomial.aeval
      (fun i : Fin (n + 2) => pointJetFunctionTuple f n i z) P = 0 := by
    calc
      _ = (Pi.evalAlgHom ℂ (fun _ : ℂ => ℂ) z)
          (MvPolynomial.aeval (pointJetFunctionTuple f n) P) := by
            rw [MvPolynomial.comp_aeval_apply]
            rfl
      _ = 0 := by rw [hP]; rfl
  have htuple :
      (fun i : Fin (n + 2) => pointJetFunctionTuple f n i z) =
        Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  rw [htuple] at hz
  simpa [MvPolynomial.aeval_eq_eval] using hz

end

end GaloisForLFunctions
