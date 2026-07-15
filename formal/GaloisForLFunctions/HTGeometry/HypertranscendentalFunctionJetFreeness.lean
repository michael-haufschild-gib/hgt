import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Function hypertranscendence gives free derivative jets

The analytic-function predicate `Hypertranscendental` excludes differential equations with a
point variable and polynomial coefficients. In particular it excludes every autonomous
polynomial relation among the derivative functions themselves. This file packages that bridge as
algebraic independence of the complete derivative family in the pointwise function ring.
-/

open MvPolynomial

namespace GaloisForLFunctions

/-- Every finite initial derivative family of a hypertranscendental complex function is
algebraically independent over `ℂ` in the pointwise function ring. -/
theorem Hypertranscendental.algebraicIndependent_initialJets
    {f : ℂ → ℂ} (hf : Hypertranscendental f) (n : ℕ) :
    AlgebraicIndependent ℂ (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f) := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  apply hf
  refine ⟨n, rename Fin.succ P, ?_, ?_⟩
  · exact fun h => hP0 (rename_injective Fin.succ (Fin.succ_injective _) h)
  · intro z
    have hz : MvPolynomial.aeval
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0 := by
      calc
        _ = (Pi.evalAlgHom ℂ (fun _ : ℂ => ℂ) z)
            (MvPolynomial.aeval
              (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f) P) := by
              rw [MvPolynomial.comp_aeval_apply]
              rfl
        _ = 0 := by rw [hP]; rfl
    rw [eval_rename]
    simpa using hz

/-- **Free-jet consequence of hypertranscendence.** The complete family of derivative functions
of a hypertranscendental function is algebraically independent over `ℂ`. -/
theorem Hypertranscendental.algebraicIndependent_iteratedDeriv
    {f : ℂ → ℂ} (hf : Hypertranscendental f) :
    AlgebraicIndependent ℂ (fun j : ℕ => iteratedDeriv j f) := by
  rw [algebraicIndependent_iff]
  intro P hP
  obtain ⟨m, a, ha, Q, rfl⟩ := MvPolynomial.exists_fin_rename P
  let N : ℕ := Finset.univ.sup a
  have haN (i : Fin m) : a i ≤ N :=
    Finset.le_sup (f := a) (Finset.mem_univ i)
  let e : Fin m → Fin (N + 1) := fun i => ⟨a i, Nat.lt_succ_of_le (haN i)⟩
  have he : Function.Injective e := by
    intro i j hij
    apply ha
    exact congrArg Fin.val hij
  have hAI : AlgebraicIndependent ℂ
      ((fun j : Fin (N + 1) => iteratedDeriv (j : ℕ) f) ∘ e) :=
    (hf.algebraicIndependent_initialJets N).comp e he
  have hQ : Q = 0 := by
    apply hAI.eq_zero_of_aeval_eq_zero Q
    rw [MvPolynomial.aeval_rename] at hP
    simpa [e, Function.comp_def] using hP
  simp [hQ]

end GaloisForLFunctions
