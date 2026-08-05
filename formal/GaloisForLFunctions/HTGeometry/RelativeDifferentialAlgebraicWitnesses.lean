import GaloisForLFunctions.HTGeometry.GammaHypertranscendental
import GaloisForLFunctions.HTGeometry.RelativeDifferentialAlgebraicity

/-!
# Relative differential algebraicity is realized

Differential algebraicity over a base family is realized at order zero by the zero function: the
single coordinate variable is a nonzero relation vanishing on it.  So the relative notion is not
empty, and its negation — relative hypertranscendence — is the substantive side.
-/

namespace GaloisForLFunctions
namespace RelativeDifferentialAlgebraicity

variable {ι : Type*}

/-- **The zero function is differentially algebraic over every base, at order zero.** -/
theorem differentiallyAlgebraicOverOfOrder_zero (g : ι → ℂ → ℂ) :
    DifferentiallyAlgebraicOverOfOrder g (fun _ => 0) 0 := by
  refine ⟨MvPolynomial.X (Sum.inr 0), MvPolynomial.X_ne_zero _, fun z => ?_⟩
  simp

/-- Hence the zero function is differentially algebraic over every base. -/
theorem differentiallyAlgebraicOver_zero (g : ι → ℂ → ℂ) :
    DifferentiallyAlgebraicOver g (fun _ => 0) :=
  ⟨0, differentiallyAlgebraicOverOfOrder_zero g⟩

/-- The zero function is therefore not relatively hypertranscendental. -/
theorem not_hypertranscendentalOver_zero (g : ι → ℂ → ℂ) :
    ¬ HypertranscendentalOver g (fun _ => 0) := fun h => h (differentiallyAlgebraicOver_zero g)

/-- A relative differential equation over the empty base is an ordinary differential equation:
adjoin the unused point coordinate and shift every jet coordinate by one. -/
theorem differentiallyAlgebraic_of_differentiallyAlgebraicOver_empty
    {f : ℂ → ℂ} (h : DifferentiallyAlgebraicOver (fun i : Empty => Empty.elim i) f) :
    DifferentiallyAlgebraic f := by
  obtain ⟨n, P, hP, hzero⟩ := h
  let e : Empty ⊕ Fin (n + 1) → Fin (n + 2) :=
    Sum.elim Empty.elim Fin.succ
  have he : Function.Injective e := by
    intro a b hab
    cases a with
    | inl a => exact Empty.elim a
    | inr a =>
      cases b with
      | inl b => exact Empty.elim b
      | inr b =>
        exact congrArg (fun x : Fin (n + 1) => (Sum.inr x : Empty ⊕ Fin (n + 1)))
          (Fin.succ_injective _ hab)
  refine ⟨n, MvPolynomial.rename e P, ?_, ?_⟩
  · intro hrename
    apply hP
    apply MvPolynomial.rename_injective e he
    simpa using hrename
  · intro z
    rw [MvPolynomial.eval_rename]
    have hcomp :
        (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) ∘ e =
          Sum.elim (fun i : Empty => (Empty.elim i : ℂ → ℂ) z)
            (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) := by
      funext v
      cases v with
      | inl i => exact Empty.elim i
      | inr j => simp [e]
    rw [hcomp]
    exact hzero z

/-- Ordinary hypertranscendence implies relative hypertranscendence over the empty base. -/
theorem hypertranscendentalOver_empty_of_hypertranscendental
    {f : ℂ → ℂ} (hf : GaloisForLFunctions.Hypertranscendental f) :
    HypertranscendentalOver (fun i : Empty => Empty.elim i) f :=
  fun h => hf (differentiallyAlgebraic_of_differentiallyAlgebraicOver_empty h)

/-- The relative interface is inhabited: Gamma is hypertranscendental over the empty base. -/
theorem hypertranscendentalOver_empty_gamma :
    HypertranscendentalOver (fun i : Empty => Empty.elim i) Complex.Gamma :=
  hypertranscendentalOver_empty_of_hypertranscendental hypertranscendental_gamma

end RelativeDifferentialAlgebraicity
end GaloisForLFunctions
