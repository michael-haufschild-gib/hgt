import GaloisForLFunctions.RHTower.HedenmalmPrimeNormalSolderingCurvature
import GaloisForLFunctions.HTGeometry.EntireJetEvaluation

/-!
# Full covariant marked-prime jet tower
-/

open Complex

namespace RHTower

noncomputable section

/-- Scalar coefficient multiplied into both orientations of the marked prime character. -/
def hedenmalmMarkedPrimeSection (p : ℕ) (F : ℂ → ℂ) (z : ℂ) : ℂ × ℂ :=
  (F z * (hedenmalmMarkedPrimeHalfCharacter p z).1,
    F z * (hedenmalmMarkedPrimeHalfCharacter p z).2)

/-- Canonical covariant derivative of a marked section. -/
def hedenmalmMarkedPrimeCovariantDerivative (p : ℕ) (s : ℂ → ℂ × ℂ) (z : ℂ) : ℂ × ℂ :=
  hedenmalmMarkedPrimeConnection p
    (deriv (fun w => (s w).1) z, deriv (fun w => (s w).2) z) (s z)

/-- Iteration of the marked covariant derivative. -/
def hedenmalmMarkedPrimeCovariantIterate (p : ℕ) : ℕ → (ℂ → ℂ × ℂ) → (ℂ → ℂ × ℂ)
  | 0, s => s
  | n + 1, s => hedenmalmMarkedPrimeCovariantDerivative p
      (hedenmalmMarkedPrimeCovariantIterate p n s)

/-- **Covariant Leibniz cancellation.** The prime-log derivative of the moving character is
cancelled exactly, leaving only the derivative of the scalar coefficient. -/
theorem hedenmalmMarkedPrimeCovariantDerivative_section
    (p : ℕ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) (z : ℂ) :
    hedenmalmMarkedPrimeCovariantDerivative p (hedenmalmMarkedPrimeSection p F) z =
      hedenmalmMarkedPrimeSection p (deriv F) z := by
  have hFz : HasDerivAt F (deriv F z) z := (hF z).hasDerivAt
  have hfst := hFz.mul (hasDerivAt_hedenmalmMarkedPrimeHalfCharacter_fst p z)
  have hsnd := hFz.mul (hasDerivAt_hedenmalmMarkedPrimeHalfCharacter_snd p z)
  have hfstDeriv :
      deriv (fun w => F w * (hedenmalmMarkedPrimeHalfCharacter p w).1) z =
        deriv F z * (hedenmalmMarkedPrimeHalfCharacter p z).1 +
          F z * (hedenmalmMarkedPrimeGenerator p
            (hedenmalmMarkedPrimeHalfCharacter p z)).1 := by
    convert hfst.deriv using 1
    apply congrArg (fun g : ℂ → ℂ => deriv g z)
    funext w
    rfl
  have hsndDeriv :
      deriv (fun w => F w * (hedenmalmMarkedPrimeHalfCharacter p w).2) z =
        deriv F z * (hedenmalmMarkedPrimeHalfCharacter p z).2 +
          F z * (hedenmalmMarkedPrimeGenerator p
            (hedenmalmMarkedPrimeHalfCharacter p z)).2 := by
    convert hsnd.deriv using 1
    apply congrArg (fun g : ℂ → ℂ => deriv g z)
    funext w
    rfl
  rw [hedenmalmMarkedPrimeCovariantDerivative]
  change hedenmalmMarkedPrimeConnection p
      (deriv (fun w => F w * (hedenmalmMarkedPrimeHalfCharacter p w).1) z,
        deriv (fun w => F w * (hedenmalmMarkedPrimeHalfCharacter p w).2) z)
      (hedenmalmMarkedPrimeSection p F z) = _
  rw [hfstDeriv, hsndDeriv]
  simp only [hedenmalmMarkedPrimeSection, hedenmalmMarkedPrimeConnection,
    hedenmalmMarkedPrimeGenerator]
  ext <;> dsimp <;> ring

/-- **All-grade transport.** Every covariant marked grade is exactly the corresponding scalar jet;
no power of `log p` is introduced at any Jordan depth. -/
theorem hedenmalmMarkedPrimeCovariantIterate_section
    (p : ℕ) {F : ℂ → ℂ}
    (hF : ∀ n : ℕ, Differentiable ℂ (iteratedDeriv n F)) (n : ℕ) :
    hedenmalmMarkedPrimeCovariantIterate p n (hedenmalmMarkedPrimeSection p F) =
      hedenmalmMarkedPrimeSection p (iteratedDeriv n F) := by
  induction n with
  | zero =>
      simp [hedenmalmMarkedPrimeCovariantIterate, iteratedDeriv_zero]
  | succ n ih =>
      rw [hedenmalmMarkedPrimeCovariantIterate, ih]
      funext z
      rw [hedenmalmMarkedPrimeCovariantDerivative_section p (hF n) z]
      exact congrFun (congrArg (hedenmalmMarkedPrimeSection p) iteratedDeriv_succ.symm) z

/-- Unconditional specialization to the complete centered Xi divisor. -/
theorem hedenmalmMarkedPrimeCovariantIterate_XiC (p n : ℕ) :
    hedenmalmMarkedPrimeCovariantIterate p n (hedenmalmMarkedPrimeSection p XiC) =
      hedenmalmMarkedPrimeSection p (iteratedDeriv n XiC) := by
  apply hedenmalmMarkedPrimeCovariantIterate_section
  intro j
  exact GaloisForLFunctions.differentiable_iteratedDeriv_of_entire
    XiC_differentiable j

end

end RHTower

