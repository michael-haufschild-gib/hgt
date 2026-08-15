import GaloisForLFunctions.RHTower.BakerGeneralProof.AlgebraicFamilyField

/-!
# Full qualitative Baker theorem: public statement

The indexed family adjoins `1` to arbitrary chosen complex logarithms of algebraic numbers. No
principal-logarithm or multiplicative-independence surrogate appears in the interface: additive
`ℚ`-linear independence of the chosen branches is exactly the standard hypothesis.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower

/-- A chosen complex logarithm of an algebraic number. No principal-branch restriction is imposed. -/
def IsLogarithmOfAlgebraic (lambda : ℂ) : Prop :=
  IsAlgebraic ℚ (Complex.exp lambda)

/-- Baker's full qualitative theorem, including the inhomogeneous extension by `1`. -/
def BakerTheorem : Prop :=
  ∀ (n : ℕ) (lambda : Fin n → ℂ),
    (∀ i, IsLogarithmOfAlgebraic (lambda i)) →
    LinearIndependent ℚ lambda →
    LinearIndependent (algebraicClosure ℚ ℂ)
      (fun j : Option (Fin n) => match j with
        | none => (1 : ℂ)
        | some i => lambda i)

/-- The inhomogeneous theorem immediately contains homogeneous Baker independence. -/
theorem BakerTheorem.homogeneous (hB : BakerTheorem)
    (n : ℕ) (lambda : Fin n → ℂ)
    (halg : ∀ i, IsLogarithmOfAlgebraic (lambda i))
    (hind : LinearIndependent ℚ lambda) :
    LinearIndependent (algebraicClosure ℚ ℂ) lambda := by
  unfold BakerTheorem at hB
  have hfull := hB n lambda halg hind
  simpa [Function.comp_def] using
    hfull.comp (fun i => some i) (Option.some_injective (Fin n))

end GaloisForLFunctions.RHTower
