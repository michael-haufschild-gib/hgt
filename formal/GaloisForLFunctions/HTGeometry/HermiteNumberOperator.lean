import GaloisForLFunctions.HTGeometry.HermiteOrthogonality

/-!
# The number operator of the oscillator

Composing the creation operator after the annihilation operator gives the number operator
`N = A B`.  On the Hermite functions it acts by a scalar: the annihilation operator lowers the
index with factor `2n`, the creation operator raises it back with factor `2π`, so `N hₙ = 4πn hₙ`.

The number operator is symmetric for the bilinear pairing, because the creation and annihilation
operators are adjoint to each other for it.  Symmetry plus the eigenrelation moves every power of
`N` from one side of the pairing to the other, which turns the coefficient of a Schwartz function
against a Hermite function into a coefficient of `Nᵏ f` divided by `(4πn)ᵏ`.  That is the exact
mechanism behind the rapid decay of Hermite coefficients.

* `numberCLM` : the number operator `A B`.
* `numberCLM_hermiteSchwartz` : **the Hermite functions are its eigenfunctions**, eigenvalue `4πn`.
* `schwartzPair_numberCLM` : **the number operator is symmetric for the bilinear pairing.**
* `schwartzPair_hermiteSchwartz_numberCLM_iterate` : **the Hermite coefficient of `Nᵏ f` is
  `(4πn)ᵏ` times the Hermite coefficient of `f`.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- The **number operator** `N = A B` of the oscillator. -/
def numberCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := creationCLM.comp annihilationCLM

theorem numberCLM_apply (f : 𝓢(ℝ, ℂ)) : numberCLM f = creationCLM (annihilationCLM f) := rfl

/-- **The Hermite functions are the eigenfunctions of the number operator**, with eigenvalue
`4πn`: the annihilation operator lowers the index with factor `2n` and the creation operator
raises it back with factor `2π`. -/
theorem numberCLM_hermiteSchwartz (n : ℕ) :
    numberCLM (hermiteSchwartz n) = (4 * (π : ℂ) * n) • hermiteSchwartz n := by
  cases n with
  | zero =>
    rw [numberCLM_apply, annihilationCLM_hermiteSchwartz_zero, map_zero]
    simp
  | succ n =>
    rw [numberCLM_apply, annihilationCLM_hermiteSchwartz, map_smul, creationCLM_hermiteSchwartz,
      smul_smul]
    congr 1
    push_cast
    ring

/-- **The number operator is symmetric for the bilinear pairing**, since the creation and
annihilation operators are adjoint to each other. -/
theorem schwartzPair_numberCLM (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair (numberCLM f) g = schwartzPair f (numberCLM g) := by
  calc schwartzPair (numberCLM f) g
      = schwartzPair (annihilationCLM f) (annihilationCLM g) :=
        schwartzPair_creationCLM (annihilationCLM f) g
    _ = schwartzPair (annihilationCLM g) (annihilationCLM f) :=
        schwartzPair_comm _ _
    _ = schwartzPair (numberCLM g) f :=
        (schwartzPair_creationCLM (annihilationCLM g) f).symm
    _ = schwartzPair f (numberCLM g) := schwartzPair_comm _ _

/-- The iterated number operator scales a Hermite function by the power of its eigenvalue. -/
theorem numberCLM_iterate_hermiteSchwartz (k n : ℕ) :
    (numberCLM^[k]) (hermiteSchwartz n) = ((4 * (π : ℂ) * n) ^ k) • hermiteSchwartz n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, numberCLM_hermiteSchwartz, smul_smul,
      pow_succ]

/-- The iterated number operator is symmetric for the bilinear pairing. -/
theorem schwartzPair_numberCLM_iterate (k : ℕ) (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair ((numberCLM^[k]) f) g = schwartzPair f ((numberCLM^[k]) g) := by
  induction k generalizing f g with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', ih, schwartzPair_numberCLM]

/-- **The Hermite coefficient of `Nᵏ f` is `(4πn)ᵏ` times the Hermite coefficient of `f`.**  This
is the identity behind the rapid decay of the Hermite coefficients of a Schwartz function: the
coefficient of `f` at index `n` is the coefficient of `Nᵏ f` divided by `(4πn)ᵏ`. -/
theorem schwartzPair_hermiteSchwartz_numberCLM_iterate (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    schwartzPair ((numberCLM^[k]) f) (hermiteSchwartz n)
      = (4 * (π : ℂ) * n) ^ k * schwartzPair f (hermiteSchwartz n) := by
  rw [schwartzPair_numberCLM_iterate, numberCLM_iterate_hermiteSchwartz,
    schwartzPair_smul_right]

end GaloisForLFunctions

end
