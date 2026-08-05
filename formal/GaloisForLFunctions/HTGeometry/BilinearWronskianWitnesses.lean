import GaloisForLFunctions.HTGeometry.NonlinearConstraintHorizon
import GaloisForLFunctions.HTGeometry.DifferentialPolynomial

/-!
# A nonvanishing bilinear horizon Wronskian

The nonlinear constraint laws are conditioned on the bilinear Wronskian `x′y″ − x″y′` of two
elements not vanishing, and nothing exhibited such a pair.  The free differential polynomial ring on
two generators supplies one: there the four jets involved are four distinct coordinates, so the two
products are distinct monomials and their difference is not zero.

The proof is one evaluation: send the two coordinates of the first product to one and the two of the
second to zero.  The Wronskian then evaluates to one.
-/

open scoped Differential

namespace GaloisForLFunctions

open MvPolynomial

variable {C : Type*} [CommRing C] [Nontrivial C]

/-- The separating evaluation: it sees the first product and kills the second. -/
noncomputable def wronskianSeparator (C : Type*) [CommRing C] : Fin 2 × ℕ → C :=
  fun c => if c = ((0 : Fin 2), 1) ∨ c = ((1 : Fin 2), 2) then 1 else 0

omit [Nontrivial C] in
@[simp] theorem wronskianSeparator_fst : wronskianSeparator C ((0 : Fin 2), 1) = 1 := by
  rw [wronskianSeparator]
  simp

omit [Nontrivial C] in
@[simp] theorem wronskianSeparator_snd : wronskianSeparator C ((1 : Fin 2), 2) = 1 := by
  rw [wronskianSeparator]
  simp

omit [Nontrivial C] in
@[simp] theorem wronskianSeparator_off_fst : wronskianSeparator C ((0 : Fin 2), 2) = 0 := by
  rw [wronskianSeparator]
  simp [Prod.ext_iff]

omit [Nontrivial C] in
@[simp] theorem wronskianSeparator_off_snd : wronskianSeparator C ((1 : Fin 2), 1) = 0 := by
  rw [wronskianSeparator]
  simp [Prod.ext_iff]

/-- **The bilinear Wronskian of two free generators does not vanish.** -/
theorem bilinearHorizonWronskian_X_ne_zero :
    bilinearHorizonWronskian
        (MvPolynomial.X ((0 : Fin 2), 0) : DifferentialPolynomial (Fin 2) C)
        (MvPolynomial.X ((1 : Fin 2), 0)) ≠ 0 := by
  classical
  intro h
  have heval := congrArg (MvPolynomial.eval (wronskianSeparator C)) h
  rw [bilinearHorizonWronskian] at heval
  simp only [differentialPolynomial_deriv_X, map_sub, map_mul, MvPolynomial.eval_X,
    map_zero] at heval
  rw [wronskianSeparator_fst, wronskianSeparator_snd, wronskianSeparator_off_fst,
    wronskianSeparator_off_snd] at heval
  norm_num at heval

/-- Hence a pair with nonvanishing bilinear Wronskian exists. -/
theorem exists_bilinearHorizonWronskian_ne_zero :
    ∃ x y : DifferentialPolynomial (Fin 2) C, bilinearHorizonWronskian x y ≠ 0 :=
  ⟨_, _, bilinearHorizonWronskian_X_ne_zero⟩

end GaloisForLFunctions
