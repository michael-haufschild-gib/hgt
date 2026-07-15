import GaloisForLFunctions.HTGeometry.AlgebraicallyIndependentCoefficientFormalGerm
import GaloisForLFunctions.HTGeometry.GammaBellSubstitution
import GaloisForLFunctions.HTGeometry.GammaFactorialHarmonicSequenceFreeness

/-!
# Algebraic independence of the complete regular Gamma pole-germ coefficients

`GammaFactorialHarmonicSequenceFreeness` proves algebraic independence of the exact
logarithmic coefficients of the factorially rescaled Gamma pole family.  This module crosses the
nonlinear exponential step.

The universal Bell map

`(lambda_0, ..., lambda_n) |-> (B_1(lambda), ..., B_{n+1}(lambda))`

is triangular.  The existing theorem `exists_bellAt_solution` gives a stronger finite statement:
the value map is surjective over `ℂ`.  Hence substitution by the Bell coordinates is injective on
the polynomial algebra.  Algebraic independence therefore survives the Bell transform and every
nonzero coordinate scaling.

For the scaled Gamma pole unit `U = exp L`, its positive coefficients are

`[X^k] U = B_k(L'(0), ..., L^(k)(0)) / k!`.

The regular part of `-U/X` has coefficients `-[X^(j+1)] U`.  These coefficients form a countably
algebraically independent family.  Consequently their formal power series satisfies no nonzero
finite-order algebraic differential equation.
-/

open MvPolynomial PowerSeries

namespace GaloisForLFunctions

noncomputable section

/-- The Bell-coordinate substitution in the common frame `Fin (n+1)`. -/
def bellCoefficientMap (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin (n + 1)) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j =>
    bellAt n ((j : ℕ) + 1) j.isLt

theorem eval_bellCoefficientMap (n : ℕ) (w : Fin (n + 1) → ℂ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval w (bellCoefficientMap n P) =
      MvPolynomial.eval
        (fun j : Fin (n + 1) =>
          MvPolynomial.eval w (bellAt n ((j : ℕ) + 1) j.isLt)) P := by
  have hhom : (MvPolynomial.eval w).comp (bellCoefficientMap n) =
      MvPolynomial.eval
        (fun j : Fin (n + 1) =>
          MvPolynomial.eval w (bellAt n ((j : ℕ) + 1) j.isLt)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [bellCoefficientMap]
    · intro j
      simp [bellCoefficientMap]
  exact RingHom.congr_fun hhom P

/-- Surjectivity of the finite Bell value map forces the Bell polynomial substitution to be
injective. -/
theorem bellCoefficientMap_injective (n : ℕ) :
    Function.Injective (bellCoefficientMap n) := by
  intro P Q hPQ
  apply MvPolynomial.funext
  intro t
  obtain ⟨w, hw⟩ := exists_bellAt_solution n t
  have h := congrArg (MvPolynomial.eval w) hPQ
  rw [eval_bellCoefficientMap, eval_bellCoefficientMap] at h
  have hvalues :
      (fun j : Fin (n + 1) =>
        MvPolynomial.eval w (bellAt n ((j : ℕ) + 1) j.isLt)) = t := by
    funext j
    exact hw j
  rw [hvalues] at h
  exact h

/-- Bell substitution after a coordinatewise scalar multiplication. -/
def scaledBellCoefficientMap (n : ℕ) (c : Fin (n + 1) → ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin (n + 1)) ℂ :=
  (bellCoefficientMap n).comp (affineCoordinateMap (n + 1) c 0)

theorem scaledBellCoefficientMap_injective (n : ℕ) {c : Fin (n + 1) → ℂ}
    (hc : ∀ j, c j ≠ 0) : Function.Injective (scaledBellCoefficientMap n c) := by
  exact (bellCoefficientMap_injective n).comp
    (affineCoordinateMap_injective (n + 1) hc)

theorem scaledBellCoefficientMap_eq_aeval (n : ℕ) (c : Fin (n + 1) → ℂ) :
    scaledBellCoefficientMap n c =
      (MvPolynomial.aeval fun j =>
        MvPolynomial.C (c j) * bellAt n ((j : ℕ) + 1) j.isLt).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [scaledBellCoefficientMap, bellCoefficientMap, affineCoordinateMap]
  · intro j
    simp [scaledBellCoefficientMap, bellCoefficientMap, affineCoordinateMap]

theorem algebraicIndependent_scaledBellPolynomials (n : ℕ)
    {c : Fin (n + 1) → ℂ} (hc : ∀ j, c j ≠ 0) :
    AlgebraicIndependent ℂ
      (fun j => MvPolynomial.C (c j) * bellAt n ((j : ℕ) + 1) j.isLt) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h := scaledBellCoefficientMap_injective n hc
  rw [scaledBellCoefficientMap_eq_aeval] at h
  exact h

/-- Algebraic independence survives every nonzero scaled Bell transform. -/
theorem AlgebraicIndependent.scaledBellValues
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (n : ℕ) {x : Fin (n + 1) → A} (hx : AlgebraicIndependent ℂ x)
    {c : Fin (n + 1) → ℂ} (hc : ∀ j, c j ≠ 0) :
    AlgebraicIndependent ℂ (fun j =>
      algebraMap ℂ A (c j) *
        MvPolynomial.aeval x (bellAt n ((j : ℕ) + 1) j.isLt)) := by
  have hpoly := algebraicIndependent_scaledBellPolynomials n hc
  have h := hx.aeval_of_algebraicIndependent hpoly
  simpa using h

local instance gammaPoleNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- The exact derivative-normalized logarithmic coordinates of the scaled Gamma pole family:
`L^((j+1))(0)`. -/
def gammaPoleLogDerivativeGerm (j : ℕ) : NatGerm :=
  reciprocalSignedFactorialGerm ^ (j + 1) *
    (algebraMap ℂ NatGerm (-1) * harmonicJetGerm j +
      algebraMap ℂ NatGerm
        ((j + 1).factorial * gammaPoleLogConstant j))

theorem gammaPoleLogDerivativeGerm_eq_factorial_mul (j : ℕ) :
    gammaPoleLogDerivativeGerm j =
      algebraMap ℂ NatGerm ((j + 1).factorial : ℂ) *
        gammaPoleLogCoefficientGerm j := by
  have hfac : ((j + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j + 1))
  have hcancel :
      algebraMap ℂ NatGerm ((j + 1).factorial : ℂ) *
          algebraMap ℂ NatGerm (gammaPoleLogSlope j) =
        algebraMap ℂ NatGerm (-1) := by
    rw [← map_mul]
    congr 1
    simp [gammaPoleLogSlope, hfac]
  rw [gammaPoleLogDerivativeGerm, gammaPoleLogCoefficientGerm]
  rw [show algebraMap ℂ NatGerm
      (((j + 1).factorial : ℂ) * gammaPoleLogConstant j) =
        algebraMap ℂ NatGerm ((j + 1).factorial : ℂ) *
          algebraMap ℂ NatGerm (gammaPoleLogConstant j) by rw [map_mul]]
  rw [← hcancel]
  ring

theorem algebraicIndependent_gammaPoleLogDerivativeGerm_fin (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin m => gammaPoleLogDerivativeGerm (j : ℕ)) := by
  let β : Fin m → ℂ := fun j => ((j : ℕ) + 1).factorial *
    gammaPoleLogConstant (j : ℕ)
  have h := algebraicIndependent_weightedAffineGerm m
    (hα := fun _j => neg_ne_zero.mpr one_ne_zero) (β := β)
  have hfamily :
      (fun j : Fin m => gammaPoleLogDerivativeGerm (j : ℕ)) =
        weightedAffineGerm m (fun _j => -1) β := by
    funext j
    simp [gammaPoleLogDerivativeGerm, weightedAffineGerm, β, map_mul]
  rw [hfamily]
  exact h

theorem algebraicIndependent_gammaPoleLogDerivativeGerm :
    AlgebraicIndependent ℂ gammaPoleLogDerivativeGerm := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  rcases ht.bddAbove with ⟨k, hk⟩
  let f : t → Fin (k + 1) := fun i => ⟨i, Nat.lt_succ_of_le (hk i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have hprefix := algebraicIndependent_gammaPoleLogDerivativeGerm_fin (k + 1)
  have hsub := hprefix.comp f hf
  simpa [f, Function.comp_def] using hsub

/-- Coefficient `j` of the regular power-series part of the scaled Gamma pole germ
`-exp(L(X))/X`: it is `-B_(j+1)(L'(0),...,L^((j+1))(0))/(j+1)!`. -/
def gammaPoleRegularCoefficientGerm (j : ℕ) : NatGerm :=
  algebraMap ℂ NatGerm (-(((j + 1).factorial : ℂ)⁻¹)) *
    MvPolynomial.aeval
      (fun i : Fin (j + 1) => gammaPoleLogDerivativeGerm (i : ℕ))
      (bellCore (j + 1))

theorem algebraicIndependent_gammaPoleRegularCoefficientGerm_fin (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => gammaPoleRegularCoefficientGerm (j : ℕ)) := by
  have hx := algebraicIndependent_gammaPoleLogDerivativeGerm_fin (n + 1)
  have hc (j : Fin (n + 1)) :
      -((((j : ℕ) + 1).factorial : ℂ)⁻¹) ≠ 0 := by
    exact neg_ne_zero.mpr (inv_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ((j : ℕ) + 1))))
  have h := AlgebraicIndependent.scaledBellValues n hx hc
  simpa [gammaPoleRegularCoefficientGerm, bellAt,
    MvPolynomial.aeval_rename, Function.comp_def] using h

/-- The complete countable regular coefficient family of the factorially rescaled Gamma pole
germs is algebraically independent over `ℂ`. -/
theorem algebraicIndependent_gammaPoleRegularCoefficientGerm :
    AlgebraicIndependent ℂ gammaPoleRegularCoefficientGerm := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  rcases ht.bddAbove with ⟨k, hk⟩
  let f : t → Fin (k + 1) := fun i => ⟨i, Nat.lt_succ_of_le (hk i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have hprefix := algebraicIndependent_gammaPoleRegularCoefficientGerm_fin k
  have hsub := hprefix.comp f hf
  simpa [f, Function.comp_def] using hsub

/-- The regular formal power series carried by the full scaled Gamma pole family. -/
def gammaPoleRegularFormalGerm : NatGerm⟦X⟧ :=
  PowerSeries.mk gammaPoleRegularCoefficientGerm

/-- **All-order formal hypertranscendence of the regular Gamma pole deformation.**  No nonzero
finite-order algebraic differential polynomial over `ℂ[X]` vanishes on the regular pole-germ
coefficient family. -/
theorem gammaPoleRegularFormalGerm_formallyHypertranscendental
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    MvPolynomial.aeval (formalJetsOver n gammaPoleRegularFormalGerm) P ≠ 0 := by
  exact aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent
    gammaPoleRegularCoefficientGerm
    algebraicIndependent_gammaPoleRegularCoefficientGerm hP

end

end GaloisForLFunctions
