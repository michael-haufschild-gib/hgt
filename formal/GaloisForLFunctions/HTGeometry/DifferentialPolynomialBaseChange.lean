import GaloisForLFunctions.HTGeometry.DifferentialPolynomialRename
import GaloisForLFunctions.HTGeometry.MvPolynomialBaseChangeProper

/-!
# Base change and transport of differential polynomial evaluation

Extending the coefficients of a differential polynomial along a differential map of the base
commutes with the total derivation, so a system over a differential field becomes a system over any
differential extension without changing its meaning.

The three evaluation identities recorded here are what a system needs in order to travel: a renamed
system is evaluated at the composed point, a coefficient-extended system is evaluated exactly as the
original one, and a differential map of the target carries a solution to a solution.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {ι F L : Type*} [CommRing F] [Differential F] [CommRing L] [Differential L]
  [Algebra F L]

/-- Extending the coefficients of a differential polynomial. -/
def differentialCoeffExtend :
    DifferentialPolynomial ι F →+* DifferentialPolynomial ι L :=
  MvPolynomial.map (algebraMap F L)

omit [Differential F] [Differential L] in
@[simp] theorem differentialCoeffExtend_X (i : ι) (n : ℕ) :
    differentialCoeffExtend (ι := ι) (F := F) (L := L) (MvPolynomial.X (i, n))
      = MvPolynomial.X (i, n) := by
  simp [differentialCoeffExtend]

omit [Differential F] [Differential L] in
@[simp] theorem differentialCoeffExtend_C (a : F) :
    differentialCoeffExtend (ι := ι) (F := F) (L := L) (MvPolynomial.C a)
      = MvPolynomial.C (algebraMap F L a) := by
  simp [differentialCoeffExtend]

/-- **Extending the coefficients commutes with the total derivation** when the coefficient map is
differential. -/
theorem differentialCoeffExtend_deriv
    (hcompat : ∀ a : F, Differential.deriv (algebraMap F L a)
      = algebraMap F L (Differential.deriv a))
    (p : DifferentialPolynomial ι F) :
    differentialCoeffExtend (ι := ι) (F := F) (L := L)
        (differentialPolynomialOverDerivation ι F p)
      = differentialPolynomialOverDerivation ι L (differentialCoeffExtend p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [differentialPolynomialOverDerivation_C, differentialCoeffExtend_C,
        differentialCoeffExtend_C, differentialPolynomialOverDerivation_C, hcompat]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p s hp =>
      obtain ⟨i, n⟩ := s
      have hLp : differentialPolynomialOverDerivation ι F (p * MvPolynomial.X (i, n))
          = p * MvPolynomial.X (i, n + 1)
            + MvPolynomial.X (i, n) * differentialPolynomialOverDerivation ι F p := by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, differentialPolynomialOverDerivation_X]
      have hRp : differentialPolynomialOverDerivation ι L
            (differentialCoeffExtend (ι := ι) (F := F) (L := L) p * MvPolynomial.X (i, n))
          = differentialCoeffExtend (ι := ι) (F := F) (L := L) p * MvPolynomial.X (i, n + 1)
            + MvPolynomial.X (i, n) * differentialPolynomialOverDerivation ι L
              (differentialCoeffExtend (ι := ι) (F := F) (L := L) p) := by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, differentialPolynomialOverDerivation_X]
      rw [hLp, map_add, map_mul, map_mul, differentialCoeffExtend_X,
        differentialCoeffExtend_X, hp, map_mul, differentialCoeffExtend_X, hRp]

section Evaluation

variable {ι κ F L M : Type*} [CommRing F] [CommRing L] [CommRing M]

/-- A ring map commuting with the derivations commutes with the jets. -/
theorem map_differentialJet [Differential L] [Differential M] (φ : L →+* M)
    (hφ : ∀ x : L, φ (Differential.deriv x) = Differential.deriv (φ x)) (n : ℕ) (x : L) :
    φ (differentialJet n x) = differentialJet n (φ x) := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, hφ, ih, differentialJet_succ]

/-- Evaluating a renamed differential polynomial evaluates the original at the composed point. -/
theorem differentialPolynomialEvalOver_differentialRename [Differential F] [Algebra F L]
    [Differential L] (f : ι → κ) (y : κ → L) (p : DifferentialPolynomial ι F) :
    differentialPolynomialEvalOver (K := F) y (differentialRename f p)
      = differentialPolynomialEvalOver (K := F) (fun i => y (f i)) p := by
  rw [differentialRename, differentialPolynomialEvalOver, differentialPolynomialEvalOver]
  show MvPolynomial.aeval _ ((MvPolynomial.rename _) p) = _
  rw [MvPolynomial.aeval_rename]
  rfl

/-- Evaluating after extending the coefficients is evaluating over the smaller field. -/
theorem differentialPolynomialEvalOver_differentialCoeffExtend [Differential F] [Differential L]
    [Differential M] [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]
    (y : ι → M) (p : DifferentialPolynomial ι F) :
    differentialPolynomialEvalOver (K := L) y
        (differentialCoeffExtend (ι := ι) (F := F) (L := L) p)
      = differentialPolynomialEvalOver (K := F) y p := by
  rw [differentialCoeffExtend, differentialPolynomialEvalOver, differentialPolynomialEvalOver]
  exact MvPolynomial.aeval_map_algebraMap L _ p

/-- A differential map of the target transports an evaluation to the evaluation at the image
point. -/
theorem map_differentialPolynomialEvalOver [Differential F] [Differential L] [Differential M]
    [Algebra F L] [Algebra F M] (φ : L →+* M)
    (hφδ : ∀ x : L, φ (Differential.deriv x) = Differential.deriv (φ x))
    (hφF : ∀ a : F, φ (algebraMap F L a) = algebraMap F M a)
    (y : ι → L) (p : DifferentialPolynomial ι F) :
    φ (differentialPolynomialEvalOver (K := F) y p)
      = differentialPolynomialEvalOver (K := F) (fun i => φ (y i)) p := by
  letI ψ : L →ₐ[F] M := { φ with commutes' := hφF }
  have hcomp := MvPolynomial.comp_aeval (R := F) (σ := ι × ℕ)
    (fun q : ι × ℕ => differentialJet q.2 (y q.1)) ψ
  have := congrArg (fun g : DifferentialPolynomial ι F →ₐ[F] M => g p) hcomp
  simp only [AlgHom.coe_comp, Function.comp_apply] at this
  have hfun : (fun q : ι × ℕ => ψ (differentialJet q.2 (y q.1)))
      = fun q : ι × ℕ => differentialJet q.2 (φ (y q.1)) := by
    funext q
    exact map_differentialJet φ hφδ q.2 (y q.1)
  rw [differentialPolynomialEvalOver, differentialPolynomialEvalOver, ← hfun]
  exact this

end Evaluation

end

end GaloisForLFunctions.HTGeometry
