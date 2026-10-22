import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSourcePositiveD1ScalarContravariantNoGo

/-!
# No finite matrix contravariant D1 carrier for the source-positive theta sl₂ action

The scalar contravariant obstruction does not disappear after adding finitely many positive
channels or replacing the scalar adjoint coefficient by a matrix. The D1-generated affine-vacuum
string already proved in the scalar analysis gives vectors `u,v` with

* `E u = 0` and `F v = u`, where `u` is nonzero;
* `E v` is nonzero.

For a positive matrix-valued form, contravariance on `(u,v)` says that the positive-definite
matrix `⟨u,u⟩` annihilates the channel coefficient. Its invertibility forces that coefficient to
vanish. Contravariance on `(v,E v)` then makes the positive-definite matrix `⟨E v,E v⟩` vanish, a
contradiction. The proof handles both canonical left and right channel actions, every nonempty
finite channel dimension, arbitrary source-`sl₂`-stable polynomial carriers, and actual D1.

This kills the finite positive matrix-channel escape from the source-`sl₂` route. A survivor must
be genuinely infinite-channel, localized/singular, indefinite, or use direct cross-scale Hankel
geometry rather than a positive finite-matrix contravariant form.
-/

open Complex Real Matrix
open scoped ComplexOrder

namespace HTGeometry

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Finite-channel positive matrix-valued contravariant data on an arbitrary source-`sl₂`-stable
polynomial carrier containing D1. The adjoint coefficient acts on the right channel. -/
structure ModularThetaSourcePositiveD1RightMatrixContravariantCarrier where
  carrier : Submodule ℂ ModularThetaSourcePositivePolynomial
  d1_mem : modularThetaSourcePositiveReflectedEighthPolynomial ∈ carrier
  sl2E_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ carrier
  sl2F_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ carrier
  coefficient : Matrix I I ℂ
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → Matrix I I ℂ
  smul_left : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair (a • p) q = star a • pair p q
  smul_right : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair p (a • q) = a • pair p q
  positive : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → (pair p p).PosDef
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → q ∈ carrier →
      pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
        pair p (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q) *
          coefficient

omit [DecidableEq I] [Nonempty I] in
theorem ModularThetaSourcePositiveD1RightMatrixContravariantCarrier.sl2FIterate_mem
    (B : ModularThetaSourcePositiveD1RightMatrixContravariantCarrier (I := I))
    (n : ℕ) {P : ModularThetaSourcePositivePolynomial} (hP : P ∈ B.carrier) :
    modularThetaSourcePositiveSl2FIterate n P ∈ B.carrier := by
  induction n with
  | zero => exact hP
  | succ n ih => exact B.sl2F_mem _ ih

/-- No finite positive matrix-channel right contravariant lift contains actual D1. -/
theorem modularThetaSourcePositive_no_D1_rightMatrixContravariantCarrier :
    ¬ Nonempty (ModularThetaSourcePositiveD1RightMatrixContravariantCarrier (I := I)) := by
  rintro ⟨B⟩
  rcases exists_modularThetaSourcePositiveReflectedEighth_vacuumString with
    ⟨n, v, u, hvgen, hugen, hu, hFv, hEu, _hHv, hEv⟩
  have hcomponent : modularThetaSourcePositiveAdaptedComponent (n + 1)
      modularThetaSourcePositiveReflectedEighthPolynomial ∈ B.carrier :=
    modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant
      B.carrier B.sl2E_mem B.sl2F_mem B.d1_mem (n + 1)
  have hvMem : v ∈ B.carrier := by
    rw [hvgen]
    exact B.sl2FIterate_mem n hcomponent
  have huMem : u ∈ B.carrier := by
    rw [hugen]
    exact B.sl2FIterate_mem (n + 1) hcomponent
  have hEvMem : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ∈
      B.carrier := B.sl2E_mem v hvMem
  have hzeroLeft : B.pair 0 v = 0 := by
    have h := B.smul_left (0 : ℂ) u v
    simpa using h
  have hcontra := B.contravariant u v huMem hvMem
  rw [hEu, hFv, hzeroLeft] at hcontra
  have hcoefficient : B.coefficient = 0 := by
    exact (B.positive u huMem hu).isUnit.mul_left_cancel (by
      simpa using hcontra.symm)
  have hcontraEv := B.contravariant v
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hvMem hEvMem
  rw [hcoefficient, Matrix.mul_zero] at hcontraEv
  have hpairZero : B.pair
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v) = 0 :=
    hcontraEv
  have hpos := B.positive
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hEvMem hEv
  exact hpos.isUnit.ne_zero hpairZero

/-- Finite-channel positive matrix-valued contravariant data with the adjoint coefficient acting
on the left channel. -/
structure ModularThetaSourcePositiveD1LeftMatrixContravariantCarrier where
  carrier : Submodule ℂ ModularThetaSourcePositivePolynomial
  d1_mem : modularThetaSourcePositiveReflectedEighthPolynomial ∈ carrier
  sl2E_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ carrier
  sl2F_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ carrier
  coefficient : Matrix I I ℂ
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → Matrix I I ℂ
  smul_left : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair (a • p) q = star a • pair p q
  smul_right : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair p (a • q) = a • pair p q
  positive : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → (pair p p).PosDef
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → q ∈ carrier →
      pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
        coefficient *
          pair p (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q)

omit [DecidableEq I] [Nonempty I] in
theorem ModularThetaSourcePositiveD1LeftMatrixContravariantCarrier.sl2FIterate_mem
    (B : ModularThetaSourcePositiveD1LeftMatrixContravariantCarrier (I := I))
    (n : ℕ) {P : ModularThetaSourcePositivePolynomial} (hP : P ∈ B.carrier) :
    modularThetaSourcePositiveSl2FIterate n P ∈ B.carrier := by
  induction n with
  | zero => exact hP
  | succ n ih => exact B.sl2F_mem _ ih

/-- No finite positive matrix-channel left contravariant lift contains actual D1. -/
theorem modularThetaSourcePositive_no_D1_leftMatrixContravariantCarrier :
    ¬ Nonempty (ModularThetaSourcePositiveD1LeftMatrixContravariantCarrier (I := I)) := by
  rintro ⟨B⟩
  rcases exists_modularThetaSourcePositiveReflectedEighth_vacuumString with
    ⟨n, v, u, hvgen, hugen, hu, hFv, hEu, _hHv, hEv⟩
  have hcomponent : modularThetaSourcePositiveAdaptedComponent (n + 1)
      modularThetaSourcePositiveReflectedEighthPolynomial ∈ B.carrier :=
    modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant
      B.carrier B.sl2E_mem B.sl2F_mem B.d1_mem (n + 1)
  have hvMem : v ∈ B.carrier := by
    rw [hvgen]
    exact B.sl2FIterate_mem n hcomponent
  have huMem : u ∈ B.carrier := by
    rw [hugen]
    exact B.sl2FIterate_mem (n + 1) hcomponent
  have hEvMem : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ∈
      B.carrier := B.sl2E_mem v hvMem
  have hzeroLeft : B.pair 0 v = 0 := by
    have h := B.smul_left (0 : ℂ) u v
    simpa using h
  have hcontra := B.contravariant u v huMem hvMem
  rw [hEu, hFv, hzeroLeft] at hcontra
  have hcoefficient : B.coefficient = 0 := by
    exact (B.positive u huMem hu).isUnit.mul_right_cancel (by
      simpa using hcontra.symm)
  have hcontraEv := B.contravariant v
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hvMem hEvMem
  rw [hcoefficient, Matrix.zero_mul] at hcontraEv
  have hpairZero : B.pair
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v) = 0 :=
    hcontraEv
  have hpos := B.positive
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hEvMem hEv
  exact hpos.isUnit.ne_zero hpairZero

/-- No nonempty finite right matrix channel in any dimension supports a positive D1
contravariant lift. -/
theorem modularThetaSourcePositive_no_D1_finiteRightMatrixContravariantCarrier :
    ¬ ∃ n : ℕ, Nonempty
      (ModularThetaSourcePositiveD1RightMatrixContravariantCarrier
        (I := Fin (n + 1))) := by
  rintro ⟨n, B⟩
  exact modularThetaSourcePositive_no_D1_rightMatrixContravariantCarrier B

/-- No nonempty finite left matrix channel in any dimension supports a positive D1
contravariant lift. -/
theorem modularThetaSourcePositive_no_D1_finiteLeftMatrixContravariantCarrier :
    ¬ ∃ n : ℕ, Nonempty
      (ModularThetaSourcePositiveD1LeftMatrixContravariantCarrier
        (I := Fin (n + 1))) := by
  rintro ⟨n, B⟩
  exact modularThetaSourcePositive_no_D1_leftMatrixContravariantCarrier B

/-- **Finite non-scalar D1 carrier no-go.** Neither canonical side for a matrix-valued
contravariant coefficient admits a positive finite-channel carrier containing actual D1. -/
theorem modularThetaSourcePositive_no_D1_finiteMatrixContravariantCarrier :
    (¬ ∃ n : ℕ, Nonempty
      (ModularThetaSourcePositiveD1RightMatrixContravariantCarrier
        (I := Fin (n + 1)))) ∧
    (¬ ∃ n : ℕ, Nonempty
      (ModularThetaSourcePositiveD1LeftMatrixContravariantCarrier
        (I := Fin (n + 1)))) :=
  ⟨modularThetaSourcePositive_no_D1_finiteRightMatrixContravariantCarrier,
    modularThetaSourcePositive_no_D1_finiteLeftMatrixContravariantCarrier⟩

end

end HTGeometry
