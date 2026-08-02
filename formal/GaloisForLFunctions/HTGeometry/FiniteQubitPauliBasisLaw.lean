import GaloisForLFunctions.HTGeometry.SelfAdjointPauliTransferConservationLaw
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Explicit finite-qubit Pauli basis

This module realizes the abstract label dictionary used by the permanent
locality--Haar separator as the literal Pauli basis of an arbitrary finite
qubit register.  A Pauli string is defined entrywise as the product of its
single-qubit entries.  Exact Hilbert--Schmidt orthogonality then follows by
factoring the finite sum over product configurations.
-/

open scoped BigOperators Matrix
open Module NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Computational configurations of a finite qubit register. -/
abbrev FiniteQubitConfiguration (σ : Type*) := σ → Bool

/-- Pauli X, Y, and Z, indexed in that order. -/
def finiteQubitPauli (q : Fin 3) : Matrix Bool Bool ℂ :=
  if q = 0 then
    fun x y => if x = y then 0 else 1
  else if q = 1 then
    fun x y =>
      if x = y then 0
      else if x = false then -Complex.I else Complex.I
  else
    fun x y =>
      if x = y then
        if x = false then 1 else -1
      else 0

theorem finiteQubitPauli_isHermitian
    (q : Fin 3) :
    (finiteQubitPauli q).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  fin_cases q <;> fin_cases x <;> fin_cases y <;>
    simp [finiteQubitPauli, Matrix.conjTranspose_apply]

/-- The four single-qubit Pauli labels: identity, X, Y, and Z. -/
def boolPauliOption : Option (Fin 3) → Matrix Bool Bool ℂ
  | none => 1
  | some q => finiteQubitPauli q

/-- One Pauli-matrix entry, indexed by a row/column pair. -/
def boolPauliOptionEntry
    (p : Option (Fin 3)) (xy : Bool × Bool) : ℂ :=
  boolPauliOption p xy.1 xy.2

theorem boolPauliOption_isHermitian
    (p : Option (Fin 3)) :
    (boolPauliOption p).IsHermitian := by
  cases p with
  | none => exact Matrix.isHermitian_one
  | some q => exact finiteQubitPauli_isHermitian q

/-- Entrywise Hermiticity of a single-qubit Pauli label. -/
theorem star_boolPauliOptionEntry_swap
    (p : Option (Fin 3)) (x y : Bool) :
    star (boolPauliOptionEntry p (y, x)) =
      boolPauliOptionEntry p (x, y) := by
  have h := boolPauliOption_isHermitian p
  rw [Matrix.IsHermitian] at h
  exact congrFun (congrFun h x) y

/-- A Pauli string on a finite qubit register, in the computational basis. -/
def finitePauliMatrix
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  fun x y => ∏ s, boolPauliOptionEntry (P s) (x s, y s)

/-- Row configuration selected by a function of row/column pairs. -/
def finiteQubitPairRow
    {σ : Type*} (xy : σ → Bool × Bool) :
    FiniteQubitConfiguration σ :=
  fun s => (xy s).1

/-- Column configuration selected by a function of row/column pairs. -/
def finiteQubitPairColumn
    {σ : Type*} (xy : σ → Bool × Bool) :
    FiniteQubitConfiguration σ :=
  fun s => (xy s).2

/-- One arbitrary-qubit Pauli-string entry, indexed by all local row/column
pairs at once. -/
def finitePauliMatrixPairEntry
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) (xy : σ → Bool × Bool) : ℂ :=
  ∏ s, boolPauliOptionEntry (P s) (xy s)

theorem finitePauliMatrix_pairEntry
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) (xy : σ → Bool × Bool) :
    finitePauliMatrix P (finiteQubitPairRow xy)
        (finiteQubitPairColumn xy) =
      finitePauliMatrixPairEntry P xy := by
  rfl

/-- Single-qubit Hilbert--Schmidt pairing of two Pauli labels. -/
def boolPauliHilbertSchmidt
    (p q : Option (Fin 3)) : ℂ :=
  ∑ xy : Bool × Bool,
    star (boolPauliOptionEntry p xy) *
      boolPauliOptionEntry q xy

/-- The four single-qubit Pauli matrices are exactly orthogonal, with squared
Hilbert--Schmidt norm two. -/
theorem boolPauliHilbertSchmidt_eq
    (p q : Option (Fin 3)) :
    boolPauliHilbertSchmidt p q =
      if p = q then 2 else 0 := by
  fin_cases p <;> fin_cases q <;>
    norm_num [boolPauliHilbertSchmidt, boolPauliOptionEntry,
      boolPauliOption, finiteQubitPauli,
      Fintype.sum_prod_type, Fintype.sum_bool] <;>
    try simp

/-- Hilbert--Schmidt pairing of two Pauli strings, written as one sum over
the product of the row and column configurations. -/
def finitePauliHilbertSchmidt
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P Q : σ → Option (Fin 3)) : ℂ :=
  ∑ xy : σ → Bool × Bool,
    ∏ s,
      star (boolPauliOptionEntry (P s) (xy s)) *
        boolPauliOptionEntry (Q s) (xy s)

/-- Exact arbitrary-qubit Pauli orthogonality. -/
theorem finitePauliHilbertSchmidt_eq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P Q : σ → Option (Fin 3)) :
    finitePauliHilbertSchmidt P Q =
      if P = Q then (2 : ℂ) ^ Fintype.card σ else 0 := by
  rw [finitePauliHilbertSchmidt]
  calc
    (∑ xy : σ → Bool × Bool,
      ∏ s,
        star (boolPauliOptionEntry (P s) (xy s)) *
          boolPauliOptionEntry (Q s) (xy s)) =
      ∏ s, ∑ xy : Bool × Bool,
        star (boolPauliOptionEntry (P s) xy) *
          boolPauliOptionEntry (Q s) xy :=
        (Fintype.prod_sum (fun s (xy : Bool × Bool) =>
          star (boolPauliOptionEntry (P s) xy) *
            boolPauliOptionEntry (Q s) xy)).symm
    _ = if P = Q then (2 : ℂ) ^ Fintype.card σ else 0 := by
      change (∏ s, boolPauliHilbertSchmidt (P s) (Q s)) =
        if P = Q then (2 : ℂ) ^ Fintype.card σ else 0
      simp_rw [boolPauliHilbertSchmidt_eq]
      by_cases hPQ : P = Q
      · subst Q
        simp [Finset.prod_const]
      · obtain ⟨s, hs⟩ : ∃ s, P s ≠ Q s := by
          simpa only [Function.ne_iff] using hPQ
        rw [if_neg hPQ]
        apply Finset.prod_eq_zero (Finset.mem_univ s)
        simp [hs]

/-- Every finite Pauli string is Hermitian. -/
theorem finitePauliMatrix_isHermitian
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    (finitePauliMatrix P).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  rw [Matrix.conjTranspose_apply]
  change
    star (∏ s, boolPauliOptionEntry (P s) (y s, x s)) =
      ∏ s, boolPauliOptionEntry (P s) (x s, y s)
  calc
    star (∏ s, boolPauliOptionEntry (P s) (y s, x s)) =
        ∏ s, star (boolPauliOptionEntry (P s) (y s, x s)) :=
      map_prod (starRingEnd ℂ) _ Finset.univ
    _ = ∏ s, boolPauliOptionEntry (P s) (x s, y s) := by
      apply Finset.prod_congr rfl
      intro s _hs
      exact star_boolPauliOptionEntry_swap (P s) (x s) (y s)

/-- A Pauli string as a literal self-adjoint matrix. -/
def finitePauliSelfAdjoint
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :=
  ⟨finitePauliMatrix P, finitePauliMatrix_isHermitian P⟩

/-- Hilbert--Schmidt pairing against a fixed Pauli string, as a complex-linear
functional on the full matrix space. -/
def finitePauliPairingLinear
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ →ₗ[ℂ] ℂ where
  toFun A :=
    ∑ xy : σ → Bool × Bool,
      star (finitePauliMatrixPairEntry P xy) *
        A (finiteQubitPairRow xy) (finiteQubitPairColumn xy)
  map_add' A B := by
    change
      (∑ xy : σ → Bool × Bool,
        star (finitePauliMatrixPairEntry P xy) *
          (A (finiteQubitPairRow xy) (finiteQubitPairColumn xy) +
            B (finiteQubitPairRow xy) (finiteQubitPairColumn xy))) =
        (∑ xy : σ → Bool × Bool,
          star (finitePauliMatrixPairEntry P xy) *
            A (finiteQubitPairRow xy) (finiteQubitPairColumn xy)) +
        ∑ xy : σ → Bool × Bool,
          star (finitePauliMatrixPairEntry P xy) *
            B (finiteQubitPairRow xy) (finiteQubitPairColumn xy)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' z A := by
    change
      (∑ xy : σ → Bool × Bool,
        star (finitePauliMatrixPairEntry P xy) *
          (z * A (finiteQubitPairRow xy) (finiteQubitPairColumn xy))) =
        z * ∑ xy : σ → Bool × Bool,
          star (finitePauliMatrixPairEntry P xy) *
            A (finiteQubitPairRow xy) (finiteQubitPairColumn xy)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro xy _hxy
    ring

/-- Pairing a Pauli string against another literal Pauli matrix gives the
factored Hilbert--Schmidt pairing proved above. -/
theorem finitePauliPairingLinear_apply_pauli
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P Q : σ → Option (Fin 3)) :
    finitePauliPairingLinear P (finitePauliMatrix Q) =
      finitePauliHilbertSchmidt P Q := by
  rw [finitePauliPairingLinear, finitePauliHilbertSchmidt]
  apply Finset.sum_congr rfl
  intro xy _hxy
  rw [finitePauliMatrix_pairEntry]
  change
    star (∏ s, boolPauliOptionEntry (P s) (xy s)) *
        (∏ s, boolPauliOptionEntry (Q s) (xy s)) =
      ∏ s,
        star (boolPauliOptionEntry (P s) (xy s)) *
          boolPauliOptionEntry (Q s) (xy s)
  calc
    star (∏ s, boolPauliOptionEntry (P s) (xy s)) *
        (∏ s, boolPauliOptionEntry (Q s) (xy s)) =
      (∏ s, star (boolPauliOptionEntry (P s) (xy s))) *
        (∏ s, boolPauliOptionEntry (Q s) (xy s)) := by
          congr 1
          exact map_prod (starRingEnd ℂ) _ Finset.univ
    _ = ∏ s,
        star (boolPauliOptionEntry (P s) (xy s)) *
          boolPauliOptionEntry (Q s) (xy s) :=
      Finset.prod_mul_distrib.symm

/-- The literal finite-qubit Pauli matrices are complex-linearly independent. -/
theorem finitePauliMatrix_linearIndependent
    {σ : Type*} [Fintype σ] [DecidableEq σ] :
    LinearIndependent ℂ
      (finitePauliMatrix :
        (σ → Option (Fin 3)) →
          Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum P
  have hpair := congrArg (finitePauliPairingLinear P) hsum
  simp only [map_sum, map_smul, map_zero,
    finitePauliPairingLinear_apply_pauli,
    finitePauliHilbertSchmidt_eq] at hpair
  have hpow : (2 : ℂ) ^ Fintype.card σ ≠ 0 := pow_ne_zero _ (by norm_num)
  have : c P * (2 : ℂ) ^ Fintype.card σ = 0 := by
    simpa [eq_comm] using hpair
  exact (mul_eq_zero.mp this).resolve_right hpow

/-- Multiplication by `-i` identifies skew-adjoint and self-adjoint parts as
real vector spaces. -/
def skewAdjointSelfAdjointLinearEquiv
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    [StarAddMonoid A] [StarModule ℂ A] :
    skewAdjoint A ≃ₗ[ℝ] selfAdjoint A :=
  LinearEquiv.ofBijective skewAdjoint.negISMul ⟨by
    intro a b hab
    apply Subtype.ext
    calc
      (a : A) = Complex.I • (skewAdjoint.negISMul a : A) :=
        (skewAdjoint.I_smul_neg_I a).symm
      _ = Complex.I • (skewAdjoint.negISMul b : A) := by
        rw [hab]
      _ = (b : A) := skewAdjoint.I_smul_neg_I b, by
    intro a
    let b : skewAdjoint A :=
      ⟨Complex.I • (a : A),
        Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint.mpr a.prop⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    simp [b, skewAdjoint.negISMul, smul_smul]⟩

/-- Real dimension of Hermitian matrices is the square of Hilbert dimension. -/
theorem finrank_selfAdjoint_complexMatrix
    (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Module.finrank ℝ (selfAdjoint (Matrix κ κ ℂ)) =
      Fintype.card κ * Fintype.card κ := by
  let A := Matrix κ κ ℂ
  letI : FiniteDimensional ℝ A := by infer_instance
  letI : FiniteDimensional ℝ (selfAdjoint A) :=
    FiniteDimensional.of_injective
      (selfAdjoint.submodule ℝ A).subtype
      (Submodule.injective_subtype _)
  letI : FiniteDimensional ℝ (skewAdjoint A) :=
    FiniteDimensional.of_injective
      (skewAdjoint.submodule ℝ A).subtype
      (Submodule.injective_subtype _)
  have hdecomp :=
    (StarModule.decomposeProdAdjoint ℝ A).finrank_eq
  have hskew :=
    (skewAdjointSelfAdjointLinearEquiv
      (A := A)).finrank_eq
  have hreal :
      Module.finrank ℝ A =
        2 * (Fintype.card κ * Fintype.card κ) := by
    have hcomplex : Module.finrank ℝ ℂ = 2 := by
      simpa using
        (Module.finrank_eq_card_basis Complex.basisOneI)
    calc
      Module.finrank ℝ A =
          Module.finrank ℝ ℂ * Module.finrank ℂ A :=
        (Module.finrank_mul_finrank ℝ ℂ A).symm
      _ = 2 * (Fintype.card κ * Fintype.card κ) := by
        rw [hcomplex]
        simp [A, Module.finrank_matrix]
  rw [Module.finrank_prod, hskew] at hdecomp
  change Module.finrank ℝ (selfAdjoint A) =
    Fintype.card κ * Fintype.card κ
  omega

/-- The literal self-adjoint Pauli strings are real-linearly independent. -/
theorem finitePauliSelfAdjoint_linearIndependent
    {σ : Type*} [Fintype σ] [DecidableEq σ] :
    LinearIndependent ℝ
      (finitePauliSelfAdjoint :
        (σ → Option (Fin 3)) →
          selfAdjoint
            (Matrix (FiniteQubitConfiguration σ)
              (FiniteQubitConfiguration σ) ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum P
  have hsumCoe := congrArg
    (fun A :
      selfAdjoint
        (Matrix (FiniteQubitConfiguration σ)
          (FiniteQubitConfiguration σ) ℂ) => (A :
            Matrix (FiniteQubitConfiguration σ)
              (FiniteQubitConfiguration σ) ℂ)) hsum
  have hsumC :
      ∑ Q, (c Q : ℂ) • finitePauliMatrix Q = 0 := by
    ext x y
    have hxy := congrFun (congrFun hsumCoe x) y
    simpa [finitePauliSelfAdjoint, Finset.sum_apply] using hxy
  have hc :=
    Fintype.linearIndependent_iff.mp
      (finitePauliMatrix_linearIndependent (σ := σ))
      (fun Q => (c Q : ℂ)) hsumC P
  exact_mod_cast hc

/-- Pauli-label cardinality equals the real dimension of Hermitian matrices. -/
theorem finitePauliLabel_card_eq_selfAdjoint_finrank
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Fintype.card (σ → Option (Fin 3)) =
      Module.finrank ℝ
        (selfAdjoint
          (Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ)) := by
  rw [finrank_selfAdjoint_complexMatrix]
  simp only [Fintype.card_fun, Fintype.card_option,
    Fintype.card_fin, Fintype.card_bool]
  rw [← mul_pow]
  norm_num

/-- Literal arbitrary-qubit Pauli basis of the real Hermitian matrix space. -/
def finitePauliSelfAdjointBasis
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Basis (σ → Option (Fin 3)) ℝ
      (selfAdjoint
        (Matrix (FiniteQubitConfiguration σ)
          (FiniteQubitConfiguration σ) ℂ)) :=
  basisOfLinearIndependentOfCardEqFinrank
    (finitePauliSelfAdjoint_linearIndependent (σ := σ))
    (finitePauliLabel_card_eq_selfAdjoint_finrank σ)

@[simp]
theorem finitePauliSelfAdjointBasis_apply
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    finitePauliSelfAdjointBasis σ P =
      finitePauliSelfAdjoint P := by
  exact congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank
      (finitePauliSelfAdjoint_linearIndependent (σ := σ))
      (finitePauliLabel_card_eq_selfAdjoint_finrank σ)) P

/-- Principal coordinate compression to the labels satisfying `p`. -/
def matrixCoordinateCompression
    {R ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p]
    (T : Matrix ι ι R) :
    Matrix {i // p i} {i // p i} R :=
  fun i j => T i.1 j.1

/-- Restriction of a coordinate vector to the labels satisfying `p`. -/
def vectorCoordinateRestriction
    {R ι : Type*}
    (p : ι → Prop) (v : ι → R) :
    {i // p i} → R :=
  fun i => v i.1

/-- A fixed vector supported on a coordinate sector remains fixed after
principal compression to that sector. -/
theorem matrixCoordinateCompression_mulVec_restriction_eq_of_fixed_of_support
    {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p]
    (T : Matrix ι ι R) (v : ι → R)
    (hfix : T *ᵥ v = v)
    (hsupport : ∀ i, ¬ p i → v i = 0) :
    matrixCoordinateCompression p T *ᵥ
        vectorCoordinateRestriction p v =
      vectorCoordinateRestriction p v := by
  funext i
  change
    (∑ j : {j // p j}, T i.1 j.1 * v j.1) = v i.1
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype p
      (fun j => T i.1 j * v j)
  have hout :
      (∑ j : {j // ¬ p j}, T i.1 j.1 * v j.1) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    rw [hsupport j.1 j.2, mul_zero]
  have hfull :
      (∑ j, T i.1 j * v j) = v i.1 := by
    have hi := congrFun hfix i.1
    simpa [Matrix.mulVec, dotProduct] using hi
  rw [hout, add_zero] at hsplit
  rw [hsplit, hfull]

/-- Restricting a nonzero vector to a sector containing its full support
cannot produce the zero vector. -/
theorem vectorCoordinateRestriction_ne_zero_of_ne_zero_of_support
    {R ι : Type*} [Zero R]
    (p : ι → Prop) (v : ι → R)
    (hv : v ≠ 0)
    (hsupport : ∀ i, ¬ p i → v i = 0) :
    vectorCoordinateRestriction p v ≠ 0 := by
  intro hzero
  apply hv
  funext i
  by_cases hi : p i
  · have hz := congrFun hzero ⟨i, hi⟩
    simpa [vectorCoordinateRestriction] using hz
  · exact hsupport i hi

/-- Labels of Pauli strings supported on at most `q` qubits. -/
abbrev FiniteQLocalPauliLabel
    (σ : Type*) [Fintype σ] (q : ℕ) :=
  {P : σ → Option (Fin 3) // finitePauliWeight P ≤ q}

/-- A Hamiltonian is `q`-local in Pauli support when every Pauli coefficient
of weight greater than `q` vanishes. -/
def HasPauliWeightAtMost
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ)) : Prop :=
  ∀ P : σ → Option (Fin 3),
    q < finitePauliWeight P →
      ((finitePauliSelfAdjointBasis σ).repr H :
        (σ → Option (Fin 3)) → ℝ) P = 0

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- Real-linear conjugation of self-adjoint finite matrices, without replacing
the literal matrix type by a bundled C-star-matrix wrapper. -/
def finiteMatrixSelfAdjointConjugationLinearMap
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix κ κ ℂ) :
    selfAdjoint (Matrix κ κ ℂ) →ₗ[ℝ]
      selfAdjoint (Matrix κ κ ℂ) where
  toFun X :=
    ⟨star U * (X : Matrix κ κ ℂ) * U,
      X.prop.conjugate' U⟩
  map_add' X Y := by
    ext
    simp [mul_add, add_mul]
  map_smul' r X := by
    ext
    simp

/-- Literal finite-matrix Schrödinger evolution fixes its generating
Hamiltonian under Heisenberg conjugation at every real time. -/
theorem finiteMatrixSelfAdjointConjugation_fixes_energy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : selfAdjoint (Matrix κ κ ℂ)) (t : ℝ) :
    finiteMatrixSelfAdjointConjugationLinearMap
        (exp (t • ((-Complex.I) •
          (H : Matrix κ κ ℂ)))) H = H := by
  apply Subtype.ext
  change
    star (exp (t • ((-Complex.I) •
      (H : Matrix κ κ ℂ)))) *
      (H : Matrix κ κ ℂ) *
      exp (t • ((-Complex.I) •
        (H : Matrix κ κ ℂ))) = H
  let _ : NormedAlgebra ℚ (Matrix κ κ ℂ) :=
    .restrictScalars ℚ ℂ (Matrix κ κ ℂ)
  have hx :
      (-Complex.I) • (H : Matrix κ κ ℂ) ∈
        skewAdjoint (Matrix κ κ ℂ) := by
    rw [skewAdjoint.mem_iff, star_smul, H.prop.star_eq]
    simp
  rw [star_exp,
    skewAdjoint.mem_iff.mp (skewAdjoint.smul_mem t hx)]
  have hcomm :
      Commute (H : Matrix κ κ ℂ)
        (t • ((-Complex.I) •
          (H : Matrix κ κ ℂ))) := by
    exact
      ((Commute.refl (H : Matrix κ κ ℂ)).smul_right
        (-Complex.I)).smul_right t
  exact hcomm.exp_neg_mul_mul_exp_eq_self

/-- Principal `q`-local block of the exact Pauli-transfer matrix. -/
def finiteQLocalPauliTransferMatrix
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ))
    (t : ℝ) :
    Matrix (FiniteQLocalPauliLabel σ q)
      (FiniteQLocalPauliLabel σ q) ℝ :=
  matrixCoordinateCompression
    (fun P : σ → Option (Fin 3) =>
      finitePauliWeight P ≤ q)
    (LinearMap.toMatrix
      (finitePauliSelfAdjointBasis σ)
      (finitePauliSelfAdjointBasis σ)
      (finiteMatrixSelfAdjointConjugationLinearMap
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ))))))

/-- Restriction of the Hamiltonian's Pauli coordinates to weight at most
`q`. -/
def finiteQLocalEnergyCoordinates
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ)) :
    FiniteQLocalPauliLabel σ q → ℝ :=
  vectorCoordinateRestriction
    (fun P : σ → Option (Fin 3) =>
      finitePauliWeight P ≤ q)
    ((finitePauliSelfAdjointBasis σ).repr H :
      (σ → Option (Fin 3)) → ℝ)

/-- Exact conservation survives compression to the full `q`-local Pauli
sector for every real time. -/
theorem finiteQLocalPauliTransferMatrix_fixes_energyCoordinates
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ))
    (hlocal : HasPauliWeightAtMost σ q H)
    (t : ℝ) :
    finiteQLocalPauliTransferMatrix σ q H t *ᵥ
        finiteQLocalEnergyCoordinates σ q H =
      finiteQLocalEnergyCoordinates σ q H := by
  rw [finiteQLocalPauliTransferMatrix,
    finiteQLocalEnergyCoordinates]
  apply
    matrixCoordinateCompression_mulVec_restriction_eq_of_fixed_of_support
  · exact
      linearMap_toMatrix_mulVec_repr_eq_of_fixed
        (finitePauliSelfAdjointBasis σ)
        (finiteMatrixSelfAdjointConjugationLinearMap
          (exp (t • ((-Complex.I) •
            (H : Matrix (FiniteQubitConfiguration σ)
              (FiniteQubitConfiguration σ) ℂ)))))
        H
        (finiteMatrixSelfAdjointConjugation_fixes_energy H t)
  · intro P hP
    exact hlocal P (Nat.lt_of_not_ge hP)

/-- A nonzero `q`-local Hamiltonian has a nonzero coordinate vector in the
`q`-local Pauli sector. -/
theorem finiteQLocalEnergyCoordinates_ne_zero
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ))
    (hH : H ≠ 0)
    (hlocal : HasPauliWeightAtMost σ q H) :
    finiteQLocalEnergyCoordinates σ q H ≠ 0 := by
  rw [finiteQLocalEnergyCoordinates]
  apply vectorCoordinateRestriction_ne_zero_of_ne_zero_of_support
  · intro hzero
    apply hH
    apply (finitePauliSelfAdjointBasis σ).repr.injective
    exact Finsupp.ext fun P => by
      simpa using congrFun hzero P
  · intro P hP
    exact hlocal P (Nat.lt_of_not_ge hP)

/-- **Literal finite-qubit permanent separator.** Every nonzero
time-independent Hamiltonian with Pauli weight at most `q` retains, at every
real time, a product-stabilizer two-query signal strictly above the exact
inverse-dimension Haar benchmark whenever the displayed finite-size
inequality holds. -/
theorem finiteQLocalAutonomousTransferSignal_gt_haarBenchmark
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ))
    (hH : H ≠ 0)
    (hlocal : HasPauliWeightAtMost σ q H)
    (t : ℝ)
    (hsep :
      Fintype.card (FiniteQLocalPauliLabel σ q) * 3 ^ q <
        2 ^ Fintype.card σ + 1) :
    1 / (((2 ^ Fintype.card σ + 1 : ℕ) : ℝ)) <
      productStabilizerTwoQueryProtocolSignal
        (fun P : FiniteQLocalPauliLabel σ q => P.1)
        (finiteQLocalPauliTransferMatrix σ q H t) := by
  classical
  let identityLabel : σ → Option (Fin 3) := fun _ => none
  have hidentity :
      finitePauliWeight identityLabel ≤ q := by
    simp [finitePauliWeight, identityLabel]
  letI : Nonempty (FiniteQLocalPauliLabel σ q) :=
    ⟨⟨identityLabel, hidentity⟩⟩
  exact
    productStabilizerTwoQueryProtocolSignal_gt_haarBenchmark
      q (2 ^ Fintype.card σ)
      (fun P : FiniteQLocalPauliLabel σ q => P.1)
      Subtype.val_injective
      (fun P => P.2)
      (finiteQLocalPauliTransferMatrix σ q H t)
      (finiteQLocalEnergyCoordinates σ q H)
      (finiteQLocalEnergyCoordinates_ne_zero σ q H hH hlocal)
      (finiteQLocalPauliTransferMatrix_fixes_energyCoordinates
        σ q H hlocal t)
      hsep

end

end GaloisForLFunctions.HTGeometry
