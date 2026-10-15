import GaloisForLFunctions.HTGeometry.PaperRotationPolynomialTraceIntegrality
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Clock induction into the concrete rotation algebra

An integer linear flow on M induces explicit Weyl operators on Z ->_0 M.
The proved independent Weyl basis extends these operators to a genuine
representation of the concrete finite rotation algebra. Intertwiners of
flows induce equivariant maps of these arithmetic clock families.

For finite-dimensional M with a supplied basis, its clock-zero basis
vectors give a surjective finite free cover, equivariant for the algebra
action. This constructs a finitely generated module; it does not assert
projectivity, a completed C*-module structure, or a Chern pairing.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped Classical

section Extension
variable (t : ℝ) (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
variable {A : Type*} [Ring A] [Algebra ℂ A] (W : ℤ → ℤ → A)

private def rotationWordExtension : paperRotationPolynomialAlgebra t →ₗ[ℂ] A :=
  (Finsupp.linearCombination ℂ (fun ab : ℤ × ℤ => W ab.1 ab.2)).comp
    (paperRotationWords_linearIndependent t ht).repr

private theorem rotationWordExtension_word (a b : ℤ) :
    rotationWordExtension t ht W (paperRotationPolynomialWord t a b) = W a b := by
  change Finsupp.linearCombination ℂ _
    ((paperRotationWords_linearIndependent t ht).repr (paperRotationPolynomialWord t a b)) = _
  rw [(paperRotationWords_linearIndependent t ht).repr_eq_single (a, b) _ rfl,
    Finsupp.linearCombination_single, one_smul]

variable (hW0 : W 0 0 = 1)
variable (hWmul : ∀ a b d e : ℤ, W a b * W d e =
  (↑(paperRotationQuantumUnit t ^ (a * e)) : ℂ) • W (a + d) (b + e))

include hW0 in
private theorem rotationWordExtension_one : rotationWordExtension t ht W 1 = 1 := by
  rw [← paperRotationPolynomialWord_zero t, rotationWordExtension_word, hW0]

include hWmul in
private theorem rotationWordExtension_mul (X Y : paperRotationPolynomialAlgebra t) :
    rotationWordExtension t ht W (X * Y) =
      rotationWordExtension t ht W X * rotationWordExtension t ht W Y := by
  induction X using paperRotationPolynomial_induction t with
  | hword a b =>
    induction Y using paperRotationPolynomial_induction t with
    | hword d e =>
      rw [paperRotationPolynomialWord_mul, map_smul, rotationWordExtension_word,
        rotationWordExtension_word, rotationWordExtension_word, hWmul]
    | hzero => simp
    | hadd Y Z hY hZ => simp only [mul_add, map_add, hY, hZ]
    | hsmul z Y hY => simp only [mul_smul_comm, map_smul, hY]
  | hzero => simp
  | hadd X Z hX hZ => simp only [add_mul, map_add, hX, hZ]
  | hsmul z X hX => simp only [smul_mul_assoc, map_smul, hX]

/-- Extend exact Weyl words to the concrete finite operator algebra through its proved basis. -/
def paperRotationRepresentation : paperRotationPolynomialAlgebra t →ₐ[ℂ] A :=
  AlgHom.ofLinearMap (rotationWordExtension t ht W)
    (rotationWordExtension_one t ht W hW0) (rotationWordExtension_mul t ht W hWmul)

@[simp] theorem paperRotationRepresentation_word (a b : ℤ) :
    paperRotationRepresentation t ht W hW0 hWmul (paperRotationPolynomialWord t a b) = W a b :=
  rotationWordExtension_word t ht W a b
end Extension

section Induction
variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- An integer flow on a complex vector space, with its group law included in the data. -/
abbrev IntegerLinearFlow (M : Type*) [AddCommGroup M] [Module ℂ M] :=
  Multiplicative ℤ →* Module.End ℂ M

/-- Clock induction of a literal flow. Both the clock index and the entire source vector survive. -/
def rotationInducedWord (t : ℝ) (T : IntegerLinearFlow M) (a b : ℤ) :
    Module.End ℂ (ℤ →₀ M) :=
  Finsupp.lsum ℂ fun n => (Finsupp.lsingle (n + a)).comp
    (paperRotationPhase ((b : ℝ) * t * ((n + a : ℤ) : ℝ)) • T (Multiplicative.ofAdd b))

@[simp] theorem rotationInducedWord_single (t : ℝ) (T : IntegerLinearFlow M)
    (a b n : ℤ) (m : M) :
    rotationInducedWord t T a b (Finsupp.single n m) =
      Finsupp.single (n + a)
        (paperRotationPhase ((b : ℝ) * t * ((n + a : ℤ) : ℝ)) • T (Multiplicative.ofAdd b) m) := by
  simp [rotationInducedWord]

@[simp] theorem rotationInducedWord_zero (t : ℝ) (T : IntegerLinearFlow M) :
    rotationInducedWord t T 0 0 = 1 := by
  apply Finsupp.lhom_ext
  intro n m
  simp

theorem rotationInducedWord_mul (t : ℝ) (T : IntegerLinearFlow M) (a b d e : ℤ) :
    rotationInducedWord t T a b * rotationInducedWord t T d e =
      (↑(paperRotationQuantumUnit t ^ (a * e)) : ℂ) •
        rotationInducedWord t T (a + d) (b + e) := by
  apply Finsupp.lhom_ext
  intro n m
  change rotationInducedWord t T a b
    (rotationInducedWord t T d e (Finsupp.single n m)) = _
  rw [rotationInducedWord_single, rotationInducedWord_single]
  simp only [LinearMap.smul_apply, rotationInducedWord_single, map_smul, smul_smul]
  have hT : T (Multiplicative.ofAdd b) (T (Multiplicative.ofAdd e) m) =
      T (Multiplicative.ofAdd (b + e)) m :=
    (congrArg (fun L : Module.End ℂ M => L m)
      (T.map_mul (Multiplicative.ofAdd b) (Multiplicative.ofAdd e))).symm
  rw [hT]
  rw [paperRotationQuantumUnit_zpow]
  have hn : n + d + a = n + (a + d) := by omega
  rw [hn]
  simp only [← Finsupp.smul_single, smul_smul, ← paperRotationPhase_add]
  congr 2
  push_cast
  ring

/-- An actual representation of the finite rotation algebra on the integer family of a flow. -/
def rotationInducedRepresentation (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (T : IntegerLinearFlow M) :
    paperRotationPolynomialAlgebra t →ₐ[ℂ] Module.End ℂ (ℤ →₀ M) :=
  paperRotationRepresentation t ht (rotationInducedWord t T)
    (rotationInducedWord_zero t T) (rotationInducedWord_mul t T)

@[simp] theorem rotationInducedRepresentation_word (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (T : IntegerLinearFlow M) (a b : ℤ) :
    rotationInducedRepresentation t ht T (paperRotationPolynomialWord t a b) =
      rotationInducedWord t T a b := paperRotationRepresentation_word _ _ _ _ _ _ _

/-- An intertwiner of source flows induces an intertwiner of their literal Weyl families. -/
theorem rotationInducedWord_natural (t : ℝ) (T : IntegerLinearFlow M) (S : IntegerLinearFlow N)
    (f : M →ₗ[ℂ] N) (hf : ∀ b x, f (T (Multiplicative.ofAdd b) x) = S (Multiplicative.ofAdd b) (f x))
    (a b : ℤ) (x : ℤ →₀ M) :
    Finsupp.mapRange.linearMap f (rotationInducedWord t T a b x) =
      rotationInducedWord t S a b (Finsupp.mapRange.linearMap f x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single n m =>
    simp [rotationInducedWord_single, Finsupp.mapRange.linearMap, hf]

theorem rotationInducedRepresentation_natural (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (T : IntegerLinearFlow M) (S : IntegerLinearFlow N)
    (f : M →ₗ[ℂ] N) (hf : ∀ b x, f (T (Multiplicative.ofAdd b) x) = S (Multiplicative.ofAdd b) (f x))
    (A : paperRotationPolynomialAlgebra t) (x : ℤ →₀ M) :
    Finsupp.mapRange.linearMap f (rotationInducedRepresentation t ht T A x) =
      rotationInducedRepresentation t ht S A (Finsupp.mapRange.linearMap f x) := by
  induction A using paperRotationPolynomial_induction t with
  | hword a b =>
    simp only [rotationInducedRepresentation_word]
    exact rotationInducedWord_natural t T S f hf a b x
  | hzero => simp
  | hadd A B hA hB => simp only [map_add, LinearMap.add_apply, hA, hB]
  | hsmul z A hA => simp only [map_smul, LinearMap.smul_apply, hA]

end Induction
section FreeCover
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {ι : Type*} [Fintype ι]
variable (t : ℝ) (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
variable (T : IntegerLinearFlow M) (B : Module.Basis ι ℂ M)

/-- Finite free cover of the induced module, using the genuine packet basis at clock zero. -/
def rotationInducedFreeCover :
    (ι → paperRotationPolynomialAlgebra t) →ₗ[ℂ] (ℤ →₀ M) where
  toFun A := ∑ i, rotationInducedRepresentation t ht T (A i) (Finsupp.single 0 (B i))
  map_add' A C := by simp [Finset.sum_add_distrib]
  map_smul' z A := by simp [Finset.smul_sum]

/-- The finite cover intertwines left multiplication by every polynomial operator. -/
theorem rotationInducedFreeCover_equivariant (A : paperRotationPolynomialAlgebra t)
    (C : ι → paperRotationPolynomialAlgebra t) :
    rotationInducedRepresentation t ht T A (rotationInducedFreeCover t ht T B C) =
      rotationInducedFreeCover t ht T B (fun i => A * C i) := by
  simp only [rotationInducedFreeCover, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    map_mul, Module.End.mul_apply]

/-- Every clock family of a finite packet is generated by its clock-zero basis vectors. -/
theorem rotationInducedFreeCover_surjective :
    Function.Surjective (rotationInducedFreeCover t ht T B) := by
  intro x
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨A, rfl⟩ := hx
    obtain ⟨C, rfl⟩ := hy
    exact ⟨A + C, map_add _ _ _⟩
  | single n m =>
    refine ⟨fun i => (B.repr m i) • paperRotationPolynomialWord t n 0, ?_⟩
    change (∑ i, rotationInducedRepresentation t ht T
      ((B.repr m i) • paperRotationPolynomialWord t n 0) (Finsupp.single 0 (B i))) = _
    simp only [map_smul, LinearMap.smul_apply, rotationInducedRepresentation_word,
      rotationInducedWord_single, Int.cast_zero, zero_mul, paperRotationPhase_zero,
      zero_add, ofAdd_zero, map_one, Module.End.one_apply, one_smul]
    change (∑ i, (B.repr m i) • Finsupp.single n (B i)) = Finsupp.single n m
    calc
      _ = (Finsupp.lsingle n : M →ₗ[ℂ] ℤ →₀ M) (∑ i, (B.repr m i) • B i) := by
        simp only [map_sum, map_smul, Finsupp.lsingle_apply]
      _ = Finsupp.single n m := by rw [B.sum_repr]; rfl

end FreeCover

end
end GaloisForLFunctions.HTGeometry
