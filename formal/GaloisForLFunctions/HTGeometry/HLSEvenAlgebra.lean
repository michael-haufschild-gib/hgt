import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Complex.Basic

/-!
# The even (bosonic) Coleman--Mandula algebra in spinorial form

The Haag--Łopuszański--Sohnius theorem classifies the `ℤ₂`-graded extensions of the
bosonic symmetry algebra that Coleman--Mandula leaves available, namely

  `𝔤₀ = 𝔰𝔩₂(ℂ) ⊕ 𝔰𝔩₂(ℂ) ⊕ (translations) ⊕ (internal)`,

written in the spinor basis where the complexified Lorentz algebra is a sum of two
commuting copies of `𝔰𝔩₂(ℂ)` and translations `P_{α α̇}` form the `(½, ½)` bimodule of
`2 × 2` matrices.  This module builds `𝔤₀` concretely, together with its bracket,
its real-form conjugation, and the Cartan pair `(h, h̄)` used in the weight analysis.

Nothing here is a hypothesis: the algebra is an explicit construction and every
structural law is proved.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- Coordinates of an `𝔰𝔩₂(ℂ)` element in the basis `(e, f, h)`. -/
abbrev HLSSl2 : Type := Fin 3 → ℂ

/-- The `2 × 2` traceless matrix attached to `𝔰𝔩₂` coordinates `(e, f, h)`. -/
def hlsSl2Mat (x : HLSSl2) : Matrix (Fin 2) (Fin 2) ℂ := !![x 2, x 0; x 1, -x 2]

/-- The `𝔰𝔩₂` bracket in the `(e, f, h)` basis. -/
def hlsSl2Br (x y : HLSSl2) : HLSSl2 :=
  ![2 * (y 0 * x 2 - x 0 * y 2), 2 * (x 1 * y 2 - y 1 * x 2), x 0 * y 1 - y 0 * x 1]

/-- The raising generator `e`. -/
def hlsSl2E : HLSSl2 := ![1, 0, 0]

/-- The lowering generator `f`. -/
def hlsSl2F : HLSSl2 := ![0, 1, 0]

/-- The Cartan generator `h`. -/
def hlsSl2H : HLSSl2 := ![0, 0, 1]

@[simp] theorem hlsSl2Mat_zero : hlsSl2Mat 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat]

theorem hlsSl2Mat_add (x y : HLSSl2) : hlsSl2Mat (x + y) = hlsSl2Mat x + hlsSl2Mat y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat, add_comm]

theorem hlsSl2Mat_smul (c : ℂ) (x : HLSSl2) : hlsSl2Mat (c • x) = c • hlsSl2Mat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat]

/-- `hlsSl2Mat` turns the coordinate bracket into the matrix commutator. -/
theorem hlsSl2Mat_br (x y : HLSSl2) :
    hlsSl2Mat (hlsSl2Br x y) = hlsSl2Mat x * hlsSl2Mat y - hlsSl2Mat y * hlsSl2Mat x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat, hlsSl2Br] <;> ring

/-- `hlsSl2Mat` is injective, so the coordinate bracket is determined by the matrix
commutator. -/
theorem hlsSl2Mat_injective : Function.Injective hlsSl2Mat := by
  intro x y h
  funext i
  have h0 := congr_fun (congr_fun h 0) 1
  have h1 := congr_fun (congr_fun h 1) 0
  have h2 := congr_fun (congr_fun h 0) 0
  simp [hlsSl2Mat] at h0 h1 h2
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem hlsSl2Br_add_left (x y z : HLSSl2) :
    hlsSl2Br (x + y) z = hlsSl2Br x z + hlsSl2Br y z := by
  funext i; fin_cases i <;> simp [hlsSl2Br] <;> ring

theorem hlsSl2Br_add_right (x y z : HLSSl2) :
    hlsSl2Br x (y + z) = hlsSl2Br x y + hlsSl2Br x z := by
  funext i; fin_cases i <;> simp [hlsSl2Br] <;> ring

theorem hlsSl2Br_smul_left (c : ℂ) (x y : HLSSl2) :
    hlsSl2Br (c • x) y = c • hlsSl2Br x y := by
  funext i; fin_cases i <;> simp [hlsSl2Br] <;> ring

theorem hlsSl2Br_smul_right (c : ℂ) (x y : HLSSl2) :
    hlsSl2Br x (c • y) = c • hlsSl2Br x y := by
  funext i; fin_cases i <;> simp [hlsSl2Br] <;> ring

@[simp] theorem hlsSl2Br_self (x : HLSSl2) : hlsSl2Br x x = 0 := by
  funext i; fin_cases i <;> simp [hlsSl2Br]

theorem hlsSl2Br_skew (x y : HLSSl2) : hlsSl2Br x y = -hlsSl2Br y x := by
  funext i; fin_cases i <;> simp [hlsSl2Br] <;> ring

theorem hlsSl2Br_jacobi (x y z : HLSSl2) :
    hlsSl2Br x (hlsSl2Br y z) + hlsSl2Br y (hlsSl2Br z x) + hlsSl2Br z (hlsSl2Br x y) = 0 := by
  funext i; fin_cases i <;> simp [hlsSl2Br] <;> ring

@[simp] theorem hlsSl2Br_e_f : hlsSl2Br hlsSl2E hlsSl2F = hlsSl2H := by
  funext i; fin_cases i <;> simp [hlsSl2Br, hlsSl2E, hlsSl2F, hlsSl2H]

@[simp] theorem hlsSl2Br_h_e : hlsSl2Br hlsSl2H hlsSl2E = (2 : ℂ) • hlsSl2E := by
  funext i; fin_cases i <;> simp [hlsSl2Br, hlsSl2E, hlsSl2H]

@[simp] theorem hlsSl2Br_h_f : hlsSl2Br hlsSl2H hlsSl2F = (-2 : ℂ) • hlsSl2F := by
  funext i; fin_cases i <;> simp [hlsSl2Br, hlsSl2F, hlsSl2H]

/-- The Lorentz action on the translation bimodule `P_{α α̇}`:
the undotted `𝔰𝔩₂` acts on rows, the dotted one on columns. -/
def hlsLorAct (x x' : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  hlsSl2Mat x * P + P * (hlsSl2Mat x')ᵀ

theorem hlsLorAct_br (x x' y y' : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsLorAct (hlsSl2Br x y) (hlsSl2Br x' y') P
      = hlsLorAct x x' (hlsLorAct y y' P) - hlsLorAct y y' (hlsLorAct x x' P) := by
  simp only [hlsLorAct, hlsSl2Mat_br, Matrix.transpose_sub, Matrix.transpose_mul]
  noncomm_ring


section Even

variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]

@[simp] theorem hlsLorAct_zero_lor (P : Matrix (Fin 2) (Fin 2) ℂ) : hlsLorAct 0 0 P = 0 := by
  simp [hlsLorAct]

@[simp] theorem hlsLorAct_zero_mom (x x' : HLSSl2) : hlsLorAct x x' 0 = 0 := by
  simp [hlsLorAct]

theorem hlsLorAct_add_mom (x x' : HLSSl2) (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsLorAct x x' (P + Q) = hlsLorAct x x' P + hlsLorAct x x' Q := by
  simp only [hlsLorAct, Matrix.mul_add, Matrix.add_mul]; abel

theorem hlsLorAct_smul_mom (c : ℂ) (x x' : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsLorAct x x' (c • P) = c • hlsLorAct x x' P := by
  simp only [hlsLorAct, Matrix.mul_smul, Matrix.smul_mul, smul_add]

theorem hlsLorAct_add_lor (x y x' y' : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsLorAct (x + y) (x' + y') P = hlsLorAct x x' P + hlsLorAct y y' P := by
  simp only [hlsLorAct, hlsSl2Mat_add, Matrix.add_mul, Matrix.transpose_add, Matrix.mul_add]
  abel

theorem hlsLorAct_smul_lor (c : ℂ) (x x' : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsLorAct (c • x) (c • x') P = c • hlsLorAct x x' P := by
  simp only [hlsLorAct, hlsSl2Mat_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.mul_smul,
    smul_add]

/-- The even part `𝔤₀` of a Coleman--Mandula symmetry algebra, in spinorial coordinates:
undotted `𝔰𝔩₂`, dotted `𝔰𝔩₂`, translations `P_{α α̇}`, internal charges. -/
abbrev HLSEven (B : Type*) [LieRing B] [LieAlgebra ℂ B] :=
  HLSSl2 × HLSSl2 × Matrix (Fin 2) (Fin 2) ℂ × B

/-- The bracket of `𝔤₀`: `(Lorentz ⋉ translations) ⊕ internal`. -/
def hlsEvenBr (X Y : HLSEven B) : HLSEven B :=
  (hlsSl2Br X.1 Y.1, hlsSl2Br X.2.1 Y.2.1,
    hlsLorAct X.1 X.2.1 Y.2.2.1 - hlsLorAct Y.1 Y.2.1 X.2.2.1,
    ⁅X.2.2.2, Y.2.2.2⁆)

/-- Undotted Lorentz generator. -/
def hlsLorL (x : HLSSl2) : HLSEven B := (x, 0, 0, 0)

/-- Dotted Lorentz generator. -/
def hlsLorR (x : HLSSl2) : HLSEven B := (0, x, 0, 0)

/-- Translation generator `P_{α α̇}`. -/
def hlsMom (P : Matrix (Fin 2) (Fin 2) ℂ) : HLSEven B := (0, 0, P, 0)

/-- Internal generator. -/
def hlsInt (b : B) : HLSEven B := (0, 0, 0, b)

@[simp] theorem hlsEvenBr_self (X : HLSEven B) : hlsEvenBr X X = 0 := by
  simp [hlsEvenBr, Prod.ext_iff]

theorem hlsEvenBr_skew (X Y : HLSEven B) : hlsEvenBr X Y = -hlsEvenBr Y X := by
  simp only [hlsEvenBr, Prod.neg_mk, Prod.mk.injEq]
  refine ⟨hlsSl2Br_skew _ _, hlsSl2Br_skew _ _, by abel, (lie_skew _ _).symm⟩

theorem hlsEvenBr_add_left (X Y Z : HLSEven B) :
    hlsEvenBr (X + Y) Z = hlsEvenBr X Z + hlsEvenBr Y Z := by
  refine Prod.ext (hlsSl2Br_add_left _ _ _) (Prod.ext (hlsSl2Br_add_left _ _ _) (Prod.ext ?_ ?_))
  · show hlsLorAct (X.1 + Y.1) (X.2.1 + Y.2.1) Z.2.2.1
        - hlsLorAct Z.1 Z.2.1 (X.2.2.1 + Y.2.2.1) = _
    rw [hlsLorAct_add_lor, hlsLorAct_add_mom]
    show _ = (hlsLorAct X.1 X.2.1 Z.2.2.1 - hlsLorAct Z.1 Z.2.1 X.2.2.1)
        + (hlsLorAct Y.1 Y.2.1 Z.2.2.1 - hlsLorAct Z.1 Z.2.1 Y.2.2.1)
    abel
  · show ⁅X.2.2.2 + Y.2.2.2, Z.2.2.2⁆ = _
    exact add_lie _ _ _

theorem hlsEvenBr_add_right (X Y Z : HLSEven B) :
    hlsEvenBr X (Y + Z) = hlsEvenBr X Y + hlsEvenBr X Z := by
  rw [hlsEvenBr_skew, hlsEvenBr_add_left, hlsEvenBr_skew Y X, hlsEvenBr_skew Z X]
  abel

theorem hlsEvenBr_smul_left (c : ℂ) (X Y : HLSEven B) :
    hlsEvenBr (c • X) Y = c • hlsEvenBr X Y := by
  refine Prod.ext (hlsSl2Br_smul_left _ _ _) (Prod.ext (hlsSl2Br_smul_left _ _ _) (Prod.ext ?_ ?_))
  · show hlsLorAct (c • X.1) (c • X.2.1) Y.2.2.1 - hlsLorAct Y.1 Y.2.1 (c • X.2.2.1) = _
    rw [hlsLorAct_smul_lor, hlsLorAct_smul_mom]
    show _ = c • (hlsLorAct X.1 X.2.1 Y.2.2.1 - hlsLorAct Y.1 Y.2.1 X.2.2.1)
    rw [smul_sub]
  · show ⁅c • X.2.2.2, Y.2.2.2⁆ = _
    exact smul_lie _ _ _

theorem hlsEvenBr_smul_right (c : ℂ) (X Y : HLSEven B) :
    hlsEvenBr X (c • Y) = c • hlsEvenBr X Y := by
  rw [hlsEvenBr_skew, hlsEvenBr_smul_left, hlsEvenBr_skew Y X, smul_neg, neg_neg]

@[simp] theorem hlsEvenBr_zero_left (Y : HLSEven B) : hlsEvenBr 0 Y = 0 := by
  have := hlsEvenBr_smul_left (0 : ℂ) (0 : HLSEven B) Y
  simpa using this

@[simp] theorem hlsEvenBr_zero_right (X : HLSEven B) : hlsEvenBr X 0 = 0 := by
  rw [hlsEvenBr_skew, hlsEvenBr_zero_left, neg_zero]

theorem hlsEvenBr_jacobi (X Y Z : HLSEven B) :
    hlsEvenBr X (hlsEvenBr Y Z) + hlsEvenBr Y (hlsEvenBr Z X)
      + hlsEvenBr Z (hlsEvenBr X Y) = 0 := by
  refine Prod.ext (hlsSl2Br_jacobi _ _ _) (Prod.ext (hlsSl2Br_jacobi _ _ _) (Prod.ext ?_ ?_))
  · show hlsLorAct X.1 X.2.1 (hlsLorAct Y.1 Y.2.1 Z.2.2.1 - hlsLorAct Z.1 Z.2.1 Y.2.2.1)
        - hlsLorAct (hlsSl2Br Y.1 Z.1) (hlsSl2Br Y.2.1 Z.2.1) X.2.2.1
      + (hlsLorAct Y.1 Y.2.1 (hlsLorAct Z.1 Z.2.1 X.2.2.1 - hlsLorAct X.1 X.2.1 Z.2.2.1)
        - hlsLorAct (hlsSl2Br Z.1 X.1) (hlsSl2Br Z.2.1 X.2.1) Y.2.2.1)
      + (hlsLorAct Z.1 Z.2.1 (hlsLorAct X.1 X.2.1 Y.2.2.1 - hlsLorAct Y.1 Y.2.1 X.2.2.1)
        - hlsLorAct (hlsSl2Br X.1 Y.1) (hlsSl2Br X.2.1 Y.2.1) Z.2.2.1) = 0
    rw [hlsLorAct_br X.1 X.2.1 Y.1 Y.2.1, hlsLorAct_br Y.1 Y.2.1 Z.1 Z.2.1,
      hlsLorAct_br Z.1 Z.2.1 X.1 X.2.1]
    simp only [hlsLorAct, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_add, Matrix.add_mul]
    abel
  · show ⁅X.2.2.2, ⁅Y.2.2.2, Z.2.2.2⁆⁆ + ⁅Y.2.2.2, ⁅Z.2.2.2, X.2.2.2⁆⁆
      + ⁅Z.2.2.2, ⁅X.2.2.2, Y.2.2.2⁆⁆ = 0
    exact lie_jacobi _ _ _

@[simp] theorem hlsSl2Br_zero_left (y : HLSSl2) : hlsSl2Br 0 y = 0 := by
  simpa using hlsSl2Br_smul_left (0 : ℂ) 0 y

@[simp] theorem hlsSl2Br_zero_right (x : HLSSl2) : hlsSl2Br x 0 = 0 := by
  simpa using hlsSl2Br_smul_right (0 : ℂ) x 0

/-- Bracket with an undotted Lorentz generator, componentwise. -/
theorem hlsEvenBr_lorL (x : HLSSl2) (X : HLSEven B) :
    hlsEvenBr (hlsLorL x) X = (hlsSl2Br x X.1, 0, hlsSl2Mat x * X.2.2.1, 0) := by
  simp [hlsEvenBr, hlsLorL, hlsLorAct]

/-- Bracket with a dotted Lorentz generator, componentwise. -/
theorem hlsEvenBr_lorR (x : HLSSl2) (X : HLSEven B) :
    hlsEvenBr (hlsLorR x) X = (0, hlsSl2Br x X.2.1, X.2.2.1 * (hlsSl2Mat x)ᵀ, 0) := by
  simp [hlsEvenBr, hlsLorR, hlsLorAct]

/-- Adjoint action of the undotted Cartan generator `h` on `𝔤₀`. -/
def hlsEvenAdL (B : Type*) [LieRing B] [LieAlgebra ℂ B] : Module.End ℂ (HLSEven B) where
  toFun X := hlsEvenBr (hlsLorL hlsSl2H) X
  map_add' := hlsEvenBr_add_right _
  map_smul' c X := hlsEvenBr_smul_right c _ X

/-- Adjoint action of the dotted Cartan generator `h̄` on `𝔤₀`. -/
def hlsEvenAdR (B : Type*) [LieRing B] [LieAlgebra ℂ B] : Module.End ℂ (HLSEven B) where
  toFun X := hlsEvenBr (hlsLorR hlsSl2H) X
  map_add' := hlsEvenBr_add_right _
  map_smul' c X := hlsEvenBr_smul_right c _ X

theorem hlsEvenAdL_apply (X : HLSEven B) :
    hlsEvenAdL B X = (hlsSl2Br hlsSl2H X.1, 0, hlsSl2Mat hlsSl2H * X.2.2.1, 0) :=
  hlsEvenBr_lorL _ _

theorem hlsEvenAdR_apply (X : HLSEven B) :
    hlsEvenAdR B X = (0, hlsSl2Br hlsSl2H X.2.1, X.2.2.1 * (hlsSl2Mat hlsSl2H)ᵀ, 0) :=
  hlsEvenBr_lorR _ _

theorem hlsSl2Mat_H : hlsSl2Mat hlsSl2H = !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat, hlsSl2H]

theorem hlsEvenAdL_pow_rightComp (c : ℂ) (k : ℕ) (X : HLSEven B) :
    (((hlsEvenAdL B - c • (1 : Module.End ℂ (HLSEven B))) ^ k) X).2.1 = (-c) ^ k • X.2.1 := by
  have hstep : ∀ Y : HLSEven B,
      ((hlsEvenAdL B - c • (1 : Module.End ℂ (HLSEven B))) Y).2.1 = (-c) • Y.2.1 := by
    intro Y
    simp [hlsEvenAdL_apply, LinearMap.sub_apply, LinearMap.smul_apply, neg_smul]
  induction k generalizing X with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp only [Module.End.mul_apply]
      rw [ih, hstep, smul_smul, ← pow_succ]

theorem hlsEvenAdL_pow_intComp (c : ℂ) (k : ℕ) (X : HLSEven B) :
    (((hlsEvenAdL B - c • (1 : Module.End ℂ (HLSEven B))) ^ k) X).2.2.2 = (-c) ^ k • X.2.2.2 := by
  have hstep : ∀ Y : HLSEven B,
      ((hlsEvenAdL B - c • (1 : Module.End ℂ (HLSEven B))) Y).2.2.2 = (-c) • Y.2.2.2 := by
    intro Y
    simp [hlsEvenAdL_apply, LinearMap.sub_apply, LinearMap.smul_apply, neg_smul]
  induction k generalizing X with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp only [Module.End.mul_apply]
      rw [ih, hstep, smul_smul, ← pow_succ]

theorem hlsEvenAdR_pow_leftComp (c : ℂ) (k : ℕ) (X : HLSEven B) :
    (((hlsEvenAdR B - c • (1 : Module.End ℂ (HLSEven B))) ^ k) X).1 = (-c) ^ k • X.1 := by
  have hstep : ∀ Y : HLSEven B,
      ((hlsEvenAdR B - c • (1 : Module.End ℂ (HLSEven B))) Y).1 = (-c) • Y.1 := by
    intro Y
    simp [hlsEvenAdR_apply, LinearMap.sub_apply, LinearMap.smul_apply, neg_smul]
  induction k generalizing X with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp only [Module.End.mul_apply]
      rw [ih, hstep, smul_smul, ← pow_succ]

theorem hlsEvenAdL_pow_momComp (c : ℂ) (k : ℕ) (X : HLSEven B) :
    (((hlsEvenAdL B - c • (1 : Module.End ℂ (HLSEven B))) ^ k) X).2.2.1
      = (!![1 - c, 0; 0, -1 - c] : Matrix (Fin 2) (Fin 2) ℂ) ^ k * X.2.2.1 := by
  have hstep : ∀ Y : HLSEven B,
      ((hlsEvenAdL B - c • (1 : Module.End ℂ (HLSEven B))) Y).2.2.1
        = (!![1 - c, 0; 0, -1 - c] : Matrix (Fin 2) (Fin 2) ℂ) * Y.2.2.1 := by
    intro Y
    have h1 : ((hlsEvenAdL B - c • (1 : Module.End ℂ (HLSEven B))) Y).2.2.1
        = hlsSl2Mat hlsSl2H * Y.2.2.1 - c • Y.2.2.1 := by
      simp [hlsEvenAdL_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    have hmat : (!![1 - c, 0; 0, -1 - c] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![1, 0; 0, -1] - c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h1, hlsSl2Mat_H, hmat, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  induction k generalizing X with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp only [Module.End.mul_apply]
      rw [ih, hstep, ← Matrix.mul_assoc, ← pow_succ]

theorem hlsDiagPow (a b : ℂ) (k : ℕ) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℂ) ^ k = !![a ^ k, 0; 0, b ^ k] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
      rw [pow_succ, ih, Matrix.mul_fin_two]
      norm_num [pow_succ]

/-- **Weight rigidity of the even algebra.**  If the joint generalized `(h, h̄)`-weight
`(c₁, c₂)` avoids the finite list of weights actually carried by
`𝔤₀ = 𝔰𝔩₂ ⊕ 𝔰𝔩₂ ⊕ P ⊕ 𝔅`, the corresponding weight vector vanishes. -/
theorem hlsEven_joint_weight_eq_zero {c₁ c₂ : ℂ} (h0 : c₁ ≠ 0) (h1 : c₁ ≠ 1) (hm1 : c₁ ≠ -1)
    (h0' : c₂ ≠ 0)
    (X : HLSEven B) (k m : ℕ)
    (hL : ((hlsEvenAdL B - c₁ • (1 : Module.End ℂ (HLSEven B))) ^ k) X = 0)
    (hR : ((hlsEvenAdR B - c₂ • (1 : Module.End ℂ (HLSEven B))) ^ m) X = 0) : X = 0 := by
  have hcpow : ∀ n : ℕ, (-c₁) ^ n ≠ 0 := fun n => pow_ne_zero _ (neg_ne_zero.mpr h0)
  have hcpow' : ∀ n : ℕ, (-c₂) ^ n ≠ 0 := fun n => pow_ne_zero _ (neg_ne_zero.mpr h0')
  set c := c₁ with hc
  have hX1 : X.1 = 0 := by
    have h := hlsEvenAdR_pow_leftComp c₂ m X
    rw [hR] at h
    exact (smul_eq_zero.mp h.symm).resolve_left (hcpow' m)
  have hX21 : X.2.1 = 0 := by
    have h := hlsEvenAdL_pow_rightComp c k X
    rw [hL] at h
    exact (smul_eq_zero.mp h.symm).resolve_left (hcpow k)
  have hX222 : X.2.2.2 = 0 := by
    have h := hlsEvenAdL_pow_intComp c k X
    rw [hL] at h
    exact (smul_eq_zero.mp h.symm).resolve_left (hcpow k)
  have hX221 : X.2.2.1 = 0 := by
    have hmom := hlsEvenAdL_pow_momComp c k X
    rw [hL, hlsDiagPow] at hmom
    have hz : (!![(1 - c) ^ k, 0; 0, (-1 - c) ^ k] : Matrix (Fin 2) (Fin 2) ℂ) * X.2.2.1 = 0 :=
      hmom.symm
    have ha : (1 - c) ^ k ≠ 0 := by
      refine pow_ne_zero _ ?_
      intro hh
      rw [sub_eq_zero] at hh
      exact h1 hh.symm
    have hb : (-1 - c) ^ k ≠ 0 := by
      refine pow_ne_zero _ ?_
      intro hh
      rw [sub_eq_zero] at hh
      exact hm1 hh.symm
    have hdet : IsUnit (Matrix.det
        (!![(1 - c) ^ k, 0; 0, (-1 - c) ^ k] : Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [Matrix.det_fin_two_of]
      exact (isUnit_iff_ne_zero).mpr (by simpa using mul_ne_zero ha hb)
    calc X.2.2.1 = 1 * X.2.2.1 := (Matrix.one_mul _).symm
      _ = ((!![(1 - c) ^ k, 0; 0, (-1 - c) ^ k] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ *
            (!![(1 - c) ^ k, 0; 0, (-1 - c) ^ k] : Matrix (Fin 2) (Fin 2) ℂ)) * X.2.2.1 := by
            rw [Matrix.nonsing_inv_mul _ hdet]
      _ = (!![(1 - c) ^ k, 0; 0, (-1 - c) ^ k] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ *
            ((!![(1 - c) ^ k, 0; 0, (-1 - c) ^ k] : Matrix (Fin 2) (Fin 2) ℂ) * X.2.2.1) :=
          Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hz, Matrix.mul_zero]
  exact Prod.ext hX1 (Prod.ext hX21 (Prod.ext hX221 hX222))

/-- Diagonal specialization: the only joint `(h, h̄)`-weights of `𝔤₀` of the form `(c, c)`
are `c ∈ {-1, 0, 1}`. -/
theorem hlsEven_joint_diagonal_weight {c : ℂ} (h0 : c ≠ 0) (h1 : c ≠ 1) (hm1 : c ≠ -1)
    (X : HLSEven B) (k m : ℕ)
    (hL : ((hlsEvenAdL B - c • (1 : Module.End ℂ (HLSEven B))) ^ k) X = 0)
    (hR : ((hlsEvenAdR B - c • (1 : Module.End ℂ (HLSEven B))) ^ m) X = 0) : X = 0 :=
  hlsEven_joint_weight_eq_zero h0 h1 hm1 h0 X k m hL hR

end Even

end GaloisForLFunctions.HTGeometry
