import GaloisForLFunctions.HTGeometry.RotationInducedArithmeticModule
import GaloisForLFunctions.HTGeometry.TraceDerivationCyclicCocycleLaw
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The actual canonical rotation two-cocycle

Directional Euler derivations are constructed on the concrete finite Weyl
algebra using its independent word basis. They obey Leibniz, commute, and
are annihilated by the constructed canonical trace. The antisymmetrized
trace cochain therefore has actual cyclic symmetry and zero Hochschild
boundary. Scalar linearity is proved in every slot.

Two explicit Weyl triples form a quantum Hochschild cycle. Their pairing
is nonzero, proving this cochain is not a Hochschild coboundary. Scalar
arguments give zero; the nonzero class retains the clock through the
quantum commutator cycle. This is an unnormalized Euler cocycle, not an
asserted integer Chern coordinate or a constructed arithmetic K0 lift.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped Classical TensorProduct

section General
variable {A K : Type*} [Ring A] [AddCommGroup K]

/-- The antisymmetrized two-derivation trace cochain. -/
def traceDerivTwoCocycle (τ : A →+ K) (D E : A →+ A) (a b c : A) : K :=
  τ (a * (D b * E c - E b * D c))

theorem traceDerivTwoCocycle_add_left (τ : A →+ K) (D E : A →+ A) (a a' b c : A) :
    traceDerivTwoCocycle τ D E (a + a') b c =
      traceDerivTwoCocycle τ D E a b c + traceDerivTwoCocycle τ D E a' b c := by
  simp [traceDerivTwoCocycle, add_mul]

theorem traceDerivTwoCocycle_add_middle (τ : A →+ K) (D E : A →+ A) (a b b' c : A) :
    traceDerivTwoCocycle τ D E a (b + b') c =
      traceDerivTwoCocycle τ D E a b c + traceDerivTwoCocycle τ D E a b' c := by
  simp [traceDerivTwoCocycle, add_mul, mul_add, add_sub_add_comm]

theorem traceDerivTwoCocycle_add_right (τ : A →+ K) (D E : A →+ A) (a b c c' : A) :
    traceDerivTwoCocycle τ D E a b (c + c') =
      traceDerivTwoCocycle τ D E a b c + traceDerivTwoCocycle τ D E a b c' := by
  simp [traceDerivTwoCocycle, mul_add, add_sub_add_comm]

/-- The Hochschild boundary vanishes by the Leibniz rules and cyclicity of the trace. -/
theorem traceDerivTwoCocycle_boundary (τ : A →+ K) (D E : A →+ A)
    (hτ : IsAlgebraTrace τ) (hD : IsAlgebraDerivation D) (hE : IsAlgebraDerivation E)
    (a b c d : A) :
    traceDerivTwoCocycle τ D E (a * b) c d - traceDerivTwoCocycle τ D E a (b * c) d +
      traceDerivTwoCocycle τ D E a b (c * d) - traceDerivTwoCocycle τ D E (d * a) b c = 0 := by
  have hring : (a * b) * (D c * E d - E c * D d) -
      a * (D (b * c) * E d - E (b * c) * D d) +
      a * (D b * E (c * d) - E b * D (c * d)) =
      (a * (D b * E c - E b * D c)) * d := by
    rw [hD b c, hE b c, hD c d, hE c d]
    noncomm_ring
  simp only [traceDerivTwoCocycle, ← map_sub, ← map_add]
  rw [hring, map_sub, hτ, mul_assoc, sub_self]

/-- Commuting trace-annihilated derivations give the actual cyclic symmetry. -/
theorem traceDerivTwoCocycle_cyclic (τ : A →+ K) (D E : A →+ A)
    (hτ : IsAlgebraTrace τ) (hD : IsAlgebraDerivation D) (hE : IsAlgebraDerivation E)
    (hτD : ∀ a, τ (D a) = 0) (hτE : ∀ a, τ (E a) = 0)
    (hDE : ∀ a, D (E a) = E (D a)) (a b c : A) :
    traceDerivTwoCocycle τ D E a b c = traceDerivTwoCocycle τ D E b c a := by
  have hring : a * (D b * E c - E b * D c) =
      a * D (b * E c) - a * E (b * D c) := by
    rw [hD b (E c), hE b (D c), hDE c]
    noncomm_ring
  have hd := traceDerivCocycle_antisymm hτ hD hτD a (b * E c)
  have he := traceDerivCocycle_antisymm hτ hE hτE a (b * D c)
  simp only [traceDerivCocycle] at hd he
  rw [traceDerivTwoCocycle, hring, map_sub, hd, he]
  simp only [traceDerivTwoCocycle, mul_sub, map_sub, mul_assoc]
  abel
end General

section Rotation
variable (t : ℝ) (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)

/-- Directional Euler derivation on the actual concrete finite Weyl algebra. -/
def paperRotationEulerDerivation (u v : ℂ) :
    paperRotationPolynomialAlgebra t →ₗ[ℂ] paperRotationPolynomialAlgebra t :=
  (Finsupp.linearCombination ℂ (fun ab : ℤ × ℤ =>
    ((ab.1 : ℂ) * u + (ab.2 : ℂ) * v) • paperRotationPolynomialWord t ab.1 ab.2)).comp
      (paperRotationWords_linearIndependent t ht).repr

@[simp] theorem paperRotationEulerDerivation_word (u v : ℂ) (a b : ℤ) :
    paperRotationEulerDerivation t ht u v (paperRotationPolynomialWord t a b) =
      ((a : ℂ) * u + (b : ℂ) * v) • paperRotationPolynomialWord t a b := by
  change Finsupp.linearCombination ℂ _
    ((paperRotationWords_linearIndependent t ht).repr (paperRotationPolynomialWord t a b)) = _
  rw [(paperRotationWords_linearIndependent t ht).repr_eq_single (a, b) _ rfl,
    Finsupp.linearCombination_single, one_smul]

/-- The quantum multiplier is respected exactly by both coordinate derivations. -/
theorem paperRotationEulerDerivation_mul (u v : ℂ) (X Y : paperRotationPolynomialAlgebra t) :
    paperRotationEulerDerivation t ht u v (X * Y) =
      paperRotationEulerDerivation t ht u v X * Y + X * paperRotationEulerDerivation t ht u v Y := by
  induction X using paperRotationPolynomial_induction t with
  | hword a b =>
    induction Y using paperRotationPolynomial_induction t with
    | hword d e =>
      simp only [paperRotationPolynomialWord_mul, map_smul, paperRotationEulerDerivation_word,
        smul_mul_assoc, mul_smul_comm, smul_smul, ← add_smul]
      congr 1
      push_cast
      ring
    | hzero => simp
    | hadd Y Z hY hZ => simp only [mul_add, map_add, hY, hZ]; abel
    | hsmul z Y hY => simp only [mul_smul_comm, map_smul, hY, smul_add]
  | hzero => simp
  | hadd X Z hX hZ => simp only [add_mul, map_add, hX, hZ]; abel
  | hsmul z X hX => simp only [smul_mul_assoc, map_smul, hX, smul_add]

/-- Both Euler directions commute on every actual finite operator, not merely on coordinates. -/
theorem paperRotationEulerDerivation_commute (u v r s : ℂ) (X : paperRotationPolynomialAlgebra t) :
    paperRotationEulerDerivation t ht u v (paperRotationEulerDerivation t ht r s X) =
      paperRotationEulerDerivation t ht r s (paperRotationEulerDerivation t ht u v X) := by
  induction X using paperRotationPolynomial_induction t with
  | hword a b => simp only [paperRotationEulerDerivation_word, map_smul, smul_smul, mul_comm]
  | hzero => simp
  | hadd X Y hX hY => simp only [map_add, hX, hY]
  | hsmul z X hX => simp only [map_smul, hX]

/-- Restriction of the constructed bounded canonical trace to the concrete finite algebra. -/
def paperRotationPolynomialTrace : paperRotationPolynomialAlgebra t →ₗ[ℂ] ℂ where
  toFun X := paperRotationTrace X.val
  map_add' X Y := map_add paperRotationTrace X.val Y.val
  map_smul' z X := map_smul paperRotationTrace z X.val

@[simp] theorem paperRotationPolynomialTrace_one : paperRotationPolynomialTrace t 1 = 1 := by
  change paperRotationTrace 1 = 1
  exact paperRotationTrace_one

include ht in
@[simp] theorem paperRotationPolynomialTrace_word (a b : ℤ) :
    paperRotationPolynomialTrace t (paperRotationPolynomialWord t a b) =
      if a = 0 ∧ b = 0 then 1 else 0 := paperRotationTrace_integer_word t ht a b

include ht in
theorem paperRotationPolynomialTrace_cyclic (X Y : paperRotationPolynomialAlgebra t) :
    paperRotationPolynomialTrace t (X * Y) = paperRotationPolynomialTrace t (Y * X) := by
  change paperRotationTrace (X * Y).val = paperRotationTrace (Y * X).val
  rw [← paperRotationPolynomialLift_trace t ht, ← paperRotationPolynomialLift_trace t ht,
    map_mul (paperRotationPolynomialLift t ht) X Y, map_mul (paperRotationPolynomialLift t ht) Y X,
    quantumLaurentTrace_cyclic]

/-- Integration by parts comes from the actual canonical constant coefficient. -/
theorem paperRotationPolynomialTrace_derivation (u v : ℂ) (X : paperRotationPolynomialAlgebra t) :
    paperRotationPolynomialTrace t (paperRotationEulerDerivation t ht u v X) = 0 := by
  induction X using paperRotationPolynomial_induction t with
  | hword a b =>
    rw [paperRotationEulerDerivation_word, map_smul, paperRotationPolynomialTrace_word t ht]
    by_cases h : a = 0 ∧ b = 0
    · rcases h with ⟨rfl, rfl⟩; simp
    · simp [h]
  | hzero => simp
  | hadd X Y hX hY => simp only [map_add, hX, hY, add_zero]
  | hsmul z X hX => simp only [map_smul, hX, smul_zero]

/-- The canonical rotation two-cocycle, computed from actual operators and their two derivations. -/
def paperRotationCyclicTwoCocycle (X Y Z : paperRotationPolynomialAlgebra t) : ℂ :=
  traceDerivTwoCocycle (paperRotationPolynomialTrace t).toAddMonoidHom
    (paperRotationEulerDerivation t ht 1 0).toAddMonoidHom
    (paperRotationEulerDerivation t ht 0 1).toAddMonoidHom X Y Z

theorem paperRotationCyclicTwoCocycle_cyclic (X Y Z : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht X Y Z = paperRotationCyclicTwoCocycle t ht Y Z X :=
  traceDerivTwoCocycle_cyclic (paperRotationPolynomialTrace t).toAddMonoidHom
    (paperRotationEulerDerivation t ht 1 0).toAddMonoidHom
    (paperRotationEulerDerivation t ht 0 1).toAddMonoidHom
    (paperRotationPolynomialTrace_cyclic t ht)
    (paperRotationEulerDerivation_mul t ht 1 0) (paperRotationEulerDerivation_mul t ht 0 1)
    (paperRotationPolynomialTrace_derivation t ht 1 0)
    (paperRotationPolynomialTrace_derivation t ht 0 1)
    (paperRotationEulerDerivation_commute t ht 1 0 0 1) X Y Z

theorem paperRotationCyclicTwoCocycle_boundary (W X Y Z : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht (W * X) Y Z -
      paperRotationCyclicTwoCocycle t ht W (X * Y) Z +
      paperRotationCyclicTwoCocycle t ht W X (Y * Z) -
      paperRotationCyclicTwoCocycle t ht (Z * W) X Y = 0 :=
  traceDerivTwoCocycle_boundary (paperRotationPolynomialTrace t).toAddMonoidHom
    (paperRotationEulerDerivation t ht 1 0).toAddMonoidHom
    (paperRotationEulerDerivation t ht 0 1).toAddMonoidHom
    (paperRotationPolynomialTrace_cyclic t ht)
    (paperRotationEulerDerivation_mul t ht 1 0) (paperRotationEulerDerivation_mul t ht 0 1) W X Y Z

/-- The actual tensor-valued Hochschild boundary of a pure degree-two chain. -/
def rotationHochschildBoundary (X Y Z : paperRotationPolynomialAlgebra t) :
    paperRotationPolynomialAlgebra t ⊗[ℂ] paperRotationPolynomialAlgebra t :=
  (X * Y) ⊗ₜ[ℂ] Z - X ⊗ₜ[ℂ] (Y * Z) + (Z * X) ⊗ₜ[ℂ] Y

theorem paperRotationCyclicTwoCocycle_smul_left (z : ℂ)
    (X Y Z : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht (z • X) Y Z = z * paperRotationCyclicTwoCocycle t ht X Y Z := by
  change paperRotationPolynomialTrace t ((z • X) * _) = _
  rw [smul_mul_assoc, map_smul]
  rfl

theorem paperRotationCyclicTwoCocycle_smul_middle (z : ℂ)
    (X Y Z : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht X (z • Y) Z = z * paperRotationCyclicTwoCocycle t ht X Y Z := by
  change paperRotationPolynomialTrace t (X *
    (paperRotationEulerDerivation t ht 1 0 (z • Y) * paperRotationEulerDerivation t ht 0 1 Z -
     paperRotationEulerDerivation t ht 0 1 (z • Y) * paperRotationEulerDerivation t ht 1 0 Z)) = _
  simp only [map_smul, smul_mul_assoc, ← smul_sub, mul_smul_comm]
  rfl

theorem paperRotationCyclicTwoCocycle_smul_right (z : ℂ)
    (X Y Z : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht X Y (z • Z) = z * paperRotationCyclicTwoCocycle t ht X Y Z := by
  change paperRotationPolynomialTrace t (X *
    (paperRotationEulerDerivation t ht 1 0 Y * paperRotationEulerDerivation t ht 0 1 (z • Z) -
     paperRotationEulerDerivation t ht 0 1 Y * paperRotationEulerDerivation t ht 1 0 (z • Z))) = _
  simp only [map_smul, mul_smul_comm, ← smul_sub]
  rfl

/-- The oriented fundamental Weyl triple has nonzero cyclic value. -/
theorem paperRotationCyclicTwoCocycle_fundamental :
    paperRotationCyclicTwoCocycle t ht (paperRotationPolynomialWord t (-1) (-1))
      (paperRotationPolynomialWord t 1 0) (paperRotationPolynomialWord t 0 1) = 1 := by
  simp [paperRotationCyclicTwoCocycle, traceDerivTwoCocycle,
    paperRotationEulerDerivation_word, paperRotationPolynomialWord_mul]

/-- Reversing the two directions records the actual inverse quantum multiplier. -/
theorem paperRotationCyclicTwoCocycle_fundamental_reverse :
    paperRotationCyclicTwoCocycle t ht (paperRotationPolynomialWord t (-1) (-1))
      (paperRotationPolynomialWord t 0 1) (paperRotationPolynomialWord t 1 0) =
        -((paperRotationQuantumUnit t : ℂ)⁻¹) := by
  simp [paperRotationCyclicTwoCocycle, traceDerivTwoCocycle,
    paperRotationEulerDerivation_word, paperRotationPolynomialWord_mul]

/-- The two explicit Weyl triples form a genuine quantum Hochschild cycle. -/
theorem rotationHochschildBoundary_fundamental :
    rotationHochschildBoundary t (paperRotationPolynomialWord t (-1) (-1))
      (paperRotationPolynomialWord t 1 0) (paperRotationPolynomialWord t 0 1) =
      (paperRotationQuantumUnit t : ℂ) •
        rotationHochschildBoundary t (paperRotationPolynomialWord t (-1) (-1))
          (paperRotationPolynomialWord t 0 1) (paperRotationPolynomialWord t 1 0) := by
  simp only [rotationHochschildBoundary, paperRotationPolynomialWord_mul]
  simp only [mul_zero, mul_one, one_mul, zero_mul, zero_add, add_zero,
    neg_add_cancel, add_neg_cancel, zpow_zero, zpow_one, zpow_neg_one,
    Units.val_one, one_smul, Units.val_inv_eq_inv_val]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_sub, smul_add, smul_smul,
    mul_inv_cancel₀ (paperRotationQuantumUnit t).ne_zero, one_smul]
  abel

/-- The actual canonical rotation cocycle is not a Hochschild coboundary. -/
theorem paperRotationCyclicTwoCocycle_not_coboundary :
    ¬ ∃ L : (paperRotationPolynomialAlgebra t ⊗[ℂ] paperRotationPolynomialAlgebra t) →ₗ[ℂ] ℂ,
      ∀ X Y Z, paperRotationCyclicTwoCocycle t ht X Y Z = L (rotationHochschildBoundary t X Y Z) := by
  rintro ⟨L, hL⟩
  have hf := hL (paperRotationPolynomialWord t (-1) (-1))
    (paperRotationPolynomialWord t 1 0) (paperRotationPolynomialWord t 0 1)
  rw [paperRotationCyclicTwoCocycle_fundamental, rotationHochschildBoundary_fundamental,
    map_smul] at hf
  rw [← hL, paperRotationCyclicTwoCocycle_fundamental_reverse] at hf
  have hm : (1 : ℂ) = -1 := by
    simpa only [smul_eq_mul, mul_neg, mul_inv_cancel₀ (paperRotationQuantumUnit t).ne_zero] using hf
  norm_num at hm

@[simp] theorem paperRotationEulerDerivation_one (u v : ℂ) :
    paperRotationEulerDerivation t ht u v 1 = 0 := by
  rw [← paperRotationPolynomialWord_zero t, paperRotationEulerDerivation_word]
  simp

@[simp] theorem paperRotationCyclicTwoCocycle_one_right (X Y : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht X Y 1 = 0 := by
  simp [paperRotationCyclicTwoCocycle, traceDerivTwoCocycle]

/-- A scalar clock inserted directly into the cyclic cochain carries no two-dimensional charge. -/
theorem paperRotationCyclicTwoCocycle_scalar_left (z : ℂ) (Y Z : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht (z • 1) Y Z = 0 := by
  rw [paperRotationCyclicTwoCocycle_smul_left, paperRotationCyclicTwoCocycle_cyclic,
    paperRotationCyclicTwoCocycle_one_right, mul_zero]

theorem paperRotationCyclicTwoCocycle_scalar_middle (z : ℂ) (X Z : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht X (z • 1) Z = 0 := by
  rw [paperRotationCyclicTwoCocycle_cyclic, paperRotationCyclicTwoCocycle_scalar_left]

theorem paperRotationCyclicTwoCocycle_scalar_right (z : ℂ) (X Y : paperRotationPolynomialAlgebra t) :
    paperRotationCyclicTwoCocycle t ht X Y (z • 1) = 0 := by
  rw [paperRotationCyclicTwoCocycle_smul_right, paperRotationCyclicTwoCocycle_one_right, mul_zero]

end Rotation
end
end GaloisForLFunctions.HTGeometry
