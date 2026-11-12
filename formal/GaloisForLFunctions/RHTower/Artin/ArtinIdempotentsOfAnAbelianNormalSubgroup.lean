import GaloisForLFunctions.RHTower.Artin.ArtinRangeOfACommutingIdempotent
import GaloisForLFunctions.RHTower.Artin.ArtinFiniteAbelianFourier

/-!
# The idempotents of an abelian normal subgroup

Let `A` be an abelian normal subgroup of a finite group `E` and `ρ` a representation of `E` on
`V`. The group acts on the linear characters of `A` by `(g • χ)(a) = χ(g⁻¹ a g)`
(`conjCharacterAction`). For a linear character `χ` of `A` put

  `e_χ = (1/|A|) Σ_{a ∈ A} χ(a⁻¹) ρ(a)`   (`isotypicProjector`).

* `ρ(b) e_χ = χ(b) e_χ` for `b ∈ A` (`apply_mul_isotypicProjector`);
* `e_χ e_ψ = δ_{χψ} e_ψ` (`isotypicProjector_mul`) and `Σ_χ e_χ = 1`
  (`sum_isotypicProjector`), by the two orthogonality relations of the characters of `A`;
* `ρ(g) e_χ ρ(g)⁻¹ = e_{g • χ}` (`apply_mul_isotypicProjector_mul_apply_inv`).

For the functions `F_χ(g) = tr(ρ(g) e_χ)` (`isotypicTrace`):

* `Σ_χ F_χ` is the character of `ρ` (`sum_isotypicTrace`);
* `F_χ(g) = 0` unless `g` fixes `χ` (`isotypicTrace_eq_zero`):
  `tr(ρ(g) e_χ) = tr(e_{gχ} ρ(g) e_χ) = tr(ρ(g) e_χ e_{gχ})`;
* `F_χ(x g x⁻¹) = F_{x⁻¹ • χ}(g)` (`isotypicTrace_conj`);
* on the stabilizer of `χ`, `F_χ` is a character: the character of the stabilizer on the range
  of `e_χ` (`isotypicTrace_mem_fdCharacterSet_stabilizer`).
-/

open scoped Classical BigOperators IsMulCommutative

noncomputable section

universe u w

namespace GaloisForLFunctions

attribute [local instance] finiteLinearCharacter fintypeLinearCharacter

/-! ### The second orthogonality relation -/

/-- `Σ_χ χ(a) = |B|` if `a = 1`, and `0` otherwise, for a finite abelian group `B`. -/
theorem sum_linearCharacter_apply {B : Type u} [CommGroup B] [Fintype B] (a : B) :
    ∑ χ : LinearCharacter B, ((χ a : ℂˣ) : ℂ) = if a = 1 then (Nat.card B : ℂ) else 0 := by
  have hcard : (Nat.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- the Fourier coefficients of the indicator of `1` are `1/|B|`
  have hcoeff : ∀ χ : LinearCharacter B, characterPairing B (RHTower.deningerCharacterFn χ)
      (fun b => if b = 1 then (1 : ℂ) else 0) = (Nat.card B : ℂ)⁻¹ := by
    intro χ
    rw [characterPairing]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [inv_one, RHTower.deningerCharacterFn_apply, map_one, Units.val_one, mul_one]
  have h := congrFun
    (finiteAbelian_fourier_reconstruction (fun b : B => if b = 1 then (1 : ℂ) else 0)) a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcoeff,
    RHTower.deningerCharacterFn_apply, ← Finset.mul_sum] at h
  rw [inv_mul_eq_iff_eq_mul₀ hcard] at h
  rw [h, mul_ite, mul_one, mul_zero]

/-! ### The action on the characters and the idempotents -/

variable {E : Type u} [Group E] [Fintype E] (A : Subgroup E) [A.Normal] [IsMulCommutative A]
  {V : Type w} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ E V)

omit [Fintype E] [IsMulCommutative A] in
/-- Conjugation by `g` and by `g⁻¹` on a normal subgroup are inverse to each other. -/
theorem conjNormal_inv_conjNormal_inv (g : E) (a : A) :
    MulAut.conjNormal g⁻¹ ((MulAut.conjNormal g a)⁻¹) = a⁻¹ := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, Subgroup.coe_inv, MulAut.conjNormal_apply, Subgroup.coe_inv]
  group

/-- The action of the group on the linear characters of a normal subgroup:
`(g • χ)(a) = χ(g⁻¹ a g)`. -/
def conjCharacterAction : MulAction E (LinearCharacter A) where
  smul g χ := χ.comp (MulAut.conjNormal g⁻¹ : A ≃* A).toMonoidHom
  one_smul χ := by
    refine MonoidHom.ext fun a => ?_
    show χ (MulAut.conjNormal (1 : E)⁻¹ a) = χ a
    rw [inv_one, map_one]
    rfl
  mul_smul g h χ := by
    refine MonoidHom.ext fun a => ?_
    show χ (MulAut.conjNormal (g * h)⁻¹ a) =
      χ (MulAut.conjNormal h⁻¹ (MulAut.conjNormal g⁻¹ a))
    rw [mul_inv_rev, map_mul]
    rfl

attribute [local instance] conjCharacterAction

omit [Fintype E] [IsMulCommutative A] in
theorem conjCharacter_apply (g : E) (χ : LinearCharacter A) (a : A) :
    (g • χ) a = χ (MulAut.conjNormal g⁻¹ a) :=
  rfl

/-- The idempotent of a linear character `χ` of `A`: `e_χ = (1/|A|) Σ_a χ(a⁻¹) ρ(a)`. -/
def isotypicProjector (χ : LinearCharacter A) : Module.End ℂ V :=
  (Nat.card A : ℂ)⁻¹ • ∑ a : A, ((χ a⁻¹ : ℂˣ) : ℂ) • ρ (a : E)

/-- `ρ(b) e_χ = χ(b) e_χ` for `b` in `A`. -/
theorem apply_mul_isotypicProjector (χ : LinearCharacter A) (b : A) :
    ρ (b : E) * isotypicProjector A ρ χ = ((χ b : ℂˣ) : ℂ) • isotypicProjector A ρ χ := by
  have hsum : ρ (b : E) * ∑ a : A, ((χ a⁻¹ : ℂˣ) : ℂ) • ρ (a : E) =
      ((χ b : ℂˣ) : ℂ) • ∑ a : A, ((χ a⁻¹ : ℂˣ) : ℂ) • ρ (a : E) := by
    rw [Finset.mul_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft b)
      fun a : A => ((χ b : ℂˣ) : ℂ) • (((χ a⁻¹ : ℂˣ) : ℂ) • ρ (a : E))]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hval : ((χ b : ℂˣ) : ℂ) * ((χ (b * a)⁻¹ : ℂˣ) : ℂ) = ((χ a⁻¹ : ℂˣ) : ℂ) := by
      rw [← Units.val_mul, ← map_mul, show b * (b * a)⁻¹ = a⁻¹ by
        rw [mul_inv_rev, mul_comm' a⁻¹, mul_inv_cancel_left]]
    show ρ (b : E) * (((χ a⁻¹ : ℂˣ) : ℂ) • ρ (a : E)) =
      ((χ b : ℂˣ) : ℂ) • (((χ (b * a)⁻¹ : ℂˣ) : ℂ) • ρ ((b * a : A) : E))
    rw [smul_smul, hval, mul_smul_comm, ← map_mul]
    rfl
  rw [isotypicProjector, mul_smul_comm, hsum, smul_comm]

/-- **Orthogonality**: `e_χ e_ψ = e_ψ` if `χ = ψ` and `0` otherwise. -/
theorem isotypicProjector_mul (χ ψ : LinearCharacter A) :
    isotypicProjector A ρ χ * isotypicProjector A ρ ψ =
      if χ = ψ then isotypicProjector A ρ ψ else 0 := by
  have hχ : isotypicProjector A ρ χ =
      (Nat.card A : ℂ)⁻¹ • ∑ a : A, ((χ a⁻¹ : ℂˣ) : ℂ) • ρ (a : E) := rfl
  have h : isotypicProjector A ρ χ * isotypicProjector A ρ ψ =
      characterPairing A (RHTower.deningerCharacterFn χ) (RHTower.deningerCharacterFn ψ) •
        isotypicProjector A ρ ψ := by
    rw [hχ, smul_mul_assoc, Finset.sum_mul, characterPairing, mul_smul, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_mul_assoc, apply_mul_isotypicProjector, smul_smul, mul_comm]
    rfl
  rw [h, linearCharacterPairing_orthonormal]
  by_cases hχψ : χ = ψ
  · rw [if_pos hχψ, if_pos hχψ, one_smul]
  · rw [if_neg hχψ, if_neg hχψ, zero_smul]

/-- **Completeness**: `Σ_χ e_χ = 1`. -/
theorem sum_isotypicProjector : ∑ χ : LinearCharacter A, isotypicProjector A ρ χ = 1 := by
  have hcard : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hterm : ∀ a : A, ∑ χ : LinearCharacter A, ((χ a⁻¹ : ℂˣ) : ℂ) • ρ (a : E) =
      if a = 1 then (Nat.card A : ℂ) • (1 : Module.End ℂ V) else 0 := by
    intro a
    rw [← Finset.sum_smul, sum_linearCharacter_apply, inv_eq_one]
    by_cases ha : a = 1
    · rw [if_pos ha, if_pos ha, ha, OneMemClass.coe_one, map_one]
    · rw [if_neg ha, if_neg ha, zero_smul]
  simp only [isotypicProjector]
  rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun a _ => hterm a,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- **Conjugation**: `ρ(g) e_χ ρ(g)⁻¹ = e_{g • χ}`. -/
theorem apply_mul_isotypicProjector_mul_apply_inv (g : E) (χ : LinearCharacter A) :
    ρ g * isotypicProjector A ρ χ * ρ g⁻¹ = isotypicProjector A ρ (g • χ) := by
  rw [isotypicProjector, isotypicProjector, mul_smul_comm, smul_mul_assoc, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [← Equiv.sum_comp (MulAut.conjNormal g : A ≃* A).toEquiv
    fun a : A => (((g • χ) a⁻¹ : ℂˣ) : ℂ) • ρ (a : E)]
  refine Finset.sum_congr rfl fun a _ => ?_
  show ρ g * (((χ a⁻¹ : ℂˣ) : ℂ) • ρ (a : E)) * ρ g⁻¹ =
    (((g • χ) (MulAut.conjNormal g a)⁻¹ : ℂˣ) : ℂ) • ρ ((MulAut.conjNormal g a : A) : E)
  rw [conjCharacter_apply, conjNormal_inv_conjNormal_inv, MulAut.conjNormal_apply, map_mul,
    map_mul, mul_smul_comm, smul_mul_assoc]

/-- `ρ(g) e_χ = e_{g • χ} ρ(g)`. -/
theorem apply_mul_isotypicProjector_eq (g : E) (χ : LinearCharacter A) :
    ρ g * isotypicProjector A ρ χ = isotypicProjector A ρ (g • χ) * ρ g := by
  rw [← apply_mul_isotypicProjector_mul_apply_inv, mul_assoc, ← map_mul, inv_mul_cancel, map_one,
    mul_one]

theorem isotypicProjector_idempotent (χ : LinearCharacter A) :
    isotypicProjector A ρ χ * isotypicProjector A ρ χ = isotypicProjector A ρ χ := by
  rw [isotypicProjector_mul, if_pos rfl]

/-! ### The traces -/

variable [FiniteDimensional ℂ V]

/-- `F_χ(g) = tr(ρ(g) e_χ)`. -/
def isotypicTrace (χ : LinearCharacter A) (g : E) : ℂ :=
  LinearMap.trace ℂ V (ρ g * isotypicProjector A ρ χ)

/-- **The character is the sum of the functions `F_χ`.** -/
theorem sum_isotypicTrace (g : E) :
    ∑ χ : LinearCharacter A, isotypicTrace A ρ χ g = ρ.character g := by
  simp only [isotypicTrace]
  rw [← map_sum, ← Finset.mul_sum, sum_isotypicProjector, mul_one]
  rfl

/-- **`F_χ` vanishes off the stabilizer of `χ`.** -/
theorem isotypicTrace_eq_zero {χ : LinearCharacter A} {g : E} (h : g • χ ≠ χ) :
    isotypicTrace A ρ χ g = 0 := by
  have hzero : isotypicProjector A ρ χ * isotypicProjector A ρ (g • χ) = 0 := by
    rw [isotypicProjector_mul, if_neg (Ne.symm h)]
  calc isotypicTrace A ρ χ g
      = LinearMap.trace ℂ V (ρ g * isotypicProjector A ρ χ * isotypicProjector A ρ χ) := by
        rw [isotypicTrace, mul_assoc, isotypicProjector_idempotent]
    _ = LinearMap.trace ℂ V
          (isotypicProjector A ρ (g • χ) * (ρ g * isotypicProjector A ρ χ)) := by
        rw [apply_mul_isotypicProjector_eq, mul_assoc, ← apply_mul_isotypicProjector_eq]
    _ = LinearMap.trace ℂ V
          (ρ g * isotypicProjector A ρ χ * isotypicProjector A ρ (g • χ)) :=
        LinearMap.trace_mul_comm ℂ _ _
    _ = 0 := by rw [mul_assoc, hzero, mul_zero, map_zero]

/-- `F_χ(x g x⁻¹) = F_{x⁻¹ • χ}(g)`. -/
theorem isotypicTrace_conj (χ : LinearCharacter A) (x g : E) :
    isotypicTrace A ρ χ (x * g * x⁻¹) = isotypicTrace A ρ (x⁻¹ • χ) g := by
  have e1 : ρ x * ρ g * ρ x⁻¹ * isotypicProjector A ρ χ =
      ρ x * (ρ g * (ρ x⁻¹ * isotypicProjector A ρ χ)) := by simp only [mul_assoc]
  have e2 : ρ g * (ρ x⁻¹ * isotypicProjector A ρ χ * ρ x) =
      ρ g * (ρ x⁻¹ * isotypicProjector A ρ χ) * ρ x := by simp only [mul_assoc]
  rw [isotypicTrace, isotypicTrace, ← apply_mul_isotypicProjector_mul_apply_inv, inv_inv, map_mul,
    map_mul, e1, e2, LinearMap.trace_mul_comm]

/-- **On the stabilizer of `χ` the function `F_χ` is a character**: the character of the
stabilizer on the range of `e_χ`. -/
theorem isotypicTrace_mem_fdCharacterSet_stabilizer (χ : LinearCharacter A) :
    (fun t : MulAction.stabilizer E χ => isotypicTrace A ρ χ (t : E)) ∈
      fdCharacterSet (MulAction.stabilizer E χ) :=
  trace_mul_idempotent_mem_fdCharacterSet (ρ.comp (MulAction.stabilizer E χ).subtype)
    (isotypicProjector A ρ χ) (isotypicProjector_idempotent A ρ χ) fun t => by
      show ρ (t : E) * isotypicProjector A ρ χ = isotypicProjector A ρ χ * ρ (t : E)
      rw [apply_mul_isotypicProjector_eq, MulAction.mem_stabilizer_iff.mp t.2]

end GaloisForLFunctions
