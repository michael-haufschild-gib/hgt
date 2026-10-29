import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2KubotaCocycle

/-!
# Central extensions from the proved rank-one symbol

Pushing the Milnor-valued Kubota cocycle through an additive homomorphism gives
an explicit group on pairs. Projection is surjective, and its kernel is exactly
the injective central copy of the coefficient group.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {K A : Type*} [Field K] [AddCommGroup A]

/-- Pairs with multiplication twisted by the image of the Kubota symbol. -/
@[ext] structure SL2SymbolExtension (τ : MilnorKDeg K 2 →+ A) where
  /-- The determinant-one matrix. -/
  base : SL2 K
  /-- The central coordinate, written additively. -/
  centralCoord : A

namespace SL2SymbolExtension

variable {τ : MilnorKDeg K 2 →+ A}

instance : Mul (SL2SymbolExtension τ) :=
  ⟨fun x y => ⟨x.base * y.base,
    x.centralCoord + y.centralCoord + τ (kubotaCocycle x.base y.base)⟩⟩

instance : One (SL2SymbolExtension τ) := ⟨⟨1, 0⟩⟩

instance : Inv (SL2SymbolExtension τ) :=
  ⟨fun x => ⟨x.base⁻¹, -x.centralCoord - τ (kubotaCocycle x.base⁻¹ x.base)⟩⟩

@[simp] theorem base_mul (x y : SL2SymbolExtension τ) :
    (x * y).base = x.base * y.base := rfl

@[simp] theorem centralCoord_mul (x y : SL2SymbolExtension τ) :
    (x * y).centralCoord =
      x.centralCoord + y.centralCoord + τ (kubotaCocycle x.base y.base) := rfl

@[simp] theorem base_one : (1 : SL2SymbolExtension τ).base = 1 := rfl

@[simp] theorem centralCoord_one : (1 : SL2SymbolExtension τ).centralCoord = 0 := rfl

@[simp] theorem base_inv (x : SL2SymbolExtension τ) : (x⁻¹).base = x.base⁻¹ := rfl

@[simp] theorem centralCoord_inv (x : SL2SymbolExtension τ) :
    (x⁻¹).centralCoord = -x.centralCoord - τ (kubotaCocycle x.base⁻¹ x.base) := rfl

instance : Group (SL2SymbolExtension τ) where
  mul_assoc x y z := by
    apply SL2SymbolExtension.ext
    · exact mul_assoc _ _ _
    · simp only [centralCoord_mul, base_mul]
      have hc := congrArg τ (kubotaCocycle_identity x.base y.base z.base)
      simp only [map_add] at hc
      calc
        _ = x.centralCoord + y.centralCoord + z.centralCoord +
            (τ (kubotaCocycle x.base y.base) +
              τ (kubotaCocycle (x.base * y.base) z.base)) := by abel
        _ = x.centralCoord + y.centralCoord + z.centralCoord +
            (τ (kubotaCocycle x.base (y.base * z.base)) +
              τ (kubotaCocycle y.base z.base)) := by rw [hc]
        _ = _ := by abel
  one_mul x := by
    apply SL2SymbolExtension.ext
    · exact one_mul _
    · simp only [centralCoord_mul, centralCoord_one, base_one,
        kubotaCocycle_one_left, map_zero, zero_add, add_zero]
  mul_one x := by
    apply SL2SymbolExtension.ext
    · exact mul_one _
    · simp only [centralCoord_mul, centralCoord_one, base_one,
        kubotaCocycle_one_right, map_zero, add_zero]
  inv_mul_cancel x := by
    apply SL2SymbolExtension.ext
    · exact inv_mul_cancel _
    · simp only [centralCoord_mul, centralCoord_inv, base_inv, centralCoord_one]
      abel

/-- Forget the central coordinate. -/
def projection (τ : MilnorKDeg K 2 →+ A) : SL2SymbolExtension τ →* SL2 K where
  toFun := base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The set-theoretic section with zero central coordinate. -/
def sectionOf (τ : MilnorKDeg K 2 →+ A) (g : SL2 K) : SL2SymbolExtension τ := ⟨g, 0⟩

@[simp] theorem projection_sectionOf (g : SL2 K) :
    projection τ (sectionOf τ g) = g := rfl

theorem projection_surjective (τ : MilnorKDeg K 2 →+ A) :
    Function.Surjective (projection τ) := fun g => ⟨sectionOf τ g, rfl⟩

/-- The coefficient group embeds as the central fiber over the identity. -/
def centralEmbedding (τ : MilnorKDeg K 2 →+ A) :
    Multiplicative A →* SL2SymbolExtension τ where
  toFun z := ⟨1, z.toAdd⟩
  map_one' := rfl
  map_mul' z w := by
    apply SL2SymbolExtension.ext
    · exact (one_mul (1 : SL2 K)).symm
    · change z.toAdd + w.toAdd = z.toAdd + w.toAdd + τ (kubotaCocycle 1 1)
      rw [kubotaCocycle_one_left, map_zero, add_zero]

@[simp] theorem projection_centralEmbedding (z : Multiplicative A) :
    projection τ (centralEmbedding τ z) = 1 := rfl

theorem centralEmbedding_injective (τ : MilnorKDeg K 2 →+ A) :
    Function.Injective (centralEmbedding τ) := by
  intro z w h
  exact Multiplicative.toAdd.injective (congrArg centralCoord h)

theorem centralEmbedding_commute (z : Multiplicative A) (x : SL2SymbolExtension τ) :
    Commute (centralEmbedding τ z) x := by
  apply SL2SymbolExtension.ext
  · exact (one_mul x.base).trans (mul_one x.base).symm
  · change z.toAdd + x.centralCoord + τ (kubotaCocycle 1 x.base) =
      x.centralCoord + z.toAdd + τ (kubotaCocycle x.base 1)
    rw [kubotaCocycle_one_left, kubotaCocycle_one_right, map_zero, add_zero, add_zero]
    exact add_comm _ _

/-- Exactness is literal equality of the kernel and the embedded coefficient group. -/
theorem projection_ker_eq_range (τ : MilnorKDeg K 2 →+ A) :
    (projection τ).ker = (centralEmbedding τ).range := by
  ext x
  constructor
  · intro hx
    refine ⟨Multiplicative.ofAdd x.centralCoord, ?_⟩
    apply SL2SymbolExtension.ext
    · exact hx.symm
    · rfl
  · rintro ⟨z, rfl⟩
    rfl

end SL2SymbolExtension

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
