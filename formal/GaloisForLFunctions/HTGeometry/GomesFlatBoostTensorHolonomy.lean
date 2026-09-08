import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Associated tensor matter for the actual flat Cartan connection

The induced-transport construction described in arXiv:2404.10461 and the
representation-dependent visibility discussed in arXiv:2607.24901v1 apply to the
corpus's flat boost connection. Its original carrier has no nonzero fixed vector
at nontrivial holonomy. Its tensor square has exactly two independent neutral
weight directions. The full circle representation is induced from the original
holonomy; the classification holds for every integer winding.
-/

open scoped TensorProduct
noncomputable section
namespace HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy

/-- The two weight directions of the actual flat Cartan fibre. -/
def flatBoostWeight (b : Bool) : Fibre := if b then eMinus else ePlus

/-- Dual light-cone coordinate, normalized to the existing weight vectors. -/
def flatBoostCoordinate (b : Bool) : Fibre →ₗ[ℝ] ℝ where
  toFun v := if b then (v.1+v.2)/2 else (v.1-v.2)/2
  map_add' v w := by cases b <;> dsimp <;> ring
  map_smul' r v := by cases b <;> dsimp <;> ring

/-- Exact light-cone decomposition of every original carrier vector. -/
theorem flatBoost_weight_resolution (v : Fibre) :
    flatBoostCoordinate true v • eMinus + flatBoostCoordinate false v • ePlus = v := by
  apply Prod.ext <;> simp [flatBoostCoordinate,eMinus,ePlus] <;> ring

/-- Boosts act by positive and negative exponential weights. -/
theorem boost_flatBoostWeight (a : ℝ) (b : Bool) :
    boost a (flatBoostWeight b) = Real.exp (if b then a else -a) • flatBoostWeight b := by
  cases b
  · apply Prod.ext
    · simpa [flatBoostWeight,ePlus,sub_eq_add_neg] using Real.cosh_sub_sinh a
    · change Real.sinh a * 1 + Real.cosh a * (-1) = Real.exp (-a) * (-1)
      calc
        _ = -(Real.cosh a - Real.sinh a) := by ring
        _ = _ := by rw [Real.cosh_sub_sinh]; ring
  · apply Prod.ext
    · simp [flatBoostWeight,eMinus,Real.cosh_add_sinh]
    · simp [flatBoostWeight,eMinus,add_comm,Real.cosh_add_sinh]

/-- Dual coordinates carry the same two exponential weights. -/
theorem flatBoostCoordinate_boost (a : ℝ) (b : Bool) (v : Fibre) :
    flatBoostCoordinate b (boost a v) =
      Real.exp (if b then a else -a) * flatBoostCoordinate b v := by
  cases b
  · simp only [flatBoostCoordinate, Bool.false_eq_true, ↓reduceIte,
      LinearMap.coe_mk, AddHom.coe_mk, boost_apply]
    rw [← Real.cosh_sub_sinh]
    ring
  · simp only [flatBoostCoordinate, ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk, boost_apply]
    rw [← Real.cosh_add_sinh]
    ring

/-- The associated tensor-square transport of the same flat connection. -/
def flatBoostTensor (a : ℝ) : (Fibre ⊗[ℝ] Fibre) ≃ₗ[ℝ] (Fibre ⊗[ℝ] Fibre) :=
  TensorProduct.congr (boost a) (boost a)

theorem flatBoostTensor_tmul (a : ℝ) (v w : Fibre) :
    flatBoostTensor a (v ⊗ₜ[ℝ] w) = boost a v ⊗ₜ[ℝ] boost a w := rfl

/-- The four tensor-coordinate functionals. -/
def flatBoostTensorCoordinate (b c : Bool) : (Fibre ⊗[ℝ] Fibre) →ₗ[ℝ] ℝ :=
  TensorProduct.lift
    { toFun := fun v => flatBoostCoordinate b v • flatBoostCoordinate c
      map_add' v w := by simp [map_add, add_smul]
      map_smul' r v := by simp [map_smul, smul_smul] }

theorem flatBoostTensorCoordinate_tmul (b c : Bool) (v w : Fibre) :
    flatBoostTensorCoordinate b c (v ⊗ₜ[ℝ] w) = flatBoostCoordinate b v * flatBoostCoordinate c w := rfl

/-- Every tensor weight is the sum of its two original connection weights. -/
theorem flatBoostTensor_weight (a : ℝ) (b c : Bool) :
    flatBoostTensor a (flatBoostWeight b ⊗ₜ[ℝ] flatBoostWeight c) =
      Real.exp ((if b then a else -a)+(if c then a else -a)) •
        (flatBoostWeight b ⊗ₜ[ℝ] flatBoostWeight c) := by
  rw [flatBoostTensor_tmul, boost_flatBoostWeight, boost_flatBoostWeight,
    TensorProduct.smul_tmul_smul, ← Real.exp_add]

/-- The mixed weights cancel and retain two parallel tensor directions. -/
theorem flatBoostTensor_mixed_fixed (a : ℝ) :
    flatBoostTensor a (eMinus ⊗ₜ[ℝ] ePlus) = eMinus ⊗ₜ[ℝ] ePlus ∧
    flatBoostTensor a (ePlus ⊗ₜ[ℝ] eMinus) = ePlus ⊗ₜ[ℝ] eMinus := by
  constructor
  · simpa [flatBoostWeight] using flatBoostTensor_weight a true false
  · simpa [flatBoostWeight] using flatBoostTensor_weight a false true

/-- Every tensor coordinate measures its exact additive transport weight. -/
theorem flatBoostTensorCoordinate_transport (a : ℝ) (b c : Bool) (x : Fibre ⊗[ℝ] Fibre) :
    flatBoostTensorCoordinate b c (flatBoostTensor a x) =
      Real.exp ((if b then a else -a)+(if c then a else -a)) * flatBoostTensorCoordinate b c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add,hx,hy,mul_add]
  | tmul v w =>
      rw [flatBoostTensor_tmul,flatBoostTensorCoordinate_tmul,flatBoostTensorCoordinate_tmul,
        flatBoostCoordinate_boost,flatBoostCoordinate_boost,Real.exp_add]
      ring

/-- The four weight coefficients reconstruct every tensor in the literal tensor product. -/
theorem flatBoostTensor_resolution (x : Fibre ⊗[ℝ] Fibre) :
    x = flatBoostTensorCoordinate true true x • (eMinus ⊗ₜ[ℝ] eMinus) +
      flatBoostTensorCoordinate true false x • (eMinus ⊗ₜ[ℝ] ePlus) +
      flatBoostTensorCoordinate false true x • (ePlus ⊗ₜ[ℝ] eMinus) +
      flatBoostTensorCoordinate false false x • (ePlus ⊗ₜ[ℝ] ePlus) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add,add_smul]
      conv_lhs => rw [hx,hy]
      abel
  | tmul v w =>
      simp only [flatBoostTensorCoordinate_tmul]
      calc
        v ⊗ₜ[ℝ] w =
          (flatBoostCoordinate true v • eMinus + flatBoostCoordinate false v • ePlus) ⊗ₜ[ℝ]
            (flatBoostCoordinate true w • eMinus + flatBoostCoordinate false w • ePlus) := by
              rw [flatBoost_weight_resolution,flatBoost_weight_resolution]
        _ = _ := by
          simp only [TensorProduct.add_tmul,TensorProduct.tmul_add,TensorProduct.smul_tmul_smul]
          abel

/-- Coordinate values on the original two weight vectors are Kronecker deltas. -/
theorem flatBoostCoordinate_weight (b c : Bool) :
    flatBoostCoordinate b (flatBoostWeight c) = if b=c then 1 else 0 := by
  cases b <;> cases c <;> simp [flatBoostCoordinate,flatBoostWeight,eMinus,ePlus]

/-- The two parallel tensor directions are linearly independent. -/
theorem flatBoostTensor_mixed_independent (r s : ℝ) :
    r • (eMinus ⊗ₜ[ℝ] ePlus) + s • (ePlus ⊗ₜ[ℝ] eMinus) = 0 ↔ r=0 ∧ s=0 := by
  constructor
  · intro h
    have hr := congrArg (flatBoostTensorCoordinate true false) h
    have hs := congrArg (flatBoostTensorCoordinate false true) h
    simp [flatBoostTensorCoordinate_tmul,flatBoostCoordinate,eMinus,ePlus] at hr hs
    exact ⟨hr,hs⟩
  · rintro ⟨rfl,rfl⟩
    simp

/-- Zero connection induces identity tensor transport. -/
theorem flatBoostTensor_zero (x : Fibre ⊗[ℝ] Fibre) : flatBoostTensor 0 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | tmul v w => simp [flatBoostTensor_tmul]

/-- The original carrier has no nonzero fixed vector for nontrivial boost holonomy. -/
theorem boost_fixed_vector_iff (a : ℝ) (v : Fibre) :
    boost a v = v ↔ a=0 ∨ v=0 := by
  constructor
  · intro h
    by_cases ha : a=0
    · exact Or.inl ha
    · right
      have hc (b : Bool) : flatBoostCoordinate b v = 0 := by
        by_contra hz
        have ht := flatBoostCoordinate_boost a b v
        rw [h] at ht
        have he := (Real.exp_eq_one_iff _).mp ((mul_eq_right₀ hz).mp ht.symm)
        cases b <;> simp at he <;> exact ha he
      have hr := flatBoost_weight_resolution v
      simpa [hc] using hr.symm
  · rintro (rfl | rfl) <;> simp

/-- The full tensor-square fixed space is exactly the two-dimensional mixed-weight space,
unless the original holonomy is trivial. -/
theorem flatBoostTensor_fixed_space (a : ℝ) (x : Fibre ⊗[ℝ] Fibre) :
    flatBoostTensor a x = x ↔ a=0 ∨
      ∃ r s : ℝ, x = r • (eMinus ⊗ₜ[ℝ] ePlus) + s • (ePlus ⊗ₜ[ℝ] eMinus) := by
  constructor
  · intro h
    by_cases ha : a=0
    · exact Or.inl ha
    · right
      have hc (b : Bool) : flatBoostTensorCoordinate b b x = 0 := by
        by_contra hz
        have ht := flatBoostTensorCoordinate_transport a b b x
        rw [h] at ht
        have he := (Real.exp_eq_one_iff _).mp ((mul_eq_right₀ hz).mp ht.symm)
        apply ha
        cases b <;> simp at he <;> linarith
      refine ⟨flatBoostTensorCoordinate true false x, flatBoostTensorCoordinate false true x, ?_⟩
      have hr := flatBoostTensor_resolution x
      simpa only [hc,zero_smul,zero_add,add_zero] using hr
  · rintro (rfl | ⟨r,s,rfl⟩)
    · exact flatBoostTensor_zero x
    · simp only [map_add,map_smul,(flatBoostTensor_mixed_fixed a).1,(flatBoostTensor_mixed_fixed a).2]

/-- A nonzero parallel tensor survives every value of the original boost holonomy. -/
theorem flatBoostTensor_parallel_nonzero (a : ℝ) :
    ∃ x : Fibre ⊗[ℝ] Fibre, x ≠ 0 ∧ flatBoostTensor a x = x := by
  refine ⟨eMinus ⊗ₜ[ℝ] ePlus, ?_, (flatBoostTensor_mixed_fixed a).1⟩
  intro hx
  have h := congrArg (flatBoostTensorCoordinate true false) hx
  simp [flatBoostTensorCoordinate_tmul,flatBoostCoordinate,eMinus,ePlus] at h

/-- The associated tensor-square construction is a genuine representation functor. -/
def flatTensorSquareHom : (Fibre ≃ₗ[ℝ] Fibre) →*
    ((Fibre ⊗[ℝ] Fibre) ≃ₗ[ℝ] (Fibre ⊗[ℝ] Fibre)) where
  toFun U := TensorProduct.congr U U
  map_one' := by
    apply LinearEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (·+·) hx hy
    | tmul v w => rfl
  map_mul' U V := by
    apply LinearEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (·+·) hx hy
    | tmul v w => rfl

/-- Holonomy of the tensor matter is induced by the exact original circle representation. -/
def flatTensorHolonomy (a : ℝ) : Multiplicative ℤ →*
    ((Fibre ⊗[ℝ] Fibre) ≃ₗ[ℝ] (Fibre ⊗[ℝ] Fibre)) :=
  flatTensorSquareHom.comp (holonomyRepresentation a)

/-- The tensor circle holonomy retains the source holonomy on both tensor legs. -/
theorem flatTensorHolonomy_tmul (a : ℝ) (n : Multiplicative ℤ) (v w : Fibre) :
    flatTensorHolonomy a n (v ⊗ₜ[ℝ] w) =
      holonomyRepresentation a n v ⊗ₜ[ℝ] holonomyRepresentation a n w := rfl

/-- The generating tensor holonomy is precisely the previously classified one-turn transport. -/
theorem flatTensorHolonomy_generator (a : ℝ) :
    flatTensorHolonomy a (Multiplicative.ofAdd 1) = flatBoostTensor a := by
  change flatTensorSquareHom (holonomyRepresentation a (Multiplicative.ofAdd 1)) = _
  rw [holonomy_generator]
  rfl

/-- Integer winding acts by powers of the classified generating tensor holonomy. -/
theorem flatTensorHolonomy_winding (a : ℝ) (n : ℤ) :
    flatTensorHolonomy a (Multiplicative.ofAdd n) = flatBoostTensor a ^ n := by
  change flatTensorSquareHom (boost a ^ n) = flatBoostTensor a ^ n
  exact map_zpow flatTensorSquareHom (boost a) n

/-- The same fixed-space classification holds for every integer winding of the actual connection. -/
theorem flatTensorHolonomy_fixed_space (a : ℝ) (x : Fibre ⊗[ℝ] Fibre) :
    (∀ n : ℤ, flatTensorHolonomy a (Multiplicative.ofAdd n) x = x) ↔ a=0 ∨
      ∃ r s : ℝ, x = r • (eMinus ⊗ₜ[ℝ] ePlus) + s • (ePlus ⊗ₜ[ℝ] eMinus) := by
  rw [← flatBoostTensor_fixed_space]
  constructor
  · intro h
    simpa only [flatTensorHolonomy_generator] using h 1
  · intro h n
    rw [flatTensorHolonomy_winding]
    have hf : x ∈ MulAction.fixedBy (Fibre ⊗[ℝ] Fibre) (flatBoostTensor a) := h
    exact MulAction.mem_fixedBy_zpow hf n

end HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy
