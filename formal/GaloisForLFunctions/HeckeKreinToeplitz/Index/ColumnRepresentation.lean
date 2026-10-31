import GaloisForLFunctions.HeckeKreinToeplitz.Index.NullSubgroupRank

/-!
# The column representation of a group kernel

Inverse pullback preserves the span of all kernel columns. It gives an algebraic group
representation whose identity column and evaluation at identity recover the original kernel.
No positivity, continuity, or finite-dimensionality is required.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-- Left translation on functions, with inverse pullback. -/
def kernelColumnTranslate (a : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => a⁻¹ * x)

theorem kernelColumnTranslate_column (k : G → ℂ) (a g : G) :
    kernelColumnTranslate a (kernelColumn k g) = kernelColumn k (a * g) := by
  funext x
  change k ((a⁻¹ * x)⁻¹ * g) = k (x⁻¹ * (a * g))
  congr 1
  group

theorem kernelColumnTranslate_mem (k : G → ℂ) (a : G) {f : G → ℂ}
    (hf : f ∈ kernelColumnSpan k) : kernelColumnTranslate a f ∈ kernelColumnSpan k := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    rw [kernelColumnTranslate_column]
    exact Submodule.subset_span ⟨a * g, rfl⟩
  | zero => simpa only [map_zero] using (kernelColumnSpan k).zero_mem
  | add f g hf hg ihf ihg =>
    simpa only [map_add] using (kernelColumnSpan k).add_mem ihf ihg
  | smul c f hf ih =>
    simpa only [map_smul] using (kernelColumnSpan k).smul_mem c ih

/-- The group acts on the full column space of its kernel. -/
def kernelColumnRepresentation (k : G → ℂ) : G →* Module.End ℂ (kernelColumnSpan k) where
  toFun a :=
    { toFun := fun f => ⟨kernelColumnTranslate a f, kernelColumnTranslate_mem k a f.property⟩
      map_add' f g := Subtype.ext ((kernelColumnTranslate a).map_add f g)
      map_smul' c f := Subtype.ext ((kernelColumnTranslate a).map_smul c f) }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change (f : G → ℂ) (1⁻¹ * x) = (f : G → ℂ) x
    rw [inv_one, one_mul]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change (f : G → ℂ) ((a * b)⁻¹ * x) = (f : G → ℂ) (b⁻¹ * (a⁻¹ * x))
    rw [_root_.mul_inv_rev, mul_assoc]

/-- The identity column is the canonical vector of the column representation. -/
def kernelColumnVector (k : G → ℂ) : kernelColumnSpan k :=
  ⟨kernelColumn k 1, Submodule.subset_span ⟨1, rfl⟩⟩

/-- Evaluation at identity recovers the coefficient of the column representation. -/
def kernelColumnObservation (k : G → ℂ) : kernelColumnSpan k →ₗ[ℂ] ℂ where
  toFun f := f.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernelColumnRepresentation_vector (k : G → ℂ) (g : G) :
    (kernelColumnRepresentation k g (kernelColumnVector k) : G → ℂ) = kernelColumn k g := by
  change kernelColumnTranslate g (kernelColumn k 1) = kernelColumn k g
  rw [kernelColumnTranslate_column, mul_one]

/-- Every group kernel is a coefficient of its algebraic column representation. -/
theorem kernelColumnObservation_representation (k : G → ℂ) (g : G) :
    kernelColumnObservation k (kernelColumnRepresentation k g (kernelColumnVector k)) = k g := by
  change (kernelColumnRepresentation k g (kernelColumnVector k) : G → ℂ) 1 = k g
  rw [kernelColumnRepresentation_vector]
  simp only [kernelColumn, inv_one, one_mul]

#print axioms kernelColumnRepresentation
#print axioms kernelColumnObservation_representation
end GaloisForLFunctions.HeckeKreinToeplitz
