import GaloisForLFunctions.RepresentationLifting.Hecke.AffineBraidBoundary

/-!
# Polynomial Hecke permutation specialization

A three-dimensional polynomial action retains both quadratic and braid relations
at every parameter. Its trivial line splits exactly away from the cubic divisor.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.Hecke

/-- The first generator of the polynomial three-letter Hecke permutation module. -/
def permutationLeft (t : ℂ) : Module.End ℂ Triple where
  toFun v := ((t - 1) * v.1 + v.2.1, t * v.1, t * v.2.2)
  map_add' _ _ := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' _ _ := by ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

/-- The adjacent second generator, with the same quadratic parameter. -/
def permutationRight (t : ℂ) : Module.End ℂ Triple where
  toFun v := (t * v.1, (t - 1) * v.2.1 + v.2.2, t * v.2.1)
  map_add' _ _ := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' _ _ := by ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

/-- The first generator satisfies the Hecke relation at every parameter, including zero. -/
theorem permutationLeft_quadratic (t : ℂ) :
    permutationLeft t * permutationLeft t = (t - 1) • permutationLeft t + t • 1 := by
  apply LinearMap.ext
  intro v
  ext <;> simp [permutationLeft, Module.End.mul_apply] <;> ring

theorem permutationRight_quadratic (t : ℂ) :
    permutationRight t * permutationRight t = (t - 1) • permutationRight t + t • 1 := by
  apply LinearMap.ext
  intro v
  ext <;> simp [permutationRight, Module.End.mul_apply] <;> ring

/-- This polynomial deformation retains the braid relation for every specialization. -/
theorem permutation_braid (t : ℂ) :
    permutationLeft t * permutationRight t * permutationLeft t =
      permutationRight t * permutationLeft t * permutationRight t := by
  apply LinearMap.ext
  intro v
  ext <;> simp [permutationLeft, permutationRight, Module.End.mul_apply] <;> ring

/-- Parameter one recovers the literal adjacent transpositions. -/
theorem permutation_at_one : permutationLeft 1 = swapLeft ∧ permutationRight 1 = swapRight := by
  constructor
  · apply LinearMap.ext
    intro v
    simp [permutationLeft, swapLeft]
  · apply LinearMap.ext
    intro v
    simp [permutationRight, swapRight]

/-- The constant vector spans the trivial Hecke character for every parameter. -/
def permutationUnit : Triple := (1, 1, 1)

theorem permutationUnit_left (t : ℂ) : permutationLeft t permutationUnit = t • permutationUnit := by
  ext <;> simp [permutationLeft, permutationUnit]

theorem permutationUnit_right (t : ℂ) : permutationRight t permutationUnit = t • permutationUnit := by
  ext <;> simp [permutationRight, permutationUnit]

/-- The unique weighted augmentation, normalized at the last standard basis vector. -/
def permutationAugmentation (t : ℂ) : Triple →ₗ[ℂ] ℂ where
  toFun v := t ^ 2 * v.1 + t * v.2.1 + v.2.2
  map_add' _ _ := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' _ _ := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem permutationAugmentation_apply (t : ℂ) (v : Triple) :
    permutationAugmentation t v = t ^ 2 * v.1 + t * v.2.1 + v.2.2 := rfl

theorem permutationAugmentation_left (t : ℂ) (v : Triple) :
    permutationAugmentation t (permutationLeft t v) = t * permutationAugmentation t v := by
  simp only [permutationAugmentation_apply, permutationLeft, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem permutationAugmentation_right (t : ℂ) (v : Triple) :
    permutationAugmentation t (permutationRight t v) = t * permutationAugmentation t v := by
  simp only [permutationAugmentation_apply, permutationRight, LinearMap.coe_mk, AddHom.coe_mk]
  ring

private def e₁ : Triple := (1, 0, 0)
private def e₂ : Triple := (0, 1, 0)
private def e₃ : Triple := (0, 0, 1)

private theorem linear_coordinates (f : Triple →ₗ[ℂ] ℂ) (v : Triple) :
    f v = v.1 * f e₁ + v.2.1 * f e₂ + v.2.2 * f e₃ := by
  have hv : v = v.1 • e₁ + v.2.1 • e₂ + v.2.2 • e₃ := by ext <;> simp [e₁, e₂, e₃]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

/-- All intertwining functionals are scalar multiples of the weighted augmentation, even at singular parameters. -/
theorem permutation_intertwiner_iff (t : ℂ) (f : Triple →ₗ[ℂ] ℂ) :
    ((∀ v, f (permutationLeft t v) = t * f v) ∧
      ∀ v, f (permutationRight t v) = t * f v) ↔
      f = f (0, 0, 1) • permutationAugmentation t := by
  constructor
  · rintro ⟨hL, hR⟩
    have hLe : permutationLeft t e₂ = e₁ := by ext <;> simp [permutationLeft, e₁, e₂]
    have hRe : permutationRight t e₃ = e₂ := by ext <;> simp [permutationRight, e₂, e₃]
    have h1 : f e₁ = t * f e₂ := by simpa only [hLe] using hL e₂
    have h2 : f e₂ = t * f e₃ := by simpa only [hRe] using hR e₃
    apply LinearMap.ext
    intro v
    rw [linear_coordinates f v, h1, h2]
    simp only [LinearMap.smul_apply, smul_eq_mul, permutationAugmentation_apply, e₃]
    ring
  · intro hf
    constructor
    · intro v
      rw [hf]
      simp only [LinearMap.smul_apply, smul_eq_mul, permutationAugmentation_left]
      ring
    · intro v
      rw [hf]
      simp only [LinearMap.smul_apply, smul_eq_mul, permutationAugmentation_right]
      ring

/-- The trivial line admits an equivariant retraction exactly away from the third cyclotomic divisor. -/
theorem permutation_retraction_iff (t : ℂ) :
    (∃ f : Triple →ₗ[ℂ] ℂ, (∀ v, f (permutationLeft t v) = t * f v) ∧
      (∀ v, f (permutationRight t v) = t * f v) ∧ f permutationUnit = 1) ↔
      t ^ 2 + t + 1 ≠ 0 := by
  constructor
  · rintro ⟨f, hL, hR, hu⟩ hz
    have hf := (permutation_intertwiner_iff t f).mp ⟨hL, hR⟩
    rw [hf] at hu
    simp only [LinearMap.smul_apply, smul_eq_mul, permutationAugmentation_apply,
      permutationUnit, mul_one, hz, mul_zero] at hu
    exact zero_ne_one hu
  · intro ht
    refine ⟨(t ^ 2 + t + 1)⁻¹ • permutationAugmentation t, ?_, ?_, ?_⟩
    · intro v
      simp only [LinearMap.smul_apply, smul_eq_mul, permutationAugmentation_left]
      ring
    · intro v
      simp only [LinearMap.smul_apply, smul_eq_mul, permutationAugmentation_right]
      ring
    · simp only [LinearMap.smul_apply, smul_eq_mul, permutationAugmentation_apply,
        permutationUnit, mul_one, inv_mul_cancel₀ ht]

/-- At parameter minus one the generator has a genuine nonzero nilpotent part. -/
theorem permutationLeft_collision :
    (permutationLeft (-1) + 1) ^ 2 = 0 ∧ permutationLeft (-1) + 1 ≠ 0 := by
  constructor
  · rw [pow_two]
    simp only [add_mul, mul_add, one_mul, mul_one, permutationLeft_quadratic]
    module
  · intro h
    have he := congrArg (fun T : Module.End ℂ Triple => (T (0, 1, 0)).1) h
    simp [permutationLeft] at he

#print axioms permutation_braid
#print axioms permutation_intertwiner_iff
#print axioms permutation_retraction_iff
#print axioms permutationLeft_collision
end GaloisForLFunctions.RepresentationLifting.Hecke
