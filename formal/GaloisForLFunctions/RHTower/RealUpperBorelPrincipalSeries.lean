import GaloisForLFunctions.RHTower.MaassHomogeneousSpaceCorrespondence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RepresentationTheory.Coinduced

/-!
# Algebraic principal series for the real upper Borel of `SL(2)`

This file constructs the upper-triangular Borel subgroup of `SL(2, ℝ)`, its real-power diagonal
characters, and the resulting algebraically coinduced representations using Mathlib's
`Representation.coind`.  These are the algebraic function spaces underlying real principal-series
models.  Smooth vectors, Hilbert completions, irreducibility, genericity, and unitarity are not
asserted here.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Matrix

/-- Upper-triangular Borel subgroup of `SL(2, ℝ)`. -/
def realUpperBorel : Subgroup SL2R where
  carrier := {g | g 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a 1 0 = 0 at ha
    change b 1 0 = 0 at hb
    change (a * b : SL2R) 1 0 = 0
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    change a 1 0 = 0 at ha
    change (a⁻¹ : SL2R) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [ha]

@[simp]
theorem realUpperBorel_mem_iff (g : SL2R) :
    g ∈ realUpperBorel ↔ g 1 0 = 0 :=
  Iff.rfl

/-- The upper-left entry of a product in the upper Borel is the product of upper-left entries. -/
@[simp]
theorem realUpperBorel_mul_zero_zero (a b : realUpperBorel) :
    ((a * b : realUpperBorel) : SL2R) 0 0 =
      ((a : realUpperBorel) : SL2R) 0 0 * ((b : realUpperBorel) : SL2R) 0 0 := by
  change ((a : SL2R) * (b : SL2R)) 0 0 = (a : SL2R) 0 0 * (b : SL2R) 0 0
  have hb : (b : SL2R) 1 0 = 0 := (realUpperBorel_mem_iff (b : SL2R)).mp b.property
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [hb]

/-- Both diagonal entries of an upper-triangular special-linear matrix are nonzero. -/
theorem realUpperBorel_zero_zero_ne_zero (b : realUpperBorel) :
    (b : SL2R) 0 0 ≠ 0 := by
  intro hb
  have hb10 : (b : SL2R) 1 0 = 0 := (realUpperBorel_mem_iff (b : SL2R)).mp b.property
  have hdet := (b : SL2R).property
  rw [Matrix.det_fin_two] at hdet
  simp [hb10, hb] at hdet

/-- Absolute-value real-power character on the real upper Borel. -/
def realUpperBorelRpowCharacter (σ : ℝ) : realUpperBorel →* ℂ where
  toFun b := ((|(b : SL2R) 0 0| ^ σ : ℝ) : ℂ)
  map_one' := by simp
  map_mul' a b := by
    rw [realUpperBorel_mul_zero_zero, abs_mul,
      Real.mul_rpow (abs_nonneg ((a : SL2R) 0 0)) (abs_nonneg ((b : SL2R) 0 0))]
    norm_cast

@[simp]
theorem realUpperBorelRpowCharacter_apply (σ : ℝ) (b : realUpperBorel) :
    realUpperBorelRpowCharacter σ b = ((|(b : SL2R) 0 0| ^ σ : ℝ) : ℂ) :=
  rfl

/-- The positive diagonal element `diag(2, 1/2)` in the real upper Borel. -/
def twoDiagonalBorel : realUpperBorel :=
  ⟨⟨!![(2 : ℝ), 0; 0, 1 / 2], by norm_num [Matrix.det_fin_two]⟩, by simp⟩

@[simp]
theorem realUpperBorelRpowCharacter_twoDiagonal (σ : ℝ) :
    realUpperBorelRpowCharacter σ twoDiagonalBorel = (((2 : ℝ) ^ σ : ℝ) : ℂ) := by
  simp [realUpperBorelRpowCharacter, twoDiagonalBorel]

/-- Real exponents whose Borel character has unit norm on every group element. -/
def unitaryRealBorelExponentLocus : Set ℝ :=
  {σ | ∀ b : realUpperBorel, ‖realUpperBorelRpowCharacter σ b‖ = 1}

/-- A real-power Borel character is unitary exactly when its real exponent vanishes. -/
theorem unitaryRealBorelExponentLocus_eq_singleton :
    unitaryRealBorelExponentLocus = {0} := by
  ext σ
  simp only [unitaryRealBorelExponentLocus, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have htwo := h twoDiagonalBorel
    rw [realUpperBorelRpowCharacter_twoDiagonal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (by norm_num) σ)] at htwo
    have hp : (2 : ℝ) ^ σ = (2 : ℝ) ^ (0 : ℝ) := by simpa using htwo
    exact (Real.rpow_right_inj (by norm_num) (by norm_num)).mp hp
  · intro hσ
    subst σ
    intro b
    simp [realUpperBorelRpowCharacter]

/-- One-dimensional representation attached to a complex-valued monoid character. -/
def oneDimensionalCharacterRepresentation {G : Type*} [Monoid G] (χ : G →* ℂ) :
    Representation ℂ G ℂ where
  toFun g :=
    { toFun := fun z ↦ χ g * z
      map_add' := fun x y ↦ by rw [mul_add]
      map_smul' := fun c x ↦ by simp only [RingHom.id_apply]; ring }
  map_one' := by
    apply LinearMap.ext
    intro z
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    simp [mul_assoc]

@[simp]
theorem oneDimensionalCharacterRepresentation_apply {G : Type*} [Monoid G]
    (χ : G →* ℂ) (g : G) (z : ℂ) :
    oneDimensionalCharacterRepresentation χ g z = χ g * z :=
  rfl

/-- Algebraic inducing character with exponent `σ`. -/
def realUpperBorelExponentRepresentation (σ : ℝ) :
    Representation ℂ realUpperBorel ℂ :=
  oneDimensionalCharacterRepresentation (realUpperBorelRpowCharacter σ)

/-- Algebraically coinduced real principal-series representation with explicit exponent `σ`. -/
def algebraicRealPrincipalSeries (σ : ℝ) :
    Representation ℂ SL2R
      (Representation.coindV realUpperBorel.subtype
        (realUpperBorelExponentRepresentation σ)) :=
  Representation.coind realUpperBorel.subtype
    (realUpperBorelExponentRepresentation σ)

/-- The defining Borel-equivariance law in the algebraic principal-series model. -/
@[simp]
theorem mem_algebraicRealPrincipalSeriesSpace_iff (σ : ℝ) (f : SL2R → ℂ) :
    f ∈ Representation.coindV realUpperBorel.subtype
        (realUpperBorelExponentRepresentation σ) ↔
      ∀ b : realUpperBorel, ∀ g : SL2R,
        f ((b : SL2R) * g) = realUpperBorelRpowCharacter σ b * f g :=
  Iff.rfl

/-- The principal-series action is right translation. -/
@[simp]
theorem algebraicRealPrincipalSeries_apply (σ : ℝ) (h g : SL2R)
    (f : Representation.coindV realUpperBorel.subtype
      (realUpperBorelExponentRepresentation σ)) :
    ((algebraicRealPrincipalSeries σ) h f).1 g = f.1 (g * h) :=
  rfl

end

end GaloisForLFunctions.RHTower
