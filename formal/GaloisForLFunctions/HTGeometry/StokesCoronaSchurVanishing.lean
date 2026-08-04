import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Corona elimination, Schur complements, and relative vanishing coordinates

A positive hidden corona block is eliminated exactly by completing the quadratic square.  The
effective boundary kernel is its Schur complement; the hidden residual is the relative
vanishing-cycle coordinate and its positive quadratic norm is precisely the energy lost under
elimination.  The effective energy is the unique exact minimum.  Consequently any sequence of
exact corona eliminations is independent of elimination order.
-/

open scoped Matrix

namespace GaloisForLFunctions
namespace IrregularStokes
namespace CoronaSchur

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Full boundary-plus-corona quadratic energy. -/
def fullEnergy (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (x : m → ℝ) (y : n → ℝ) : ℝ :=
  (star (x ⊕ᵥ y)) ᵥ* (Matrix.fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y)

/-- Dirichlet-to-Neumann kernel obtained by eliminating the hidden block. -/
def effectiveKernel (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (D : Matrix n n ℝ) : Matrix m m ℝ :=
  A - B * D⁻¹ * Bᴴ

/-- Effective boundary energy. -/
def effectiveEnergy (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (x : m → ℝ) : ℝ :=
  (star x) ᵥ* (effectiveKernel A B D) ⬝ᵥ x

/-- Hidden residual after harmonic extension from the attachment boundary. -/
def coronaShift (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (x : m → ℝ) (y : n → ℝ) : n → ℝ :=
  (D⁻¹ * Bᴴ) *ᵥ x + y

/-- Positive metric on the relative vanishing-cycle coordinate. -/
def coronaCorrection (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (x : m → ℝ) (y : n → ℝ) : ℝ :=
  (star (coronaShift B D x y)) ᵥ* D ⬝ᵥ (coronaShift B D x y)

/-- Unique hidden harmonic extension minimizing full energy. -/
def hiddenMinimizer (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (x : m → ℝ) : n → ℝ :=
  -((D⁻¹ * Bᴴ) *ᵥ x)

/-- Harmonic graph embedding of boundary data into boundary-plus-hidden data. -/
noncomputable def harmonicGraph (B : Matrix m n ℝ) (D : Matrix n n ℝ) :
    (m → ℝ) →ₗ[ℝ] ((m → ℝ) × (n → ℝ)) where
  toFun x := (x, hiddenMinimizer B D x)
  map_add' x y := by
    ext a <;> simp [hiddenMinimizer, Matrix.mulVec_add] <;> ring
  map_smul' c x := by
    ext a <;> simp [hiddenMinimizer, Matrix.mulVec_smul] <;> ring

/-- Relative vanishing quotient: hidden data modulo harmonic extension from the boundary. -/
noncomputable def relativeVanishingMap (B : Matrix m n ℝ) (D : Matrix n n ℝ) :
    ((m → ℝ) × (n → ℝ)) →ₗ[ℝ] (n → ℝ) where
  toFun xy := coronaShift B D xy.1 xy.2
  map_add' x y := by
    ext a
    simp [coronaShift, Matrix.mulVec_add]
    ring
  map_smul' c x := by
    ext a
    simp [coronaShift, Matrix.mulVec_smul]
    ring

/-- Boundary-to-total-to-relative-vanishing is an exact linear sequence. -/
theorem harmonicGraph_relativeVanishing_exact
    (B : Matrix m n ℝ) (D : Matrix n n ℝ) :
    Function.Exact (harmonicGraph B D) (relativeVanishingMap B D) := by
  rw [LinearMap.exact_iff]
  ext xy
  constructor
  · intro hxy
    change relativeVanishingMap B D xy = 0 at hxy
    refine ⟨xy.1, ?_⟩
    apply Prod.ext
    · rfl
    · funext a
      have ha := congrFun hxy a
      change (((D⁻¹ * Bᴴ) *ᵥ xy.1) a + xy.2 a) = 0 at ha
      change -(((D⁻¹ * Bᴴ) *ᵥ xy.1) a) = xy.2 a
      linarith
  · rintro ⟨x, rfl⟩
    change relativeVanishingMap B D (harmonicGraph B D x) = 0
    ext a
    simp [harmonicGraph, relativeVanishingMap, coronaShift, hiddenMinimizer]

/-- Every relative vanishing coordinate has a representative with zero boundary value. -/
theorem relativeVanishingMap_surjective
    (B : Matrix m n ℝ) (D : Matrix n n ℝ) :
    Function.Surjective (relativeVanishingMap B D) := by
  intro y
  refine ⟨(0, y), ?_⟩
  ext a
  simp [relativeVanishingMap, coronaShift]

/-- Exact elimination means every boundary value has a minimizer and the stated effective energy
is a lower bound for every hidden extension. -/
def IsExactElimination {X Y : Type*} (energy : X → Y → ℝ)
    (effective : X → ℝ) : Prop :=
  (∀ x, ∃ y, energy x y = effective x) ∧
    ∀ x y, effective x ≤ energy x y

/-- Exact effective energy is unique. -/
theorem exactElimination_unique {X Y : Type*} {energy : X → Y → ℝ}
    {left right : X → ℝ} (hleft : IsExactElimination energy left)
    (hright : IsExactElimination energy right) : left = right := by
  funext x
  obtain ⟨yl, hyl⟩ := hleft.1 x
  obtain ⟨yr, hyr⟩ := hright.1 x
  apply le_antisymm
  · rw [← hyr]
    exact hleft.2 x yr
  · rw [← hyl]
    exact hright.2 x yl

/-- Exact elimination composes across successive hidden blocks. -/
theorem IsExactElimination.comp {X Y Z : Type*} {energy : X → Y → Z → ℝ}
    {middle : X → Y → ℝ} {effective : X → ℝ}
    (hinner : ∀ x y, IsExactElimination (fun _ : Unit => energy x y)
      (fun _ : Unit => middle x y))
    (houter : IsExactElimination middle effective) :
    IsExactElimination (fun x (yz : Y × Z) => energy x yz.1 yz.2) effective := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := houter.1 x
    obtain ⟨z, hz⟩ := (hinner x y).1 ()
    exact ⟨(y, z), hz.trans hy⟩
  · intro x yz
    exact (houter.2 x yz.1).trans ((hinner x yz.1).2 () yz.2)

/-- Exact Schur square-completion identity. -/
theorem fullEnergy_eq_correction_add_effective
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (x : m → ℝ) (y : n → ℝ) :
    fullEnergy A B D x y = coronaCorrection B D x y + effectiveEnergy A B D x := by
  letI : Invertible D := hD.isUnit.invertible
  exact Matrix.schur_complement_eq₂₂ A B x y hD.1

theorem coronaShift_hiddenMinimizer (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (x : m → ℝ) : coronaShift B D x (hiddenMinimizer B D x) = 0 := by
  simp [coronaShift, hiddenMinimizer]

/-- Harmonic hidden extension has exactly the effective boundary energy. -/
theorem fullEnergy_hiddenMinimizer_eq_effective
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (x : m → ℝ) :
    fullEnergy A B D x (hiddenMinimizer B D x) = effectiveEnergy A B D x := by
  rw [fullEnergy_eq_correction_add_effective A B hD]
  simp [coronaCorrection, coronaShift_hiddenMinimizer]

/-- Effective boundary energy is a lower bound for every hidden extension. -/
theorem effectiveEnergy_le_fullEnergy
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (x : m → ℝ) (y : n → ℝ) :
    effectiveEnergy A B D x ≤ fullEnergy A B D x y := by
  rw [fullEnergy_eq_correction_add_effective A B hD]
  have hnonneg := hD.posSemidef.dotProduct_mulVec_nonneg (coronaShift B D x y)
  rw [Matrix.dotProduct_mulVec] at hnonneg
  exact le_add_of_nonneg_left (by simpa [coronaCorrection] using hnonneg)

/-- Equality occurs exactly at the unique harmonic hidden extension. -/
theorem fullEnergy_eq_effective_iff_hiddenMinimizer
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (x : m → ℝ) (y : n → ℝ) :
    fullEnergy A B D x y = effectiveEnergy A B D x ↔
      y = hiddenMinimizer B D x := by
  rw [fullEnergy_eq_correction_add_effective A B hD]
  constructor
  · intro h
    have hzero : coronaCorrection B D x y = 0 := by linarith
    have hshift : coronaShift B D x y = 0 := by
      by_contra hne
      have hpos := hD.dotProduct_mulVec_pos hne
      rw [Matrix.dotProduct_mulVec] at hpos
      exact (ne_of_gt hpos) (by simpa [coronaCorrection] using hzero)
    funext a
    change y a = -(((D⁻¹ * Bᴴ) *ᵥ x) a)
    have ha := congrFun hshift a
    have : ((D⁻¹ * Bᴴ) *ᵥ x) a + y a = 0 := by
      simpa [coronaShift] using ha
    linarith
  · intro hy
    subst y
    simp [coronaCorrection, coronaShift_hiddenMinimizer]

/-- Positive hidden block gives an exact corona elimination. -/
theorem effectiveEnergy_isExactElimination
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) :
    IsExactElimination (fun x y => fullEnergy A B D x y)
      (fun x => effectiveEnergy A B D x) := by
  constructor
  · intro x
    exact ⟨hiddenMinimizer B D x, fullEnergy_hiddenMinimizer_eq_effective A B hD x⟩
  · intro x y
    exact effectiveEnergy_le_fullEnergy A B hD x y

/-- **Order independence of exact corona reduction.** Eliminating either hidden block first yields
the same final boundary energy. -/
theorem successiveElimination_order_independent
    {X Y Z : Type*} {energy : X → Y → Z → ℝ}
    {middleYZ : X → Y → ℝ} {middleZY : X → Z → ℝ}
    {left right : X → ℝ}
    (hZ : ∀ x y, IsExactElimination (fun _ : Unit => energy x y)
      (fun _ : Unit => middleYZ x y))
    (hYafterZ : IsExactElimination middleYZ left)
    (hY : ∀ x z, IsExactElimination (fun _ : Unit => fun y => energy x y z)
      (fun _ : Unit => middleZY x z))
    (hZafterY : IsExactElimination middleZY right) :
    left = right := by
  apply exactElimination_unique (IsExactElimination.comp hZ hYafterZ)
  have hright : IsExactElimination (fun x (zy : Z × Y) => energy x zy.2 zy.1) right :=
    IsExactElimination.comp hY hZafterY
  exact {
    left := fun x => by
      obtain ⟨zy, hzy⟩ := hright.1 x
      exact ⟨(zy.2, zy.1), hzy⟩
    right := fun x yz => hright.2 x (yz.2, yz.1) }

end
end CoronaSchur
end IrregularStokes
end GaloisForLFunctions
