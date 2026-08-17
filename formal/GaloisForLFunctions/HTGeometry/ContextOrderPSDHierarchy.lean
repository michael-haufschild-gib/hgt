import GaloisForLFunctions.HTGeometry.SimplexEffectiveHarmonic

/-!
# Strict context-order positivity hierarchy

For every order `N ≥ 3`, this file gives an explicit normalized Hermitian kernel whose restriction
to every maximal proper context is positive semidefinite while the full kernel is not.  The balanced
scale makes the local and global constant-line margins equal and opposite.

The proof is an exact harmonic decomposition.  It uses the orthogonal projections onto the constant
section and its complement already provided by `SimplexEffectiveHarmonic`; no diagonalization,
probability, source model, numerical computation, or physical hypothesis occurs.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

/-- Equality-pattern context kernel: diagonal `1`, every off-diagonal entry `-t`. -/
def contextOrderKernel {ι : Type*} [DecidableEq ι] (t : ℝ) : Matrix ι ι ℂ :=
  fun i j => if i = j then 1 else -(t : ℂ)

/-- Exact decomposition into the constant harmonic line and its orthogonal complement. -/
theorem contextOrderKernel_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℝ) :
    contextOrderKernel (ι := ι) t =
      ((1 + t : ℝ) : ℂ) •
          (1 - _root_.HTGeometry.simplexEffectiveHarmonicProjection) +
        ((1 - ((Fintype.card ι : ℝ) - 1) * t : ℝ) : ℂ) •
          _root_.HTGeometry.simplexEffectiveHarmonicProjection := by
  have hnR : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext i j
  by_cases hij : i = j
  · subst j
    simp [contextOrderKernel, _root_.HTGeometry.simplexEffectiveHarmonicProjection]
    field_simp
    ring
  · simp [contextOrderKernel, _root_.HTGeometry.simplexEffectiveHarmonicProjection, hij]
    field_simp
    ring

/-- Balanced coherence scale for the order `r+3` globality fracture. -/
def balancedContextScale (r : ℕ) : ℝ := 2 / (2 * (r : ℝ) + 3)

/-- Equal local/global constant-line margin at the balanced scale. -/
def balancedContextMargin (r : ℕ) : ℝ := 1 / (2 * (r : ℝ) + 3)

theorem balancedContextMargin_pos (r : ℕ) : 0 < balancedContextMargin r := by
  unfold balancedContextMargin
  positivity

theorem balancedContextScale_nonneg (r : ℕ) : 0 ≤ balancedContextScale r := by
  unfold balancedContextScale
  positivity

/-- A maximal proper context has exact positive constant-line margin. -/
theorem balancedContext_local_coefficient (r : ℕ) :
    1 - (((Fintype.card (Fin (r + 2)) : ℝ) - 1) * balancedContextScale r) =
      balancedContextMargin r := by
  simp [balancedContextScale, balancedContextMargin]
  field_simp
  ring

/-- The full context has the equal and opposite constant-line margin. -/
theorem balancedContext_global_coefficient (r : ℕ) :
    1 - (((Fintype.card (Fin (r + 3)) : ℝ) - 1) * balancedContextScale r) =
      -balancedContextMargin r := by
  simp [balancedContextScale, balancedContextMargin]
  field_simp
  ring

/-- Every canonical maximal proper context is positive semidefinite. -/
theorem balancedContext_local_posSemidef (r : ℕ) :
    (contextOrderKernel (ι := Fin (r + 2)) (balancedContextScale r)).PosSemidef := by
  rw [contextOrderKernel_decomposition, balancedContext_local_coefficient]
  apply Matrix.PosSemidef.add
  · apply _root_.HTGeometry.one_sub_simplexEffectiveHarmonicProjection_posSemidef.smul
    rw [Complex.nonneg_iff]
    exact ⟨by
      have hs := balancedContextScale_nonneg r
      dsimp
      linarith, by simp⟩
  · apply _root_.HTGeometry.simplexEffectiveHarmonicProjection_posSemidef.smul
    rw [Complex.nonneg_iff]
    exact ⟨(balancedContextMargin_pos r).le, by simp⟩

/-- Equality-pattern kernels are unchanged by injective reindexing. -/
theorem contextOrderKernel_submatrix {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (t : ℝ) (e : κ ↪ ι) :
    (contextOrderKernel (ι := ι) t).submatrix e e = contextOrderKernel (ι := κ) t := by
  ext i j
  simp [Matrix.submatrix_apply, contextOrderKernel, e.injective.eq_iff]

/-- Every maximal proper context, not merely the leading one, is positive semidefinite. -/
theorem balancedContext_every_maximalProperContext_posSemidef (r : ℕ)
    (e : Fin (r + 2) ↪ Fin (r + 3)) :
    ((contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)).submatrix e e).PosSemidef := by
  rw [contextOrderKernel_submatrix]
  exact balancedContext_local_posSemidef r

/-- Every subface of every maximal proper context is positive semidefinite. -/
theorem balancedContext_every_subface_posSemidef {κ : Type*} (r : ℕ)
    (e : Fin (r + 2) ↪ Fin (r + 3)) (f : κ → Fin (r + 2)) :
    ((contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)).submatrix
      (fun x => e (f x)) (fun x => e (f x))).PosSemidef := by
  have h := (balancedContext_every_maximalProperContext_posSemidef r e).submatrix f
  have heq :
      ((contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)).submatrix e e).submatrix f f =
        (contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)).submatrix
          (fun x => e (f x)) (fun x => e (f x)) := by
    ext i j
    rfl
  rw [heq] at h
  exact h

/-- Exact positive local action on the constant section. -/
theorem balancedContext_local_section_action (r : ℕ) :
    contextOrderKernel (ι := Fin (r + 2)) (balancedContextScale r) *ᵥ
        _root_.HTGeometry.simplexEffectiveSection =
      (balancedContextMargin r : ℝ) • _root_.HTGeometry.simplexEffectiveSection := by
  rw [contextOrderKernel_decomposition, balancedContext_local_coefficient]
  let P := _root_.HTGeometry.simplexEffectiveHarmonicProjection (ι := Fin (r + 2))
  let s := _root_.HTGeometry.simplexEffectiveSection (ι := Fin (r + 2))
  have hP : P *ᵥ s = s :=
    _root_.HTGeometry.simplexEffectiveHarmonicProjection_mulVec_section
  have hcomp : (1 - P) *ᵥ s = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hP]
    simp
  change (((((1 + balancedContextScale r : ℝ) : ℂ) • (1 - P)) +
      ((balancedContextMargin r : ℝ) : ℂ) • P) *ᵥ s) =
        ((balancedContextMargin r : ℝ) : ℂ) • s
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hcomp, hP]
  simp

/-- Exact negative global action on the same constant section. -/
theorem balancedContext_global_section_action (r : ℕ) :
    contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r) *ᵥ
        _root_.HTGeometry.simplexEffectiveSection =
      (-balancedContextMargin r : ℝ) • _root_.HTGeometry.simplexEffectiveSection := by
  rw [contextOrderKernel_decomposition, balancedContext_global_coefficient]
  let P := _root_.HTGeometry.simplexEffectiveHarmonicProjection (ι := Fin (r + 3))
  let s := _root_.HTGeometry.simplexEffectiveSection (ι := Fin (r + 3))
  have hP : P *ᵥ s = s :=
    _root_.HTGeometry.simplexEffectiveHarmonicProjection_mulVec_section
  have hcomp : (1 - P) *ᵥ s = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hP]
    simp
  change (((((1 + balancedContextScale r : ℝ) : ℂ) • (1 - P)) +
      ((-balancedContextMargin r : ℝ) : ℂ) • P) *ᵥ s) =
        ((-balancedContextMargin r : ℝ) : ℂ) • s
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hcomp, hP]
  simp

/-- **Unconditional all-order globality fracture.**  At every order `r+3`, every proper maximal
context is positive semidefinite, but the full occurrence-identified kernel is not. -/
theorem balancedContext_global_not_posSemidef (r : ℕ) :
    ¬ (contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)).PosSemidef := by
  intro h
  have hq := h.dotProduct_mulVec_nonneg
    (_root_.HTGeometry.simplexEffectiveSection : Fin (r + 3) → ℂ)
  rw [balancedContext_global_section_action] at hq
  simp [dotProduct, _root_.HTGeometry.simplexEffectiveSection] at hq
  have hqR := (Complex.nonpos_iff.mp hq).1
  simp at hqR
  have hm := balancedContextMargin_pos r
  have hcard : (0 : ℝ) < (r : ℝ) + 3 := by positivity
  exact (not_le_of_gt (mul_pos hcard hm)) hqR

end

end GaloisForLFunctions.HTGeometry
