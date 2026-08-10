import GaloisForLFunctions.HTGeometry.OperatorSystemLevelNorm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Order

/-!
# `C(X, ℂ)` as an operator system

The abstract matrix-ordering layer is instantiated here by its motivating example: a matrix over
`C(X, ℂ)` is declared positive when it is pointwise positive semidefinite.

* `isMatrixOrdering_cstarCone` — this is a matrix ordering; the compression axiom is exactly
  `Matrix.PosSemidef.conjTranspose_mul_mul_same` applied pointwise, once one knows that the
  module-valued compression evaluates to the scalar one (`compress_eval`);
* `isOrderUnitLevelOne_one` — the constant function `1` is an order unit for the scalar level.

Together with `isMatrixOrderUnit_of_levelOne` this makes `C(X, ℂ)` an operator system with
Archimedean matrix order unit `1`, and `levelNorm` at the scalar level is the sup-norm.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Matrix MatrixModule

open scoped ComplexOrder

universe u

variable {X : Type*} [TopologicalSpace X]

/-- A matrix over `C(X, ℂ)` is positive when it is pointwise positive semidefinite. -/
def cstarCone (X : Type*) [TopologicalSpace X] :
    ∀ (n : Type u) [Fintype n], Set (Matrix n n C(X, ℂ)) :=
  fun _ _ => {x | ∀ p : X, (Matrix.of fun i j => x i j p).PosSemidef}

/-- The module-valued compression evaluates to the scalar compression. -/
theorem compress_eval {m n : Type u} [Fintype m] (α : Matrix m n ℂ) (x : Matrix m m C(X, ℂ))
    (i j : n) (p : X) :
    (compress α x) i j p = (αᴴ * (Matrix.of fun a b => x a b p) * α) i j := by
  rw [compress_apply]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **Pointwise positive semidefiniteness is a matrix ordering.** -/
theorem isMatrixOrdering_cstarCone (X : Type*) [TopologicalSpace X] :
    IsMatrixOrdering (cstarCone.{u} X) where
  isSelfAdjoint := by
    intro n _ x hx
    ext i j p
    have h := (hx p).1
    have h2 := congrFun (congrFun h i) j
    simpa [Matrix.conjTranspose_apply] using h2
  zero_mem := by
    intro n _ p
    have hz : (Matrix.of fun i j => (0 : Matrix n n C(X, ℂ)) i j p) = (0 : Matrix n n ℂ) := by
      ext i j; simp
    rw [hz]
    exact Matrix.PosSemidef.zero
  add_mem := by
    intro n _ x hx y hy p
    have := (hx p).add (hy p)
    convert this using 1
    ext i j
    simp
  compress_mem := by
    intro m n _ _ α x hx p
    have hpsd := (hx p).conjTranspose_mul_mul_same α
    convert hpsd using 1
    ext i j
    simpa using compress_eval α x i j p

/-- Positivity at the scalar level is pointwise nonnegativity. -/
theorem levelOne_cstarCone_iff {u : C(X, ℂ)} :
    LevelOne (cstarCone.{u} X) u ↔ ∀ p : X, (0 : ℂ) ≤ u p := by
  constructor
  · intro h p
    have hthis := h p
    simp only [Matrix.of_apply] at hthis
    have hd : (Matrix.of fun _ _ : PUnit.{u + 1} => u p)
        = Matrix.diagonal (fun _ : PUnit.{u + 1} => u p) := by
      ext a b
      simp [Subsingleton.elim a b]
    rw [hd, Matrix.posSemidef_diagonal_iff] at hthis
    exact hthis default
  · intro h p
    simp only [Matrix.of_apply]
    have hd : (Matrix.of fun _ _ : PUnit.{u + 1} => u p)
        = Matrix.diagonal (fun _ : PUnit.{u + 1} => u p) := by
      ext a b
      simp [Subsingleton.elim a b]
    rw [hd]
    exact Matrix.PosSemidef.diagonal fun _ => h p

/-- **The constant function `1` is an order unit for the scalar level.** -/
theorem isOrderUnitLevelOne_one (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    IsOrderUnitLevelOne (cstarCone.{u} X) (1 : C(X, ℂ)) where
  pos := by
    rw [levelOne_cstarCone_iff]
    intro p
    simp
  bound := by
    intro v hv
    have hvim : ∀ p : X, (v p).im = 0 := by
      intro p
      have := congrFun (congrArg (fun f : C(X, ℂ) => (f : X → ℂ)) hv) p
      simp only [ContinuousMap.star_apply, Complex.star_def] at this
      have h2 := congrArg Complex.im this
      simp only [Complex.conj_im] at h2
      linarith
    have hvre : ∀ p : X, |(v p).re| ≤ ‖v‖ := by
      intro p
      have h1 : |(v p).re| ≤ ‖v p‖ := Complex.abs_re_le_norm _
      exact h1.trans (v.norm_coe_le_norm p)
    refine ⟨‖v‖ + 1, by positivity, ?_, ?_⟩
    · rw [levelOne_cstarCone_iff]
      intro p
      rw [Complex.le_def]
      have hp : ((((‖v‖ + 1 : ℝ)) : ℂ) • (1 : C(X, ℂ)) - v) p = ((‖v‖ + 1 : ℝ) : ℂ) - v p := by
        simp
      rw [hp]
      have h1 := hvre p
      rw [abs_le] at h1
      constructor
      · simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re]
        linarith [h1.2]
      · simp [hvim p]
    · rw [levelOne_cstarCone_iff]
      intro p
      rw [Complex.le_def]
      have hp : ((((‖v‖ + 1 : ℝ)) : ℂ) • (1 : C(X, ℂ)) + v) p = ((‖v‖ + 1 : ℝ) : ℂ) + v p := by
        simp
      rw [hp]
      have h1 := hvre p
      rw [abs_le] at h1
      constructor
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re]
        linarith [h1.1]
      · simp [hvim p]

/-! ## The scalar level norm is the sup-norm -/

theorem levelBounds_cstarCone [CompactSpace X] {f : C(X, ℂ)} (hf : star f = f) :
    levelBounds (cstarCone.{u} X) (1 : C(X, ℂ)) PUnit.{u + 1} (Matrix.of fun _ _ => f)
      = {t : ℝ | 0 < t ∧ ‖f‖ ≤ t} := by
  have hfim : ∀ p : X, (f p).im = 0 := by
    intro p
    have h := congrFun (congrArg (fun g : C(X, ℂ) => (g : X → ℂ)) hf) p
    simp only [ContinuousMap.star_apply, Complex.star_def] at h
    have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    linarith
  have hsub : ∀ t : ℝ, ((t : ℂ) • amplifyUnit PUnit.{u + 1} (1 : C(X, ℂ))
      - (Matrix.of fun _ _ => f)) = Matrix.of fun _ _ => ((t : ℂ) • (1 : C(X, ℂ)) - f) := by
    intro t
    ext a b
    simp [amplifyUnit_apply, Subsingleton.elim a b]
  have hadd : ∀ t : ℝ, ((t : ℂ) • amplifyUnit PUnit.{u + 1} (1 : C(X, ℂ))
      + (Matrix.of fun _ _ => f)) = Matrix.of fun _ _ => ((t : ℂ) • (1 : C(X, ℂ)) + f) := by
    intro t
    ext a b
    simp [amplifyUnit_apply, Subsingleton.elim a b]
  ext t
  simp only [levelBounds, Set.mem_setOf_eq, hsub t, hadd t]
  constructor
  · rintro ⟨ht, h1, h2⟩
    refine ⟨ht, ?_⟩
    rw [ContinuousMap.norm_le _ ht.le]
    intro p
    have hp1 : (0 : ℂ) ≤ ((t : ℂ) • (1 : C(X, ℂ)) - f) p := (levelOne_cstarCone_iff.mp h1) p
    have hp2 : (0 : ℂ) ≤ ((t : ℂ) • (1 : C(X, ℂ)) + f) p := (levelOne_cstarCone_iff.mp h2) p
    rw [Complex.le_def] at hp1 hp2
    simp only [Complex.zero_re, Complex.zero_im] at hp1 hp2
    have e1 : (((t : ℂ) • (1 : C(X, ℂ)) - f) p).re = t - (f p).re := by simp
    have e2 : (((t : ℂ) • (1 : C(X, ℂ)) + f) p).re = t + (f p).re := by simp
    rw [e1] at hp1
    rw [e2] at hp2
    have hnorm : ‖f p‖ = |(f p).re| := by
      have hval : f p = ((f p).re : ℂ) := by
        apply Complex.ext <;> simp [hfim p]
      conv_lhs => rw [hval]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_le]
    constructor <;> [linarith [hp2.1]; linarith [hp1.1]]
  · rintro ⟨ht, hle⟩
    refine ⟨ht, ?_, ?_⟩
    · refine levelOne_cstarCone_iff.mpr ?_
      intro p
      rw [Complex.le_def]
      have hb : ‖f p‖ ≤ t := (f.norm_coe_le_norm p).trans hle
      have hre : |(f p).re| ≤ t := (Complex.abs_re_le_norm _).trans hb
      rw [abs_le] at hre
      constructor
      · simp only [Complex.zero_re, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
          ContinuousMap.one_apply, smul_eq_mul, mul_one, Complex.sub_re, Complex.ofReal_re]
        linarith [hre.2]
      · simp [hfim p]
    · refine levelOne_cstarCone_iff.mpr ?_
      intro p
      rw [Complex.le_def]
      have hb : ‖f p‖ ≤ t := (f.norm_coe_le_norm p).trans hle
      have hre : |(f p).re| ≤ t := (Complex.abs_re_le_norm _).trans hb
      rw [abs_le] at hre
      constructor
      · simp only [Complex.zero_re, ContinuousMap.add_apply, ContinuousMap.smul_apply,
          ContinuousMap.one_apply, smul_eq_mul, mul_one, Complex.add_re, Complex.ofReal_re]
        linarith [hre.1]
      · simp [hfim p]

/-- **The scalar level norm of the operator system `C(X, ℂ)` is the sup-norm.** -/
theorem levelNorm_cstarCone [CompactSpace X] {f : C(X, ℂ)} (hf : star f = f) :
    levelNorm (cstarCone.{u} X) (1 : C(X, ℂ)) PUnit.{u + 1} (Matrix.of fun _ _ => f) = ‖f‖ := by
  rw [levelNorm, levelBounds_cstarCone hf]
  have hne : ({t : ℝ | 0 < t ∧ ‖f‖ ≤ t}).Nonempty :=
    ⟨‖f‖ + 1, by positivity, by linarith⟩
  refine le_antisymm ?_ (le_csInf hne fun t ht => ht.2)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact csInf_le ⟨0, fun t ht => ht.1.le⟩ ⟨by positivity, by linarith⟩

/-- **`C(X, ℂ)` is an operator system.**  Every self-adjoint matrix over `C(X, ℂ)` is dominated on
both sides by a multiple of the amplified unit. -/
theorem exists_amplifyUnit_bound_cstarCone (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (n : Type u) [Fintype n] [DecidableEq n] (x : Matrix n n C(X, ℂ)) (hx : xᴴ = x) :
    ∃ T : ℝ, 0 < T ∧ (T : ℂ) • amplifyUnit n (1 : C(X, ℂ)) - x ∈ cstarCone.{u} X n ∧
      (T : ℂ) • amplifyUnit n (1 : C(X, ℂ)) + x ∈ cstarCone.{u} X n :=
  (isMatrixOrdering_cstarCone X).isMatrixOrderUnit_of_levelOne (isOrderUnitLevelOne_one X) x hx

end ShilovLocal

end GaloisForLFunctions.HTGeometry
