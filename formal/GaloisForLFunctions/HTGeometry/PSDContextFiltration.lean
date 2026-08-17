import GaloisForLFunctions.HTGeometry.ContextOrderPSDHierarchy
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Positive-semidefinite context filtration

For tolerance `ε`, a nonempty context is a face when its principal kernel plus `ε I` is positive
semidefinite. These faces form a genuine pre-abstract simplicial complex and grow monotonically
with tolerance. For the balanced all-order anomaly, the full context enters exactly at its spectral
margin.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Set Finset
open scoped ComplexOrder

noncomputable section

/-- Canonical embedding of a finite subface into a containing face. -/
def faceInclusion {I : Type*} {S T : Finset I} (hTS : T ⊆ S) : T ↪ S where
  toFun x := ⟨x.1, hTS x.2⟩
  inj' _ _ h := Subtype.ext (congrArg (fun z : S => (z : I)) h)

/-- **PSD context complex.** Nonempty faces whose shifted principal kernel is PSD. -/
def psdContextFiltration {I : Type*} [Fintype I] [DecidableEq I]
    (K : Matrix I I ℂ) (ε : ℝ) : PreAbstractSimplicialComplex I where
  faces := {S | S.Nonempty ∧
    (K.submatrix (fun x : S => x.1) (fun x : S => x.1) + ((ε : ℂ) • 1)).PosSemidef}
  isRelLowerSet_faces := by
    intro S hS
    refine ⟨hS.1, ?_⟩
    intro T hTS hT
    refine ⟨hT, ?_⟩
    let e : T ↪ S := faceInclusion hTS
    have hsub := hS.2.submatrix e
    have heq :
        (K.submatrix (fun x : S => x.1) (fun x : S => x.1) + ((ε : ℂ) • 1)).submatrix e e =
          K.submatrix (fun x : T => x.1) (fun x : T => x.1) + ((ε : ℂ) • 1) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.submatrix_apply]
        change K (i : I) (i : I) = K (i : I) (i : I)
        rfl
      · simp [Matrix.submatrix_apply, hij, e, faceInclusion]
    rwa [heq] at hsub

/-- **Filtration monotonicity.** Increasing tolerance can only add admissible faces. -/
theorem psdContextFiltration_mono {I : Type*} [Fintype I] [DecidableEq I]
    (K : Matrix I I ℂ) {ε η : ℝ} (hεη : ε ≤ η) :
    psdContextFiltration K ε ≤ psdContextFiltration K η := by
  intro S hS
  refine ⟨hS.1, ?_⟩
  have hdelta : (0 : ℂ) ≤ ((η - ε : ℝ) : ℂ) := by
    rw [Complex.nonneg_iff]
    exact ⟨sub_nonneg.mpr hεη, by simp⟩
  have hadd := hS.2.add (Matrix.PosSemidef.one.smul hdelta)
  convert hadd using 1
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    ring
  · simp [hij]

/-- Noise threshold at which the balanced full context enters its PSD filtration. -/
def balancedContextNoiseThreshold (r : ℕ) : ℝ := balancedContextMargin r

/-- Additive noise shift of the balanced context kernel. -/
def noiseShiftedBalancedContextKernel (r : ℕ) (ε : Set.Ici (0 : ℝ)) :
    Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ :=
  contextOrderKernel (balancedContextScale r) + (((ε : ℝ) : ℂ) • 1)

/-- Orthogonal decomposition of the noise-shifted balanced kernel. -/
theorem noiseShiftedBalancedContextKernel_decomposition (r : ℕ) (ε : Set.Ici (0 : ℝ)) :
    noiseShiftedBalancedContextKernel r ε =
      (((1 + balancedContextScale r + (ε : ℝ) : ℝ) : ℂ) •
          (1 - _root_.HTGeometry.simplexEffectiveHarmonicProjection)) +
        (((ε : ℝ) - balancedContextMargin r : ℝ) : ℂ) •
          _root_.HTGeometry.simplexEffectiveHarmonicProjection := by
  rw [noiseShiftedBalancedContextKernel, contextOrderKernel_decomposition,
    balancedContext_global_coefficient]
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  ring

/-- **Exact filtration entry time.** The full balanced context is PSD exactly when additive noise
reaches its spectral margin. -/
theorem noiseShiftedBalancedContextKernel_posSemidef_iff (r : ℕ) (ε : Set.Ici (0 : ℝ)) :
    (noiseShiftedBalancedContextKernel r ε).PosSemidef ↔
      balancedContextNoiseThreshold r ≤ (ε : ℝ) := by
  rw [balancedContextNoiseThreshold]
  constructor
  · intro h
    have hq := h.dotProduct_mulVec_nonneg
      (_root_.HTGeometry.simplexEffectiveSection : Fin (r + 3) → ℂ)
    have haction :
        noiseShiftedBalancedContextKernel r ε *ᵥ
            _root_.HTGeometry.simplexEffectiveSection =
          (((ε : ℝ) - balancedContextMargin r : ℝ) : ℂ) •
            _root_.HTGeometry.simplexEffectiveSection := by
      rw [noiseShiftedBalancedContextKernel_decomposition]
      let P := _root_.HTGeometry.simplexEffectiveHarmonicProjection (ι := Fin (r + 3))
      let s := _root_.HTGeometry.simplexEffectiveSection (ι := Fin (r + 3))
      have hP : P *ᵥ s = s :=
        _root_.HTGeometry.simplexEffectiveHarmonicProjection_mulVec_section
      have hcomp : (1 - P) *ᵥ s = 0 := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hP]
        simp
      change (((((1 + balancedContextScale r + (ε : ℝ) : ℝ) : ℂ) • (1 - P)) +
          ((((ε : ℝ) - balancedContextMargin r : ℝ) : ℂ) • P)) *ᵥ s) = _
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hcomp, hP]
      simp [s]
    rw [haction] at hq
    have hqR := (Complex.nonneg_iff.mp hq).1
    simp [dotProduct, _root_.HTGeometry.simplexEffectiveSection] at hqR
    have hcard : 0 < (r : ℝ) + 3 := by positivity
    have hprod : 0 ≤ ((r : ℝ) + 3) * ((ε : ℝ) - balancedContextMargin r) := by
      rw [mul_sub]
      exact sub_nonneg.mpr hqR
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hcard).mp hprod)
  · intro hε
    rw [noiseShiftedBalancedContextKernel_decomposition]
    apply Matrix.PosSemidef.add
    · apply _root_.HTGeometry.one_sub_simplexEffectiveHarmonicProjection_posSemidef.smul
      rw [Complex.nonneg_iff]
      refine ⟨?_, by simp⟩
      have hnonneg : 0 ≤ (ε : ℝ) := ε.property
      have hs := balancedContextScale_nonneg r
      norm_num
      exact add_nonneg (add_nonneg zero_le_one hs) hnonneg
    · apply _root_.HTGeometry.simplexEffectiveHarmonicProjection_posSemidef.smul
      rw [Complex.nonneg_iff]
      exact ⟨sub_nonneg.mpr hε, by simp⟩

end

end GaloisForLFunctions.HTGeometry
