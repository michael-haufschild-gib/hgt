import GaloisForLFunctions.HTGeometry.LpInjectionCompression
import GaloisForLFunctions.HTGeometry.PaperConvergentDiagonal

/-! # Full two-channel corners preserve the compact quotient

The corner `U₀ T U₁*` is square-zero. Isometric coordinate injections and
contractive compressions nevertheless preserve its operator norm, compactness
and exact distance from the compact ideal, allowing arbitrary mixing corrections.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open RHTower

abbrev PaperCornerSource := lp (fun _ : ℕ => ℂ) 2
abbrev PaperCornerSpace := lp (fun _ : ℕ × Fin 2 => ℂ) 2

def paperCornerInjection (b : Fin 2) : PaperCornerSource →ₗᵢ[ℂ] PaperCornerSpace :=
  lpScalarInjection (fun j => (j, b)) (fun _ _ h => congrArg Prod.fst h)

def paperCornerPullback (b : Fin 2) : PaperCornerSpace →L[ℂ] PaperCornerSource :=
  lpCoordinatePullback (fun j => (j, b)) (fun _ _ h => congrArg Prod.fst h)

@[simp] theorem paperCornerPullback_apply (b : Fin 2) (x : PaperCornerSpace) (j : ℕ) :
    paperCornerPullback b x j = x (j, b) := rfl

theorem paperCornerInjection_apply (b c : Fin 2) (x : PaperCornerSource) (j : ℕ) :
    paperCornerInjection b x (j, c) = if c = b then x j else 0 := by
  classical
  by_cases h : c = b
  · subst c
    simpa [paperCornerInjection] using
      lpScalarInjection_coordinate (fun k => (k, b)) (fun _ _ he => congrArg Prod.fst he) x j
  · rw [if_neg h]
    have hz : paperCornerPullback b (lp.single 2 (j, c) (1 : ℂ)) = 0 := by
      ext k
      simp [paperCornerPullback_apply, lp.single_apply, Prod.mk.injEq, Ne.symm h]
    have he := ContinuousLinearMap.adjoint_inner_left
      (paperCornerInjection b).toContinuousLinearMap x (lp.single 2 (j, c) (1 : ℂ))
    dsimp only [paperCornerInjection] at he
    rw [← lpCoordinatePullback_eq_adjoint_lpScalarInjection] at he
    change inner ℂ (paperCornerPullback b (lp.single 2 (j, c) (1 : ℂ))) x = _ at he
    rw [hz, inner_zero_left, lp.inner_single_left] at he
    simpa [paperCornerInjection] using he.symm

@[simp] theorem paperCornerPullback_injection (b c : Fin 2) (x : PaperCornerSource) :
    paperCornerPullback b (paperCornerInjection c x) = if b = c then x else 0 := by
  ext j
  simp [paperCornerInjection_apply]
  split_ifs <;> rfl

theorem paperCornerPullback_norm_le (b : Fin 2) (x : PaperCornerSpace) :
    ‖paperCornerPullback b x‖ ≤ ‖x‖ :=
  lpCoordinatePullbackLinear_norm_le (fun j => (j, b))
    (fun _ _ h => congrArg Prod.fst h) x

def paperHilbertOffDiagonal (T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    PaperCornerSpace →L[ℂ] PaperCornerSpace :=
  (paperCornerInjection 0).toContinuousLinearMap.comp (T.comp (paperCornerPullback 1))

def paperHilbertCornerCompression (T : PaperCornerSpace →L[ℂ] PaperCornerSpace) :
    PaperCornerSource →L[ℂ] PaperCornerSource :=
  (paperCornerPullback 0).comp (T.comp (paperCornerInjection 1).toContinuousLinearMap)

@[simp] theorem paperHilbertOffDiagonal_source
    (T : PaperCornerSource →L[ℂ] PaperCornerSource) (x : PaperCornerSource) :
    paperHilbertOffDiagonal T (paperCornerInjection 1 x) = paperCornerInjection 0 (T x) := by
  simp [paperHilbertOffDiagonal]

@[simp] theorem paperHilbertOffDiagonal_target
    (T : PaperCornerSource →L[ℂ] PaperCornerSource) (x : PaperCornerSource) :
    paperHilbertOffDiagonal T (paperCornerInjection 0 x) = 0 := by
  simp [paperHilbertOffDiagonal]

theorem paperHilbertOffDiagonal_sq (T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    paperHilbertOffDiagonal T ^ 2 = 0 := by
  ext x : 1
  change paperHilbertOffDiagonal T
    (paperCornerInjection 0 (T (paperCornerPullback 1 x))) = 0
  exact paperHilbertOffDiagonal_target T _

@[simp] theorem paperHilbertCornerCompression_offDiagonal
    (T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    paperHilbertCornerCompression (paperHilbertOffDiagonal T) = T := by
  ext x : 1
  simp [paperHilbertCornerCompression]

theorem paperHilbertOffDiagonal_norm_le (T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    ‖paperHilbertOffDiagonal T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖paperCornerInjection 0 (T (paperCornerPullback 1 x))‖ ≤ _
  rw [(paperCornerInjection 0).norm_map]
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (paperCornerPullback_norm_le 1 x) (norm_nonneg T))

theorem paperHilbertCornerCompression_norm_le (T : PaperCornerSpace →L[ℂ] PaperCornerSpace) :
    ‖paperHilbertCornerCompression T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (paperCornerPullback_norm_le 0 (T (paperCornerInjection 1 x))).trans
  simpa using T.le_opNorm (paperCornerInjection 1 x)

theorem paperHilbertOffDiagonal_norm (T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    ‖paperHilbertOffDiagonal T‖ = ‖T‖ := by
  apply le_antisymm (paperHilbertOffDiagonal_norm_le T)
  simpa using paperHilbertCornerCompression_norm_le (paperHilbertOffDiagonal T)

theorem paperHilbertCornerCompression_compact
    (T : compactOperatorStarAlgebra PaperCornerSpace) :
    IsCompactOperator (paperHilbertCornerCompression T.1) :=
  (T.2.comp_clm (paperCornerInjection 1).toContinuousLinearMap).clm_comp (paperCornerPullback 0)

theorem paperHilbertOffDiagonal_compact_iff (T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    IsCompactOperator (paperHilbertOffDiagonal T) ↔ IsCompactOperator T := by
  constructor
  · intro h
    simpa using paperHilbertCornerCompression_compact ⟨paperHilbertOffDiagonal T, h⟩
  · intro h
    exact (h.comp_clm (paperCornerPullback 1)).clm_comp
      (paperCornerInjection 0).toContinuousLinearMap

theorem paperHilbertOffDiagonal_sub (S T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    paperHilbertOffDiagonal (S - T) = paperHilbertOffDiagonal S - paperHilbertOffDiagonal T := by
  ext x : 1
  simp [paperHilbertOffDiagonal]

theorem paperHilbertCornerCompression_sub (S T : PaperCornerSpace →L[ℂ] PaperCornerSpace) :
    paperHilbertCornerCompression (S - T) =
      paperHilbertCornerCompression S - paperHilbertCornerCompression T := by
  ext x : 1
  simp [paperHilbertCornerCompression]

theorem paperHilbertOffDiagonal_compactIdealDistance
    (T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    compactIdealDistance (paperHilbertOffDiagonal T) = compactIdealDistance T := by
  apply le_antisymm
  · apply le_compactIdealDistance
    intro K hK
    have h := compactIdealDistance_le (paperHilbertOffDiagonal T) (paperHilbertOffDiagonal K)
      ((paperHilbertOffDiagonal_compact_iff K).mpr hK)
    simpa only [← paperHilbertOffDiagonal_sub, paperHilbertOffDiagonal_norm] using h
  · apply le_compactIdealDistance
    intro K hK
    calc
      compactIdealDistance T ≤ ‖T - paperHilbertCornerCompression K‖ :=
        compactIdealDistance_le T _ (paperHilbertCornerCompression_compact ⟨K, hK⟩)
      _ ≤ ‖paperHilbertOffDiagonal T - K‖ := by
        simpa only [paperHilbertCornerCompression_sub, paperHilbertCornerCompression_offDiagonal]
          using paperHilbertCornerCompression_norm_le (paperHilbertOffDiagonal T - K)

theorem paperHilbertOffDiagonal_traceCost (T : PaperCornerSource →L[ℂ] PaperCornerSource) :
    compactOperatorTraceCost PaperCornerSpace (paperHilbertOffDiagonal T) =
      compactOperatorTraceCost PaperCornerSource T := by
  rw [compactOperatorTraceCost_eq, compactOperatorTraceCost_eq]
  by_cases h : IsCompactOperator T
  · rw [if_pos h, if_pos ((paperHilbertOffDiagonal_compact_iff T).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((paperHilbertOffDiagonal_compact_iff T).mp hc))]

end
end GaloisForLFunctions.HTGeometry
