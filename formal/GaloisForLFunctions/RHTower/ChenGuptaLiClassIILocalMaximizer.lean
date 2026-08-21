/-
# Chen--Gupta--Li Class-II local critical-line maximizer

Chen--Gupta--Li Section 12.2 selects, near each Class-II zero ordinate, an
ordinate where the critical-line Dirichlet L-value is maximal.  This module
constructs that maximizer on every closed finite local interval and packages
it as the existing CGL character/ordinate row.  The later estimate turning a
large source Mellin integral into a quantitative lower bound at this row is
not assumed or claimed here.

No RH, GRH, zero-density, zero-detection, large-value, fourth-moment, or
continuity premise is supplied by callers.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveZeroPartition
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIICriticalLine

open Complex Topology

noncomputable section

namespace RHTower

/-- A critical-line point is never the pole `1` of a Dirichlet L-function. -/
theorem cglCriticalLinePoint_ne_one (t : ℝ) : (cglCriticalLinePoint t).1 ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [cglCriticalLinePoint] at hre

/-- The critical-line L-value along every real translate is continuous. -/
theorem continuous_cglCriticalLineLValue
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) :
    Continuous fun u : ℝ =>
      DirichletCharacter.LFunction χ (cglCriticalLinePoint (t + u)).1 := by
  have harg : Continuous fun u : ℝ => ((cglCriticalLinePoint (t + u)).1 : ℂ) := by
    change Continuous fun u : ℝ => (1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I
    fun_prop
  rw [continuous_iff_continuousAt]
  intro u
  have hL : ContinuousAt (DirichletCharacter.LFunction χ)
      ((cglCriticalLinePoint (t + u)).1 : ℂ) :=
    (DirichletCharacter.differentiableAt_LFunction χ
      ((cglCriticalLinePoint (t + u)).1 : ℂ)
      (Or.inl (cglCriticalLinePoint_ne_one (t + u)))).continuousAt
  have hargAt : ContinuousAt (fun v : ℝ =>
      ((cglCriticalLinePoint (t + v)).1 : ℂ)) u := harg.continuousAt
  simpa only [Function.comp_def] using
    hL.comp (f := fun v : ℝ => ((cglCriticalLinePoint (t + v)).1 : ℂ)) hargAt

/-- Certified offset interval used for the local Class-II L-value maximum. -/
def CGLClassIICriticalLineLocalOffset (B : NNReal) := Set.Icc (-((B : ℝ))) (B : ℝ)

/-- A maximum of the critical-line L-value norm exists on every source-style
closed local interval. -/
theorem exists_cglClassIICriticalLineLocalMaximizer
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) (B : NNReal) :
    ∃ u : CGLClassIICriticalLineLocalOffset B,
      IsMaxOn (fun v : ℝ =>
        ‖DirichletCharacter.LFunction χ (cglCriticalLinePoint (t + v)).1‖)
        (CGLClassIICriticalLineLocalOffset B) u := by
  have hcompact : IsCompact (CGLClassIICriticalLineLocalOffset B) := isCompact_Icc
  have hnonempty : (CGLClassIICriticalLineLocalOffset B).Nonempty := by
    refine ⟨0, ?_⟩
    simp [CGLClassIICriticalLineLocalOffset]
  obtain ⟨u, hu, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    (continuous_cglCriticalLineLValue q χ t).norm.continuousOn
  exact ⟨⟨u, hu⟩, hmax⟩

/-- Canonical local maximizer for the source Class-II critical-line L-value. -/
noncomputable def cglClassIICriticalLineLocalMaximizer
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) (B : NNReal) :
    CGLClassIICriticalLineLocalOffset B :=
  Classical.choose (exists_cglClassIICriticalLineLocalMaximizer q χ t B)

/-- The canonical offset maximizes the critical-line L-value norm throughout
its closed local interval. -/
theorem cglClassIICriticalLineLocalMaximizer_maximal
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) (B : NNReal)
    (u : CGLClassIICriticalLineLocalOffset B) :
    ‖DirichletCharacter.LFunction χ (cglCriticalLinePoint (t + u.1)).1‖ ≤
      ‖DirichletCharacter.LFunction χ
        (cglCriticalLinePoint (t + (cglClassIICriticalLineLocalMaximizer q χ t B).1)).1‖ := by
  exact (Classical.choose_spec
    (exists_cglClassIICriticalLineLocalMaximizer q χ t B)) u.2

/-- The CGL character/ordinate row at the selected local maximum. -/
def cglClassIICriticalLineLocalMaximizerRow
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) (B : NNReal) :
    CGLCharacterDyadicRowData (q + 1) :=
  { time := t + (cglClassIICriticalLineLocalMaximizer q χ t B).1
    character := χ }

/-- The local-maximum row stays within the selected radius of its source zero
ordinate. -/
theorem cglClassIICriticalLineLocalMaximizerRow_time_displacement_le
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) (B : NNReal) :
    |(cglClassIICriticalLineLocalMaximizerRow q χ t B).time - t| ≤ B := by
  change |t + (cglClassIICriticalLineLocalMaximizer q χ t B).1 - t| ≤ B
  rw [add_sub_cancel_left]
  exact abs_le.mpr (cglClassIICriticalLineLocalMaximizer q χ t B).2

/-- Every candidate point in the local source interval is bounded by the
selected row's critical-line L-value. -/
theorem cglClassIICriticalLineLocalMaximizerRow_maximal
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) (B : NNReal)
    (u : CGLClassIICriticalLineLocalOffset B) :
    ‖DirichletCharacter.LFunction χ (cglCriticalLinePoint (t + u.1)).1‖ ≤
      ‖DirichletCharacter.LFunction χ
        (cglCriticalLinePoint (cglClassIICriticalLineLocalMaximizerRow q χ t B).time).1‖ := by
  exact cglClassIICriticalLineLocalMaximizer_maximal q χ t B u

/-- The selected local row retains its source Dirichlet character. -/
theorem cglClassIICriticalLineLocalMaximizerRow_character
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) (B : NNReal) :
    (cglClassIICriticalLineLocalMaximizerRow q χ t B).character = χ := rfl

/-- The local row's literal critical-line value is exactly the existing
Class-II large-value carrier. -/
theorem cglClassIICriticalLineLocalMaximizerRow_LValue_eq
    (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (t : ℝ) (B : NNReal) :
    cglClassIICriticalLineLValue (cglClassIICriticalLineLocalMaximizerRow q χ t B) =
      DirichletCharacter.LFunction χ
        (cglCriticalLinePoint (cglClassIICriticalLineLocalMaximizerRow q χ t B).time).1 := rfl

end RHTower
