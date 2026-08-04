import GaloisForLFunctions.HTGeometry.WaveEnergyGreenIdentity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Directional derivatives of a field on time-space

The energy of a wave field pairs its time derivative with its spatial gradient, so both have to be
read as directional derivatives of one function of the event. This file records the calculus of
those derivatives: smoothness, supports, the symmetry of mixed second derivatives, and the two
bridges identifying a directional derivative with the derivative of a slice — in time with an
ordinary derivative, in space with the coordinate partial derivative of the previous file.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Directional

variable {d : ℕ}

/-- The derivative of a field of events along a fixed direction. -/
noncomputable def waveDirDeriv (v : ℝ × (Fin d → ℝ)) (u : ℝ × (Fin d → ℝ) → ℝ)
    (p : ℝ × (Fin d → ℝ)) : ℝ := fderiv ℝ u p v

/-- The time direction. -/
def timeDir (d : ℕ) : ℝ × (Fin d → ℝ) := (1, 0)

/-- The `i`-th spatial direction. -/
noncomputable def spaceDir (d : ℕ) (i : Fin d) : ℝ × (Fin d → ℝ) := (0, Pi.single i 1)

theorem contDiff_dirDeriv {u : ℝ × (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (v : ℝ × (Fin d → ℝ)) : ContDiff ℝ ∞ (waveDirDeriv v u) :=
  ContDiff.clm_apply (contDiff_infty_iff_fderiv.mp hu).2 contDiff_const

theorem differentiableAt_of_contDiff_infty' {u : ℝ × (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (p : ℝ × (Fin d → ℝ)) : DifferentiableAt ℝ u p :=
  (contDiff_infty_iff_fderiv.mp hu).1 p

theorem waveDirDeriv_eq_zero_of_eventually {u : ℝ × (Fin d → ℝ) → ℝ} {p : ℝ × (Fin d → ℝ)}
    (h : u =ᶠ[nhds p] fun _ => (0 : ℝ)) (v : ℝ × (Fin d → ℝ)) : waveDirDeriv v u p = 0 := by
  rw [waveDirDeriv, h.fderiv_eq]
  simp

/-- A field vanishing off a closed set of events has all its directional derivatives vanishing
there. -/
theorem waveDirDeriv_eq_zero_of_notMem {u : ℝ × (Fin d → ℝ) → ℝ} {S : Set (ℝ × (Fin d → ℝ))}
    (hS : IsClosed S) (hzero : ∀ q : ℝ × (Fin d → ℝ), q ∉ S → u q = 0)
    {p : ℝ × (Fin d → ℝ)} (hp : p ∉ S) (v : ℝ × (Fin d → ℝ)) : waveDirDeriv v u p = 0 :=
  waveDirDeriv_eq_zero_of_eventually
    (Filter.eventually_of_mem (hS.isOpen_compl.mem_nhds hp) fun q hq => hzero q hq) v

/-! ## The two slice bridges -/

theorem waveDirDeriv_timeDir_eq {u : ℝ × (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ)
    (x : Fin d → ℝ) : waveDirDeriv (timeDir d) u (t, x) = deriv (fun s : ℝ => u (s, x)) t := by
  have hslice : HasDerivAt (fun s : ℝ => u (s, x)) (fderiv ℝ u (t, x) (timeDir d)) t := by
    have hmap : HasFDerivAt (fun s : ℝ => ((s, x) : ℝ × (Fin d → ℝ)))
        ((ContinuousLinearMap.id ℝ ℝ).prod 0) t :=
      (hasFDerivAt_id t).prodMk (hasFDerivAt_const x t)
    have hcomp := (differentiableAt_of_contDiff_infty' hu (t, x)).hasFDerivAt.comp t hmap
    have hval : ((fderiv ℝ u (t, x)).comp ((ContinuousLinearMap.id ℝ ℝ).prod 0)) 1
        = fderiv ℝ u (t, x) (timeDir d) := by
      simp [timeDir]
    have := hcomp.hasDerivAt
    rwa [hval] at this
  rw [waveDirDeriv, hslice.deriv]

theorem waveDirDeriv_spaceDir_eq {u : ℝ × (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin d) (t : ℝ)
    (x : Fin d → ℝ) :
    waveDirDeriv (spaceDir d i) u (t, x) = coordPartial i (fun y : Fin d → ℝ => u (t, y)) x := by
  have hmap : HasFDerivAt (fun y : Fin d → ℝ => ((t, y) : ℝ × (Fin d → ℝ)))
      ((0 : (Fin d → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin d → ℝ))) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hcomp : HasFDerivAt (fun y : Fin d → ℝ => u (t, y))
      ((fderiv ℝ u (t, x)).comp
        ((0 : (Fin d → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin d → ℝ)))) x :=
    (differentiableAt_of_contDiff_infty' hu (t, x)).hasFDerivAt.comp x hmap
  rw [coordPartial, hcomp.fderiv, waveDirDeriv]
  simp [spaceDir]

/-! ## Symmetry of the mixed second derivative -/

theorem waveDirDeriv_comm {u : ℝ × (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (v w : ℝ × (Fin d → ℝ)) (p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv v (waveDirDeriv w u) p = waveDirDeriv w (waveDirDeriv v u) p := by
  have hfd : ∀ z : ℝ × (Fin d → ℝ), HasFDerivAt (fderiv ℝ u)
      (fderiv ℝ (fderiv ℝ u) z) z := fun z =>
    ((contDiff_infty_iff_fderiv.mp hu).2.differentiable (by simp) z).hasFDerivAt
  have happ : ∀ (a : ℝ × (Fin d → ℝ)),
      HasFDerivAt (waveDirDeriv a u)
        ((ContinuousLinearMap.apply ℝ ℝ a).comp (fderiv ℝ (fderiv ℝ u) p)) p := by
    intro a
    exact (ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp p (hfd p)
  have hsymm : IsSymmSndFDerivAt ℝ u p := by
    refine ContDiffAt.isSymmSndFDerivAt hu.contDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  have hv := (happ w).fderiv
  have hw := (happ v).fderiv
  rw [waveDirDeriv, waveDirDeriv, hv, hw]
  simpa using hsymm v w

end Directional

end GaloisForLFunctions.HTGeometry
