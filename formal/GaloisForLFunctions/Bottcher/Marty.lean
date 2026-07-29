/-
# Marty's equicontinuity bound — the normality criterion input

The Marty side of complex normal families: a holomorphic `f` whose spherical derivative is bounded by
`M` on a convex set is `M`-Lipschitz in the chordal metric of `ℂ̂`, `χ(f a, f b) ≤ M‖a-b‖`. This is the
quantitative form of Marty's criterion (a locally-bounded spherical derivative ⟹ equicontinuity in the
chordal metric ⟹, with Arzelà–Ascoli, normality), the engine that turns local control of `σf` into
normality of the family.

The proof realises `χ` as a Euclidean chord on the embedded sphere (`norm_stereo_sub`) and integrates
the round-metric speed `2σf` of the lifted path `stereo ∘ f` by the Euclidean mean-value inequality,
using the path-derivative helper `hasDerivAt_stereo_path` (built from the component `HasDerivAt`
plumbing `hasDerivAt_euclidean3` and the dynamic conformality `stereo_speed_identity`).

New file (Montel/Julia lane — Marty's criterion). General lemmas; consumes `ChordalMetric`,
`SphericalDeriv`.
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import GaloisForLFunctions.Bottcher.ChordalMetric
import GaloisForLFunctions.Bottcher.SphericalDeriv

open Complex

namespace Bottcher

theorem hasDerivAt_stereo_path {w : ℝ → ℂ} {w' : ℂ} {t : ℝ} (hw : HasDerivAt w w' t) :
    ∃ V : EuclideanSpace ℝ (Fin 3), HasDerivAt (fun s => stereo (w s)) V t
      ∧ ‖V‖ = 2 * ‖w'‖ / (1 + ‖w t‖ ^ 2) := by
  have hu : HasDerivAt (fun s => (w s).re) w'.re t := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hw
  have hv : HasDerivAt (fun s => (w s).im) w'.im t := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hw
  have hDne : (1 : ℝ) + ((w t).re ^ 2 + (w t).im ^ 2) ≠ 0 := by positivity
  have hD : HasDerivAt (fun s => 1 + ((w s).re ^ 2 + (w s).im ^ 2))
      (2 * (w t).re * w'.re + 2 * (w t).im * w'.im) t := by
    have := (hasDerivAt_const t (1:ℝ)).add ((hu.pow 2).add (hv.pow 2))
    exact this.congr_deriv (by ring)
  -- rewrite the path into re/im rational form
  have hstereo : (fun s => stereo (w s)) = fun s =>
      (!₂[2 * (w s).re / (1 + ((w s).re ^ 2 + (w s).im ^ 2)),
         2 * (w s).im / (1 + ((w s).re ^ 2 + (w s).im ^ 2)),
         ((w s).re ^ 2 + (w s).im ^ 2 - 1) / (1 + ((w s).re ^ 2 + (w s).im ^ 2))]
         : EuclideanSpace ℝ (Fin 3)) := by
    funext s
    have hzn : ‖w s‖ ^ 2 = (w s).re ^ 2 + (w s).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    unfold stereo; rw [hzn]
  have hc0 := (hu.const_mul 2).div hD hDne
  have hc1 := (hv.const_mul 2).div hD hDne
  have hc2 := (((hu.pow 2).add (hv.pow 2)).sub_const (1:ℝ)).div hD hDne
  refine ⟨_, by rw [hstereo]; exact hasDerivAt_euclidean3 hc0 hc1 hc2, ?_⟩
  rw [norm_euclidean3]
  have hw'2 : ‖w'‖ ^ 2 = w'.re ^ 2 + w'.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hwt2 : ‖w t‖ ^ 2 = (w t).re ^ 2 + (w t).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hRHSnn : 0 ≤ 2 * ‖w'‖ / (1 + ‖w t‖ ^ 2) := by positivity
  rw [← Real.sqrt_sq hRHSnn]
  congr 1
  have e1 : (2 * ‖w'‖ / (1 + ‖w t‖ ^ 2)) ^ 2
      = 4 * (w'.re ^ 2 + w'.im ^ 2) / (1 + ((w t).re ^ 2 + (w t).im ^ 2)) ^ 2 := by
    rw [hwt2, div_pow, mul_pow, hw'2]; norm_num
  rw [e1]
  norm_num
  field_simp
  ring

/-- **Marty's equicontinuity bound.** If `f` is holomorphic on a convex set `U` with spherical
derivative `≤ M`, then `f` is `M`-Lipschitz in the chordal metric: `χ(f a, f b) ≤ M‖a-b‖`. The
Euclidean mean-value inequality on the lifted path `stereo ∘ f`, via `hasDerivAt_stereo_path`. -/
theorem marty_equicontinuity {f : ℂ → ℂ} {U : Set ℂ} {M : ℝ}
    (hU : Convex ℝ U) (hf : ∀ z ∈ U, DifferentiableAt ℂ f z)
    (hM : ∀ z ∈ U, sphericalDeriv f z ≤ M)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    chordalDist (f a) (f b) ≤ M * ‖a - b‖ := by
  classical
  set γ : ℝ → ℂ := fun s => a + (s : ℂ) * (b - a) with hγ_def
  have hγ0 : γ 0 = a := by simp [hγ_def]
  have hγ1 : γ 1 = b := by simp only [hγ_def]; push_cast; ring
  have hγderiv : ∀ s, HasDerivAt γ (b - a) s := by
    intro s
    have hs1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := by
      rw [show (fun r : ℝ => (r : ℂ)) = (Complex.ofRealCLM : ℝ → ℂ) by rfl]
      exact Complex.ofRealCLM.hasDerivAt
    have := ((hs1.mul_const (b - a)).const_add a)
    simpa [hγ_def] using this
  have hγmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ U := by
    intro s hs
    refine hU.segment_subset ha hb ?_
    rw [segment_eq_image]
    exact ⟨s, hs, by simp only [hγ_def, Complex.real_smul]; push_cast; ring⟩
  set h : ℝ → EuclideanSpace ℝ (Fin 3) := fun s => stereo (f (γ s)) with hh_def
  have hkey : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ Vs, HasDerivAt h Vs s ∧ ‖Vs‖ ≤ 2 * M * ‖b - a‖ := by
    intro s hs
    have hws : HasDerivAt (fun r => f (γ r)) ((b - a) • deriv f (γ s)) s :=
      (hf (γ s) (hγmem s hs)).hasDerivAt.scomp s (hγderiv s)
    obtain ⟨Vs, hVderiv, hVnorm⟩ := hasDerivAt_stereo_path hws
    refine ⟨Vs, hVderiv, ?_⟩
    rw [hVnorm]
    have heq : 2 * ‖(b - a) • deriv f (γ s)‖ / (1 + ‖f (γ s)‖ ^ 2)
        = 2 * ‖b - a‖ * sphericalDeriv f (γ s) := by
      rw [smul_eq_mul, norm_mul, sphericalDeriv]; ring
    rw [heq]
    have hσ := hM (γ s) (hγmem s hs)
    have h2b : (0 : ℝ) ≤ 2 * ‖b - a‖ := by positivity
    calc 2 * ‖b - a‖ * sphericalDeriv f (γ s) ≤ 2 * ‖b - a‖ * M := by
            exact mul_le_mul_of_nonneg_left hσ h2b
      _ = 2 * M * ‖b - a‖ := by ring
  -- assemble with the mean value inequality
  set h' : ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun s => if hs : s ∈ Set.Icc (0 : ℝ) 1 then (hkey s hs).choose else 0 with hh'_def
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt h (h' s) (Set.Icc 0 1) s := by
    intro s hs; simp only [hh'_def]; rw [dif_pos hs]; exact (hkey s hs).choose_spec.1.hasDerivWithinAt
  have hnb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖h' s‖ ≤ 2 * M * ‖b - a‖ := by
    intro s hs; simp only [hh'_def]; rw [dif_pos hs]; exact (hkey s hs).choose_spec.2
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hnb (convex_Icc (0:ℝ) 1)
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
  -- ‖h 1 - h 0‖ ≤ (2M‖b-a‖)·‖1-0‖ = 2M‖b-a‖
  simp only [hh_def, hγ1, hγ0, sub_zero, norm_one, mul_one] at hmv
  rw [norm_stereo_sub, chordalDist_comm] at hmv
  have hfin : chordalDist (f a) (f b) ≤ M * ‖b - a‖ := by linarith
  rwa [norm_sub_rev] at hfin

end Bottcher
