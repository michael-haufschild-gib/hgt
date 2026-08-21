/-
# The spherical cap patch of the diagonal block

The incubation law needs a compact carrier patch of positive measure inside the diagonal coefficient
subspace, on which every diagonal coefficient stays bounded away from zero.  The closed cap of
radius `ρ` about the normalized all-positive direction is such a patch: it is compact, its cone
annulus contains a nonempty open set, and every coordinate of a point of the cap is at least
`f^{-1/2} - ρ`.

Main results:
* `uniformDir`, `norm_uniformDir` — the normalized all-positive direction.
* `sphericalCap`, `isCompact_sphericalCap`, `isCompact_embedPatch_sphericalCap`.
* `sphericalCap_coord_ge` — **`(16)`**.
* `volume_patchAnnulus_sphericalCap_pos` — the carrier factor is positive.
-/
import GaloisForLFunctions.HTGeometry.SphericalPatchTube

open MeasureTheory Metric Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {f : ℕ}

/-- The normalized all-positive coefficient direction. -/
def uniformDir (f : ℕ) : EuclideanSpace ℝ (Fin f) :=
  (Real.sqrt (f : ℝ))⁻¹ • (WithLp.toLp 2 (fun _ => (1 : ℝ)))

theorem norm_ones (f : ℕ) :
    ‖(WithLp.toLp 2 (fun _ => (1 : ℝ)) : EuclideanSpace ℝ (Fin f))‖ = Real.sqrt (f : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp

theorem norm_uniformDir (hf : 0 < f) : ‖uniformDir f‖ = 1 := by
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hsq : (0 : ℝ) < Real.sqrt (f : ℝ) := Real.sqrt_pos.mpr hfR
  rw [uniformDir, norm_smul, norm_ones, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg hsq.le, inv_mul_cancel₀ hsq.ne']

theorem uniformDir_apply (i : Fin f) :
    WithLp.ofLp (uniformDir f) i = (Real.sqrt (f : ℝ))⁻¹ := by
  show (Real.sqrt (f : ℝ))⁻¹ * (1 : ℝ) = _
  rw [mul_one]

/-- The closed spherical cap of radius `ρ` about a unit direction. -/
def sphericalCap (u₀ : EuclideanSpace ℝ (Fin f)) (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin f)) :=
  {w | ‖w‖ = 1 ∧ dist w u₀ ≤ ρ}

theorem isClosed_sphericalCap (u₀ : EuclideanSpace ℝ (Fin f)) (ρ : ℝ) :
    IsClosed (sphericalCap u₀ ρ) := by
  have h1 : IsClosed {w : EuclideanSpace ℝ (Fin f) | ‖w‖ = 1} :=
    isClosed_eq continuous_norm continuous_const
  have h2 : IsClosed {w : EuclideanSpace ℝ (Fin f) | dist w u₀ ≤ ρ} :=
    isClosed_le (continuous_id.dist continuous_const) continuous_const
  exact h1.inter h2

theorem isCompact_sphericalCap (u₀ : EuclideanSpace ℝ (Fin f)) (ρ : ℝ) :
    IsCompact (sphericalCap u₀ ρ) := by
  refine isCompact_of_isClosed_isBounded (isClosed_sphericalCap u₀ ρ) ?_
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin f))) (r := 1)).subset ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right, hw.1]

theorem measurableSet_sphericalCap (u₀ : EuclideanSpace ℝ (Fin f)) (ρ : ℝ) :
    MeasurableSet (sphericalCap u₀ ρ) := (isClosed_sphericalCap u₀ ρ).measurableSet

theorem isCompact_embedPatch_sphericalCap {d : ℕ} (u₀ : EuclideanSpace ℝ (Fin f)) (ρ : ℝ) :
    IsCompact (embedPatch (d := d) (sphericalCap u₀ ρ)) := by
  refine (isCompact_sphericalCap u₀ ρ).image ?_
  refine (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin f))
    (EuclideanSpace ℝ (Fin d))).symm.continuous.comp ?_
  exact continuous_id.prodMk continuous_const

theorem nonempty_embedPatch_sphericalCap {d : ℕ} {u₀ : EuclideanSpace ℝ (Fin f)}
    (hu₀ : ‖u₀‖ = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (embedPatch (d := d) (sphericalCap u₀ ρ)).Nonempty :=
  ⟨_, ⟨u₀, ⟨hu₀, by rw [dist_self]; exact hρ⟩, rfl⟩⟩


theorem abs_coord_le_norm (v : EuclideanSpace ℝ (Fin f)) (i : Fin f) :
    |WithLp.ofLp v i| ≤ ‖v‖ := by
  have hle : |WithLp.ofLp v i| ^ 2 ≤ ∑ j, ‖WithLp.ofLp v j‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum
      (f := fun j => ‖WithLp.ofLp v j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))
    rw [Real.norm_eq_abs]
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (abs_nonneg (WithLp.ofLp v i))]
  exact Real.sqrt_le_sqrt hle

/-- **`(16)`.**  Every direction of the cap about the uniform vector has all coordinates at least
`f^{-1/2} - ρ`. -/
theorem sphericalCap_coord_ge {ρ : ℝ} {w : EuclideanSpace ℝ (Fin f)}
    (hw : w ∈ sphericalCap (uniformDir f) ρ) (i : Fin f) :
    (Real.sqrt (f : ℝ))⁻¹ - ρ ≤ WithLp.ofLp w i := by
  have hd : |WithLp.ofLp w i - WithLp.ofLp (uniformDir f) i| ≤ ρ := by
    refine le_trans ?_ hw.2
    rw [dist_eq_norm]
    exact abs_coord_le_norm (w - uniformDir f) i
  rw [uniformDir_apply i] at hd
  have hab := abs_le.mp hd
  linarith [hab.1]

/-- The annulus over a spherical cap has positive volume. -/
theorem volume_patchAnnulus_sphericalCap_pos {u₀ : EuclideanSpace ℝ (Fin f)} (hu₀ : ‖u₀‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ) : 0 < volume (patchAnnulus (sphericalCap u₀ ρ)) := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A : Set (EuclideanSpace ℝ (Fin f)),
    A = {u | 1 / 2 < ‖u‖ ∧ ‖u‖ < 3 / 4} := ⟨_, rfl⟩
  have hmemA : ∀ u : EuclideanSpace ℝ (Fin f), u ∈ A ↔ (1 / 2 < ‖u‖ ∧ ‖u‖ < 3 / 4) := by
    intro u
    rw [hAdef]
    exact Iff.rfl
  have hAopen : IsOpen A := by
    rw [hAdef]
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hAne : ∀ u ∈ A, ‖u‖ ≠ 0 := by
    intro u hu
    have h1 := ((hmemA u).mp hu).1
    intro hzero
    rw [hzero] at h1
    linarith
  have hcont : ContinuousOn (fun u : EuclideanSpace ℝ (Fin f) => dist (‖u‖⁻¹ • u) u₀) A := by
    intro u hu
    refine ContinuousAt.continuousWithinAt ?_
    refine (Continuous.continuousAt (continuous_id.dist continuous_const)).comp ?_
    exact ((continuous_norm.continuousAt).inv₀ (hAne u hu)).smul continuousAt_id
  obtain ⟨V, hVdef⟩ : ∃ V : Set (EuclideanSpace ℝ (Fin f)),
    V = A ∩ (fun u => dist (‖u‖⁻¹ • u) u₀) ⁻¹' (Set.Iio ρ) := ⟨_, rfl⟩
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact hcont.isOpen_inter_preimage hAopen isOpen_Iio
  have hVsub : V ⊆ patchAnnulus (sphericalCap u₀ ρ) := by
    intro u hu
    rw [hVdef] at hu
    have hA := (hmemA u).mp hu.1
    have hnz : ‖u‖ ≠ 0 := hAne u hu.1
    refine ⟨hA.1, hA.2, ?_, le_of_lt hu.2⟩
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u),
      inv_mul_cancel₀ hnz]
  have hVne : V.Nonempty := by
    have hn : ‖(5 / 8 : ℝ) • u₀‖ = 5 / 8 := by
      rw [norm_smul, Real.norm_eq_abs, hu₀, mul_one]
      norm_num
    refine ⟨(5 / 8 : ℝ) • u₀, ?_⟩
    rw [hVdef]
    refine ⟨(hmemA _).mpr ⟨by rw [hn]; norm_num, by rw [hn]; norm_num⟩, ?_⟩
    show dist (‖(5 / 8 : ℝ) • u₀‖⁻¹ • ((5 / 8 : ℝ) • u₀)) u₀ < ρ
    rw [hn, smul_smul]
    norm_num
    exact hρ
  exact lt_of_lt_of_le (hVopen.measure_pos volume hVne) (measure_mono hVsub)

end GaloisForLFunctions.HTGeometry

end
