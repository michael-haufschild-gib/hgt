/-
# The codimension tail and the moment divergence of the coupled shortcut law

The tube of radius `c/L` around the separated diagonal patch carries shell mass at least a constant
times `L^{-(10n+12)}`, because the spherical tube law gives `a_P r^d` and the transverse codimension
of the diagonal carrier is `d = 10n+12`.  Any onset time whose lateness follows from survival of the
incubation certificate through `L` therefore has a `d`-power tail, and every moment of order above
`d` -- and the boundary moment itself -- is infinite.

Main results:
* `coupled_tail_lower` — **`(23)`**: the codimension tail of the diagonal tube.
* `lintegral_coupled_onset_pow_eq_top` — **`(24)`** above the exponent.
* `lintegral_coupled_onset_rpow_eq_top` — **`(24)`** at the boundary exponent.
-/
import GaloisForLFunctions.HTGeometry.CoupledShortcutCollision
import GaloisForLFunctions.HTGeometry.PowerTailMomentDivergence

open MeasureTheory Metric Set Filter
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {k : ℕ}

theorem finrank_patchSpace (f d : ℕ) : Module.finrank ℝ (PatchSpace f d) = f + d := by
  rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ
    (EuclideanSpace ℝ (Fin f) × EuclideanSpace ℝ (Fin d)))]
  rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]

/-- The shell-mass constant of the diagonal tube. -/
def diagTubeConst (k : ℕ) (eps rho : ℝ) : ℝ≥0∞ :=
  (Module.finrank ℝ (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) : ℝ≥0∞) *
    (volume (patchAnnulus (sphericalCap (carrierPatchDir (k + 1) eps) rho)) *
      volume (ball (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12))) 1))

theorem diagTubeConst_pos {eps rho : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ ((k + 1) + 2) ≤ 1) (hrho : 0 < rho) :
    0 < diagTubeConst k eps rho := by
  have hdir : ‖carrierPatchDir (k + 1) eps‖ = 1 := norm_carrierPatchDir heps.le hsmall
  have hann : 0 < volume (patchAnnulus (sphericalCap (carrierPatchDir (k + 1) eps) rho)) :=
    volume_patchAnnulus_sphericalCap_pos hdir hrho
  have hball : 0 < volume (ball (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12))) 1) :=
    measure_ball_pos volume _ one_pos
  have hrank : 0 < Module.finrank ℝ (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) := by
    rw [finrank_patchSpace]
    omega
  have hrankE : (0 : ℝ≥0∞) <
      (Module.finrank ℝ (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) : ℝ≥0∞) := by
    exact_mod_cast hrank
  rw [diagTubeConst, pos_iff_ne_zero]
  exact mul_ne_zero (ne_of_gt hrankE) (mul_ne_zero (ne_of_gt hann) (ne_of_gt hball))

theorem diagTubeConst_ne_top (eps rho : ℝ) : diagTubeConst k eps rho ≠ ⊤ := by
  have hann : volume (patchAnnulus (sphericalCap (carrierPatchDir (k + 1) eps) rho)) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (measure_ball_lt_top (x := (0 : EuclideanSpace ℝ (Fin (2 * (k + 1) + 3)))) (r := 1)))
    intro u hu
    rw [mem_ball, dist_zero_right]
    exact lt_trans hu.2.1 (by norm_num)
  have hball : volume (ball (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12))) 1) ≠ ⊤ :=
    ne_of_lt measure_ball_lt_top
  rw [diagTubeConst]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top hann hball)

/-- **`(23)`.**  The tube of radius `c/L` around the separated diagonal patch carries shell mass at
least a positive constant times `L^{-(10n+12)}`. -/
theorem coupled_tail_lower {eps rho c : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ ((k + 1) + 2) ≤ 1) (hrho : 0 < rho) (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, max c 1 ≤ L →
      ENNReal.ofReal (A * L ^ (-((10 * (k + 1) + 12 : ℕ) : ℝ)))
        ≤ (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere
            (patchThickening (sphericalCap (carrierPatchDir (k + 1) eps) rho) (c / L)) := by
  classical
  have hKpos := diagTubeConst_pos heps hsmall hrho
  have hKtop := diagTubeConst_ne_top (k := k) eps rho
  have hKreal : 0 < (diagTubeConst k eps rho).toReal :=
    ENNReal.toReal_pos (ne_of_gt hKpos) hKtop
  refine ⟨(diagTubeConst k eps rho).toReal * (c / 8) ^ (10 * (k + 1) + 12), by positivity, ?_⟩
  intro L hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hcL : c ≤ L := le_trans (le_max_left _ _) hL
  have hr0 : 0 < c / L := div_pos hc hLpos
  have hr1 : c / L ≤ 1 := by
    rw [div_le_one hLpos]
    exact hcL
  have hbase := toSphere_patchThickening_ge (d := 10 * (k + 1) + 12)
    (measurableSet_sphericalCap (carrierPatchDir (k + 1) eps) rho) hr0 hr1
  refine le_trans (le_of_eq ?_) hbase
  have hpow : ((diagTubeConst k eps rho).toReal * (c / 8) ^ (10 * (k + 1) + 12))
      * L ^ (-((10 * (k + 1) + 12 : ℕ) : ℝ))
      = (diagTubeConst k eps rho).toReal * (c / L / 8) ^ (10 * (k + 1) + 12) := by
    have h8 : (c / L / 8 : ℝ) ^ (10 * (k + 1) + 12)
        = (c / 8) ^ (10 * (k + 1) + 12) * (L ^ (10 * (k + 1) + 12))⁻¹ := by
      rw [show (c / L / 8 : ℝ) = (c / 8) * L⁻¹ by ring, mul_pow, inv_pow]
    rw [Real.rpow_neg hLpos.le, Real.rpow_natCast, h8, mul_assoc]
  rw [hpow, ENNReal.ofReal_mul (le_of_lt hKreal), ENNReal.ofReal_toReal hKtop, diagTubeConst]
  ring

/-- **`(24)` above the exponent.**  Every moment of order above `10n+12` is infinite. -/
theorem lintegral_coupled_onset_pow_eq_top {eps rho c : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ ((k + 1) + 2) ≤ 1) (hrho : 0 < rho) (hc : 0 < c)
    (τ : sphere (0 : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) 1 → ℝ)
    {p : ℝ} (hp : ((10 * (k + 1) + 12 : ℕ) : ℝ) < p)
    (hτm : AEMeasurable (fun u => ENNReal.ofReal (τ u ^ p))
      ((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere))
    (hτ : ∀ L : ℝ, 0 < L →
      patchThickening (sphericalCap (carrierPatchDir (k + 1) eps) rho) (c / L) ⊆ {u | L < τ u}) :
    ∫⁻ u, ENNReal.ofReal (τ u ^ p)
      ∂((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere) = ⊤ := by
  obtain ⟨A, hA, hfloor⟩ := coupled_tail_lower heps hsmall hrho hc
  obtain ⟨L₀, hL₀def⟩ : ∃ L₀ : ℝ, L₀ = max c 1 := ⟨_, rfl⟩
  have hL₀pos : 0 < L₀ := by
    rw [hL₀def]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hppos : 0 < p := lt_trans (by positivity) hp
  refine lintegral_eq_top_of_unbounded_real
    (g := fun L => A * (max L L₀) ^ (p - ((10 * (k + 1) + 12 : ℕ) : ℝ))) ?_ ?_
  · intro L
    have hmax : L₀ ≤ max L L₀ := le_max_right _ _
    have hmaxpos : 0 < max L L₀ := lt_of_lt_of_le hL₀pos hmax
    have hcut : max c 1 ≤ max L L₀ := by
      calc max c 1 = L₀ := hL₀def.symm
        _ ≤ max L L₀ := hmax
    have htail : ENNReal.ofReal (A * (max L L₀) ^ (-((10 * (k + 1) + 12 : ℕ) : ℝ)))
        ≤ ((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere)
            {u | max L L₀ < τ u} :=
      le_trans (hfloor _ hcut) (measure_mono (hτ _ hmaxpos))
    exact moment_floor hτm hppos hmaxpos htail
  · refine Filter.Tendsto.const_mul_atTop hA ?_
    refine Filter.Tendsto.comp (tendsto_rpow_atTop (by linarith)) ?_
    exact tendsto_atTop_mono (fun L => le_max_left L L₀) tendsto_id

/-- **The boundary case at a general exponent.**  A tail `A L^{-q}` makes the `q`-th moment
infinite: the layer-cake integrand is `A t^{-1}`, which diverges. -/
theorem lintegral_rpow_eq_top_of_boundary_tail_gen {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {τ : Ω → ℝ} {A L₀ q : ℝ} (hq : 0 < q) (hA : 0 < A) (hL₀ : 0 < L₀)
    (hτ0 : 0 ≤ᵐ[μ] τ) (hτm : AEMeasurable τ μ)
    (htail : ∀ t : ℝ, L₀ < t → ENNReal.ofReal (A * t ^ (-q)) ≤ μ {ω | t < τ ω}) :
    ∫⁻ ω, ENNReal.ofReal (τ ω ^ q) ∂μ = ⊤ := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ hτ0 hτm hq]
  have hinner : ∫⁻ t in Set.Ioi (0 : ℝ),
      μ {ω | t < τ ω} * ENNReal.ofReal (t ^ (q - 1)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    have hsub : Set.Ioi L₀ ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (le_of_lt hL₀)
    refine le_trans ?_ (lintegral_mono_set hsub)
    have hpt : ∀ t ∈ Set.Ioi L₀,
        ENNReal.ofReal A * ENNReal.ofReal (t ^ (-1 : ℝ))
          ≤ μ {ω | t < τ ω} * ENNReal.ofReal (t ^ (q - 1)) := by
      intro t ht
      have htpos : 0 < t := lt_trans hL₀ ht
      have hfac : ENNReal.ofReal A * ENNReal.ofReal (t ^ (-1 : ℝ))
          = ENNReal.ofReal (A * t ^ (-q)) * ENNReal.ofReal (t ^ (q - 1)) := by
        rw [← ENNReal.ofReal_mul (le_of_lt hA), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc, ← Real.rpow_add htpos]
        ring_nf
      rw [hfac]
      gcongr
      exact htail t ht
    calc (⊤ : ℝ≥0∞)
        = ENNReal.ofReal A * ∫⁻ t in Set.Ioi L₀, ENNReal.ofReal (t ^ (-1 : ℝ)) := by
          rw [lintegral_Ioi_rpow_neg_one_eq_top hL₀,
            ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le, hA])]
      _ = ∫⁻ t in Set.Ioi L₀, ENNReal.ofReal A * ENNReal.ofReal (t ^ (-1 : ℝ)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Set.Ioi L₀, μ {ω | t < τ ω} * ENNReal.ofReal (t ^ (q - 1)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact hpt t ht
  rw [hinner, ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le, hq])]

/-- **`(24)` at the boundary exponent.**  The `(10n+12)`-th moment itself is infinite. -/
theorem lintegral_coupled_onset_rpow_eq_top {eps rho c : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ ((k + 1) + 2) ≤ 1) (hrho : 0 < rho) (hc : 0 < c)
    (τ : sphere (0 : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) 1 → ℝ)
    (hτ0 : 0 ≤ᵐ[(volume : Measure (PatchSpace (2 * (k + 1) + 3)
      (10 * (k + 1) + 12))).toSphere] τ)
    (hτm : AEMeasurable τ
      ((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere))
    (hτ : ∀ L : ℝ, 0 < L →
      patchThickening (sphericalCap (carrierPatchDir (k + 1) eps) rho) (c / L) ⊆ {u | L < τ u}) :
    ∫⁻ u, ENNReal.ofReal (τ u ^ ((10 * (k + 1) + 12 : ℕ) : ℝ))
      ∂((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere) = ⊤ := by
  obtain ⟨A, hA, hfloor⟩ := coupled_tail_lower heps hsmall hrho hc
  obtain ⟨L₀, hL₀def⟩ : ∃ L₀ : ℝ, L₀ = max c 1 := ⟨_, rfl⟩
  have hL₀pos : 0 < L₀ := by
    rw [hL₀def]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine lintegral_rpow_eq_top_of_boundary_tail_gen (by positivity) hA hL₀pos hτ0 hτm ?_
  intro t ht
  have htpos : 0 < t := lt_trans hL₀pos ht
  have hcut : max c 1 ≤ t := by
    rw [← hL₀def]
    exact le_of_lt ht
  exact le_trans (hfloor t hcut) (measure_mono (hτ t htpos))

end GaloisForLFunctions.HTGeometry

end
