import GaloisForLFunctions.HTGeometry.HorizontalLayerPaleyWienerLimit

/-!
# Unique power normalization of finite horizontal-layer Hardy leakage

Under the exact Paley--Wiener transport, unnormalized finite horizontal-layer leakage is
`L_ω = ω T_A + o(ω)` in operator norm.  This module proves the complete static power
trichotomy for `ω⁻ᵅ L_ω` along `ω → 0⁺` and the strict critical-strip norm threshold.
-/

open Complex Filter Topology
open scoped BigOperators InnerProductSpace

noncomputable section


namespace GaloisForLFunctions.HTGeometry

theorem tendsto_rpow_nhdsGT_zero_of_pos {q : ℝ} (hq : 0 < q) :
    Tendsto (fun ω : ℝ => ω ^ q) (𝓝[>] 0) (nhds 0) := by
  have hmul := Real.tendsto_log_nhdsGT_zero.atBot_mul_const hq
  have hexp := Real.tendsto_exp_atBot.comp hmul
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact (Real.rpow_def_of_pos hω q).symm

theorem tendsto_rpow_nhdsGT_zero_atTop_of_neg {q : ℝ} (hq : q < 0) :
    Tendsto (fun ω : ℝ => ω ^ q) (𝓝[>] 0) atTop := by
  have hmul := Real.tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg hq
  have hexp := Real.tendsto_exp_atTop.comp hmul
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact (Real.rpow_def_of_pos hω q).symm

/-- Unnormalized Paley--Wiener transport of the finite horizontal-layer leakage. -/
def horizontalLayerPaleyWienerLeakage {r : ℕ} (a : Fin r → ℝ)
    (m : Fin r → ℕ) (ω : ℝ) :
    HalfLineExponentialL2 →L[ℂ] HalfLineExponentialL2 :=
  paleyWienerOperatorTransport
    (hardyLeakage (projectiveBoundaryMul
      (horizontalLayerPowerProduct a m ω - 1)))

theorem horizontalLayerPaleyWienerLeakage_eq_smul_normalized {r : ℕ}
    (a : Fin r → ℝ) (m : Fin r → ℕ) {ω : ℝ} (hω : ω ≠ 0) :
    horizontalLayerPaleyWienerLeakage a m ω =
      (ω : ℂ) • horizontalLayerPaleyWienerNormalized a m ω := by
  have hboundary : horizontalLayerPowerProduct a m ω - 1 =
      (ω : ℂ) • horizontalLayerPowerNormalizedProjective a m ω := by
    rw [horizontalLayerPowerNormalizedProjective]
    rw [smul_smul]
    simp [hω]
  rw [horizontalLayerPaleyWienerLeakage, hboundary,
    projectiveBoundaryMul_smul, hardyLeakage_smul]
  change paleyWienerOperatorTransportLinear
      ((ω : ℂ) • hardyLeakage
        (projectiveBoundaryMul (horizontalLayerPowerNormalizedProjective a m ω))) = _
  rw [map_smul]
  rfl

/-- Static real-power normalization `ω⁻ᵅ L_ω` of the unnormalized leakage. -/
def horizontalLayerPaleyWienerPowerNormalized {r : ℕ} (α : ℝ)
    (a : Fin r → ℝ) (m : Fin r → ℕ) (ω : ℝ) :
    HalfLineExponentialL2 →L[ℂ] HalfLineExponentialL2 :=
  ((ω ^ (-α) : ℝ) : ℂ) • horizontalLayerPaleyWienerLeakage a m ω

theorem horizontalLayerPaleyWienerPowerNormalized_eq_rpow_smul {r : ℕ}
    (α : ℝ) (a : Fin r → ℝ) (m : Fin r → ℕ) {ω : ℝ} (hω : 0 < ω) :
    horizontalLayerPaleyWienerPowerNormalized α a m ω =
      ((ω ^ (1 - α) : ℝ) : ℂ) • horizontalLayerPaleyWienerNormalized a m ω := by
  rw [horizontalLayerPaleyWienerPowerNormalized,
    horizontalLayerPaleyWienerLeakage_eq_smul_normalized a m hω.ne', smul_smul]
  congr 1
  have hreal : ω ^ (-α) * ω = ω ^ (1 - α) := by
    calc
      ω ^ (-α) * ω = ω ^ (-α) * ω ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ω ^ ((-α) + 1) := (Real.rpow_add hω _ _).symm
      _ = ω ^ (1 - α) := by congr 1; ring
  exact_mod_cast hreal

theorem nhdsGT_zero_le_punctured : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] 0 := by
  exact nhdsWithin_mono _ (by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hx.ne')

theorem tendsto_horizontalLayerPaleyWienerRpowNormalized_of_lt_one {r : ℕ}
    {α : ℝ} (hα : α < 1) (a : Fin r → ℝ) (ha : ∀ j, 0 < a j)
    (m : Fin r → ℕ) :
    Tendsto (fun ω : ℝ => ((ω ^ (1 - α) : ℝ) : ℂ) •
      horizontalLayerPaleyWienerNormalized a m ω) (𝓝[>] 0) (nhds 0) := by
  have hscalarR := tendsto_rpow_nhdsGT_zero_of_pos (sub_pos.mpr hα)
  have hscalarC : Tendsto (fun ω : ℝ => ((ω ^ (1 - α) : ℝ) : ℂ))
      (𝓝[>] 0) (nhds 0) := by
    convert (Complex.continuous_ofReal.tendsto 0).comp hscalarR using 1 <;>
      simp [Function.comp_def]
  have hnormalized :
      Tendsto (horizontalLayerPaleyWienerNormalized a m) (𝓝[>] 0)
        (nhds (finiteExponentialHankel a ha m)) :=
    (tendsto_horizontalLayerPaleyWienerNormalized a ha m).mono_left
      nhdsGT_zero_le_punctured
  have hsmul : Tendsto (fun ω : ℝ =>
      ((ω ^ (1 - α) : ℝ) : ℂ) • horizontalLayerPaleyWienerNormalized a m ω)
      (𝓝[>] 0) (nhds 0) := by
    simpa only [zero_smul] using hscalarC.smul hnormalized
  exact hsmul

theorem eventually_horizontalLayerPaleyWienerPowerNormalized_eq_rpow_smul
    {r : ℕ} (α : ℝ) (a : Fin r → ℝ) (m : Fin r → ℕ) :
    ∀ᶠ ω : ℝ in 𝓝[>] 0,
      horizontalLayerPaleyWienerPowerNormalized α a m ω =
        ((ω ^ (1 - α) : ℝ) : ℂ) •
          horizontalLayerPaleyWienerNormalized a m ω := by
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact horizontalLayerPaleyWienerPowerNormalized_eq_rpow_smul α a m hω

theorem tendsto_horizontalLayerPaleyWienerPowerNormalized_of_lt_one {r : ℕ}
    {α : ℝ} (hα : α < 1) (a : Fin r → ℝ) (ha : ∀ j, 0 < a j)
    (m : Fin r → ℕ) :
    Tendsto (horizontalLayerPaleyWienerPowerNormalized α a m) (𝓝[>] 0)
      (nhds 0) := by
  refine (tendsto_horizontalLayerPaleyWienerRpowNormalized_of_lt_one
    hα a ha m).congr' ?_
  exact (eventually_horizontalLayerPaleyWienerPowerNormalized_eq_rpow_smul
    α a m).mono fun ω hω => hω.symm

theorem horizontalLayerPaleyWienerPowerNormalized_one_eq_normalized {r : ℕ}
    (a : Fin r → ℝ) (m : Fin r → ℕ) {ω : ℝ} (hω : 0 < ω) :
    horizontalLayerPaleyWienerPowerNormalized 1 a m ω =
      horizontalLayerPaleyWienerNormalized a m ω := by
  simpa using
    horizontalLayerPaleyWienerPowerNormalized_eq_rpow_smul (1 : ℝ) a m hω

theorem tendsto_horizontalLayerPaleyWienerPowerNormalized_one {r : ℕ}
    (a : Fin r → ℝ) (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) :
    Tendsto (horizontalLayerPaleyWienerPowerNormalized 1 a m) (𝓝[>] 0)
      (nhds (finiteExponentialHankel a ha m)) := by
  refine ((tendsto_horizontalLayerPaleyWienerNormalized a ha m).mono_left
    nhdsGT_zero_le_punctured).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact (horizontalLayerPaleyWienerPowerNormalized_one_eq_normalized a m hω).symm

theorem tendsto_norm_horizontalLayerPaleyWienerPowerNormalized_atTop_of_one_lt
    {r : ℕ} {α : ℝ} (hα : 1 < α) (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (j : Fin r) (hmj : 0 < m j) :
    Tendsto (fun ω : ℝ => ‖horizontalLayerPaleyWienerPowerNormalized α a m ω‖)
      (𝓝[>] 0) atTop := by
  have hscalar := tendsto_rpow_nhdsGT_zero_atTop_of_neg (sub_neg.mpr hα)
  have hnormalized :
      Tendsto (horizontalLayerPaleyWienerNormalized a m) (𝓝[>] 0)
        (nhds (finiteExponentialHankel a ha m)) :=
    (tendsto_horizontalLayerPaleyWienerNormalized a ha m).mono_left
      nhdsGT_zero_le_punctured
  have hnorm := hnormalized.norm
  have hlimitPos : 0 < ‖finiteExponentialHankel a ha m‖ :=
    (div_pos (Nat.cast_pos.mpr hmj) (ha j)).trans_le
      (multiplicity_div_rate_le_norm_finiteExponentialHankel a ha m j)
  have hprod := hscalar.atTop_mul_pos hlimitPos hnorm
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  rw [horizontalLayerPaleyWienerPowerNormalized_eq_rpow_smul α a m hω,
    norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hω.le _)]

/-- One positive-multiplicity layer inside the critical strip forces norm strictly above `2m`. -/
theorem two_mul_multiplicity_lt_norm_finiteExponentialHankel_of_lt_half
    {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 < a j) (m : Fin r → ℕ)
    (j : Fin r) (hmj : 0 < m j) (hhalf : a j < 1 / 2) :
    2 * (m j : ℝ) < ‖finiteExponentialHankel a ha m‖ := by
  have hma : 2 * (m j : ℝ) < (m j : ℝ) / a j := by
    rw [lt_div_iff₀ (ha j)]
    have hmreal : 0 < (m j : ℝ) := Nat.cast_pos.mpr hmj
    nlinarith
  exact hma.trans_le
    (multiplicity_div_rate_le_norm_finiteExponentialHankel a ha m j)

/-- Consequently every such nontrivial critical-strip layer has norm strictly above `2`. -/
theorem two_lt_norm_finiteExponentialHankel_of_lt_half
    {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 < a j) (m : Fin r → ℕ)
    (j : Fin r) (hmj : 0 < m j) (hhalf : a j < 1 / 2) :
    2 < ‖finiteExponentialHankel a ha m‖ := by
  have hmone : (1 : ℝ) ≤ m j := by exact_mod_cast hmj
  exact (show (2 : ℝ) ≤ 2 * (m j : ℝ) by nlinarith).trans_lt
    (two_mul_multiplicity_lt_norm_finiteExponentialHankel_of_lt_half
      a ha m j hmj hhalf)

/-- A source-side norm cap `≤ 2` excludes every positive-multiplicity layer with rate `< 1/2`. -/
theorem no_criticalStripLayer_of_norm_le_two
    {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 < a j) (m : Fin r → ℕ)
    (hnorm : ‖finiteExponentialHankel a ha m‖ ≤ 2) (j : Fin r) :
    ¬(0 < m j ∧ a j < 1 / 2) := by
  rintro ⟨hmj, hhalf⟩
  exact (not_lt_of_ge hnorm)
    (two_lt_norm_finiteExponentialHankel_of_lt_half a ha m j hmj hhalf)

end GaloisForLFunctions.HTGeometry
