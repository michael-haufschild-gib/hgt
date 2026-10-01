import GaloisForLFunctions.RHTower.WeilFullConeSpectralConsistency

/-!
# The boundary measure of a full-cone Weil-positive system

For a full-cone Weil-positive `lam` there is a positive Borel measure `μ_lam` on `ℝ` with

`W_lam(f ⋆ f̃) = ∫ |f̂|² dμ_lam`

for every `C²` compactly supported test `f` (`weilFullFunctional_weilTest_eq_lintegral`).  More
precisely, the Bochner measure of every such `f` is `|f̂|² μ_lam`
(`eq_withDensity_boundaryMeasure`).

**Construction.**  The mollifiers `ρ_j` (radius `1/(j+1)`) satisfy `|ρ̂_j(r)| ≥ ½` for
`|r| ≤ (j+1)/4`.  On the shell `S_j = {j/4 ≤ |r| < (j+1)/4}` put `μ = |ρ̂_j|⁻² ν_{ρ_j}`, and let
`μ_lam` be the sum over the shells.  The consistency law `|ρ̂_j|² ν_f = |f̂|² ν_{ρ_j}` turns each
restriction `ν_f|_{S_j}` into `|f̂|² μ|_{S_j}`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate NNReal ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-! ## Shells -/

/-- The shell `j/4 ≤ |r| < (j+1)/4`. -/
def shell (j : ℕ) : Set ℝ := {r | (j : ℝ) / 4 ≤ |r| ∧ |r| < ((j : ℝ) + 1) / 4}

theorem measurableSet_shell (j : ℕ) : MeasurableSet (shell j) :=
  (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)

theorem shell_pairwise_disjoint : Pairwise (Function.onFun Disjoint shell) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro r hi hj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have h' : ((i : ℝ) + 1) ≤ j := by exact_mod_cast h
    have := hi.2
    have := hj.1
    linarith
  · have h' : ((j : ℝ) + 1) ≤ i := by exact_mod_cast h
    have := hj.2
    have := hi.1
    linarith

theorem iUnion_shell : ⋃ j, shell j = Set.univ := by
  refine Set.eq_univ_of_forall fun r => Set.mem_iUnion.mpr ⟨⌊4 * |r|⌋₊, ?_⟩
  have h0 : 0 ≤ 4 * |r| := by positivity
  constructor
  · have := Nat.floor_le h0
    linarith
  · have := Nat.lt_floor_add_one (4 * |r|)
    linarith

/-! ## Mollifier transforms on the shells -/

theorem norm_paperFT_mollC_ge (j : ℕ) {r : ℝ} (hr : |r| ≤ ((j : ℝ) + 1) / 4) :
    1 / 2 ≤ ‖paperFT (WeilHerglotz.mollC j) r‖ := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hz : ‖(r : ℂ)‖ ≤ (j : ℝ) + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have h := WeilHerglotz.norm_paperFT_mollC_sub_one_le j hz
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  have h2 : 2 * |r| / ((j : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ hj]
    linarith
  have h3 := norm_sub_norm_le (1 : ℂ) (paperFT (WeilHerglotz.mollC j) r)
  rw [norm_one, norm_sub_rev] at h3
  linarith

theorem specDensity_mollC_pos (j : ℕ) {r : ℝ} (hr : r ∈ shell j) :
    0 < specDensity (WeilHerglotz.mollC j) r := by
  have h := norm_paperFT_mollC_ge j hr.2.le
  rw [specDensity]
  have : 0 < ‖paperFT (WeilHerglotz.mollC j) r‖₊ := by
    rw [← NNReal.coe_pos, coe_nnnorm]
    linarith
  positivity

theorem contDiff_mollC (j : ℕ) : ContDiff ℝ 2 (WeilHerglotz.mollC j) := WeilHerglotz.contDiff_mollC j

/-! ## The boundary measure -/

theorem exists_mollifierMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (j : ℕ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ y, charFun ν y = spectralKernel lam (WeilHerglotz.mollC j) y :=
  exists_spectralMeasure hW (contDiff_mollC j) (WeilHerglotz.hasCompactSupport_mollC j)

/-- The Bochner measure of the `j`-th mollifier. -/
def mollifierMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (j : ℕ) : Measure ℝ :=
  Classical.choose (exists_mollifierMeasure hW j)

theorem isFiniteMeasure_mollifierMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (j : ℕ) :
    IsFiniteMeasure (mollifierMeasure hW j) :=
  (Classical.choose_spec (exists_mollifierMeasure hW j)).1

theorem charFun_mollifierMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (j : ℕ) (y : ℝ) :
    charFun (mollifierMeasure hW j) y = spectralKernel lam (WeilHerglotz.mollC j) y :=
  (Classical.choose_spec (exists_mollifierMeasure hW j)).2 y

/-- The inverse density `|ρ̂_j|⁻²`. -/
def invDensity (j : ℕ) (r : ℝ) : ℝ≥0 := (specDensity (WeilHerglotz.mollC j) r)⁻¹

theorem measurable_invDensity (j : ℕ) : Measurable (invDensity j) :=
  (measurable_specDensity (WeilHerglotz.integrable_mollC j)).inv

/-- **The boundary measure** `μ_lam = Σ_j |ρ̂_j|⁻² ν_{ρ_j}|_{S_j}`. -/
def boundaryMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : Measure ℝ :=
  Measure.sum fun j : ℕ => ((mollifierMeasure hW j).restrict (shell j)).withDensity
    fun r => (invDensity j r : ℝ≥0∞)

/-- **The Bochner measure of every test is `|f̂|² μ_lam`.** -/
theorem eq_withDensity_boundaryMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ y, charFun ν y = spectralKernel lam f y) :
    ν = (boundaryMeasure hW).withDensity fun r => (specDensity f r : ℝ≥0∞) := by
  have hfint : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  rw [boundaryMeasure, withDensity_sum]
  conv_lhs => rw [← Measure.restrict_univ (μ := ν), ← iUnion_shell,
    Measure.restrict_iUnion shell_pairwise_disjoint measurableSet_shell]
  congr 1
  funext j
  haveI := isFiniteMeasure_mollifierMeasure hW j
  have hcons := spectralMeasure_consistency hf hfc (contDiff_mollC j)
    (WeilHerglotz.hasCompactSupport_mollC j) hν (charFun_mollifierMeasure hW j)
  have hres := congrArg (fun m : Measure ℝ => m.restrict (shell j)) hcons
  simp only [restrict_withDensity (measurableSet_shell j)] at hres
  have hmf := measurable_specDensity hfint
  have hmχ := measurable_specDensity (WeilHerglotz.integrable_mollC j)
  have hmi := measurable_invDensity j
  have hone : (fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)) *
      (fun r => (invDensity j r : ℝ≥0∞)) =ᵐ[ν.restrict (shell j)] 1 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_shell j)]
    refine Eventually.of_forall fun r hr => ?_
    have hpos := specDensity_mollC_pos j hr
    simp only [Pi.mul_apply, Pi.one_apply, invDensity]
    rw [← ENNReal.coe_mul, mul_inv_cancel₀ hpos.ne', ENNReal.coe_one]
  calc ν.restrict (shell j)
      = (ν.restrict (shell j)).withDensity 1 := withDensity_one.symm
    _ = (ν.restrict (shell j)).withDensity ((fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)) *
          (fun r => (invDensity j r : ℝ≥0∞))) := (withDensity_congr_ae hone).symm
    _ = ((ν.restrict (shell j)).withDensity fun r =>
          (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)).withDensity
            fun r => (invDensity j r : ℝ≥0∞) :=
        withDensity_mul _ (hmχ.coe_nnreal_ennreal)
          (hmi.coe_nnreal_ennreal)
    _ = (((mollifierMeasure hW j).restrict (shell j)).withDensity fun r =>
          (specDensity f r : ℝ≥0∞)).withDensity fun r => (invDensity j r : ℝ≥0∞) := by rw [hres]
    _ = ((mollifierMeasure hW j).restrict (shell j)).withDensity
          ((fun r => (specDensity f r : ℝ≥0∞)) * fun r => (invDensity j r : ℝ≥0∞)) :=
        (withDensity_mul _ (hmf.coe_nnreal_ennreal)
          (hmi.coe_nnreal_ennreal)).symm
    _ = ((mollifierMeasure hW j).restrict (shell j)).withDensity
          ((fun r => (invDensity j r : ℝ≥0∞)) * fun r => (specDensity f r : ℝ≥0∞)) := by
        rw [mul_comm]
    _ = (((mollifierMeasure hW j).restrict (shell j)).withDensity fun r =>
          (invDensity j r : ℝ≥0∞)).withDensity fun r => (specDensity f r : ℝ≥0∞) :=
        withDensity_mul _ (hmi.coe_nnreal_ennreal)
          (hmf.coe_nnreal_ennreal)

theorem transl_zero (k : ℝ → ℂ) : transl 0 k = k := by
  funext x
  simp [transl]

/-- **Spectral representation of the Weil form.**  For every `C²` compactly supported `f`,
`W_lam(f ⋆ f̃) = ∫ |f̂|² dμ_lam`, and this integral is finite. -/
theorem weilFullFunctional_weilTest_eq_lintegral {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫⁻ r, (specDensity f r : ℝ≥0∞) ∂boundaryMeasure hW) < ⊤ ∧
      weilFullFunctional lam (EF.weilTest f f) =
        (((∫⁻ r, (specDensity f r : ℝ≥0∞) ∂boundaryMeasure hW).toReal : ℝ) : ℂ) := by
  obtain ⟨ν, hfin, hν⟩ := exists_spectralMeasure hW hf hfc
  have heq := eq_withDensity_boundaryMeasure hW hf hfc hν
  have huniv : ν Set.univ = ∫⁻ r, (specDensity f r : ℝ≥0∞) ∂boundaryMeasure hW := by
    rw [heq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine ⟨huniv ▸ measure_lt_top ν _, ?_⟩
  have h0 := hν 0
  rw [spectralKernel, transl_zero, charFun_zero] at h0
  rw [← h0, ← huniv]
  rfl

end RHTower.WeilSpectral

end
