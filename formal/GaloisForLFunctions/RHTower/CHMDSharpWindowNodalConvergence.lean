import GaloisForLFunctions.RHTower.CHMDSharpSpatialCut
import GaloisForLFunctions.HTGeometry.StrongConvergenceDense

/-!
# Exact spatial localization of the complete nodal defect

Expanding sharp windows converge in the full arithmetic graph norm and
preserve odd parity. Their exact commutation with nodal contractions
recovers the full signed cross-pairing, Weil energy and oneL defect.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace RHTower
open CHMDDoobGraph CHMDClosedJump CHMDPolar
set_option autoImplicit false




/-- Bounded literal interval restriction on the full maximal graph. -/
def sharpIntervalGraphCLM (lo hi : ℝ) : SourceGraph →L[ℝ] SourceGraph :=
  (sharpLowerGraphCLM hi).comp
    (ContinuousLinearMap.id ℝ SourceGraph - sharpLowerGraphCLM lo)

theorem sharpIntervalGraphCLM_apply (lo hi : ℝ) (p : SourceGraph) :
    sharpIntervalGraphCLM lo hi p = sharpIntervalGraph lo hi p := rfl

/-- Symmetric sharp windows preserve reflection, including the full edge coordinate. -/
theorem reflectGraph_sharpIntervalGraph (a : ℝ) (p : SourceGraph) :
    reflectGraph (sharpIntervalGraph (-a) a p) =
      sharpIntervalGraph (-a) a (reflectGraph p) := by
  apply source_projection_injective
  change (reflectGraph (sharpIntervalGraph (-a) a p)).val.fst = _
  rw [reflectGraph_fst]
  apply Lp.ext
  have hcut := measurePreserving_neg_mass.quasiMeasurePreserving.ae_eq_comp
    (sharpIntervalGraph_source_ae (-a) a p)
  have hne₁ : ∀ᵐ x ∂massMeasure, x ≠ a :=
    (withDensity_absolutelyContinuous volume _).ae_le (volume.ae_ne a)
  have hne₂ : ∀ᵐ x ∂massMeasure, x ≠ -a :=
    (withDensity_absolutelyContinuous volume _).ae_le (volume.ae_ne (-a))
  filter_upwards [reflectMass_coeFn (sharpIntervalGraph (-a) a p).val.fst,
    hcut, sharpIntervalGraph_source_ae (-a) a (reflectGraph p),
    reflectMass_coeFn p.val.fst, hne₁, hne₂] with x hr hc hs hp hxp hxm
  simp only [Function.comp_apply] at hc
  rw [hr, hc, hs]
  have hmem : -x ∈ Ico (-a) a ↔ x ∈ Ico (-a) a := by
    simp only [mem_Ico]
    constructor
    · intro h
      exact ⟨by linarith [h.2], lt_of_le_of_ne (by linarith [h.1]) hxp⟩
    · intro h
      have hx : -a < x := lt_of_le_of_ne h.1 hxm.symm
      exact ⟨by linarith [h.2], by linarith⟩
  by_cases hx : x ∈ Ico (-a) a
  · simp only [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx), reflectGraph_fst, hp]
  · simp only [indicator_of_notMem hx, indicator_of_notMem (not_iff_not.mpr hmem |>.mpr hx)]

/-- Odd maximal states retain their parity under exact interval localization. -/
theorem sharpIntervalGraph_fst_mem_oddSector (a : ℝ) {p : SourceGraph}
    (hp : p.val.fst ∈ oddSector) :
    (sharpIntervalGraph (-a) a p).val.fst ∈ oddSector := by
  rw [mem_oddSector, ← reflectGraph_fst, reflectGraph_sharpIntervalGraph,
    reflectGraph_eq_neg_of_odd hp]
  change (sharpIntervalGraphCLM (-a) a (-p)).val.fst = -(sharpIntervalGraph (-a) a p).val.fst
  rw [map_neg]
  rfl

private theorem sharpIntervalGraph_eventually_compactLift
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    ∀ᶠ n : ℕ in atTop,
      sharpIntervalGraph (-(n:ℝ)) n (compactLift v hv hc) = compactLift v hv hc := by
  obtain ⟨a, ha0, ha⟩ := hc.exists_pos_le_norm
  have hn : ∀ᶠ n : ℕ in atTop, a < (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop a)
  filter_upwards [hn] with n hn
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [sharpIntervalGraph_source_ae (-(n:ℝ)) n (compactLift v hv hc),
    compactLift_source_ae v hv hc] with x hcut hvx
  rw [hcut]
  by_cases hx : x ∈ Ico (-(n:ℝ)) n
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, hvx]
    symm
    apply ha
    rw [Real.norm_eq_abs]
    by_contra habs
    have habs' := abs_lt.mp (lt_of_not_ge habs)
    exact hx ⟨by linarith [habs'.1], by linarith [habs'.2]⟩

/-- Expanding sharp windows converge in the complete graph norm, including
every prime-power edge and the singular archimedean component. -/
theorem tendsto_sharpIntervalGraph (p : SourceGraph) :
    Tendsto (fun n : ℕ => sharpIntervalGraph (-(n:ℝ)) n p) atTop (𝓝 p) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_sharpIntervalGraph_bound
  have hbound (n : ℕ) : ‖sharpIntervalGraphCLM (-(n:ℝ)) n‖ ≤ C + 1 := by
    apply ContinuousLinearMap.opNorm_le_bound (sharpIntervalGraphCLM (-(n:ℝ)) n)
      (by linarith : 0 ≤ C+1)
    intro q
    rw [sharpIntervalGraphCLM_apply]
    exact (hb (-(n:ℝ)) n q).trans (by nlinarith only [norm_nonneg q])
  have hid : ‖ContinuousLinearMap.id ℝ SourceGraph‖ ≤ C + 1 :=
    ContinuousLinearMap.norm_id_le.trans (by linarith)
  have hconv : ∀ q ∈ (compactTests : Set SourceGraph),
      Tendsto (fun n : ℕ => sharpIntervalGraphCLM (-(n:ℝ)) n q) atTop (𝓝 q) := by
    rintro q ⟨v, hv, hc, rfl⟩
    simp only [sharpIntervalGraphCLM_apply]
    have heq : (fun _ : ℕ => compactLift v hv hc) =ᶠ[atTop]
        (fun n : ℕ => sharpIntervalGraph (-(n:ℝ)) n (compactLift v hv hc)) :=
      (sharpIntervalGraph_eventually_compactLift v hv hc).mono fun _ h => h.symm
    exact tendsto_const_nhds.congr' heq
  have h := GaloisForLFunctions.HTGeometry.tendsto_of_dense_of_uniform_bound
    (T := fun n : ℕ => sharpIntervalGraphCLM (-(n:ℝ)) n)
    (S := ContinuousLinearMap.id ℝ SourceGraph) (by linarith : 0 ≤ C+1)
    (Eventually.of_forall hbound) hid dense_compactTests hconv p
  simpa only [sharpIntervalGraphCLM_apply, ContinuousLinearMap.id_apply] using h

/-- Sharp restriction commutes with the positive lobe as an exact graph identity. -/
theorem sharpIntervalGraph_posGraph (lo hi : ℝ) (p : SourceGraph) :
    sharpIntervalGraph lo hi (posGraph p) = posGraph (sharpIntervalGraph lo hi p) := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [sharpIntervalGraph_source_ae lo hi (posGraph p),
    posGraph_fst_ae (sharpIntervalGraph lo hi p),
    sharpIntervalGraph_source_ae lo hi p, posGraph_fst_ae p] with x hc hp hcut hpos
  rw [hc, hp, hcut]
  by_cases hx : x ∈ Ico lo hi
  · simp only [indicator_of_mem hx, hpos]
  · simp only [indicator_of_notMem hx, posFun_zero]

/-- Sharp restriction commutes with the negative lobe as an exact graph identity. -/
theorem sharpIntervalGraph_negGraph (lo hi : ℝ) (p : SourceGraph) :
    sharpIntervalGraph lo hi (negGraph p) = negGraph (sharpIntervalGraph lo hi p) := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [sharpIntervalGraph_source_ae lo hi (negGraph p),
    negGraph_fst_ae (sharpIntervalGraph lo hi p),
    sharpIntervalGraph_source_ae lo hi p, negGraph_fst_ae p] with x hc hp hcut hneg
  rw [hc, hp, hcut]
  by_cases hx : x ∈ Ico lo hi
  · simp only [indicator_of_mem hx, hneg]
  · simp only [indicator_of_notMem hx, negFun_zero]

/-- Sharp restriction commutes with modulus as an exact graph identity. -/
theorem sharpIntervalGraph_absGraph (lo hi : ℝ) (p : SourceGraph) :
    sharpIntervalGraph lo hi (absGraph p) = absGraph (sharpIntervalGraph lo hi p) := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [sharpIntervalGraph_source_ae lo hi (absGraph p),
    absGraph_fst_ae (sharpIntervalGraph lo hi p),
    sharpIntervalGraph_source_ae lo hi p, absGraph_fst_ae p] with x hc hp hcut habs
  rw [hc, hp, hcut]
  by_cases hx : x ∈ Ico lo hi
  · simp only [indicator_of_mem hx, habs]
  · simp only [indicator_of_notMem hx, absFun_zero]

theorem tendsto_posGraph_sharpIntervalGraph (p : SourceGraph) :
    Tendsto (fun n : ℕ => posGraph (sharpIntervalGraph (-(n:ℝ)) n p))
      atTop (𝓝 (posGraph p)) := by
  simpa only [sharpIntervalGraph_posGraph] using tendsto_sharpIntervalGraph (posGraph p)

theorem tendsto_negGraph_sharpIntervalGraph (p : SourceGraph) :
    Tendsto (fun n : ℕ => negGraph (sharpIntervalGraph (-(n:ℝ)) n p))
      atTop (𝓝 (negGraph p)) := by
  simpa only [sharpIntervalGraph_negGraph] using tendsto_sharpIntervalGraph (negGraph p)

theorem tendsto_absGraph_sharpIntervalGraph (p : SourceGraph) :
    Tendsto (fun n : ℕ => absGraph (sharpIntervalGraph (-(n:ℝ)) n p))
      atTop (𝓝 (absGraph p)) := by
  simpa only [sharpIntervalGraph_absGraph] using tendsto_sharpIntervalGraph (absGraph p)

/-- The full signed Weil energy is recovered from exact-support windows. -/
theorem tendsto_weilForm_sharpIntervalGraph (p : SourceGraph) :
    Tendsto (fun n : ℕ => weilForm (sharpIntervalGraph (-(n:ℝ)) n p))
      atTop (𝓝 (weilForm p)) :=
  continuous_weilForm.continuousAt.tendsto.comp (tendsto_sharpIntervalGraph p)

private theorem sharpWindow_pair_tendsto {u v : ℕ → SourceGraph} {p q : SourceGraph}
    (hu : Tendsto u atTop (𝓝 p)) (hv : Tendsto v atTop (𝓝 q)) :
    Tendsto (fun n => sourcePair (u n) (v n)) atTop (𝓝 (sourcePair p q)) := by
  have heu : Tendsto (fun n => edgeMap (u n)) atTop (𝓝 (edgeMap p)) :=
    (edgeMap.continuous.tendsto p).comp hu
  have hev : Tendsto (fun n => edgeMap (v n)) atTop (𝓝 (edgeMap q)) :=
    (edgeMap.continuous.tendsto q).comp hv
  have hsu : Tendsto (fun n => sourceMap (u n)) atTop (𝓝 (sourceMap p)) :=
    (sourceMap.continuous.tendsto p).comp hu
  have hsv : Tendsto (fun n => sourceMap (v n)) atTop (𝓝 (sourceMap q)) :=
    (sourceMap.continuous.tendsto q).comp hv
  exact (heu.inner (𝕜 := ℝ) hev).sub (hsu.inner (𝕜 := ℝ) hsv)

/-- Localization retains the complete signed interaction between the two nodal lobes. -/
theorem tendsto_sourcePair_nodal_sharpIntervalGraph (p : SourceGraph) :
    Tendsto (fun n : ℕ => sourcePair
      (posGraph (sharpIntervalGraph (-(n:ℝ)) n p))
      (negGraph (sharpIntervalGraph (-(n:ℝ)) n p))) atTop
      (𝓝 (sourcePair (posGraph p) (negGraph p))) := by
  exact sharpWindow_pair_tendsto
    (u := fun n => posGraph (sharpIntervalGraph (-(n:ℝ)) n p))
    (v := fun n => negGraph (sharpIntervalGraph (-(n:ℝ)) n p))
    (tendsto_posGraph_sharpIntervalGraph p) (tendsto_negGraph_sharpIntervalGraph p)

/-- The signed nodal defect, including its squared ground-state moment,
converges under exact localization. -/
theorem tendsto_oneL_defect_sharpIntervalGraph (p : SourceGraph) :
    Tendsto (fun n : ℕ =>
      -4 * sourcePair (posGraph (sharpIntervalGraph (-(n:ℝ)) n p))
        (negGraph (sharpIntervalGraph (-(n:ℝ)) n p)) -
      2 * ⟪(absGraph (sharpIntervalGraph (-(n:ℝ)) n p)).val.fst, oneL⟫_ℝ ^ 2)
      atTop (𝓝 (-4 * sourcePair (posGraph p) (negGraph p) -
        2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2)) := by
  have hs : Tendsto (fun n : ℕ =>
      sourceMap (absGraph (sharpIntervalGraph (-(n:ℝ)) n p))) atTop
        (𝓝 (sourceMap (absGraph p))) :=
    (sourceMap.continuous.tendsto (absGraph p)).comp (tendsto_absGraph_sharpIntervalGraph p)
  have hm : Tendsto (fun n : ℕ =>
      ⟪sourceMap (absGraph (sharpIntervalGraph (-(n:ℝ)) n p)), oneL⟫_ℝ) atTop
        (𝓝 ⟪sourceMap (absGraph p), oneL⟫_ℝ) :=
    hs.inner (𝕜 := ℝ) (tendsto_const_nhds (x := oneL))
  exact ((tendsto_sourcePair_nodal_sharpIntervalGraph p).const_mul (-4)).sub
    ((hm.pow 2).const_mul 2)


end RHTower
