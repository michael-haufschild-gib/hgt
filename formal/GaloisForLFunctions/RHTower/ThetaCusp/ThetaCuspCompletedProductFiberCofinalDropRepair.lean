import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompletedProductFiberOddPtolemyNoGo

/-!
# Cofinal product-fibre repair of the first-shell seam rise

The first completed product fibre rises away from the modular seam, whereas the
fully completed reflected theta source decreases strictly at every positive
displacement. Absolute product-fibre summability turns this mismatch into an
exact cofinal repair law: the combined drop of every higher fibre is strictly
larger than the first-fibre rise. The strict repair persists on a right germ of
positive centres.

This is the positive survivor of the fibrewise odd-Ptolemy no-go. It proves
that higher-shell cancellation repairs monotonicity before any aggregate
fifth-root curvature or projective-antitonicity argument can start.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Cofinal sum of completed product fibres strictly above the first fibre. -/
def thetaCuspCompletedProductFiberHigherTail (u t : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspCompletedProductFiberAmplitude (k + 2) u t

/-- Product fibre zero is empty. -/
theorem thetaCuspCompletedProductFiberAmplitude_zero (u t : ℝ) :
    thetaCuspCompletedProductFiberAmplitude 0 u t = 0 := by
  simp [thetaCuspCompletedProductFiberAmplitude, thetaPositiveFactorPairs]

/-- Exact decomposition into first fibre and cofinal higher tail. -/
theorem thetaCuspCompletedProductFiberAmplitude_one_add_higherTail
    (u t : ℝ) :
    thetaCuspCompletedProductFiberAmplitude 1 u t +
        thetaCuspCompletedProductFiberHigherTail u t =
      thetaCuspReflectedSourceProduct u t := by
  let f : ℕ → ℝ := fun k => thetaCuspCompletedProductFiberAmplitude k u t
  have hf : Summable f := summable_thetaCuspCompletedProductFiberAmplitude u t
  have hsplit := hf.sum_add_tsum_nat_add 2
  have hcofinal := tsum_thetaCuspCompletedProductFiberAmplitude_eq_fullSourceProduct u t
  unfold thetaCuspCompletedProductFiberHigherTail thetaCuspReflectedSourceProduct
  change f 1 + ∑' k : ℕ, f (k + 2) = _
  rw [← hcofinal, ← hsplit]
  norm_num [Finset.sum_range_succ, f,
    thetaCuspCompletedProductFiberAmplitude_zero]

/-- At the seam, higher fibres strictly over-repair one first-fibre rise. -/
theorem exists_thetaCuspCompletedProductFiberHigherTail_drop_repairs_first_rise :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspCompletedProductFiberAmplitude 1 0 t -
          thetaCuspCompletedProductFiberAmplitude 1 0 0 <
        thetaCuspCompletedProductFiberHigherTail 0 0 -
          thetaCuspCompletedProductFiberHigherTail 0 t := by
  obtain ⟨t, ht, hrise⟩ :=
    exists_thetaCuspCompletedProductFiberAmplitude_one_rise
  have hdrop := thetaCuspReflectedSourceFirstDrop_pos 0 ht
  have hzero := thetaCuspCompletedProductFiberAmplitude_one_add_higherTail 0 0
  have htval := thetaCuspCompletedProductFiberAmplitude_one_add_higherTail 0 t
  unfold thetaCuspReflectedSourceFirstDrop at hdrop
  refine ⟨t, ht, ?_⟩
  linarith

theorem continuous_thetaCuspCompletedProductFiberAmplitude_one_left
    (t : ℝ) :
    Continuous (fun u => thetaCuspCompletedProductFiberAmplitude 1 u t) := by
  simp_rw [thetaCuspCompletedProductFiberAmplitude_one]
  have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x 1) :=
    continuous_thetaCuspSourceTerm_one
  exact
    (hsource.comp (continuous_abs.comp (continuous_id.add continuous_const))).mul
      (hsource.comp (continuous_abs.comp (continuous_id.sub continuous_const)))

/-- Cofinal drop repair persists on a right germ of positive centres. -/
theorem exists_thetaCuspCompletedProductFiberHigherTail_drop_repairs_first_rise_germ :
    ∃ t : ℝ, 0 < t ∧ ∀ᶠ u : ℝ in 𝓝[>] 0,
      thetaCuspCompletedProductFiberAmplitude 1 u t -
          thetaCuspCompletedProductFiberAmplitude 1 u 0 <
        thetaCuspCompletedProductFiberHigherTail u 0 -
          thetaCuspCompletedProductFiberHigherTail u t := by
  obtain ⟨t, ht, hrise⟩ :=
    exists_thetaCuspCompletedProductFiberAmplitude_one_rise
  have hcont : Continuous (fun u : ℝ =>
      thetaCuspCompletedProductFiberAmplitude 1 u t -
        thetaCuspCompletedProductFiberAmplitude 1 u 0) :=
    (continuous_thetaCuspCompletedProductFiberAmplitude_one_left t).sub
      (continuous_thetaCuspCompletedProductFiberAmplitude_one_left 0)
  have hnear : ∀ᶠ u : ℝ in nhds 0,
      0 < thetaCuspCompletedProductFiberAmplitude 1 u t -
        thetaCuspCompletedProductFiberAmplitude 1 u 0 :=
    hcont.continuousAt.tendsto.eventually (eventually_gt_nhds (sub_pos.mpr hrise))
  have hnearRight : ∀ᶠ u : ℝ in 𝓝[>] 0,
      0 < thetaCuspCompletedProductFiberAmplitude 1 u t -
        thetaCuspCompletedProductFiberAmplitude 1 u 0 :=
    hnear.filter_mono (show 𝓝[>] (0 : ℝ) ≤ nhds 0 from inf_le_left)
  refine ⟨t, ht, ?_⟩
  filter_upwards [hnearRight] with u hu
  have hdrop := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hzero := thetaCuspCompletedProductFiberAmplitude_one_add_higherTail u 0
  have htval := thetaCuspCompletedProductFiberAmplitude_one_add_higherTail u t
  unfold thetaCuspReflectedSourceFirstDrop at hdrop
  linarith

/-- A strictly positive centre witnesses cofinal higher-fibre repair. -/
theorem exists_pos_thetaCuspCompletedProductFiberHigherTail_drop_repairs_first_rise :
    ∃ u t : ℝ, 0 < u ∧ 0 < t ∧
      thetaCuspCompletedProductFiberAmplitude 1 u t -
          thetaCuspCompletedProductFiberAmplitude 1 u 0 <
        thetaCuspCompletedProductFiberHigherTail u 0 -
          thetaCuspCompletedProductFiberHigherTail u t := by
  obtain ⟨t, ht, hrepair⟩ :=
    exists_thetaCuspCompletedProductFiberHigherTail_drop_repairs_first_rise_germ
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  obtain ⟨u, hrepairu, hu⟩ := (hrepair.and hpos).exists
  exact ⟨u, t, hu, ht, hrepairu⟩

end

end RHTower
