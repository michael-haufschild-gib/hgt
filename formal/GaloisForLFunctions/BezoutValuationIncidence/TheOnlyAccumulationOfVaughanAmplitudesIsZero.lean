import GaloisForLFunctions.BezoutValuationIncidence.TheCompactArithmeticAmplitudesOfVaughanGrams
import Mathlib.Topology.ClusterPt

/-!
Every positive Möbius harmonic amplitude is isolated. Finiteness above each
positive level and arbitrarily small positive amplitudes identify zero as the
unique accumulation point.
-/

open Finset Filter RHTower
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Only finitely many smooth amplitudes can exceed a fixed positive level. -/
theorem finite_pmVaughanSmoothAmplitudeSet_above {δ : ℝ} (hδ : 0 < δ) :
    {a ∈ pmVaughanSmoothAmplitudeSet | δ ≤ a}.Finite := by
  classical
  obtain ⟨N, hN⟩ := exists_cutoff_bound_of_pmVaughanSmoothAmplitude_ge hδ
  let F : Finset ℝ := ((range N).product (range N)).image
    (fun p : ℕ × ℕ => deningerHarmonicPartial p.1 ^ 2 * deningerHarmonicPartial p.2 ^ 2)
  apply F.finite_toSet.subset
  rintro a ⟨⟨⟨U, V⟩, rfl⟩, ha⟩
  have hcut := hN U V ha
  exact mem_image.mpr ⟨(U, V), mem_product.mpr
    ⟨mem_range.mpr hcut.1, mem_range.mpr hcut.2⟩, rfl⟩

private theorem punctured_amplitude_compl_mem_nhds {a : ℝ} (ha : 0 < a) :
    (pmVaughanSmoothAmplitudeSet \ {a})ᶜ ∈ 𝓝 a := by
  let F : Set ℝ := {b ∈ pmVaughanSmoothAmplitudeSet | a / 2 ≤ b}
  have hfinite : F.Finite := finite_pmVaughanSmoothAmplitudeSet_above (half_pos ha)
  have hc : (F \ {a})ᶜ ∈ 𝓝 a :=
    (hfinite.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hc, lt_mem_nhds (by linarith only [ha] : a / 2 < a)] with b hb hba
  rintro ⟨hbs, hne⟩
  exact hb ⟨⟨hbs, hba.le⟩, hne⟩

/-- Every positive amplitude is isolated from all other amplitudes. -/
theorem isolated_pmVaughanSmoothAmplitude_of_pos {a : ℝ} (ha : 0 < a) :
    ∃ δ > 0, ∀ b ∈ pmVaughanSmoothAmplitudeSet, |b - a| < δ → b = a := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (punctured_amplitude_compl_mem_nhds ha)
  refine ⟨δ, hδ, fun b hb hdist => ?_⟩
  by_contra hne
  have hmem : b ∈ Metric.ball a δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hdist
  exact (hball hmem) ⟨hb, hne⟩

/-- Zero is the unique accumulation point of the compact arithmetic amplitude set. -/
theorem accPt_pmVaughanSmoothAmplitudeSet_iff (a : ℝ) :
    AccPt a (𝓟 pmVaughanSmoothAmplitudeSet) ↔ a = 0 := by
  constructor
  · intro hacc
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · obtain ⟨b, hb, _⟩ := accPt_iff_nhds.mp hacc (Set.Iio 0) (gt_mem_nhds hneg)
      exact (not_lt_of_ge (pmVaughanSmoothAmplitudeSet_nonneg hb.2)) hb.1
    · obtain ⟨b, hb, hba⟩ := accPt_iff_nhds.mp hacc
        (pmVaughanSmoothAmplitudeSet \ {a})ᶜ (punctured_amplitude_compl_mem_nhds hpos)
      exact hb.1 ⟨hb.2, hba⟩
  · rintro rfl
    apply accPt_iff_nhds.mpr
    intro U hU
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨b, hb, hb0, hbδ⟩ := exists_pos_pmVaughanSmoothAmplitude_lt hδ
    refine ⟨b, ⟨hball ?_, hb⟩, hb0.ne'⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hb0] using hbδ

/-- Product escape and an eventually fixed positive amplitude are mutually exclusive. -/
theorem not_product_escape_and_eventually_positive_amplitude
    (U V : ℕ → ℕ) (hU : ∀ t, 1 ≤ U t) (hV : ∀ t, 1 ≤ V t) :
    ¬ (Tendsto (fun t => U t * V t) atTop atTop ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ t : ℕ in atTop,
        deningerHarmonicPartial (U t) ^ 2 * deningerHarmonicPartial (V t) ^ 2 = a) := by
  rintro ⟨hUV, a, ha, heq⟩
  have hzero := (tendsto_pmVaughanSmoothAmplitude_zero_iff_product U V hU hV).mpr hUV
  have hconst : Tendsto (fun t =>
      deningerHarmonicPartial (U t) ^ 2 * deningerHarmonicPartial (V t) ^ 2) atTop (𝓝 a) :=
    (tendsto_congr' heq).mpr tendsto_const_nhds
  exact ha.ne' (tendsto_nhds_unique hconst hzero)

#print axioms finite_pmVaughanSmoothAmplitudeSet_above
#print axioms not_product_escape_and_eventually_positive_amplitude
#print axioms isolated_pmVaughanSmoothAmplitude_of_pos
#print axioms accPt_pmVaughanSmoothAmplitudeSet_iff
end GaloisForLFunctions.BezoutValuationIncidence
