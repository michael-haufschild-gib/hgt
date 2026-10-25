import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicCancellationInTheVaughanConvolution
import GaloisForLFunctions.BezoutValuationIncidence.SignedVaughanTailsVanishAtTheirAbsoluteScale
import GaloisForLFunctions.RHTower.FiniteMobiusHarmonicSumsNeverVanish
import Mathlib.Topology.Compactness.Compact

/-!
Products of squared finite Möbius harmonic sums form a compact countably infinite
set. Nonzero amplitudes lie in finite cutoff rectangles; at positive cutoffs,
vanishing amplitude is equivalent to escape of the cutoff product.
-/

open Finset Filter RHTower
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The arithmetic amplitudes of the subcritical smooth Vaughan Gram. -/
def pmVaughanSmoothAmplitudeSet : Set ℝ :=
  Set.range (fun a : ℕ × ℕ => deningerHarmonicPartial a.1 ^ 2 * deningerHarmonicPartial a.2 ^ 2)

private theorem harmonic_tendsto_zero : Tendsto deningerHarmonicPartial atTop (𝓝 0) := by
  simpa only [pow_zero, one_mul] using Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 0

private theorem harmonic_zero : deningerHarmonicPartial 0 = 0 := by
  simp [deningerHarmonicPartial]

private theorem harmonic_one : deningerHarmonicPartial 1 = 1 := by
  simp [deningerHarmonicPartial, Finset.sum_range_succ]

private theorem harmonic_ne_zero {N : ℕ} (hN : 1 ≤ N) : deningerHarmonicPartial N ≠ 0 := by
  rw [deningerHarmonicPartial_eq_sum_Icc]
  exact sum_moebius_div_ne_zero hN

private theorem harmonic_sq_le_one (N : ℕ) : deningerHarmonicPartial N ^ 2 ≤ 1 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_deningerHarmonicPartial_le_one N) 2
  simpa only [sq_abs, one_pow] using h

/-- Zero is an actual amplitude, realized by a zero cutoff. -/
theorem zero_mem_pmVaughanSmoothAmplitudeSet : 0 ∈ pmVaughanSmoothAmplitudeSet := by
  refine ⟨(0, 0), ?_⟩
  simp only [harmonic_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]

/-- The unit cutoffs attain the maximal amplitude. -/
theorem one_mem_pmVaughanSmoothAmplitudeSet : 1 ∈ pmVaughanSmoothAmplitudeSet := by
  refine ⟨(1, 1), ?_⟩
  simp only [harmonic_one, one_pow, one_mul]

theorem pmVaughanSmoothAmplitudeSet_nonneg {a : ℝ} (ha : a ∈ pmVaughanSmoothAmplitudeSet) : 0 ≤ a := by
  obtain ⟨⟨U, V⟩, rfl⟩ := ha
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem pmVaughanSmoothAmplitudeSet_le_one {a : ℝ} (ha : a ∈ pmVaughanSmoothAmplitudeSet) : a ≤ 1 := by
  obtain ⟨⟨U, V⟩, rfl⟩ := ha
  simpa only [one_mul] using mul_le_mul (harmonic_sq_le_one U)
    (harmonic_sq_le_one V) (sq_nonneg _) zero_le_one

/-- The amplitude set is countable because its cutoffs are natural numbers. -/
theorem countable_pmVaughanSmoothAmplitudeSet : pmVaughanSmoothAmplitudeSet.Countable :=
  Set.countable_range _

/-- The harmonic range is compact because it contains its limiting value. -/
theorem isCompact_range_deningerHarmonicPartial : IsCompact (Set.range deningerHarmonicPartial) := by
  have hz : (0 : ℝ) ∈ Set.range deningerHarmonicPartial := ⟨0, harmonic_zero⟩
  simpa only [Set.insert_eq_of_mem hz] using harmonic_tendsto_zero.isCompact_insert_range

/-- The amplitude set is the continuous square-product image of two compact harmonic ranges. -/
theorem isCompact_pmVaughanSmoothAmplitudeSet : IsCompact pmVaughanSmoothAmplitudeSet := by
  have hcompact := (isCompact_range_deningerHarmonicPartial.prod isCompact_range_deningerHarmonicPartial).image
    ((continuous_fst.pow 2).mul (continuous_snd.pow 2))
  convert hcompact using 1
  ext x
  simp only [pmVaughanSmoothAmplitudeSet, Set.mem_range, Set.mem_image, Set.mem_prod]
  constructor
  · rintro ⟨⟨U, V⟩, rfl⟩
    exact ⟨(deningerHarmonicPartial U, deningerHarmonicPartial V),
      ⟨⟨U, rfl⟩, ⟨V, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨u, v⟩, ⟨⟨U, rfl⟩, ⟨V, rfl⟩⟩, rfl⟩
    exact ⟨(U, V), rfl⟩

/-- Every amplitude bounded away from zero has both cutoffs in one fixed finite rectangle. -/
theorem exists_cutoff_bound_of_pmVaughanSmoothAmplitude_ge {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ U V : ℕ, δ ≤ deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2 →
      U < N ∧ V < N := by
  have hlim : Tendsto (fun N : ℕ => deningerHarmonicPartial N ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using harmonic_tendsto_zero.pow 2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun U V hUV => ⟨?_, ?_⟩⟩
  · by_contra hU
    have hprod : deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2 ≤
        deningerHarmonicPartial U ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg _) (harmonic_sq_le_one V)
    exact (not_lt_of_ge (hUV.trans hprod)) (hN U (not_lt.mp hU))
  · by_contra hV
    have hprod : deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2 ≤
        deningerHarmonicPartial V ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (harmonic_sq_le_one U)
    exact (not_lt_of_ge (hUV.trans hprod)) (hN V (not_lt.mp hV))

/-- Arbitrarily small positive amplitudes occur at positive cutoffs. -/
theorem exists_pos_pmVaughanSmoothAmplitude_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ a ∈ pmVaughanSmoothAmplitudeSet, 0 < a ∧ a < δ := by
  have hlim : Tendsto (fun N : ℕ => deningerHarmonicPartial N ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using harmonic_tendsto_zero.pow 2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨deningerHarmonicPartial (max N 1) ^ 2, ?_,
    sq_pos_of_ne_zero (harmonic_ne_zero (le_max_right N 1)), hN _ (le_max_left N 1)⟩
  refine ⟨(max N 1, 1), ?_⟩
  simp only [harmonic_one, one_pow, mul_one]

/-- Finite harmonic nonvanishing makes the compact amplitude set infinite. -/
theorem infinite_pmVaughanSmoothAmplitudeSet : pmVaughanSmoothAmplitudeSet.Infinite := by
  intro hfinite
  have hclosed : IsClosed (pmVaughanSmoothAmplitudeSet \ {0}) :=
    (hfinite.subset Set.diff_subset).isClosed
  have hlim : Tendsto (fun N : ℕ => deningerHarmonicPartial (N + 1) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (harmonic_tendsto_zero.comp (tendsto_add_atTop_nat 1)).pow 2
  have hmem : ∀ N : ℕ, deningerHarmonicPartial (N + 1) ^ 2 ∈ pmVaughanSmoothAmplitudeSet \ {0} := by
    intro N
    refine ⟨⟨(N + 1, 1), ?_⟩, ?_⟩
    · simp only [harmonic_one, one_pow, mul_one]
    · simpa only [Set.mem_singleton_iff] using pow_ne_zero 2 (harmonic_ne_zero (by omega))
  have h := hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  exact h.2 rfl

private theorem eventually_eq_of_tendsto_in_finite_set {S : Set ℝ} (hS : S.Finite)
    {f : ℕ → ℝ} {a : ℝ} (hmem : ∀ᶠ n : ℕ in atTop, f n ∈ S)
    (hlim : Tendsto f atTop (𝓝 a)) : ∀ᶠ n : ℕ in atTop, f n = a := by
  have hclosed : IsClosed (S \ {a}) := (hS.subset Set.diff_subset).isClosed
  have hnhood : (S \ {a})ᶜ ∈ 𝓝 a := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hmem, hlim.eventually hnhood] with n hn hnot
  by_contra hne
  exact hnot ⟨hn, hne⟩

/-- A positive limiting smooth amplitude must eventually be attained exactly. -/
theorem eventually_eq_pmVaughanSmoothAmplitude_of_tendsto_pos
    (U V : ℕ → ℕ) {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto (fun n => deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2)
      atTop (𝓝 a)) :
    ∀ᶠ n : ℕ in atTop, deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2 = a := by
  classical
  obtain ⟨N, hN⟩ := exists_cutoff_bound_of_pmVaughanSmoothAmplitude_ge (half_pos ha)
  let F : Finset ℝ := ((range N).product (range N)).image
    (fun p : ℕ × ℕ => deningerHarmonicPartial p.1 ^ 2 * deningerHarmonicPartial p.2 ^ 2)
  have hmem : ∀ᶠ n : ℕ in atTop,
      deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2 ∈ (F : Set ℝ) := by
    filter_upwards [hlim.eventually (lt_mem_nhds (by linarith only [ha] : a / 2 < a))] with n hn
    have hcut := hN (U n) (V n) hn.le
    exact mem_image.mpr ⟨(U n, V n), mem_product.mpr ⟨mem_range.mpr hcut.1, mem_range.mpr hcut.2⟩, rfl⟩
  exact eventually_eq_of_tendsto_in_finite_set F.finite_toSet hmem hlim

/-- A positive amplitude limit confines the cutoff pair to one finite fiber. -/
theorem eventually_finite_fiber_of_pmVaughanSmoothAmplitude_tendsto_pos
    (U V : ℕ → ℕ) {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto (fun n => deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2)
      atTop (𝓝 a)) :
    ∃ N : ℕ, ∀ᶠ n : ℕ in atTop, U n < N ∧ V n < N ∧
      deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2 = a := by
  obtain ⟨N, hN⟩ := exists_cutoff_bound_of_pmVaughanSmoothAmplitude_ge ha
  refine ⟨N, ?_⟩
  filter_upwards [eventually_eq_pmVaughanSmoothAmplitude_of_tendsto_pos U V ha hlim] with n hn
  have hcut := hN (U n) (V n) hn.ge
  exact ⟨hcut.1, hcut.2, hn⟩

/-- Vanishing harmonic amplitude forces every bounded positive-cutoff rectangle to be left eventually. -/
theorem tendsto_product_of_pmVaughanSmoothAmplitude_tendsto_zero
    (U V : ℕ → ℕ) (hU : ∀ n, 1 ≤ U n) (hV : ∀ n, 1 ≤ V n)
    (hlim : Tendsto (fun n => deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2)
      atTop (𝓝 0)) : Tendsto (fun n => U n * V n) atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro B
  let F : Finset ℝ := ((Icc 1 B).product (Icc 1 B)).image
    (fun p : ℕ × ℕ => deningerHarmonicPartial p.1 ^ 2 * deningerHarmonicPartial p.2 ^ 2)
  have hz : (0 : ℝ) ∉ (F : Set ℝ) := by
    intro hz
    obtain ⟨⟨u, v⟩, huv, heq⟩ := mem_image.mp hz
    have hu := (mem_Icc.mp (mem_product.mp huv).1).1
    have hv := (mem_Icc.mp (mem_product.mp huv).2).1
    exact (mul_ne_zero (pow_ne_zero 2 (harmonic_ne_zero hu))
      (pow_ne_zero 2 (harmonic_ne_zero hv))) heq
  have hnhds : (F : Set ℝ)ᶜ ∈ 𝓝 (0 : ℝ) :=
    F.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
  filter_upwards [hlim.eventually hnhds] with n hn
  by_contra hprod
  have hprod' : U n * V n < B := lt_of_not_ge hprod
  have hUn : U n ≤ U n * V n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (U n) (hV n)
  have hVn : V n ≤ U n * V n := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (V n) (hU n)
  apply hn
  exact mem_image.mpr ⟨(U n, V n), mem_product.mpr
    ⟨mem_Icc.mpr ⟨hU n, hUn.trans hprod'.le⟩,
      mem_Icc.mpr ⟨hV n, hVn.trans hprod'.le⟩⟩, rfl⟩

/-- For positive cutoffs, zero harmonic amplitude is exactly escape of their product. -/
theorem tendsto_pmVaughanSmoothAmplitude_zero_iff_product
    (U V : ℕ → ℕ) (hU : ∀ n, 1 ≤ U n) (hV : ∀ n, 1 ≤ V n) :
    Tendsto (fun n => deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2)
      atTop (𝓝 0) ↔ Tendsto (fun n => U n * V n) atTop atTop := by
  constructor
  · exact tendsto_product_of_pmVaughanSmoothAmplitude_tendsto_zero U V hU hV
  · intro hUV
    have h := tendsto_mul_of_product_indices_atTop zero_le_one
      abs_deningerHarmonicPartial_le_one harmonic_tendsto_zero U V hUV
    simpa only [mul_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h.pow 2

#print axioms zero_mem_pmVaughanSmoothAmplitudeSet
#print axioms one_mem_pmVaughanSmoothAmplitudeSet
#print axioms pmVaughanSmoothAmplitudeSet_nonneg
#print axioms pmVaughanSmoothAmplitudeSet_le_one
#print axioms countable_pmVaughanSmoothAmplitudeSet
#print axioms isCompact_range_deningerHarmonicPartial
#print axioms isCompact_pmVaughanSmoothAmplitudeSet
#print axioms exists_cutoff_bound_of_pmVaughanSmoothAmplitude_ge
#print axioms exists_pos_pmVaughanSmoothAmplitude_lt
#print axioms infinite_pmVaughanSmoothAmplitudeSet
#print axioms eventually_eq_pmVaughanSmoothAmplitude_of_tendsto_pos
#print axioms eventually_finite_fiber_of_pmVaughanSmoothAmplitude_tendsto_pos
#print axioms tendsto_product_of_pmVaughanSmoothAmplitude_tendsto_zero
#print axioms tendsto_pmVaughanSmoothAmplitude_zero_iff_product
end GaloisForLFunctions.BezoutValuationIncidence
