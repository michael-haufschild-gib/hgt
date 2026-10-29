import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.RamanujanQuasimodesAreUniformThroughTouching
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPacketPoleCoordinatesSelectConductorOne

/-!
# Finite Ramanujan packets at convergent width ratios

Uniform norm quasimodes through touching allow the atom width to vary with
the horizon. The complete packet limit therefore survives integer rounding
of a zero-padding horizon.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem tendsto_adjunction_variable (φ : ℝ → ℝ) (m : ℕ)
    {r : ℕ → ℝ} {c : ℝ} (hr : Tendsto r atTop (𝓝 c)) (hc : 0 < c) :
    Tendsto (fun N => completeWeilAdjunctionEnergy φ (r N) m)
      atTop (𝓝 (completeWeilAdjunctionEnergy φ c m)) := by
  have hd : 2 * Real.pi * c ≠ 0 := by positivity
  have hl := (tendsto_const_nhds.div (hr.const_mul (2 * Real.pi)) hd).log
    (by positivity : (1 : ℝ) / (2 * Real.pi * c) ≠ 0)
  have hs := ((hl.add_const (bumpRobin φ 1 / (∫ u, φ u ^ 2))).add_const
    (ramanujanAdjunctionEnergy m)).sub_const Real.eulerMascheroniConstant
  by_cases hm : m = 1
  · simpa only [completeWeilAdjunctionEnergy, completeWeilSelfFinitePart,
      completeWeilPoleShift, if_pos hm, Pi.div_apply] using
      hs.add ((hr.mul_const ((∫ u, φ u) ^ 2)).div_const (∫ u, φ u ^ 2))
  · simpa only [completeWeilAdjunctionEnergy, completeWeilSelfFinitePart,
      if_neg hm, add_zero, Pi.div_apply] using hs

/-- Every mixed packet entry has the same limit along a convergent strict ratio. -/
theorem tendsto_completeWeilMatrix_ramanujan_inner_variable {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {r : ℕ → ℝ} {c : ℝ}
    (hr : Tendsto r atTop (𝓝 c)) (hc0 : 0 < c) (hc1 : c < 1)
    {H : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (r N) (H N)) (normalizedRamanujanHorizonVector m (H N)),
        normalizedRamanujanHorizonVector l (H N)⟫)
      atTop (𝓝 (if m = l then completeWeilAdjunctionEnergy φ c m else 0)) := by
  have hres : Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ (r N) (H N)) (normalizedRamanujanHorizonVector m (H N)) -
        completeWeilAdjunctionEnergy φ (r N) m • normalizedRamanujanHorizonVector m (H N)‖)
      atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall fun N => ha.trans_le (norm_nonneg _)
    · intro b hb
      filter_upwards [hH.eventually (eventually_completeWeil_ramanujan_residual_small_uniformly
        hφ hsupp hM hm (half_pos hb)), hr.eventually (lt_mem_nhds hc0),
        hr.eventually (gt_mem_nhds hc1)] with N hN hr0 hr1
      exact (hN (r N) hr0 hr1.le).trans_lt (half_lt_self hb)
  have herr : Tendsto (fun N =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (r N) (H N)) (normalizedRamanujanHorizonVector m (H N)) -
        completeWeilAdjunctionEnergy φ (r N) m • normalizedRamanujanHorizonVector m (H N),
        normalizedRamanujanHorizonVector l (H N)⟫) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => norm_inner_le_norm _ _)
    simpa only [zero_mul, Function.comp_apply] using hres.mul
      ((tendsto_normalizedRamanujanHorizonVector_norm hl).comp hH)
  have hmain := (tendsto_adjunction_variable φ m hr hc0).mul
    ((tendsto_normalizedRamanujanHorizonVector_gram hm hl).comp hH)
  simpa only [Function.comp_apply, inner_sub_left, real_inner_smul_left, sub_add_cancel, zero_add,
    mul_ite, mul_one, mul_zero] using herr.add hmain

private theorem packet_diagonal_sum (S : Finset ℕ) (b e : ℕ → ℝ) :
    (∑ m ∈ S, ∑ l ∈ S, b m * (b l * if m = l then e m else 0)) =
      ∑ m ∈ S, b m ^ 2 * e m := by
  apply sum_congr rfl
  intro m hm
  rw [sum_eq_single m]
  · rw [if_pos rfl]
    ring
  · intro l _ hl
    rw [if_neg (Ne.symm hl), mul_zero, mul_zero]
  · exact fun h => False.elim (h hm)

private theorem packet_weil_ratio_eq_matrix {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (S : Finset ℕ) (b : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    weilQuad (ramanujanPacketTest φ c S b N) / ((c / N) * Real.log N) =
      (∫ u, φ u ^ 2) *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanPacketVector S b N),
          normalizedRamanujanPacketVector S b N⟫ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw : 0 < c / N := div_pos hc0 hN0
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hext : atomicTest N (primeHorizonExtension
      (horizonProfileVector (ramanujanPacketProfile S b) N)) (atomDilate φ (c / N)) =
      atomicTest N (ramanujanPacketProfile S b) (atomDilate φ (c / N)) := by
    funext u
    unfold atomicTest
    apply sum_congr rfl
    intro n hn
    have h := primeHorizonExtension_coe (horizonProfileVector (ramanujanPacketProfile S b) N)
      (⟨n, hn⟩ : PrimeHorizonIndex N)
    change primeHorizonExtension (horizonProfileVector (ramanujanPacketProfile S b) N) n =
      ramanujanPacketProfile S b n at h
    rw [h]
  rw [normalizedRamanujanPacketVector_matrix_inner,
    completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc0 (by omega), hext,
    integral_atomDilate_sq hw, ramanujanPacketTest]
  field_simp [hN0.ne', hc0.ne', hM.ne', hlog.ne']

/-- The actual complete form has its finite-packet limit at a convergent width ratio. -/
theorem tendsto_ramanujanPacketTest_weil_variable {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {r : ℕ → ℝ} {c : ℝ}
    (hr : Tendsto r atTop (𝓝 c)) (hc0 : 0 < c) (hc1 : c < 1)
    {H : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ => weilQuad (ramanujanPacketTest φ (r N) S b (H N)) /
      (((r N) / (H N)) * Real.log (H N))) atTop
      (𝓝 ((∫ u, φ u ^ 2) * ∑ m ∈ S, b m ^ 2 * completeWeilAdjunctionEnergy φ c m)) := by
  have h := tendsto_finsetSum S fun m hm => tendsto_finsetSum S fun l hl =>
    ((tendsto_completeWeilMatrix_ramanujan_inner_variable hφ hsupp hM hr hc0 hc1 hH
      (hS m hm) (hS l hl)).const_mul (b l)).const_mul (b m)
  rw [packet_diagonal_sum] at h
  have heq (N : ℕ) :
      (∑ m ∈ S, ∑ l ∈ S, b m * (b l *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (r N) (H N)) (normalizedRamanujanHorizonVector m (H N)),
          normalizedRamanujanHorizonVector l (H N)⟫)) =
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (r N) (H N)) (normalizedRamanujanPacketVector S b (H N)),
          normalizedRamanujanPacketVector S b (H N)⟫ := by
    simp only [normalizedRamanujanPacketVector, map_sum, map_smul, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right]
    rw [sum_comm]
    apply sum_congr rfl
    intro l _
    apply sum_congr rfl
    intro m _
    ring
  have hmat := (h.congr heq).const_mul (∫ u, φ u ^ 2)
  refine hmat.congr' ?_
  filter_upwards [hr.eventually (lt_mem_nhds hc0), hH.eventually (eventually_ge_atTop 2)] with N hrN hN
  exact (packet_weil_ratio_eq_matrix hφ hsupp hM hrN S b hN).symm

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.tendsto_ramanujanPacketTest_weil_variable
