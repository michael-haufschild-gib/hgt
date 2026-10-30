import GaloisForLFunctions.CompletedArithmeticForms.WeilGrowingOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorEnergiesHavePolynomialBounds
import GaloisForLFunctions.SignedArithmeticHodgeTheory.GrowingRamanujanFamiliesHaveAUniformGramBudget
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Complete finite conductor packets at growing overlap

The actual residual and the quantitative Gram discrepancy are both paid
against the common vanishing conductor floor. Every fixed finite family
of distinct positive conductors is therefore positive simultaneously for
all coefficients along `c_N = (log N)^α`, `0 < α < 1/40`.
-/

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  SignedArithmeticHodgeTheory

/-- The actual normalized arithmetic Gram has a conductor-explicit inverse-logarithmic error. -/
theorem normalizedRamanujan_gram_error_le (m l : ℕ+) {N : ℕ} (hN : 2 ≤ N) :
    |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
      (if m = l then 1 else 0)| ≤ (2 * (m : ℝ) * (l : ℝ) + 1) / Real.log N := by
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let H : ℝ := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)
  let δ : ℝ := if m = l then 1 else 0
  have hδ : 0 ≤ δ ∧ δ ≤ 1 := by dsimp only [δ]; split_ifs <;> norm_num
  have hh : |H - Real.log N| ≤ 1 := by
    have hlo : Real.log N ≤ (harmonic N : ℝ) := by
      simpa only [Nat.floor_natCast] using log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)
    have hup := harmonic_le_one_add_log N
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      ← one_div] at hlo hup
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith only [hup]
  have hg := ramanujanPoleProfile_gram_error_le m l N
  have hs : |(∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
      δ * Real.log N| ≤ 2 * (m : ℝ) * (l : ℝ) + 1 := by
    calc
      _ = |((∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
          δ * H) + δ * (H - Real.log N)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hg (by
        rw [abs_mul, abs_of_nonneg hδ.1]
        exact (mul_le_mul_of_nonneg_left hh hδ.1).trans (by simpa using hδ.2)))
  rw [normalizedRamanujanHorizonVector_inner]
  have he : (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) /
      Real.log N - δ =
      ((∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
        δ * Real.log N) / Real.log N := by field_simp
  rw [he, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right hs hL.le

/-- The complete scaled packet entries differ from their varying energy diagonal by `o(1)`. -/
theorem tendsto_tiltedWeil_scaled_packet_entry_error {α : ℝ}
    (hα0 : 0 < α) (hα : α < 1 / 40) (m l : ℕ+) :
    Tendsto (fun N : ℕ => logarithmicPacketOverlap α N ^ 7 *
      (⟪Matrix.toEuclideanLin
          (completeWeilMatrix tiltedUnitSpline (logarithmicPacketOverlap α N) N)
          (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then completedConductorEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) m
          else 0))) atTop (𝓝 0) := by
  let c := logarithmicPacketOverlap α
  let E (N : ℕ) := completedConductorEnergy tiltedUnitSpline (c N) m
  let r (N : ℕ) := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector m N) - E N • normalizedRamanujanHorizonVector m N
  have hres : Tendsto (fun N : ℕ => ‖c N ^ 7 • r N‖) atTop (𝓝 0) := by
    dsimp only [c, r, E]
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg _) α) 7)] using
      tendsto_tiltedWeil_scaled_residual_norm hα0 hα m.property
  have hi := tendsto_horizon_inner_zero_of_norm (fun N => c N ^ 7 • r N)
    (fun N => normalizedRamanujanHorizonVector l N) hres
    (tendsto_normalizedRamanujanHorizonVector_norm l.property)
  obtain ⟨C, hC, hE⟩ := exists_completedConductorEnergy_polynomial_bound
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos m.property
  have hlim := (tendsto_packetOverlap_pow_div_log (α := α) 9 (by linarith only [hα])).const_mul
    (C * (2 * (m : ℝ) * (l : ℝ) + 1))
  simp only [mul_zero] at hlim
  have hgram : Tendsto (fun N : ℕ => c N ^ 7 * E N *
      (⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then 1 else 0))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_logarithmicPacketOverlap_source_domain hα0,
      eventually_ge_atTop 2] with N hd hN
    have hc : 0 ≤ c N := (zero_lt_one.trans_le hd.1).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hc 7)]
    calc
      _ ≤ c N ^ 7 * (C * c N ^ 2) * ((2 * (m : ℝ) * (l : ℝ) + 1) / Real.log N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hE _ hd.1) (pow_nonneg hc 7))
          (normalizedRamanujan_gram_error_le m l hN) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h := hi.add hgram
  simp only [zero_add] at h
  apply h.congr
  intro N
  simp only [r, real_inner_smul_left, inner_sub_left, E, c]
  split_ifs <;> ring

/-- Every fixed distinct conductor family is positive for all coefficients at the same growing overlap. -/
theorem eventually_tiltedWeil_growing_packet_pos {α : ℝ}
    (hα0 : 0 < α) (hα : α < 1 / 40) {d : ℕ}
    (m : Fin d → ℕ+) (hm : Function.Injective m) :
    ∀ᶠ N : ℕ in atTop, ∀ b : Fin d → ℝ, b ≠ 0 →
      0 < completeWeilEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) N
        (∑ i, b i • normalizedRamanujanHorizonVector (m i) N) := by
  let c := logarithmicPacketOverlap α
  let κ := tiltedConductorFloorCoefficient
  let H (N : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j => c N ^ 7 *
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector (m i) N), normalizedRamanujanHorizonVector (m j) N⟫
  let D (N : ℕ) : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal fun i =>
    c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) (m i)
  let ε := κ / (2 * ((d : ℝ) + 1))
  have hκ : 0 < κ := tiltedConductorFloorCoefficient_pos
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hgap : (d : ℝ) * ε < κ := by
    dsimp only [ε]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith only [hκ, mul_nonneg (Nat.cast_nonneg d) hκ.le]
  have hclose : ∀ᶠ N : ℕ in atTop, ∀ i j, |(H N - D N) i j| ≤ ε := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have ht := tendsto_tiltedWeil_scaled_packet_entry_error hα0 hα (m i) (m j)
    filter_upwards [Metric.tendsto_nhds.mp ht ε hε] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    have he : (m i = m j) ↔ i = j := hm.eq_iff
    simpa only [H, D, Matrix.sub_apply, Matrix.diagonal_apply, he, mul_ite, mul_zero,
      mul_sub] using hN.le
  filter_upwards [hclose, eventually_logarithmicPacketOverlap_source_domain hα0] with N hN hd
  intro b hb
  have hc : 0 < c N := zero_lt_one.trans_le hd.1
  have hmass : 0 < b ⬝ᵥ b := by
    have hnon : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    exact lt_of_le_of_ne hnon (Ne.symm fun he => hb (dotProduct_self_eq_zero.mp he))
  have hfloor : κ * (b ⬝ᵥ b) ≤ b ⬝ᵥ D N *ᵥ b := by
    rw [Matrix.diagonal_mulVec, dotProduct, mul_sum]
    apply sum_le_sum
    intro i _
    have hf := tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hd.1 (m i).property
    change κ / c N ^ 7 ≤ _ at hf
    rw [div_le_iff₀ (pow_pos hc 7)] at hf
    have h := mul_le_mul_of_nonneg_right hf (sq_nonneg (b i))
    dsimp only [D, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith only [h]
  have herr := HTGeometry.abs_dotProduct_mulVec_le (H N - D N) hε.le (hN) b
  have heq : b ⬝ᵥ H N *ᵥ b = b ⬝ᵥ D N *ᵥ b + b ⬝ᵥ (H N - D N) *ᵥ b := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    ring
  have hpos : 0 < b ⬝ᵥ H N *ᵥ b := by
    have hneg := (abs_le.mp herr).1
    have hp := mul_pos (sub_pos.mpr hgap) hmass
    nlinarith only [hfloor, hneg, heq, hp]
  have hform : b ⬝ᵥ H N *ᵥ b = c N ^ 7 *
      completeWeilEnergy tiltedUnitSpline (c N) N
        (∑ i, b i • normalizedRamanujanHorizonVector (m i) N) := by
    simp only [H, completeWeilEnergy, dotProduct, Matrix.mulVec, map_sum, map_smul,
      sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [hform] at hpos
  exact (mul_pos_iff_of_pos_left (pow_pos hc 7)).mp hpos

#print axioms normalizedRamanujan_gram_error_le
#print axioms tendsto_tiltedWeil_scaled_packet_entry_error
#print axioms eventually_tiltedWeil_growing_packet_pos

end GaloisForLFunctions.CompletedArithmeticForms
