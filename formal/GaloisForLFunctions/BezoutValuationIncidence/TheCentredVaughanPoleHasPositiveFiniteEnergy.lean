import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketsHaveAnExactResidualEnergyDensity

/-!
Centering the Vaughan pole leaves the active correction, whose first cell has
explicit positive energy. Its total energy is finite and positive, independently
of moving cutoffs, and obstructs faster normalized power decay.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The first active-pair increment is a strictly positive prime contribution. -/
theorem addDiff_pmActiveSawtoothComponent_one (ε : ℝ) :
    addDiff (pmActiveSawtoothComponent ε) 1 = (2 : ℝ) ^ (-ε) / 4 := by
  have htwo : pmActiveSawtoothComponent ε 2 = (2 : ℝ) ^ (-ε) / 4 := by
    rw [pmActiveSawtoothComponent,
      pmPowerDampedDivisorCoeff_prime ε Nat.prime_two,
      pmPowerDampedDivisorCoeff_prime (1 + ε) Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
    rw [show -(1 + ε) = -ε + (-1 : ℝ) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_neg_one]
    ring
  rw [addDiff, pmActiveSawtoothComponent_one, show (1 : ℕ) + 1 = 2 from rfl, htwo, sub_zero]

/-- A fixed positive first cell remains in the centered pole energy. -/
theorem pmActivePairPronicEnergy_one (ε : ℝ) :
    pmActivePairPronicEnergy ε 1 = ((2 : ℝ) ^ (-ε)) ^ 2 / 32 := by
  rw [pmActivePairPronicEnergy, Icc_self, sum_singleton, addDiff_pmActiveSawtoothComponent_one]
  norm_num only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Every nonempty horizon retains the explicit positive pole cell. -/
theorem pmActivePairPronicEnergy_lower (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    ((2 : ℝ) ^ (-ε)) ^ 2 / 32 ≤ pmActivePairPronicEnergy ε T := by
  rw [← pmActivePairPronicEnergy_one]
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hT) (fun n _ _ => by positivity)

/-- Centering the pole leaves exactly the bounded active-pair energy, independently of cutoffs. -/
theorem pmPronicVaughanCentredGram_pole_eq_active (ε : ℝ) (U V T : ℕ) :
    pmPronicVaughanCentredGram ε U V T 4 4 = pmActivePairPronicEnergy ε T := by
  have heq (n : ℕ) : pmPronicVaughanCentredPiece ε U V n 4 =
      -addDiff (pmActiveSawtoothComponent ε) n := by
    change -(pmPowerDampedDivisorDensity ε).re * n - addDiff (pmActiveSawtoothComponent ε) n -
      (-(pmPowerDampedDivisorDensity ε).re) * n = _
    ring
  simp only [pmPronicVaughanCentredGram, heq, pmActivePairPronicEnergy, neg_mul_neg, pow_two]

private theorem active_energy_eq_sum_range (ε : ℝ) (T : ℕ) :
    pmActivePairPronicEnergy ε T =
      ∑ n ∈ range (T + 1), addDiff (pmActiveSawtoothComponent ε) n ^ 2 / (pronicSeq n : ℝ) := by
  have hset : range (T + 1) = insert 0 (Icc 1 T) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp)]
  simp only [pmActivePairPronicEnergy, pronicSeq, Nat.cast_mul, Nat.cast_add,
    Nat.cast_zero, Nat.cast_one, zero_mul, div_zero, zero_add]

/-- The centered pole has a strictly positive finite total energy. -/
theorem exists_tendsto_pmActivePairPronicEnergy {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ L : ℝ, ((2 : ℝ) ^ (-ε)) ^ 2 / 32 ≤ L ∧ L ≤ 1 / 4 ∧
      Tendsto (pmActivePairPronicEnergy ε) atTop (𝓝 L) := by
  let f : ℕ → ℝ := fun n => addDiff (pmActiveSawtoothComponent ε) n ^ 2 / (pronicSeq n : ℝ)
  have hf : Summable f := by
    apply summable_of_sum_range_le (c := (1 / 4 : ℝ)) (fun n => by dsimp only [f]; positivity)
    intro N
    rcases N with _ | N
    · simp
    · change (∑ n ∈ range (N + 1), addDiff (pmActiveSawtoothComponent ε) n ^ 2 /
        (pronicSeq n : ℝ)) ≤ _
      rw [← active_energy_eq_sum_range]
      exact (pmActivePairPronicEnergy_bounds hε N).2
  have hsucc : Tendsto (fun T : ℕ => T + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with T hT
    omega
  have hlim : Tendsto (pmActivePairPronicEnergy ε) atTop (𝓝 (∑' n, f n)) := by
    simpa only [Function.comp_def, f, ← active_energy_eq_sum_range] using
      hf.hasSum.tendsto_sum_nat.comp hsucc
  refine ⟨∑' n, f n, ?_, le_of_tendsto' hlim (fun T => (pmActivePairPronicEnergy_bounds hε T).2), hlim⟩
  have hfirst : pmActivePairPronicEnergy ε 1 ≤ ∑' n, f n := by
    rw [active_energy_eq_sum_range]
    exact hf.sum_le_tsum _ (fun n _ => by dsimp only [f]; positivity)
  simpa only [pmActivePairPronicEnergy_one] using hfirst

/-- Arbitrary moving cutoffs retain the same nonzero finite pole limit. -/
theorem exists_positive_tendsto_pmPronicVaughanCentredGram_pole {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ L : ℝ, 0 < L ∧ L ≤ 1 / 4 ∧ ∀ U V : ℕ → ℕ,
      Tendsto (fun T => pmPronicVaughanCentredGram ε (U T) (V T) T 4 4) atTop (𝓝 L) := by
  obtain ⟨L, hlo, hhi, hlim⟩ := exists_tendsto_pmActivePairPronicEnergy hε
  refine ⟨L, (by positivity : 0 < ((2 : ℝ) ^ (-ε)) ^ 2 / 32).trans_le hlo, hhi, fun U V => ?_⟩
  simpa only [pmPronicVaughanCentredGram_pole_eq_active] using hlim

/-- A normalized residual matrix cannot decay faster than its positive finite pole cell. -/
theorem not_pmPronicVaughanCentredGram_pole_faster_power {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 1 - 2 * ε < δ) (U V : ℕ → ℕ) :
    ¬ ∃ C : ℝ, ∀ᶠ T : ℕ in atTop,
      pmPronicVaughanCentredGram ε (U T) (V T) T 4 4 / (T : ℝ) ^ (1 - 2 * ε) ≤
        C / (T : ℝ) ^ δ := by
  rintro ⟨C, hC⟩
  have hpow : Tendsto (fun T : ℕ => (T : ℝ) ^ (δ - (1 - 2 * ε))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith only [hδ])).comp tendsto_natCast_atTop_atTop
  have hupper : ∀ᶠ T : ℕ in atTop, pmActivePairPronicEnergy ε T ≤
      C / (T : ℝ) ^ (δ - (1 - 2 * ε)) := by
    filter_upwards [hC, eventually_ge_atTop 1] with T hCT hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have h := hCT
    rw [pmPronicVaughanCentredGram_pole_eq_active,
      div_le_iff₀ (Real.rpow_pos_of_pos hT0 (1 - 2 * ε))] at h
    refine h.trans_eq ?_
    rw [Real.rpow_sub hT0]
    field_simp [Real.rpow_ne_zero hT0.ne' (1 - 2 * ε),
      Real.rpow_ne_zero hT0.ne' δ]
  have hzero : Tendsto (pmActivePairPronicEnergy ε) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun T => (pmActivePairPronicEnergy_bounds hε T).1)
      hupper (tendsto_const_nhds.div_atTop hpow)
  obtain ⟨L, hlo, _, hlim⟩ := exists_tendsto_pmActivePairPronicEnergy hε
  have hz : L = 0 := tendsto_nhds_unique hlim hzero
  rw [hz] at hlo
  exact (not_le_of_gt (by positivity : 0 < ((2 : ℝ) ^ (-ε)) ^ 2 / 32)) hlo

#print axioms addDiff_pmActiveSawtoothComponent_one
#print axioms pmActivePairPronicEnergy_one
#print axioms pmActivePairPronicEnergy_lower
#print axioms pmPronicVaughanCentredGram_pole_eq_active
#print axioms exists_tendsto_pmActivePairPronicEnergy
#print axioms exists_positive_tendsto_pmPronicVaughanCentredGram_pole
#print axioms not_pmPronicVaughanCentredGram_pole_faster_power
end GaloisForLFunctions.BezoutValuationIncidence
