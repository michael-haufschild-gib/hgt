import GaloisForLFunctions.RHTower.CHMDPrimeRowBound

/-!
# Arithmetic adds no restriction to the CHMD form domain

Both endpoint marginals of the complete arithmetic edge measure are dominated
by the source mass measure. Consequently every mass-L2 source has an arithmetic
difference in L2, and full edge admission is exactly archimedean admission.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph

abbrev allPrimeMeasure : Measure (ℝ × ℝ) := Measure.sum primeMeasure

theorem summable_primeWeight (x : ℝ) : Summable (fun n : ℕ => primeWeight n x) := by
  convert (summable_prime_row_plus x).mul_left (riemannKernelReal x) using 1
  funext n
  unfold primeWeight
  ring

theorem tsum_primeWeight_le (x : ℝ) :
    (∑' n : ℕ, primeWeight n x) ≤ (2 * primeRowConstant) * massDensity x := by
  have hrow := mul_le_mul_of_nonneg_left (prime_row_plus_le x) (riemannKernelReal_pos x).le
  have hsum : (∑' n : ℕ, primeWeight n x) = riemannKernelReal x *
      ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold primeWeight
    ring
  have he : Real.exp (-x / 2) ≤ 2 * Real.cosh (x / 2) := by
    rw [Real.cosh_eq]
    have := (Real.exp_pos (x / 2)).le
    rw [neg_div]
    linarith
  rw [hsum]
  calc
    _ ≤ riemannKernelReal x * (primeRowConstant * Real.exp (-x / 2)) := hrow
    _ ≤ riemannKernelReal x * (primeRowConstant * (2 * Real.cosh (x / 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he primeRowConstant_nonneg)
        (riemannKernelReal_pos x).le
    _ = _ := by unfold massDensity; ring

theorem massDensity_neg (x : ℝ) : massDensity (-x) = massDensity x := by
  simp only [massDensity, WeilExcess.riemannKernelReal_neg, neg_div, Real.cosh_neg]

theorem map_add_right_withDensity (w : ℝ → ℝ≥0∞) (a : ℝ) :
    Measure.map (fun x : ℝ => x + a) (volume.withDensity w) =
      volume.withDensity (fun x => w (x - a)) := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    withDensity_apply _ ((measurable_id.add_const a) hs), withDensity_apply _ hs,
    ← lintegral_indicator ((measurable_id.add_const a) hs), ← lintegral_indicator hs]
  calc
    _ = ∫⁻ x : ℝ, (s.indicator (fun y => w (y - a))) (x + a) := by
      apply lintegral_congr
      intro x
      by_cases hx : x + a ∈ s <;> simp [Set.indicator, hx]
    _ = _ := lintegral_add_right_eq_self _ a

theorem map_prime_left (n : ℕ) :
    Measure.map left (primeMeasure n) =
      volume.withDensity (fun x => ENNReal.ofReal (primeWeight n x)) := by
  rw [primeMeasure, Measure.map_map measurable_snd (by fun_prop)]
  exact Measure.map_id

theorem map_prime_right (n : ℕ) :
    Measure.map right (primeMeasure n) =
      volume.withDensity (fun x => ENNReal.ofReal (primeWeight n (-x))) := by
  rw [primeMeasure, Measure.map_map (measurable_snd.add measurable_fst) (by fun_prop)]
  change Measure.map (fun x : ℝ => x + Real.log n) _ = _
  rw [map_add_right_withDensity]
  congr 1
  funext x
  congr 1
  unfold primeWeight
  rw [sub_add_cancel, WeilExcess.riemannKernelReal_neg,
    show -x + Real.log n = -(x - Real.log n) by ring,
    WeilExcess.riemannKernelReal_neg]
  ring

theorem map_allPrime_left_le :
    Measure.map left allPrimeMeasure ≤ ENNReal.ofReal (2 * primeRowConstant) • massMeasure := by
  rw [Measure.map_sum measurable_snd.aemeasurable]
  simp_rw [map_prime_left]
  rw [← withDensity_tsum (fun n => (continuous_primeWeight n).measurable.ennreal_ofReal),
    massMeasure, ← withDensity_smul _ continuous_massDensity.measurable.ennreal_ofReal]
  apply withDensity_mono
  filter_upwards [] with x
  simp only [Pi.smul_apply, smul_eq_mul, tsum_apply]
  change (∑' n : ℕ, ENNReal.ofReal (primeWeight n x)) ≤
    ENNReal.ofReal (2 * primeRowConstant) * ENNReal.ofReal (massDensity x)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => primeWeight_nonneg n x)
      (summable_primeWeight x), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (tsum_primeWeight_le x)

theorem map_allPrime_right_le :
    Measure.map right allPrimeMeasure ≤ ENNReal.ofReal (2 * primeRowConstant) • massMeasure := by
  rw [Measure.map_sum (measurable_snd.add measurable_fst).aemeasurable]
  simp_rw [map_prime_right]
  rw [← withDensity_tsum (fun n =>
    ((continuous_primeWeight n).comp continuous_neg).measurable.ennreal_ofReal),
    massMeasure, ← withDensity_smul _ continuous_massDensity.measurable.ennreal_ofReal]
  apply withDensity_mono
  filter_upwards [] with x
  simp only [Pi.smul_apply, smul_eq_mul, tsum_apply]
  change (∑' n : ℕ, ENNReal.ofReal (primeWeight n (-x))) ≤
    ENNReal.ofReal (2 * primeRowConstant) * ENNReal.ofReal (massDensity x)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => primeWeight_nonneg n (-x))
      (summable_primeWeight (-x)), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [massDensity_neg] using tsum_primeWeight_le (-x)

theorem nonsingular_allPrime_left :
    Measure.QuasiMeasurePreserving left allPrimeMeasure massMeasure :=
  ⟨measurable_snd, Measure.absolutelyContinuous_of_le_smul map_allPrime_left_le⟩

theorem nonsingular_allPrime_right :
    Measure.QuasiMeasurePreserving right allPrimeMeasure massMeasure :=
  ⟨measurable_snd.add measurable_fst, Measure.absolutelyContinuous_of_le_smul map_allPrime_right_le⟩

theorem memLp_allPrime_left {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) :
    MemLp (v ∘ left) 2 allPrimeMeasure := by
  have h := hv.of_measure_le_smul (by simp) map_allPrime_left_le
  exact (memLp_map_measure_iff h.aestronglyMeasurable measurable_snd.aemeasurable).mp h

theorem memLp_allPrime_right {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) :
    MemLp (v ∘ right) 2 allPrimeMeasure := by
  have h := hv.of_measure_le_smul (by simp) map_allPrime_right_le
  exact (memLp_map_measure_iff h.aestronglyMeasurable
    (measurable_snd.add measurable_fst).aemeasurable).mp h

/-- Every source in mass L2 admits the entire arithmetic difference. -/
theorem memLp_allPrime_difference {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) :
    MemLp (difference v) 2 allPrimeMeasure :=
  (memLp_allPrime_left hv).sub (memLp_allPrime_right hv)

/-- There is no additional arithmetic condition on the full form domain. -/
theorem memLp_full_difference_iff_arch {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) :
    MemLp (difference v) 2 edgeMeasure ↔ MemLp (difference v) 2 archMeasure := by
  constructor
  · exact MemLp.left_of_add_measure
  · intro ha
    have hm : AEStronglyMeasurable (difference v) edgeMeasure :=
      (hv.aestronglyMeasurable.comp_quasiMeasurePreserving nonsingular_left).sub
        (hv.aestronglyMeasurable.comp_quasiMeasurePreserving nonsingular_right)
    exact (memLp_two_iff_integrable_sq hm).mpr
      (ha.integrable_sq.add_measure (memLp_allPrime_difference hv).integrable_sq)

end RHTower.CHMDDoobGraph
