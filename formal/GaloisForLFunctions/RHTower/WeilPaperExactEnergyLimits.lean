import GaloisForLFunctions.RHTower.WeilPaperNativeEnergyTopology

/-!
# Exact full-energy losses in weak limits

Any nonnegative prescribed energy increment can be maintained along a sequence
of native laws converging to a fixed native law. Thus the closure of the graph
of intrinsic native energy contains the entire vertical ray above each point.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Arbitrary weights tending to zero suppress any moving second spectral law. -/
theorem tendsto_spectralProbability_admixture_of_weight_tendsto_zero
    (a : NormalizedMixture) (b : ℕ → NormalizedMixture)
    (t : ℕ → Set.Icc (0 : ℝ) 1) (ht : Tendsto (fun n => (t n).1) atTop (𝓝 0)) :
    Tendsto (fun n => spectralProbability (paperNormalizedSegment a (b n) (t n)))
      atTop (𝓝 (spectralProbability a)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    norm_spectralExpectation_segment_sub_le F a (b n) (t n)) ?_
  simpa using (tendsto_const_nhds.mul ht).mul_const ‖F‖

/-- Exact origin constraints survive arbitrary vanishing admixture weights. -/
theorem tendsto_spectralRepresentingMeasure_admixture_of_weight_tendsto_zero
    (a : ComplexNullMixture) (b : ℕ → ComplexNullMixture)
    (t : ℕ → Set.Icc (0 : ℝ) 1) (ht : Tendsto (fun n => (t n).1) atTop (𝓝 0)) :
    Tendsto (fun n => spectralRepresentingMeasure (paperComplexNullSegment a (b n) (t n)))
      atTop (𝓝 (spectralRepresentingMeasure a)) := by
  apply tendsto_subtype_rng.mpr
  exact ((ProbabilityMeasure.continuous_map continuous_primeSpectralPoint).tendsto
    (spectralProbability a.1)).comp
      (tendsto_spectralProbability_admixture_of_weight_tendsto_zero a.1
        (fun n => (b n).1) t ht)

/-- Every nonnegative energy increment is lost exactly along some weakly convergent
sequence of actual normalized complex-null laws. -/
theorem exists_spectralRepresentingMeasure_tendsto_exact_energy
    (a : ComplexNullMixture) (δ : ℝ≥0) :
    ∃ c : ℕ → ComplexNullMixture,
      Tendsto (fun n => spectralRepresentingMeasure (c n)) atTop
        (𝓝 (spectralRepresentingMeasure a)) ∧
      ∀ n, energy (c n).1.1 = energy a.1.1 + δ := by
  classical
  let A := energy a.1.1
  choose b hb using fun n : ℕ => exists_complexNullMixture_energy_gt
    (A + ((n : ℝ)+1)*δ + 1)
  have hD (n : ℕ) : 0 < energy (b n).1.1 - A := by
    have := hb n
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hd := δ.coe_nonneg
    nlinarith
  have hδ (n : ℕ) : (δ : ℝ) ≤ energy (b n).1.1 - A := by
    have := hb n
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hd := δ.coe_nonneg
    nlinarith
  let t (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
    ⟨(δ : ℝ)/(energy (b n).1.1-A), div_nonneg δ.coe_nonneg (hD n).le,
      (div_le_one (hD n)).mpr (hδ n)⟩
  have htbound (n : ℕ) : (t n).1 ≤ 1/((n : ℝ)+1) := by
    apply (div_le_div_iff₀ (hD n) (by positivity)).mpr
    have := hb n
    nlinarith
  have ht : Tendsto (fun n => (t n).1) atTop (𝓝 0) :=
    squeeze_zero (fun n => (t n).2.1) htbound tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun n => paperComplexNullSegment a (b n) (t n),
    tendsto_spectralRepresentingMeasure_admixture_of_weight_tendsto_zero a b t ht, ?_⟩
  intro n
  change energy (paperNormalizedSegment a.1 (b n).1 (t n)).1 = _
  rw [paperNormalizedSegment_observe]
  simp only [smul_eq_mul]
  have he : (t n).1 * (energy (b n).1.1 - A) = δ :=
    div_mul_cancel₀ _ (hD n).ne'
  dsimp only [A] at he
  nlinarith only [he]

/-- The closure of the energy graph contains the vertical ray above each native law. -/
theorem native_full_energy_vertical_ray_mem_closure
    (μ : Set.range spectralRepresentingMeasure) (δ : ℝ≥0) :
    (μ, paperNativeSpectralEnergy μ + δ) ∈
      closure {p : Set.range spectralRepresentingMeasure × ℝ |
        paperNativeSpectralEnergy p.1 = p.2} := by
  rcases μ with ⟨μ, a, rfl⟩
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_exact_energy a δ
  let c' (n : ℕ) : Set.range spectralRepresentingMeasure :=
    ⟨spectralRepresentingMeasure (c n), Set.mem_range_self (c n)⟩
  have hc' : Tendsto c' atTop
      (𝓝 ⟨spectralRepresentingMeasure a, Set.mem_range_self a⟩) :=
    tendsto_subtype_rng.mpr hc
  rw [paperNativeSpectralEnergy_apply]
  apply mem_closure_of_tendsto (hc'.prodMk_nhds
    (tendsto_const_nhds (x := energy a.1.1 + (δ : ℝ))))
  exact Filter.Eventually.of_forall fun n => by
    change paperNativeSpectralEnergy (c' n) = _
    simpa only [c', paperNativeSpectralEnergy_apply] using he n

/-- Intrinsic native energy has a nonclosed graph in the weak law topology. -/
theorem not_isClosed_native_full_energy_graph :
    ¬ IsClosed {p : Set.range spectralRepresentingMeasure × ℝ |
      paperNativeSpectralEnergy p.1 = p.2} := by
  intro h
  obtain ⟨a, _⟩ := exists_complexNullMixture_energy_gt 0
  have hm := native_full_energy_vertical_ray_mem_closure
    ⟨spectralRepresentingMeasure a, Set.mem_range_self a⟩ 1
  rw [h.closure_eq] at hm
  change paperNativeSpectralEnergy _ = paperNativeSpectralEnergy _ + (1 : ℝ) at hm
  linarith

end RHTower.WeilWorkPBAP
