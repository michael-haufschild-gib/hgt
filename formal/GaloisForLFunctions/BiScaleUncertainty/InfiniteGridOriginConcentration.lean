import GaloisForLFunctions.BiScaleUncertainty.CorrelationOriginEnergy

/-!
# Exact energy continuity and origin concentration

For actual bounded-energy infinite-grid sources with uniformly convergent normalized
correlations, convergence of singular energies is equivalent to uniform smallness of
their origin integrals. Every convergent energy defect lies entirely at zero.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

variable {K : ℝ}

/-- Any limiting total energy determines the energy limit in each fixed origin interval. -/
theorem tendsto_correlationOriginEnergy_of_energy_limit
    (f : ℕ → InfiniteGridEnergySource K) {H : ℝ → ℝ} {L : ℝ}
    (h : ∀ x, Tendsto (fun n => (f n).correlation x) atTop (𝓝 (H x)))
    (hE : Tendsto (fun n => normalizedArchEnergy (f n).source) atTop (𝓝 L))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => correlationOriginEnergy (f n).correlation a) atTop
      (𝓝 (L - correlationTailEnergy H a)) := by
  have heq : (fun n => correlationOriginEnergy (f n).correlation a) =
      fun n => normalizedArchEnergy (f n).source -
        correlationTailEnergy (f n).correlation a := by
    funext n
    linarith [(f n).energy_split ha]
  rw [heq]
  exact hE.sub (tendsto_correlationTailEnergy_of_pointwise f h ha)

/-- Eventual origin control already controls the whole sequence after shrinking the cutoff. -/
theorem infiniteGrid_uniform_origin_iff_eventual (f : ℕ → InfiniteGridEnergySource K) :
    (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ n : ℕ, correlationOriginEnergy (f n).correlation a < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → correlationOriginEnergy (f n).correlation a < ε) := by
  constructor
  · intro h ε hε
    obtain ⟨a, ha, hb⟩ := h ε hε
    exact ⟨a, ha, 0, fun n _ => hb n⟩
  · intro h ε hε
    obtain ⟨a, ha, N, hb⟩ := h ε hε
    obtain ⟨b, hbpos, hsmall⟩ := exists_common_small_correlationOriginEnergy
      (Finset.range N) (fun n => (f n).correlation)
      (fun n _ => (f n).integrable_correlationLevyIntegrand)
      (fun n _ => (f n).abs_correlation_le_one) hε
    refine ⟨min a b, lt_min ha hbpos, ?_⟩
    intro n
    rcases lt_or_ge n N with hn | hn
    · exact (correlationOriginEnergy_mono (f n).integrable_correlationLevyIntegrand
        (f n).abs_correlation_le_one (min_le_right a b)).trans_lt
          (hsmall n (Finset.mem_range.mpr hn))
    · exact (correlationOriginEnergy_mono (f n).integrable_correlationLevyIntegrand
        (f n).abs_correlation_le_one (min_le_left a b)).trans_lt (hb n hn)

/-- Exact energy continuity criterion, with eventual origin control. -/
theorem infiniteGrid_energy_convergence_iff_eventual_origin (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) {H : ℝ → ℝ}
    (h : TendstoUniformly (fun n => (f n).correlation) H atTop) :
    Tendsto (fun n => normalizedArchEnergy (f n).source) atTop
      (𝓝 (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → correlationOriginEnergy (f n).correlation a < ε) := by
  have hiH := (infiniteGrid_uniform_limit_integrable_energy hK f h).1
  have hbH := (infiniteGrid_uniform_limit_geometry hK f h).2.2.2.1
  constructor
  · intro hE ε hε
    obtain ⟨a, ha, hsmall⟩ := exists_small_correlationOriginEnergy hiH (half_pos hε)
    have hsplit := correlation_energy_split hiH ha
    have hc := tendsto_correlationOriginEnergy_of_energy_limit f (fun x => h.tendsto_at x) hE ha
    have hlimit : (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) -
        correlationTailEnergy H a = correlationOriginEnergy H a := by linarith
    rw [hlimit] at hc
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_order.mp hc).2 ε (by linarith))
    exact ⟨a, ha, N, hN⟩
  · intro hcore
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    obtain ⟨a, ha, N, hNa⟩ := hcore (ε / 3) hε3
    obtain ⟨b, hb, hsmall⟩ := exists_small_correlationOriginEnergy hiH hε3
    let c := min a b
    have hc : 0 < c := lt_min ha hb
    have hHc : correlationOriginEnergy H c < ε / 3 :=
      (correlationOriginEnergy_mono hiH hbH (min_le_right a b)).trans_lt hsmall
    have hfc : ∀ n, N ≤ n → correlationOriginEnergy (f n).correlation c < ε / 3 := by
      intro n hn
      exact (correlationOriginEnergy_mono (f n).integrable_correlationLevyIntegrand
        (f n).abs_correlation_le_one (min_le_left a b)).trans_lt (hNa n hn)
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp
      (tendsto_correlationTailEnergy_of_pointwise f (fun x => h.tendsto_at x) hc) (ε / 3) hε3
    refine ⟨max N M, ?_⟩
    intro n hn
    have hnN : N ≤ n := (le_max_left N M).trans hn
    have hnM : M ≤ n := (le_max_right N M).trans hn
    have ht := hM n hnM
    rw [Real.dist_eq] at ht ⊢
    rw [(f n).energy_split hc, correlation_energy_split hiH hc]
    have hfn := correlationOriginEnergy_nonneg (f n).abs_correlation_le_one c
    have hHn := correlationOriginEnergy_nonneg hbH c
    have htail := abs_lt.mp ht
    apply abs_lt.mpr
    constructor <;> linarith [hfc n hnN]

/-- Energy converges exactly when every member has uniformly small origin energy. -/
theorem infiniteGrid_energy_convergence_iff_uniform_origin (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) {H : ℝ → ℝ}
    (h : TendstoUniformly (fun n => (f n).correlation) H atTop) :
    Tendsto (fun n => normalizedArchEnergy (f n).source) atTop
      (𝓝 (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ n : ℕ, correlationOriginEnergy (f n).correlation a < ε) :=
  (infiniteGrid_energy_convergence_iff_eventual_origin hK f h).trans
    (infiniteGrid_uniform_origin_iff_eventual f).symm

/-- Every positive origin interval retains the whole limiting energy defect. -/
theorem infiniteGrid_origin_energy_defect (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) {H : ℝ → ℝ} {L : ℝ}
    (h : TendstoUniformly (fun n => (f n).correlation) H atTop)
    (hE : Tendsto (fun n => normalizedArchEnergy (f n).source) atTop (𝓝 L)) :
    0 ≤ L - (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) ∧
    ∀ a : ℝ, 0 < a → Tendsto (fun n => correlationOriginEnergy (f n).correlation a)
      atTop (𝓝 (L - (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) +
        correlationOriginEnergy H a)) := by
  have hiH := (infiniteGrid_uniform_limit_integrable_energy hK f h).1
  have hc : ∀ a : ℝ, 0 < a → Tendsto
      (fun n => correlationOriginEnergy (f n).correlation a) atTop
      (𝓝 (L - (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) +
        correlationOriginEnergy H a)) := by
    intro a ha
    have heq : L - correlationTailEnergy H a =
        L - (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) +
          correlationOriginEnergy H a := by linarith [correlation_energy_split hiH ha]
    rw [← heq]
    exact tendsto_correlationOriginEnergy_of_energy_limit f (fun x => h.tendsto_at x) hE ha
  refine ⟨?_, hc⟩
  apply sub_nonneg.mpr
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, hsmall⟩ := exists_small_correlationOriginEnergy hiH hε
  have hnonneg := le_of_tendsto' ((hc a ha).neg)
    (fun n => neg_nonpos.mpr (correlationOriginEnergy_nonneg (f n).abs_correlation_le_one a))
  linarith

/-- Sending the origin cutoff to zero leaves exactly the defect and no kernel energy. -/
theorem infiniteGrid_origin_defect_iterated_limit (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) {H : ℝ → ℝ} {L : ℝ}
    (h : TendstoUniformly (fun n => (f n).correlation) H atTop)
    (hE : Tendsto (fun n => normalizedArchEnergy (f n).source) atTop (𝓝 L)) :
    ∃ D : ℝ, 0 ≤ D ∧
      D = L - (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) ∧
      (∀ a : ℝ, 0 < a → Tendsto (fun n => correlationOriginEnergy (f n).correlation a)
        atTop (𝓝 (D + correlationOriginEnergy H a))) ∧
      Tendsto (fun m : ℕ => D + correlationOriginEnergy H (1 / ((m : ℝ) + 1)))
        atTop (𝓝 D) := by
  have hd := infiniteGrid_origin_energy_defect hK f h hE
  refine ⟨L - (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x), hd.1, rfl, hd.2, ?_⟩
  simpa only [add_zero] using tendsto_const_nhds.add
    (tendsto_correlationOriginEnergy_zero (infiniteGrid_uniform_limit_integrable_energy hK f h).1)

/-- Every bounded-energy source sequence has a subsequence with a fully localized defect. -/
theorem exists_infiniteGrid_origin_defect_limit (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) :
    ∃ (φ : ℕ → ℕ) (H : ℝ → ℝ) (L D : ℝ), StrictMono φ ∧ Continuous H ∧
      TendstoUniformly (fun n => (f (φ n)).correlation) H atTop ∧
      Tendsto (fun n => normalizedArchEnergy (f (φ n)).source) atTop (𝓝 L) ∧
      L ∈ Icc 0 K ∧ 0 ≤ D ∧
      D = L - (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) ∧
      (∀ a : ℝ, 0 < a → Tendsto (fun n => correlationOriginEnergy (f (φ n)).correlation a)
        atTop (𝓝 (D + correlationOriginEnergy H a))) ∧
      (∀ a : ℝ, 0 < a → Tendsto (fun n => correlationTailEnergy (f (φ n)).correlation a)
        atTop (𝓝 (correlationTailEnergy H a))) := by
  obtain ⟨φ, H, hφ, hH, hu⟩ := exists_uniform_limit_infiniteGrid_correlations hK f
  have hb : ∀ n : ℕ, normalizedArchEnergy (f (φ n)).source ∈ Icc 0 K := by
    intro n
    refine ⟨?_, (f (φ n)).energy_le⟩
    exact div_nonneg
      (biScaleLevyEnergy_nonneg (f (φ n)).source.hasCompactSupport (f (φ n)).source.continuous)
      (f (φ n)).mass_pos.le
  obtain ⟨L, hL, ψ, hψ, he⟩ := isCompact_Icc.tendsto_subseq hb
  have hu' : TendstoUniformly (fun n => (f (φ (ψ n))).correlation) H atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact hψ.tendsto_atTop.eventually (Metric.tendstoUniformly_iff.mp hu ε hε)
  have hd := infiniteGrid_origin_energy_defect hK (fun n => f (φ (ψ n))) hu' he
  refine ⟨φ ∘ ψ, H, L, L - (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x),
    hφ.comp hψ, hH, hu', he, hL, hd.1, rfl, hd.2, ?_⟩
  intro a ha
  exact tendsto_correlationTailEnergy_of_pointwise (fun n => f (φ (ψ n)))
    (fun x => hu'.tendsto_at x) ha

end

end GaloisForLFunctions.BiScaleUncertainty
