import GaloisForLFunctions.RHTower.ChronologicalTailL1IntegrableNoGo

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Topology ENNReal
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-- A quantitative tail-`L¹` Cauchy repair has a measurable tail-supported limit, and therefore
cannot approach the critical Bose response. -/
theorem no_summably_cauchy_integrable_tail_repair :
    ¬ ∃ (θ : ℝ) (ρ : ℂ) (f : ℕ → ℝ → ℂ) (B : ℕ → ℝ≥0∞),
      0 < θ ∧ θ < 1 ∧ ρ.re = 1 / 2 ∧
      (∀ n, Measurable (f n)) ∧
      (∀ n, IntegrableOn (tailProfile θ (f n)) (Ioo (0 : ℝ) 1)) ∧
      (∑' n, B n ≠ ∞) ∧
      (∀ N n m : ℕ, N ≤ n → N ≤ m →
        eLpNorm (tailProfile θ (f n) - tailProfile θ (f m)) 1
          (volume.restrict (Ioo (0 : ℝ) 1)) < B N) ∧
      (∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        Tendsto (fun n => boseTransform (tailProfile θ (f n)) (t : ℂ)) atTop
          (𝓝 (boseTransform (criticalProfile θ ρ) (t : ℂ)))) := by
  rintro ⟨θ, ρ, f, B, hθ0, hθ1, hρ, hfm, hfi, hB, hCau, htarget⟩
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have hmem : ∀ n, MemLp (tailProfile θ (f n)) 1 μ := by
    intro n
    exact memLp_one_iff_integrable.mpr (hfi n)
  have hae : ∀ᵐ x ∂μ, ∃ l : ℂ,
      Tendsto (fun n => tailProfile θ (f n) x) atTop (𝓝 l) := by
    exact Lp.ae_tendsto_of_cauchy_eLpNorm
      (fun n => (hmem n).aestronglyMeasurable) le_rfl hB hCau
  obtain ⟨g, hgm, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae
    (fun n => (hmem n).aestronglyMeasurable) hae
  have hLp : Tendsto (fun n => eLpNorm (tailProfile θ (f n) - g) 1 μ) atTop (𝓝 0) :=
    Lp.cauchy_tendsto_of_tendsto
      (fun n => (hmem n).aestronglyMeasurable) g hB hCau hlim
  have hgmem : MemLp g 1 μ :=
    Lp.memLp_of_cauchy_tendsto le_rfl hmem g hgm.aestronglyMeasurable hLp
  have hgi : IntegrableOn g (Ioo (0 : ℝ) 1) := memLp_one_iff_integrable.mp hgmem
  have htailg : tailProfile θ g =ᵐ[μ] g := by
    filter_upwards [hlim] with x hx
    by_cases hxθ : θ ≤ x
    · simp [tailProfile, hxθ]
    · have hconst : (fun n => tailProfile θ (f n) x) = fun _ : ℕ => (0 : ℂ) := by
        funext n
        exact tailProfile_of_lt (lt_of_not_ge hxθ)
      have hzero : Tendsto (fun n => tailProfile θ (f n) x) atTop (𝓝 0) := by
        rw [hconst]
        exact tendsto_const_nhds
      have hg0 : g x = 0 := tendsto_nhds_unique hx hzero
      simp [tailProfile, hxθ, hg0]
  have htgi : IntegrableOn (tailProfile θ g) (Ioo (0 : ℝ) 1) :=
    hgi.congr htailg.symm
  have hLpTail : Tendsto (fun n =>
      eLpNorm (tailProfile θ (f n) - tailProfile θ g) 1 μ) atTop (𝓝 0) := by
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hLp
    apply eLpNorm_congr_ae
    filter_upwards [htailg] with x hx
    simp [hx]
  have hreal : Tendsto (fun n =>
      (eLpNorm (tailProfile θ (f n) - tailProfile θ g) 1 μ).toReal) atTop (𝓝 0) := by
    change Tendsto (ENNReal.toReal ∘ fun n =>
      eLpNorm (tailProfile θ (f n) - tailProfile θ g) 1 μ) atTop (𝓝 0)
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hLpTail
  have hL1 : Tendsto (fun n => ∫ x in Ioo (0 : ℝ) 1,
      ‖tailProfile θ (f n) x - tailProfile θ g x‖) atTop (𝓝 0) := by
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hreal
    have hdiff : IntegrableOn (tailProfile θ (f n) - tailProfile θ g)
        (Ioo (0 : ℝ) 1) := (hfi n).sub htgi
    symm
    change (∫ x, ‖(tailProfile θ (f n) - tailProfile θ g) x‖ ∂μ) =
      (eLpNorm (tailProfile θ (f n) - tailProfile θ g) 1 μ).toReal
    rw [integral_norm_eq_lintegral_enorm hdiff.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm]
  exact no_l1_stable_integrable_tail_repair
    ⟨θ, ρ, f, g, hθ0, hθ1, hρ, hfm, hfi, hgm.measurable, htgi, hL1, htarget⟩

end RHTower
