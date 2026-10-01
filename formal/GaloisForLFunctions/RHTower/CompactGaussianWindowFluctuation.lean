import GaloisForLFunctions.RHTower.SteinhausCompactAffineFluctuation
import GaloisForLFunctions.RHTower.CompactGaussianNormalizedChannelEnergy
import GaloisForLFunctions.RHTower.SteinhausOriginalFiniteLocalTarget

open MeasureTheory Filter Topology Finset Complex Metric
open scoped ENNReal
noncomputable section
namespace RHTower
open SteinhausModel

/-- Literal normalized free-window columns have simultaneous compact centered
fluctuation events in the original infinite product law, with the exact bias cost
and no dependence on the number of selected prime coordinates. -/
theorem eventually_compactGaussianWindow_original_fluctuation
    (c : ℂ) {r ρ ε : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 ≤ c.re - ρ) (hε : 0 < ε) {D : ℕ} (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ, ∀ ω : Omega,
      ∀ {n : ℕ} (p : Fin n → ℕ), Function.Injective p →
      (∀ i, p i ∈ largePrimes N (N / D)) →
      ∀ m : Fin n → ℂ, (∀ i, ‖m i‖ ≤ 1 / 2) →
      ∃ E : Set Omega, MeasurableSet E ∧
        (1 / 4 : ℝ) * Real.exp (-(2 * ∑ i, ‖m i‖ ^ 2)) ≤ steinhausMeasure.real E ∧
        ∀ ξ ∈ E, ∀ s ∈ closedBall c r,
          ‖∑ i, (charFactor 1 (ξ (p i)) - m i) *
            compactGaussianNormalizedPrimeChannel s N (p i) tau (L / p i) ω‖ < ε := by
  classical
  obtain ⟨δ, hδ, hcompact⟩ := exists_steinhausCompactAffineFluctuation_threshold c hρ hrρ hε
  obtain ⟨C, _, henergy⟩ := exists_compactGaussianNormalizedWindow_energy_upper (c.re + ρ) hD
  have hlim : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [henergy, hlim.eventually (Iio_mem_nhds hδ), eventually_ge_atTop 1]
    with N henergyN hsmall hN1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  intro tau L ω n p hinj hp m hm
  let a : Fin n → ℂ → ℂ := fun i s => compactGaussianNormalizedPrimeChannel s N (p i) tau (L / p i) ω
  have ha (i : Fin n) : Differentiable ℂ (a i) :=
    differentiable_compactGaussianNormalizedPrimeChannel hNR
      (by exact_mod_cast (mem_largePrimes.mp (hp i)).1.2.pos) tau (L / p i) ω
  have hsum (s : ℂ) : (∑ i, ‖a i s‖ ^ 2) ≤
      ∑ q ∈ largePrimes N (N / D),
        ‖compactGaussianNormalizedPrimeChannel s N q tau (L / q) ω‖ ^ 2 := by
    have heq : (∑ i, ‖a i s‖ ^ 2) =
        ∑ q ∈ univ.image p, ‖compactGaussianNormalizedPrimeChannel s N q tau (L / q) ω‖ ^ 2 := by
      exact (sum_image (f := fun q : ℕ => ‖compactGaussianNormalizedPrimeChannel s N q tau (L / q) ω‖ ^ 2)
        (s := univ) (g := p) hinj.injOn).symm
    rw [heq]
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨i, _, rfl⟩ := mem_image.mp hq
      exact hp i
    · intro q _ _
      exact sq_nonneg _
  have hbound (s : ℂ) (hs : s ∈ ball c ρ) : (∑ i, ‖a i s‖ ^ 2) ≤ δ := by
    have habs : |s.re - c.re| ≤ dist s c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
    have hd : dist s c < ρ := hs
    have hl := (abs_le.mp habs).1
    have hu := (abs_le.mp habs).2
    exact (hsum s).trans ((henergyN tau L ω s (by linarith) (by linarith)).trans hsmall.le)
  obtain ⟨E, hEm, _, hprob, hfluct⟩ := hcompact m hm a ha hbound
  let f : Omega → (Fin n → ℝ) := fun ξ i => ξ (p i)
  have hfm : Measurable f := measurable_pi_lambda _ (fun i => measurable_pi_apply (p i))
  have hmap := map_steinhausMeasure_finiteCoordinates p hinj
  have heq : steinhausMeasure.real (f ⁻¹' E) = (steinhausFinitePhaseMeasure n).real E := by
    unfold Measure.real
    rw [← hmap, Measure.map_apply hfm hEm]
  refine ⟨f ⁻¹' E, hEm.preimage hfm, heq.symm ▸ hprob, ?_⟩
  intro ξ hξ s hs
  simpa only [steinhausFiniteCenteredSum, steinhausFiniteCenteredPhase, smul_eq_mul, a, f] using
    hfluct (f ξ) hξ s hs

end RHTower
