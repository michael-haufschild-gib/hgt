import GaloisForLFunctions.RHTower.SteinhausFullGaussianEndpointEnvelope
import GaloisForLFunctions.RHTower.SteinhausFullGaussianHolomorphy
import GaloisForLFunctions.HTGeometry.VitaliConvergence

open Complex Set Metric Filter Topology
noncomputable section
namespace RHTower

/-- The actual coherent Gaussian cofactor mean converges uniformly on every smaller
closed disc in the open unit strip, along the full real scale filter. -/
theorem tendstoUniformlyOn_finitePrimeTwistExtension_gaussian_mean
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (t : ℝ)
    {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1) :
    TendstoUniformlyOn (fun R : ℝ => fun s : ℂ =>
      steinhausFullGaussianCofactor s R (finitePrimeTwistExtension S ω t) *
        (R : ℂ) ^ (-(s + (t : ℂ) * I)))
      (fun s => finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi)) *
        (Complex.exp ((s + (t : ℂ) * I) ^ 2) / (s + (t : ℂ) * I)))
      atTop (closedBall c r) := by
  let η := finitePrimeTwistExtension S ω t
  let A := finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi))
  let F : ℝ → ℂ → ℂ := fun R s =>
    steinhausFullGaussianCofactor s R η * (R : ℂ) ^ (-(s + (t : ℂ) * I))
  let T : ℂ → ℂ := fun s => A *
    (Complex.exp ((s + (t : ℂ) * I) ^ 2) / (s + (t : ℂ) * I))
  change TendstoUniformlyOn F T atTop (closedBall c r)
  have hstrip (s : ℂ) (hs : s ∈ ball c ρ) : c.re - ρ ≤ s.re ∧ s.re ≤ c.re + ρ := by
    have habs : |s.re - c.re| ≤ dist s c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
    have hd : dist s c < ρ := hs
    have hl := (abs_le.mp habs).1
    have hu := (abs_le.mp habs).2
    constructor <;> linarith
  obtain ⟨C, _hC, hC⟩ := exists_normalizedFullGaussianCofactor_band_bound hc0
    (show c.re - ρ ≤ c.re + ρ by linarith) hc1
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp hC
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro Rn hRn
  let q : ℕ → ℝ := fun n => max (Rn n) R0
  have hq (n : ℕ) := hR0 (q n) (le_max_right _ _)
  have heq : ∀ᶠ n : ℕ in atTop, q n = Rn n := by
    filter_upwards [hRn.eventually (eventually_ge_atTop R0)] with n hn
    exact max_eq_left hn
  have hqtop : Tendsto q atTop atTop := hRn.congr' (heq.mono fun _ hn => hn.symm)
  have hF (n : ℕ) : DifferentiableOn ℂ (F (q n)) (ball c ρ) :=
    (differentiable_normalizedFullGaussianCofactor (hq n).1 η t).differentiableOn
  have hloc : ∀ z ∈ ball c ρ, ∃ δ : ℝ, 0 < δ ∧ ball z δ ⊆ ball c ρ ∧
      ∃ B : ℝ, ∀ n, ∀ w ∈ ball z δ, ‖F (q n) w‖ ≤ B := by
    intro z hz
    obtain ⟨δ, hδ, hsub⟩ := Metric.exists_ball_subset_ball hz
    refine ⟨δ, hδ, hsub, C, fun n w hw => ?_⟩
    exact (hq n).2 w (hstrip w (hsub hw)).1 (hstrip w (hsub hw)).2 η t
  have hden : ∀ s ∈ ball c ρ, s + (t : ℂ) * I ≠ 0 := by
    intro s hs heq0
    have hpos : 0 < s.re := hc0.trans_le (hstrip s hs).1
    have hre := congrArg Complex.re heq0
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    exact hpos.ne' hre
  have hT : DifferentiableOn ℂ T (ball c ρ) :=
    (((differentiable_id.add_const ((t : ℂ) * I)).pow 2).cexp.differentiableOn.div
      (differentiable_id.add_const ((t : ℂ) * I)).differentiableOn hden).const_mul A
  have hnear : ∀ᶠ z in 𝓝[≠] c, z ∈ ball c ρ :=
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have hacc : ∃ᶠ z in 𝓝[≠] c, z ∈ ball c ρ := hnear.frequently
  have hpoint (s : ℂ) (hs : s ∈ ball c ρ) :
      Tendsto (fun n : ℕ => F (q n) s) atTop (𝓝 (T s)) := by
    have h := tendsto_finitePrimeTwistExtension_gaussian_mean S ω t
      (s := s) (hc0.trans_le (hstrip s hs).1) ((hstrip s hs).2.trans_lt hc1)
    exact h.comp hqtop
  have hv := GaloisForLFunctions.HTGeometry.tendstoLocallyUniformlyOn_of_pointwise_on_uniquenessSet
    isOpen_ball (convex_ball c ρ).isPreconnected hF hloc hT (Subset.refl _)
    (mem_ball_self hρ) hacc hpoint
  have hsub : closedBall c r ⊆ ball c ρ :=
    fun s hs => (mem_closedBall.mp hs).trans_lt hrρ
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hv
    (closedBall c r) hsub (isCompact_closedBall c r)
  apply hu.congr
  filter_upwards [heq] with n hn s _
  rw [hn]

end RHTower
