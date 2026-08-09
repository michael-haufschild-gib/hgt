import Mathlib

/-!
# The activation/divisor corner is an exceptional blow-up

The infinite-depth activation face is `Z_∞(h, s) = ζ(s)/ζ(s + h)`.  At a zeta zero the two
boundary faces disagree: `Z_∞(0, s) = 1` off the zero, while `Z_∞(h, ρ) = 0`.  No ordinary
continuous value reconciles them, but every projective normal direction does: along the chart
`h = λ (s - ρ)` the face converges to `(1 + λ)^{-d}`, where `d` is the order of the zero.  The
missing point is therefore an exceptional fibre, not a removable singularity.

The local factorization of zeta at a point other than its pole is obtained from analyticity plus
the identity theorem on the connected set `ℂ \ {1}`.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The infinite-depth activation face `Z_∞(h, s) = ζ(s) / ζ(s + h)`. -/
def woldActivationInfiniteDepth (h s : ℂ) : ℂ := riemannZeta s / riemannZeta (s + h)

/-- **Equation (22), zero-activation face.**  Off the zeta divisor the zero-activation value is
one. -/
theorem woldActivationInfiniteDepth_zero_activation {s : ℂ} (hs : riemannZeta s ≠ 0) :
    woldActivationInfiniteDepth 0 s = 1 := by
  rw [woldActivationInfiniteDepth, add_zero, div_self hs]

/-- **Equation (22), divisor face.**  On the zeta divisor every positive activation value is
zero. -/
theorem woldActivationInfiniteDepth_on_divisor {ρ h : ℂ} (hρ : riemannZeta ρ = 0) :
    woldActivationInfiniteDepth h ρ = 0 := by
  rw [woldActivationInfiniteDepth, hρ, zero_div]

/-! ### Local factorization of zeta away from its pole -/

theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hopen : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hdiff.analyticOnNhd hopen s hs

theorem not_eventually_riemannZeta_eq_zero {ρ : ℂ} (hρ : ρ ≠ 1) :
    ¬ ∀ᶠ s in 𝓝 ρ, riemannZeta s = 0 := by
  intro hcon
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank hrank (1 : ℂ)).isPreconnected
  have hAn : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun z hz => analyticAt_riemannZeta hz
  have hzero : Set.EqOn riemannZeta 0 ({(1 : ℂ)}ᶜ) :=
    hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hρ hcon
  have h2mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have h2 : riemannZeta 2 ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    norm_num
  exact h2 (hzero h2mem)

/-- **Equation (20).**  Away from its pole, zeta factors as a power of `(s - ρ)` times a
nonvanishing analytic germ. -/
theorem exists_riemannZeta_local_factorization {ρ : ℂ} (hρ : ρ ≠ 1) :
    ∃ (d : ℕ) (u : ℂ → ℂ), AnalyticAt ℂ u ρ ∧ u ρ ≠ 0 ∧
      ∀ᶠ s in 𝓝 ρ, riemannZeta s = (s - ρ) ^ d * u s := by
  obtain ⟨d, u, hu, hu0, hfg⟩ :=
    (analyticAt_riemannZeta hρ).exists_eventuallyEq_pow_smul_nonzero_iff.mpr
      (not_eventually_riemannZeta_eq_zero hρ)
  exact ⟨d, u, hu, hu0, hfg.mono fun s hs => by simpa [smul_eq_mul] using hs⟩

/-! ### The exceptional blow-up chart -/

/-- **Equation (23), abstract form.**  Along the projective normal direction `h = λ (s - ρ)` the
ratio of the two local factorizations converges to `(1 + λ)^{-d}`. -/
theorem tendsto_blowupChart {u : ℂ → ℂ} {ρ : ℂ} (hu : ContinuousAt u ρ) (hu0 : u ρ ≠ 0)
    (d : ℕ) (lam : ℂ) :
    Tendsto (fun s : ℂ =>
        ((s - ρ) / (s + lam * (s - ρ) - ρ)) ^ d * (u s / u (s + lam * (s - ρ))))
      (𝓝[≠] ρ) (𝓝 (((1 + lam) ^ d)⁻¹)) := by
  have hc : Continuous fun s : ℂ => s + lam * (s - ρ) := by fun_prop
  have hshift : Tendsto (fun s : ℂ => s + lam * (s - ρ)) (𝓝 ρ) (𝓝 ρ) := by
    have h : Tendsto (fun s : ℂ => s + lam * (s - ρ)) (𝓝 ρ) (𝓝 (ρ + lam * (ρ - ρ))) :=
      hc.tendsto ρ
    rwa [show (ρ : ℂ) + lam * (ρ - ρ) = ρ from by ring] at h
  have huT : Tendsto u (𝓝 ρ) (𝓝 (u ρ)) := hu
  have hu2 : Tendsto (fun s : ℂ => u (s + lam * (s - ρ))) (𝓝[≠] ρ) (𝓝 (u ρ)) :=
    huT.comp (hshift.mono_left nhdsWithin_le_nhds)
  have hu1 : Tendsto (fun s : ℂ => u s) (𝓝[≠] ρ) (𝓝 (u ρ)) :=
    huT.mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun s : ℂ => u s / u (s + lam * (s - ρ))) (𝓝[≠] ρ) (𝓝 1) := by
    have := hu1.div hu2 hu0
    rwa [div_self hu0] at this
  have hconst : ∀ᶠ s in 𝓝[≠] ρ,
      ((s - ρ) / (s + lam * (s - ρ) - ρ)) ^ d * (u s / u (s + lam * (s - ρ)))
        = ((1 + lam) ^ d)⁻¹ * (u s / u (s + lam * (s - ρ))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsne : s - ρ ≠ 0 := sub_ne_zero.mpr hs
    have hden : s + lam * (s - ρ) - ρ = (1 + lam) * (s - ρ) := by ring
    rw [hden, div_mul_eq_div_div_swap, div_self hsne, one_div, inv_pow]
  refine Tendsto.congr' (hconst.mono fun s hs => hs.symm) ?_
  have := hratio.const_mul (((1 + lam) ^ d)⁻¹)
  rwa [mul_one] at this

/-- **Equation (21).**  On a punctured neighbourhood of `ρ` the infinite-depth face along the
chart `h = λ (s - ρ)` is the ratio of the two local factorizations. -/
theorem eventuallyEq_woldActivationInfiniteDepth_blowupChart {ρ : ℂ} {u : ℂ → ℂ} {d : ℕ}
    (hfac : ∀ᶠ s in 𝓝 ρ, riemannZeta s = (s - ρ) ^ d * u s) (lam : ℂ) :
    ∀ᶠ s in 𝓝 ρ, woldActivationInfiniteDepth (lam * (s - ρ)) s
      = ((s - ρ) / (s + lam * (s - ρ) - ρ)) ^ d * (u s / u (s + lam * (s - ρ))) := by
  have hc : Continuous fun s : ℂ => s + lam * (s - ρ) := by fun_prop
  have hshift : Tendsto (fun s : ℂ => s + lam * (s - ρ)) (𝓝 ρ) (𝓝 ρ) := by
    have h : Tendsto (fun s : ℂ => s + lam * (s - ρ)) (𝓝 ρ) (𝓝 (ρ + lam * (ρ - ρ))) :=
      hc.tendsto ρ
    rwa [show (ρ : ℂ) + lam * (ρ - ρ) = ρ from by ring] at h
  have hfac2 : ∀ᶠ s in 𝓝 ρ, riemannZeta (s + lam * (s - ρ))
      = (s + lam * (s - ρ) - ρ) ^ d * u (s + lam * (s - ρ)) :=
    hshift.eventually hfac
  filter_upwards [hfac, hfac2] with s hs hs2
  rw [woldActivationInfiniteDepth, hs, hs2, div_pow, mul_comm ((s - ρ) ^ d) (u s),
    mul_comm ((s + lam * (s - ρ) - ρ) ^ d) (u (s + lam * (s - ρ))), mul_div_mul_comm,
    mul_comm (u s / u (s + lam * (s - ρ)))]

/-- **The activation/divisor corner is an exceptional blow-up.**  At every point other than the
pole, the infinite-depth activation face has a finite limit along each projective normal
direction, and that limit is `(1 + λ)^{-d}` for the local zero order `d`. -/
theorem exists_tendsto_woldActivationInfiniteDepth_blowupChart {ρ : ℂ} (hρ : ρ ≠ 1) :
    ∃ d : ℕ, ∀ lam : ℂ, 1 + lam ≠ 0 →
      (1 + lam) ^ d ≠ 0 ∧
      Tendsto (fun s : ℂ => woldActivationInfiniteDepth (lam * (s - ρ)) s) (𝓝[≠] ρ)
        (𝓝 (((1 + lam) ^ d)⁻¹)) := by
  obtain ⟨d, u, hu, hu0, hfac⟩ := exists_riemannZeta_local_factorization hρ
  refine ⟨d, fun lam hlam => ⟨pow_ne_zero d hlam, ?_⟩⟩
  refine Tendsto.congr' ?_ (tendsto_blowupChart hu.continuousAt hu0 d lam)
  exact ((eventuallyEq_woldActivationInfiniteDepth_blowupChart hfac lam).filter_mono
    nhdsWithin_le_nhds).mono fun s hs => hs.symm

end

end GaloisForLFunctions.RHTower
