import GaloisForLFunctions.RHTower.ProlateTailIntegralBound

/-!
# The Gaussian target and the two transfer inputs for the profile integral

The growing-window transfer needs three inputs at the prolate family: convergence of the integral
over every fixed window, convergence of the window values to the target, and smallness of the tails.
This file supplies the first two in the form the family provides them, plus the reflection that
turns the right tail bound into the left one.

* `integral_gaussianProfile` : `∫_ℝ e^{−x²/2} = √(2π)`, the target value.
* `tendsto_intervalIntegral_gaussianProfile` : the window values converge to it.
* `tendsto_intervalIntegral_of_window_dist` : uniform closeness on a window transfers to the
  integrals over that window.
* `intervalIntegral_neg_of_even` : for an even integrand the left tail equals the right tail.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The Gaussian target -/

theorem gaussianProfile_eq (x : ℝ) : gaussianProfile x = Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ)) := by
  rw [gaussianProfile]
  ring_nf

theorem integrable_gaussianProfile : Integrable gaussianProfile volume := by
  have h := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  refine h.congr ?_
  filter_upwards with x
  exact (gaussianProfile_eq x).symm

theorem continuous_gaussianProfile : Continuous gaussianProfile := by
  have hfun : gaussianProfile = fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ)) :=
    funext gaussianProfile_eq
  rw [hfun]
  exact Real.continuous_exp.comp (by fun_prop)

/-- **The total mass of the Gaussian profile.** -/
theorem integral_gaussianProfile : (∫ x : ℝ, gaussianProfile x) = Real.sqrt (2 * Real.pi) := by
  have hfun : (fun x : ℝ => gaussianProfile x) = fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ)) := by
    funext x
    exact gaussianProfile_eq x
  rw [hfun, integral_gaussian]
  congr 1
  ring

/-- **The symmetric windows exhaust the Gaussian mass.** -/
theorem tendsto_intervalIntegral_gaussianProfile :
    Tendsto (fun K : ℝ => ∫ x in (-K)..K, gaussianProfile x) atTop
      (𝓝 (Real.sqrt (2 * Real.pi))) := by
  have h := intervalIntegral_tendsto_integral (μ := volume) (l := (atTop : Filter ℝ))
    (a := fun K : ℝ => -K) (b := fun K : ℝ => K) integrable_gaussianProfile
    tendsto_neg_atTop_atBot tendsto_id
  rwa [integral_gaussianProfile] at h

/-! ## Uniform closeness on a window transfers to the integrals -/

/-- Uniform closeness on a symmetric window bounds the difference of the integrals by the
envelope times the window length. -/
theorem abs_intervalIntegral_sub_le_of_window_dist {u v : ℝ → ℝ} {K E : ℝ} (hK : 0 ≤ K)
    (hu : Continuous u) (hv : Continuous v)
    (hdist : ∀ x ∈ Icc (-K) K, |u x - v x| ≤ E) :
    ‖(∫ x in (-K)..K, u x) - ∫ x in (-K)..K, v x‖ ≤ E * (2 * K) := by
  have hsub : (∫ x in (-K)..K, u x) - ∫ x in (-K)..K, v x = ∫ x in (-K)..K, (u x - v x) := by
    rw [intervalIntegral.integral_sub (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]
  have hsubset : uIoc (-K) K ⊆ Icc (-K) K := by
    rw [uIoc_of_le (by linarith : (-K : ℝ) ≤ K)]
    exact Ioc_subset_Icc_self
  rw [hsub]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => u x - v x) (a := -K) (b := K) (C := E)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hdist x (hsubset hx))
  have habs : |K - -K| = 2 * K := by
    rw [show K - -K = 2 * K by ring, abs_of_nonneg (by linarith)]
  rwa [habs] at hle

/-- **Window transfer.**  A family eventually uniformly close to a fixed continuous function on a
symmetric window has integrals over that window converging to the integral of the limit. -/
theorem tendsto_intervalIntegral_of_window_dist {ι : Type*} {L : Filter ι}
    {u : ι → ℝ → ℝ} {v : ℝ → ℝ} {K : ℝ} {E : ι → ℝ} (hK : 0 ≤ K)
    (hv : Continuous v)
    (hev : ∀ᶠ i in L, Continuous (u i) ∧ ∀ x ∈ Icc (-K) K, |u i x - v x| ≤ E i)
    (hE : Tendsto E L (𝓝 0)) :
    Tendsto (fun i => ∫ x in (-K)..K, u i x) L (𝓝 (∫ x in (-K)..K, v x)) := by
  have hbnd : ∀ᶠ i in L,
      ‖(∫ x in (-K)..K, u i x) - ∫ x in (-K)..K, v x‖ ≤ E i * (2 * K) := by
    filter_upwards [hev] with i hi
    exact abs_intervalIntegral_sub_le_of_window_dist hK hi.1 hv hi.2
  have henv : Tendsto (fun i => E i * (2 * K)) L (𝓝 0) := by
    simpa using hE.mul_const (2 * K)
  have hzero := squeeze_zero_norm' hbnd henv
  have hadd := hzero.add_const (∫ x in (-K)..K, v x)
  simpa using hadd

/-! ## Reflection -/

/-- For an even integrand the left tail equals the right tail. -/
theorem intervalIntegral_neg_of_even {f : ℝ → ℝ} (hf : Function.Even f) (K R : ℝ) :
    (∫ x in (-R)..(-K), f x) = ∫ x in K..R, f x := by
  have h := intervalIntegral.integral_comp_neg (a := K) (b := R) f
  rw [show (fun x : ℝ => f (-x)) = f from funext fun x => hf x] at h
  exact h.symm

/-! ## The growing-window transfer with eventual integrability -/

/-- **Convergence of integrals over a growing window**, with integrability required only
eventually.  A family indexed by a bandwidth and defined only for positive bandwidth satisfies the
hypotheses in this form and not in the unconditional one. -/
theorem tendsto_intervalIntegral_growing_window' {ι : Type*} {L : Filter ι}
    {F : ι → ℝ → ℝ} {R : ι → ℝ} {g : ℝ → ℝ} {A : ℝ}
    (hint : ∀ᶠ i in L, ∀ u v : ℝ, IntervalIntegrable (F i) volume u v)
    (hcompact : ∀ K : ℝ, 0 < K → Tendsto (fun i => ∫ x in (-K)..K, F i x) L (𝓝 (g K)))
    (hg : Tendsto g atTop (𝓝 A))
    (hKR : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, K ≤ R i)
    (htail : ∀ δ : ℝ, 0 < δ → ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      ∀ᶠ i in L, |∫ x in K..(R i), F i x| ≤ δ ∧ |∫ x in (-(R i))..(-K), F i x| ≤ δ) :
    Tendsto (fun i => ∫ x in (-(R i))..(R i), F i x) L (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K₀, hK₀, htailK⟩ := htail (ε / 5) (by linarith)
  have hgev := (Metric.tendsto_nhds.1 hg) (ε / 5) (by linarith)
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.1 hgev
  set K : ℝ := max K₀ (max K₁ 1) with hKdef
  have hK1le : (1 : ℝ) ≤ K := le_trans (le_max_right K₁ 1) (le_max_right K₀ _)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1le
  have hKK₀ : K₀ ≤ K := le_max_left _ _
  have hKK₁ : K₁ ≤ K := le_trans (le_max_left K₁ 1) (le_max_right K₀ _)
  have hgK : dist (g K) A < ε / 5 := hK₁ K hKK₁
  have hmid := (Metric.tendsto_nhds.1 (hcompact K hK0)) (ε / 5) (by linarith)
  filter_upwards [hmid, htailK K hKK₀, hKR K hK0, hint] with i hi hti _hRi hinti
  obtain ⟨htail1, htail2⟩ := hti
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (f := F i) (μ := volume) (a := -(R i)) (b := -K) (c := K) (hinti _ _) (hinti _ _)
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    (f := F i) (μ := volume) (a := -(R i)) (b := K) (c := R i) (hinti _ _) (hinti _ _)
  rw [Real.dist_eq] at hi hgK ⊢
  have hid : (∫ x in (-(R i))..(R i), F i x) - A
      = ((∫ x in (-K)..K, F i x) - g K) + (g K - A)
        + (∫ x in (-(R i))..(-K), F i x) + (∫ x in K..(R i), F i x) := by
    have h1 : (∫ x in (-(R i))..(-K), F i x) + (∫ x in (-K)..K, F i x)
        = ∫ x in (-(R i))..K, F i x := hadd1
    have h2 : (∫ x in (-(R i))..K, F i x) + (∫ x in K..(R i), F i x)
        = ∫ x in (-(R i))..(R i), F i x := hadd2
    linarith [h1, h2]
  rw [hid]
  have hb1 := abs_add_le ((∫ x in (-K)..K, F i x) - g K + (g K - A)
      + (∫ x in (-(R i))..(-K), F i x)) (∫ x in K..(R i), F i x)
  have hb2 := abs_add_le ((∫ x in (-K)..K, F i x) - g K + (g K - A))
      (∫ x in (-(R i))..(-K), F i x)
  have hb3 := abs_add_le ((∫ x in (-K)..K, F i x) - g K) (g K - A)
  linarith [hb1, hb2, hb3, hi, hgK, htail1, htail2]

end GaloisForLFunctions.RHTower

end
