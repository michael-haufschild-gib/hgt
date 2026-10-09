import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic
import GaloisForLFunctions.Bottcher.AnalyticRoot

/-!
# Extension and order classification of punctured power roots

A holomorphic punctured root of an analytic function vanishing at the puncture
extends analytically by zero. Analytic orders multiply by the root degree.
Conversely, divisibility of a finite analytic order constructs a local root;
thus the punctured lifting condition is classified exactly by that divisibility.
-/

open Filter Topology Function Classical

namespace GaloisForLFunctions.HTGeometry

/-- A punctured power root tends to zero whenever its power does. -/
theorem tendsto_zero_of_pow_eq_on_punctured_nhds
    {f s : ℂ → ℂ} {a : ℂ} {n : ℕ} (_hn : 0 < n)
    (hf : ContinuousAt f a) (hfa : f a = 0)
    (hpow : ∀ᶠ z in 𝓝[≠] a, s z ^ n = f z) :
    Tendsto s (𝓝[≠] a) (𝓝 0) := by
  have hf0 : Tendsto f (𝓝[≠] a) (𝓝 0) := by
    simpa only [hfa] using hf.tendsto.mono_left nhdsWithin_le_nhds
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hf0 (ε ^ n) (pow_pos hε n), hpow] with z hz hp
  have hnorm : ‖s z‖ ^ n < ε ^ n := by
    rw [← norm_pow, hp]
    simpa only [dist_zero_right] using hz
  rw [dist_zero_right]
  by_contra! hge
  have hle : ε ^ n ≤ ‖s z‖ ^ n := by gcongr
  exact (not_le_of_gt hnorm) hle

/-- A holomorphic power root on a punctured neighborhood extends analytically across the zero. -/
theorem analyticAt_update_zero_of_pow_eq_on_punctured_nhds
    {f s : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (hs : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ s z)
    (hpow : ∀ᶠ z in 𝓝[≠] a, s z ^ n = f z) :
    AnalyticAt ℂ (update s a 0) a := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [hs, self_mem_nhdsWithin] with z hz hzne
    apply hz.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hzne] with w hw
    exact update_of_ne hw _ _
  · exact continuousAt_update_same.mpr
      (tendsto_zero_of_pow_eq_on_punctured_nhds hn hf.continuousAt hfa hpow)

/-- The extension has exactly the order forced by the ramified projection. -/
theorem analyticOrderAt_update_zero_mul_of_pow_eq_on_punctured_nhds
    {f s : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (hs : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ s z)
    (hpow : ∀ᶠ z in 𝓝[≠] a, s z ^ n = f z) :
    analyticOrderAt f a = n • analyticOrderAt (update s a 0) a := by
  have he : AnalyticAt ℂ (update s a 0) a :=
    analyticAt_update_zero_of_pow_eq_on_punctured_nhds hn hf hfa hs hpow
  have heq : ((update s a 0) ^ n) =ᶠ[𝓝 a] f := by
    have hp := eventually_nhdsWithin_iff.mp hpow
    filter_upwards [hp] with z hz
    by_cases hza : z = a
    · subst z
      simp [hfa, Nat.ne_of_gt hn]
    · simpa only [Pi.pow_apply, update_of_ne hza] using hz hza
  rw [← analyticOrderAt_congr heq]
  exact analyticOrderAt_pow he n

/-- In particular the ramification degree divides the natural analytic order. -/
theorem dvd_analyticOrderNatAt_of_pow_eq_on_punctured_nhds
    {f s : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (hs : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ s z)
    (hpow : ∀ᶠ z in 𝓝[≠] a, s z ^ n = f z) :
    n ∣ analyticOrderNatAt f a := by
  have hord := analyticOrderAt_update_zero_mul_of_pow_eq_on_punctured_nhds hn hf hfa hs hpow
  refine ⟨analyticOrderNatAt (update s a 0) a, ?_⟩
  simpa [analyticOrderNatAt] using congrArg ENat.toNat hord

private theorem exists_analyticAt_power_root_of_ne_zero
    {u : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hu : AnalyticAt ℂ u a) (hu0 : u a ≠ 0) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v a ∧ (v ^ n) =ᶠ[𝓝 a] u := by
  have he : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ u z ∧ u z ≠ 0 :=
    hu.eventually_analyticAt.and
      (hu.continuousAt.eventually (isOpen_ne.mem_nhds hu0))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hsc : IsSimplyConnected (Metric.ball a r) := by
    letI : ContractibleSpace (Metric.ball a r) :=
      (convex_ball a r).contractibleSpace (Metric.nonempty_ball.mpr hr)
    change SimplyConnectedSpace ↥(Metric.ball a r)
    infer_instance
  obtain ⟨v, hva, hvp⟩ := Bottcher.exists_analyticOnNhd_pow_eq hsc Metric.isOpen_ball
    (fun z hz => (hball hz).1) (fun z hz => (hball hz).2) hn
  refine ⟨v, hva a (Metric.mem_ball_self hr), ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hr] with z hz
  exact hvp z hz

/-- Finite-order divisibility is sufficient for a local analytic power root. -/
theorem exists_analyticAt_power_root_of_dvd_order
    {f : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticAt ℂ f a) (hfin : analyticOrderAt f a ≠ ⊤)
    (hdiv : n ∣ analyticOrderNatAt f a) :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s a ∧ (s ^ n) =ᶠ[𝓝 a] f := by
  obtain ⟨u, hu, hu0, hfu⟩ := (hf.analyticOrderNatAt_eq_iff hfin).mp rfl
  obtain ⟨v, hv, hvp⟩ := exists_analyticAt_power_root_of_ne_zero hn hu hu0
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨fun z => (z - a) ^ k * v z,
    ((analyticAt_id.sub analyticAt_const).pow k).mul hv, ?_⟩
  filter_upwards [hfu, hvp] with z hz hvz
  change ((z - a) ^ k * v z) ^ n = f z
  change v z ^ n = u z at hvz
  rw [mul_pow, hvz, hz, smul_eq_mul, ← pow_mul, hk, Nat.mul_comm k n]

/-- The exact local ramification criterion at a finite-order zero. -/
theorem exists_punctured_power_root_iff_dvd_analyticOrderNatAt
    {f : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticAt ℂ f a) (hfa : f a = 0) (hfin : analyticOrderAt f a ≠ ⊤) :
    (∃ s : ℂ → ℂ, (∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ s z) ∧
      ∀ᶠ z in 𝓝[≠] a, s z ^ n = f z) ↔ n ∣ analyticOrderNatAt f a := by
  constructor
  · rintro ⟨s, hs, hpow⟩
    exact dvd_analyticOrderNatAt_of_pow_eq_on_punctured_nhds hn hf hfa hs hpow
  · intro hdiv
    obtain ⟨s, hs, hpow⟩ := exists_analyticAt_power_root_of_dvd_order hn hf hfin hdiv
    refine ⟨s, ?_, hpow.filter_mono nhdsWithin_le_nhds⟩
    exact (hs.eventually_analyticAt.mono fun z hz => hz.differentiableAt).filter_mono
      nhdsWithin_le_nhds

end GaloisForLFunctions.HTGeometry
