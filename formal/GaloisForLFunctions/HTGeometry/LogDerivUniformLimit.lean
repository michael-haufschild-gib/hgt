/-
# Uniform convergence of logarithmic derivatives, and of their contour integrals

If entire functions `Fₐ` converge to `f` uniformly on a closed disc and `f` does not vanish on an
interior circle, then the logarithmic derivatives converge uniformly on that circle and hence so do
their contour integrals.

Two ingredients: Cauchy's estimate turns a sup bound on a difference into a sup bound on the
derivative of the difference, and the algebraic identity

  `F′/F − f′/f = (F′ − f′)/F + f′(f − F)/(F f)`

turns both into a bound on the difference of logarithmic derivatives.

Main results:
* `norm_deriv_le_of_forall_norm_le` — Cauchy's estimate for the first derivative.
* `tendstoUniformlyOn_deriv_of_tendstoUniformlyOn` — derivatives converge uniformly on a smaller
  disc.
* `norm_logDeriv_sub_le` — the pointwise bound on the difference of logarithmic derivatives.
* `tendsto_circleIntegral_logDeriv` — **the contour integrals of the logarithmic derivatives
  converge**.
* `eventually_zeroCount_eq_analyticOrder` — **counting Hurwitz**: the eventual zero count of the
  approximants equals the order of vanishing of the limit.
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import GaloisForLFunctions.HTGeometry.HurwitzZeroLimit
import GaloisForLFunctions.HTGeometry.EntireZeroFactorization

namespace GaloisForLFunctions.HTGeometry

open Metric Filter

/-- **Cauchy's estimate for the first derivative.**  A sup bound on a disc of radius `δ` around `z`
bounds `‖h′ z‖` by `ε/δ`. -/
theorem norm_deriv_le_of_forall_norm_le {h : ℂ → ℂ} (hh : Differentiable ℂ h) {c : ℂ}
    {R ε δ : ℝ} (hδ : 0 < δ) (hbound : ∀ w : ℂ, ‖w - c‖ ≤ R → ‖h w‖ ≤ ε) {z : ℂ}
    (hz : ‖z - c‖ + δ ≤ R) : ‖deriv h z‖ ≤ ε / δ := by
  have hsphere : ∀ w ∈ sphere z δ, ‖h w‖ ≤ ε := by
    intro w hw
    have hwz : ‖w - z‖ = δ := by simpa [Complex.dist_eq] using mem_sphere.mp hw
    refine hbound w ?_
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      _ = δ + ‖z - c‖ := by rw [hwz]
      _ ≤ R := by linarith
  have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := z) (R := δ) (C := ε)
    1 hδ hh.diffContOnCl hsphere
  rw [iteratedDeriv_one] at h1
  simpa using h1

/-- **The derivatives converge uniformly on a smaller disc.** -/
theorem tendstoUniformlyOn_deriv_of_tendstoUniformlyOn {α : Type*} {p : Filter α}
    {F : α → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ a, Differentiable ℂ (F a)) (hf : Differentiable ℂ f)
    {c : ℂ} {R ρ : ℝ} (hρR : ρ < R)
    (huniform : TendstoUniformlyOn F f p (closedBall c R)) :
    TendstoUniformlyOn (fun a => deriv (F a)) (deriv f) p (closedBall c ρ) := by
  set δ : ℝ := R - ρ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  rw [Metric.tendstoUniformlyOn_iff] at huniform ⊢
  intro ε hε
  have hεδ : 0 < ε * δ / 2 := by positivity
  filter_upwards [huniform (ε * δ / 2) hεδ] with a ha z hz
  have hdiff : Differentiable ℂ (fun w => f w - F a w) := hf.sub (hF a)
  have hbound : ∀ w : ℂ, ‖w - c‖ ≤ R → ‖f w - F a w‖ ≤ ε * δ / 2 := by
    intro w hw
    have hwmem : w ∈ closedBall c R := by
      rw [mem_closedBall, Complex.dist_eq]
      exact hw
    have := ha w hwmem
    rw [Complex.dist_eq] at this
    exact this.le
  have hzc : ‖z - c‖ ≤ ρ := by
    rw [mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hzδ : ‖z - c‖ + δ ≤ R := by rw [hδdef]; linarith
  have hderiv := norm_deriv_le_of_forall_norm_le hdiff hδ hbound hzδ
  have hsub : deriv (fun w => f w - F a w) z = deriv f z - deriv (F a) z := by
    exact deriv_fun_sub hf.differentiableAt (hF a).differentiableAt
  rw [hsub] at hderiv
  rw [Complex.dist_eq]
  calc ‖deriv f z - deriv (F a) z‖ ≤ ε * δ / 2 / δ := hderiv
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- The pointwise bound on the difference of two logarithmic derivatives, from the identity
`F′/F − f′/f = (F′ − f′)/F + f′(f − F)/(F f)`. -/
theorem norm_logDeriv_sub_le {F f : ℂ → ℂ} {z : ℂ} {m Mf η : ℝ} (hm : 0 < m)
    (hfz : m ≤ ‖f z‖) (hFz : m / 2 ≤ ‖F z‖) (hMf : 0 ≤ Mf) (hdf : ‖deriv f z‖ ≤ Mf)
    (h1 : ‖f z - F z‖ ≤ η) (h2 : ‖deriv (F) z - deriv f z‖ ≤ η) :
    ‖logDeriv F z - logDeriv f z‖ ≤ 2 * η / m + 2 * Mf * η / m ^ (2 : ℕ) := by
  have hFne : F z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hFz
    linarith
  have hfne : f z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hfz
    linarith
  have hFpos : 0 < ‖F z‖ := norm_pos_iff.mpr hFne
  have hfpos : 0 < ‖f z‖ := norm_pos_iff.mpr hfne
  have hid : logDeriv F z - logDeriv f z
      = (deriv F z - deriv f z) / F z + deriv f z * (f z - F z) / (F z * f z) := by
    rw [logDeriv_apply, logDeriv_apply]
    field_simp
    ring
  have hη : 0 ≤ η := le_trans (norm_nonneg _) h1
  have hb1 : ‖(deriv F z - deriv f z) / F z‖ ≤ 2 * η / m := by
    rw [norm_div, div_le_div_iff₀ hFpos hm]
    calc ‖deriv F z - deriv f z‖ * m ≤ η * m := mul_le_mul_of_nonneg_right h2 hm.le
      _ ≤ 2 * η * ‖F z‖ := by nlinarith [hη, hFz]
  have hb2 : ‖deriv f z * (f z - F z) / (F z * f z)‖ ≤ 2 * Mf * η / m ^ (2 : ℕ) := by
    rw [norm_div, norm_mul, norm_mul]
    have hden : 0 < ‖F z‖ * ‖f z‖ := by positivity
    rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < m ^ (2 : ℕ))]
    have hprod : ‖deriv f z‖ * ‖f z - F z‖ ≤ Mf * η :=
      mul_le_mul hdf h1 (norm_nonneg _) hMf
    have hFf : m ^ (2 : ℕ) / 2 ≤ ‖F z‖ * ‖f z‖ := by nlinarith [hFz, hfz, hm]
    calc ‖deriv f z‖ * ‖f z - F z‖ * m ^ (2 : ℕ) ≤ Mf * η * m ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
      _ ≤ 2 * Mf * η * (‖F z‖ * ‖f z‖) := by nlinarith [mul_nonneg hMf hη, hFf]
  calc ‖logDeriv F z - logDeriv f z‖
      = ‖(deriv F z - deriv f z) / F z + deriv f z * (f z - F z) / (F z * f z)‖ := by rw [hid]
    _ ≤ ‖(deriv F z - deriv f z) / F z‖ + ‖deriv f z * (f z - F z) / (F z * f z)‖ :=
        norm_add_le _ _
    _ ≤ 2 * η / m + 2 * Mf * η / m ^ (2 : ℕ) := add_le_add hb1 hb2

/-- The derivative of an entire function is entire. -/
theorem differentiable_deriv_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) := fun _ =>
  ((hf.differentiableOn.analyticAt Filter.univ_mem).deriv).differentiableAt

/-- **The contour integrals of the logarithmic derivatives converge.** -/
theorem tendsto_circleIntegral_logDeriv {α : Type*} {p : Filter α}
    {F : α → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ a, Differentiable ℂ (F a)) (hf : Differentiable ℂ f)
    {c : ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (huniform : TendstoUniformlyOn F f p (closedBall c R))
    (hfne : ∀ z ∈ sphere c r, f z ≠ 0) :
    Tendsto (fun a => ∮ z in C(c, r), logDeriv (F a) z) p
      (nhds (∮ z in C(c, r), logDeriv f z)) := by
  classical
  have hdf : Differentiable ℂ (deriv f) := differentiable_deriv_of_differentiable hf
  obtain ⟨m, hm, hmle⟩ :=
    exists_pos_le_norm_on_sphere hr hf.continuous.continuousOn hfne
  obtain ⟨w, hw, hmax⟩ := (isCompact_sphere c r).exists_isMaxOn
    ⟨c + r, by simp [Complex.norm_real, abs_of_pos hr]⟩ hdf.continuous.continuousOn.norm
  set Mf : ℝ := ‖deriv f w‖ with hMfdef
  have hMf : 0 ≤ Mf := norm_nonneg _
  have hMfle : ∀ z ∈ sphere c r, ‖deriv f z‖ ≤ Mf := fun z hz => hmax hz
  set ρ : ℝ := (r + R) / 2 with hρdef
  have hrρ : r < ρ := by rw [hρdef]; linarith
  have hρR : ρ < R := by rw [hρdef]; linarith
  have hsphρ : sphere c r ⊆ closedBall c ρ := fun z hz => by
    rw [mem_closedBall, Metric.mem_sphere.mp hz]
    exact hrρ.le
  have hsphR : sphere c r ⊆ closedBall c R := fun z hz => by
    rw [mem_closedBall, Metric.mem_sphere.mp hz]
    linarith
  have hderivU := tendstoUniformlyOn_deriv_of_tendstoUniformlyOn hF hf hρR huniform
  rw [Metric.tendstoUniformlyOn_iff] at huniform hderivU
  set Cb : ℝ := 2 / m + 2 * Mf / m ^ (2 : ℕ) with hCbdef
  have hCb : 0 ≤ Cb := by rw [hCbdef]; positivity
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  set K : ℝ := 2 * Real.pi * r * Cb + 1 with hKdef
  have hK : 0 < K := by
    rw [hKdef]
    have : 0 ≤ 2 * Real.pi * r * Cb := by positivity
    linarith
  set η : ℝ := min (m / 2) (ε / K) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  filter_upwards [huniform η hη, hderivU η hη] with a ha hda
  -- pointwise control on the circle
  have hpt : ∀ z ∈ sphere c r, ‖logDeriv (F a) z - logDeriv f z‖ ≤ η * Cb := by
    intro z hz
    have h1 : ‖f z - F a z‖ ≤ η := by
      have := ha z (hsphR hz)
      rw [Complex.dist_eq] at this
      exact this.le
    have h2 : ‖deriv (F a) z - deriv f z‖ ≤ η := by
      have := hda z (hsphρ hz)
      rw [Complex.dist_eq, ← norm_neg] at this
      simpa using this.le
    have hFz : m / 2 ≤ ‖F a z‖ := by
      have hmz : m ≤ ‖f z‖ := hmle z hz
      have hle : η ≤ m / 2 := min_le_left _ _
      have := norm_sub_norm_le (f z) (F a z)
      linarith
    have := norm_logDeriv_sub_le hm (hmle z hz) hFz hMf (hMfle z hz) h1 h2
    calc ‖logDeriv (F a) z - logDeriv f z‖ ≤ 2 * η / m + 2 * Mf * η / m ^ (2 : ℕ) := this
      _ = η * Cb := by rw [hCbdef]; field_simp
  -- circle integrability of both logarithmic derivatives
  have hciF : CircleIntegrable (fun z => logDeriv (F a) z) c r := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    have hFz : F a z ≠ 0 := by
      intro h0
      have hmz : m ≤ ‖f z‖ := hmle z hz
      have h1 : ‖f z - F a z‖ ≤ η := by
        have := ha z (hsphR hz)
        rw [Complex.dist_eq] at this
        exact this.le
      rw [h0, sub_zero] at h1
      have hle : η ≤ m / 2 := min_le_left _ _
      linarith
    exact ((differentiable_deriv_of_differentiable (hF a)).continuous.continuousAt.div
      (hF a).continuous.continuousAt hFz).continuousWithinAt
  have hcif : CircleIntegrable (fun z => logDeriv f z) c r := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    exact (hdf.continuous.continuousAt.div (hf.continuous.continuousAt)
      (hfne z hz)).continuousWithinAt
  -- bound the contour integral of the difference
  have hsub : (∮ z in C(c, r), logDeriv (F a) z) - ∮ z in C(c, r), logDeriv f z
      = ∮ z in C(c, r), (logDeriv (F a) z - logDeriv f z) :=
    (circleIntegral.integral_sub hciF hcif).symm
  have hbound : ‖(∮ z in C(c, r), logDeriv (F a) z) - ∮ z in C(c, r), logDeriv f z‖
      ≤ 2 * Real.pi * r * (η * Cb) := by
    rw [hsub]
    exact circleIntegral.norm_integral_le_of_norm_le_const hr.le hpt
  have hfinal : 2 * Real.pi * r * (η * Cb) < ε := by
    have hηK : η ≤ ε / K := min_le_right _ _
    have hpos : 0 ≤ 2 * Real.pi * r * Cb := by positivity
    calc 2 * Real.pi * r * (η * Cb) = η * (2 * Real.pi * r * Cb) := by ring
      _ ≤ (ε / K) * (2 * Real.pi * r * Cb) := by nlinarith [hη.le]
      _ < (ε / K) * K := by
          refine mul_lt_mul_of_pos_left ?_ (by positivity)
          rw [hKdef]; linarith
      _ = ε := by field_simp
  rw [Complex.dist_eq]
  exact lt_of_le_of_lt hbound hfinal

/-- A convergent family of natural numbers is eventually constant. -/
theorem eventually_eq_of_tendsto_natCast {α : Type*} {p : Filter α} {n : α → ℕ} {d : ℕ}
    (h : Tendsto (fun a => ((n a : ℕ) : ℂ)) p (nhds ((d : ℕ) : ℂ))) :
    ∀ᶠ a in p, n a = d := by
  filter_upwards [Metric.tendsto_nhds.mp h 1 one_pos] with a ha
  rw [Complex.dist_eq] at ha
  have hreal : ‖((n a : ℕ) : ℂ) - ((d : ℕ) : ℂ)‖ = |((n a : ℕ) : ℝ) - ((d : ℕ) : ℝ)| := by
    rw [show ((n a : ℕ) : ℂ) = (((n a : ℕ) : ℝ) : ℂ) by push_cast; ring,
      show ((d : ℕ) : ℂ) = (((d : ℕ) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hreal] at ha
  have hint : |((n a : ℕ) : ℤ) - ((d : ℕ) : ℤ)| < 1 := by exact_mod_cast ha
  rw [abs_lt] at hint
  omega

/-- **Counting Hurwitz.**  If the approximants converge uniformly on a disc, the limit has an
isolated zero of order `d` at the centre and no other zeros, and each approximant's logarithmic
derivative integrates to `2πi·nₐ`, then eventually `nₐ = d`. -/
theorem eventually_zeroCount_eq_analyticOrder {α : Type*} {p : Filter α}
    {F : α → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ a, Differentiable ℂ (F a)) (hf : Differentiable ℂ f)
    {c : ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (huniform : TendstoUniformlyOn F f p (closedBall c R))
    {d : ℕ} {R' : ℝ} (hrR' : r < R') (hord : analyticOrderAt f c = (d : ℕ∞))
    (hne : ∀ z ∈ closedBall c R', z ≠ c → f z ≠ 0)
    {n : α → ℕ} (hn : ∀ a, (∮ z in C(c, r), logDeriv (F a) z)
      = 2 * Real.pi * Complex.I * (n a : ℂ)) :
    ∀ᶠ a in p, n a = d := by
  have hfne : ∀ z ∈ sphere c r, f z ≠ 0 := by
    intro z hz
    have hd : dist z c = r := Metric.mem_sphere.mp hz
    refine hne z (by rw [mem_closedBall, hd]; linarith) fun hzc => ?_
    rw [hzc, dist_self] at hd
    exact hr.ne hd
  have hlim := tendsto_circleIntegral_logDeriv hF hf hr hrR huniform hfne
  have hf' : (∮ z in C(c, r), logDeriv f z) = 2 * Real.pi * Complex.I * (d : ℂ) := by
    have := circleIntegral_logDeriv_eq_analyticOrder_local (R := R') hf hord
      (fun z hz hzc => hne z (ball_subset_closedBall hz) hzc) hr hrR'
    simpa [logDeriv_apply] using this
  have hconst : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have htend : Tendsto (fun a => ((n a : ℕ) : ℂ)) p (nhds ((d : ℕ) : ℂ)) := by
    have hscaled : Tendsto (fun a => 2 * Real.pi * Complex.I * (n a : ℂ)) p
        (nhds (2 * Real.pi * Complex.I * (d : ℂ))) := by
      simp only [← hn, ← hf']
      exact hlim
    have hmul := hscaled.const_mul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
    simp only [← mul_assoc, inv_mul_cancel₀ hconst, one_mul] at hmul
    exact hmul
  exact eventually_eq_of_tendsto_natCast htend

end GaloisForLFunctions.HTGeometry
