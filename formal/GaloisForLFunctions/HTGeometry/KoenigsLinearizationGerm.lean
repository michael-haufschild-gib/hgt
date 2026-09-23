import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Koenigs linearization of a holomorphic germ

A holomorphic germ fixing the origin with attracting nonzero multiplier is linearizable: the
rescaled iterates `g^[n] z / μ^n` converge locally uniformly to a holomorphic `κ` with `κ 0 = 0`,
`κ' 0 = 1` and `κ ∘ g = μ · κ`.  The convergence rests on the second-order Taylor bound for the
germ, which is the first statement below.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

noncomputable section

/-- **Second-order Taylor bound for a holomorphic germ.**  An analytic germ vanishing at the origin
differs from its linear part by `O(‖z‖²)` on a neighbourhood. -/
theorem exists_quadratic_bound {g : ℂ → ℂ} {μ : ℂ} (hg : AnalyticAt ℂ g 0)
    (hg0 : g 0 = 0) (hgd : deriv g 0 = μ) :
    ∃ K r : ℝ, 0 < K ∧ 0 < r ∧ ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ) := by
  set G : ℂ → ℂ := fun z => g z - μ * z with hG
  have hGa : AnalyticAt ℂ G 0 := hg.sub ((analyticAt_const).mul analyticAt_id)
  have hG0 : G 0 = 0 := by simp [hG, hg0]
  have hGd : deriv G 0 = 0 := by
    have h1 : HasDerivAt g μ 0 := by
      have := hg.differentiableAt.hasDerivAt
      rwa [hgd] at this
    have h2 : HasDerivAt (fun z : ℂ => μ * z) μ 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul μ
    exact (h1.sub h2).deriv.trans (by ring)
  obtain ⟨p, hp⟩ := hGa
  have hd : p.coeff 1 = deriv G 0 := hp.deriv.symm
  have hpartial : ∀ y : ℂ, p.partialSum 2 y = 0 := by
    intro y
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    have h0 : p 0 (fun _ => y) = 0 := by
      have := hp.coeff_zero (fun _ => y)
      simpa [hG0] using this
    have h1 : p 1 (fun _ => y) = y * p.coeff 1 := by
      rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
      simp [smul_eq_mul]
    rw [h0, h1, hd, hGd, mul_zero, add_zero]
  have hbig := hp.isBigO_sub_partialSum_pow 2
  simp only [zero_add, hpartial, sub_zero] at hbig
  obtain ⟨K, hKpos, hKev⟩ := hbig.exists_pos
  rw [Asymptotics.isBigOWith_iff] at hKev
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hKev
  refine ⟨K, r / 2, hKpos, by linarith, fun z hz => ?_⟩
  have hzmem : z ∈ Metric.ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right]
    linarith
  have := hrsub hzmem
  simpa using this

/-- **Contraction ball for an attracting germ.**  Below any contraction rate strictly above the
multiplier modulus, the germ contracts a small ball and carries its quadratic Taylor bound. -/
theorem exists_contraction_ball {g : ℂ → ℂ} {μ : ℂ} (hg : AnalyticAt ℂ g 0)
    (hg0 : g 0 = 0) (hgd : deriv g 0 = μ) {c : ℝ} (hc : ‖μ‖ < c) :
    ∃ K r : ℝ, 0 < K ∧ 0 < r ∧
      (∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ)) ∧
      (∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖) := by
  obtain ⟨K, r₀, hK, hr₀, hquad⟩ := exists_quadratic_bound hg hg0 hgd
  refine ⟨K, min r₀ ((c - ‖μ‖) / K), hK, lt_min hr₀ (by positivity), ?_, ?_⟩
  · intro z hz
    exact hquad z (le_trans hz (min_le_left _ _))
  · intro z hz
    have hz₀ : ‖z‖ ≤ r₀ := le_trans hz (min_le_left _ _)
    have hzc : ‖z‖ ≤ (c - ‖μ‖) / K := le_trans hz (min_le_right _ _)
    have hq := hquad z hz₀
    have hsplit : ‖g z‖ ≤ ‖μ * z‖ + ‖g z - μ * z‖ := by
      have := norm_add_le (μ * z) (g z - μ * z)
      simpa using this
    have hKz : K * ‖z‖ ^ (2 : ℕ) ≤ (c - ‖μ‖) * ‖z‖ := by
      have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      have h1 : ‖z‖ * K ≤ c - ‖μ‖ := (le_div_iff₀ hK).mp hzc
      nlinarith [h1, hzn]
    have hmul : ‖μ * z‖ = ‖μ‖ * ‖z‖ := norm_mul μ z
    linarith [hsplit, hq, hKz, hmul]

/-- **Geometric decay of the orbit.** -/
theorem orbit_norm_le {g : ℂ → ℂ} {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖) :
    ∀ (n : ℕ) {z : ℂ}, ‖z‖ ≤ r → ‖g^[n] z‖ ≤ c ^ n * ‖z‖ := by
  intro n
  induction n with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    have hstep := ih hz
    have hmem : ‖g^[n] z‖ ≤ r := by
      have hcn : c ^ n ≤ 1 := pow_le_one₀ hc0 hc1
      have hle : c ^ n * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) hcn
      linarith
    rw [Function.iterate_succ_apply']
    have := hgc _ hmem
    calc ‖g (g^[n] z)‖ ≤ c * ‖g^[n] z‖ := this
      _ ≤ c * (c ^ n * ‖z‖) := by
          exact mul_le_mul_of_nonneg_left hstep hc0
      _ = c ^ (n + 1) * ‖z‖ := by ring

/-- The Koenigs approximants of an attracting germ. -/
def koenigsApproxGerm (g : ℂ → ℂ) (μ : ℂ) (n : ℕ) (z : ℂ) : ℂ := g^[n] z / μ ^ n

@[simp] theorem koenigsApproxGerm_zero (g : ℂ → ℂ) (μ : ℂ) (z : ℂ) :
    koenigsApproxGerm g μ 0 z = z := by simp [koenigsApproxGerm]

/-- **The Koenigs telescope estimate.**  Consecutive approximants differ by a geometric term with
ratio `c²/‖μ‖`, which is less than one as soon as `c < √‖μ‖`. -/
theorem koenigsApproxGerm_dist_succ {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖)
    (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖koenigsApproxGerm g μ (n + 1) z - koenigsApproxGerm g μ n z‖ ≤
      (K * ‖z‖ ^ (2 : ℕ) / ‖μ‖) * (c ^ (2 : ℕ) / ‖μ‖) ^ n := by
  have hμn : (μ : ℂ) ^ n ≠ 0 := pow_ne_zero n hμ
  have hμnorm : (0 : ℝ) < ‖μ‖ := norm_pos_iff.mpr hμ
  have horb := orbit_norm_le hc0 hc1 hgc n hz
  have hmem : ‖g^[n] z‖ ≤ r := by
    have hcn : c ^ n ≤ 1 := pow_le_one₀ hc0 hc1
    have hle : c ^ n * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) hcn
    linarith
  have hkey : koenigsApproxGerm g μ (n + 1) z - koenigsApproxGerm g μ n z =
      (g (g^[n] z) - μ * g^[n] z) / μ ^ (n + 1) := by
    rw [koenigsApproxGerm, koenigsApproxGerm, Function.iterate_succ_apply']
    field_simp
    ring
  rw [hkey, norm_div, norm_pow]
  have hnum : ‖g (g^[n] z) - μ * g^[n] z‖ ≤ K * (c ^ n * ‖z‖) ^ (2 : ℕ) := by
    refine le_trans (hquad _ hmem) ?_
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have h1 : (0 : ℝ) ≤ ‖g^[n] z‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ c ^ n * ‖z‖ := by positivity
    nlinarith [horb, h1, h2]
  have hpos : (0 : ℝ) < ‖μ‖ ^ (n + 1) := by positivity
  rw [div_le_iff₀ hpos]
  have hμne : (‖μ‖ : ℝ) ≠ 0 := ne_of_gt hμnorm
  have hrhs : (K * ‖z‖ ^ (2 : ℕ) / ‖μ‖) * (c ^ (2 : ℕ) / ‖μ‖) ^ n * ‖μ‖ ^ (n + 1) = K * (c ^ n * ‖z‖) ^ (2 : ℕ) := by
    rw [div_pow, ← pow_mul, pow_succ]
    field_simp
    ring
  rw [hrhs]
  exact hnum

/-- **The Koenigs approximants form a Cauchy sequence.** -/
theorem koenigsApproxGerm_cauchySeq {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖)
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    CauchySeq (fun n => koenigsApproxGerm g μ n z) := by
  have hμnorm : (0 : ℝ) < ‖μ‖ := norm_pos_iff.mpr hμ
  refine cauchySeq_of_le_geometric (c ^ (2 : ℕ) / ‖μ‖) (K * ‖z‖ ^ (2 : ℕ) / ‖μ‖) ?_ ?_
  · rw [div_lt_one hμnorm]
    exact hq
  · intro n
    rw [dist_eq_norm, ← norm_neg]
    have hnorm : -(koenigsApproxGerm g μ n z - koenigsApproxGerm g μ (n + 1) z) =
        koenigsApproxGerm g μ (n + 1) z - koenigsApproxGerm g μ n z := by ring
    rw [hnorm]
    exact koenigsApproxGerm_dist_succ hμ hK0 hc0 hc1 hquad hgc n hz

/-- The Koenigs linearizer of an attracting germ. -/
def koenigsGerm (g : ℂ → ℂ) (μ : ℂ) (z : ℂ) : ℂ :=
  limUnder Filter.atTop fun n => koenigsApproxGerm g μ n z

theorem koenigsApproxGerm_tendsto {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖)
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    Filter.Tendsto (fun n => koenigsApproxGerm g μ n z) Filter.atTop
      (nhds (koenigsGerm g μ z)) :=
  (koenigsApproxGerm_cauchySeq hμ hK0 hc0 hc1 hq hquad hgc hz).tendsto_limUnder

/-- **The Koenigs functional equation.**  The linearizer conjugates the germ to multiplication by
its multiplier. -/
theorem koenigsGerm_semiconj {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖)
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    koenigsGerm g μ (g z) = μ * koenigsGerm g μ z := by
  have hgz : ‖g z‖ ≤ r := by
    have h1 := hgc z hz
    have h2 : c * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) hc1
    linarith
  have hshift : ∀ n : ℕ, koenigsApproxGerm g μ n (g z) = μ * koenigsApproxGerm g μ (n + 1) z := by
    intro n
    have hμn : (μ : ℂ) ^ n ≠ 0 := pow_ne_zero n hμ
    rw [koenigsApproxGerm, koenigsApproxGerm, ← Function.iterate_succ_apply]
    field_simp
    ring
  have h1 := koenigsApproxGerm_tendsto hμ hK0 hc0 hc1 hq hquad hgc hgz
  have h2 := (koenigsApproxGerm_tendsto hμ hK0 hc0 hc1 hq hquad hgc hz).comp
    (Filter.tendsto_add_atTop_nat 1)
  have h3 : Filter.Tendsto (fun n => koenigsApproxGerm g μ n (g z)) Filter.atTop
      (nhds (μ * koenigsGerm g μ z)) := by
    have hmul := h2.const_mul μ
    refine hmul.congr fun n => ?_
    exact (hshift n).symm
  exact tendsto_nhds_unique h1 h3

@[simp] theorem koenigsApproxGerm_at_zero {g : ℂ → ℂ} {μ : ℂ} (hg0 : g 0 = 0) (n : ℕ) :
    koenigsApproxGerm g μ n 0 = 0 := by
  have hfix : g^[n] 0 = 0 := Function.iterate_fixed hg0 n
  simp [koenigsApproxGerm, hfix]

theorem koenigsGerm_zero {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖)
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖)
    (hr : 0 ≤ r) (hg0 : g 0 = 0) :
    koenigsGerm g μ 0 = 0 := by
  have h := koenigsApproxGerm_tendsto hμ hK0 hc0 hc1 hq hquad hgc (z := 0) (by simpa using hr)
  have hconst : (fun n => koenigsApproxGerm g μ n (0 : ℂ)) = fun _ => (0 : ℂ) := by
    funext n
    exact koenigsApproxGerm_at_zero hg0 n
  rw [hconst] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The telescope differences of the Koenigs approximants. -/
def koenigsDiff (g : ℂ → ℂ) (μ : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  koenigsApproxGerm g μ (k + 1) z - koenigsApproxGerm g μ k z

theorem koenigsApproxGerm_eq_add_sum (g : ℂ → ℂ) (μ : ℂ) (n : ℕ) (z : ℂ) :
    koenigsApproxGerm g μ n z = z + ∑ k ∈ Finset.range n, koenigsDiff g μ k z := by
  have h := Finset.sum_range_sub (fun i => koenigsApproxGerm g μ i z) n
  simp only [koenigsDiff]
  rw [h, koenigsApproxGerm_zero]
  ring

/-- **Uniform convergence of the Koenigs approximants on the contraction ball.** -/
theorem koenigsApproxGerm_tendstoUniformlyOn {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖) (hr : 0 ≤ r)
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖) :
    TendstoUniformlyOn (fun n => koenigsApproxGerm g μ n) (koenigsGerm g μ)
      Filter.atTop (Metric.closedBall (0 : ℂ) r) := by
  have hμnorm : (0 : ℝ) < ‖μ‖ := norm_pos_iff.mpr hμ
  set q : ℝ := c ^ (2 : ℕ) / ‖μ‖ with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one hμnorm]
    exact hq
  set B : ℝ := K * r ^ (2 : ℕ) / ‖μ‖ with hBdef
  have hsum : Summable fun k : ℕ => B * q ^ k :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left B
  have hbound : ∀ k : ℕ, ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      ‖koenigsDiff g μ k z‖ ≤ B * q ^ k := by
    intro k z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    have hstep := koenigsApproxGerm_dist_succ hμ hK0 hc0 hc1 hquad hgc k hz
    refine le_trans hstep ?_
    have hzr : K * ‖z‖ ^ (2 : ℕ) / ‖μ‖ ≤ B := by
      rw [hBdef, div_le_div_iff_of_pos_right hμnorm]
      have : ‖z‖ ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by nlinarith [norm_nonneg z]
      nlinarith
    exact mul_le_mul_of_nonneg_right hzr (by positivity)
  have hpartial := tendstoUniformlyOn_tsum_nat (f := fun k => koenigsDiff g μ k) hsum hbound
  have hconst : TendstoUniformlyOn (fun (_ : ℕ) (z : ℂ) => z) (fun z : ℂ => z)
      Filter.atTop (Metric.closedBall (0 : ℂ) r) := by
    intro u hu
    filter_upwards with n
    intro z _
    exact refl_mem_uniformity hu
  have hsumUnif := hconst.add hpartial
  have hfinal : TendstoUniformlyOn (fun n => koenigsApproxGerm g μ n)
      (fun z : ℂ => z + ∑' k : ℕ, koenigsDiff g μ k z) Filter.atTop
      (Metric.closedBall (0 : ℂ) r) := by
    refine hsumUnif.congr ?_
    filter_upwards with n
    intro z _
    exact (koenigsApproxGerm_eq_add_sum g μ n z).symm
  refine hfinal.congr_right fun z hz => ?_
  have h1 : Filter.Tendsto (fun n => koenigsApproxGerm g μ n z) Filter.atTop
      (nhds (z + ∑' k : ℕ, koenigsDiff g μ k z)) := hfinal.tendsto_at hz
  have h2 := koenigsApproxGerm_tendsto hμ hK0 hc0 hc1 hq hquad hgc
    (by rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz)
  exact tendsto_nhds_unique h1 h2

/-- The contraction ball is invariant under the germ. -/
theorem mapsTo_ball_of_contraction {g : ℂ → ℂ} {c r : ℝ} (hc1 : c ≤ 1)
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖) :
    Set.MapsTo g (Metric.ball (0 : ℂ) r) (Metric.ball (0 : ℂ) r) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz ⊢
  have h1 := hgc z hz.le
  have h2 : c * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) hc1
  linarith

theorem mapsTo_ball_iterate {g : ℂ → ℂ} {c r : ℝ} (hc1 : c ≤ 1)
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖) (n : ℕ) :
    Set.MapsTo (g^[n]) (Metric.ball (0 : ℂ) r) (Metric.ball (0 : ℂ) r) := by
  induction n with
  | zero => simpa using Set.mapsTo_id _
  | succ n ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    exact mapsTo_ball_of_contraction hc1 hgc (ih hz)

theorem iterate_differentiableOn_ball {g : ℂ → ℂ} {c r : ℝ} (hc1 : c ≤ 1)
    (hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖) (n : ℕ) :
    DifferentiableOn ℂ (g^[n]) (Metric.ball (0 : ℂ) r) := by
  induction n with
  | zero => simpa using differentiableOn_id
  | succ n ih =>
    have hcomp : DifferentiableOn ℂ (g ∘ g^[n]) (Metric.ball (0 : ℂ) r) :=
      hgd.comp ih (mapsTo_ball_iterate hc1 hgc n)
    refine hcomp.congr fun z _ => ?_
    rw [Function.iterate_succ_apply']
    rfl

theorem koenigsApproxGerm_differentiableOn {g : ℂ → ℂ} {μ : ℂ} {c r : ℝ} (hc1 : c ≤ 1)
    (hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖) (n : ℕ) :
    DifferentiableOn ℂ (koenigsApproxGerm g μ n) (Metric.ball (0 : ℂ) r) :=
  (iterate_differentiableOn_ball hc1 hgd hgc n).div_const _

/-- **The Koenigs linearizer is holomorphic on the contraction ball.** -/
theorem koenigsGerm_differentiableOn {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖) (hr : 0 ≤ r)
    (hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r))
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖) :
    DifferentiableOn ℂ (koenigsGerm g μ) (Metric.ball (0 : ℂ) r) := by
  have hunif := koenigsApproxGerm_tendstoUniformlyOn hμ hK0 hc0 hc1 hq hr hquad hgc
  have hloc : TendstoLocallyUniformlyOn (fun n => koenigsApproxGerm g μ n) (koenigsGerm g μ)
      Filter.atTop (Metric.ball (0 : ℂ) r) :=
    (hunif.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  exact hloc.differentiableOn
    (Filter.Eventually.of_forall fun n => koenigsApproxGerm_differentiableOn hc1 hgd hgc n)
    Metric.isOpen_ball

theorem hasDerivAt_iterate_zero {g : ℂ → ℂ} {μ : ℂ}
    (hg0 : g 0 = 0) (hga : HasDerivAt g μ 0) (n : ℕ) :
    HasDerivAt (g^[n]) (μ ^ n) 0 := by
  induction n with
  | zero => simpa using hasDerivAt_id (0 : ℂ)
  | succ n ih =>
    have hfix : g^[n] 0 = 0 := Function.iterate_fixed hg0 n
    have hga' : HasDerivAt g μ (g^[n] 0) := by rw [hfix]; exact hga
    have hcomp : HasDerivAt (g ∘ g^[n]) (μ * μ ^ n) 0 := hga'.comp 0 ih
    have hfun : (g ∘ g^[n]) = g^[n + 1] := by
      funext z
      rw [Function.iterate_succ_apply']
      rfl
    rw [hfun] at hcomp
    have hpow : μ * μ ^ n = μ ^ (n + 1) := by ring
    rwa [hpow] at hcomp

theorem deriv_koenigsApproxGerm_zero {g : ℂ → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (hg0 : g 0 = 0) (hga : HasDerivAt g μ 0) (n : ℕ) :
    deriv (koenigsApproxGerm g μ n) 0 = 1 := by
  have h := (hasDerivAt_iterate_zero hg0 hga n).div_const (μ ^ n)
  have hd : deriv (koenigsApproxGerm g μ n) 0 = μ ^ n / μ ^ n := h.deriv
  rw [hd, div_self (pow_ne_zero n hμ)]

/-- **The Koenigs linearizer is normalized.**  Its derivative at the fixed point is one. -/
theorem deriv_koenigsGerm_zero {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖) (hr : 0 < r)
    (hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r))
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖)
    (hg0 : g 0 = 0) (hga : HasDerivAt g μ 0) :
    deriv (koenigsGerm g μ) 0 = 1 := by
  have hunif := koenigsApproxGerm_tendstoUniformlyOn hμ hK0 hc0 hc1 hq hr.le hquad hgc
  have hloc : TendstoLocallyUniformlyOn (fun n => koenigsApproxGerm g μ n) (koenigsGerm g μ)
      Filter.atTop (Metric.ball (0 : ℂ) r) :=
    (hunif.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hderiv := hloc.deriv
    (Filter.Eventually.of_forall fun n => koenigsApproxGerm_differentiableOn hc1 hgd hgc n)
    Metric.isOpen_ball
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_self]
    exact hr
  have h1 : Filter.Tendsto (fun n => deriv (koenigsApproxGerm g μ n) 0) Filter.atTop
      (nhds (deriv (koenigsGerm g μ) 0)) := hderiv.tendsto_at hmem
  have h2 : (fun n => deriv (koenigsApproxGerm g μ n) 0) = fun _ => (1 : ℂ) := by
    funext n
    exact deriv_koenigsApproxGerm_zero hμ hg0 hga n
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- **Uniqueness of the Koenigs linearizer.**  Any normalized solution of the linearizing equation
agrees with the constructed one near the fixed point. -/
theorem eq_koenigsGerm_of_linearizer {g κ : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖) (hr : 0 < r)
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖)
    (hκan : AnalyticAt ℂ κ 0) (hκ0 : κ 0 = 0) (hκd : deriv κ 0 = 1)
    (hκsemi : ∀ z : ℂ, ‖z‖ ≤ r → κ (g z) = μ * κ z) :
    ∃ s : ℝ, 0 < s ∧ ∀ z : ℂ, ‖z‖ ≤ s → κ z = koenigsGerm g μ z := by
  obtain ⟨C, r₂, hC, hr₂, hCbound⟩ := exists_quadratic_bound hκan hκ0 hκd
  have hμnorm : (0 : ℝ) < ‖μ‖ := norm_pos_iff.mpr hμ
  set q : ℝ := c ^ (2 : ℕ) / ‖μ‖ with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one hμnorm]
    exact hq
  refine ⟨min r r₂, lt_min hr hr₂, fun z hz => ?_⟩
  have hzr : ‖z‖ ≤ r := le_trans hz (min_le_left _ _)
  have hzr₂ : ‖z‖ ≤ r₂ := le_trans hz (min_le_right _ _)
  have horb : ∀ n : ℕ, ‖g^[n] z‖ ≤ c ^ n * ‖z‖ := fun n => orbit_norm_le hc0 hc1 hgc n hzr
  have horbr : ∀ n : ℕ, ‖g^[n] z‖ ≤ r := by
    intro n
    have hcn : c ^ n ≤ 1 := pow_le_one₀ hc0 hc1
    have hle : c ^ n * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) hcn
    linarith [horb n]
  have horbr₂ : ∀ n : ℕ, ‖g^[n] z‖ ≤ r₂ := by
    intro n
    have hcn : c ^ n ≤ 1 := pow_le_one₀ hc0 hc1
    have hle : c ^ n * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) hcn
    linarith [horb n]
  have hiter : ∀ n : ℕ, κ (g^[n] z) = μ ^ n * κ z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', hκsemi _ (horbr n), ih]
      ring
  have hbound : ∀ n : ℕ, dist (koenigsApproxGerm g μ n z) (κ z) ≤ (C * ‖z‖ ^ (2 : ℕ)) * q ^ n := by
    intro n
    have hμn : (μ : ℂ) ^ n ≠ 0 := pow_ne_zero n hμ
    have hdiff : koenigsApproxGerm g μ n z - κ z =
        (g^[n] z - κ (g^[n] z)) / μ ^ n := by
      rw [koenigsApproxGerm, hiter n]
      field_simp
    rw [dist_eq_norm, hdiff, norm_div, norm_pow]
    have hnum : ‖g^[n] z - κ (g^[n] z)‖ ≤ C * (c ^ n * ‖z‖) ^ (2 : ℕ) := by
      have h1 : ‖κ (g^[n] z) - 1 * g^[n] z‖ ≤ C * ‖g^[n] z‖ ^ (2 : ℕ) := hCbound _ (horbr₂ n)
      rw [one_mul] at h1
      have h2 : ‖g^[n] z - κ (g^[n] z)‖ = ‖κ (g^[n] z) - g^[n] z‖ := by
        rw [← norm_neg]
        congr 1
        ring
      rw [h2]
      refine le_trans h1 ?_
      refine mul_le_mul_of_nonneg_left ?_ hC.le
      have hnn : (0 : ℝ) ≤ ‖g^[n] z‖ := norm_nonneg _
      have hcz : (0 : ℝ) ≤ c ^ n * ‖z‖ := by positivity
      nlinarith [horb n]
    have hpos : (0 : ℝ) < ‖μ‖ ^ n := by positivity
    rw [div_le_iff₀ hpos]
    have hμne : (‖μ‖ : ℝ) ≠ 0 := ne_of_gt hμnorm
    have hrhs : C * ‖z‖ ^ (2 : ℕ) * q ^ n * ‖μ‖ ^ n = C * (c ^ n * ‖z‖) ^ (2 : ℕ) := by
      rw [hqdef, div_pow, ← pow_mul]
      field_simp
      ring
    rw [hrhs]
    exact hnum
  have hlim : Filter.Tendsto (fun n : ℕ => (C * ‖z‖ ^ (2 : ℕ)) * q ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa using this.const_mul (C * ‖z‖ ^ (2 : ℕ))
  have hconv : Filter.Tendsto (fun n => koenigsApproxGerm g μ n z) Filter.atTop (nhds (κ z)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) hbound hlim
  have hconv2 := koenigsApproxGerm_tendsto hμ hK0 hc0 hc1 hq hquad hgc hzr
  exact tendsto_nhds_unique hconv hconv2

end

end GaloisForLFunctions.HTGeometry
