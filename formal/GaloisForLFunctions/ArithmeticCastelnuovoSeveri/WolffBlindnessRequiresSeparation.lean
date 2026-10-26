import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeSeesEveryWellFoundedLevel

/-!
# Wolff blindness requires separation

The tower `g(· − kℓ)` of one fixed test sees an outer Frobenius eigenvalue `b = e^{ℓ(ρ−½)}` once,
for every vector `a` orthogonal to the tower, the class sums at `b` and at `1/b̄` vanish. Such a
vector has vanishing Laurent moments `Σ_τ q_τ β̄_τ^k = 0` (`k ∈ ℤ`, `q_τ = conj X_τ(g) a_τ`).
`OnePrimeSeesEveryWellFoundedLevel` extracts the classes from the moments by Cesàro means from the
top down, which needs the real parts above `Re ρ` to contain no increasing sequence; the symmetric
Wolff configurations of `OnePrimeAgainstTwoAndWolffTowerObstruction` show that a fixed test can be
blind without it. Here the classes are extracted by complex analysis instead.

* **Discrete Cauchy transforms.** `G(z) = Σ_τ q_τ/(1 − c_τ z)` is holomorphic off the closure of
  its poles `c_τ⁻¹` (`differentiableOn_discreteCauchy`). Vanishing moments `Σ q_τ c_τ^k = 0`,
  `k ≥ 0`, make it vanish near the origin (`discreteCauchy_eq_zero_of_moments`), hence on every
  connected open set through the origin that avoids the poles (`discreteCauchy_eqOn_zero`). If such
  a set contains a punctured disc around a pole `c₀⁻¹`, the residue there, the class sum
  `Σ_{c_τ = c₀} q_τ`, vanishes (`classSum_eq_zero_of_accessible`).
* **Towers** (`card_le_towerDefect_of_accessibleOff`). For the tower the poles are the reciprocal
  eigenvalues `β_τ⁻¹` of the zeros the test sees and their conjugates: the *active folded spectrum*
  (`activeFoldedSpectrum`). Every visible `b` with `b⁻¹` **accessible from the origin** off its
  closure (`AccessibleOff`) is seen, and finitely many such `b` by one window together. No order
  condition on the real parts enters.
* **Blindness is separation** (`not_accessibleOff_of_towerGram_psd`). If every window of the tower
  is positive, every visible `b⁻¹` is walled off from the origin by the closed folded spectrum: the
  Wolff mechanism needs the folded zeros to separate, not merely to accumulate in real part.
* **Countable folded spectra** (`card_le_towerDefect_of_countable`). If the closed folded spectrum
  meets the unit disc in a countable set, every visible `b` with `b⁻¹` isolated in it is seen. Real
  parts increasing to their supremum blind a fixed test only if their folded points fill a
  continuum around the origin.
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate Classical lp
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Discrete Cauchy transforms -/

section Cauchy

variable {T : Type*} {q c : T → ℂ}

/-- The discrete Cauchy transform `G(z) = Σ_τ q_τ/(1 − c_τ z)`. -/
def discreteCauchy (q c : T → ℂ) (z : ℂ) : ℂ := ∑' τ, q τ / (1 - c τ * z)

/-- The poles of `discreteCauchy q c`: the reciprocal nodes `c_τ⁻¹` of nonzero weight. -/
def cauchyPoles (q c : T → ℂ) : Set ℂ := {z | ∃ τ, q τ ≠ 0 ∧ z = (c τ)⁻¹}

/-- A node at distance `≥ r` from `z`, of modulus `≥ m`, gives a denominator `≥ m r`. -/
theorem norm_one_sub_mul_ge {m r : ℝ} {d z : ℂ} (hdm : m ≤ ‖d‖) (hm : 0 ≤ m) (hr0 : 0 ≤ r)
    (hr : r ≤ ‖d⁻¹ - z‖) (hd : d ≠ 0) : m * r ≤ ‖1 - d * z‖ := by
  have h : 1 - d * z = d * (d⁻¹ - z) := by rw [mul_sub, mul_inv_cancel₀ hd]
  rw [h, norm_mul]
  exact mul_le_mul hdm hr hr0 (hm.trans hdm)

/-- Distance to a far point drops by at most the distance moved. -/
theorem le_norm_sub_of_le {r : ℝ} {x z z₀ : ℂ} (hx : r ≤ ‖x - z₀‖) (hz : ‖z - z₀‖ < r / 2) :
    r / 2 ≤ ‖x - z‖ := by
  have h := norm_sub_norm_le (x - z₀) (z - z₀)
  rw [sub_sub_sub_cancel_right] at h
  linarith

/-- **The transform is holomorphic off the closed pole set.** -/
theorem differentiableOn_discreteCauchy (hq : Summable fun τ => ‖q τ‖) {m : ℝ} (hm : 0 < m)
    (hcm : ∀ τ, m ≤ ‖c τ‖) :
    DifferentiableOn ℂ (discreteCauchy q c) (closure (cauchyPoles q c))ᶜ := by
  intro z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl z₀ hz₀
  have hr2 : 0 < r / 2 := by positivity
  have hc0 : ∀ τ, c τ ≠ 0 := fun τ => norm_pos_iff.mp (hm.trans_le (hcm τ))
  have hden : ∀ τ, q τ ≠ 0 → ∀ z ∈ ball z₀ (r / 2), m * (r / 2) ≤ ‖1 - c τ * z‖ := by
    intro τ hqτ z hz
    have hpole : (c τ)⁻¹ ∉ ball z₀ r := fun h => hball h (subset_closure ⟨τ, hqτ, rfl⟩)
    rw [Metric.mem_ball, not_lt, dist_eq_norm] at hpole
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact norm_one_sub_mul_ge (hcm τ) hm.le hr2.le (le_norm_sub_of_le hpole hz) (hc0 τ)
  have hbound : ∀ τ, ∀ z ∈ ball z₀ (r / 2), ‖q τ / (1 - c τ * z)‖ ≤ ‖q τ‖ / (m * (r / 2)) := by
    intro τ z hz
    by_cases hqτ : q τ = 0
    · simp [hqτ]
    · rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (hden τ hqτ z hz)
  have hterm : ∀ τ, DifferentiableOn ℂ (fun z => q τ / (1 - c τ * z)) (ball z₀ (r / 2)) := by
    intro τ z hz
    by_cases hqτ : q τ = 0
    · simp only [hqτ, zero_div]
      exact differentiableWithinAt_const _
    · have hne : 1 - c τ * z ≠ 0 := fun h0 => by
        have h := hden τ hqτ z hz
        rw [h0, norm_zero] at h
        exact absurd h (not_le.mpr (by positivity))
      have hdz : DifferentiableAt ℂ (fun w => q τ / (1 - c τ * w)) z := by
        fun_prop (disch := exact hne)
      exact hdz.differentiableWithinAt
  have hd := Complex.differentiableOn_tsum_of_summable_norm (hq.div_const (m * (r / 2))) hterm
    isOpen_ball hbound
  exact ((hd z₀ (mem_ball_self hr2)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self hr2))).differentiableWithinAt

/-- **Vanishing moments make the transform vanish near the origin.** For `‖z‖ < 1/M` the transform
is the power series `Σ_k (Σ_τ q_τ c_τ^k) z^k`. -/
theorem discreteCauchy_eq_zero_of_moments (hq : Summable fun τ => ‖q τ‖) {M : ℝ} (hM : 0 < M)
    (hcM : ∀ τ, ‖c τ‖ ≤ M) (hmom : ∀ k : ℕ, ∑' τ, q τ * c τ ^ k = 0) {z : ℂ}
    (hz : ‖z‖ < M⁻¹) : discreteCauchy q c z = 0 := by
  have hr : M * ‖z‖ < 1 := by
    have h := mul_lt_mul_of_pos_left hz hM
    rwa [mul_inv_cancel₀ hM.ne'] at h
  have hr0 : 0 ≤ M * ‖z‖ := by positivity
  have hgeo : ∀ τ, ‖c τ * z‖ < 1 := fun τ => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hcM τ) (norm_nonneg _)) hr
  have hterm : ∀ τ, q τ / (1 - c τ * z) = ∑' k : ℕ, q τ * c τ ^ k * z ^ k := fun τ => by
    rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one (hgeo τ), ← tsum_mul_left]
    exact tsum_congr fun k => by rw [mul_pow, mul_assoc]
  have hsum : Summable (Function.uncurry fun (τ : T) (k : ℕ) => q τ * c τ ^ k * z ^ k) := by
    refine Summable.of_norm_bounded (hq.mul_of_nonneg (summable_geometric_of_lt_one hr0 hr)
      (fun _ => norm_nonneg _) (fun _ => by positivity)) fun p => ?_
    rcases p with ⟨τ, k⟩
    simp only [Function.uncurry_apply_pair, norm_mul, norm_pow]
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (hcM τ) (norm_nonneg _)) k) (norm_nonneg _)
  rw [discreteCauchy, tsum_congr hterm, ← hsum.tsum_comm]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  rw [tsum_mul_right, hmom k, zero_mul]

/-- **Identity theorem.** With vanishing moments the transform vanishes on every connected open
set through the origin that avoids the closed pole set. -/
theorem discreteCauchy_eqOn_zero (hq : Summable fun τ => ‖q τ‖) {m M : ℝ} (hm : 0 < m)
    (hM : 0 < M) (hcm : ∀ τ, m ≤ ‖c τ‖) (hcM : ∀ τ, ‖c τ‖ ≤ M)
    (hmom : ∀ k : ℕ, ∑' τ, q τ * c τ ^ k = 0) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hUK : ∀ z ∈ U, z ∉ closure (cauchyPoles q c)) :
    EqOn (discreteCauchy q c) 0 U := by
  have hd : DifferentiableOn ℂ (discreteCauchy q c) U :=
    (differentiableOn_discreteCauchy hq hm hcm).mono fun z hz => hUK z hz
  refine (hd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc h0 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hM)] with z hz
  exact discreteCauchy_eq_zero_of_moments hq hM hcM hmom (by simpa using hz)

/-- **The residue at an isolated pole.** If the transform vanishes on a punctured disc around
`c₀⁻¹` that avoids the other poles, the class sum `Σ_{c_τ = c₀} q_τ` vanishes: it is the residue
of `G` there, the rest of the sum being continuous at `c₀⁻¹`. -/
theorem classSum_eq_zero_of_punctured (hq : Summable fun τ => ‖q τ‖) {m : ℝ} (hm : 0 < m)
    (hcm : ∀ τ, m ≤ ‖c τ‖) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hpunct : ∀ z, ‖z - c₀⁻¹‖ < ε → z ≠ c₀⁻¹ →
      z ∉ closure (cauchyPoles q c) ∧ discreteCauchy q c z = 0) :
    ∑' τ, (if c τ = c₀ then q τ else 0) = 0 := by
  have hc0 : ∀ τ, c τ ≠ 0 := fun τ => norm_pos_iff.mp (hm.trans_le (hcm τ))
  -- the other poles keep distance `ε`
  have hfar : ∀ τ, q τ ≠ 0 → c τ ≠ c₀ → ε ≤ ‖(c τ)⁻¹ - c₀⁻¹‖ := by
    intro τ hqτ hne
    by_contra hlt
    exact (hpunct _ (not_le.mp hlt) fun h => hne (inv_injective h)).1
      (subset_closure ⟨τ, hqτ, rfl⟩)
  have hε2 : 0 < ε / 2 := by positivity
  have hden : ∀ τ, q τ ≠ 0 → c τ ≠ c₀ → ∀ z ∈ ball c₀⁻¹ (ε / 2),
      m * (ε / 2) ≤ ‖1 - c τ * z‖ := by
    intro τ hqτ hne z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact norm_one_sub_mul_ge (hcm τ) hm.le hε2.le (le_norm_sub_of_le (hfar τ hqτ hne) hz)
      (hc0 τ)
  have hRbound : ∀ τ, ∀ z ∈ ball c₀⁻¹ (ε / 2),
      ‖(if c τ = c₀ then 0 else q τ / (1 - c τ * z))‖ ≤ ‖q τ‖ / (m * (ε / 2)) := by
    intro τ z hz
    split_ifs with hcτ
    · rw [norm_zero]; positivity
    · by_cases hqτ : q τ = 0
      · simp [hqτ]
      · rw [norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (hden τ hqτ hcτ z hz)
  -- the regular part is continuous on the disc
  have hRcont : ContinuousOn (fun z => ∑' τ, (if c τ = c₀ then 0 else q τ / (1 - c τ * z)))
      (ball c₀⁻¹ (ε / 2)) := by
    refine continuousOn_tsum (fun τ => ?_) (hq.div_const _) hRbound
    by_cases hcτ : c τ = c₀
    · simp only [hcτ, if_true]
      exact continuousOn_const
    · simp only [hcτ, if_false]
      by_cases hqτ : q τ = 0
      · simp only [hqτ, zero_div]
        exact continuousOn_const
      · refine ContinuousOn.div continuousOn_const
          (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) fun z hz h0 => ?_
        have h := hden τ hqτ hcτ z hz
        rw [h0, norm_zero] at h
        exact absurd h (not_le.mpr (by positivity))
  set R : ℂ → ℂ := fun z => ∑' τ, (if c τ = c₀ then 0 else q τ / (1 - c τ * z))
  set Q₀ := ∑' τ, (if c τ = c₀ then q τ else 0)
  -- off the pole, `G = Q₀/(1 − c₀ z) + R`, so `Q₀ = −(1 − c₀ z) R(z)`
  have hkey : ∀ z ∈ ball c₀⁻¹ (ε / 2), z ≠ c₀⁻¹ → Q₀ = -((1 - c₀ * z) * R z) := by
    intro z hz hne
    have hzε : ‖z - c₀⁻¹‖ < ε := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    have hG := (hpunct z hzε hne).2
    have hs0 : Summable fun τ => (if c τ = c₀ then q τ else 0) :=
      Summable.of_norm_bounded hq fun τ => by split_ifs <;> simp
    have hs1 : Summable fun τ => (if c τ = c₀ then q τ else 0) / (1 - c₀ * z) :=
      hs0.div_const _
    have hs2 : Summable fun τ => (if c τ = c₀ then 0 else q τ / (1 - c τ * z)) :=
      Summable.of_norm_bounded (hq.div_const _) fun τ => hRbound τ z hz
    have hsplit : discreteCauchy q c z = Q₀ / (1 - c₀ * z) + R z := by
      show ∑' τ, q τ / (1 - c τ * z) = (∑' τ, (if c τ = c₀ then q τ else 0)) / (1 - c₀ * z) +
        ∑' τ, (if c τ = c₀ then 0 else q τ / (1 - c τ * z))
      rw [← tsum_div_const, ← hs1.tsum_add hs2]
      refine tsum_congr fun τ => ?_
      split_ifs with hcτ
      · rw [hcτ, add_zero]
      · rw [zero_div, zero_add]
    have hd : 1 - c₀ * z ≠ 0 := fun h =>
      hne (eq_inv_of_mul_eq_one_right (by linear_combination -h))
    rw [hsplit] at hG
    have h1 : Q₀ = Q₀ / (1 - c₀ * z) * (1 - c₀ * z) := (div_mul_cancel₀ _ hd).symm
    rw [h1]
    linear_combination (1 - c₀ * z) * hG
  have hRat : ContinuousAt R c₀⁻¹ :=
    hRcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε2))
  have htend : Tendsto (fun z => -((1 - c₀ * z) * R z)) (𝓝[≠] c₀⁻¹)
      (𝓝 (-((1 - c₀ * c₀⁻¹) * R c₀⁻¹))) :=
    (((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).mul hRat).neg).tendsto
      |>.mono_left nhdsWithin_le_nhds
  rw [mul_inv_cancel₀ hc₀, sub_self, zero_mul, neg_zero] at htend
  have hev : (fun _ : ℂ => Q₀) =ᶠ[𝓝[≠] c₀⁻¹] fun z => -((1 - c₀ * z) * R z) := by
    filter_upwards [inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds (mem_ball_self hε2))] with z hz
    exact hkey z hz.2 hz.1
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) htend

/-- **Class extraction at an accessible pole.** If the moments `Σ q_τ c_τ^k`, `k ≥ 0`, vanish and a
connected open set through the origin avoiding the closed pole set contains a punctured disc around
`c₀⁻¹`, the class sum at `c₀` vanishes. -/
theorem classSum_eq_zero_of_accessible (hq : Summable fun τ => ‖q τ‖) {m M : ℝ} (hm : 0 < m)
    (hM : 0 < M) (hcm : ∀ τ, m ≤ ‖c τ‖) (hcM : ∀ τ, ‖c τ‖ ≤ M)
    (hmom : ∀ k : ℕ, ∑' τ, q τ * c τ ^ k = 0) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (h0 : (0 : ℂ) ∈ U)
    (hUK : ∀ z ∈ U, z ∉ closure (cauchyPoles q c)) {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ z, ‖z - c₀⁻¹‖ < ε → z ≠ c₀⁻¹ → z ∈ U) :
    ∑' τ, (if c τ = c₀ then q τ else 0) = 0 :=
  classSum_eq_zero_of_punctured hq hm hcm hc₀ hε fun z hz hne =>
    ⟨hUK z (hball z hz hne),
      discreteCauchy_eqOn_zero hq hm hM hcm hcM hmom hUo hUc h0 hUK (hball z hz hne)⟩

end Cauchy

/-! ### 2. Accessibility -/

/-- `w` is **accessible from the origin off** `F`: a connected open set avoiding `F` contains the
origin and a punctured disc around `w`. -/
def AccessibleOff (F : Set ℂ) (w : ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ IsPreconnected U ∧ (0 : ℂ) ∈ U ∧ (∀ z ∈ U, z ∉ F) ∧
    ∃ ε > 0, ∀ z, ‖z - w‖ < ε → z ≠ w → z ∈ U

theorem AccessibleOff.mono {F F' : Set ℂ} {w : ℂ} (h : AccessibleOff F w) (hF : F' ⊆ F) :
    AccessibleOff F' w := by
  obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball⟩ := h
  exact ⟨U, hUo, hUc, h0, fun z hz hzF => hUF z hz (hF hzF), ε, hε, hball⟩

/-- Accessibility is invariant under complex conjugation. -/
theorem AccessibleOff.conj {F : Set ℂ} {w : ℂ} (h : AccessibleOff F w) :
    AccessibleOff ((starRingEnd ℂ) ⁻¹' F) (conj w) := by
  obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball⟩ := h
  have himg : (starRingEnd ℂ) ⁻¹' U = (starRingEnd ℂ) '' U := by
    ext z
    constructor
    · intro hz
      exact ⟨conj z, hz, Complex.conj_conj z⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  refine ⟨(starRingEnd ℂ) ⁻¹' U, hUo.preimage Complex.continuous_conj, ?_, by simpa using h0,
    fun z hz hzF => hUF _ hz hzF, ε, hε, fun z hz hne => hball _ ?_ ?_⟩
  · rw [himg]
    exact hUc.image _ Complex.continuous_conj.continuousOn
  · rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
    exact hz
  · intro h'
    apply hne
    rw [← h', Complex.conj_conj]

/-- **Countable obstacles.** If a closed set `F` missing the origin meets the unit disc in a
countable set, every point of the disc isolated from `F` is accessible off `F`: the disc minus a
countable set is path-connected. -/
theorem accessibleOff_of_countable {F : Set ℂ} (hFc : IsClosed F)
    (hcount : (F ∩ ball (0 : ℂ) 1).Countable) (h0 : (0 : ℂ) ∉ F) {w : ℂ} (hw : ‖w‖ < 1)
    {ε : ℝ} (hε : 0 < ε) (hiso : ∀ z ∈ F, ‖z - w‖ < ε → z = w) : AccessibleOff F w := by
  set e : ℂ ≃ₜ ball (0 : ℂ) 1 := Homeomorph.unitBall
  set f : ℂ → ℂ := fun x => (e x : ℂ)
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hfinj : Function.Injective f := fun x y h => e.injective (Subtype.ext h)
  have hsub : f ⁻¹' F ⊆ f ⁻¹' (F ∩ ball (0 : ℂ) 1) := fun x hx =>
    show f x ∈ F ∩ ball (0 : ℂ) 1 from ⟨hx, (e x).2⟩
  have hA : (f ⁻¹' F).Countable := (hcount.preimage hfinj).mono hsub
  have hpc : IsPathConnected (f '' (f ⁻¹' F)ᶜ) :=
    (hA.isPathConnected_compl_of_one_lt_rank
      (by simp only [rank_real_complex, Nat.one_lt_ofNat])).image hf
  have himg : f '' (f ⁻¹' F)ᶜ = ball (0 : ℂ) 1 \ F := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(e x).2, hx⟩
    · rintro ⟨hz, hzF⟩
      refine ⟨e.symm ⟨z, hz⟩, ?_, by simp [f]⟩
      simpa [f] using hzF
  have h0U : (0 : ℂ) ∈ ball (0 : ℂ) 1 \ F := ⟨by simp, h0⟩
  refine ⟨ball (0 : ℂ) 1 \ F, isOpen_ball.sdiff hFc, ?_, h0U, fun z hz => hz.2,
    min ε (1 - ‖w‖), lt_min hε (by linarith), fun z hz hne => ⟨?_, fun hzF => hne ?_⟩⟩
  · rw [← himg]
    exact hpc.isConnected.isPreconnected
  · rw [mem_ball_zero_iff]
    calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ < (1 - ‖w‖) + ‖w‖ := by linarith [hz.trans_le (min_le_right _ _)]
      _ = 1 := by ring
  · exact hiso z hzF (hz.trans_le (min_le_left _ _))

/-! ### 3. Towers -/

/-- The **active folded spectrum** of `g` at scale `ℓ`: the reciprocal eigenvalues `e^{−ℓ(τ−½)}`
of the zeros `τ` at which `ĝ` does not vanish at `γ_τ` or at `γ̄_τ`. -/
def activeFoldedSpectrum (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) : Set ℂ :=
  {w | ∃ τ ∈ Z.carrier, (paperFT g (gammaOf τ) ≠ 0 ∨ paperFT g (conj (gammaOf τ)) ≠ 0) ∧
    w = (frobEig ℓ τ)⁻¹}

theorem exp_neg_half_le_norm_conj_frobEig (Z : ZeroConfig) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (τ : Z.carrier) : Real.exp (-(ℓ / 2)) ≤ ‖conj (frobEig ℓ τ)‖ := by
  rw [Complex.norm_conj, norm_frobEig, Real.exp_le_exp]
  have := (Z.strip _ τ.2).1
  nlinarith

/-- **Tower class extraction at accessible eigenvalues.** If `b⁻¹` is accessible from the origin
off the closed active folded spectrum, every vector orthogonal to the tower has zero class sums at
`b` and at `1/b̄`. -/
theorem classSum_eq_zero_of_accessibleOff (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℂ} (hb : b ≠ 0)
    (hacc : AccessibleOff (closure (activeFoldedSpectrum Z g ℓ)) b⁻¹)
    (a : ℓ²(Z.carrier, ℂ)) (ha : ∀ k : ℤ, inner ℂ (towerVec Z hZ hg hgc ℓ k) a = 0) :
    (∑' τ : Z.carrier, (if frobEig ℓ τ = b then conj (zeroCoord Z g τ) * a τ else 0)) = 0 ∧
      ∑' τ : Z.carrier, (if frobEig ℓ τ = reflEig b then
        conj (zeroCoord Z g τ) * a τ else 0) = 0 := by
  set q : Z.carrier → ℂ := fun τ => conj (zeroCoord Z g τ) * a τ
  have hq : Summable fun τ => ‖q τ‖ := summable_conj_zeroCoord_mul Z hZ hg hgc a
  have hmom := tsum_mul_conj_frobEig_zpow_eq_zero Z hZ hg hgc ℓ a ha
  have hm : 0 < Real.exp (-(ℓ / 2)) := Real.exp_pos _
  have hM : 0 < Real.exp (ℓ / 2) := Real.exp_pos _
  -- a node of nonzero weight is a zero the test sees
  have hseen : ∀ τ : Z.carrier, q τ ≠ 0 → paperFT g (gammaOf τ) ≠ 0 :=
    fun τ h hz => h (by simp [q, zeroCoord, hz])
  set F := activeFoldedSpectrum Z g ℓ
  constructor
  · -- the outer class: nodes `β̄_τ`, poles `conj β_τ⁻¹`
    have hpoles : closure (cauchyPoles q fun τ : Z.carrier => conj (frobEig ℓ τ)) ⊆
        (starRingEnd ℂ) ⁻¹' closure F := by
      refine (closure_mono ?_).trans (Complex.continuous_conj.closure_preimage_subset F)
      rintro z ⟨τ, hqτ, rfl⟩
      exact ⟨τ, τ.2, Or.inl (hseen τ hqτ), by rw [map_inv₀, Complex.conj_conj]⟩
    obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball⟩ := (hacc.conj).mono hpoles
    have h := classSum_eq_zero_of_accessible hq hm hM
      (exp_neg_half_le_norm_conj_frobEig Z ℓ hℓ) (norm_conj_frobEig_le Z hℓ)
      (fun n => (tsum_congr fun τ => by rw [zpow_natCast]).trans (hmom n))
      ((map_ne_zero (starRingEnd ℂ)).mpr hb) hUo hUc h0 hUF hε
      (fun z hz hne => hball z (by rw [map_inv₀]; exact hz) (by rw [map_inv₀]; exact hne))
    simpa only [(starRingEnd ℂ).injective.eq_iff] using h
  · -- the reflected class: nodes `β̄_τ⁻¹`, poles `β̄_τ = (β_{1−τ̄})⁻¹`
    have e : ∀ β : ℂ, (conj β)⁻¹ = b ↔ β = reflEig b := fun β => by
      constructor
      · intro h; rw [reflEig, ← h, map_inv₀, Complex.conj_conj, inv_inv]
      · intro h; rw [h, reflEig, map_inv₀, Complex.conj_conj, inv_inv]
    have hpoles : closure (cauchyPoles q fun τ : Z.carrier => (conj (frobEig ℓ τ))⁻¹) ⊆
        closure F := by
      refine closure_mono ?_
      rintro z ⟨τ, hqτ, rfl⟩
      refine ⟨reflect (τ : ℂ), Z.reflect_mem _ τ.2, Or.inr ?_, ?_⟩
      · rw [gammaOf_reflect, Complex.conj_conj]
        exact hseen τ hqτ
      · rw [inv_inv, frobEig_reflect, inv_inv]
    obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball⟩ := hacc.mono hpoles
    have hlow : ∀ τ : Z.carrier, Real.exp (-(ℓ / 2)) ≤ ‖(conj (frobEig ℓ τ))⁻¹‖ := fun τ => by
      rw [norm_inv, Real.exp_neg]
      exact inv_anti₀ (norm_pos_iff.mpr ((map_ne_zero _).mpr (frobEig_ne_zero ℓ τ)))
        (norm_conj_frobEig_le Z hℓ τ)
    have h := classSum_eq_zero_of_accessible hq hm hM hlow (norm_inv_conj_frobEig_le Z hℓ)
      (fun n => (tsum_congr fun τ => by rw [zpow_neg, zpow_natCast, inv_pow]).trans
        (hmom (-(n : ℤ)))) hb hUo hUc h0 hUF hε hball
    simpa only [e] using h

/-- **Accessible eigenvalues are seen together.** Finitely many visible outer eigenvalues whose
reciprocals are accessible from the origin off the closed active folded spectrum are seen by one
window of the tower of `g`. -/
theorem card_le_towerDefect_of_accessibleOff (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (O : Finset ℂ) (hO : ∀ b ∈ O, b ∈ visibleSet Z g ℓ)
    (hacc : ∀ b ∈ O, AccessibleOff (closure (activeFoldedSpectrum Z g ℓ)) b⁻¹) :
    ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) :=
  exists_towerGram_negIndex_ge_of_closure Z hZ hg hgc hℓ O hO fun b hb => by
    obtain ⟨⟨ρ, -, rfl⟩, -⟩ := hO b hb
    exact eigTarget_mem_closure_of_classSum Z hZ hg hgc _ fun a ha =>
      classSum_eq_zero_of_accessibleOff Z hZ hg hgc hℓ (frobEig_ne_zero ℓ ρ) (hacc _ hb) a ha

/-- **Wolff blindness requires separation.** If every window of the tower of `g` is positive, no
visible outer eigenvalue `b` has `b⁻¹` accessible from the origin off the closed active folded
spectrum: the folded zeros must wall `b⁻¹` off from the origin. -/
theorem not_accessibleOff_of_towerGram_psd (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hpsd : ∀ K : Finset ℤ, hermNegIndex (towerGram Z g ℓ K) = 0) {b : ℂ}
    (hb : b ∈ visibleSet Z g ℓ) : ¬ AccessibleOff (closure (activeFoldedSpectrum Z g ℓ)) b⁻¹ :=
  fun hacc => by
    obtain ⟨K, hK⟩ := card_le_towerDefect_of_accessibleOff Z hZ hg hgc hℓ {b}
      (by simpa using hb) (by simpa using hacc)
    rw [hpsd K] at hK
    simp at hK

/-- **Countable folded spectra do not blind a fixed test.** If the closed active folded spectrum
meets the unit disc in a countable set, finitely many visible outer eigenvalues whose reciprocals
are isolated points of it are seen by one window of the tower of `g`. This covers real parts
increasing to their supremum whose folded points accumulate at countably many points, where the
top-down extraction does not apply. -/
theorem card_le_towerDefect_of_countable (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcount : (closure (activeFoldedSpectrum Z g ℓ) ∩ ball (0 : ℂ) 1).Countable)
    (O : Finset ℂ) (hO : ∀ b ∈ O, b ∈ visibleSet Z g ℓ)
    (hiso : ∀ b ∈ O, ∃ ε > 0, ∀ z ∈ closure (activeFoldedSpectrum Z g ℓ), ‖z - b⁻¹‖ < ε →
      z = b⁻¹) :
    ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) := by
  -- the folded spectrum stays at modulus `≥ e^{−ℓ/2}`
  have hlow : closure (activeFoldedSpectrum Z g ℓ) ⊆ {z : ℂ | Real.exp (-(ℓ / 2)) ≤ ‖z‖} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    rintro z ⟨τ, hτ, -, rfl⟩
    show Real.exp (-(ℓ / 2)) ≤ ‖(frobEig ℓ τ)⁻¹‖
    rw [norm_inv, norm_frobEig, ← Real.exp_neg, Real.exp_le_exp]
    have := (Z.strip _ hτ).2
    nlinarith
  refine card_le_towerDefect_of_accessibleOff Z hZ hg hgc hℓ O hO fun b hb => ?_
  obtain ⟨ε, hε, hisoε⟩ := hiso b hb
  obtain ⟨⟨ρ, hρ, rfl⟩, -⟩ := hO b hb
  refine accessibleOff_of_countable isClosed_closure hcount (fun h0 => ?_) ?_ hε hisoε
  · have := hlow h0
    simp only [Set.mem_setOf_eq, norm_zero] at this
    exact absurd this (not_le.mpr (Real.exp_pos _))
  · rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ ((one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
