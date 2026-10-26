import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneTestCarriesTheDefectOfZetaAtEachPrime
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime

/-!
# One Lefschetz sequence grows at the zero width

Over `𝔽_q` the Lefschetz numbers `N_m − q^m − 1 = −Σ_i α_i^m` grow like `max_i |α_i|^m`, and Weil
bounds them by the Castelnuovo–Severi inequality on the two-dimensional spans `⟨Δ, Γ_m⟩`. Over `ℤ`
the Lefschetz sequence of a test `g` at scale `ℓ = log p` is the moment sequence of its tower,

`c_m = W(T_{p^m} g, g) = Σ_τ X_τ conj X_{1−τ̄} β_τ^m`,  `β_τ = e^{ℓ(τ − ½)}`  (`towerMoment`),

and the two-element windows `{g, T_{p^m} g}` are Weil's spans.

* **Upper bound** (`exists_norm_towerMoment_le`). For every test `c_m = O(R^m)` once `R ≥ 1`
  dominates every outer eigenvalue `|β_ρ|`.
* **Growth extraction** (`classSum_eq_zero_of_growth`). If the moments of
  `G(z) = Σ_τ q_τ/(1 − c_τ z)` are `O(R^m)`, the moment power series continues `G` from the origin
  to the disc `|z| < 1/R`, so the residue at a pole `c₀⁻¹` accessible inside that disc, the class
  sum at `c₀`, vanishes.
* **Towers** (`not_towerMoment_isBigO_of_isolated`). A visible eigenvalue `b` whose reciprocal is
  isolated in a countable set containing the closed active folded spectrum near the origin forces
  `c_m ≠ O(R^m)` for every `R < |b|`.
* **One test reaches the top** (`deepSparse_exists_test_lefschetz_growth`). For a deep-sparse
  configuration one test has `c_m = O(R^m)`, `R ≥ 1`, iff `R ≥ |β_ρ|` for every right zero `ρ`.
  An attained top is kept alone among the deep zeros; otherwise the test keeps a sequence of zeros
  whose real parts increase to the top and whose folded points converge.
* **For `ζ`** (`zeta_lefschetz_growth_law`, `zeta_riemannHypothesis_iff_lefschetz_minors`). At every
  prime one test has `c_m = O(R^m)`, `R ≥ 1`, iff `R ≥ p^w`, `w = sup |Re ρ − ½|` the zero width:
  a bound `c_m = O(p^{θm})` is the zero-free strip `|Re ρ − ½| ≤ θ`. RH holds iff the two-element
  windows satisfy Weil's inequality `|c_m| ≤ c_0` for every `m`.
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  zetaZeroWidth abs_re_sub_half_le_zetaZeroWidth)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Growth extraction for discrete Cauchy transforms -/

section Growth

variable {T : Type*} {q c : T → ℂ}

/-- **Near the origin the transform is the moment power series:**
`Σ_τ q_τ/(1 − c_τ z) = Σ_k (Σ_τ q_τ c_τ^k) z^k` for `‖z‖ < 1/M`. -/
theorem discreteCauchy_eq_tsum_moments (hq : Summable fun τ => ‖q τ‖) {M : ℝ} (hM : 0 < M)
    (hcM : ∀ τ, ‖c τ‖ ≤ M) {z : ℂ} (hz : ‖z‖ < M⁻¹) :
    discreteCauchy q c z = ∑' k : ℕ, (∑' τ, q τ * c τ ^ k) * z ^ k := by
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
  exact tsum_congr fun k => tsum_mul_right

/-- Coefficients `|a_k| ≤ C R^k` give a power series holomorphic on `|z| < r'` when `R r' < 1`. -/
theorem differentiableOn_tsum_mul_pow {a : ℕ → ℂ} {C R : ℝ} (ha : ∀ k, ‖a k‖ ≤ C * R ^ k)
    (hR : 0 ≤ R) {r' : ℝ} (hr' : 0 ≤ r') (hRr : R * r' < 1) :
    DifferentiableOn ℂ (fun z => ∑' k : ℕ, a k * z ^ k) (ball (0 : ℂ) r') := by
  refine Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one (by positivity) hRr).mul_left C)
    (fun k => ((differentiable_const (a k)).mul (differentiable_pow k)).differentiableOn)
    isOpen_ball fun k z hz => ?_
  rw [norm_mul, norm_pow, mul_pow, ← mul_assoc]
  have hz' : ‖z‖ ≤ r' := (mem_ball_zero_iff.mp hz).le
  exact mul_le_mul (ha k) (pow_le_pow_left₀ (norm_nonneg _) hz' k) (by positivity)
    ((norm_nonneg _).trans (ha k))

/-- **The residue against a continuous function.** If the transform agrees, on a punctured disc
around `c₀⁻¹` avoiding the other poles, with a function continuous at `c₀⁻¹`, the class sum
`Σ_{c_τ = c₀} q_τ` vanishes. -/
theorem classSum_eq_zero_of_punctured_eq (hq : Summable fun τ => ‖q τ‖) {m : ℝ} (hm : 0 < m)
    (hcm : ∀ τ, m ≤ ‖c τ‖) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) {H : ℂ → ℂ}
    (hH : ContinuousAt H c₀⁻¹)
    (hpunct : ∀ z, ‖z - c₀⁻¹‖ < ε → z ≠ c₀⁻¹ →
      z ∉ closure (cauchyPoles q c) ∧ discreteCauchy q c z = H z) :
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
  -- off the pole, `G = Q₀/(1 − c₀ z) + R = H`, so `Q₀ = (1 − c₀ z)(H(z) − R(z))`
  have hkey : ∀ z ∈ ball c₀⁻¹ (ε / 2), z ≠ c₀⁻¹ → Q₀ = (1 - c₀ * z) * (H z - R z) := by
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
  have htend : Tendsto (fun z => (1 - c₀ * z) * (H z - R z)) (𝓝[≠] c₀⁻¹)
      (𝓝 ((1 - c₀ * c₀⁻¹) * (H c₀⁻¹ - R c₀⁻¹))) :=
    ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).mul (hH.sub hRat)).tendsto
      |>.mono_left nhdsWithin_le_nhds
  rw [mul_inv_cancel₀ hc₀, sub_self, zero_mul] at htend
  have hev : (fun _ : ℂ => Q₀) =ᶠ[𝓝[≠] c₀⁻¹] fun z => (1 - c₀ * z) * (H z - R z) := by
    filter_upwards [inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds (mem_ball_self hε2))] with z hz
    exact hkey z hz.2 hz.1
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) htend

/-- **Growth extraction.** If the moments `Σ_τ q_τ c_τ^k` are `O(R^k)` and a connected open set
through the origin inside `|z| < r`, `R r < 1`, avoiding the closed pole set, contains a punctured
disc around `c₀⁻¹`, the class sum at `c₀` vanishes: on that set the transform is the moment power
series, which is continuous at `c₀⁻¹`. -/
theorem classSum_eq_zero_of_growth (hq : Summable fun τ => ‖q τ‖) {m M : ℝ} (hm : 0 < m)
    (hM : 0 < M) (hcm : ∀ τ, m ≤ ‖c τ‖) (hcM : ∀ τ, ‖c τ‖ ≤ M) {C R : ℝ} (hR : 0 < R)
    (hgrowth : ∀ k : ℕ, ‖∑' τ, q τ * c τ ^ k‖ ≤ C * R ^ k) {r : ℝ} (hRr : R * r < 1)
    {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (h0 : (0 : ℂ) ∈ U) (hUr : U ⊆ ball (0 : ℂ) r)
    (hUK : ∀ z ∈ U, z ∉ closure (cauchyPoles q c)) {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ z, ‖z - c₀⁻¹‖ < ε → z ≠ c₀⁻¹ → z ∈ U) :
    ∑' τ, (if c τ = c₀ then q τ else 0) = 0 := by
  set P : ℂ → ℂ := fun z => ∑' k : ℕ, (∑' τ, q τ * c τ ^ k) * z ^ k with hP
  have hr0 : 0 < r := by simpa using hUr h0
  have hrR : r < R⁻¹ := by
    rw [← one_div, lt_div_iff₀ hR, mul_comm]
    exact hRr
  set r' : ℝ := (r + R⁻¹) / 2 with hr'
  have hrr' : r < r' := by rw [hr']; linarith
  have hRr' : R * r' < 1 := by
    have h : R * r' = (R * r + 1) / 2 := by
      rw [hr', mul_div_assoc', mul_add, mul_inv_cancel₀ hR.ne']
    rw [h]
    linarith
  have hPd : DifferentiableOn ℂ P (ball (0 : ℂ) r') :=
    differentiableOn_tsum_mul_pow hgrowth hR.le (by linarith) hRr'
  have hGd : DifferentiableOn ℂ (discreteCauchy q c) U :=
    (differentiableOn_discreteCauchy hq hm hcm).mono fun z hz => hUK z hz
  have hUr' : U ⊆ ball (0 : ℂ) r' := hUr.trans (ball_subset_ball hrr'.le)
  have heq : EqOn (discreteCauchy q c) P U := by
    refine (hGd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
      ((hPd.mono hUr').analyticOnNhd hUo) hUc h0 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hM)] with z hz
    exact discreteCauchy_eq_tsum_moments hq hM hcM (by simpa using hz)
  -- the pole lies in the disc of convergence
  have hc₀r' : c₀⁻¹ ∈ ball (0 : ℂ) r' := by
    set t : ℝ := min ε (r' - r) / 2 with ht
    have ht0 : 0 < t := by rw [ht]; exact half_pos (lt_min hε (by linarith))
    have htε : t < ε := by rw [ht]; linarith [min_le_left ε (r' - r)]
    have htr : t < r' - r := by rw [ht]; linarith [min_le_right ε (r' - r)]
    have hz : c₀⁻¹ + (t : ℂ) ∈ U := hball _ (by simpa [abs_of_pos ht0] using htε)
      (by simpa using ht0.ne')
    have hzr := mem_ball_zero_iff.mp (hUr hz)
    rw [mem_ball_zero_iff]
    calc ‖c₀⁻¹‖ = ‖(c₀⁻¹ + (t : ℂ)) - (t : ℂ)‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖c₀⁻¹ + (t : ℂ)‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
      _ < r' := by
        rw [Complex.norm_real, Real.norm_of_nonneg ht0.le]
        linarith
  have hH : ContinuousAt P c₀⁻¹ := hPd.continuousOn.continuousAt (isOpen_ball.mem_nhds hc₀r')
  exact classSum_eq_zero_of_punctured_eq hq hm hcm hc₀ hε hH fun z hz hne =>
    ⟨hUK z (hball z hz hne), heq (hball z hz hne)⟩

end Growth

/-! ### 2. The Lefschetz sequence of a tower -/

/-- The nonnegative tower moments are the moments of the weights `X_τ conj X_{1−τ̄}` at the nodes
`β_τ`. -/
theorem towerMoment_natCast (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (k : ℕ) :
    towerMoment Z g ℓ k = ∑' τ : Z.carrier,
      zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) * frobEig ℓ τ ^ k := by
  simp only [towerMoment, zpow_natCast]

/-- **Upper bound.** If `R ≥ 1` dominates every outer eigenvalue, the Lefschetz sequence of every
test is `O(R^m)`. -/
theorem exists_norm_towerMoment_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} (hR : 1 ≤ R)
    (hdom : ∀ ρ ∈ rightZeros Z, ‖frobEig ℓ ρ‖ ≤ R) :
    ∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k := by
  set w : Z.carrier → ℂ := fun τ => zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ))
  have hw : Summable fun τ => ‖w τ‖ := summable_zeroCoord_mul_reflect Z hZ hg hgc
  have hβ : ∀ τ : Z.carrier, ‖frobEig ℓ τ‖ ≤ R := fun τ => by
    by_cases hτ : 1 / 2 < (τ : ℂ).re
    · exact hdom τ ⟨τ.2, hτ⟩
    · rw [norm_frobEig]
      exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hℓ.le
        (by linarith [not_lt.mp hτ]))).trans hR
  have hterm : ∀ k : ℕ, ∀ τ, ‖w τ * frobEig ℓ τ ^ k‖ ≤ ‖w τ‖ * R ^ k := fun k τ => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hβ τ) k) (norm_nonneg _)
  refine ⟨∑' τ, ‖w τ‖, fun k => ?_⟩
  have hs : Summable fun τ => ‖w τ * frobEig ℓ τ ^ k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm k) (hw.mul_right _)
  rw [towerMoment_natCast, ← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (hterm k) (hw.mul_right _))

/-- **Weil's inequality on the line.** If no zero lies right of the line, every test has
`|c_m| ≤ c_0` for every `m ≥ 0`. -/
theorem norm_towerMoment_le_of_rightZeros_eq_empty (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ)
    (hR : rightZeros Z = ∅) (k : ℕ) :
    ‖towerMoment Z g ℓ k‖ ≤ (towerMoment Z g ℓ 0).re := by
  have hon : ∀ τ : Z.carrier, (τ : ℂ).re = 1 / 2 := fun τ => by
    rcases lt_trichotomy (τ : ℂ).re (1 / 2) with h | h | h
    · have hr : reflect (τ : ℂ) ∈ rightZeros Z :=
        ⟨Z.reflect_mem _ τ.2, by rw [re_reflect]; linarith⟩
      rw [hR] at hr
      exact absurd hr (Set.notMem_empty _)
    · exact h
    · have hr : (τ : ℂ) ∈ rightZeros Z := ⟨τ.2, h⟩
      rw [hR] at hr
      exact absurd hr (Set.notMem_empty _)
  set w : Z.carrier → ℂ := fun τ => zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ))
  have hws : Summable fun τ => ‖w τ‖ := summable_zeroCoord_mul_reflect Z hZ hg hgc
  have hw : ∀ τ, w τ = (Complex.normSq (zeroCoord Z g τ) : ℂ) := fun τ => by
    show zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) = _
    rw [reflectCarrier_eq_self (hon τ), Complex.mul_conj]
  have hnw : ∀ τ, ‖w τ‖ = Complex.normSq (zeroCoord Z g τ) := fun τ => by
    rw [hw τ, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
  have h0 : (towerMoment Z g ℓ 0).re = ∑' τ, ‖w τ‖ := by
    have e : towerMoment Z g ℓ 0 = ∑' τ, (Complex.normSq (zeroCoord Z g τ) : ℂ) := by
      rw [towerMoment]
      exact tsum_congr fun τ => by rw [zpow_zero, mul_one]; exact hw τ
    rw [e, Complex.re_tsum (hws.of_norm.congr hw)]
    exact tsum_congr fun τ => by rw [Complex.ofReal_re, hnw τ]
  have hterm : ∀ τ, ‖w τ * frobEig ℓ τ ^ k‖ = ‖w τ‖ := fun τ => by
    rw [norm_mul, norm_pow, norm_frobEig_eq_one (hon τ), one_pow, mul_one]
  have hs : Summable fun τ => ‖w τ * frobEig ℓ τ ^ k‖ := by simpa only [hterm] using hws
  rw [towerMoment_natCast, h0]
  exact (norm_tsum_le_tsum_norm hs).trans (le_of_eq (tsum_congr hterm))

/-- **A visible accessible eigenvalue bounds the growth from below.** If `b` is visible and `b⁻¹`
is accessible from the origin inside `|z| < r` off the closed active folded spectrum, the Lefschetz
sequence of `g` is not `O(R^m)` for any `0 < R < 1/r`. -/
theorem not_towerMoment_isBigO_of_accessible (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℂ}
    (hb : b ∈ visibleSet Z g ℓ) {r : ℝ}
    (hacc : AccessibleOff (closure (activeFoldedSpectrum Z g ℓ) ∪ (ball (0 : ℂ) r)ᶜ) b⁻¹)
    {R : ℝ} (hR : 0 < R) (hRr : R * r < 1) :
    ¬ ∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k := by
  rintro ⟨C, hC⟩
  obtain ⟨⟨ρ, -, rfl⟩, hvis⟩ := hb
  obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball⟩ := hacc
  set q : Z.carrier → ℂ := fun τ => zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ))
  have hq : Summable fun τ => ‖q τ‖ := summable_zeroCoord_mul_reflect Z hZ hg hgc
  have hpoles : closure (cauchyPoles q fun τ : Z.carrier => frobEig ℓ τ) ⊆
      closure (activeFoldedSpectrum Z g ℓ) := by
    refine closure_mono ?_
    rintro z ⟨τ, hqτ, rfl⟩
    refine ⟨τ, τ.2, Or.inl fun hz => hqτ ?_, rfl⟩
    simp [q, zeroCoord, hz]
  have hUr : U ⊆ ball (0 : ℂ) r := fun z hz => by
    by_contra h
    exact hUF z hz (Or.inr h)
  have h := classSum_eq_zero_of_growth hq (Real.exp_pos (-(ℓ / 2))) (Real.exp_pos (ℓ / 2))
    (c := fun τ : Z.carrier => frobEig ℓ τ)
    (fun τ => by simpa only [Complex.norm_conj] using exp_neg_half_le_norm_conj_frobEig Z ℓ hℓ τ)
    (fun τ => by simpa only [Complex.norm_conj] using norm_conj_frobEig_le Z hℓ τ)
    hR (fun k => by have := hC k; rwa [towerMoment_natCast] at this) hRr
    (frobEig_ne_zero ℓ ρ) hUo hUc h0 hUr (fun z hz hzP => hUF z hz (Or.inl (hpoles hzP))) hε
    hball
  exact hvis h

/-! ### 3. Isolated eigenvalues -/

/-- **Accessibility inside a disc.** If near the origin the closed active folded spectrum lies in a
countable set `S` in which `w` is isolated, `w` is accessible inside every disc `|z| < r` with
`|w| < r ≤ r₀`. -/
theorem accessibleOff_ball_of_countable (Z : ZeroConfig) (g : ℝ → ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {S : Set ℂ} (hS : S.Countable) {r₀ : ℝ}
    (hsub : ball (0 : ℂ) r₀ ∩ closure (activeFoldedSpectrum Z g ℓ) ⊆ S) {w : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hiso : ∀ z ∈ S, ‖z - w‖ < ε → z = w) {r : ℝ} (hwr : ‖w‖ < r) (hrr₀ : r ≤ r₀) :
    AccessibleOff (closure (activeFoldedSpectrum Z g ℓ) ∪ (ball (0 : ℂ) r)ᶜ) w := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hwr
  have hFc : IsClosed (closure (activeFoldedSpectrum Z g ℓ) ∪ (ball (0 : ℂ) r)ᶜ) :=
    isClosed_closure.union isOpen_ball.isClosed_compl
  have hFball :
      (closure (activeFoldedSpectrum Z g ℓ) ∪ (ball (0 : ℂ) r)ᶜ) ∩ ball (0 : ℂ) r ⊆ S := by
    rintro z ⟨hzF | hzF, hzr⟩
    · exact hsub ⟨ball_subset_ball hrr₀ hzr, hzF⟩
    · exact absurd hzr hzF
  have h0 : (0 : ℂ) ∉ closure (activeFoldedSpectrum Z g ℓ) ∪ (ball (0 : ℂ) r)ᶜ := by
    rintro (h | h)
    · exact zero_notMem_closure_activeFoldedSpectrum Z g hℓ h
    · exact h (mem_ball_self hr)
  refine accessibleOff_of_countable hFc hr (hS.mono hFball) h0 hwr
    (lt_min hε (sub_pos.mpr hwr)) fun z hz hzw => ?_
  have hzr : z ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff]
    calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ < r := by linarith [hzw.trans_le (min_le_right _ _)]
  exact hiso z (hFball ⟨hz, hzr⟩) (hzw.trans_le (min_le_left _ _))

/-- **An isolated visible eigenvalue bounds the growth from below.** If `b` is visible and, inside
some disc `|z| < r₀` containing `b⁻¹`, the closed active folded spectrum lies in a countable set in
which `b⁻¹` is isolated, the Lefschetz sequence of `g` is not `O(R^m)` for any `0 < R < |b|`. -/
theorem not_towerMoment_isBigO_of_isolated (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℂ}
    (hb : b ∈ visibleSet Z g ℓ) {S : Set ℂ} (hS : S.Countable) {r₀ : ℝ} (hbr₀ : ‖b⁻¹‖ < r₀)
    (hsub : ball (0 : ℂ) r₀ ∩ closure (activeFoldedSpectrum Z g ℓ) ⊆ S) {ε : ℝ} (hε : 0 < ε)
    (hiso : ∀ z ∈ S, ‖z - b⁻¹‖ < ε → z = b⁻¹) {R : ℝ} (hR : 0 < R) (hRb : R < ‖b‖) :
    ¬ ∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k := by
  have hinv : ‖b⁻¹‖ < R⁻¹ := by
    rw [norm_inv]
    exact (inv_lt_inv₀ (hR.trans hRb) hR).mpr hRb
  set r : ℝ := min r₀ ((‖b⁻¹‖ + R⁻¹) / 2) with hrdef
  have hbr : ‖b⁻¹‖ < r := lt_min hbr₀ (by linarith)
  have hRr : R * r < 1 := by
    have h1 : R * r ≤ R * ((‖b⁻¹‖ + R⁻¹) / 2) := mul_le_mul_of_nonneg_left (min_le_right _ _) hR.le
    have h2 : R * ‖b⁻¹‖ < 1 := by
      have h := mul_lt_mul_of_pos_left hinv hR
      rwa [mul_inv_cancel₀ hR.ne'] at h
    have h3 : R * ((‖b⁻¹‖ + R⁻¹) / 2) = (R * ‖b⁻¹‖ + 1) / 2 := by
      rw [mul_div_assoc', mul_add, mul_inv_cancel₀ hR.ne']
    linarith
  exact not_towerMoment_isBigO_of_accessible Z hZ hg hgc hℓ hb
    (accessibleOff_ball_of_countable Z g hℓ hS hsub hε hiso hbr (min_le_left _ _)) hR hRr

/-! ### 4. One test reaches the top -/

/-- `|β_τ| < |β_ρ|` iff `Re τ < Re ρ`. -/
theorem norm_frobEig_lt_norm_frobEig {ℓ : ℝ} (hℓ : 0 < ℓ) {τ ρ : ℂ} (h : τ.re < ρ.re) :
    ‖frobEig ℓ τ‖ < ‖frobEig ℓ ρ‖ := by
  rw [norm_frobEig, norm_frobEig, Real.exp_lt_exp]
  exact mul_lt_mul_of_pos_left (by linarith) hℓ

/-- **A top zero is reached by one test.** The test killing every right zero of depth at least
half that of `ρ₀`, except `ρ₀`, has `c_m ≠ O(R^m)` for every `0 < R < |β_{ρ₀}|`. -/
theorem exists_test_growth_of_top (Z : ZeroConfig) (hZ : TemperedConfig Z) (hsp : DeepSparse Z)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ rightZeros Z) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ R : ℝ, 0 < R →
      R < ‖frobEig ℓ ρ₀‖ → ¬ ∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k := by
  set δ : ℝ := ρ₀.re - 1 / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith [hρ₀.2]
  have hσ : 1 / 2 < 1 / 2 + δ / 2 := by linarith
  obtain ⟨g, hg, hgc, hkill, hkeep⟩ :=
    exists_test_killing_deep_zeros Z hsp hσ {ρ₀} fun τ hτ => by
      rw [Set.mem_singleton_iff.mp hτ]; exact hρ₀
  refine ⟨g, hg, hgc, fun R hR hRb => ?_⟩
  have hvis : frobEig ℓ ρ₀ ∈ visibleSet Z g ℓ := by
    refine ⟨⟨ρ₀, hρ₀, rfl⟩, frobWeight_ne_zero_of_single Z hρ₀ rfl
      (hkeep ρ₀ (Set.mem_singleton ρ₀)) fun τ hτ hne he => ?_⟩
    have hre : τ.re = ρ₀.re := re_eq_of_norm_frobEig_eq hℓ (congrArg norm he)
    exact (hkill τ ⟨hτ, by rw [hre]; exact hρ₀.2⟩ (by rw [hre]; linarith) hne).1
  set r₀ : ℝ := Real.exp (-(ℓ * (δ / 2))) with hr₀
  have hsub' : ball (0 : ℂ) r₀ ∩ activeFoldedSpectrum Z g ℓ ⊆ {(frobEig ℓ ρ₀)⁻¹} := by
    rintro z ⟨hzr, τ, hτ, hact, rfl⟩
    rw [mem_ball_zero_iff, norm_inv, norm_frobEig, ← Real.exp_neg, hr₀, Real.exp_lt_exp] at hzr
    have hτre : 1 / 2 + δ / 2 < τ.re := by
      have := lt_of_mul_lt_mul_left (show ℓ * (δ / 2) < ℓ * (τ.re - 1 / 2) by linarith) hℓ.le
      linarith
    by_cases hτρ : τ = ρ₀
    · rw [hτρ]; exact Set.mem_singleton _
    · exfalso
      have h0 := hkill τ ⟨hτ, by linarith⟩ hτre.le hτρ
      rw [gammaOf_reflect] at h0
      rcases hact with h | h
      · exact h h0.1
      · exact h h0.2
  have hsub : ball (0 : ℂ) r₀ ∩ closure (activeFoldedSpectrum Z g ℓ) ⊆ {(frobEig ℓ ρ₀)⁻¹} :=
    isOpen_ball.inter_closure.trans ((closure_mono hsub').trans isClosed_singleton.closure_subset)
  have hbr₀ : ‖(frobEig ℓ ρ₀)⁻¹‖ < r₀ := by
    rw [norm_inv, norm_frobEig, ← Real.exp_neg, hr₀, Real.exp_lt_exp]
    have h2 := mul_lt_mul_of_pos_left (half_lt_self hδ) hℓ
    have h3 : ℓ * δ = ℓ * (ρ₀.re - 1 / 2) := by rw [hδdef]
    linarith
  exact not_towerMoment_isBigO_of_isolated Z hZ hg hgc hℓ hvis (Set.countable_singleton _) hbr₀
    hsub one_pos (fun z hz _ => Set.mem_singleton_iff.mp hz) hR hRb

/-- **A cofinal increasing sequence.** If the real parts of the right zeros have no largest
element, some sequence of right zeros has strictly increasing real parts, eventually above the real
part of every right zero. -/
theorem exists_strictMono_cofinal_seq (Z : ZeroConfig) (hne : (rightZeros Z).Nonempty)
    (hnotop : ∀ ρ ∈ rightZeros Z, ∃ ρ' ∈ rightZeros Z, ρ.re < ρ'.re) :
    ∃ ρs : ℕ → ℂ, (∀ n, ρs n ∈ rightZeros Z) ∧ StrictMono (fun n => (ρs n).re) ∧
      ∀ ρ ∈ rightZeros Z, ∃ n, ρ.re < (ρs n).re := by
  -- the top `s` of the real parts is not attained
  set A : Set ℝ := Complex.re '' rightZeros Z with hA
  have hAne : A.Nonempty := hne.image _
  have hAbdd : BddAbove A := ⟨1, by rintro _ ⟨ρ, hρ, rfl⟩; exact (Z.strip ρ hρ.1).2⟩
  set s : ℝ := sSup A with hs
  have hlt : ∀ ρ ∈ rightZeros Z, ρ.re < s := fun ρ hρ => by
    obtain ⟨ρ', hρ', h⟩ := hnotop ρ hρ
    exact h.trans_le (le_csSup hAbdd ⟨ρ', hρ', rfl⟩)
  have hex : ∀ t : ℝ, t < s → ∃ ρ, ρ ∈ rightZeros Z ∧ t < ρ.re := fun t ht => by
    obtain ⟨_, ⟨ρ, hρ, rfl⟩, h⟩ := exists_lt_of_lt_csSup hAne ht
    exact ⟨ρ, hρ, h⟩
  choose! pick hpickR hpickre using hex
  set ρs : ℕ → ℂ := fun n => Nat.rec (motive := fun _ => ℂ) (pick (s - 1))
    (fun n ρ => pick (max ρ.re (s - 1 / ((n : ℝ) + 2)))) n with hρs
  have hρs0 : ρs 0 = pick (s - 1) := rfl
  have hρsS : ∀ n : ℕ, ρs (n + 1) = pick (max (ρs n).re (s - 1 / ((n : ℝ) + 2))) := fun n => rfl
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 2) := fun n => by positivity
  have hmem : ∀ n, ρs n ∈ rightZeros Z := by
    intro n
    induction n with
    | zero => rw [hρs0]; exact hpickR _ (by linarith)
    | succ n ih =>
      rw [hρsS]
      exact hpickR (max (ρs n).re (s - 1 / ((n : ℝ) + 2)))
        (max_lt (hlt _ ih) (by linarith [hpos n]))
  have hstep : ∀ n : ℕ, (ρs n).re < (ρs (n + 1)).re ∧
      s - 1 / ((n : ℝ) + 2) < (ρs (n + 1)).re := by
    intro n
    have h := hpickre (max (ρs n).re (s - 1 / ((n : ℝ) + 2)))
      (max_lt (hlt _ (hmem n)) (by linarith [hpos n]))
    rw [← hρsS] at h
    exact ⟨(le_max_left _ _).trans_lt h, (le_max_right _ _).trans_lt h⟩
  refine ⟨ρs, hmem, strictMono_nat_of_lt_succ fun n => (hstep n).1, fun ρ hρ => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (hlt ρ hρ))
  refine ⟨n + 1, lt_trans ?_ (hstep n).2⟩
  have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- **A kept sequence with convergent folded points reaches its top.** Let `ρ'` be right zeros with
strictly increasing real parts and `g` a test that sees every `ρ' n` and kills every other right
zero of depth at least half that of `ρ' 0`. If the folded points `β_{ρ' n}⁻¹` converge at scale `ℓ`,
each is isolated in the sequence and its limit, and `c_m ≠ O(R^m)` for every
`0 < R < |β_{ρ' n}|`. -/
theorem not_towerMoment_isBigO_of_kept_seq (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {ρ' : ℕ → ℂ} (hmem : ∀ n, ρ' n ∈ rightZeros Z) (hmono : StrictMono fun n => (ρ' n).re)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hkill : ∀ τ ∈ rightZeros Z, 1 / 2 + ((ρ' 0).re - 1 / 2) / 2 ≤ τ.re → τ ∉ Set.range ρ' →
      paperFT g (gammaOf τ) = 0 ∧ paperFT g (gammaOf (reflect τ)) = 0)
    (hkeep : ∀ τ ∈ Set.range ρ',
      paperFT g (gammaOf τ) ≠ 0 ∧ paperFT g (gammaOf (reflect τ)) ≠ 0)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℂ} (hlim : Tendsto (fun n => (frobEig ℓ (ρ' n))⁻¹) atTop (𝓝 x))
    (n : ℕ) {R : ℝ} (hR : 0 < R) (hRb : R < ‖frobEig ℓ (ρ' n)‖) :
    ¬ ∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k := by
  set v : ℕ → ℂ := fun n => (frobEig ℓ (ρ' n))⁻¹ with hv
  have hvn : ∀ n, v n = (frobEig ℓ (ρ' n))⁻¹ := fun n => rfl
  have hanti : StrictAnti fun n => ‖v n‖ := fun a b hab => by
    simp only [hvn, norm_inv]
    exact (inv_lt_inv₀ (norm_pos_iff.mpr (frobEig_ne_zero _ _))
      (norm_pos_iff.mpr (frobEig_ne_zero _ _))).mpr (norm_frobEig_lt_norm_frobEig hℓ (hmono hab))
  have hx : ∀ n, ‖x‖ < ‖v n‖ := fun n => by
    have hlimn : Tendsto (fun m => ‖v m‖) atTop (𝓝 ‖x‖) := (continuous_norm.tendsto x).comp hlim
    have h1 : ‖x‖ ≤ ‖v (n + 1)‖ :=
      le_of_tendsto hlimn (eventually_atTop.mpr ⟨n + 1, fun m hm => hanti.antitone hm⟩)
    exact h1.trans_lt (hanti (Nat.lt_succ_self n))
  -- each `v n` is isolated in `{x} ∪ {v m}`
  have hiso : ∀ n, ∃ ε > 0, ∀ z ∈ insert x (Set.range v), ‖z - v n‖ < ε → z = v n := by
    intro n
    have hgap : ∀ k, 0 < ‖v k‖ - ‖v (k + 1)‖ := fun k => sub_pos.mpr (hanti (Nat.lt_succ_self k))
    refine ⟨min (‖v n‖ - ‖v (n + 1)‖) (‖v (n - 1)‖ - ‖v (n - 1 + 1)‖),
      lt_min (hgap n) (hgap _), fun z hz hzn => ?_⟩
    have hrev : ‖v n‖ - ‖z‖ ≤ ‖z - v n‖ := by
      have := norm_sub_norm_le (v n) z
      rwa [norm_sub_rev] at this
    have hfwd : ‖z‖ - ‖v n‖ ≤ ‖z - v n‖ := norm_sub_norm_le z (v n)
    have hε1 := hzn.trans_le (min_le_left _ _)
    have hε2 := hzn.trans_le (min_le_right _ _)
    rcases hz with hzx | ⟨m, rfl⟩
    · exfalso
      rw [hzx] at hrev hε1
      linarith [hx (n + 1)]
    · rcases lt_trichotomy m n with h | rfl | h
      · exfalso
        have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega))
        rw [hn1] at hε2
        have hm : ‖v (n - 1)‖ ≤ ‖v m‖ := hanti.antitone (by omega)
        linarith
      · rfl
      · exfalso
        have hm : ‖v m‖ ≤ ‖v (n + 1)‖ := hanti.antitone h
        linarith
  set δ₀ : ℝ := (ρ' 0).re - 1 / 2 with hδ₀
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; linarith [(hmem 0).2]
  have hdeep : ∀ n, δ₀ ≤ (ρ' n).re - 1 / 2 := fun n => by
    have h : (ρ' 0).re ≤ (ρ' n).re := hmono.monotone (Nat.zero_le n)
    rw [hδ₀]; linarith
  -- the kept zero `ρ' n` is visible
  have hvis : frobEig ℓ (ρ' n) ∈ visibleSet Z g ℓ := by
    refine ⟨⟨_, hmem n, rfl⟩, frobWeight_ne_zero_of_single Z (hmem n) rfl
      (hkeep _ ⟨n, rfl⟩) fun τ hτ hne he => ?_⟩
    have hre : τ.re = (ρ' n).re := re_eq_of_norm_frobEig_eq hℓ (congrArg norm he)
    have hτF : τ ∉ Set.range ρ' := by
      rintro ⟨k, hk⟩
      have hk' : (ρ' k).re = (ρ' n).re := by rw [hk, hre]
      have hkn : k = n := hmono.injective hk'
      exact hne (by rw [← hk, hkn])
    exact (hkill τ ⟨hτ, by rw [hre]; exact (hmem _).2⟩
      (by rw [hre]; linarith [hdeep n]) hτF).1
  -- near the origin the folded spectrum lies in the sequence and its limit
  set r₀ : ℝ := Real.exp (-(ℓ * (δ₀ / 2))) with hr₀
  have hsub' : ball (0 : ℂ) r₀ ∩ activeFoldedSpectrum Z g ℓ ⊆ Set.range v := by
    rintro z ⟨hzr, τ, hτ, hact, rfl⟩
    rw [mem_ball_zero_iff, norm_inv, norm_frobEig, ← Real.exp_neg, hr₀, Real.exp_lt_exp] at hzr
    have hτre : 1 / 2 + δ₀ / 2 < τ.re := by
      have := lt_of_mul_lt_mul_left (show ℓ * (δ₀ / 2) < ℓ * (τ.re - 1 / 2) by linarith) hℓ.le
      linarith
    by_cases hτF : τ ∈ Set.range ρ'
    · obtain ⟨k, hk⟩ := hτF
      exact ⟨k, by rw [hvn, hk]⟩
    · exfalso
      have h0 := hkill τ ⟨hτ, by linarith⟩ hτre.le hτF
      rw [gammaOf_reflect] at h0
      rcases hact with h | h
      · exact h h0.1
      · exact h h0.2
  have hsub : ball (0 : ℂ) r₀ ∩ closure (activeFoldedSpectrum Z g ℓ) ⊆ insert x (Set.range v) :=
    isOpen_ball.inter_closure.trans ((closure_mono hsub').trans
      (closure_minimal (Set.subset_insert _ _) hlim.isCompact_insert_range.isClosed))
  have hbr₀ : ‖(frobEig ℓ (ρ' n))⁻¹‖ < r₀ := by
    rw [norm_inv, norm_frobEig, ← Real.exp_neg, hr₀, Real.exp_lt_exp]
    have h1 := mul_le_mul_of_nonneg_left (hdeep n) hℓ.le
    have h2 := mul_lt_mul_of_pos_left (half_lt_self hδ₀pos) hℓ
    linarith
  obtain ⟨ε, hε, hisoε⟩ := hiso n
  exact not_towerMoment_isBigO_of_isolated Z hZ hg hgc hℓ hvis
    ((Set.countable_range v).insert x) hbr₀ hsub hε (fun z hz hzn => hisoε z hz hzn) hR hRb

/-- **A non-attained top is reached by one test.** If the real parts of the right zeros have no
largest element, the test keeping a sequence of zeros whose real parts increase to the top and
whose folded points converge has `c_m ≠ O(R^m)` for every `0 < R < |β_ρ|`, `ρ` any right zero. -/
theorem exists_test_growth_of_no_top (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ℓ : ℝ} (hℓ : 0 < ℓ) (hne : (rightZeros Z).Nonempty)
    (hnotop : ∀ ρ ∈ rightZeros Z, ∃ ρ' ∈ rightZeros Z, ρ.re < ρ'.re) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ ρ ∈ rightZeros Z, ∀ R : ℝ, 0 < R →
      R < ‖frobEig ℓ ρ‖ → ¬ ∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k := by
  obtain ⟨ρs, hmem, hmono, hcof⟩ := exists_strictMono_cofinal_seq Z hne hnotop
  -- folded points and a convergent subsequence
  have hu1 : ∀ n, (frobEig ℓ (ρs n))⁻¹ ∈ closedBall (0 : ℂ) 1 := fun n => by
    rw [mem_closedBall_zero_iff, norm_inv]
    exact (inv_lt_one_of_one_lt₀ ((one_lt_norm_frobEig_iff hℓ _).mpr (hmem n).2)).le
  obtain ⟨x, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq hu1
  have hmono' : StrictMono fun n => (ρs (φ n)).re := hmono.comp hφ
  have hσ : 1 / 2 < 1 / 2 + ((ρs (φ 0)).re - 1 / 2) / 2 := by linarith [(hmem (φ 0)).2]
  obtain ⟨g, hg, hgc, hkill, hkeep⟩ :=
    exists_test_killing_deep_zeros Z hsp hσ (Set.range fun n => ρs (φ n)) fun τ ⟨n, hn⟩ => by
      rw [← show ρs (φ n) = τ from hn]; exact hmem (φ n)
  refine ⟨g, hg, hgc, fun ρ hρ R hR hRρ => ?_⟩
  obtain ⟨n, hn⟩ := hcof ρ hρ
  have hφn : (ρs n).re ≤ (ρs (φ n)).re := hmono.monotone (hφ.id_le n)
  exact not_towerMoment_isBigO_of_kept_seq Z hZ (ρ' := fun n => ρs (φ n)) (fun n => hmem (φ n))
    hmono' hg hgc hkill hkeep hℓ hlim n hR
    (hRρ.trans (norm_frobEig_lt_norm_frobEig hℓ (hn.trans_le hφn)))

/-- **One Lefschetz sequence carries the top.** For a deep-sparse configuration and every `ℓ > 0`
one `C²` compactly supported test has `c_m = O(R^m)`, `R ≥ 1`, iff `R ≥ |β_ρ|` for every right
zero `ρ`: the exponential growth rate of its Lefschetz sequence is the top Frobenius modulus. -/
theorem deepSparse_exists_test_lefschetz_growth (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ R : ℝ, 1 ≤ R →
      ((∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k) ↔
        ∀ ρ ∈ rightZeros Z, ‖frobEig ℓ ρ‖ ≤ R) := by
  suffices h : ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ ρ ∈ rightZeros Z,
      ∀ R : ℝ, 0 < R → R < ‖frobEig ℓ ρ‖ → ¬ ∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k by
    obtain ⟨g, hg, hgc, hlow⟩ := h
    refine ⟨g, hg, hgc, fun R hR =>
      ⟨fun hO ρ hρ => ?_, exists_norm_towerMoment_le Z hZ hg hgc hℓ hR⟩⟩
    by_contra hlt
    exact hlow ρ hρ R (by linarith) (not_le.mp hlt) hO
  rcases (rightZeros Z).eq_empty_or_nonempty with he | hne
  · exact ⟨0, contDiff_const, HasCompactSupport.zero, fun ρ hρ => by
      rw [he] at hρ; exact absurd hρ (Set.notMem_empty _)⟩
  · by_cases htop : ∃ ρ₀ ∈ rightZeros Z, ∀ ρ ∈ rightZeros Z, ρ.re ≤ ρ₀.re
    · obtain ⟨ρ₀, hρ₀, htop⟩ := htop
      obtain ⟨g, hg, hgc, h⟩ := exists_test_growth_of_top Z hZ hsp hℓ hρ₀
      refine ⟨g, hg, hgc, fun ρ hρ R hR hRρ => h R hR (hRρ.trans_le ?_)⟩
      rw [norm_frobEig, norm_frobEig, Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left (by linarith [htop ρ hρ]) hℓ.le
    · push Not at htop
      exact exists_test_growth_of_no_top Z hZ hsp hℓ hne htop

/-! ### 5. `ζ` -/

/-- For `R ≥ 1` the outer eigenvalues `p^{ρ−½}` of `ζ` are bounded by `R` iff `p^w ≤ R`, `w` the
zero width. -/
theorem zeta_forall_norm_frobEig_le_iff {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : 1 ≤ R) :
    (∀ ρ ∈ rightZeros zetaZeroConfig, ‖frobEig (Real.log p) ρ‖ ≤ R) ↔
      (p : ℝ) ^ zetaZeroWidth ≤ R := by
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hR0 : 0 < R := by linarith
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos)]
  constructor
  · intro hdom
    have key : ∀ τ ∈ rightZeros zetaZeroConfig, Real.log p * (τ.re - 1 / 2) ≤ Real.log R :=
      fun τ hτ => (Real.le_log_iff_exp_le hR0).mpr (by rw [← norm_frobEig]; exact hdom τ hτ)
    have hw : zetaZeroWidth ≤ Real.log R / Real.log p := by
      refine Real.sSup_le ?_ (div_nonneg (Real.log_nonneg hR) hℓ.le)
      rintro _ ⟨ρ, hρ, rfl⟩
      rw [le_div_iff₀ hℓ]
      show |ρ.re - 1 / 2| * Real.log p ≤ Real.log R
      rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
      · have hr : reflect ρ ∈ rightZeros zetaZeroConfig :=
          ⟨zetaZeroConfig.reflect_mem ρ hρ, by rw [re_reflect]; linarith⟩
        have := key _ hr
        rw [re_reflect] at this
        rw [abs_of_neg (by linarith)]
        linarith
      · rw [h, sub_self, abs_zero, zero_mul]
        exact Real.log_nonneg hR
      · rw [abs_of_pos (by linarith), mul_comm]
        exact key ρ ⟨hρ, h⟩
    calc Real.exp (Real.log p * zetaZeroWidth)
        ≤ Real.exp (Real.log p * (Real.log R / Real.log p)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hℓ.le)
      _ = R := by rw [mul_div_cancel₀ _ hℓ.ne', Real.exp_log hR0]
  · intro hpw ρ hρ
    rw [norm_frobEig]
    refine le_trans (Real.exp_le_exp.mpr ?_) hpw
    exact mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (abs_re_sub_half_le_zetaZeroWidth hρ.1)) hℓ.le

/-- **The Lefschetz sequence of one test grows at the zero width.** For every prime `p` one test `g`
has `|W(T_{p^m} g, g)| = O(R^m)`, `R ≥ 1`, iff `R ≥ p^w`, `w = sup |Re ρ − ½|` the zero width of
`ζ`. A bound `O(p^{θm})` is the zero-free strip `|Re ρ − ½| ≤ θ`. -/
theorem zeta_lefschetz_growth_law {p : ℕ} (hp : p.Prime) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ R : ℝ, 1 ≤ R →
      ((∃ C, ∀ k : ℕ, ‖towerMoment zetaZeroConfig g (Real.log p) k‖ ≤ C * R ^ k) ↔
        (p : ℝ) ^ zetaZeroWidth ≤ R) := by
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨g, hg, hgc, hlaw⟩ := deepSparse_exists_test_lefschetz_growth _
    temperedConfig_zetaZeroConfig deepSparse_zeta hℓ
  exact ⟨g, hg, hgc, fun R hR => (hlaw R hR).trans (zeta_forall_norm_frobEig_le_iff hp hR)⟩

/-- **Weil's two-element windows decide RH at one prime.** For every prime `p` one test `g` has: RH
holds iff `|W(T_{p^m} g, g)| ≤ W(g, g)` for every `m ≥ 0`, the Castelnuovo–Severi inequality on
the spans `⟨g, T_{p^m} g⟩` as in Weil's proof over `𝔽_q`. -/
theorem zeta_riemannHypothesis_iff_lefschetz_minors {p : ℕ} (hp : p.Prime) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (RiemannHypothesis ↔ ∀ k : ℕ, ‖towerMoment zetaZeroConfig g (Real.log p) k‖ ≤
        (towerMoment zetaZeroConfig g (Real.log p) 0).re) := by
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨g, hg, hgc, hlaw⟩ := deepSparse_exists_test_lefschetz_growth _
    temperedConfig_zetaZeroConfig deepSparse_zeta hℓ
  refine ⟨g, hg, hgc, ?_⟩
  rw [← rightZeros_zeta_eq_empty_iff]
  constructor
  · exact fun hR k => norm_towerMoment_le_of_rightZeros_eq_empty _
      temperedConfig_zetaZeroConfig hg hgc _ hR k
  · intro hmin
    have hdom := (hlaw 1 le_rfl).mp ⟨(towerMoment zetaZeroConfig g (Real.log p) 0).re,
      fun k => by rw [one_pow, mul_one]; exact hmin k⟩
    refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ => ?_
    exact absurd (hdom ρ hρ) (not_le.mpr ((one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
