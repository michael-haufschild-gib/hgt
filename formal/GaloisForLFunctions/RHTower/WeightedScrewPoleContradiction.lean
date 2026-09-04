import GaloisForLFunctions.RHTower.WeightedScrewLandauEngine
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The pole contradiction for a positive weighted screw divisor

If a bounded weight `W` on the Xi zero copies depends only on the spectral point, is even under the
functional-equation reflection, does not vanish at any off-line copy, and the weighted screw divisor
`Φ_W` is real and nonnegative on the source half-line, then RH holds.

Proof.  By the weighted Widder–Landau engine the Laplace transform `F` of `Φ_W` is analytic on the
open right half-plane.  The weighted atom series `G(s) = Σ'_q W_q/(s(s² + γ_q²))` is analytic on the
right half-plane minus the countable pole set `{±iγ_q}`, which is connected (it is the image of the
complement of a countable set under the chart `u ↦ e^{Re u} + i Im u`), and `F = G` there by the
identity theorem.  An off-line copy `q₀` with `Im γ_{q₀} < 0` gives the pole `s₀ = iγ_{q₀}` with
`Re s₀ > 0`; along `s_n = s₀ + 1/(n+1)` the products `(s_n − s₀) G(s_n)` tend to
`(Σ_{γ_q = ±γ_{q₀}} W_q) / (2 s₀²) ≠ 0`, whereas `(s_n − s₀) F(s_n) → 0`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Finiteness of bounded spectral points -/

theorem finite_xiZeroCopy_norm_le (K : ℝ) :
    {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ K}.Finite := by
  rcases le_or_gt K 0 with hK | hK
  · have hempty : {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ K} = ∅ := by
      ext q
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_le_of_lt hK (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))
    rw [hempty]
    exact finite_empty
  · have hev := xiSpectralPoint_inv_sq_summable.tendsto_cofinite_zero.eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * K ^ 2) by positivity))
    rw [Filter.eventually_cofinite] at hev
    refine hev.subset ?_
    intro q hq
    simp only [mem_setOf_eq, not_lt] at hq ⊢
    have hγ : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have h1 : ‖xiSpectralPoint q‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hγ.le hq 2
    calc 1 / (2 * K ^ 2) ≤ 1 / (2 * ‖xiSpectralPoint q‖ ^ 2) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
      _ ≤ 1 / ‖xiSpectralPoint q‖ ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg ‖xiSpectralPoint q‖]

/-! ## The pole set and the punctured right half-plane -/

/-- The poles `±iγ_q` of the atom series. -/
def spectralPoleSet : Set ℂ :=
  Set.range (fun q : XiZeroCopy => I * xiSpectralPoint q) ∪
    Set.range (fun q : XiZeroCopy => -(I * xiSpectralPoint q))

theorem countable_spectralPoleSet : spectralPoleSet.Countable :=
  (Set.countable_range _).union (Set.countable_range _)

/-- The open right half-plane with the poles removed. -/
def rightHalfPunctured : Set ℂ := {s : ℂ | 0 < s.re} \ spectralPoleSet

theorem one_notMem_spectralPoleSet : (1 : ℂ) ∉ spectralPoleSet := by
  intro h
  rcases h with ⟨q, hq⟩ | ⟨q, hq⟩
  · have := congrArg Complex.im hq
    simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, one_im] at this
    have h4 := four_lt_abs_re_xiSpectralPoint q
    rw [this] at h4
    norm_num at h4
  · have := congrArg Complex.im hq
    simp only [neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, one_im] at this
    have h4 := four_lt_abs_re_xiSpectralPoint q
    rw [show (xiSpectralPoint q).re = 0 by linarith] at h4
    norm_num at h4

/-- The chart `u ↦ e^{Re u} + i Im u` from `ℂ` onto the open right half-plane. -/
def rightHalfPlaneChart (u : ℂ) : ℂ := (Real.exp u.re : ℂ) + (u.im : ℂ) * I

theorem continuous_rightHalfPlaneChart : Continuous rightHalfPlaneChart := by
  unfold rightHalfPlaneChart
  fun_prop

@[simp] theorem halfPlaneChart_re (u : ℂ) : (rightHalfPlaneChart u).re = Real.exp u.re := by
  simp [rightHalfPlaneChart, Complex.exp_ofReal_re]

@[simp] theorem halfPlaneChart_im (u : ℂ) : (rightHalfPlaneChart u).im = u.im := by
  simp [rightHalfPlaneChart]

theorem halfPlaneChart_injective : Function.Injective rightHalfPlaneChart := by
  intro u v huv
  have h1 := congrArg Complex.re huv
  have h2 := congrArg Complex.im huv
  rw [halfPlaneChart_re, halfPlaneChart_re] at h1
  rw [halfPlaneChart_im, halfPlaneChart_im] at h2
  exact Complex.ext (Real.exp_injective h1) h2

theorem exists_halfPlaneChart_eq {s : ℂ} (hs : 0 < s.re) : ∃ u, rightHalfPlaneChart u = s :=
  ⟨(Real.log s.re : ℂ) + (s.im : ℂ) * I, by
    apply Complex.ext
    · simp [rightHalfPlaneChart, Real.exp_log hs]
    · simp [rightHalfPlaneChart]⟩

theorem one_lt_rank_real_complex : 1 < Module.rank ℝ ℂ := by
  rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
  exact_mod_cast (by norm_num : (1 : ℕ) < 2)

/-- **The punctured right half-plane is connected.** -/
theorem isPreconnected_rightHalfPunctured : IsPreconnected rightHalfPunctured := by
  have hT : IsConnected (rightHalfPlaneChart ⁻¹' spectralPoleSet)ᶜ :=
    Set.Countable.isConnected_compl_of_one_lt_rank one_lt_rank_real_complex
      (countable_spectralPoleSet.preimage_of_injOn halfPlaneChart_injective.injOn)
  have himg : rightHalfPlaneChart '' (rightHalfPlaneChart ⁻¹' spectralPoleSet)ᶜ = rightHalfPunctured := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, hu⟩
      show 0 < (rightHalfPlaneChart u).re
      rw [halfPlaneChart_re]
      exact Real.exp_pos _
    · rintro ⟨hre, hP⟩
      obtain ⟨u, rfl⟩ := exists_halfPlaneChart_eq hre
      exact ⟨u, hP, rfl⟩
  rw [← himg]
  exact (hT.image _ continuous_rightHalfPlaneChart.continuousOn).isPreconnected

/-! ## Atom bounds away from the poles -/

theorem sq_add_sq_eq_mul (s γ : ℂ) : s ^ 2 + γ ^ 2 = (s - I * γ) * (s + I * γ) := by
  ring_nf
  rw [I_sq]
  ring

theorem norm_atom_le_of_dist {s γ : ℂ} {ds dm dp : ℝ} (h0 : 0 < ds) (h1 : 0 < dm) (h2 : 0 < dp)
    (hs : ds ≤ ‖s‖) (hm : dm ≤ ‖s - I * γ‖) (hp : dp ≤ ‖s + I * γ‖) :
    ‖suzukiPsiLaplaceAtom s γ‖ ≤ 1 / (ds * dm * dp) := by
  unfold suzukiPsiLaplaceAtom
  rw [sq_add_sq_eq_mul, norm_div, norm_one, norm_mul, norm_mul]
  apply one_div_le_one_div_of_le (by positivity)
  calc ds * dm * dp = ds * (dm * dp) := by ring
    _ ≤ ‖s‖ * (‖s - I * γ‖ * ‖s + I * γ‖) := by gcongr

theorem differentiableOn_atom_of_ne {γ : ℂ} {U : Set ℂ}
    (h0 : ∀ s ∈ U, s ≠ 0) (hm : ∀ s ∈ U, s - I * γ ≠ 0) (hp : ∀ s ∈ U, s + I * γ ≠ 0) :
    DifferentiableOn ℂ (fun s => suzukiPsiLaplaceAtom s γ) U := by
  intro s hs
  have hquad : s ^ 2 + γ ^ 2 ≠ 0 := by
    rw [sq_add_sq_eq_mul]
    exact mul_ne_zero (hm s hs) (hp s hs)
  apply DifferentiableAt.differentiableWithinAt
  unfold suzukiPsiLaplaceAtom
  exact (differentiableAt_const (c := (1 : ℂ))).div (by fun_prop) (mul_ne_zero (h0 s hs) hquad)

variable (W : XiZeroCopy → ℂ)

/-- The weighted atom series with a finite set of copies removed. -/
def weightedScrewContinuationExcept (E : Finset XiZeroCopy) (s : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, if q ∈ E then 0 else W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q)

/-- **Uniform bound on a ball around a non-pole point.**  Returns a radius `ρ`, a summable
majorant `u`, and the statements that on the closed ball every point is nonzero and away from
every pole of a copy outside `E`, with the majorant controlling the corresponding terms. -/
theorem exists_uniform_atom_bound {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (E : Finset XiZeroCopy) {s₁ : ℂ} (hre : 0 < s₁.re)
    (hnot : ∀ q, q ∉ E → I * xiSpectralPoint q ≠ s₁ ∧ -(I * xiSpectralPoint q) ≠ s₁) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ u : XiZeroCopy → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      (∀ s ∈ Metric.closedBall s₁ ρ, 0 < s.re) ∧
      (∀ q, q ∉ E → ∀ s ∈ Metric.closedBall s₁ ρ,
        s - I * xiSpectralPoint q ≠ 0 ∧ s + I * xiSpectralPoint q ≠ 0) ∧
      (∀ q, q ∉ E → ∀ s ∈ Metric.closedBall s₁ ρ,
        ‖W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q)‖ ≤ u q) := by
  have hs₁ : 0 < ‖s₁‖ := by
    have : s₁.re ≤ ‖s₁‖ := (le_abs_self _).trans (Complex.abs_re_le_norm s₁)
    linarith
  set K : ℝ := 2 * ‖s₁‖ + 2 with hK
  have hAfin := finite_xiZeroCopy_norm_le K
  set A : Finset XiZeroCopy := hAfin.toFinset with hA
  have hAmem : ∀ q, q ∈ A ↔ ‖xiSpectralPoint q‖ ≤ K := fun q => by
    rw [hA, Set.Finite.mem_toFinset]
    rfl
  -- distance from `s₁` to the poles of the finitely many small copies outside `E`
  set B : Finset XiZeroCopy := A.filter (fun q => q ∉ E) with hB
  let dist2 : XiZeroCopy → ℝ := fun q =>
    min ‖s₁ - I * xiSpectralPoint q‖ ‖s₁ + I * xiSpectralPoint q‖
  have hdist2pos : ∀ q, q ∉ E → 0 < dist2 q := by
    intro q hq
    have h := hnot q hq
    apply lt_min
    · rw [norm_pos_iff, sub_ne_zero]
      exact fun h' => h.1 h'.symm
    · rw [norm_pos_iff]
      intro h'
      exact h.2 (by linear_combination (-1 : ℂ) * h')
  obtain ⟨δ₀, hδ₀, hδ⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ q ∈ B, δ₀ ≤ dist2 q := by
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · exact ⟨1, one_pos, fun q hq => by rw [hBe] at hq; exact absurd hq (Finset.notMem_empty q)⟩
    · obtain ⟨q₁, hq₁, hmin⟩ := B.exists_min_image dist2 hBne
      have hq₁E : q₁ ∉ E := (Finset.mem_filter.mp hq₁).2
      exact ⟨dist2 q₁, hdist2pos q₁ hq₁E, fun q hq => hmin q hq⟩
  set ρ : ℝ := min (min (δ₀ / 2) (‖s₁‖ / 2)) (s₁.re / 2) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hρδ : ρ ≤ δ₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hρs : ρ ≤ ‖s₁‖ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρre : ρ ≤ s₁.re / 2 := min_le_right _ _
  -- pointwise facts on the closed ball
  have hball_norm : ∀ s ∈ Metric.closedBall s₁ ρ, ‖s₁‖ / 2 ≤ ‖s‖ ∧ ‖s‖ ≤ 3 * ‖s₁‖ / 2 := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    have h1 := norm_sub_norm_le s s₁
    have h2 := norm_sub_norm_le s₁ s
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  have hball_re : ∀ s ∈ Metric.closedBall s₁ ρ, 0 < s.re := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    have := (neg_le_abs _).trans (Complex.abs_re_le_norm (s - s₁))
    rw [sub_re] at this
    linarith
  -- the majorant
  let u : XiZeroCopy → ℝ := fun q =>
    if q ∈ A then C * (1 / ((‖s₁‖ / 2) * (δ₀ / 2) * (δ₀ / 2)))
    else C * (32 / ‖s₁‖) * (1 / ‖xiSpectralPoint q‖ ^ 2)
  have hu_summable : Summable u := by
    have h1 : Summable (fun q : XiZeroCopy =>
        if q ∈ A then C * (1 / ((‖s₁‖ / 2) * (δ₀ / 2) * (δ₀ / 2))) else 0) :=
      summable_of_ne_finset_zero (s := A) fun q hq => by simp [hq]
    have h2 : Summable (fun q : XiZeroCopy =>
        C * (32 / ‖s₁‖) * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
      xiSpectralPoint_inv_sq_summable.mul_left _
    refine (h1.add h2).of_nonneg_of_le (fun q => ?_) (fun q => ?_)
    · dsimp only [u]
      split_ifs <;> positivity
    · dsimp only [u]
      by_cases hq : q ∈ A
      · simp only [hq, if_true]
        have : 0 ≤ C * (32 / ‖s₁‖) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by positivity
        linarith
      · simp only [hq, if_false, zero_add, le_refl]
  have hu_nonneg : ∀ q, 0 ≤ u q := by
    intro q
    dsimp only [u]
    split_ifs <;> positivity
  refine ⟨ρ, hρpos, u, hu_summable, hu_nonneg, hball_re, ?_, ?_⟩
  · -- nonvanishing of `s ∓ iγ_q` for `q ∉ E`
    intro q hq s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    by_cases hqA : q ∈ A
    · have hqB : q ∈ B := Finset.mem_filter.mpr ⟨hqA, hq⟩
      have hd := hδ q hqB
      have hm : δ₀ ≤ ‖s₁ - I * xiSpectralPoint q‖ := hd.trans (min_le_left _ _)
      have hp : δ₀ ≤ ‖s₁ + I * xiSpectralPoint q‖ := hd.trans (min_le_right _ _)
      constructor
      · rw [← norm_pos_iff]
        have := norm_sub_norm_le (s₁ - I * xiSpectralPoint q) (s₁ - s)
        rw [show s₁ - I * xiSpectralPoint q - (s₁ - s) = s - I * xiSpectralPoint q by ring] at this
        rw [norm_sub_rev] at hs
        linarith
      · rw [← norm_pos_iff]
        have := norm_sub_norm_le (s₁ + I * xiSpectralPoint q) (s₁ - s)
        rw [show s₁ + I * xiSpectralPoint q - (s₁ - s) = s + I * xiSpectralPoint q by ring] at this
        rw [norm_sub_rev] at hs
        linarith
    · have hγ : K < ‖xiSpectralPoint q‖ := by
        by_contra hle
        exact hqA ((hAmem q).mpr (not_lt.mp hle))
      have hsn := (hball_norm s (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hs)).2
      have hI : ‖I * xiSpectralPoint q‖ = ‖xiSpectralPoint q‖ := by
        rw [norm_mul, norm_I, one_mul]
      constructor
      · rw [← norm_pos_iff]
        have := norm_sub_norm_le (I * xiSpectralPoint q) s
        rw [norm_sub_rev, hI] at this
        linarith
      · rw [← norm_pos_iff]
        have := norm_sub_norm_le (I * xiSpectralPoint q) (-s)
        rw [show I * xiSpectralPoint q - -s = s + I * xiSpectralPoint q by ring, hI, norm_neg] at this
        linarith
  · -- the majorant bound
    intro q hq s hs
    have hsmem := hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    have hsn := hball_norm s hsmem
    rw [norm_mul]
    by_cases hqA : q ∈ A
    · have hqB : q ∈ B := Finset.mem_filter.mpr ⟨hqA, hq⟩
      have hd := hδ q hqB
      have hm : δ₀ / 2 ≤ ‖s - I * xiSpectralPoint q‖ := by
        have := norm_sub_norm_le (s₁ - I * xiSpectralPoint q) (s₁ - s)
        rw [show s₁ - I * xiSpectralPoint q - (s₁ - s) = s - I * xiSpectralPoint q by ring] at this
        rw [norm_sub_rev] at hs
        linarith [hd.trans (min_le_left _ _)]
      have hp : δ₀ / 2 ≤ ‖s + I * xiSpectralPoint q‖ := by
        have := norm_sub_norm_le (s₁ + I * xiSpectralPoint q) (s₁ - s)
        rw [show s₁ + I * xiSpectralPoint q - (s₁ - s) = s + I * xiSpectralPoint q by ring] at this
        rw [norm_sub_rev] at hs
        linarith [hd.trans (min_le_right _ _)]
      have hatom := norm_atom_le_of_dist (by positivity) (by positivity) (by positivity) hsn.1 hm hp
      dsimp only [u]
      rw [if_pos hqA]
      exact mul_le_mul (hW q) hatom (norm_nonneg _) hC
    · have hγ : K < ‖xiSpectralPoint q‖ := by
        by_contra hle
        exact hqA ((hAmem q).mpr (not_lt.mp hle))
      have hI : ‖I * xiSpectralPoint q‖ = ‖xiSpectralPoint q‖ := by
        rw [norm_mul, norm_I, one_mul]
      have hm : ‖xiSpectralPoint q‖ / 4 ≤ ‖s - I * xiSpectralPoint q‖ := by
        have := norm_sub_norm_le (I * xiSpectralPoint q) s
        rw [norm_sub_rev, hI] at this
        linarith [hsn.2]
      have hp : ‖xiSpectralPoint q‖ / 4 ≤ ‖s + I * xiSpectralPoint q‖ := by
        have := norm_sub_norm_le (I * xiSpectralPoint q) (-s)
        rw [show I * xiSpectralPoint q - -s = s + I * xiSpectralPoint q by ring, hI, norm_neg] at this
        linarith [hsn.2]
      have hγpos : 0 < ‖xiSpectralPoint q‖ := by linarith
      have hatom := norm_atom_le_of_dist (by positivity) (by positivity) (by positivity) hsn.1 hm hp
      dsimp only [u]
      rw [if_neg hqA]
      calc ‖W q‖ * ‖suzukiPsiLaplaceAtom s (xiSpectralPoint q)‖
          ≤ C * (1 / ((‖s₁‖ / 2) * (‖xiSpectralPoint q‖ / 4) * (‖xiSpectralPoint q‖ / 4))) :=
            mul_le_mul (hW q) hatom (norm_nonneg _) hC
        _ = C * (32 / ‖s₁‖) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
            field_simp
            ring

/-- **Analyticity of the partial atom series away from its remaining poles.** -/
theorem analyticAt_weightedScrewContinuationExcept {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (E : Finset XiZeroCopy) {s₁ : ℂ} (hre : 0 < s₁.re)
    (hnot : ∀ q, q ∉ E → I * xiSpectralPoint q ≠ s₁ ∧ -(I * xiSpectralPoint q) ≠ s₁) :
    AnalyticAt ℂ (weightedScrewContinuationExcept W E) s₁ := by
  obtain ⟨ρ, hρ, u, hu, hu0, hball_re, hball_ne, hball_le⟩ :=
    exists_uniform_atom_bound W hC hW E hre hnot
  have hdiff : DifferentiableOn ℂ (weightedScrewContinuationExcept W E) (Metric.ball s₁ ρ) := by
    unfold weightedScrewContinuationExcept
    apply Complex.differentiableOn_tsum_of_summable_norm (u := u) hu
    · intro q
      by_cases hq : q ∈ E
      · simp only [hq, if_true]
        exact differentiableOn_const 0
      · simp only [hq, if_false]
        refine (differentiableOn_atom_of_ne ?_ ?_ ?_).const_mul _
        · intro s hs
          have := hball_re s (Metric.ball_subset_closedBall hs)
          intro h0
          rw [h0, zero_re] at this
          exact lt_irrefl _ this
        · intro s hs
          exact (hball_ne q hq s (Metric.ball_subset_closedBall hs)).1
        · intro s hs
          exact (hball_ne q hq s (Metric.ball_subset_closedBall hs)).2
    · exact Metric.isOpen_ball
    · intro q s hs
      by_cases hq : q ∈ E
      · simp only [hq, if_true, norm_zero]
        exact hu0 q
      · simp only [hq, if_false]
        exact hball_le q hq s (Metric.ball_subset_closedBall hs)
  exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))

theorem weightedScrewContinuationExcept_empty :
    weightedScrewContinuationExcept W ∅ = weightedScrewLaplaceContinuation W := by
  funext s
  unfold weightedScrewContinuationExcept weightedScrewLaplaceContinuation
  simp

theorem analyticOnNhd_weightedScrewLaplaceContinuation_punctured {C : ℝ} (hC : 0 ≤ C)
    (hW : ∀ q, ‖W q‖ ≤ C) :
    AnalyticOnNhd ℂ (weightedScrewLaplaceContinuation W) rightHalfPunctured := by
  intro s₁ hs₁
  have h := analyticAt_weightedScrewContinuationExcept W hC hW ∅ hs₁.1 (fun q _ =>
    ⟨fun h => hs₁.2 (Or.inl ⟨q, h⟩), fun h => hs₁.2 (Or.inr ⟨q, h⟩)⟩)
  rwa [weightedScrewContinuationExcept_empty] at h

/-- **Identity theorem on the punctured half-plane.** -/
theorem weightedScrewLaplace_eqOn_punctured {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) :
    EqOn (weightedScrewLaplace W) (weightedScrewLaplaceContinuation W) rightHalfPunctured := by
  have hF := analyticOnNhd_weightedScrewLaplace_rightHalf W hC hW hpos hreal
  have hF' : AnalyticOnNhd ℂ (weightedScrewLaplace W) rightHalfPunctured := fun s hs => hF s hs.1
  have hG := analyticOnNhd_weightedScrewLaplaceContinuation_punctured W hC hW
  have hone : (1 : ℂ) ∈ rightHalfPunctured := ⟨by simp, one_notMem_spectralPoleSet⟩
  have hev : weightedScrewLaplace W =ᶠ[𝓝 (1 : ℂ)] weightedScrewLaplaceContinuation W := by
    have hopen : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact weightedScrewLaplace_eq_continuation W hC hW hs
  exact hF'.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_rightHalfPunctured hone hev

/-- Decomposition of the full series into a finite part and the partial series. -/
theorem weightedScrewLaplaceContinuation_eq_sum_add_except (E : Finset XiZeroCopy) {s : ℂ}
    (hsum : Summable fun q : XiZeroCopy => W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q)) :
    weightedScrewLaplaceContinuation W s =
      (∑ q ∈ E, W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q)) +
        weightedScrewContinuationExcept W E s := by
  unfold weightedScrewLaplaceContinuation weightedScrewContinuationExcept
  have h1 : Summable fun q : XiZeroCopy =>
      if q ∈ E then W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q) else 0 :=
    summable_of_ne_finset_zero (s := E) fun q hq => by simp [hq]
  have h2 : Summable fun q : XiZeroCopy =>
      if q ∈ E then 0 else W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q) := by
    refine (hsum.sub h1).congr fun q => ?_
    split_ifs <;> simp
  have hsplit : (fun q : XiZeroCopy => W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q)) =
      fun q => (if q ∈ E then W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q) else 0) +
        (if q ∈ E then 0 else W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q)) := by
    funext q
    split_ifs <;> simp
  rw [hsplit, h1.tsum_add h2, tsum_eq_sum (s := E) (fun q hq => by simp [hq])]
  congr 1
  exact Finset.sum_congr rfl fun q hq => by simp [hq]

/-- **Off-line zeros contradict positivity of a nondegenerate weighted screw divisor.** -/
theorem riemannHypothesis_of_weighted_positive {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hWpt : ∀ q q' : XiZeroCopy, xiSpectralPoint q' = xiSpectralPoint q → W q' = W q)
    (hWeven : ∀ q q' : XiZeroCopy, xiSpectralPoint q' = -xiSpectralPoint q → W q' = W q)
    (hWne : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → W q ≠ 0)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  by_contra hq
  have him : (xiSpectralPoint q).im ≠ 0 := fun h0 =>
    hq ⟨(xiSpectralPoint q).re, by apply Complex.ext <;> simp [h0]⟩
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : XiZeroCopy, (xiSpectralPoint q₀).im < 0 := by
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨q, h⟩
    · refine ⟨xiZeroCopyReflectEquiv q, ?_⟩
      rw [xiSpectralPoint_reflect, neg_im]
      linarith
  set γ₀ : ℂ := xiSpectralPoint q₀ with hγ₀
  set s₀ : ℂ := I * γ₀ with hs₀
  have hre0 : 0 < s₀.re := by
    rw [hs₀, mul_re, I_re, I_im]
    simp only [zero_mul, one_mul, zero_sub]
    linarith
  have hs₀ne : s₀ ≠ 0 := by
    intro h
    rw [h, zero_re] at hre0
    exact lt_irrefl _ hre0
  -- the exceptional copies `γ_q = ±γ₀`
  set E : Finset XiZeroCopy := (finite_xiZeroCopy_norm_le ‖γ₀‖).toFinset.filter
    (fun q => xiSpectralPoint q = γ₀ ∨ xiSpectralPoint q = -γ₀) with hE
  have hEmem : ∀ q, q ∈ E ↔ (xiSpectralPoint q = γ₀ ∨ xiSpectralPoint q = -γ₀) := by
    intro q
    rw [hE, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      show ‖xiSpectralPoint q‖ ≤ ‖γ₀‖
      rcases h with h | h <;> rw [h] <;> simp
  have hq₀E : q₀ ∈ E := (hEmem q₀).mpr (Or.inl rfl)
  have hnot : ∀ q, q ∉ E → I * xiSpectralPoint q ≠ s₀ ∧ -(I * xiSpectralPoint q) ≠ s₀ := by
    intro q hq
    constructor
    · intro h
      apply hq
      rw [hEmem]
      left
      exact mul_left_cancel₀ I_ne_zero h
    · intro h
      apply hq
      rw [hEmem]
      right
      have h' : I * xiSpectralPoint q = I * -γ₀ := by
        rw [hs₀] at h
        linear_combination (-1 : ℂ) * h
      exact mul_left_cancel₀ I_ne_zero h'
  have hWE : ∀ q ∈ E, W q = W q₀ := by
    intro q hq
    rcases (hEmem q).mp hq with h | h
    · exact hWpt q₀ q h
    · exact hWeven q₀ q h
  -- analytic data
  have hF := analyticOnNhd_weightedScrewLaplace_rightHalf W hC hW hpos hreal
  have hEq := weightedScrewLaplace_eqOn_punctured W hC hW hpos hreal
  have hrest := analyticAt_weightedScrewContinuationExcept W hC hW E hre0 hnot
  obtain ⟨ρ, hρ, u, hu, hu0, hball_re, hball_ne, hball_le⟩ :=
    exists_uniform_atom_bound W hC hW E hre0 hnot
  -- the approaching sequence `s_n = s₀ + ρ/(n+2)`
  let c : ℕ → ℝ := fun n => ρ / ((n : ℝ) + 2)
  let sn : ℕ → ℂ := fun n => s₀ + (c n : ℂ)
  have hc_pos : ∀ n, 0 < c n := fun n => by dsimp only [c]; positivity
  have hc_le : ∀ n, c n ≤ ρ / 2 := fun n => by
    dsimp only [c]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hc_tend : Tendsto c atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h2 := h1.inv_tendsto_atTop.const_mul ρ
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    dsimp only [c]
    rw [div_eq_mul_inv]
    rfl
  have hcC_tend : Tendsto (fun n => (c n : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hc_tend
    rw [Complex.ofReal_zero] at this
    exact this
  have hsn_ball : ∀ n, sn n ∈ Metric.closedBall s₀ ρ := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp only [sn]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc_pos n)]
    linarith [hc_le n]
  have hsn_ne_s₀ : ∀ n, sn n ≠ s₀ := by
    intro n h
    dsimp only [sn] at h
    have : (c n : ℂ) = 0 := by linear_combination h
    exact (hc_pos n).ne' (by exact_mod_cast this)
  have hsn_re : ∀ n, 0 < (sn n).re := fun n => hball_re _ (hsn_ball n)
  have hsn_mem : ∀ n, sn n ∈ rightHalfPunctured := by
    intro n
    refine ⟨hsn_re n, ?_⟩
    rintro (⟨q, hq⟩ | ⟨q, hq⟩)
    · change I * xiSpectralPoint q = sn n at hq
      by_cases hqE : q ∈ E
      · rcases (hEmem q).mp hqE with h | h
        · rw [h] at hq
          exact hsn_ne_s₀ n hq.symm
        · rw [h] at hq
          have := hsn_re n
          rw [← hq, mul_neg, neg_re] at this
          linarith
      · exact (hball_ne q hqE _ (hsn_ball n)).1 (by rw [hq]; ring)
    · change -(I * xiSpectralPoint q) = sn n at hq
      by_cases hqE : q ∈ E
      · rcases (hEmem q).mp hqE with h | h
        · rw [h] at hq
          have := hsn_re n
          rw [← hq, neg_re] at this
          linarith
        · rw [h] at hq
          apply hsn_ne_s₀ n
          rw [← hq]
          ring
      · exact (hball_ne q hqE _ (hsn_ball n)).2 (by rw [← hq]; ring)
  have hsn_tend : Tendsto sn atTop (𝓝 s₀) := by
    have := hcC_tend.const_add s₀
    simpa using this
  -- summability of the full series at `s_n`
  have hsum : ∀ n, Summable fun q : XiZeroCopy =>
      W q * suzukiPsiLaplaceAtom (sn n) (xiSpectralPoint q) := by
    intro n
    have hfin : Summable fun q : XiZeroCopy =>
        if q ∈ E then ‖W q * suzukiPsiLaplaceAtom (sn n) (xiSpectralPoint q)‖ else 0 :=
      summable_of_ne_finset_zero (s := E) fun q hq => by simp [hq]
    refine Summable.of_norm_bounded (g := fun q => u q +
      (if q ∈ E then ‖W q * suzukiPsiLaplaceAtom (sn n) (xiSpectralPoint q)‖ else 0))
      (hu.add hfin) fun q => ?_
    by_cases hq : q ∈ E
    · simp only [hq, if_true]
      linarith [hu0 q]
    · simp only [hq, if_false, add_zero]
      exact hball_le q hq _ (hsn_ball n)
  -- the finite part along the sequence
  have hatomE : ∀ n, ∀ q ∈ E,
      (c n : ℂ) * suzukiPsiLaplaceAtom (sn n) (xiSpectralPoint q) = 1 / (sn n * (sn n + s₀)) := by
    intro n q hq
    have hsq : xiSpectralPoint q ^ 2 = γ₀ ^ 2 := by
      rcases (hEmem q).mp hq with h | h <;> rw [h] <;> ring
    unfold suzukiPsiLaplaceAtom
    rw [hsq]
    have hs₀sq : s₀ ^ 2 = -γ₀ ^ 2 := by rw [hs₀, mul_pow, I_sq]; ring
    have hfac : sn n ^ 2 + γ₀ ^ 2 = (c n : ℂ) * (sn n + s₀) := by
      have : (sn n : ℂ) - s₀ = (c n : ℂ) := by dsimp only [sn]; ring
      rw [← this, ← sub_neg_eq_add (sn n ^ 2), ← hs₀sq]
      ring
    rw [hfac]
    have hc0 : (c n : ℂ) ≠ 0 := by exact_mod_cast (hc_pos n).ne'
    have hsn0 : sn n ≠ 0 := by
      intro h
      have := hsn_re n
      rw [h, zero_re] at this
      exact lt_irrefl _ this
    have hsum0 : sn n + s₀ ≠ 0 := by
      intro h
      have h1 := hsn_re n
      have h2 := congrArg Complex.re h
      rw [add_re, zero_re] at h2
      linarith
    field_simp
  -- limit of `c_n · G(s_n)`
  have hlimG : Tendsto (fun n => (c n : ℂ) * weightedScrewLaplaceContinuation W (sn n)) atTop
      (𝓝 ((∑ q ∈ E, W q) * (1 / (s₀ * (s₀ + s₀))) + 0 * weightedScrewContinuationExcept W E s₀)) := by
    have hfun : (fun n => (c n : ℂ) * weightedScrewLaplaceContinuation W (sn n)) =
        fun n => (∑ q ∈ E, W q) * (1 / (sn n * (sn n + s₀))) +
          (c n : ℂ) * weightedScrewContinuationExcept W E (sn n) := by
      funext n
      rw [weightedScrewLaplaceContinuation_eq_sum_add_except W E (hsum n), mul_add, Finset.mul_sum,
        Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [← hatomE n q hq]
      ring
    rw [hfun]
    refine Tendsto.add (tendsto_const_nhds.mul ?_) (hcC_tend.mul ?_)
    · have hden : Tendsto (fun n => sn n * (sn n + s₀)) atTop (𝓝 (s₀ * (s₀ + s₀))) :=
        hsn_tend.mul (hsn_tend.add_const s₀)
      have hden0 : s₀ * (s₀ + s₀) ≠ 0 := by
        refine mul_ne_zero hs₀ne ?_
        intro h
        have := congrArg Complex.re h
        rw [add_re, zero_re] at this
        linarith
      simpa [one_div] using hden.inv₀ hden0
    · exact (hrest.continuousAt.tendsto).comp hsn_tend
  -- limit of `c_n · F(s_n)`
  have hlimF : Tendsto (fun n => (c n : ℂ) * weightedScrewLaplace W (sn n)) atTop
      (𝓝 (0 * weightedScrewLaplace W s₀)) :=
    hcC_tend.mul (((hF s₀ hre0).continuousAt.tendsto).comp hsn_tend)
  have heqn : (fun n => (c n : ℂ) * weightedScrewLaplace W (sn n)) =
      fun n => (c n : ℂ) * weightedScrewLaplaceContinuation W (sn n) := by
    funext n
    rw [hEq (hsn_mem n)]
  rw [heqn] at hlimF
  have hzero := tendsto_nhds_unique hlimG hlimF
  rw [zero_mul, add_zero, zero_mul] at hzero
  -- contradiction with the nonzero finite part
  have hsumE : ∑ q ∈ E, W q = (E.card : ℂ) * W q₀ := by
    rw [Finset.sum_congr rfl hWE, Finset.sum_const, nsmul_eq_mul]
  have hW0 : W q₀ ≠ 0 := hWne q₀ hq₀.ne
  have hcard : (E.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨q₀, hq₀E⟩).ne'
  have hden0 : s₀ * (s₀ + s₀) ≠ 0 := by
    refine mul_ne_zero hs₀ne ?_
    intro h
    have := congrArg Complex.re h
    rw [add_re, zero_re] at this
    linarith
  rw [hsumE] at hzero
  have : (E.card : ℂ) * W q₀ * (1 / (s₀ * (s₀ + s₀))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcard hW0) (one_div_ne_zero hden0)
  exact this hzero

end

end RHTower
