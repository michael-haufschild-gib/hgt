import GaloisForLFunctions.SquareRootThreshold.LagGridsSeeAttainedTops

/-!
# Chains hide from lag grids

A one-sided bound on a lag grid excludes every attained top (`exists_re_gt_of_grid_lag_ge`):
under a grid bound only chains, off-line depths without a largest value, can remain. This is the
true limit of grids. At the level of exponential sums a chain can keep a one-sided bound on the
grid while the same sum is unbounded on the continuum of lags (`exists_chain_hidden_from_grid`).

* **Aliasing.** On the grid `v = k` a height is seen only modulo `2π`. The chain `δ_n ↑ ¼` with
  heights `γ_n = 2π(n + 1) + θ_n`, `θ_n ↓ 0`, looks on the grid like the exponents `δ_n + iθ_n`,
  which accumulate at the real point `¼`. The grid is not resonant: no two heights differ by a
  multiple of `2π`, and none is one (`gridChainExp_im_sub_eq`, `gridChainExp_im_ne`).
* **Hiding** (`re_gridChainSum_nat_nonpos`). With coefficients `−c_n` the grid values are
  `−Σ_n c_n e^{δ_n k} cos(θ_n k)`. The phases are so small that `cos(θ_n k) ≥ ½` until the next
  exponent dominates (`gridChainTime`), so at every `k` the leading term is positive and outweighs
  all earlier ones (`gridChain_cos_sum_nonneg`).
* **Continuous lags see the chain** (`not_bddAbove_re_gridChainSum`). Every height is at least `2π`
  from the real axis and the heights are separated, so Landau's theorem continues the Laplace
  transform of a one-sided bounded real part to `Re s > 0`, and every residue with `Re λ > 0`
  vanishes (`eq_zero_of_re_tsum_exp_le_of_separated`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Landau for real parts with separated heights -/

/-- The exponents `λ_t` and `conj λ_t` of the real part of `Σ_t q_t e^{λ_t v}`. -/
def doubledExp {ι : Type*} (lam : ι → ℂ) : ι ⊕ ι → ℂ := Sum.elim lam fun t => conj (lam t)

/-- The coefficients `q_t/2` and `conj q_t/2` of the real part of `Σ_t q_t e^{λ_t v}`. -/
def doubledCoeff {ι : Type*} (q : ι → ℂ) : ι ⊕ ι → ℂ :=
  Sum.elim (fun t => q t / 2) fun t => conj (q t) / 2

@[simp] theorem doubledExp_inl {ι : Type*} (lam : ι → ℂ) (t : ι) :
    doubledExp lam (Sum.inl t) = lam t := rfl

@[simp] theorem doubledExp_inr {ι : Type*} (lam : ι → ℂ) (t : ι) :
    doubledExp lam (Sum.inr t) = conj (lam t) := rfl

@[simp] theorem doubledCoeff_inl {ι : Type*} (q : ι → ℂ) (t : ι) :
    doubledCoeff q (Sum.inl t) = q t / 2 := rfl

@[simp] theorem doubledCoeff_inr {ι : Type*} (q : ι → ℂ) (t : ι) :
    doubledCoeff q (Sum.inr t) = conj (q t) / 2 := rfl

/-- **Landau for the real part of an exponential sum with separated heights.** Let
`Σ_t |q_t| < ∞`, `|Re λ_t| ≤ ½`, `Im λ_t ≥ η > 0`, and `|Im λ_s − Im λ_t| ≥ η` for `s ≠ t`. If
`Re Σ_t q_t e^{λ_t v} ≤ M` for all `v ≥ 0`, then `q_t = 0` whenever `Re λ_t > 0`. -/
theorem eq_zero_of_re_tsum_exp_le_of_separated {ι : Type*} [Countable ι] {lam q : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) (hre : ∀ t, |(lam t).re| ≤ 1 / 2) {η : ℝ} (hη : 0 < η)
    (him : ∀ t, η ≤ (lam t).im) (hsep : ∀ s t, s ≠ t → η ≤ |(lam s).im - (lam t).im|) {M : ℝ}
    (hM : ∀ v : ℝ, 0 ≤ v → (∑' t, q t * cexp (lam t * v)).re ≤ M) {t₁ : ι}
    (h₁ : 0 < (lam t₁).re) : q t₁ = 0 := by
  classical
  have hQs : Summable fun T => ‖doubledCoeff q T‖ :=
    Summable.sum _ ((hq.div_const 2).congr fun t => by simp)
      ((hq.div_const 2).congr fun t => by simp)
  have hΛre : ∀ T, (doubledExp lam T).re ≤ 1 / 2 := by
    rintro (t | t) <;> simpa using (abs_le.mp (hre t)).2
  have hterm : ∀ t, ∀ v : ℝ, ‖q t * cexp (lam t * v)‖ ≤ ‖q t‖ * Real.exp (|v| / 2) := by
    intro t v
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (lam t * (v : ℂ)).re = (lam t).re * v := by simp
    rw [this]
    calc (lam t).re * v ≤ |(lam t).re * v| := le_abs_self _
      _ = |(lam t).re| * |v| := abs_mul _ _
      _ ≤ 1 / 2 * |v| := mul_le_mul_of_nonneg_right (hre t) (abs_nonneg _)
      _ = |v| / 2 := by ring
  have hS : ∀ v : ℝ, Summable fun t => q t * cexp (lam t * v) := fun v =>
    Summable.of_norm_bounded (hq.mul_right (Real.exp (|v| / 2))) (hterm · v)
  have hconj : ∀ t, ∀ v : ℝ,
      conj (q t * cexp (lam t * v)) = conj (q t) * cexp (conj (lam t) * v) :=
    fun t v => by rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  -- `φ(v) = Re Σ_t q_t e^{λ_t v}` is the doubled exponential sum
  have hφrep : ∀ v : ℝ, (((∑' t, q t * cexp (lam t * v)).re : ℝ) : ℂ) =
      ∑' T, doubledCoeff q T * cexp (doubledExp lam T * v) := by
    intro v
    have h1 : Summable fun t => doubledCoeff q (Sum.inl t) * cexp (doubledExp lam (Sum.inl t) * v) :=
      ((hS v).div_const 2).congr fun t => by simp only [doubledCoeff_inl, doubledExp_inl]; ring
    have h2 : Summable fun t => doubledCoeff q (Sum.inr t) * cexp (doubledExp lam (Sum.inr t) * v) :=
      ((Summable.of_norm_bounded (hS v).norm fun t => by
        rw [← hconj, Complex.norm_conj]).div_const 2).congr fun t => by
          simp only [doubledCoeff_inr, doubledExp_inr]; ring
    rw [Summable.tsum_sum h1 h2]
    have e1 : ∑' t, doubledCoeff q (Sum.inl t) * cexp (doubledExp lam (Sum.inl t) * v) =
        (∑' t, q t * cexp (lam t * v)) / 2 := by
      rw [← tsum_div_const]
      exact tsum_congr fun t => by simp only [doubledCoeff_inl, doubledExp_inl]; ring
    have e2 : ∑' t, doubledCoeff q (Sum.inr t) * cexp (doubledExp lam (Sum.inr t) * v) =
        conj (∑' t, q t * cexp (lam t * v)) / 2 := by
      rw [Complex.conj_tsum, ← tsum_div_const]
      exact tsum_congr fun t => by simp only [doubledCoeff_inr, doubledExp_inr, hconj]; ring
    rw [e1, e2, Complex.re_eq_add_conj]
    ring
  set φ : ℝ → ℝ := fun v => (∑' t, q t * cexp (lam t * v)).re with hφ
  -- the inputs of Landau's theorem
  have hφc : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hon : ContinuousOn (fun v : ℝ => ∑' t, q t * cexp (lam t * v)) (Ioo (x - 1) (x + 1)) :=
      continuousOn_tsum (fun t => by fun_prop) (hq.mul_right (Real.exp ((|x| + 1) / 2)))
        fun t v hv => (hterm t v).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          have : |v| ≤ |x| + 1 := by
            rw [abs_le]; constructor <;> linarith [hv.1, hv.2, neg_abs_le x, le_abs_self x]
          linarith)) (norm_nonneg _))
    exact Complex.continuous_re.continuousAt.comp
      (hon.continuousAt (Ioo_mem_nhds (by linarith) (by linarith)))
  have hKb : ∀ u, 0 < u → |φ u| ≤ (∑' t, ‖q t‖) * Real.exp (u / 2) := fun u hu => by
    refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm (hS u).norm).trans ?_)
    rw [← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun t => ?_) (hS u).norm (hq.mul_right _)
    simpa [abs_of_pos hu] using hterm t u
  have hΛan : ∀ t : ℝ, 0 < t → AnalyticAt ℂ (resolventSum (doubledExp lam) (doubledCoeff q)) t := by
    intro t _
    have hgap : ∀ (T : ι ⊕ ι) (s : ℂ), s ∈ Metric.ball (t : ℂ) (η / 2) →
        η / 2 ≤ ‖s - doubledExp lam T‖ := by
      intro T s hs
      rw [Metric.mem_ball, Complex.dist_eq] at hs
      have h2 : |s.im| ≤ ‖s - t‖ := by
        have := Complex.abs_im_le_norm (s - t); simpa using this
      have hΛim : η ≤ |(doubledExp lam T).im| := by
        rcases T with T | T
        · simpa [abs_of_pos (hη.trans_le (him T))] using him T
        · simpa [abs_of_pos (hη.trans_le (him T))] using him T
      have h3 : |(s - doubledExp lam T).im| ≤ ‖s - doubledExp lam T‖ := Complex.abs_im_le_norm _
      have h4 : |(doubledExp lam T).im| ≤ |(s - doubledExp lam T).im| + |s.im| := by
        rw [Complex.sub_im]
        calc |(doubledExp lam T).im| = |-(s.im - (doubledExp lam T).im) + s.im| := by ring_nf
          _ ≤ |-(s.im - (doubledExp lam T).im)| + |s.im| := abs_add_le _ _
          _ = |s.im - (doubledExp lam T).im| + |s.im| := by rw [abs_neg]
      linarith
    have hdiff : DifferentiableOn ℂ (resolventSum (doubledExp lam) (doubledCoeff q))
        (Metric.ball (t : ℂ) (η / 2)) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun T => ‖doubledCoeff q T‖ / (η / 2)) (hQs.div_const _) (fun T => ?_)
        Metric.isOpen_ball (fun T s hs => ?_)
      · refine (differentiableOn_const _).div (differentiableOn_id.sub_const _) fun s hs h0 => ?_
        have := hgap T s hs
        rw [h0, norm_zero] at this
        linarith
      · rw [norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (half_pos hη) (hgap T s hs)
    exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hη)))
  have hΛφ : ∀ s : ℂ, 1 / 2 < s.re → ∫ u in Ioi (0 : ℝ), ((φ u : ℝ) : ℂ) * cexp (-s * u) =
      resolventSum (doubledExp lam) (doubledCoeff q) s := fun s hs => by
    simp_rw [hφ, hφrep]
    exact integral_tsum_exp_mul_exp_neg hQs hΛre hs
  obtain ⟨F, hF, hFG⟩ := exists_differentiable_extension_of_le_exp hφc.measurable hKb le_rfl
    (by norm_num) (M := M) (fun u hu => by simpa using hM u hu) hΛan hΛφ
  -- the residue at `λ_{t₁}`: its line carries no other exponent
  have hline : ∀ T, |(doubledExp lam T).im - (lam t₁).im| < η → T = Sum.inl t₁ := by
    rintro (s | s) hs
    · by_contra hne
      exact absurd (hsep s t₁ fun h => hne (by rw [h])) (not_le.mpr (by simpa using hs))
    · exfalso
      have h1 := him s
      have h2 := him t₁
      have : |(doubledExp lam (Sum.inr s)).im - (lam t₁).im| = (lam s).im + (lam t₁).im := by
        simp only [doubledExp_inr, Complex.conj_im]
        rw [abs_of_neg (by linarith)]; ring
      linarith
  have hΛ₁ : doubledExp lam (Sum.inl t₁) = lam t₁ := rfl
  have h0 := eq_zero_of_resolventSum_eq_differentiable (lam := doubledExp lam)
    (q := doubledCoeff q) hQs (A := 1 / 2) (Sum.inl t₁)
    (fun T hT => by rw [hline T (by rw [hT, hΛ₁, sub_self, abs_zero]; exact hη)])
    (fun T hT => hline T (by rw [hT, hΛ₁, sub_self, abs_zero]; exact hη)) hη
    (fun T hT => by rw [hline T (by rwa [hΛ₁] at hT)]) (c := 0) h₁ hF hFG
  simpa using h0

/-! ### The chain -/

/-- The depths `δ_n = (1 − 2^{−(n+1)})/4`, increasing to `¼`. -/
def gridChainDepth (n : ℕ) : ℝ := (1 - (1 / 2) ^ (n + 1)) / 4

/-- The weights `c_n = 2^{−(n+1)}`. -/
def gridChainWeight (n : ℕ) : ℝ := (1 / 2) ^ (n + 1)

/-- The lag `(n + 3) 2^{n+4}` beyond which `e^{δ_{n+1}v}` outweighs `e^{δ_n v}` by `2/c_{n+1}`. -/
def gridChainTime (n : ℕ) : ℝ := (n + 3) * 2 ^ (n + 4)

/-- The phases `θ_n = π/(3 gridChainTime n)`: `cos(θ_n v) ≥ ½` for `0 ≤ v ≤ gridChainTime n`. -/
def gridChainPhase (n : ℕ) : ℝ := π / (3 * gridChainTime n)

/-- The exponents `δ_n + i(2π(n + 1) + θ_n)`. -/
def gridChainExp (n : ℕ) : ℂ := (gridChainDepth n : ℂ) + ((2 * π * (n + 1) + gridChainPhase n : ℝ) : ℂ) * I

/-- The chain `Σ_n −c_n e^{λ_n v}`. -/
def gridChainSum (v : ℝ) : ℂ := ∑' n, -(gridChainWeight n : ℂ) * cexp (gridChainExp n * v)

theorem gridChainDepth_pos (n : ℕ) : 0 < gridChainDepth n := by
  have : (1 / 2 : ℝ) ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  unfold gridChainDepth; linarith

theorem gridChainDepth_lt (n : ℕ) : gridChainDepth n < 1 / 4 := by
  have : (0 : ℝ) < (1 / 2) ^ (n + 1) := by positivity
  unfold gridChainDepth; linarith

theorem gridChainDepth_succ_sub (n : ℕ) :
    gridChainDepth (n + 1) - gridChainDepth n = 1 / 2 ^ (n + 4) := by
  unfold gridChainDepth
  rw [one_div_pow, one_div_pow, show n + 1 + 1 = n + 1 + 1 from rfl, pow_succ (2 : ℝ) (n + 1),
    show n + 4 = n + 1 + 3 by ring, pow_add]
  field_simp
  ring

theorem gridChainDepth_strictMono : StrictMono gridChainDepth :=
  strictMono_nat_of_lt_succ fun n => by
    have := gridChainDepth_succ_sub n
    have : (0 : ℝ) < 1 / 2 ^ (n + 4) := by positivity
    linarith

theorem gridChainTime_pos (n : ℕ) : 0 < gridChainTime n := by unfold gridChainTime; positivity

theorem gridChainTime_strictMono : StrictMono gridChainTime :=
  strictMono_nat_of_lt_succ fun n => by
    unfold gridChainTime
    have hp : (0 : ℝ) < 2 ^ (n + 4) := by positivity
    have e : (2 : ℝ) ^ (n + 1 + 4) = 2 ^ (n + 4) * 2 := by ring
    rw [e]
    push_cast
    nlinarith

theorem le_gridChainTime (n : ℕ) : (n : ℝ) ≤ gridChainTime n := by
  unfold gridChainTime
  have h1 : (1 : ℝ) ≤ 2 ^ (n + 4) := one_le_pow₀ (by norm_num)
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem gridChainPhase_pos (n : ℕ) : 0 < gridChainPhase n := by
  unfold gridChainPhase; have := gridChainTime_pos n; positivity

theorem gridChainPhase_lt_one (n : ℕ) : gridChainPhase n < 1 := by
  unfold gridChainPhase
  have h : (48 : ℝ) ≤ gridChainTime n := by
    unfold gridChainTime
    have : (16 : ℝ) ≤ 2 ^ (n + 4) := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (n + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  rw [div_lt_one (by positivity)]
  linarith [Real.pi_lt_four]

/-- `cos(θ_n x) ≥ ½` for `0 ≤ x ≤ gridChainTime n`. -/
theorem half_le_cos_gridChainPhase {n : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ gridChainTime n) :
    1 / 2 ≤ Real.cos (gridChainPhase n * x) := by
  rw [← Real.cos_pi_div_three]
  have hK := gridChainTime_pos n
  have h1 : gridChainPhase n * x ≤ π / 3 := by
    unfold gridChainPhase
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (gridChainPhase_pos n).le hx0)
    (by linarith [Real.pi_pos]) h1

/-- **Dominance.** For `x ≥ gridChainTime n`, `e^{δ_n x} ≤ ½ c_{n+1} e^{δ_{n+1} x}`. -/
theorem exp_gridChainDepth_le {n : ℕ} {x : ℝ} (hx : gridChainTime n ≤ x) :
    Real.exp (gridChainDepth n * x) ≤ gridChainWeight (n + 1) * Real.exp (gridChainDepth (n + 1) * x) / 2 := by
  have hgap : (n + 3 : ℝ) ≤ (gridChainDepth (n + 1) - gridChainDepth n) * x := by
    rw [gridChainDepth_succ_sub]
    unfold gridChainTime at hx
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    linarith
  have he : (2 : ℝ) ^ (n + 3) ≤ Real.exp ((gridChainDepth (n + 1) - gridChainDepth n) * x) := by
    calc (2 : ℝ) ^ (n + 3) ≤ Real.exp 1 ^ (n + 3) :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) _
      _ = Real.exp ((n + 3 : ℕ) * 1) := by rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by push_cast; linarith)
  have hsplit : Real.exp (gridChainDepth (n + 1) * x) =
      Real.exp ((gridChainDepth (n + 1) - gridChainDepth n) * x) * Real.exp (gridChainDepth n * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  unfold gridChainWeight
  have hpos := Real.exp_pos (gridChainDepth n * x)
  have h2 : (1 / 2 : ℝ) ^ (n + 1 + 1) * 2 ^ (n + 3) / 2 = 1 := by
    rw [show n + 1 + 1 = n + 2 by ring, one_div_pow]
    field_simp
    ring
  calc Real.exp (gridChainDepth n * x)
      = (1 / 2) ^ (n + 1 + 1) * 2 ^ (n + 3) / 2 * Real.exp (gridChainDepth n * x) := by rw [h2, one_mul]
    _ ≤ (1 / 2) ^ (n + 1 + 1) * Real.exp ((gridChainDepth (n + 1) - gridChainDepth n) * x) / 2 *
        Real.exp (gridChainDepth n * x) := by gcongr
    _ = _ := by ring

theorem sum_range_gridChainWeight (j : ℕ) :
    ∑ n ∈ Finset.range j, gridChainWeight n = 1 - (1 / 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, ih]; unfold gridChainWeight; ring

end GaloisForLFunctions.SquareRootThreshold
