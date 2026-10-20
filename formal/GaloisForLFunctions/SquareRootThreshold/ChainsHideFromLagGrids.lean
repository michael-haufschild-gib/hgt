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
      ((Summable.of_norm_bounded (f := fun t => conj (q t) * cexp (conj (lam t) * v))
        (hS v).norm fun t => by
          rw [← hconj, Complex.norm_conj]).div_const 2).congr fun t => by
          simp only [doubledCoeff_inr, doubledExp_inr]; ring
    rw [Summable.tsum_sum (f := fun T => doubledCoeff q T * cexp (doubledExp lam T * v)) h1 h2]
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

theorem summable_gridChainWeight : Summable gridChainWeight :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem gridChainWeight_pos (n : ℕ) : 0 < gridChainWeight n := by
  unfold gridChainWeight; positivity

theorem summable_gridChain_term (x : ℝ) : Summable fun n =>
    gridChainWeight n * Real.exp (gridChainDepth n * x) * Real.cos (gridChainPhase n * x) := by
  refine Summable.of_norm_bounded (summable_gridChainWeight.mul_right (Real.exp |x|)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (gridChainWeight_pos n),
    abs_of_pos (Real.exp_pos _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (gridChainWeight_pos n).le
  calc Real.exp (gridChainDepth n * x) * |Real.cos (gridChainPhase n * x)|
      ≤ Real.exp (gridChainDepth n * x) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp |x| := by
        rw [mul_one, Real.exp_le_exp]
        have h0 := gridChainDepth_pos n
        have h1 := gridChainDepth_lt n
        calc gridChainDepth n * x ≤ |gridChainDepth n * x| := le_abs_self _
          _ = gridChainDepth n * |x| := by rw [abs_mul, abs_of_pos h0]
          _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ = |x| := one_mul _

/-- The balance at the first lag `x ≤ chainTime j`: the leading term `c_j e^{δ_j x}/2` outweighs
`e^{δ_{j−1}x} Σ_{n<j} c_n`. -/
theorem gridChain_balance_nonneg {j : ℕ} {x : ℝ}
    (hmin : ∀ m < j, gridChainTime m < x) :
    0 ≤ -(Real.exp (gridChainDepth (j - 1) * x) * (1 - (1 / 2) ^ j)) +
      gridChainWeight j * Real.exp (gridChainDepth j * x) / 2 := by
  cases j with
  | zero =>
    have := gridChainWeight_pos 0
    simp only [pow_zero, sub_self, mul_zero, neg_zero, zero_add]
    positivity
  | succ m =>
    have hdom := exp_gridChainDepth_le (hmin m (Nat.lt_succ_self m)).le
    have h1 : (0 : ℝ) ≤ (1 / 2) ^ (m + 1) := by positivity
    have hE := Real.exp_pos (gridChainDepth m * x)
    simp only [Nat.add_sub_cancel]
    nlinarith

/-- **The chain stays positive.** For `x ≥ 0`, `Σ_n c_n e^{δ_n x} cos(θ_n x) ≥ 0`. At the first
`j` with `x ≤ chainTime j` the leading term `c_j e^{δ_j x}/2` outweighs all earlier terms, and all
later terms are positive. -/
theorem gridChain_cos_sum_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∑' n, gridChainWeight n * Real.exp (gridChainDepth n * x) *
      Real.cos (gridChainPhase n * x) := by
  classical
  have hex : ∃ j : ℕ, x ≤ gridChainTime j := by
    obtain ⟨j, hj⟩ := exists_nat_ge x
    exact ⟨j, hj.trans (le_gridChainTime j)⟩
  obtain ⟨j, hj, hmin⟩ : ∃ j, x ≤ gridChainTime j ∧ ∀ m < j, gridChainTime m < x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_le.mp (Nat.find_min hex hm)⟩
  set E := Real.exp (gridChainDepth (j - 1) * x) with hE
  set g : ℕ → ℝ := fun n => if n < j then -(gridChainWeight n * E) else
    if n = j then gridChainWeight j * Real.exp (gridChainDepth j * x) / 2 else 0 with hg
  have hag : ∀ n, g n ≤
      gridChainWeight n * Real.exp (gridChainDepth n * x) * Real.cos (gridChainPhase n * x) := by
    intro n
    have hw := gridChainWeight_pos n
    have he := Real.exp_pos (gridChainDepth n * x)
    simp only [hg]
    split_ifs with h1 h2
    · have hexp : Real.exp (gridChainDepth n * x) ≤ E := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (gridChainDepth_strictMono.monotone (by omega)) hx)
      have hcos := Real.neg_one_le_cos (gridChainPhase n * x)
      have h1 := mul_nonneg (mul_pos hw he).le (by linarith : 0 ≤ Real.cos (gridChainPhase n * x) + 1)
      have h2 := mul_le_mul_of_nonneg_left hexp hw.le
      linarith
    · subst h2
      have := half_le_cos_gridChainPhase hx hj
      nlinarith [mul_pos hw he]
    · have hn : x ≤ gridChainTime n := hj.trans (gridChainTime_strictMono.monotone (by omega))
      have := half_le_cos_gridChainPhase hx hn
      have hc : 0 ≤ Real.cos (gridChainPhase n * x) := by linarith
      positivity
  have hzero : ∀ n ∉ Finset.range (j + 1), g n = 0 := fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    simp only [hg]
    rw [if_neg (by omega), if_neg (by omega)]
  refine le_trans ?_ (Summable.tsum_le_tsum hag (summable_of_ne_finset_zero hzero)
    (summable_gridChain_term x))
  rw [tsum_eq_sum hzero, Finset.sum_range_succ]
  have hlow : ∑ n ∈ Finset.range j, g n = -(E * ∑ n ∈ Finset.range j, gridChainWeight n) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    simp only [hg]
    rw [if_pos hn]
    ring
  have hgj : g j = gridChainWeight j * Real.exp (gridChainDepth j * x) / 2 := by
    simp [hg]
  rw [hlow, hgj, sum_range_gridChainWeight]
  exact gridChain_balance_nonneg hmin

theorem gridChainExp_re (n : ℕ) : (gridChainExp n).re = gridChainDepth n := by
  simp [gridChainExp]

theorem gridChainExp_im (n : ℕ) :
    (gridChainExp n).im = 2 * π * (n + 1) + gridChainPhase n := by
  simp [gridChainExp]

/-- **The grid hides the chain.** At every integer lag `k`, `Re Σ_n −c_n e^{λ_n k} ≤ 0`: the
heights `2π(n + 1) + θ_n` are seen on the grid as `θ_n`. -/
theorem re_gridChainSum_nat_nonpos (k : ℕ) : (gridChainSum k).re ≤ 0 := by
  have hterm : ∀ n, (-(gridChainWeight n : ℂ) * cexp (gridChainExp n * (k : ℝ))).re =
      -(gridChainWeight n * Real.exp (gridChainDepth n * k) * Real.cos (gridChainPhase n * k)) := by
    intro n
    have hre : (gridChainExp n * ((k : ℝ) : ℂ)).re = gridChainDepth n * k := by
      simp [gridChainExp]
    have him : (gridChainExp n * ((k : ℝ) : ℂ)).im =
        gridChainPhase n * k + ((n + 1) * k : ℕ) * (2 * π) := by
      simp [gridChainExp]; ring
    rw [show -(gridChainWeight n : ℂ) = ((-gridChainWeight n : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_re, hre, him, Real.cos_add_nat_mul_two_pi]
    ring
  have hs : Summable fun n => -(gridChainWeight n : ℂ) * cexp (gridChainExp n * (k : ℝ)) := by
    refine Summable.of_norm_bounded
      (summable_gridChainWeight.mul_right (Real.exp (k : ℝ))) fun n => ?_
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gridChainWeight_pos n), Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (gridChainWeight_pos n).le
    have hre : (gridChainExp n * ((k : ℝ) : ℂ)).re = gridChainDepth n * k := by
      simp [gridChainExp]
    rw [hre]
    have := gridChainDepth_lt n
    nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  unfold gridChainSum
  rw [Complex.re_tsum hs]
  simp_rw [hterm]
  rw [tsum_neg]
  linarith [gridChain_cos_sum_nonneg (k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- **Continuous lags see the chain.** `Re Σ_n −c_n e^{λ_n v}` is not bounded above on `v ≥ 0`. -/
theorem not_bddAbove_re_gridChainSum :
    ¬ ∃ M : ℝ, ∀ v : ℝ, 0 ≤ v → (gridChainSum v).re ≤ M := by
  rintro ⟨M, hM⟩
  have hθ := gridChainPhase_pos
  have hθ1 := gridChainPhase_lt_one
  have h0 := eq_zero_of_re_tsum_exp_le_of_separated (lam := gridChainExp)
    (q := fun n => -(gridChainWeight n : ℂ))
    (summable_gridChainWeight.congr fun n => by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gridChainWeight_pos n)])
    (fun n => by
      rw [gridChainExp_re, abs_of_pos (gridChainDepth_pos n)]
      linarith [gridChainDepth_lt n])
    one_pos
    (fun n => by
      rw [gridChainExp_im]
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      nlinarith [Real.pi_gt_three, hθ n])
    (fun s t hst => by
      rw [gridChainExp_im, gridChainExp_im]
      have hst' : (1 : ℝ) ≤ |(s : ℝ) - t| := by
        rcases lt_or_gt_of_ne hst with h | h
        · have : (s : ℝ) + 1 ≤ t := by exact_mod_cast Nat.succ_le_of_lt h
          rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
        · have : (t : ℝ) + 1 ≤ s := by exact_mod_cast Nat.succ_le_of_lt h
          rw [abs_of_pos (by linarith)]; linarith
      have e : 2 * π * (s + 1) + gridChainPhase s - (2 * π * (t + 1) + gridChainPhase t) =
          2 * π * ((s : ℝ) - t) + (gridChainPhase s - gridChainPhase t) := by ring
      rw [e]
      have h1 : |gridChainPhase s - gridChainPhase t| < 1 := by
        rw [abs_lt]; constructor <;> linarith [hθ s, hθ t, hθ1 s, hθ1 t]
      have h2 : |2 * π * ((s : ℝ) - t)| = 2 * π * |(s : ℝ) - t| := by
        rw [abs_mul, abs_of_pos (by positivity)]
      have h3 := abs_sub_abs_le_abs_sub (2 * π * ((s : ℝ) - t)) (-(gridChainPhase s - gridChainPhase t))
      rw [sub_neg_eq_add, abs_neg, h2] at h3
      nlinarith [Real.pi_gt_three])
    (M := M) hM (t₁ := 0) (by rw [gridChainExp_re]; exact gridChainDepth_pos 0)
  have := gridChainWeight_pos 0
  have h0' : (gridChainWeight 0 : ℂ) = 0 := neg_eq_zero.mp h0
  exact absurd (Complex.ofReal_eq_zero.mp h0') this.ne'

/-- The grid `v = k` is not resonant for the heights of the chain: no two differ by a multiple of
`2π`. -/
theorem gridChainExp_im_sub_eq {n m : ℕ} {z : ℤ}
    (h : (gridChainExp n).im - (gridChainExp m).im = 2 * π * z) : n = m := by
  rw [gridChainExp_im, gridChainExp_im] at h
  set d : ℤ := z - n + m with hd
  have hθ : gridChainPhase n - gridChainPhase m = 2 * π * d := by
    rw [hd]; push_cast; linarith
  have habs : |gridChainPhase n - gridChainPhase m| < 1 := by
    rw [abs_lt]; constructor <;>
      linarith [gridChainPhase_pos n, gridChainPhase_pos m, gridChainPhase_lt_one n,
        gridChainPhase_lt_one m]
  have hd0 : d = 0 := by
    rw [hθ, abs_mul, abs_of_pos (by positivity)] at habs
    have : |(d : ℝ)| < 1 := by nlinarith [Real.pi_gt_three, abs_nonneg (d : ℝ)]
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at this
    exact Int.abs_lt_one_iff.mp this
  rw [hd0, Int.cast_zero, mul_zero, sub_eq_zero] at hθ
  unfold gridChainPhase at hθ
  have hK : gridChainTime n = gridChainTime m := by
    have hn := gridChainTime_pos n
    have hm := gridChainTime_pos m
    field_simp at hθ
    nlinarith [Real.pi_pos]
  exact gridChainTime_strictMono.injective hK

/-- No height of the chain is a multiple of `2π`. -/
theorem gridChainExp_im_ne (n : ℕ) (z : ℤ) : (gridChainExp n).im ≠ 2 * π * z := by
  intro h
  rw [gridChainExp_im] at h
  set d : ℤ := z - n - 1 with hd
  have hθ : gridChainPhase n = 2 * π * d := by rw [hd]; push_cast; linarith
  have hpos := gridChainPhase_pos n
  have hlt := gridChainPhase_lt_one n
  rw [hθ] at hpos hlt
  have h1 : (0 : ℝ) < d := by
    by_contra h; push Not at h; nlinarith [Real.pi_pos]
  have h2 : (d : ℝ) < 1 := by nlinarith [Real.pi_gt_three]
  have h1' : (0 : ℤ) < d := by exact_mod_cast h1
  have h2' : d < 1 := by exact_mod_cast h2
  omega

/-- **Chains hide from lag grids.** There is an exponential sum `Σ_n q_n e^{λ_n v}` with
`Σ|q_n| < ∞`, all `q_n ≠ 0`, depths `Re λ_n` strictly increasing to a value that is not attained,
heights that are not resonant on the grid `v = k` (no difference and no height in `2πℤ`), whose
real part is `≤ 0` at every integer lag, but not bounded above on the continuum `v ≥ 0`. -/
theorem exists_chain_hidden_from_grid :
    ∃ lam q : ℕ → ℂ, (Summable fun n => ‖q n‖) ∧ (∀ n, q n ≠ 0) ∧
      StrictMono (fun n => (lam n).re) ∧ (∀ n, 0 < (lam n).re ∧ (lam n).re < 1 / 4) ∧
      (∀ n m (z : ℤ), (lam n).im - (lam m).im = 2 * π * z → n = m) ∧
      (∀ n (z : ℤ), (lam n).im ≠ 2 * π * z) ∧
      (∀ k : ℕ, (∑' n, q n * cexp (lam n * (k : ℝ))).re ≤ 0) ∧
      ¬ ∃ M : ℝ, ∀ v : ℝ, 0 ≤ v → (∑' n, q n * cexp (lam n * v)).re ≤ M := by
  refine ⟨gridChainExp, fun n => -(gridChainWeight n : ℂ), ?_, fun n => ?_, ?_, fun n => ?_,
    fun n m z h => gridChainExp_im_sub_eq h, gridChainExp_im_ne, re_gridChainSum_nat_nonpos,
    not_bddAbove_re_gridChainSum⟩
  · exact summable_gridChainWeight.congr fun n => by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gridChainWeight_pos n)]
  · exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (gridChainWeight_pos n).ne')
  · intro a b hab
    simp only [gridChainExp_re]
    exact gridChainDepth_strictMono hab
  · rw [gridChainExp_re]; exact ⟨gridChainDepth_pos n, gridChainDepth_lt n⟩

end GaloisForLFunctions.SquareRootThreshold
