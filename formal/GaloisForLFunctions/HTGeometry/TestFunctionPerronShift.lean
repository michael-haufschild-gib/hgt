import GaloisForLFunctions.HTGeometry.MellinTestFunctionPerron

/-!
# Perron's formula for test functions, shifted past one simple pole

Let `f` be a smooth test function supported in `[a, b]`, `0 < a ≤ b` (`IsTest f a b`), and let
`c` be a sequence with `|c(n)| ≤ 1`, `c(0) = 0`.

* **Perron** (`verticalIntegral'_eq_tsum`).  For `σ > 1` and `X > 0`,
  `(1/2πi) ∫_{(σ)} L(c, s) 𝓜f(s) X^s ds = Σ_n c(n) f(n/X)`.
* **Contour shift** (`tsum_eq_residue_add`).  Suppose `L(c, s) = A/(s − ρ) + G₀(s)` on `Re s > 1`
  with `G₀` holomorphic on `Re s > a₀`, `a₀ < σ₀ < Re ρ < 3/2`, and
  `|A/(s − ρ) + G₀(s)| ≤ K |Im s|^{κ₁}` (`κ₁ < 1`) on the strip `σ₀ ≤ Re s ≤ 3/2`, `|Im s| ≥ 1`.
  Then `Σ_n c(n) f(n/X) = A 𝓜f(ρ) X^ρ + (1/2πi) ∫_{(σ₀)} (A/(s − ρ) + G₀(s)) 𝓜f(s) X^s ds`.
  The case `A = 0` is the holomorphic shift.
* **The bound** (`norm_tsum_sub_residue_le`).  If moreover `|A/(s − ρ) + G₀(s)| ≤ K₀ (|t| + 1)^{κ₁}`
  on `Re s = σ₀`, then
  `|Σ_n c(n) f(n/X) − A 𝓜f(ρ) X^ρ| ≤ X^{σ₀} K₀/(2π) ∫ (|t| + 1)^{κ₁} |𝓜f(σ₀ + it)| dt`.
-/

open Set Function Filter Complex Real MeasureTheory Topology
open scoped Interval

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TestFunctionPerron

variable {f : ℝ → ℂ} {a b : ℝ}

theorem IsTest.continuous_mellin_line (hf : IsTest f a b) (σ : ℝ) :
    Continuous fun t : ℝ => mellin f ((σ : ℂ) + t * I) :=
  continuous_iff_continuousAt.mpr fun _ =>
    (hf.differentiableAt_mellin _).continuousAt.comp (by fun_prop)

/-- A test function is Mellin convergent everywhere. -/
theorem IsTest.mellinConvergent (hf : IsTest f a b) (s : ℂ) : MellinConvergent f s := by
  have ha := hf.pos
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Icc a b) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    exact ((continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne')).smul
      hf.continuous.continuousAt).continuousWithinAt
  refine (hcont.integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro t ht
  rw [hf.eq_zero ht.2, smul_zero]

theorem IsTest.verticalIntegrable' (hf : IsTest f a b) (σ : ℝ) :
    VerticalIntegrable (mellin f) σ := hf.verticalIntegrable σ

set_option backward.isDefEq.respectTransparency false in
theorem integral_tsum_swap (hf : IsTest f a b) (c : ℕ → ℂ) (hc0 : c 0 = 0)
    (hc : ∀ n, ‖c n‖ ≤ 1) {X : ℝ} (X_pos : 0 < X) {σ : ℝ} (σ_gt : 1 < σ) :
    ∫ (t : ℝ), ∑' (n : ℕ), c n / (n : ℂ) ^ (σ + t * I) * mellin f (σ + t * I) *
        (X : ℂ) ^ (σ + t * I) =
      ∑' (n : ℕ), ∫ (t : ℝ), c n / (n : ℂ) ^ (σ + ↑t * I) * mellin f (σ + ↑t * I) *
        (X : ℂ) ^ (σ + t * I) := by
  have cont_mellin := hf.continuous_mellin_line σ
  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re,
      mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast
  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simp only [i_eq_zero, hc0, zero_div, zero_mul]
      exact aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp [i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (Real.summable_one_div_nat_rpow.mpr σ_gt)
      have h1 : ‖c n‖ ≤ 1 := hc n
      gcongr
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact (hf.verticalIntegrable σ).hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
/-- **Perron's formula for a test function.** -/
theorem verticalIntegral'_eq_tsum (hf : IsTest f a b) (c : ℕ → ℂ) (hc0 : c 0 = 0)
    (hc : ∀ n, ‖c n‖ ≤ 1) {X : ℝ} (X_pos : 0 < X) {σ : ℝ} (σ_gt : 1 < σ) :
    VerticalIntegral' (fun s => LSeries c s * mellin f s * (X : ℂ) ^ s) σ =
      ∑' n, c n * f (n / X) := by
  dsimp [VerticalIntegral', VerticalIntegral]
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, c n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin f (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), c n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin f (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, c n * ∫ (t : ℝ),
      mellin f (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, c n * ∫ (t : ℝ),
      mellin f (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, c n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin f (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, c n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin f (σ + ↑t * I) * ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [SmoothedPerron.LSeries_eq_tsum_div c hc0, ← tsum_mul_right, ← tsum_mul_right]
  · congr
    exact integral_tsum_swap hf c hc0 hc X_pos σ_gt
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero, hc0]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
      · push_cast at this ⊢
        rw [← this, div_mul_cancel₀]
        · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
      · apply div_nonneg (by linarith : 0 ≤ X); simp
      · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · congr
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero, hc0]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    have := mellinInv_mellin_eq σ (f := f) (x := n / X) ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · exact hf.mellinConvergent _
    · exact hf.verticalIntegrable σ
    · exact hf.continuous.continuousAt

/-! ## The contour shift -/

/-- The shifted Perron integrand `(A/(s − ρ) + G₀(s)) 𝓜f(s) X^s`. -/
def shiftIntegrand (f : ℝ → ℂ) (A ρ : ℂ) (G₀ : ℂ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  (A / (s - ρ) + G₀ s) * mellin f s * (X : ℂ) ^ s

/-- A continuous function on a line that grows at most like `|t|^κ` for `|t| ≥ T` is bounded by
`K₀ (|t| + 1)^κ` everywhere. -/
theorem exists_bound_line {g : ℝ → ℝ} (hg : Continuous g) {K κ T : ℝ} (hκ : 0 ≤ κ)
    (hT : ∀ t, T ≤ |t| → g t ≤ K * |t| ^ κ) :
    ∃ K₀, 0 ≤ K₀ ∧ ∀ t, g t ≤ K₀ * (|t| + 1) ^ κ := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨|B| + |K|, by positivity, fun t => ?_⟩
  have h1 : 1 ≤ (|t| + 1) ^ κ := Real.one_le_rpow (by linarith [abs_nonneg t]) hκ
  have hle : |t| ^ κ ≤ (|t| + 1) ^ κ :=
    Real.rpow_le_rpow (abs_nonneg t) (by linarith) hκ
  have hpos : 0 ≤ |t| ^ κ := Real.rpow_nonneg (abs_nonneg t) κ
  by_cases ht : T ≤ |t|
  · calc g t ≤ K * |t| ^ κ := hT t ht
      _ ≤ |K| * |t| ^ κ := mul_le_mul_of_nonneg_right (le_abs_self K) hpos
      _ ≤ |K| * (|t| + 1) ^ κ := mul_le_mul_of_nonneg_left hle (abs_nonneg K)
      _ ≤ (|B| + |K|) * (|t| + 1) ^ κ := by
          have : 0 ≤ |B| * (|t| + 1) ^ κ := by positivity
          nlinarith
  · push Not at ht
    have hmem : t ∈ Icc (-T) T := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have := hB t hmem
    rw [Real.norm_eq_abs] at this
    calc g t ≤ |g t| := le_abs_self _
      _ ≤ |B| := this.trans (le_abs_self B)
      _ ≤ |B| * (|t| + 1) ^ κ := le_mul_of_one_le_right (abs_nonneg B) h1
      _ ≤ (|B| + |K|) * (|t| + 1) ^ κ := by
          have : 0 ≤ |K| * (|t| + 1) ^ κ := by positivity
          nlinarith

/-- **The contour shift for a test function.** -/
theorem tsum_eq_residue_add (hf : IsTest f a b) (c : ℕ → ℂ) (hc0 : c 0 = 0)
    (hc : ∀ n, ‖c n‖ ≤ 1) {A ρ : ℂ} {G₀ : ℂ → ℂ} {a₀ σ₀ : ℝ} (hσ₀ : a₀ < σ₀)
    (hρ₀ : σ₀ < ρ.re) (hρ₁ : ρ.re < 3 / 2)
    (hG₀ : DifferentiableOn ℂ G₀ {s | a₀ < s.re})
    (hLS : ∀ s : ℂ, 1 < s.re → A / (s - ρ) + G₀ s = LSeries c s)
    {K κ₁ : ℝ} (hκ₁0 : 0 ≤ κ₁) (hκ₁ : κ₁ < 1)
    (hstrip : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
      ‖A / (s - ρ) + G₀ s‖ ≤ K * |s.im| ^ κ₁)
    {X : ℝ} (hX : 0 < X) :
    ∑' n, c n * f (n / X) =
      A * mellin f ρ * (X : ℂ) ^ ρ + VerticalIntegral' (shiftIntegrand f A ρ G₀ X) σ₀ := by
  set F := shiftIntegrand f A ρ G₀ X with hFdef
  set M := mellin f with hMdef
  obtain ⟨C, hC0, hC⟩ := hf.exists_norm_mellin_le_decay (max |σ₀ - 1| (1 / 2))
  have hMd : ∀ s : ℂ, DifferentiableAt ℂ M s := hf.differentiableAt_mellin
  have hG₀d : ∀ s : ℂ, a₀ < s.re → DifferentiableAt ℂ G₀ s := fun s hs =>
    hG₀.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have hXd : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (X : ℂ) ^ s) s := fun s =>
    differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hX.ne'))
  have hFd : ∀ s : ℂ, a₀ < s.re → s ≠ ρ → DifferentiableAt ℂ F s := by
    intro s hs hsρ
    have h1 : DifferentiableAt ℂ (fun s : ℂ => A / (s - ρ) + G₀ s) s :=
      ((differentiableAt_const A).div (differentiableAt_id.sub_const ρ)
        (sub_ne_zero.mpr hsρ)).add (hG₀d s hs)
    exact (h1.mul (hMd s)).mul (hXd s)
  have hnormX : ∀ s : ℂ, ‖(X : ℂ) ^ s‖ = X ^ s.re := fun s =>
    Complex.norm_cpow_eq_rpow_re_of_pos hX s
  -- Perron at `3/2`
  have hP := verticalIntegral'_eq_tsum hf c hc0 hc hX (σ := 3 / 2) (by norm_num)
  have hright_eq : VerticalIntegral' F (3 / 2) =
      VerticalIntegral' (fun s => LSeries c s * M s * (X : ℂ) ^ s) (3 / 2) := by
    simp only [VerticalIntegral', VerticalIntegral]
    congr 3
    funext t
    simp only [hFdef, shiftIntegrand]
    rw [hLS _ (by simp; norm_num)]
  -- holomorphy off the pole
  have hhol : HolomorphicOn F (Set.Icc σ₀ (3 / 2) ×ℂ Set.univ \ {ρ}) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    rw [Complex.mem_reProdIm] at hs1
    exact (hFd s (by linarith [hs1.1.1]) hs2).differentiableWithinAt
  -- the pole at `ρ`
  have hpole : (F - fun s => A * M ρ * (X : ℂ) ^ ρ / (s - ρ)) =O[𝓝[≠] ρ] (1 : ℂ → ℂ) := by
    have hG : DifferentiableAt ℂ (fun s => A * M s * (X : ℂ) ^ s) ρ :=
      ((differentiableAt_const A).mul (hMd ρ)).mul (hXd ρ)
    have h1 := SmoothedPerron.isBigO_div_sub_div hG
    have h2 : (fun s => G₀ s * M s * (X : ℂ) ^ s) =O[𝓝[≠] ρ] (1 : ℂ → ℂ) := by
      have hc : ContinuousAt (fun s => G₀ s * M s * (X : ℂ) ^ s) ρ :=
        (((hG₀d ρ (by linarith)).mul (hMd ρ)).mul (hXd ρ)).continuousAt
      exact (hc.isBigO_one ℂ).mono nhdsWithin_le_nhds
    refine (h1.add h2).congr' (Eventually.of_forall fun s => ?_)
      (Eventually.of_forall fun s => rfl)
    simp only [Pi.sub_apply, hFdef, shiftIntegrand]
    ring
  -- horizontal decay
  set Mb : ℝ → ℝ := fun T => K * C * (X ^ σ₀ + X ^ (3 / 2 : ℝ)) * |T| ^ (κ₁ - 2) with hMb
  have hhor : ∀ T : ℝ, 1 ≤ |T| → ∀ u ∈ Ι σ₀ (3 / 2), ‖F (u + T * I)‖ ≤ Mb T := by
    intro T hT u hu
    rw [uIoc_of_le (by linarith)] at hu
    set s : ℂ := (u : ℂ) + T * I with hs
    have hsre : s.re = u := by simp [hs]
    have hsim : s.im = T := by simp [hs]
    have hG := hstrip s (by rw [hsre]; exact hu.1.le) (by rw [hsre]; exact hu.2)
      (by rw [hsim]; exact hT)
    rw [hsim] at hG
    have hT0 : 0 < |T| := by linarith
    have hMs : ‖M s‖ ≤ C * |T| ^ (-2 : ℝ) := by
      have h := hC s (by
        rw [hsre]; rw [abs_le]; constructor
        · have := le_max_left |σ₀ - 1| (1 / 2)
          have := neg_abs_le (σ₀ - 1)
          linarith [hu.1]
        · have := le_max_right |σ₀ - 1| (1 / 2)
          linarith [hu.2])
      refine h.trans ?_
      rw [hsim, Real.rpow_neg hT0.le, div_eq_mul_inv]
      gcongr
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
      linarith
    have hXs : ‖(X : ℂ) ^ s‖ ≤ X ^ σ₀ + X ^ (3 / 2 : ℝ) := by
      rw [hnormX, hsre]
      rcases le_or_gt 1 X with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h hu.2
        have := Real.rpow_nonneg hX.le σ₀
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge hX h.le hu.1.le
        have := Real.rpow_nonneg hX.le (3 / 2 : ℝ)
        linarith
    have hKT : 0 ≤ K * |T| ^ κ₁ := (norm_nonneg _).trans hG
    calc ‖F s‖ = ‖A / (s - ρ) + G₀ s‖ * ‖M s‖ * ‖(X : ℂ) ^ s‖ := by
          show ‖(A / (s - ρ) + G₀ s) * M s * (X : ℂ) ^ s‖ = _
          rw [norm_mul, norm_mul]
      _ ≤ (K * |T| ^ κ₁) * (C * |T| ^ (-2 : ℝ)) * (X ^ σ₀ + X ^ (3 / 2 : ℝ)) := by
          gcongr
      _ = Mb T := by
          rw [hMb]
          simp only
          rw [show κ₁ - 2 = κ₁ + (-2) by ring, Real.rpow_add hT0]
          ring
  have hMbt : Tendsto (fun T : ℝ => Mb T * |3 / 2 - σ₀|) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => Mb T * |3 / 2 - σ₀|) atBot (𝓝 0) := by
    have hp : Tendsto (fun y : ℝ => y ^ (κ₁ - 2)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 2 - κ₁) (by linarith)
      simpa [neg_sub] using this
    constructor
    · have := ((hp.comp tendsto_abs_atTop_atTop).const_mul
        (K * C * (X ^ σ₀ + X ^ (3 / 2 : ℝ)))).mul_const |3 / 2 - σ₀|
      simpa [hMb] using this
    · have := ((hp.comp tendsto_abs_atBot_atTop).const_mul
        (K * C * (X ^ σ₀ + X ^ (3 / 2 : ℝ)))).mul_const |3 / 2 - σ₀|
      simpa [hMb] using this
  have htop : Tendsto (fun y : ℝ => ∫ x in σ₀..(3 / 2 : ℝ), F ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hMbt.1
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT' : 1 ≤ |T| := le_trans hT (le_abs_self T)
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => hhor T hT' u hu
  have hbot : Tendsto (fun y : ℝ => ∫ x in σ₀..(3 / 2 : ℝ), F ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hMbt.2
    filter_upwards [eventually_le_atBot (-1)] with T hT
    have hT' : 1 ≤ |T| := by rw [abs_of_neg (by linarith)]; linarith
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => hhor T hT' u hu
  -- integrability on a vertical line inside the strip, away from the pole
  have hlineInt : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 3 / 2 → σ ≠ ρ.re →
      Integrable fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I) := by
    intro σ hσ1 hσ2 hσρ
    have hcont : Continuous fun y : ℝ => ‖A / ((σ : ℂ) + (y : ℂ) * I - ρ) +
        G₀ ((σ : ℂ) + (y : ℂ) * I)‖ := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have hne : (σ : ℂ) + (y : ℂ) * I - ρ ≠ 0 := by
        intro h; apply hσρ; have := congrArg Complex.re h; simp at this; linarith
      have h1 : ContinuousAt (fun s : ℂ => A / (s - ρ) + G₀ s) ((σ : ℂ) + (y : ℂ) * I) :=
        (((continuousAt_const).div (continuousAt_id.sub continuousAt_const) hne)).add
          (hG₀d _ (by simp; linarith)).continuousAt
      exact (h1.comp (f := fun y : ℝ => (σ : ℂ) + (y : ℂ) * I) (by fun_prop)).norm
    obtain ⟨K₀, hK₀0, hK₀⟩ := exists_bound_line hcont hκ₁0 (K := K) (T := 1) fun t ht => by
      have := hstrip ((σ : ℂ) + (t : ℂ) * I) (by simp; linarith) (by simp; linarith)
        (by simpa using ht)
      simpa using this
    have hbase : Integrable fun y : ℝ => (1 + |y|) ^ (-(2 - κ₁)) := by
      have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(2 - κ₁)) :=
        integrable_one_add_norm (by simp; linarith)
      exact h.congr (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs])
    refine (hbase.const_mul (K₀ * (2 * C) * X ^ σ)).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y => ?_)
      have hne : (σ : ℂ) + (y : ℂ) * I ≠ ρ := by
        intro h; apply hσρ; have := congrArg Complex.re h; simp at this; linarith
      exact ContinuousAt.comp (g := F) (hFd _ (by simp; linarith) hne).continuousAt
        (by fun_prop)
    · filter_upwards with y
      set s : ℂ := (σ : ℂ) + (y : ℂ) * I with hs
      have hsre : s.re = σ := by simp [hs]
      have hsim : s.im = y := by simp [hs]
      have hG := hK₀ y
      have hMs : ‖M s‖ ≤ 2 * C * ((|y| + 1) ^ 2)⁻¹ := by
        have h := hC s (by
          rw [hsre, abs_le]; constructor
          · have := le_max_left |σ₀ - 1| (1 / 2)
            have := neg_abs_le (σ₀ - 1)
            linarith
          · have := le_max_right |σ₀ - 1| (1 / 2)
            linarith)
        refine h.trans ?_
        rw [hsim, div_le_iff₀ (by positivity)]
        have h2 : (|y| + 1) ^ 2 ≤ 2 * (1 + y ^ 2) := by
          nlinarith [sq_abs y, abs_nonneg y, sq_nonneg (|y| - 1)]
        have hp : 0 < (|y| + 1) ^ 2 := by positivity
        have e : 2 * C * ((|y| + 1) ^ 2)⁻¹ * (1 + y ^ 2) =
            C * (2 * (1 + y ^ 2) / (|y| + 1) ^ 2) := by field_simp
        rw [e]
        have : 1 ≤ 2 * (1 + y ^ 2) / (|y| + 1) ^ 2 := by rw [le_div_iff₀ hp]; linarith
        nlinarith
      have hpow : (|y| + 1) ^ κ₁ * ((|y| + 1) ^ 2)⁻¹ = (1 + |y|) ^ (-(2 - κ₁)) := by
        rw [add_comm (|y|) 1, show -(2 - κ₁) = κ₁ - 2 by ring, Real.rpow_sub (by positivity),
          Real.rpow_two, div_eq_mul_inv]
      calc ‖F s‖ = ‖A / (s - ρ) + G₀ s‖ * ‖M s‖ * ‖(X : ℂ) ^ s‖ := by
            show ‖(A / (s - ρ) + G₀ s) * M s * (X : ℂ) ^ s‖ = _
            rw [norm_mul, norm_mul]
        _ ≤ (K₀ * (|y| + 1) ^ κ₁) * (2 * C * ((|y| + 1) ^ 2)⁻¹) * X ^ σ := by
            rw [hnormX, hsre]
            gcongr
        _ = K₀ * (2 * C) * X ^ σ * (1 + |y|) ^ (-(2 - κ₁)) := by
            rw [← hpow]; ring
  have hshift := verticalIntegral'_sub_of_simple_pole (σ := σ₀) (σ' := 3 / 2) (f := F)
    hρ₀ hρ₁ hhol hpole hbot htop (hlineInt σ₀ le_rfl (by linarith) (by linarith))
    (hlineInt (3 / 2) (by linarith) le_rfl (by linarith))
  rw [hright_eq, hP] at hshift
  rw [← hshift]
  ring

/-- `(|t| + 1)^κ |𝓜f(σ + it)|` is integrable for `κ < 1`. -/
theorem IsTest.integrable_rpow_mul_norm_mellin (hf : IsTest f a b) (σ : ℝ) {κ : ℝ}
    (hκ : κ < 1) :
    Integrable fun t : ℝ => (|t| + 1) ^ κ * ‖mellin f ((σ : ℂ) + t * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_norm_mellin_le_decay |σ - 1|
  have hbase : Integrable fun y : ℝ => (1 + |y|) ^ (-(2 - κ)) := by
    have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(2 - κ)) :=
      integrable_one_add_norm (by simp; linarith)
    exact h.congr (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs])
  refine (hbase.const_mul (2 * C)).mono' ?_ ?_
  · have hc : Continuous fun t : ℝ => (|t| + 1) ^ κ :=
      (continuous_abs.add continuous_const).rpow_const fun t =>
        Or.inl (ne_of_gt (show (0 : ℝ) < |t| + 1 by positivity))
    exact (hc.mul (hf.continuous_mellin_line σ).norm).aestronglyMeasurable
  · filter_upwards with y
    have h := hC ((σ : ℂ) + y * I) (by simp)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add] at h
    have hp : 0 < (|y| + 1) ^ 2 := by positivity
    have h2 : (|y| + 1) ^ 2 ≤ 2 * (1 + y ^ 2) := by
      nlinarith [sq_abs y, abs_nonneg y, sq_nonneg (|y| - 1)]
    have hM : ‖mellin f ((σ : ℂ) + y * I)‖ ≤ 2 * C * ((|y| + 1) ^ 2)⁻¹ := by
      refine h.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have e : 2 * C * ((|y| + 1) ^ 2)⁻¹ * (1 + y ^ 2) =
          C * (2 * (1 + y ^ 2) / (|y| + 1) ^ 2) := by field_simp
      rw [e]
      have : 1 ≤ 2 * (1 + y ^ 2) / (|y| + 1) ^ 2 := by rw [le_div_iff₀ hp]; linarith
      nlinarith
    have hpow : (|y| + 1) ^ κ * ((|y| + 1) ^ 2)⁻¹ = (1 + |y|) ^ (-(2 - κ)) := by
      rw [add_comm (|y|) 1, show -(2 - κ) = κ - 2 by ring, Real.rpow_sub (by positivity),
        Real.rpow_two, div_eq_mul_inv]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (|y| + 1) ^ κ * ‖mellin f ((σ : ℂ) + y * I)‖
        ≤ (|y| + 1) ^ κ * (2 * C * ((|y| + 1) ^ 2)⁻¹) := by gcongr
      _ = 2 * C * (1 + |y|) ^ (-(2 - κ)) := by rw [← hpow]; ring

/-- **The bound on the shifted line.** -/
theorem norm_tsum_sub_residue_le (hf : IsTest f a b) (c : ℕ → ℂ) (hc0 : c 0 = 0)
    (hc : ∀ n, ‖c n‖ ≤ 1) {A ρ : ℂ} {G₀ : ℂ → ℂ} {a₀ σ₀ : ℝ} (hσ₀ : a₀ < σ₀)
    (hρ₀ : σ₀ < ρ.re) (hρ₁ : ρ.re < 3 / 2)
    (hG₀ : DifferentiableOn ℂ G₀ {s | a₀ < s.re})
    (hLS : ∀ s : ℂ, 1 < s.re → A / (s - ρ) + G₀ s = LSeries c s)
    {K κ₁ : ℝ} (hκ₁0 : 0 ≤ κ₁) (hκ₁ : κ₁ < 1)
    (hstrip : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
      ‖A / (s - ρ) + G₀ s‖ ≤ K * |s.im| ^ κ₁)
    {K₀ : ℝ} (hline : ∀ t : ℝ,
      ‖A / ((σ₀ : ℂ) + t * I - ρ) + G₀ ((σ₀ : ℂ) + t * I)‖ ≤ K₀ * (|t| + 1) ^ κ₁)
    {X : ℝ} (hX : 0 < X) :
    ‖∑' n, c n * f (n / X) - A * mellin f ρ * (X : ℂ) ^ ρ‖ ≤
      X ^ σ₀ * K₀ / (2 * π) *
        ∫ t : ℝ, (|t| + 1) ^ κ₁ * ‖mellin f ((σ₀ : ℂ) + t * I)‖ := by
  rw [tsum_eq_residue_add hf c hc0 hc hσ₀ hρ₀ hρ₁ hG₀ hLS hκ₁0 hκ₁ hstrip hX,
    add_sub_cancel_left]
  have hint := hf.integrable_rpow_mul_norm_mellin σ₀ hκ₁
  have hpt : ∀ t : ℝ, ‖shiftIntegrand f A ρ G₀ X ((σ₀ : ℂ) + t * I)‖ ≤
      X ^ σ₀ * K₀ * ((|t| + 1) ^ κ₁ * ‖mellin f ((σ₀ : ℂ) + t * I)‖) := by
    intro t
    unfold shiftIntegrand
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have hre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    rw [hre]
    have hK := hline t
    have hX0 : 0 ≤ X ^ σ₀ := Real.rpow_nonneg hX.le _
    calc ‖A / ((σ₀ : ℂ) + t * I - ρ) + G₀ ((σ₀ : ℂ) + t * I)‖ * ‖mellin f ((σ₀ : ℂ) + t * I)‖ *
          X ^ σ₀ ≤ (K₀ * (|t| + 1) ^ κ₁) * ‖mellin f ((σ₀ : ℂ) + t * I)‖ * X ^ σ₀ := by gcongr
      _ = _ := by ring
  have hK₀ : 0 ≤ K₀ := by
    have h1 := (norm_nonneg _).trans (hline 0)
    have h2 : 0 < (|(0 : ℝ)| + 1) ^ κ₁ := by positivity
    exact nonneg_of_mul_nonneg_left h1 h2
  have hnorm : ‖VerticalIntegral' (shiftIntegrand f A ρ G₀ X) σ₀‖ =
      ‖∫ t : ℝ, shiftIntegrand f A ρ G₀ X ((σ₀ : ℂ) + t * I)‖ / (2 * π) := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
    rw [← mul_assoc, show 1 / (2 * (π : ℂ) * I) * I = ((1 / (2 * π) : ℝ) : ℂ) by
      push_cast; field_simp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  rw [hnorm, div_le_iff₀ (by positivity)]
  calc ‖∫ t : ℝ, shiftIntegrand f A ρ G₀ X ((σ₀ : ℂ) + t * I)‖
      ≤ ∫ t : ℝ, ‖shiftIntegrand f A ρ G₀ X ((σ₀ : ℂ) + t * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, X ^ σ₀ * K₀ * ((|t| + 1) ^ κ₁ * ‖mellin f ((σ₀ : ℂ) + t * I)‖) :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
          (hint.const_mul _) (Eventually.of_forall hpt)
    _ = X ^ σ₀ * K₀ / (2 * π) *
          (∫ t : ℝ, (|t| + 1) ^ κ₁ * ‖mellin f ((σ₀ : ℂ) + t * I)‖) * (2 * π) := by
        rw [integral_const_mul]
        generalize (∫ t : ℝ, (|t| + 1) ^ κ₁ * ‖mellin f ((σ₀ : ℂ) + t * I)‖) = J
        field_simp

end GaloisForLFunctions.HTGeometry.TestFunctionPerron
