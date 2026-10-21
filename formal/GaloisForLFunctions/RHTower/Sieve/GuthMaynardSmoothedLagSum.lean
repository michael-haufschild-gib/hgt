import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSum

/-!
# The smoothed lag sum `R̃` and the smoothed cubic term `Ĩ_m` (Guth–Maynard (7.5), Prop. 7.2)

For bumps `ψ₁, ψ₂ : ℝ → ℝ` and scales `N, M > 0`, Guth–Maynard (arXiv 2405.20552, (7.5)) put

`R̃(u) = (∫ NM ψ₁(NM(u − u')) ψ₂(u') |R(u')|² du')^{1/2}`,

`|R|` smoothed at scale `1/(NM)` and localised by `ψ₂`, and Proposition 7.2 bounds `S₃` through

`Ĩ_m = ∫_{1/2 ≤ v ≤ 2} |R(v)| R̃((m₁v + m₃)/(m₂v)) R̃((m₁v + m₃)/m₂) dv`.

This module holds these two definitions (`smoothedLagSum`, `smoothedCubicTerm`), the regularity
class `IsSmoothingPair` of the bumps, the two explicit bumps used in Proposition 7.2
(`innerBump A`: smooth, `0 ≤ · ≤ 1`, `= 1` on `[-A, A]`, support in `(-2A, 2A)`, derivatives
bounded uniformly in `A ≥ 1`; `outerBump`: smooth, `0 ≤ · ≤ 1`, `= 1` on `[1/4, 4]`, support in
`(1/8, 33/8)`), and the majorisation `∫_{S ∩ [c-r, c+r]} |R|² ≤ R̃(c)²/(NM)` that turns the
Cauchy–Schwarz step of Proposition 7.2 into `R̃`.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Definitions -/

/-- The smoothed lag sum `R̃_{ψ₁,ψ₂,M}(u) = (∫ NM ψ₁(NM(u − u')) ψ₂(u') |R(u')|² du')^{1/2}`
(Guth–Maynard (7.5)). -/
def smoothedLagSum (ψ₁ ψ₂ : ℝ → ℝ) (N M : ℝ) (W : Finset ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (∫ x, N * M * ψ₁ (N * M * (u - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2)

/-- The smoothed cubic term of Proposition 7.2,
`Ĩ_m = ∫_{1/2 ≤ v ≤ 2} |R(v)| R̃((m₁v + m₃)/(m₂v)) R̃((m₁v + m₃)/m₂) dv`. -/
def smoothedCubicTerm (ψ₁ ψ₂ : ℝ → ℝ) (N M : ℝ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ) : ℝ :=
  ∫ v in Icc (1 / 2 : ℝ) 2, ‖lagSum W v‖ *
    smoothedLagSum ψ₁ ψ₂ N M W ((m₁ * v + m₃) / (m₂ * v)) *
      smoothedLagSum ψ₁ ψ₂ N M W ((m₁ * v + m₃) / m₂)

/-- Regularity of a pair of smoothing bumps: continuous, compactly supported, with values in
`[0, 1]`. Every `R̃` estimate of this module holds for such a pair. -/
structure IsSmoothingPair (ψ₁ ψ₂ : ℝ → ℝ) : Prop where
  continuous₁ : Continuous ψ₁
  compactSupport₁ : HasCompactSupport ψ₁
  nonneg₁ : ∀ x, 0 ≤ ψ₁ x
  le_one₁ : ∀ x, ψ₁ x ≤ 1
  continuous₂ : Continuous ψ₂
  compactSupport₂ : HasCompactSupport ψ₂
  nonneg₂ : ∀ x, 0 ≤ ψ₂ x
  le_one₂ : ∀ x, ψ₂ x ≤ 1

/-! ### The two bumps of Proposition 7.2 -/

/-- The fixed plateau bump: `= 1` on `[-1, 1]`, support `(-2, 2)`. -/
def plateauBump : ℝ → ℝ :=
  ⇑(⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ))

/-- The inner bump `ψ̃₁(x) = φ(x / A)` of width `A` (Proposition 7.2 uses `A = 2T^η`). -/
def innerBump (A : ℝ) (x : ℝ) : ℝ :=
  plateauBump (x / A)

/-- The outer bump `ψ̃₂`: `= 1` on `[1/4, 4]`, support `(1/8, 33/8)`. -/
def outerBump : ℝ → ℝ :=
  ⇑(⟨15 / 8, 2, by norm_num, by norm_num⟩ : ContDiffBump (17 / 8 : ℝ))

theorem plateauBump_nonneg (x : ℝ) : 0 ≤ plateauBump x := ContDiffBump.nonneg _

theorem plateauBump_le_one (x : ℝ) : plateauBump x ≤ 1 := ContDiffBump.le_one _

theorem contDiff_plateauBump : ContDiff ℝ (↑(⊤ : ℕ∞)) plateauBump := ContDiffBump.contDiff _

theorem hasCompactSupport_plateauBump : HasCompactSupport plateauBump :=
  ContDiffBump.hasCompactSupport _

theorem plateauBump_eq_one {x : ℝ} (hx : |x| ≤ 1) : plateauBump x = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (by simpa [Real.dist_eq] using hx)

theorem plateauBump_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : plateauBump x = 0 := by
  have h := (ContDiffBump.support_eq (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)))
  refine Function.notMem_support.mp fun hs => ?_
  have : x ∈ Metric.ball (0 : ℝ) 2 := by
    unfold plateauBump at hs
    rw [h] at hs
    exact hs
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at this
  change |x| < 2 at this
  linarith

/-- Every derivative of a smooth compactly supported function is bounded. -/
theorem exists_abs_iteratedDeriv_le {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : HasCompactSupport f) (j : ℕ) : ∃ C, ∀ x, |iteratedDeriv j f x| ≤ C := by
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    (hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)) (hs.iteratedFDeriv j)
  refine ⟨C, fun x => ?_⟩
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hC x

theorem innerBump_nonneg (A x : ℝ) : 0 ≤ innerBump A x := plateauBump_nonneg _

theorem innerBump_le_one (A x : ℝ) : innerBump A x ≤ 1 := plateauBump_le_one _

theorem innerBump_zero (A : ℝ) : innerBump A 0 = 1 := by
  simp [innerBump, plateauBump_eq_one]

theorem innerBump_eq_one {A x : ℝ} (hA : 0 < A) (hx : |x| ≤ A) : innerBump A x = 1 := by
  refine plateauBump_eq_one ?_
  rw [abs_div, abs_of_pos hA, div_le_one hA]
  exact hx

theorem innerBump_eq_zero {A x : ℝ} (hA : 0 < A) (hx : 2 * A ≤ |x|) : innerBump A x = 0 := by
  refine plateauBump_eq_zero ?_
  rw [abs_div, abs_of_pos hA, le_div_iff₀ hA]
  linarith

theorem contDiff_innerBump (A : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (innerBump A) :=
  contDiff_plateauBump.comp (contDiff_id.div_const A)

theorem hasCompactSupport_innerBump {A : ℝ} (hA : 0 < A) : HasCompactSupport (innerBump A) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(2 * A)) (b := 2 * A)) fun x hx =>
    innerBump_eq_zero hA (by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)

/-- `‖ψ̃₁^{(j)}‖_∞ ≪_j 1` uniformly in the width `A ≥ 1`. -/
theorem exists_abs_iteratedDeriv_innerBump_le (j : ℕ) :
    ∃ C, ∀ A, 1 ≤ A → ∀ x, |iteratedDeriv j (innerBump A) x| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_le contDiff_plateauBump
    hasCompactSupport_plateauBump j
  refine ⟨C, fun A hA x => ?_⟩
  have hfun : innerBump A = fun x => plateauBump (A⁻¹ * x) := by
    funext y; simp [innerBump, div_eq_inv_mul]
  rw [hfun, iteratedDeriv_comp_const_mul (contDiff_plateauBump.of_le (by exact_mod_cast le_top))]
  have hA' : |A⁻¹ ^ j| ≤ 1 := by
    rw [abs_pow, abs_inv, abs_of_pos (by linarith)]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hA)
  rw [abs_mul]
  calc |A⁻¹ ^ j| * |iteratedDeriv j plateauBump (A⁻¹ * x)| ≤ 1 * C :=
        mul_le_mul hA' (hC _) (abs_nonneg _) zero_le_one
    _ = C := one_mul C

theorem outerBump_nonneg (x : ℝ) : 0 ≤ outerBump x := ContDiffBump.nonneg _

theorem outerBump_le_one (x : ℝ) : outerBump x ≤ 1 := ContDiffBump.le_one _

theorem contDiff_outerBump : ContDiff ℝ (↑(⊤ : ℕ∞)) outerBump := ContDiffBump.contDiff _

theorem hasCompactSupport_outerBump : HasCompactSupport outerBump :=
  ContDiffBump.hasCompactSupport _

theorem outerBump_eq_one {x : ℝ} (hx : x ∈ Icc (1 / 4 : ℝ) 4) : outerBump x = 1 := by
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> norm_num <;> linarith [hx.1, hx.2]

theorem outerBump_one : outerBump 1 = 1 := outerBump_eq_one (by norm_num)

theorem outerBump_eq_zero {x : ℝ} (hx : x ∉ Ioo (1 / 8 : ℝ) (33 / 8)) : outerBump x = 0 := by
  have h := ContDiffBump.support_eq
    (⟨15 / 8, 2, by norm_num, by norm_num⟩ : ContDiffBump (17 / 8 : ℝ))
  refine Function.notMem_support.mp fun hs => hx ?_
  have : x ∈ Metric.ball (17 / 8 : ℝ) 2 := by
    unfold outerBump at hs
    rw [h] at hs
    exact hs
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- `ψ̃₂^{(j)} ≪_j 1`. -/
theorem exists_abs_iteratedDeriv_outerBump_le (j : ℕ) :
    ∃ C, ∀ x, |iteratedDeriv j outerBump x| ≤ C :=
  exists_abs_iteratedDeriv_le contDiff_outerBump hasCompactSupport_outerBump j

/-- The bumps of Proposition 7.2 form a smoothing pair for every positive width. -/
theorem isSmoothingPair_innerBump_outerBump {A : ℝ} (hA : 0 < A) :
    IsSmoothingPair (innerBump A) outerBump where
  continuous₁ := (contDiff_innerBump A).continuous
  compactSupport₁ := hasCompactSupport_innerBump hA
  nonneg₁ := innerBump_nonneg A
  le_one₁ := innerBump_le_one A
  continuous₂ := contDiff_outerBump.continuous
  compactSupport₂ := hasCompactSupport_outerBump
  nonneg₂ := outerBump_nonneg
  le_one₂ := outerBump_le_one

/-! ### Elementary properties of `R̃` -/

/-- The integrand of `R̃(u)²`. -/
def smoothedLagSumIntegrand (ψ₁ ψ₂ : ℝ → ℝ) (N M : ℝ) (W : Finset ℝ) (u x : ℝ) : ℝ :=
  N * M * ψ₁ (N * M * (u - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2

theorem measurable_lagSum (W : Finset ℝ) : Measurable (lagSum W) := by
  unfold lagSum; fun_prop

theorem measurable_norm_lagSum_sq (W : Finset ℝ) : Measurable fun x => ‖lagSum W x‖ ^ 2 :=
  ((measurable_lagSum W).norm).pow_const 2

theorem smoothedLagSumIntegrand_nonneg {ψ₁ ψ₂ : ℝ → ℝ} (h : IsSmoothingPair ψ₁ ψ₂) {N M : ℝ}
    (hNM : 0 ≤ N * M) (W : Finset ℝ) (u x : ℝ) : 0 ≤ smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x := by
  unfold smoothedLagSumIntegrand
  have := h.nonneg₁ (N * M * (u - x))
  have := h.nonneg₂ x
  positivity

theorem integrable_smoothedLagSumIntegrand {ψ₁ ψ₂ : ℝ → ℝ} (h : IsSmoothingPair ψ₁ ψ₂)
    (N M : ℝ) (W : Finset ℝ) (u : ℝ) : Integrable (smoothedLagSumIntegrand ψ₁ ψ₂ N M W u) := by
  have hψ₂ : Integrable ψ₂ := h.continuous₂.integrable_of_hasCompactSupport h.compactSupport₂
  have hmeas : AEStronglyMeasurable
      (fun x => N * M * ψ₁ (N * M * (u - x)) * ‖lagSum W x‖ ^ 2) volume := by
    have := h.continuous₁.measurable
    have := measurable_lagSum W
    exact (by fun_prop : Measurable fun x =>
      N * M * ψ₁ (N * M * (u - x)) * ‖lagSum W x‖ ^ 2).aestronglyMeasurable
  have := hψ₂.bdd_mul (c := |N * M| * (W.card : ℝ) ^ 2) hmeas
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (h.nonneg₁ _),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖lagSum W x‖ ^ 2)]
      have h1 := h.le_one₁ (N * M * (u - x))
      have h2 : ‖lagSum W x‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2
      calc |N * M| * ψ₁ (N * M * (u - x)) * ‖lagSum W x‖ ^ 2 ≤ |N * M| * 1 * (W.card : ℝ) ^ 2 := by
            gcongr
        _ = |N * M| * (W.card : ℝ) ^ 2 := by ring)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [smoothedLagSumIntegrand]; ring

theorem smoothedLagSum_nonneg (ψ₁ ψ₂ : ℝ → ℝ) (N M : ℝ) (W : Finset ℝ) (u : ℝ) :
    0 ≤ smoothedLagSum ψ₁ ψ₂ N M W u := Real.sqrt_nonneg _

/-- `R̃(u)² = ∫ NM ψ₁(NM(u − x)) ψ₂(x) |R(x)|² dx`. -/
theorem smoothedLagSum_sq {ψ₁ ψ₂ : ℝ → ℝ} (h : IsSmoothingPair ψ₁ ψ₂) {N M : ℝ}
    (hNM : 0 ≤ N * M) (W : Finset ℝ) (u : ℝ) :
    smoothedLagSum ψ₁ ψ₂ N M W u ^ 2 = ∫ x, smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x :=
  Real.sq_sqrt (integral_nonneg (smoothedLagSumIntegrand_nonneg h hNM W u))

/-- `R̃` is measurable. -/
theorem measurable_smoothedLagSum {ψ₁ ψ₂ : ℝ → ℝ} (h : IsSmoothingPair ψ₁ ψ₂) (N M : ℝ)
    (W : Finset ℝ) : Measurable (smoothedLagSum ψ₁ ψ₂ N M W) := by
  have h₁ := h.continuous₁.measurable
  have h₂ := h.continuous₂.measurable
  have hF : StronglyMeasurable fun p : ℝ × ℝ =>
      N * M * ψ₁ (N * M * (p.1 - p.2)) * ψ₂ p.2 * ‖lagSum W p.2‖ ^ 2 := by
    have := measurable_lagSum W
    exact (by fun_prop : Measurable fun p : ℝ × ℝ =>
      N * M * ψ₁ (N * M * (p.1 - p.2)) * ψ₂ p.2 * ‖lagSum W p.2‖ ^ 2).stronglyMeasurable
  exact (hF.integral_prod_right' (ν := volume)).measurable.sqrt

/-- `R̃(u) ≤ |W| (∫ ψ₁)^{1/2}`. -/
theorem smoothedLagSum_le {ψ₁ ψ₂ : ℝ → ℝ} (h : IsSmoothingPair ψ₁ ψ₂) {N M : ℝ}
    (hNM : 0 < N * M) (W : Finset ℝ) (u : ℝ) :
    smoothedLagSum ψ₁ ψ₂ N M W u ≤ W.card * Real.sqrt (∫ x, ψ₁ x) := by
  have hψ₁ : Integrable ψ₁ := h.continuous₁.integrable_of_hasCompactSupport h.compactSupport₁
  have hscale : ∫ x, N * M * ψ₁ (N * M * (u - x)) = ∫ x, ψ₁ x := by
    rw [integral_const_mul, integral_sub_left_eq_self (fun y => ψ₁ (N * M * y)),
      Measure.integral_comp_mul_left, abs_inv, abs_of_pos hNM, smul_eq_mul,
      mul_inv_cancel_left₀ hNM.ne']
  have hle : ∫ x, smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x ≤
      ∫ x, (W.card : ℝ) ^ 2 * (N * M * ψ₁ (N * M * (u - x))) := by
    refine integral_mono (integrable_smoothedLagSumIntegrand h N M W u) ?_ fun x => ?_
    · exact (((hψ₁.comp_mul_left' hNM.ne').comp_sub_left u).const_mul (N * M)).const_mul _
    · unfold smoothedLagSumIntegrand
      have h1 := h.nonneg₁ (N * M * (u - x))
      have h2 := h.le_one₂ x
      have h3 := h.nonneg₂ x
      have h4 : ‖lagSum W x‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2
      have h5 : 0 ≤ N * M * ψ₁ (N * M * (u - x)) := mul_nonneg hNM.le h1
      calc N * M * ψ₁ (N * M * (u - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2
          ≤ N * M * ψ₁ (N * M * (u - x)) * 1 * (W.card : ℝ) ^ 2 := by gcongr
        _ = (W.card : ℝ) ^ 2 * (N * M * ψ₁ (N * M * (u - x))) := by ring
  rw [integral_const_mul, hscale] at hle
  unfold smoothedLagSum
  calc Real.sqrt (∫ x, N * M * ψ₁ (N * M * (u - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2)
      ≤ Real.sqrt ((W.card : ℝ) ^ 2 * ∫ x, ψ₁ x) := Real.sqrt_le_sqrt hle
    _ = W.card * Real.sqrt (∫ x, ψ₁ x) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

/-- **Majorisation by `R̃`.** If `ψ₂ ≥ 1` on `S` and `ψ₁ ≥ 1` on `[-NMr, NMr]`, then the `L²` mass
of `R` on `S ∩ [c - r, c + r]` is at most `R̃(c)²/(NM)`. -/
theorem setIntegral_normSq_lagSum_le {ψ₁ ψ₂ : ℝ → ℝ} (h : IsSmoothingPair ψ₁ ψ₂) {N M : ℝ}
    (hNM : 0 < N * M) (W : Finset ℝ) {S : Set ℝ} (hS : MeasurableSet S) {c r : ℝ}
    (h₁ : ∀ y, |y| ≤ N * M * r → 1 ≤ ψ₁ y) (h₂ : ∀ x ∈ S, 1 ≤ ψ₂ x) :
    ∫ x in S ∩ Icc (c - r) (c + r), ‖lagSum W x‖ ^ 2 ≤
      smoothedLagSum ψ₁ ψ₂ N M W c ^ 2 / (N * M) := by
  rw [le_div_iff₀ hNM, smoothedLagSum_sq h hNM.le]
  have hset : MeasurableSet (S ∩ Icc (c - r) (c + r)) := hS.inter measurableSet_Icc
  have hfin : volume (S ∩ Icc (c - r) (c + r)) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne
  have hint : IntegrableOn (fun x => ‖lagSum W x‖ ^ 2) (S ∩ Icc (c - r) (c + r)) :=
    Measure.integrableOn_of_bounded hfin (measurable_norm_lagSum_sq W).aestronglyMeasurable
      (M := (W.card : ℝ) ^ 2) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2)
  calc (∫ x in S ∩ Icc (c - r) (c + r), ‖lagSum W x‖ ^ 2) * (N * M)
      = ∫ x in S ∩ Icc (c - r) (c + r), N * M * ‖lagSum W x‖ ^ 2 := by
        rw [integral_const_mul, mul_comm]
    _ ≤ ∫ x in S ∩ Icc (c - r) (c + r), smoothedLagSumIntegrand ψ₁ ψ₂ N M W c x := by
        refine setIntegral_mono_on (hint.const_mul _)
          (integrable_smoothedLagSumIntegrand h N M W c).integrableOn hset fun x hx => ?_
        have hx₁ : 1 ≤ ψ₁ (N * M * (c - x)) := h₁ _ (by
          rw [abs_mul, abs_of_pos hNM]
          gcongr
          rw [abs_le]; constructor <;> linarith [hx.2.1, hx.2.2])
        have hx₂ : 1 ≤ ψ₂ x := h₂ x hx.1
        unfold smoothedLagSumIntegrand
        have : 0 ≤ N * M * ‖lagSum W x‖ ^ 2 := by positivity
        calc N * M * ‖lagSum W x‖ ^ 2 = N * M * 1 * 1 * ‖lagSum W x‖ ^ 2 := by ring
          _ ≤ N * M * ψ₁ (N * M * (c - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2 := by gcongr
    _ ≤ ∫ x, smoothedLagSumIntegrand ψ₁ ψ₂ N M W c x :=
        setIntegral_le_integral (integrable_smoothedLagSumIntegrand h N M W c)
          (Filter.Eventually.of_forall (smoothedLagSumIntegrand_nonneg h hNM.le W c))

/-- The integrand of `Ĩ_m` (with arbitrary measurable arguments of `R̃`) is integrable on
`[1/2, 2]`. -/
theorem integrableOn_norm_lagSum_mul_smoothedLagSum {ψ₁ ψ₂ : ℝ → ℝ} (h : IsSmoothingPair ψ₁ ψ₂)
    {N M : ℝ} (hNM : 0 < N * M) (W : Finset ℝ) {a b : ℝ → ℝ} (ha : Measurable a)
    (hb : Measurable b) :
    IntegrableOn (fun v => ‖lagSum W v‖ * smoothedLagSum ψ₁ ψ₂ N M W (a v) *
      smoothedLagSum ψ₁ ψ₂ N M W (b v)) (Icc (1 / 2 : ℝ) 2) := by
  have hR := measurable_smoothedLagSum h N M W
  have hL := measurable_lagSum W
  set K : ℝ := W.card * Real.sqrt (∫ x, ψ₁ x)
  refine Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (by fun_prop : Measurable fun v => ‖lagSum W v‖ * smoothedLagSum ψ₁ ψ₂ N M W (a v) *
      smoothedLagSum ψ₁ ψ₂ N M W (b v)).aestronglyMeasurable
    (M := W.card * K * K) (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    have := smoothedLagSum_nonneg ψ₁ ψ₂ N M W (a v)
    have := smoothedLagSum_nonneg ψ₁ ψ₂ N M W (b v)
    positivity)]
  have hK : 0 ≤ K := by positivity
  exact mul_le_mul (mul_le_mul (norm_lagSum_le W v) (smoothedLagSum_le h hNM W _)
    (smoothedLagSum_nonneg _ _ _ _ _ _) (Nat.cast_nonneg _)) (smoothedLagSum_le h hNM W _)
    (smoothedLagSum_nonneg _ _ _ _ _ _) (mul_nonneg (Nat.cast_nonneg _) hK)

/-- `Ĩ_m ≥ 0`. -/
theorem smoothedCubicTerm_nonneg (ψ₁ ψ₂ : ℝ → ℝ) (N M : ℝ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ) :
    0 ≤ smoothedCubicTerm ψ₁ ψ₂ N M W m₁ m₂ m₃ :=
  setIntegral_nonneg measurableSet_Icc fun v _ => by
    have := smoothedLagSum_nonneg ψ₁ ψ₂ N M W ((m₁ * v + m₃) / (m₂ * v))
    have := smoothedLagSum_nonneg ψ₁ ψ₂ N M W ((m₁ * v + m₃) / m₂)
    positivity

end

end RHTower.GuthMaynard
