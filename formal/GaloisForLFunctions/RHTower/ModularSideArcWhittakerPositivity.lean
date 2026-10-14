import GaloisForLFunctions.RHTower.ModularArcWhittakerPositivity
import GaloisForLFunctions.HTGeometry.ModularSideArcMinimumPrinciple

/-!
# No nonnegative decaying Whittaker combination on the side arcs

For `c_n = 2π(n+1)` and real `a_n, b_n` (`n < N`) let

`v(u, y) = Σ_{n<N} K₀(c_n y) (a_n cos c_n u + b_n sin c_n u)`  (`whittakerArcSum`),

so that `√y v` is a decaying `s = ½` Whittaker sum without constant mode.  The side arcs of the
modular cylinder are `{(u − 1)² + y² = 1, 0 ≤ u ≤ ½}` and `{u² + y² = 1, ½ ≤ u ≤ 1}`: the parts of
the unit semicircle with `½ ≤ |Re z| < 1`, translated into `0 ≤ u ≤ 1`.  They run from
`ρ = ½ + i√3/2` down to the cusps `u = 0` and `u = 1`.

**Theorem** (`whittakerSideArc_coeff_eq_zero`).  If `v ≥ 0` on the side arcs, every `a_n` and
`b_n` vanishes.

Proof.
* **Horn bound** (`whittakerArcSum_cusp_lower`).  A point of the region above the side arcs at
  height `η ≤ ½` lies within `η²` of a side-arc point at the same height, and
  `|∂_u v(·, η)| ≤ D/√η` because `K₀(r) ≤ √(8π/r)/2` (`kMoment_zero_le_gauss`).  So `v ≥ −D η` on
  the horn cross-section.
* The minimum principle above the side arcs (`nonneg_of_nonneg_on_modularSideArc`) gives
  `v(u, 2) ≥ 0` for every `u`.  The function `v(·, 2)` has zero mean, so it vanishes, and the
  orthogonality of the modes gives `K₀(2c_m) a_m/2 = K₀(2c_m) b_m/2 = 0`.

This is the Farkas dual of the existence of a positive measure on the side arcs that annihilates
every nonconstant decaying Whittaker function at `s = ½`.  Together with the bottom-arc statement
`whittakerArc_coeff_eq_zero` it covers the whole unit semicircle.
-/

open MeasureTheory Set Filter Topology
open scoped Interval
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- **Gaussian bound for `K₀`.**  `K₀(r) ≤ √(π/(r/8))/2` for `r > 0`. -/
theorem kMoment_zero_le_gauss {r : ℝ} (hr : 0 < r) :
    kMoment 0 r ≤ Real.sqrt (Real.pi / (r / 8)) / 2 := by
  rw [kMoment_eq, ← integral_gaussian_Ioi (r / 8)]
  refine setIntegral_mono_on (integrableOn_kIntegrand 0 hr)
    (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < r / 8)).integrableOn measurableSet_Ioi
    fun t ht => ?_
  have := kIntegrand_le (j := 0) hr (le_of_lt ht)
  simpa using this

theorem abs_arcTrigDeriv_le (a b : ℕ → ℝ) (n : ℕ) (u : ℝ) :
    |arcTrigDeriv a b n u| ≤ arcFreq n * (|a n| + |b n|) := by
  unfold arcTrigDeriv
  rw [abs_mul, abs_of_pos (arcFreq_pos n)]
  refine mul_le_mul_of_nonneg_left ?_ (arcFreq_pos n).le
  calc |b n * Real.cos (arcFreq n * u) - a n * Real.sin (arcFreq n * u)|
      ≤ |b n * Real.cos (arcFreq n * u)| + |a n * Real.sin (arcFreq n * u)| := abs_sub _ _
    _ ≤ |b n| + |a n| := by
        rw [abs_mul, abs_mul]
        gcongr
        · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
        · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
    _ = |a n| + |b n| := add_comm _ _

/-- The `u`-derivative of the Whittaker sum. -/
theorem hasDerivAt_whittakerArcSum_u (N : ℕ) (a b : ℕ → ℝ) (u y : ℝ) :
    HasDerivAt (fun s => whittakerArcSum N a b s y)
      (∑ n ∈ Finset.range N, kMoment 0 (arcFreq n * y) * arcTrigDeriv a b n u) u :=
  HasDerivAt.fun_sum fun n _ => (hasDerivAt_arcTrig a b n u).const_mul _

/-- The horn constant `D = Σ c_n (|a_n| + |b_n|) √(π/(c_n/8))/2`. -/
def hornConst (N : ℕ) (a b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    arcFreq n * (|a n| + |b n|) * (Real.sqrt (Real.pi / (arcFreq n / 8)) / 2)

theorem hornConst_nonneg (N : ℕ) (a b : ℕ → ℝ) : 0 ≤ hornConst N a b :=
  Finset.sum_nonneg fun n _ => by
    have := arcFreq_pos n
    positivity

/-- **Lipschitz bound at a fixed height.**  `|v(u, η) − v(w, η)| ≤ (D/√η)|u − w|`. -/
theorem abs_whittakerArcSum_sub_le (N : ℕ) (a b : ℕ → ℝ) {η : ℝ} (hη : 0 < η) (u w : ℝ) :
    |whittakerArcSum N a b u η - whittakerArcSum N a b w η| ≤
      hornConst N a b / Real.sqrt η * |u - w| := by
  have hsq : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hbound : ∀ s ∈ (univ : Set ℝ),
      ‖∑ n ∈ Finset.range N, kMoment 0 (arcFreq n * η) * arcTrigDeriv a b n s‖ ≤
        hornConst N a b / Real.sqrt η := by
    intro s _
    rw [Real.norm_eq_abs, hornConst, Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    have hc := arcFreq_pos n
    have hK := kMoment_zero_le_gauss (mul_pos hc hη)
    have hsplit : Real.sqrt (Real.pi / (arcFreq n * η / 8)) =
        Real.sqrt (Real.pi / (arcFreq n / 8)) / Real.sqrt η := by
      rw [show Real.pi / (arcFreq n * η / 8) = Real.pi / (arcFreq n / 8) / η by
        field_simp]
      exact Real.sqrt_div (by positivity) η
    rw [hsplit] at hK
    rw [abs_mul, abs_of_nonneg (kMoment_nonneg 0 _)]
    calc kMoment 0 (arcFreq n * η) * |arcTrigDeriv a b n s|
        ≤ (Real.sqrt (Real.pi / (arcFreq n / 8)) / Real.sqrt η / 2) *
            (arcFreq n * (|a n| + |b n|)) :=
          mul_le_mul hK (abs_arcTrigDeriv_le a b n s) (abs_nonneg _) (by positivity)
      _ = arcFreq n * (|a n| + |b n|) * (Real.sqrt (Real.pi / (arcFreq n / 8)) / 2) /
            Real.sqrt η := by
          field_simp
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => whittakerArcSum N a b s η)
    (fun s _ => (hasDerivAt_whittakerArcSum_u N a b s η).hasDerivWithinAt) hbound convex_univ
    (mem_univ w) (mem_univ u)
  simpa [Real.norm_eq_abs] using h

/-- **Horn bound.**  If `v ≥ 0` on the side arcs, then `v ≥ −δ` on every horn cross-section at a
sufficiently small height. -/
theorem whittakerArcSum_cusp_lower (N : ℕ) (a b : ℕ → ℝ)
    (harc₁ : ∀ u y, 0 < y → 0 ≤ u → u ≤ 1 / 2 → (u - 1) ^ 2 + y ^ 2 = 1 →
      0 ≤ whittakerArcSum N a b u y)
    (harc₂ : ∀ u y, 0 < y → 1 / 2 ≤ u → u ≤ 1 → u ^ 2 + y ^ 2 = 1 →
      0 ≤ whittakerArcSum N a b u y) :
    ∀ δ > 0, ∃ η₀ > 0, ∀ η, 0 < η → η ≤ η₀ → ∀ u, 0 ≤ u → u ≤ 1 →
      (1 ≤ u ^ 2 + η ^ 2 ∨ 1 ≤ (u - 1) ^ 2 + η ^ 2) → -δ ≤ whittakerArcSum N a b u η := by
  intro δ hδ
  set D := hornConst N a b with hDdef
  have hD0 : 0 ≤ D := hornConst_nonneg N a b
  refine ⟨min (1 / 2) (δ / (D + 1)), lt_min (by norm_num) (by positivity),
    fun η hη hηle u hu0 hu1 hreg => ?_⟩
  have hη2 : η ≤ 1 / 2 := hηle.trans (min_le_left _ _)
  have hηδ : η ≤ δ / (D + 1) := hηle.trans (min_le_right _ _)
  have hs : 0 ≤ 1 - η ^ 2 := by nlinarith
  set r := Real.sqrt (1 - η ^ 2) with hr
  have hr2 : r ^ 2 = 1 - η ^ 2 := Real.sq_sqrt hs
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrhalf : 1 / 2 ≤ r := (Real.le_sqrt (by norm_num) hs).mpr (by nlinarith)
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  have h1r : 1 - r ≤ η ^ 2 := by nlinarith
  -- a side-arc point at the same height within `η²`
  obtain ⟨w, hw0, huw⟩ : ∃ w, 0 ≤ whittakerArcSum N a b w η ∧ |u - w| ≤ η ^ 2 := by
    rcases hreg with h | h
    · have hu2 : r ≤ u := by
        rw [hr]
        calc Real.sqrt (1 - η ^ 2) ≤ Real.sqrt (u ^ 2) := Real.sqrt_le_sqrt (by linarith)
          _ = u := Real.sqrt_sq hu0
      refine ⟨r, harc₂ r η hη hrhalf hr1 (by linarith), ?_⟩
      rw [abs_le]
      constructor <;> nlinarith
    · have hu2 : u ≤ 1 - r := by
        have : r ≤ 1 - u := by
          rw [hr]
          calc Real.sqrt (1 - η ^ 2) ≤ Real.sqrt ((u - 1) ^ 2) := Real.sqrt_le_sqrt (by linarith)
            _ = |u - 1| := Real.sqrt_sq_eq_abs _
            _ = 1 - u := by rw [abs_of_nonpos (by linarith)]; ring
        linarith
      refine ⟨1 - r, harc₁ (1 - r) η hη (by linarith) (by linarith) (by nlinarith), ?_⟩
      rw [abs_le]
      constructor <;> nlinarith
  have hvar := abs_whittakerArcSum_sub_le N a b hη u w
  rw [← hDdef] at hvar
  have hsq : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hsq1 : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hdiv : D / Real.sqrt η * η ^ 2 = D * η * Real.sqrt η := by
    have h1 : η / Real.sqrt η = Real.sqrt η := Real.div_sqrt
    rw [div_mul_eq_mul_div, show D * η ^ 2 = D * η * η by ring, mul_div_assoc, h1]
  have hstep : D / Real.sqrt η * |u - w| ≤ D * η := by
    calc D / Real.sqrt η * |u - w| ≤ D / Real.sqrt η * η ^ 2 :=
          mul_le_mul_of_nonneg_left huw (by positivity)
      _ = D * η * Real.sqrt η := hdiv
      _ ≤ D * η * 1 := mul_le_mul_of_nonneg_left hsq1 (by positivity)
      _ = D * η := mul_one _
  have hDη : D * η ≤ δ := by
    calc D * η ≤ D * (δ / (D + 1)) := mul_le_mul_of_nonneg_left hηδ hD0
      _ ≤ (D + 1) * (δ / (D + 1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = δ := by field_simp
  rw [abs_le] at hvar
  linarith [hvar.1]

/-- Vanishing of the coefficients from nonnegativity at height `2`. -/
theorem whittakerArcSum_coeff_eq_zero_of_nonneg_two (N : ℕ) (a b : ℕ → ℝ)
    (hnn : ∀ u, 0 ≤ whittakerArcSum N a b u 2) {m : ℕ} (hm : m < N) : a m = 0 ∧ b m = 0 := by
  have hcont : Continuous fun u => whittakerArcSum N a b u 2 := by
    unfold whittakerArcSum arcTrig; fun_prop
  have hae : ∀ᵐ u, u ∈ Ι (0 : ℝ) 1 → whittakerArcSum N a b u 2 = 0 := by
    have h := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
      (Eventually.of_forall fun u => hnn u) (hcont.intervalIntegrable 0 1)).mp
      (integral_whittakerArcSum N a b 2)
    rw [uIoc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Ioc).mp h
  have hK := kMoment_zero_pos_of_pos (mul_pos (arcFreq_pos m) two_pos)
  have hcos := integral_whittakerArcSum_mul_cos N a b 2 hm
  have hsin := integral_whittakerArcSum_mul_sin N a b 2 hm
  have hc0 : ∫ u in (0 : ℝ)..1, whittakerArcSum N a b u 2 * Real.cos (arcFreq m * u) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
      (hae.mono fun u hu hmem => by rw [hu hmem, zero_mul])]
    simp
  have hs0 : ∫ u in (0 : ℝ)..1, whittakerArcSum N a b u 2 * Real.sin (arcFreq m * u) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
      (hae.mono fun u hu hmem => by rw [hu hmem, zero_mul])]
    simp
  rw [hc0] at hcos
  rw [hs0] at hsin
  constructor
  · rcases mul_eq_zero.mp hcos.symm with h | h
    · exact absurd h hK.ne'
    · linarith
  · rcases mul_eq_zero.mp hsin.symm with h | h
    · exact absurd h hK.ne'
    · linarith

/-- **No nonnegative decaying Whittaker combination on the side arcs.** -/
theorem whittakerSideArc_coeff_eq_zero (N : ℕ) (a b : ℕ → ℝ)
    (harc₁ : ∀ u y, 0 < y → 0 ≤ u → u ≤ 1 / 2 → (u - 1) ^ 2 + y ^ 2 = 1 →
      0 ≤ whittakerArcSum N a b u y)
    (harc₂ : ∀ u y, 0 < y → 1 / 2 ≤ u → u ≤ 1 → u ^ 2 + y ^ 2 = 1 →
      0 ≤ whittakerArcSum N a b u y)
    {m : ℕ} (hm : m < N) : a m = 0 ∧ b m = 0 := by
  refine whittakerArcSum_coeff_eq_zero_of_nonneg_two N a b (fun u => ?_) hm
  exact nonneg_of_nonneg_on_modularSideArc (v := whittakerArcSum N a b)
    (vu := fun u y => ∑ n ∈ Finset.range N, kMoment 0 (arcFreq n * y) * arcTrigDeriv a b n u)
    (vuu := fun u y => ∑ n ∈ Finset.range N,
      kMoment 0 (arcFreq n * y) * -(arcFreq n ^ 2 * arcTrig a b n u))
    (vy := fun u y => ∑ n ∈ Finset.range N,
      -kMoment 1 (arcFreq n * y) * arcFreq n * arcTrig a b n u)
    (vyy := fun u y => ∑ n ∈ Finset.range N,
      kMoment 2 (arcFreq n * y) * arcFreq n ^ 2 * arcTrig a b n u)
    (fun u y _ => hasDerivAt_whittakerArcSum_u N a b u y)
    (fun u y _ => HasDerivAt.fun_sum fun n _ =>
      (hasDerivAt_arcTrigDeriv a b n u).const_mul _)
    (fun u y hy => HasDerivAt.fun_sum fun n _ =>
      (hasDerivAt_kMoment_comp 0 n hy).mul_const _)
    (fun u y hy => HasDerivAt.fun_sum fun n _ => by
      have h := ((hasDerivAt_kMoment_comp 1 n hy).neg.mul_const (arcFreq n)).mul_const
        (arcTrig a b n u)
      refine h.congr_deriv ?_
      ring)
    (fun u y hy => whittakerArcSum_eq N a b hy u)
    (continuousOn_whittakerArcSum N a b) (whittakerArcSum_periodic N a b)
    (whittakerArcSum_decay N a b) harc₁ harc₂ (whittakerArcSum_cusp_lower N a b harc₁ harc₂)
    (by norm_num : (1 : ℝ) ≤ 2)

end

end RHTower
