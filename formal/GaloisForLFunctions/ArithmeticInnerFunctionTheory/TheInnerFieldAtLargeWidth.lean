import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheLogMeanIsTheInnerMassAtInfinity
import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare

/-!
# The inner field at large width

The empty mollifier `Q = 0` has budget `∫ |ζ|² P_w`. At width `x` this is a second moment over the heights up to `x`, and the mean-square bound `∫_{−N}^{N} |ζ|² ≤ D N (1 + log N)²` controls it dyadically.

* **The budget at width `x`** (`exists_budget_zero_le`). `∫ |ζ|² P_{½+x+it} ≤ C (1 + log 5x)²`, for `|t| ≤ x`.
* **The inner field at width `x`** (`exists_innerField_le_loglog`). `I(½ + x + it) ≤ log(1 + log 5x) + C`, unconditionally.
* **The depth of the zeros** (`exists_sum_depth_le`). `Σ_{|γ−t|≤T} m_ρ b_ρ ≤ (5/2) T (log(1 + log 5T) + C)`.

So moment data bound the inner mass at infinity by `log log x`, and the budget has to be sharpened by a mollifier to do better: the field is bounded iff the depth density is `O(T)`, and it vanishes iff that density is `o(T)` (`bounded_innerField_iff_depthDensity`, `tendsto_innerField_iff_depthDensity`).
-/

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- The mean square on the critical line as a function of the height. -/
private def lineSq (τ : ℝ) : ℝ := ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2

private theorem lineSq_nonneg (τ : ℝ) : 0 ≤ lineSq τ := sq_nonneg _

private theorem continuous_lineSq : Continuous lineSq := by
  have hne : ∀ τ : ℝ, (1 / 2 + (τ : ℂ) * I) ≠ 1 := fun τ h => by
    have := congrArg Complex.re h
    norm_num at this
  have hc : Continuous fun τ : ℝ => riemannZeta (1 / 2 + τ * I) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have h1 : ContinuousAt riemannZeta (1 / 2 + (τ : ℂ) * I) :=
      (differentiableAt_riemannZeta (hne τ)).continuousAt
    have h2 : ContinuousAt (fun τ : ℝ => (1 / 2 + (τ : ℂ) * I)) τ := by fun_prop
    exact ContinuousAt.comp (f := fun τ : ℝ => (1 / 2 + (τ : ℂ) * I)) h1 h2
  exact hc.norm.pow 2

/-- The mean-square bound in the form used here. -/
private theorem exists_integral_lineSq_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 4 ≤ N →
      ∫ τ in Ioc (-(N : ℝ)) N, lineSq τ ≤ D * N * (1 + Real.log N) ^ 2 := by
  obtain ⟨D, hD, h⟩ := exists_integral_normSq_zeta_critical_le
  refine ⟨D, hD, fun N hN => ?_⟩
  have hN0 : (-(N : ℝ)) ≤ N := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have h1 := h hN
  rw [intervalIntegral.integral_of_le hN0] at h1
  have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; rfl
  simp only [e] at h1
  exact h1

private theorem kernel_nonneg {x : ℝ} (hx : 0 < x) (t τ : ℝ) :
    0 ≤ halfPlanePoissonKernel (centre x t) τ :=
  (halfPlanePoissonKernel_pos (by rw [centre_re]; linarith) τ).le

private theorem kernel_eq (x t τ : ℝ) :
    halfPlanePoissonKernel (centre x t) τ = x / (π * (x ^ 2 + (τ - t) ^ 2)) := by
  simp only [halfPlanePoissonKernel, centre_re, centre_im]
  ring_nf

/-- The kernel is at most `1/(πx)`. -/
private theorem kernel_le_top {x : ℝ} (hx : 0 < x) (t τ : ℝ) :
    halfPlanePoissonKernel (centre x t) τ ≤ 1 / (π * x) := by
  rw [kernel_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  have hπ := Real.pi_pos
  nlinarith [mul_nonneg hπ.le (sq_nonneg (τ - t))]

/-- Away from the centre the kernel decays quadratically. -/
private theorem kernel_le_shell {x t τ N : ℝ} (hx : 0 < x) (ht : |t| ≤ N / 2) (hN : 0 < N)
    (hτ : N ≤ |τ|) : halfPlanePoissonKernel (centre x t) τ ≤ 4 * x / (π * N ^ 2) := by
  have hd : N / 2 ≤ |τ - t| := by
    have h1 := abs_sub_abs_le_abs_sub τ t
    linarith
  have hsq : (N / 2) ^ 2 ≤ (τ - t) ^ 2 := by
    rw [← sq_abs (τ - t)]
    exact pow_le_pow_left₀ (by positivity) hd 2
  rw [kernel_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  have hπ := Real.pi_pos
  have h2 : x * (π * N ^ 2) ≤ 4 * x * (π * (x ^ 2 + (τ - t) ^ 2)) := by
    have h3 : N ^ 2 ≤ 4 * (x ^ 2 + (τ - t) ^ 2) := by nlinarith [sq_nonneg x]
    have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hx.le hπ.le)
    linarith
  exact h2

/-- The weights of the dyadic shells. -/
private def shellWeight (j : ℕ) : ℝ := ((j : ℝ) + 2) ^ 2 * (1 / 2) ^ j

private theorem summable_shellWeight : Summable shellWeight := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).congr fun j => ?_
  simp only [shellWeight]
  ring

private theorem shellWeight_nonneg (j : ℕ) : 0 ≤ shellWeight j := by
  unfold shellWeight
  positivity

/-- **One dyadic shell.** -/
private theorem integral_shell_le {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ N : ℕ, 4 ≤ N → ∫ τ in Ioc (-(N : ℝ)) N, lineSq τ ≤ D * N * (1 + Real.log N) ^ 2)
    {x t : ℝ} (hx : 1 ≤ x) (ht : |t| ≤ x) {N₀ : ℕ} (hN₀ : 4 * x ≤ N₀) (n : ℕ) :
    ∫ τ in Ioc (-((2 ^ (n + 1) * N₀ : ℕ) : ℝ)) ((2 ^ (n + 1) * N₀ : ℕ) : ℝ),
        lineSq τ * halfPlanePoissonKernel (centre x t) τ ≤
      (∫ τ in Ioc (-((2 ^ n * N₀ : ℕ) : ℝ)) ((2 ^ n * N₀ : ℕ) : ℝ),
        lineSq τ * halfPlanePoissonKernel (centre x t) τ) +
        4 * D / π * (1 + Real.log N₀) ^ 2 * shellWeight n := by
  have hx0 : 0 < x := by linarith
  have hπ := Real.pi_pos
  have hN₀r : (4 : ℝ) ≤ N₀ := by nlinarith
  have hN₀1 : (1 : ℝ) ≤ N₀ := by linarith
  set A : ℝ := ((2 ^ n * N₀ : ℕ) : ℝ) with hA
  set B : ℝ := ((2 ^ (n + 1) * N₀ : ℕ) : ℝ) with hB
  have hAv : A = 2 ^ n * N₀ := by rw [hA]; push_cast; ring
  have hBA : B = 2 * A := by rw [hB, hAv]; push_cast; ring
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hA0 : 4 * x * 2 ^ n ≤ A := by
    rw [hAv]
    nlinarith
  have hApos : 0 < A := by nlinarith [mul_pos hx0 (by positivity : (0 : ℝ) < 2 ^ n)]
  have hsub : Ioc (-A) A ⊆ Ioc (-B) B := Ioc_subset_Ioc (by rw [hBA]; linarith) (by rw [hBA]; linarith)
  have hf : Integrable fun τ : ℝ => lineSq τ * halfPlanePoissonKernel (centre x t) τ :=
    integrable_norm_sq_zeta_poisson (by rw [centre_re]; linarith)
  have hdiff := integral_diff (μ := volume) measurableSet_Ioc hf.integrableOn hsub
  -- the shell is bounded by the sup of the kernel times the mean square
  have hc : 0 ≤ 4 * x / (π * A ^ 2) := by positivity
  have hshell : ∫ τ in Ioc (-B) B \ Ioc (-A) A, lineSq τ * halfPlanePoissonKernel (centre x t) τ ≤
      4 * x / (π * A ^ 2) * ∫ τ in Ioc (-B) B, lineSq τ := by
    have hcont : IntegrableOn lineSq (Ioc (-B) B) :=
      continuous_lineSq.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    calc ∫ τ in Ioc (-B) B \ Ioc (-A) A, lineSq τ * halfPlanePoissonKernel (centre x t) τ
        ≤ ∫ τ in Ioc (-B) B \ Ioc (-A) A, lineSq τ * (4 * x / (π * A ^ 2)) := by
          refine setIntegral_mono_on hf.integrableOn
            ((hcont.mono_set diff_subset).mul_const _) (measurableSet_Ioc.diff measurableSet_Ioc) ?_
          rintro τ ⟨-, hτ⟩
          have hτA : A ≤ |τ| := by
            by_contra hlt
            push Not at hlt
            have h1 := abs_lt.mp hlt
            exact hτ ⟨h1.1, h1.2.le⟩
          refine mul_le_mul_of_nonneg_left ?_ (lineSq_nonneg τ)
          refine kernel_le_shell hx0 ?_ hApos hτA
          nlinarith
      _ = 4 * x / (π * A ^ 2) * ∫ τ in Ioc (-B) B \ Ioc (-A) A, lineSq τ := by
          rw [integral_mul_const]
          ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          exact setIntegral_mono_set hcont (Eventually.of_forall lineSq_nonneg)
            (Eventually.of_forall diff_subset)
  -- the mean-square bound on the larger interval
  have hNB : 4 ≤ 2 ^ (n + 1) * N₀ := by
    have h1 : 4 ≤ N₀ := by exact_mod_cast hN₀r
    calc 4 ≤ N₀ := h1
      _ ≤ 2 ^ (n + 1) * N₀ := Nat.le_mul_of_pos_left _ (by positivity)
  have hmean := hbound _ hNB
  rw [← hB] at hmean
  have hL0 : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg _
  have hlogB : 1 + Real.log B ≤ (1 + Real.log N₀) * ((n : ℝ) + 2) := by
    have e : B = 2 ^ (n + 1) * N₀ := by rw [hB]; push_cast; ring
    have h1 : Real.log B = (n + 1) * Real.log 2 + Real.log N₀ := by
      rw [e, Real.log_mul (by positivity) (by linarith), Real.log_pow]
      push_cast
      ring
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left hl2 hn, mul_nonneg hL0 hn]
  have hlogB0 : 0 ≤ 1 + Real.log B := by
    have : 0 ≤ Real.log B := Real.log_nonneg (by rw [hBA]; nlinarith)
    linarith
  have hsqB : (1 + Real.log B) ^ 2 ≤ ((1 + Real.log N₀) * ((n : ℝ) + 2)) ^ 2 :=
    pow_le_pow_left₀ hlogB0 hlogB 2
  -- the product of the two bounds
  have hprod : 4 * x / (π * A ^ 2) * (D * B * (1 + Real.log B) ^ 2) ≤
      4 * D / π * (1 + Real.log N₀) ^ 2 * shellWeight n := by
    have h1 : 4 * x / (π * A ^ 2) * (D * B * (1 + Real.log B) ^ 2) =
        (8 * x / A) * (D / π) * (1 + Real.log B) ^ 2 := by
      rw [hBA]
      field_simp
      ring
    have h2 : 8 * x / A ≤ 4 * (1 / 2) ^ n := by
      rw [div_le_iff₀ hApos, hAv]
      have e : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      have h3 : 4 * (1 / 2 : ℝ) ^ n * (2 ^ n * N₀) = 4 * N₀ := by
        calc 4 * (1 / 2 : ℝ) ^ n * (2 ^ n * N₀) = 4 * N₀ * ((1 / 2 : ℝ) ^ n * 2 ^ n) := by ring
          _ = 4 * N₀ := by rw [e, mul_one]
      rw [h3]
      nlinarith
    have hDπ : 0 ≤ D / π := by positivity
    rw [h1]
    calc 8 * x / A * (D / π) * (1 + Real.log B) ^ 2
        ≤ 4 * (1 / 2) ^ n * (D / π) * ((1 + Real.log N₀) * ((n : ℝ) + 2)) ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h2 hDπ) hsqB (sq_nonneg _) (by positivity)
      _ = _ := by
          simp only [shellWeight]
          ring
  have htot := mul_le_mul_of_nonneg_left hmean hc
  linarith

/-- **The budget at width `x`.** -/
theorem exists_budget_zero_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x t : ℝ}, 1 ≤ x → |t| ≤ x →
      budget (centre x t) 0 ≤ C * (1 + Real.log (5 * x)) ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := exists_integral_lineSq_le
  have hπ := Real.pi_pos
  set S : ℝ := ∑' j, shellWeight j with hS
  have hS0 : 0 ≤ S := tsum_nonneg shellWeight_nonneg
  refine ⟨5 * D / π + 4 * D / π * S, by positivity, fun {x t} hx ht => ?_⟩
  have hx0 : 0 < x := by linarith
  set N₀ : ℕ := ⌈4 * x⌉₊ with hN₀
  have hN₁ : 4 * x ≤ N₀ := Nat.le_ceil _
  have hN₂ : (N₀ : ℝ) ≤ 5 * x := by
    have := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * x)).le
    linarith
  have hN₀r : (4 : ℝ) ≤ N₀ := by nlinarith
  have hN4 : 4 ≤ N₀ := by exact_mod_cast hN₀r
  have hL0 : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg _
  have hL : (1 + Real.log N₀) ^ 2 ≤ (1 + Real.log (5 * x)) ^ 2 := by
    refine pow_le_pow_left₀ (by linarith) ?_ 2
    have := Real.log_le_log (by linarith) hN₂
    linarith
  -- the partial integrals
  have hf : Integrable fun τ : ℝ => lineSq τ * halfPlanePoissonKernel (centre x t) τ :=
    integrable_norm_sq_zeta_poisson (by rw [centre_re]; linarith)
  have hbase : ∫ τ in Ioc (-(N₀ : ℝ)) N₀, lineSq τ * halfPlanePoissonKernel (centre x t) τ ≤
      5 * D / π * (1 + Real.log N₀) ^ 2 := by
    have hcont : IntegrableOn lineSq (Ioc (-(N₀ : ℝ)) N₀) :=
      continuous_lineSq.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have h1 : ∫ τ in Ioc (-(N₀ : ℝ)) N₀, lineSq τ * halfPlanePoissonKernel (centre x t) τ ≤
        ∫ τ in Ioc (-(N₀ : ℝ)) N₀, lineSq τ * (1 / (π * x)) := by
      refine setIntegral_mono_on hf.integrableOn (hcont.mul_const _) measurableSet_Ioc fun τ _ => ?_
      exact mul_le_mul_of_nonneg_left (kernel_le_top hx0 t τ) (lineSq_nonneg τ)
    rw [integral_mul_const] at h1
    have h2 := mul_le_mul_of_nonneg_right (hbound N₀ hN4) (by positivity : 0 ≤ 1 / (π * x))
    have h3 : D * N₀ * (1 + Real.log N₀) ^ 2 * (1 / (π * x)) ≤ 5 * D / π * (1 + Real.log N₀) ^ 2 := by
      have h4 : (N₀ : ℝ) * (1 / (π * x)) ≤ 5 / π := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hπ]
        nlinarith
      have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hD (sq_nonneg (1 + Real.log N₀)))
      calc D * N₀ * (1 + Real.log N₀) ^ 2 * (1 / (π * x))
          = D * (1 + Real.log N₀) ^ 2 * (N₀ * (1 / (π * x))) := by ring
        _ ≤ D * (1 + Real.log N₀) ^ 2 * (5 / π) := h5
        _ = _ := by ring
    linarith
  have hpartial : ∀ n : ℕ, ∫ τ in Ioc (-((2 ^ n * N₀ : ℕ) : ℝ)) ((2 ^ n * N₀ : ℕ) : ℝ),
      lineSq τ * halfPlanePoissonKernel (centre x t) τ ≤
        (5 * D / π + 4 * D / π * ∑ j ∈ Finset.range n, shellWeight j) * (1 + Real.log N₀) ^ 2 := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      exact hbase
    | succ n ih =>
      refine (integral_shell_le hD hbound hx ht hN₁ n).trans ?_
      rw [Finset.sum_range_succ]
      have e : (5 * D / π + 4 * D / π * (∑ j ∈ Finset.range n, shellWeight j + shellWeight n)) *
            (1 + Real.log N₀) ^ 2 =
          (5 * D / π + 4 * D / π * ∑ j ∈ Finset.range n, shellWeight j) * (1 + Real.log N₀) ^ 2 +
            4 * D / π * (1 + Real.log N₀) ^ 2 * shellWeight n := by ring
      rw [e]
      linarith
  have hunif : ∀ n : ℕ, ∫ τ in (-((2 ^ n * N₀ : ℕ) : ℝ))..((2 ^ n * N₀ : ℕ) : ℝ),
      lineSq τ * halfPlanePoissonKernel (centre x t) τ ≤
        (5 * D / π + 4 * D / π * S) * (1 + Real.log N₀) ^ 2 := fun n => by
    have hle : (-((2 ^ n * N₀ : ℕ) : ℝ)) ≤ ((2 ^ n * N₀ : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((2 ^ n * N₀ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    rw [intervalIntegral.integral_of_le hle]
    refine (hpartial n).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    have hsum : ∑ j ∈ Finset.range n, shellWeight j ≤ S :=
      summable_shellWeight.sum_le_tsum _ fun j _ => shellWeight_nonneg j
    have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * D / π)
    linarith
  have hgrow : Tendsto (fun n : ℕ => ((2 ^ n * N₀ : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp ?_
    refine tendsto_atTop_mono (fun n => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hlim := intervalIntegral_tendsto_integral hf (tendsto_neg_atTop_atBot.comp hgrow) hgrow
  have hle := le_of_tendsto' hlim hunif
  have hbudget : budget (centre x t) 0 =
      ∫ τ : ℝ, lineSq τ * halfPlanePoissonKernel (centre x t) τ := by
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp [lineSq]
  rw [hbudget]
  exact hle.trans (mul_le_mul_of_nonneg_left hL (by positivity))

/-- **The inner field at width `x`.** -/
theorem exists_innerField_le_loglog :
    ∃ C : ℝ, ∀ {x t : ℝ}, 3 ≤ x → |t| ≤ x →
      innerField (centre x t) ≤ Real.log (1 + Real.log (5 * x)) + C := by
  obtain ⟨C, hC0, hC⟩ := exists_budget_zero_le
  refine ⟨Real.log (16 * (C + 1)) / 2, fun {x t} hx ht => ?_⟩
  set w := centre x t with hw
  have hre : w.re = 1 / 2 + x := centre_re x t
  have h0 : zetaEntire w ≠ 0 := zetaEntire_centre_ne_zero (by linarith) t
  have hglb := (isGLB_budget_innerField (w := w) (by rw [hre]; linarith) h0).1
    ⟨0, by simp, rfl⟩
  have hbud := hC (x := x) (t := t) (by linarith) ht
  -- the normalization is bounded below
  have hw1 : w ≠ 1 := fun h => by
    rw [h] at hre
    norm_num at hre
    linarith
  have hnorm : 3 ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    rw [hre, abs_of_pos (by linarith)] at h
    linarith
  have hsub : ‖w‖ - 1 ≤ ‖w - 1‖ := by
    have h := norm_sub_norm_le w 1
    rwa [norm_one] at h
  have hz : 3 / 5 ≤ ‖riemannZeta w‖ := by
    have h := norm_riemannZeta_sub_one_le (w := w) (by rw [hre]; linarith)
    rw [hre] at h
    have h2 : 1 / (1 / 2 + x - 1) ≤ 2 / 5 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta w)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at h3
    linarith
  have hratio : 1 / 4 ≤ ‖zetaEntire w‖ / ‖w‖ := by
    rw [zetaEntire_eq hw1, norm_mul, le_div_iff₀ (by linarith)]
    have hsub' : (2 / 3) * ‖w‖ ≤ ‖w - 1‖ := by linarith
    have h1 := mul_le_mul hsub' hz (by norm_num) (norm_nonneg _)
    nlinarith
  have hsq : (1 / 4 : ℝ) ^ 2 ≤ (‖zetaEntire w‖ / ‖w‖) ^ 2 := pow_le_pow_left₀ (by norm_num) hratio 2
  have hexp : Real.exp (2 * innerField w) * (1 / 16) ≤ C * (1 + Real.log (5 * x)) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsq (Real.exp_pos (2 * innerField w)).le
    have hrw : (1 / 4 : ℝ) ^ 2 = 1 / 16 := by norm_num
    rw [hrw] at h1
    exact h1.trans (hglb.trans hbud)
  have hL : 0 < 1 + Real.log (5 * x) := by
    have : 0 ≤ Real.log (5 * x) := Real.log_nonneg (by linarith)
    linarith
  have hfin : Real.exp (2 * innerField w) ≤ 16 * (C + 1) * (1 + Real.log (5 * x)) ^ 2 := by
    have hsqpos := sq_nonneg (1 + Real.log (5 * x))
    nlinarith
  have hlog := (Real.le_log_iff_exp_le (by positivity)).mpr hfin
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **The depth of the zeros up to height `T`.** -/
theorem exists_sum_depth_le :
    ∃ C : ℝ, ∀ {T t : ℝ}, 3 ≤ T → |t| ≤ T → ∀ Z : Finset ZetaRightZero,
      (∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) →
        ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ 5 / 2 * T * (Real.log (1 + Real.log (5 * T)) + C) := by
  obtain ⟨C, hC⟩ := exists_innerField_le_loglog
  refine ⟨C, fun {T t} hT ht Z hZ => ?_⟩
  refine (sum_depth_height_le (by linarith) Z hZ).trans ?_
  exact mul_le_mul_of_nonneg_left (hC hT ht) (by positivity)

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
