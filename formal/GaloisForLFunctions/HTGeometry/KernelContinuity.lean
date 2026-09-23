import GaloisForLFunctions.HTGeometry.KernelTunableSum
import GaloisForLFunctions.HTGeometry.ChristoffelLimitFormula
import GaloisForLFunctions.HTGeometry.ChristoffelBoundedKernel

/-!
# Continuity of the kernel sum

The tunable bound applies with its two points in either order, so on a ball each of the two kernel
sums is at most `(1+ε)` times the other plus a multiple of `‖w − z‖²`.  Both are bounded there, so
the difference is at most `ε·M + C(ε)·‖w − z‖²`: choosing `ε` first and the displacement second gives
continuity outright, with no semicontinuity bookkeeping.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The kernel sum at a point. -/
noncomputable def kernelSum (s : ℕ → ℝ) (w : ℂ) : ℝ :=
  ∑' k, ‖monicOrthoC s k w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k)

theorem kernelSum_nonneg (h : PositiveMomentForm s) (w : ℂ) : 0 ≤ kernelSum s w :=
  tsum_nonneg fun k => div_nonneg (sq_nonneg _) (monicOrtho_inner_self_pos h k).le

/-- A uniform bound on the kernel roots bounds the kernel sum. -/
theorem kernelSum_le_of_bound (h : PositiveMomentForm s) {w : ℂ} {C : ℝ}
    (hC : ∀ N, kernelRoot s (fun j => monicOrthoC s j w) N ≤ C) :
    kernelSum s w ≤ C ^ (2 : ℕ) := by
  have hnn : ∀ k : ℕ,
      0 ≤ ‖monicOrthoC s k w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k) :=
    fun k => div_nonneg (sq_nonneg _) (monicOrtho_inner_self_pos h k).le
  have hsum : Summable fun k => ‖monicOrthoC s k w‖ ^ (2 : ℕ) /
      momentInner s (monicOrtho s k) (monicOrtho s k) := by
    have hs := summable_of_kernelRoot_le h w hC
    rwa [summable_normSq_eq_norm s w] at hs
  rw [kernelSum]
  refine hsum.tsum_le_of_sum_le fun t => ?_
  obtain ⟨n, hn⟩ := t.exists_nat_subset_range
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hn fun k _ _ => hnn k) ?_
  rcases n with _ | N
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact sq_nonneg _
  · rw [← kernelRoot_sq h]
    exact pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hC N) 2

/-- **The kernel sum is continuous.** -/
theorem continuousAt_kernelSum (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (z₀ : ℂ) :
    ContinuousAt (kernelSum s) z₀ := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  set h0v : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) with hh0v
  set r : ℝ := ‖z₀‖ + 2 with hrdef
  set Sb : ℝ := ballBoundQ s S P r with hSbdef
  set Pb : ℝ := ballBoundR s S P r with hPbdef
  have hz₀r : ‖z₀‖ ≤ r := by rw [hrdef]; linarith
  have hQb : ∀ w : ℂ, ‖w‖ ≤ r → ∀ N, kernelRoot s (fun j => monicOrthoC s j w) N ≤ Sb :=
    fun w hw N => kernelRoot_le_ballBoundQ h hS hP hw N
  have hPbb : ∀ w : ℂ, ‖w‖ ≤ r → ∀ N, kernelRoot s (fun j => secondKindC s j w) N ≤ Pb :=
    fun w hw N => kernelRoot_le_ballBoundR h hS hP hw N
  rw [Metric.continuousAt_iff]
  intro δ hδ
  set e : ℝ := δ / (2 * (Sb ^ (2 : ℕ) + 1)) with hedef
  have hepos : 0 < e := div_pos hδ (by positivity)
  have hinv : 0 < e⁻¹ := inv_pos.mpr hepos
  set C : ℝ := 4 * (1 + e⁻¹) * h0v ^ (2 : ℕ) * Sb ^ (2 : ℕ) * Sb ^ (2 : ℕ) * Pb ^ (2 : ℕ) with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_
    · norm_num
    · linarith
    · exact sq_nonneg _
    · exact sq_nonneg _
    · exact sq_nonneg _
    · exact sq_nonneg _
  refine ⟨min 1 (δ / (2 * (C + 1))), lt_min one_pos (div_pos hδ (by linarith)), fun w hw => ?_⟩
  have hd : ‖w - z₀‖ < min 1 (δ / (2 * (C + 1))) := by rwa [dist_eq_norm] at hw
  have hd1 : ‖w - z₀‖ < 1 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : ‖w - z₀‖ < δ / (2 * (C + 1)) := lt_of_lt_of_le hd (min_le_right _ _)
  have hwr : ‖w‖ ≤ r := by
    have := norm_sub_le w z₀
    have h1 : ‖w‖ ≤ ‖w - z₀‖ + ‖z₀‖ := by
      have h2 : ‖w‖ - ‖z₀‖ ≤ ‖w - z₀‖ := by
        simpa using norm_sub_norm_le w z₀
      linarith
    rw [hrdef]
    linarith
  -- the two tunable bounds
  have hA : kernelSum s w ≤ (1 + e) * kernelSum s z₀ + C * ‖w - z₀‖ ^ (2 : ℕ) := by
    have := tsum_kernel_le_tunable h z₀ w hepos (hQb w hwr) (hQb z₀ hz₀r) (hPbb z₀ hz₀r)
    rw [kernelSum, kernelSum]
    refine le_trans this (le_of_eq ?_)
    rw [hCdef]
    ring
  have hB : kernelSum s z₀ ≤ (1 + e) * kernelSum s w + C * ‖w - z₀‖ ^ (2 : ℕ) := by
    have hb := tsum_kernel_le_tunable h w z₀ hepos (hQb z₀ hz₀r) (hQb w hwr) (hPbb w hwr)
    rw [norm_sub_rev z₀ w] at hb
    rw [kernelSum, kernelSum]
    refine le_trans hb (le_of_eq ?_)
    rw [hCdef]
    ring
  have hKw : kernelSum s w ≤ Sb ^ (2 : ℕ) := kernelSum_le_of_bound h (hQb w hwr)
  have hKz : kernelSum s z₀ ≤ Sb ^ (2 : ℕ) := kernelSum_le_of_bound h (hQb z₀ hz₀r)
  have heSb : e * Sb ^ (2 : ℕ) < δ / 2 := by
    rw [hedef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg Sb]
  have hCterm : C * ‖w - z₀‖ ^ (2 : ℕ) < δ / 2 := by
    have hsq : ‖w - z₀‖ ^ (2 : ℕ) ≤ ‖w - z₀‖ := by nlinarith [norm_nonneg (w - z₀)]
    have h1 : C * ‖w - z₀‖ ^ (2 : ℕ) ≤ C * ‖w - z₀‖ := mul_le_mul_of_nonneg_left hsq hCnn
    have h2 : C * ‖w - z₀‖ ≤ C * (δ / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hd2.le hCnn
    have h3 : C * (δ / (2 * (C + 1))) < δ / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · nlinarith [hB, hKw, heSb, hCterm]
  · nlinarith [hA, hKz, heSb, hCterm]

theorem continuous_kernelSum (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (kernelSum s) :=
  continuous_iff_continuousAt.mpr fun z => continuousAt_kernelSum h h0b z

/-- Along the real axis the kernel sum is the real Christoffel series. -/
theorem kernelSum_ofReal (s : ℕ → ℝ) (x : ℝ) :
    kernelSum s ((x : ℝ) : ℂ)
      = ∑' k, ((monicOrtho s k).eval x) ^ (2 : ℕ) /
          momentInner s (monicOrtho s k) (monicOrtho s k) := by
  rw [kernelSum]
  refine tsum_congr fun k => ?_
  rw [Complex.sq_norm, normSq_monicOrthoC_ofReal]

/-- The kernel sum is bounded below by its first term, hence strictly positive. -/
theorem kernelSum_pos (h : PositiveMomentForm s) {w : ℂ} {C : ℝ}
    (hC : ∀ N, kernelRoot s (fun j => monicOrthoC s j w) N ≤ C) : 0 < kernelSum s w := by
  have hsum : Summable fun k => ‖monicOrthoC s k w‖ ^ (2 : ℕ) /
      momentInner s (monicOrtho s k) (monicOrtho s k) := by
    have hs := summable_of_kernelRoot_le h w hC
    rwa [summable_normSq_eq_norm s w] at hs
  have hzero : monicOrthoC s 0 w = 1 := by
    rw [monicOrthoC, monicOrtho_zero]
    simp
  have hfirst : 0 < ‖monicOrthoC s 0 w‖ ^ (2 : ℕ) /
      momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    rw [hzero, norm_one, one_pow]
    exact div_pos one_pos (monicOrtho_inner_self_pos h 0)
  refine lt_of_lt_of_le hfirst ?_
  exact hsum.le_tsum 0 fun k _ =>
    div_nonneg (sq_nonneg _) (monicOrtho_inner_self_pos h k).le

/-- **The limit Christoffel function is continuous.** -/
theorem continuous_christoffelLimit (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (christoffelLimit s) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  have hb : BoundedKernel s 0 := ⟨S, P, hSpos, hPpos, hS, hP⟩
  have hbound : ∀ x : ℝ, ∀ N, kernelRoot s (fun j => monicOrthoC s j ((x : ℝ) : ℂ)) N
      ≤ ballBoundQ s S P (‖((x : ℝ) : ℂ)‖) :=
    fun x N => kernelRoot_le_ballBoundQ h hS hP le_rfl N
  have heq : christoffelLimit s = fun x : ℝ => (kernelSum s ((x : ℝ) : ℂ))⁻¹ := by
    funext x
    have hsum : Summable fun k => ((monicOrtho s k).eval x) ^ (2 : ℕ) /
        momentInner s (monicOrtho s k) (monicOrtho s k) := by
      have hs := summable_of_kernelRoot_le h ((x : ℝ) : ℂ) (hbound x)
      have hcast : (fun k => Complex.normSq (monicOrthoC s k ((x : ℝ) : ℂ)) /
          momentInner s (monicOrtho s k) (monicOrtho s k))
          = fun k => ((monicOrtho s k).eval x) ^ (2 : ℕ) /
            momentInner s (monicOrtho s k) (monicOrtho s k) := by
        funext k
        rw [normSq_monicOrthoC_ofReal]
      rwa [hcast] at hs
    rw [christoffelLimit_eq_inv_tsum h x hsum, kernelSum_ofReal]
  rw [heq]
  refine Continuous.inv₀ ((continuous_kernelSum h hb).comp Complex.continuous_ofReal) ?_
  intro x
  exact (kernelSum_pos h (hbound x)).ne'

end HTGeometry
