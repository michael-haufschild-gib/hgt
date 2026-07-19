import GaloisForLFunctions.HTGeometry.EntryRealUniform

/-!
# The truncated denominator converges uniformly on bounded real intervals

Each truncated entry differs from its limit by `h₀·x` times the tail of a series that converges
uniformly on the ball of radius `r`.  On `|x| < r` the prefactor is bounded by `h₀·r`, so the
difference is uniformly small.

The combination `Bₙ·τ − Dₙ` inherits this, which is the estimate that locates the nodes.
-/

open scoped BigOperators
open Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Uniform convergence of the truncated `D` entry** on `|x| < r`. -/
theorem eventually_nevDreal_close (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P)
    {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : ℝ, |x| < r → |nevDreal s n x - nevDrealInf s x| < ε := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  set c : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) with hcdef
  have hcr : 0 < c * r := mul_pos h0 hr
  have huni := tendstoUniformlyOn_nevD_series h hS hP r
  rw [Metric.tendstoUniformlyOn_iff] at huni
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (huni (ε / (c * r)) (div_pos hε hcr))
  refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn x hx => ?_⟩
  have hmem : ((x : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hclose := hN₀ (n + 1) (by omega) ((x : ℝ) : ℂ) hmem
  rw [Complex.dist_eq] at hclose
  have hcast : |nevDreal s n x - nevDrealInf s x|
      = ‖((nevDreal s n x : ℝ) : ℂ) - ((nevDrealInf s x : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hcast, nevDreal_ofReal_partial, ← nevDinf_ofReal, nevDinf_tsum]
  have hfac : (c : ℂ) * ((x : ℝ) : ℂ) *
        bilinearPartialSum s (fun k => monicOrthoC s k 0)
          (fun z k => monicOrthoC s k z) (n + 1) ((x : ℝ) : ℂ)
      - (c : ℂ) * ((x : ℝ) : ℂ) * ∑' k, monicOrthoC s k 0 * monicOrthoC s k ((x : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = -((c : ℂ) * ((x : ℝ) : ℂ)) *
          ((∑' k, monicOrthoC s k 0 * monicOrthoC s k ((x : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
            - bilinearPartialSum s (fun k => monicOrthoC s k 0)
              (fun z k => monicOrthoC s k z) (n + 1) ((x : ℝ) : ℂ)) := by
    ring
  rw [hfac, norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0]
  calc c * |x| * ‖(∑' k, monicOrthoC s k 0 * monicOrthoC s k ((x : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
            - bilinearPartialSum s (fun k => monicOrthoC s k 0)
              (fun z k => monicOrthoC s k z) (n + 1) ((x : ℝ) : ℂ)‖
      < c * r * (ε / (c * r)) := by
        refine mul_lt_mul' ?_ hclose (norm_nonneg _) hcr
        exact mul_le_mul_of_nonneg_left (le_of_lt hx) h0.le
    _ = ε := by field_simp

/-- **Uniform convergence of the truncated `B` entry** on `|x| < r`. -/
theorem eventually_nevBreal_close (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P)
    {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : ℝ, |x| < r → |nevBreal s n x - nevBrealInf s x| < ε := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  set c : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) with hcdef
  have hcr : 0 < c * r := mul_pos h0 hr
  have huni := tendstoUniformlyOn_nevB_series h hS hP r
  rw [Metric.tendstoUniformlyOn_iff] at huni
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (huni (ε / (c * r)) (div_pos hε hcr))
  refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn x hx => ?_⟩
  have hmem : ((x : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hclose := hN₀ (n + 1) (by omega) ((x : ℝ) : ℂ) hmem
  rw [Complex.dist_eq] at hclose
  have hcast : |nevBreal s n x - nevBrealInf s x|
      = ‖((nevBreal s n x : ℝ) : ℂ) - ((nevBrealInf s x : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hcast, nevBreal_ofReal_partial, ← nevBinf_ofReal, nevBinf_comm_tsum]
  have hfac : (-1 + (c : ℂ) * ((x : ℝ) : ℂ) *
        bilinearPartialSum s (fun k => secondKindC s k 0)
          (fun z k => monicOrthoC s k z) (n + 1) ((x : ℝ) : ℂ))
      - (-1 + (c : ℂ) * ((x : ℝ) : ℂ) * ∑' k, secondKindC s k 0 * monicOrthoC s k ((x : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      = -((c : ℂ) * ((x : ℝ) : ℂ)) *
          ((∑' k, secondKindC s k 0 * monicOrthoC s k ((x : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
            - bilinearPartialSum s (fun k => secondKindC s k 0)
              (fun z k => monicOrthoC s k z) (n + 1) ((x : ℝ) : ℂ)) := by
    ring
  rw [hfac, norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0]
  calc c * |x| * ‖(∑' k, secondKindC s k 0 * monicOrthoC s k ((x : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
            - bilinearPartialSum s (fun k => secondKindC s k 0)
              (fun z k => monicOrthoC s k z) (n + 1) ((x : ℝ) : ℂ)‖
      < c * r * (ε / (c * r)) := by
        refine mul_lt_mul' ?_ hclose (norm_nonneg _) hcr
        exact mul_le_mul_of_nonneg_left (le_of_lt hx) h0.le
    _ = ε := by field_simp

/-- **Uniform convergence of the truncated denominator** on `|x| < r`. -/
theorem eventually_nevDenominator_close (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P)
    (tau : ℝ) {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : ℝ, |x| < r →
      |(nevBreal s n x * tau - nevDreal s n x)
        - (nevBrealInf s x * tau - nevDrealInf s x)| < ε := by
  have htau : 0 < |tau| + 1 := by positivity
  have hεB : 0 < ε / (2 * (|tau| + 1)) := by positivity
  have hεD : 0 < ε / 2 := by positivity
  filter_upwards [eventually_nevBreal_close h hS hP hr hεB,
    eventually_nevDreal_close h hS hP hr hεD] with n hB hD x hx
  have hb := hB x hx
  have hd := hD x hx
  have hsplit : (nevBreal s n x * tau - nevDreal s n x)
        - (nevBrealInf s x * tau - nevDrealInf s x)
      = (nevBreal s n x - nevBrealInf s x) * tau
        - (nevDreal s n x - nevDrealInf s x) := by ring
  rw [hsplit]
  have hbound : |(nevBreal s n x - nevBrealInf s x) * tau|
      ≤ ε / (2 * (|tau| + 1)) * |tau| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hb.le (abs_nonneg tau)
  have hfin : ε / (2 * (|tau| + 1)) * |tau| ≤ ε / 2 := by
    calc ε / (2 * (|tau| + 1)) * |tau|
        ≤ ε / (2 * (|tau| + 1)) * (|tau| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 2 := by field_simp
  calc |(nevBreal s n x - nevBrealInf s x) * tau - (nevDreal s n x - nevDrealInf s x)|
      ≤ |(nevBreal s n x - nevBrealInf s x) * tau| + |nevDreal s n x - nevDrealInf s x| :=
        abs_sub _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add_of_le_of_lt (le_trans hbound hfin) hd
    _ = ε := by ring

end HTGeometry
