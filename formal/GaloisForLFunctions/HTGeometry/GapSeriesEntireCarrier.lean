import GaloisForLFunctions.HTGeometry.EventualGapHypertranscendence
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryDoubleExponentialFamily
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# The entire carrier of a gap series

A gap series is a power series supported on a strictly increasing exponent sequence `b`, with
prescribed coefficients `c` on that sequence.  This module builds its entire carrier, computes its
Taylor series, gives the scaling and difference laws in the coefficient variable, identifies the
finitely supported case with a genuine polynomial, and — when the exponent gaps are eventually
superlinear and infinitely many coefficients are nonzero — proves the carrier hypertranscendental.
-/

open Filter PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {b : ℕ → ℕ} {c c' : ℕ → ℂ}

open Classical in
/-- The coefficient sequence supported on `b` with values `c`. -/
noncomputable def gapCoeff (b : ℕ → ℕ) (c : ℕ → ℂ) (m : ℕ) : ℂ :=
  if h : ∃ k, b k = m then c h.choose else 0

theorem gapCoeff_apply (hinj : Function.Injective b) (c : ℕ → ℂ) (k : ℕ) :
    gapCoeff b c (b k) = c k := by
  classical
  have h : ∃ k', b k' = b k := ⟨k, rfl⟩
  rw [gapCoeff, dif_pos h]
  exact congrArg c (hinj h.choose_spec)

theorem gapCoeff_eq_zero_of_notMem {m : ℕ} (c : ℕ → ℂ) (h : ¬ ∃ k, b k = m) :
    gapCoeff b c m = 0 := by
  classical
  rw [gapCoeff, dif_neg h]

theorem exists_eq_of_gapCoeff_ne_zero {m : ℕ} (h : gapCoeff b c m ≠ 0) : ∃ k, m = b k := by
  by_contra hc
  exact h (gapCoeff_eq_zero_of_notMem c (fun ⟨k, hk⟩ => hc ⟨k, hk.symm⟩))

theorem gapCoeff_sub (hinj : Function.Injective b) (c c' : ℕ → ℂ) (m : ℕ) :
    gapCoeff b c m - gapCoeff b c' m = gapCoeff b (fun k => c k - c' k) m := by
  by_cases h : ∃ k, b k = m
  · obtain ⟨k, rfl⟩ := h
    rw [gapCoeff_apply hinj, gapCoeff_apply hinj, gapCoeff_apply hinj]
  · rw [gapCoeff_eq_zero_of_notMem c h, gapCoeff_eq_zero_of_notMem c' h,
      gapCoeff_eq_zero_of_notMem _ h, sub_zero]

theorem gapCoeff_mul_pow (hinj : Function.Injective b) (c : ℕ → ℂ) (u : ℂ) (m : ℕ) :
    gapCoeff b c m * u ^ m = gapCoeff b (fun k => c k * u ^ (b k)) m := by
  by_cases h : ∃ k, b k = m
  · obtain ⟨k, rfl⟩ := h
    rw [gapCoeff_apply hinj, gapCoeff_apply hinj]
  · rw [gapCoeff_eq_zero_of_notMem c h, gapCoeff_eq_zero_of_notMem _ h, zero_mul]

/-! ### Entire coefficient sequences -/

/-- Factorial decay forces every radius to decay. -/
theorem entireCoeffs_of_norm_le_inv_factorial {a : ℕ → ℂ}
    (h : ∀ m, ‖a m‖ ≤ 1 / (m.factorial : ℝ)) : EntireCoeffs a := by
  intro r hr
  refine squeeze_zero (fun m => by positivity) (fun m => ?_)
    (FloorSemiring.tendsto_pow_div_factorial_atTop r)
  have hm : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  calc ‖a m‖ * r ^ m ≤ (1 / (m.factorial : ℝ)) * r ^ m :=
        mul_le_mul_of_nonneg_right (h m) (by positivity)
    _ = r ^ m / (m.factorial : ℝ) := by field_simp

/-- Multiplying the coefficients by a geometric factor preserves entirety. -/
theorem entireCoeffs_mul_geom {a : ℕ → ℂ} (ha : EntireCoeffs a) (u : ℂ) :
    EntireCoeffs (fun m => a m * u ^ m) := by
  intro r hr
  have hkey : ∀ m : ℕ, ‖a m * u ^ m‖ * r ^ m = ‖a m‖ * (‖u‖ * r) ^ m := by
    intro m
    rw [norm_mul, norm_pow, mul_pow]
    ring
  rcases eq_or_lt_of_le (norm_nonneg u) with hu | hu
  · have hu0 : u = 0 := by
      have := hu.symm
      simpa using this
    subst hu0
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [eventually_gt_atTop 0] with m hm
    rw [zero_pow hm.ne', mul_zero, norm_zero, zero_mul]
  · have hpos : 0 < ‖u‖ * r := by positivity
    exact (ha (‖u‖ * r) hpos).congr fun m => (hkey m).symm

theorem entireCoeffs_sub {a a' : ℕ → ℂ} (ha : EntireCoeffs a) (ha' : EntireCoeffs a') :
    EntireCoeffs (fun m => a m - a' m) := by
  intro r hr
  have hlim : Tendsto (fun m => ‖a m‖ * r ^ m + ‖a' m‖ * r ^ m) atTop (nhds 0) := by
    simpa using (ha r hr).add (ha' r hr)
  refine squeeze_zero (fun m => by positivity) (fun m => ?_) hlim
  calc ‖a m - a' m‖ * r ^ m ≤ (‖a m‖ + ‖a' m‖) * r ^ m :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    _ = ‖a m‖ * r ^ m + ‖a' m‖ * r ^ m := by ring

/-- The defect coefficients of a dilation are again entire. -/
theorem entireCoeffs_gapCoeff_defect (hinj : Function.Injective b)
    (hEC : EntireCoeffs (gapCoeff b c)) (u : ℂ) :
    EntireCoeffs (gapCoeff b (fun k => c k * (u ^ (b k) - 1))) := by
  have h1 : EntireCoeffs (gapCoeff b (fun k => c k * u ^ (b k))) := by
    intro r hr
    exact (entireCoeffs_mul_geom hEC u r hr).congr fun m => by
      simp only []
      rw [gapCoeff_mul_pow hinj]
  have hfe : (fun k => c k * u ^ (b k) - c k) = fun k => c k * (u ^ (b k) - 1) := by
    funext k; ring
  intro r hr
  refine ((entireCoeffs_sub h1 hEC) r hr).congr fun m => ?_
  simp only []
  rw [gapCoeff_sub hinj, hfe]

theorem entireCoeffs_gapCoeff (hinj : Function.Injective b)
    (hdec : ∀ k, ‖c k‖ ≤ 1 / ((b k).factorial : ℝ)) : EntireCoeffs (gapCoeff b c) := by
  refine entireCoeffs_of_norm_le_inv_factorial fun m => ?_
  by_cases h : ∃ k, b k = m
  · obtain ⟨k, rfl⟩ := h
    rw [gapCoeff_apply hinj]
    exact hdec k
  · rw [gapCoeff_eq_zero_of_notMem c h, norm_zero]
    positivity

/-! ### The carrier -/

/-- The entire function of a gap series. -/
def gapFun (b : ℕ → ℕ) (c : ℕ → ℂ) : ℂ → ℂ := coeffFun (gapCoeff b c)

theorem gapFun_eq_tsum (b : ℕ → ℕ) (c : ℕ → ℂ) (w : ℂ) :
    gapFun b c w = ∑' m : ℕ, gapCoeff b c m * w ^ m := coeffFun_eq_tsum _ w

theorem differentiable_gapFun (hEC : EntireCoeffs (gapCoeff b c)) :
    Differentiable ℂ (gapFun b c) := differentiable_coeffFun hEC

theorem contDiff_gapFun (hEC : EntireCoeffs (gapCoeff b c)) :
    ContDiff ℂ (⊤ : ℕ∞) (gapFun b c) := (differentiable_gapFun hEC).contDiff

theorem coeff_taylorPS_gapFun (hEC : EntireCoeffs (gapCoeff b c)) (m : ℕ) :
    PowerSeries.coeff m (taylorPS (gapFun b c)) = gapCoeff b c m :=
  taylorPS_ofScalarsSum_of_radius_eq_top (gapCoeff b c) (ofScalars_radius_eq_top hEC) m

/-! ### Summability, scaling and differences -/

theorem summable_coeffFun_term {a : ℕ → ℂ} (ha : EntireCoeffs a) (w : ℂ) :
    Summable fun n : ℕ => a n * w ^ n := by
  have hr : (0 : ℝ) < ‖w‖ + 1 := by positivity
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_term ha hr))
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) (by linarith) n)
    (norm_nonneg _)

theorem coeffFun_sub {a a' : ℕ → ℂ} (ha : EntireCoeffs a) (ha' : EntireCoeffs a') (w : ℂ) :
    coeffFun a w - coeffFun a' w = ∑' n : ℕ, (a n - a' n) * w ^ n := by
  rw [coeffFun_eq_tsum, coeffFun_eq_tsum,
    ← Summable.tsum_sub (summable_coeffFun_term ha w) (summable_coeffFun_term ha' w)]
  exact tsum_congr fun n => by ring

theorem gapFun_scale (hinj : Function.Injective b) (c : ℕ → ℂ) (u w : ℂ) :
    gapFun b c (u * w) = gapFun b (fun k => c k * u ^ (b k)) w := by
  rw [gapFun_eq_tsum, gapFun_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [mul_pow, ← mul_assoc, gapCoeff_mul_pow hinj]

/-- **The translation defect of a gap series.**  Dilating the variable and subtracting acts on the
coefficients by the geometric phase. -/
theorem gapFun_dilation_sub (hinj : Function.Injective b)
    (hEC : EntireCoeffs (gapCoeff b c)) (u w : ℂ) :
    gapFun b c (u * w) - gapFun b c w
      = gapFun b (fun k => c k * (u ^ (b k) - 1)) w := by
  have hEC1 : EntireCoeffs (gapCoeff b (fun k => c k * u ^ (b k))) := by
    intro r hr
    exact (entireCoeffs_mul_geom hEC u r hr).congr fun m => by
      simp only []
      rw [gapCoeff_mul_pow hinj]
  rw [gapFun_scale hinj, gapFun, gapFun, gapFun, coeffFun_sub hEC1 hEC, coeffFun_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [gapCoeff_sub hinj]
  congr 2
  funext k
  ring

/-! ### The finitely supported case and hypertranscendence -/

/-- A gap series with finitely many nonzero coefficients is the corresponding finite sum. -/
theorem gapFun_eq_finsetSum (hinj : Function.Injective b) {K : ℕ}
    (hfin : ∀ k, K ≤ k → c k = 0) (w : ℂ) :
    gapFun b c w = ∑ k ∈ Finset.range K, c k * w ^ (b k) := by
  classical
  rw [gapFun_eq_tsum, tsum_eq_sum (s := (Finset.range K).image b) ?_]
  · rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    exact Finset.sum_congr rfl fun k _ => by rw [gapCoeff_apply hinj]
  · intro m hm
    by_cases h : ∃ k, b k = m
    · obtain ⟨k, rfl⟩ := h
      have hk : K ≤ k := by
        by_contra hc
        exact hm (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩)
      rw [gapCoeff_apply hinj, hfin k hk, zero_mul]
    · rw [gapCoeff_eq_zero_of_notMem c h, zero_mul]

/-- **Hypertranscendence of a superlacunary gap series.**  Eventually superlinear exponent gaps and
infinitely many nonzero coefficients exclude every algebraic differential equation. -/
theorem hypertranscendental_gapFun (hstrict : StrictMono b)
    (hgap : ∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1))
    (hEC : EntireCoeffs (gapCoeff b c))
    (hinf : {k : ℕ | c k ≠ 0}.Infinite) :
    Hypertranscendental (gapFun b c) := by
  refine hypertranscendental_of_eventualGap (contDiff_gapFun hEC) hstrict hgap ?_ ?_
  · intro m hm
    rw [coeff_taylorPS_gapFun hEC] at hm
    exact exists_eq_of_gapCoeff_ne_zero hm
  · have hset : {i : ℕ | PowerSeries.coeff (b i) (taylorPS (gapFun b c)) ≠ 0}
        = {k : ℕ | c k ≠ 0} := by
      ext k
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, coeff_taylorPS_gapFun hEC,
        gapCoeff_apply hstrict.injective]
    rw [hset]
    exact hinf

end

end GaloisForLFunctions.HTGeometry
