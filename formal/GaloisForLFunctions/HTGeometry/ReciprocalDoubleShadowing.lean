import GaloisForLFunctions.HTGeometry.EvenReciprocalTotalPositivity
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Double shadowing: two real factors compensate one conjugate pair

For real `x, y` and complex `w` the reciprocal of
`G(σ) = (1 − xσ²)(1 − yσ²)(1 − wσ²)(1 − w̄σ²)` has the coefficient
`c_n = Σ_{i+j+k+l=n} x^i y^j w^k w̄^l` at `σ^{2n}`.

**Theorem** (`evenRecipNonneg_doubleShadow`).  If `‖w‖ ≤ x` and `‖w‖ ≤ y`, every `c_n` is
nonnegative.

One real factor is not enough.  For `x = ‖w‖` and `w < 0`, the coefficient of `σ²` in
`1/((1 − xσ²)(1 − wσ²)²)` is `x + 2w < 0`.

Proof.  Put `r = ‖w‖`, `c = Re w` and `q_m = Σ_{k+l=m} w^k w̄^l` (`pairSeq`).  Each `q_m` is
real, `q_{m+2} = 2c q_{m+1} − r² q_m` and `|q_m| ≤ (m+1) r^m`.  For `D_n`, the coefficients of
`(1 − ru)^{−2} Σ q_m u^m`, induction gives `2(r − c) D_n = (n+2) r^{n+1} − q_{n+1} ≥ 0`.  The
series `(1 − xu)^{−1}` is `(1 − ru)^{−1}` times the nonnegative series `(1 − ru)/(1 − xu)`
(`shadowSeq`).  So `c = shadow_x ⋆ shadow_y ⋆ D ≥ 0`.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The pair sequence -/

/-- `h_m(a, b) = Σ_{k ≤ m} a^k b^{m−k}`. -/
def hTwo (a b : ℂ) (m : ℕ) : ℂ := ∑ k ∈ Finset.range (m + 1), a ^ k * b ^ (m - k)

theorem hTwo_zero (a b : ℂ) : hTwo a b 0 = 1 := by simp [hTwo]

theorem hTwo_succ (a b : ℂ) (m : ℕ) : hTwo a b (m + 1) = a * hTwo a b m + b ^ (m + 1) := by
  unfold hTwo
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show m + 1 - (k + 1) = m - k by omega, pow_succ]
  ring

theorem hTwo_succ' (a b : ℂ) (m : ℕ) : hTwo a b (m + 1) = b * hTwo a b m + a ^ (m + 1) := by
  unfold hTwo
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show m + 1 - k = m - k + 1 by omega, pow_succ]
  ring

theorem hTwo_comm (a b : ℂ) (m : ℕ) : hTwo a b m = hTwo b a m := by
  induction m with
  | zero => simp [hTwo]
  | succ m ih => rw [hTwo_succ', hTwo_succ b a, ih]

theorem hTwo_rec (a b : ℂ) (m : ℕ) :
    hTwo a b (m + 2) = (a + b) * hTwo a b (m + 1) - a * b * hTwo a b m := by
  rw [hTwo_succ a b (m + 1)]
  linear_combination (-b) * hTwo_succ a b m

theorem norm_hTwo_le {a b : ℂ} {R : ℝ} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (m : ℕ) :
    ‖hTwo a b m‖ ≤ (m + 1) * R ^ m := by
  unfold hTwo
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (m + 1), ‖a ^ k * b ^ (m - k)‖ ≤ R ^ m := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [norm_mul, norm_pow, norm_pow, ← Nat.add_sub_cancel' hkm, pow_add,
      Nat.add_sub_cancel_left]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha k)
      (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity)
      (pow_nonneg ((norm_nonneg a).trans ha) _)
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [Finset.card_range, nsmul_eq_mul]
  push_cast
  rfl

/-- The real sequence `q_m = Σ_{k+l=m} w^k w̄^l`. -/
def pairSeq (w : ℂ) (m : ℕ) : ℝ := (hTwo w (starRingEnd ℂ w) m).re

theorem hTwo_conj_eq_pairSeq (w : ℂ) (m : ℕ) :
    hTwo w (starRingEnd ℂ w) m = ((pairSeq w m : ℝ) : ℂ) := by
  have h : starRingEnd ℂ (hTwo w (starRingEnd ℂ w) m) = hTwo w (starRingEnd ℂ w) m := by
    unfold hTwo
    rw [map_sum]
    have := hTwo_comm (starRingEnd ℂ w) w m
    unfold hTwo at this
    simp only [map_mul, map_pow, Complex.conj_conj]
    exact this
  exact (Complex.conj_eq_iff_re.mp h).symm

theorem pairSeq_zero (w : ℂ) : pairSeq w 0 = 1 := by simp [pairSeq, hTwo]

theorem pairSeq_one (w : ℂ) : pairSeq w 1 = 2 * w.re := by
  unfold pairSeq
  rw [hTwo_succ, hTwo_zero]
  simp
  ring

theorem pairSeq_rec (w : ℂ) (m : ℕ) :
    pairSeq w (m + 2) = 2 * w.re * pairSeq w (m + 1) - ‖w‖ ^ 2 * pairSeq w m := by
  unfold pairSeq
  rw [hTwo_rec, Complex.add_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.sub_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]

theorem abs_pairSeq_le (w : ℂ) (m : ℕ) : |pairSeq w m| ≤ (m + 1) * ‖w‖ ^ m :=
  (Complex.abs_re_le_norm _).trans (norm_hTwo_le le_rfl (Complex.norm_conj w).le m)

/-! ### Cauchy products -/

theorem cauchyConv_nonneg {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    0 ≤ cauchyConv a b n :=
  Finset.sum_nonneg fun m _ => mul_nonneg (ha m) (hb _)

theorem cauchyConv_geom_zero (r : ℝ) (b : ℕ → ℝ) : cauchyConv (fun n => r ^ n) b 0 = b 0 := by
  simp [cauchyConv]

theorem cauchyConv_geom_succ (r : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    cauchyConv (fun n => r ^ n) b (n + 1) = r * cauchyConv (fun n => r ^ n) b n + b (n + 1) := by
  unfold cauchyConv
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show n + 1 - (m + 1) = n - m by omega, pow_succ]
  ring

/-- `(1 − ru)/(1 − xu) = 1 + Σ_{n ≥ 1} (x − r) x^{n−1} uⁿ`. -/
def shadowSeq (x r : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else (x - r) * x ^ (n - 1)

theorem shadowSeq_nonneg {x r : ℝ} (hr : 0 ≤ r) (hrx : r ≤ x) (n : ℕ) : 0 ≤ shadowSeq x r n := by
  unfold shadowSeq
  split_ifs
  · exact zero_le_one
  · exact mul_nonneg (by linarith) (pow_nonneg (hr.trans hrx) _)

theorem cauchyConv_shadowSeq_geom (x r : ℝ) (n : ℕ) :
    cauchyConv (shadowSeq x r) (fun n => r ^ n) n = x ^ n := by
  rcases n with _ | k
  · simp [cauchyConv, shadowSeq]
  · unfold cauchyConv
    rw [Finset.sum_range_succ']
    have e1 : ∀ i, shadowSeq x r (i + 1) = (x - r) * x ^ i := fun i => by simp [shadowSeq]
    have e0 : shadowSeq x r 0 = 1 := by simp [shadowSeq]
    simp only [e1, e0, Nat.sub_zero, one_mul]
    have hg := geom_sum₂_mul x r (k + 1)
    simp only [Nat.add_sub_cancel] at hg
    have hs : ∑ i ∈ Finset.range (k + 1), (x - r) * x ^ i * r ^ (k + 1 - (i + 1)) =
        (x - r) * ∑ i ∈ Finset.range (k + 1), x ^ i * r ^ (k - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show k + 1 - (i + 1) = k - i by omega]
      ring
    rw [hs]
    linear_combination hg

theorem coeff_mk_mul_mk (a b : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) = cauchyConv a b n := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [cauchyConv, PowerSeries.coeff_mk]

theorem mk_cauchyConv (a b : ℕ → ℝ) :
    PowerSeries.mk (cauchyConv a b) = PowerSeries.mk a * PowerSeries.mk b := by
  ext n
  rw [coeff_mk_mul_mk, PowerSeries.coeff_mk]

theorem coeff_mul_nonneg {f g : PowerSeries ℝ} (hf : ∀ n, 0 ≤ PowerSeries.coeff n f)
    (hg : ∀ n, 0 ≤ PowerSeries.coeff n g) (n : ℕ) : 0 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hf _) (hg _)

/-! ### Positivity of the doubly shadowed pair -/

/-- `2(r − c) T_N = r^{N+1} + r q_N − q_{N+1}` for `T = (1 − ru)^{−1} ⋆ q`. -/
theorem two_mul_sub_mul_cauchyConv_pairSeq (w : ℂ) (N : ℕ) :
    2 * (‖w‖ - w.re) * cauchyConv (fun n => ‖w‖ ^ n) (pairSeq w) N =
      ‖w‖ ^ (N + 1) + ‖w‖ * pairSeq w N - pairSeq w (N + 1) := by
  induction N with
  | zero =>
    rw [cauchyConv_geom_zero, pairSeq_zero, pairSeq_one]
    ring
  | succ N ih =>
    rw [cauchyConv_geom_succ, pairSeq_rec]
    linear_combination ‖w‖ * ih

/-- `2(r − c) D_n = (n+2) r^{n+1} − q_{n+1}` for `D = (1 − ru)^{−2} ⋆ q`. -/
theorem two_mul_sub_mul_doubleConv_pairSeq (w : ℂ) (n : ℕ) :
    2 * (‖w‖ - w.re) *
        cauchyConv (fun n => ‖w‖ ^ n) (cauchyConv (fun n => ‖w‖ ^ n) (pairSeq w)) n =
      (n + 2) * ‖w‖ ^ (n + 1) - pairSeq w (n + 1) := by
  induction n with
  | zero =>
    rw [cauchyConv_geom_zero, cauchyConv_geom_zero, pairSeq_zero, pairSeq_one]
    ring
  | succ n ih =>
    rw [cauchyConv_geom_succ]
    have hT := two_mul_sub_mul_cauchyConv_pairSeq w (n + 1)
    push_cast
    linear_combination ‖w‖ * ih + hT

theorem doubleConv_pairSeq_nonneg (w : ℂ) (n : ℕ) :
    0 ≤ cauchyConv (fun n => ‖w‖ ^ n) (cauchyConv (fun n => ‖w‖ ^ n) (pairSeq w)) n := by
  have hcr : w.re ≤ ‖w‖ := (le_abs_self _).trans (Complex.abs_re_le_norm w)
  have hr : 0 ≤ ‖w‖ := norm_nonneg w
  rcases hcr.lt_or_eq with hlt | heq
  · have h := two_mul_sub_mul_doubleConv_pairSeq w n
    have hq := abs_pairSeq_le w (n + 1)
    have hq' : pairSeq w (n + 1) ≤ (n + 2) * ‖w‖ ^ (n + 1) := by
      have := (le_abs_self _).trans hq
      push_cast at this
      linarith
    have hpos : 0 < 2 * (‖w‖ - w.re) := by linarith
    nlinarith
  · -- `w` is real and nonnegative: `q_m = (m+1) r^m ≥ 0`
    have hq : ∀ m, 0 ≤ pairSeq w m := by
      intro m
      rcases m with _ | m
      · rw [pairSeq_zero]
        exact zero_le_one
      · have h := two_mul_sub_mul_doubleConv_pairSeq w m
        rw [heq, sub_self, mul_zero, zero_mul] at h
        have : pairSeq w (m + 1) = (m + 2) * ‖w‖ ^ (m + 1) := by linarith
        rw [this]
        positivity
    exact cauchyConv_nonneg (fun _ => pow_nonneg hr _)
      (cauchyConv_nonneg (fun _ => pow_nonneg hr _) hq) n

/-- **Double shadowing at the level of coefficients.** -/
theorem doubleShadow_coeff_nonneg {x y : ℝ} {w : ℂ} (hx : ‖w‖ ≤ x) (hy : ‖w‖ ≤ y) (n : ℕ) :
    0 ≤ cauchyConv (fun i => x ^ i) (cauchyConv (fun j => y ^ j) (pairSeq w)) n := by
  set r := ‖w‖ with hrdef
  have hr : 0 ≤ r := norm_nonneg w
  have hgx : PowerSeries.mk (fun i => x ^ i) =
      PowerSeries.mk (shadowSeq x r) * PowerSeries.mk (fun i => r ^ i) := by
    rw [← mk_cauchyConv]
    congr 1
    funext i
    exact (cauchyConv_shadowSeq_geom x r i).symm
  have hgy : PowerSeries.mk (fun i => y ^ i) =
      PowerSeries.mk (shadowSeq y r) * PowerSeries.mk (fun i => r ^ i) := by
    rw [← mk_cauchyConv]
    congr 1
    funext i
    exact (cauchyConv_shadowSeq_geom y r i).symm
  have hprod : PowerSeries.mk (cauchyConv (fun i => x ^ i) (cauchyConv (fun j => y ^ j)
      (pairSeq w))) = PowerSeries.mk (shadowSeq x r) * PowerSeries.mk (shadowSeq y r) *
        PowerSeries.mk (cauchyConv (fun n => r ^ n) (cauchyConv (fun n => r ^ n)
          (pairSeq w))) := by
    rw [mk_cauchyConv, mk_cauchyConv, mk_cauchyConv, mk_cauchyConv, hgx, hgy]
    ring
  have h := congrArg (PowerSeries.coeff n) hprod
  rw [PowerSeries.coeff_mk] at h
  rw [h]
  refine coeff_mul_nonneg (coeff_mul_nonneg ?_ ?_) ?_ n
  · intro i
    rw [PowerSeries.coeff_mk]
    exact shadowSeq_nonneg hr hx i
  · intro i
    rw [PowerSeries.coeff_mk]
    exact shadowSeq_nonneg hr hy i
  · intro i
    rw [PowerSeries.coeff_mk]
    exact doubleConv_pairSeq_nonneg w i

/-! ### The analytic factor -/

/-- The geometric power series of `(1 − κz)⁻¹`. -/
theorem hasFPowerSeriesAt_inv_one_sub_mul (κ : ℂ) :
    HasFPowerSeriesAt (fun z : ℂ => (1 - κ * z)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => κ ^ k)) 0 := by
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (‖κ‖₊ : ℝ≥0∞)⁻¹ → ‖κ‖₊ * t < 1 := by
    intro t ht
    rcases eq_or_ne ‖κ‖₊ 0 with h0 | hk
    · simp [h0]
    · rw [← ENNReal.coe_inv hk, ENNReal.coe_lt_coe] at ht
      rw [mul_comm]
      exact (NNReal.lt_inv_iff_mul_lt hk).mp ht
  refine ⟨(‖κ‖₊ : ℝ≥0∞)⁻¹, ?_, ENNReal.inv_pos.mpr ENNReal.coe_ne_top, ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    have hq : ‖κ‖ * (t : ℝ) < 1 := by exact_mod_cast hlt t ht
    refine (summable_geometric_of_lt_one (by positivity) hq).congr fun k => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, norm_pow, mul_pow]
  · intro y hy
    have hy' : (‖y‖₊ : ℝ≥0∞) < (‖κ‖₊ : ℝ≥0∞)⁻¹ := by
      rwa [Metric.mem_eball, edist_zero_right] at hy
    have hq : ‖κ * y‖ < 1 := by
      rw [norm_mul]
      exact_mod_cast hlt _ hy'
    have h := hasSum_geometric_of_norm_lt_one hq
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
    refine h.congr_fun fun k => ?_
    rw [mul_pow]

/-- The normalized even coefficients at `0`. -/
def evenCoeffC (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  (((2 * k).factorial : ℂ))⁻¹ * iteratedDeriv (2 * k) f 0

/-- The reciprocal factor `(1 − κσ²)⁻¹`. -/
def recipQuad (κ : ℂ) : ℂ → ℂ := fun σ => (1 - κ * σ ^ 2)⁻¹

theorem analyticAt_recipQuad (κ : ℂ) : AnalyticAt ℂ (recipQuad κ) 0 := by
  have h : AnalyticAt ℂ (fun σ : ℂ => 1 - κ * σ ^ 2) 0 := by fun_prop
  exact h.inv (by simp)

theorem evenCoeffC_recipQuad (κ : ℂ) (k : ℕ) : evenCoeffC (recipQuad κ) k = κ ^ k := by
  have hg := (hasFPowerSeriesAt_inv_one_sub_mul κ).analyticAt
  have h := iteratedDeriv_comp_sq hg k
  unfold evenCoeffC recipQuad
  rw [show ((2 * k).factorial : ℂ) = (((2 * k) ! : ℕ) : ℂ) from rfl, h,
    iteratedDeriv_eq_of_hasFPowerSeriesAt (hasFPowerSeriesAt_inv_one_sub_mul κ)]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  field_simp

theorem iteratedDeriv_recipQuad_odd (κ : ℂ) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (recipQuad κ) 0 = 0 :=
  iteratedDeriv_comp_sq_odd (hasFPowerSeriesAt_inv_one_sub_mul κ).analyticAt k

theorem evenCoeffC_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) f 0 = 0) (k : ℕ) :
    evenCoeffC (f * g) k = ∑ j ∈ Finset.range (k + 1), evenCoeffC f j * evenCoeffC g (k - j) :=
  factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt hf hg hfo k

/-- Reciprocal positivity of an even function: `1/u` has vanishing odd and nonnegative even
derivatives at `0`. -/
structure EvenRecipNonneg (u : ℂ → ℂ) : Prop where
  analyticAt : AnalyticAt ℂ u 0
  ne_zero : u 0 ≠ 0
  odd : ∀ m, iteratedDeriv (2 * m + 1) (fun σ => (u σ)⁻¹) 0 = 0
  nonneg : ∀ m, 0 ≤ iteratedDeriv (2 * m) (fun σ => (u σ)⁻¹) 0

theorem EvenRecipNonneg.analyticAt_inv {u : ℂ → ℂ} (hu : EvenRecipNonneg u) :
    AnalyticAt ℂ (fun σ => (u σ)⁻¹) 0 := hu.analyticAt.inv hu.ne_zero

theorem EvenRecipNonneg.coeff_real {u : ℂ → ℂ} (hu : EvenRecipNonneg u) (m : ℕ) :
    ((((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) (fun σ => (u σ)⁻¹) 0) =
      ((evenRecipCoeff u m : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [evenRecipCoeff]
  · simp only [Complex.ofReal_im]
    rw [Complex.mul_im, (Complex.nonneg_iff.mp (hu.nonneg m)).2.symm, mul_zero, zero_add]
    rw [show (((2 * m).factorial : ℂ))⁻¹ = ((((2 * m).factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl,
      Complex.ofReal_im, zero_mul]

theorem EvenRecipNonneg.evenRecipCoeff_nonneg {u : ℂ → ℂ} (hu : EvenRecipNonneg u) (m : ℕ) :
    0 ≤ evenRecipCoeff u m := by
  have h := hu.coeff_real m
  have hfac : (0 : ℂ) ≤ (((2 * m).factorial : ℂ))⁻¹ := by
    rw [show (((2 * m).factorial : ℂ))⁻¹ = ((((2 * m).factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (by positivity)
  have := mul_nonneg hfac (hu.nonneg m)
  rw [h] at this
  exact Complex.zero_le_real.mp this

/-- **Products.** -/
theorem EvenRecipNonneg.mul {u v : ℂ → ℂ} (hu : EvenRecipNonneg u) (hv : EvenRecipNonneg v) :
    EvenRecipNonneg (u * v) := by
  have hinv : (fun σ => ((u * v) σ)⁻¹) = (fun σ => (u σ)⁻¹) * fun σ => (v σ)⁻¹ := by
    funext σ
    simp only [Pi.mul_apply, mul_inv]
  refine ⟨hu.analyticAt.mul hv.analyticAt, mul_ne_zero hu.ne_zero hv.ne_zero, fun m => ?_,
    fun m => ?_⟩
  · rw [hinv]
    exact iteratedDeriv_mul_odd_eq_zero_of_analyticAt hu.analyticAt_inv hv.analyticAt_inv
      hu.odd hv.odd m
  · have h := factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt hu.analyticAt_inv
      hv.analyticAt_inv hu.odd m
    rw [← hinv] at h
    have hsum : 0 ≤ ∑ j ∈ Finset.range (m + 1),
        ((((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) (fun σ => (u σ)⁻¹) 0) *
          ((((2 * (m - j)).factorial : ℂ))⁻¹ *
            iteratedDeriv (2 * (m - j)) (fun σ => (v σ)⁻¹) 0) := by
      refine Finset.sum_nonneg fun j _ => ?_
      rw [hu.coeff_real, hv.coeff_real]
      exact mul_nonneg (Complex.zero_le_real.mpr (hu.evenRecipCoeff_nonneg j))
        (Complex.zero_le_real.mpr (hv.evenRecipCoeff_nonneg _))
    rw [← h] at hsum
    have hf0 : (0 : ℂ) ≤ (((2 * m).factorial : ℂ)) := Nat.cast_nonneg _
    have hne : (((2 * m).factorial : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have := mul_nonneg hf0 hsum
    rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this

/-- Positive constants. -/
theorem EvenRecipNonneg.const {c : ℝ} (hc : 0 < c) : EvenRecipNonneg (fun _ => (c : ℂ)) := by
  have hinv : (fun σ : ℂ => ((fun _ : ℂ => (c : ℂ)) σ)⁻¹) = fun _ => ((c⁻¹ : ℝ) : ℂ) := by
    funext σ
    push_cast
    rfl
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨analyticAt_const, hc', fun m => ?_, fun m => ?_⟩
  · rw [hinv, iteratedDeriv_const]
    simp
  · rw [hinv, iteratedDeriv_const]
    split_ifs
    · exact Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le)
    · exact le_rfl

/-- The doubly shadowed group `(1 − xσ²)(1 − yσ²)(1 − wσ²)(1 − w̄σ²)`. -/
def doubleShadowGroup (x y : ℝ) (w : ℂ) : ℂ → ℂ := fun σ =>
  (1 - (x : ℂ) * σ ^ 2) * (1 - (y : ℂ) * σ ^ 2) * ((1 - w * σ ^ 2) * (1 - starRingEnd ℂ w * σ ^ 2))

theorem inv_doubleShadowGroup (x y : ℝ) (w : ℂ) :
    (fun σ => (doubleShadowGroup x y w σ)⁻¹) =
      recipQuad x * (recipQuad y * (recipQuad w * recipQuad (starRingEnd ℂ w))) := by
  funext σ
  simp only [doubleShadowGroup, recipQuad, Pi.mul_apply, mul_inv]
  ring

/-- **Double shadowing.**  If `‖w‖ ≤ x` and `‖w‖ ≤ y`, the reciprocal of
`(1 − xσ²)(1 − yσ²)(1 − wσ²)(1 − w̄σ²)` has nonnegative coefficients. -/
theorem evenRecipNonneg_doubleShadow {x y : ℝ} {w : ℂ} (hx : ‖w‖ ≤ x) (hy : ‖w‖ ≤ y) :
    EvenRecipNonneg (doubleShadowGroup x y w) := by
  set w' := starRingEnd ℂ w
  have hA : ∀ κ, AnalyticAt ℂ (recipQuad κ) 0 := analyticAt_recipQuad
  have hO : ∀ κ k, iteratedDeriv (2 * k + 1) (recipQuad κ) 0 = 0 := iteratedDeriv_recipQuad_odd
  have hwA := (hA w).mul (hA w')
  have hwO := iteratedDeriv_mul_odd_eq_zero_of_analyticAt (hA w) (hA w') (hO w) (hO w')
  have hyA := (hA y).mul hwA
  have hyO := iteratedDeriv_mul_odd_eq_zero_of_analyticAt (hA y) hwA (hO y) hwO
  have hpair : ∀ m, evenCoeffC (recipQuad w * recipQuad w') m = ((pairSeq w m : ℝ) : ℂ) := by
    intro m
    rw [evenCoeffC_mul (hA w) (hA w') (hO w), ← hTwo_conj_eq_pairSeq]
    unfold hTwo
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evenCoeffC_recipQuad, evenCoeffC_recipQuad]
  have hy' : ∀ n, evenCoeffC (recipQuad y * (recipQuad w * recipQuad w')) n =
      ((cauchyConv (fun j => y ^ j) (pairSeq w) n : ℝ) : ℂ) := by
    intro n
    rw [evenCoeffC_mul (hA y) hwA (hO y)]
    unfold cauchyConv
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evenCoeffC_recipQuad, hpair]
  have hx' : ∀ n, evenCoeffC (recipQuad x * (recipQuad y * (recipQuad w * recipQuad w'))) n =
      ((cauchyConv (fun i => x ^ i) (cauchyConv (fun j => y ^ j) (pairSeq w)) n : ℝ) : ℂ) := by
    intro n
    rw [evenCoeffC_mul (hA x) hyA (hO x)]
    unfold cauchyConv
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evenCoeffC_recipQuad, hy']
    unfold cauchyConv
    push_cast
    rfl
  refine ⟨by unfold doubleShadowGroup; fun_prop, by simp [doubleShadowGroup], fun m => ?_,
    fun m => ?_⟩
  · rw [inv_doubleShadowGroup]
    exact iteratedDeriv_mul_odd_eq_zero_of_analyticAt (hA x) hyA (hO x) hyO m
  · rw [inv_doubleShadowGroup]
    have h := hx' m
    unfold evenCoeffC at h
    have hne : (((2 * m).factorial : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hD : iteratedDeriv (2 * m)
        (recipQuad x * (recipQuad y * (recipQuad w * recipQuad w'))) 0 =
        (((2 * m).factorial : ℂ)) *
          ((cauchyConv (fun i => x ^ i) (cauchyConv (fun j => y ^ j) (pairSeq w)) m : ℝ) : ℂ) := by
      rw [← h]
      field_simp
    rw [hD]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.mpr (doubleShadow_coeff_nonneg hx hy m))

end

end GaloisForLFunctions.HTGeometry
