import Mathlib

/-!
# Cell terms of a jittered discrete measure against the critical-line wave

For `N ≥ 1` the half-line `[1, ∞)` is cut into cells `[m/N, (m+1)/N)`, `m = N + k`, of length
`1/N`.  A discrete measure with one atom of mass `1/N` at a point `m/N + v/N` of each cell differs
from Lebesgue measure on the cell by a signed measure of total mass zero.  Tested against the real
part `wave t x = x^{-1/2} cos(t log x)` of `x^{-(1/2+it)}`, the difference is `cellTerm N k v t`.

* `abs_cellTerm_le_osc`: `|cellTerm| ≤ 2/(N √(m/N))` (each piece has size at most the mass times
  the amplitude).
* `abs_cellTerm_le_smooth`: `|cellTerm| ≤ (|t| + 1/2)/(√N · m √m)` (mean value theorem on a cell of
  length `1/N`, with `|∂ₓ wave| ≤ (|t| + 1/2) x^{-3/2}`).
* `abs_cellTerm_sub_param_le`: `t ↦ cellTerm` is `2 log((m+1)/N)/N`-Lipschitz.
* `integral_cellTerm_eq_zero`: `∫₀¹ cellTerm N k v t dv = 0`: an atom placed uniformly in the cell
  has the cell's Lebesgue measure as its mean.
* `sum_Ico_inv_mul_sqrt_le`: `Σ_{K ≤ k < L} 1/(m √m) ≤ 2/√(N + K − 1)` by telescoping, which gives
  summability of `cellSum` and the tail bound `abs_cellSum_sub_sum_range_le`.
-/

open Real MeasureTheory Set

noncomputable section

namespace RHTower
namespace RandomCellWeil

/-- The real part `x^{-1/2} cos(t log x)` of `x^{-(1/2+it)}`. -/
def wave (t x : ℝ) : ℝ := Real.cos (t * Real.log x) / Real.sqrt x

/-- Left end `(N + k)/N` of the `k`-th cell of length `1/N` in `[1, ∞)`. -/
def cellLeft (N k : ℕ) : ℝ := ((N + k : ℕ) : ℝ) / N

/-- An atom of mass `1/N` at `cellLeft N k + v/N`, minus Lebesgue measure on the cell, tested
against `wave t`. -/
def cellTerm (N k : ℕ) (v t : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * wave t (cellLeft N k + v / N) - ∫ x in cellLeft N k..cellLeft N k + (N : ℝ)⁻¹, wave t x

/-- The sum of all cell terms of the configuration `u`. -/
def cellSum (N : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℝ := ∑' k, cellTerm N k (u k) t

theorem wave_neg (t x : ℝ) : wave (-t) x = wave t x := by
  simp [wave, neg_mul, Real.cos_neg]

theorem abs_wave_le (t : ℝ) {x : ℝ} (hx : 0 < x) : |wave t x| ≤ 1 / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [wave, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hs.le

theorem continuousOn_wave (t : ℝ) : ContinuousOn (wave t) (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  apply ContinuousAt.continuousWithinAt
  unfold wave
  exact ((continuous_cos.continuousAt).comp
    (continuousAt_const.mul (Real.continuousAt_log hx0))).div
    Real.continuous_sqrt.continuousAt hs

theorem measurable_wave (t : ℝ) : Measurable (wave t) := by
  unfold wave
  fun_prop

theorem hasDerivAt_wave (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (wave t)
      ((-Real.sin (t * Real.log x) * (t * x⁻¹) * Real.sqrt x
        - Real.cos (t * Real.log x) * (1 / (2 * Real.sqrt x))) / Real.sqrt x ^ 2) x := by
  have h1 : HasDerivAt (fun y => Real.cos (t * Real.log y))
      (-Real.sin (t * Real.log x) * (t * x⁻¹)) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul t).cos
  have h2 := Real.hasDerivAt_sqrt hx.ne'
  have h3 := h1.div h2 (Real.sqrt_pos.mpr hx).ne'
  exact h3

/-- `|∂ₓ wave t x| ≤ (|t| + 1/2)/(x √x)`. -/
theorem abs_deriv_wave_le (t : ℝ) {x : ℝ} (hx : 0 < x) :
    |(-Real.sin (t * Real.log x) * (t * x⁻¹) * Real.sqrt x
        - Real.cos (t * Real.log x) * (1 / (2 * Real.sqrt x))) / Real.sqrt x ^ 2|
      ≤ (|t| + 1 / 2) / (x * Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have heq : (-Real.sin (t * Real.log x) * (t * x⁻¹) * Real.sqrt x
        - Real.cos (t * Real.log x) * (1 / (2 * Real.sqrt x))) / Real.sqrt x ^ 2
      = (-(t * Real.sin (t * Real.log x)) - Real.cos (t * Real.log x) / 2) / (x * Real.sqrt x) := by
    set L := t * Real.log x
    set y := Real.sqrt x
    rw [hsq, div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    rw [← hsq]
    ring
  rw [heq, abs_div, abs_of_pos (mul_pos hx hs)]
  apply div_le_div_of_nonneg_right _ (mul_pos hx hs).le
  have hsin := Real.abs_sin_le_one (t * Real.log x)
  have hcos := Real.abs_cos_le_one (t * Real.log x)
  calc |-(t * Real.sin (t * Real.log x)) - Real.cos (t * Real.log x) / 2|
      ≤ |t * Real.sin (t * Real.log x)| + |Real.cos (t * Real.log x) / 2| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_neg]
    _ ≤ |t| + 1 / 2 := by
        rw [abs_mul, abs_div, abs_two]
        have := mul_le_mul_of_nonneg_left hsin (abs_nonneg t)
        linarith

/-- Mean value bound: on `[a, ∞)`, `wave t` is `(|t| + 1/2)/(a √a)`-Lipschitz. -/
theorem abs_wave_sub_le (t : ℝ) {a x y : ℝ} (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    |wave t x - wave t y| ≤ (|t| + 1 / 2) / (a * Real.sqrt a) * |x - y| := by
  have hderiv : ∀ z ∈ Ici a, HasDerivWithinAt (wave t)
      ((-Real.sin (t * Real.log z) * (t * z⁻¹) * Real.sqrt z
        - Real.cos (t * Real.log z) * (1 / (2 * Real.sqrt z))) / Real.sqrt z ^ 2) (Ici a) z :=
    fun z hz => (hasDerivAt_wave t (lt_of_lt_of_le ha hz)).hasDerivWithinAt
  have hbound : ∀ z ∈ Ici a,
      ‖(-Real.sin (t * Real.log z) * (t * z⁻¹) * Real.sqrt z
        - Real.cos (t * Real.log z) * (1 / (2 * Real.sqrt z))) / Real.sqrt z ^ 2‖
        ≤ (|t| + 1 / 2) / (a * Real.sqrt a) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha hz
    rw [Real.norm_eq_abs]
    refine (abs_deriv_wave_le t hz0).trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos ha (Real.sqrt_pos.mpr ha))
    exact mul_le_mul hz (Real.sqrt_le_sqrt hz) (Real.sqrt_nonneg _) hz0.le
  have h := (convex_Ici a).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hy hx
  simpa [Real.norm_eq_abs] using h

/-- `t ↦ wave t x` is `log x`-Lipschitz for `x ≥ 1`. -/
theorem abs_wave_sub_param_le (t t' : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |wave t x - wave t' x| ≤ Real.log x * |t - t'| := by
  have hx0 : 0 < x := by linarith
  have hs1 : 1 ≤ Real.sqrt x := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx
  have hs : 0 < Real.sqrt x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [wave, wave, ← sub_div, abs_div, abs_of_pos hs]
  have hc := Real.abs_cos_sub_cos_le (t * Real.log x) (t' * Real.log x)
  rw [← sub_mul, abs_mul, abs_of_nonneg hlog] at hc
  calc |Real.cos (t * Real.log x) - Real.cos (t' * Real.log x)| / Real.sqrt x
      ≤ |Real.cos (t * Real.log x) - Real.cos (t' * Real.log x)| := div_le_self (abs_nonneg _) hs1
    _ ≤ Real.log x * |t - t'| := hc.trans (le_of_eq (mul_comm _ _))

section cell

variable {N : ℕ}

theorem cellLeft_pos (hN : 1 ≤ N) (k : ℕ) : 0 < cellLeft N k := by
  unfold cellLeft
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

theorem one_le_cellLeft (hN : 1 ≤ N) (k : ℕ) : 1 ≤ cellLeft N k := by
  unfold cellLeft
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hN0, one_mul]
  exact_mod_cast Nat.le_add_right N k

theorem cellLeft_add_inv (hN : 1 ≤ N) (k : ℕ) :
    cellLeft N k + (N : ℝ)⁻¹ = ((N + k + 1 : ℕ) : ℝ) / N := by
  unfold cellLeft
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  push_cast
  field_simp

theorem inv_N_pos (hN : 1 ≤ N) : (0 : ℝ) < (N : ℝ)⁻¹ := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

theorem inv_N_le_one (hN : 1 ≤ N) : (N : ℝ)⁻¹ ≤ 1 := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact inv_le_one_of_one_le₀ this

theorem cellPoint_mem (hN : 1 ≤ N) (k : ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    cellLeft N k ≤ cellLeft N k + v / N ∧ cellLeft N k + v / N ≤ cellLeft N k + (N : ℝ)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · have : 0 ≤ v / N := div_nonneg hv.1 hN0.le
    linarith
  · have : v / N ≤ (N : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_N_pos hN).le hv.2
    linarith

theorem intervalIntegrable_wave (hN : 1 ≤ N) (t : ℝ) (k : ℕ) :
    IntervalIntegrable (wave t) volume (cellLeft N k) (cellLeft N k + (N : ℝ)⁻¹) := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_wave t).mono
  intro x hx
  rw [uIcc_of_le (by linarith [inv_N_pos hN])] at hx
  exact lt_of_lt_of_le (cellLeft_pos hN k) hx.1

/-- The cell term as an integral over the cell of the difference with the value at the atom. -/
theorem cellTerm_eq_integral (hN : 1 ≤ N) (k : ℕ) (v t : ℝ) :
    cellTerm N k v t = ∫ x in cellLeft N k..cellLeft N k + (N : ℝ)⁻¹,
      (wave t (cellLeft N k + v / N) - wave t x) := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegrable_wave hN t k),
    intervalIntegral.integral_const, smul_eq_mul, cellTerm]
  ring_nf

/-- `|cellTerm| ≤ 2/(N √a)` with `a = cellLeft N k`. -/
theorem abs_cellTerm_le_osc (hN : 1 ≤ N) (k : ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    |cellTerm N k v t| ≤ 2 * (N : ℝ)⁻¹ / Real.sqrt (cellLeft N k) := by
  obtain ⟨hp1, hp2⟩ := cellPoint_mem hN k hv
  set a := cellLeft N k with ha
  have ha0 : 0 < a := cellLeft_pos hN k
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hh := inv_N_pos hN
  have hpt : |(N : ℝ)⁻¹ * wave t (a + v / N)| ≤ (N : ℝ)⁻¹ / Real.sqrt a := by
    have hw : |wave t (a + v / N)| ≤ 1 / Real.sqrt a :=
      (abs_wave_le t (by linarith)).trans (one_div_le_one_div_of_le hsa (Real.sqrt_le_sqrt hp1))
    rw [abs_mul, abs_of_pos hh]
    calc (N : ℝ)⁻¹ * |wave t (a + v / N)| ≤ (N : ℝ)⁻¹ * (1 / Real.sqrt a) :=
          mul_le_mul_of_nonneg_left hw hh.le
      _ = (N : ℝ)⁻¹ / Real.sqrt a := by ring
  have hint : |∫ x in a..a + (N : ℝ)⁻¹, wave t x| ≤ (N : ℝ)⁻¹ / Real.sqrt a := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + (N : ℝ)⁻¹)
      (C := 1 / Real.sqrt a) (f := wave t) (by
        intro x hx
        rw [uIoc_of_le (by linarith)] at hx
        rw [Real.norm_eq_abs]
        refine (abs_wave_le t (by linarith [hx.1])).trans ?_
        exact one_div_le_one_div_of_le hsa (Real.sqrt_le_sqrt hx.1.le))
    rw [Real.norm_eq_abs] at h
    rw [show a + (N : ℝ)⁻¹ - a = (N : ℝ)⁻¹ by ring, abs_of_pos hh] at h
    calc _ ≤ 1 / Real.sqrt a * (N : ℝ)⁻¹ := h
      _ = (N : ℝ)⁻¹ / Real.sqrt a := by ring
  unfold cellTerm
  rw [← ha]
  calc _ ≤ |(N : ℝ)⁻¹ * wave t (a + v / N)| + |∫ x in a..a + (N : ℝ)⁻¹, wave t x| := abs_sub _ _
    _ ≤ _ := by
      have : 2 * (N : ℝ)⁻¹ / Real.sqrt a = (N : ℝ)⁻¹ / Real.sqrt a + (N : ℝ)⁻¹ / Real.sqrt a := by
        ring
      rw [this]
      exact add_le_add hpt hint

/-- `|cellTerm| ≤ (|t| + 1/2)/(a √a) · (1/N)²` with `a = cellLeft N k`. -/
theorem abs_cellTerm_le_smooth (hN : 1 ≤ N) (k : ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    |cellTerm N k v t|
      ≤ (|t| + 1 / 2) / (cellLeft N k * Real.sqrt (cellLeft N k)) * ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) := by
  obtain ⟨hp1, hp2⟩ := cellPoint_mem hN k hv
  set a := cellLeft N k with ha
  have ha0 : 0 < a := cellLeft_pos hN k
  have hh := inv_N_pos hN
  rw [cellTerm_eq_integral hN k v t, ← ha]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + (N : ℝ)⁻¹)
    (C := (|t| + 1 / 2) / (a * Real.sqrt a) * (N : ℝ)⁻¹)
    (f := fun x => wave t (a + v / N) - wave t x) (by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      rw [Real.norm_eq_abs]
      refine (abs_wave_sub_le t ha0 hp1 hx.1.le).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2])
  rw [Real.norm_eq_abs, show a + (N : ℝ)⁻¹ - a = (N : ℝ)⁻¹ by ring, abs_of_pos hh] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- `t ↦ cellTerm N k v t` is Lipschitz with constant `2 log(a + 1/N)/N`. -/
theorem abs_cellTerm_sub_param_le (hN : 1 ≤ N) (k : ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (t t' : ℝ) :
    |cellTerm N k v t - cellTerm N k v t'|
      ≤ 2 * (N : ℝ)⁻¹ * Real.log (cellLeft N k + (N : ℝ)⁻¹) * |t - t'| := by
  obtain ⟨hp1, hp2⟩ := cellPoint_mem hN k hv
  set a := cellLeft N k with ha
  have ha1 : 1 ≤ a := one_le_cellLeft hN k
  have hh := inv_N_pos hN
  have hlogmono : ∀ x, 1 ≤ x → x ≤ a + (N : ℝ)⁻¹ → Real.log x ≤ Real.log (a + (N : ℝ)⁻¹) :=
    fun x hx hxb => Real.log_le_log (by linarith) hxb
  have hpt : |(N : ℝ)⁻¹ * wave t (a + v / N) - (N : ℝ)⁻¹ * wave t' (a + v / N)|
      ≤ (N : ℝ)⁻¹ * Real.log (a + (N : ℝ)⁻¹) * |t - t'| := by
    rw [← mul_sub, abs_mul, abs_of_pos hh, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hh.le
    refine (abs_wave_sub_param_le t t' (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (hlogmono _ (by linarith) hp2) (abs_nonneg _)
  have hint : |(∫ x in a..a + (N : ℝ)⁻¹, wave t x) - ∫ x in a..a + (N : ℝ)⁻¹, wave t' x|
      ≤ (N : ℝ)⁻¹ * Real.log (a + (N : ℝ)⁻¹) * |t - t'| := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_wave hN t k)
      (intervalIntegrable_wave hN t' k)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + (N : ℝ)⁻¹)
      (C := Real.log (a + (N : ℝ)⁻¹) * |t - t'|) (f := fun x => wave t x - wave t' x) (by
        intro x hx
        rw [uIoc_of_le (by linarith)] at hx
        rw [Real.norm_eq_abs]
        refine (abs_wave_sub_param_le t t' (by linarith [hx.1])).trans ?_
        exact mul_le_mul_of_nonneg_right (hlogmono _ (by linarith [hx.1]) hx.2) (abs_nonneg _))
    rw [Real.norm_eq_abs, show a + (N : ℝ)⁻¹ - a = (N : ℝ)⁻¹ by ring, abs_of_pos hh] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  unfold cellTerm
  rw [← ha]
  have hsplit : (N : ℝ)⁻¹ * wave t (a + v / N) - (∫ x in a..a + (N : ℝ)⁻¹, wave t x)
      - ((N : ℝ)⁻¹ * wave t' (a + v / N) - ∫ x in a..a + (N : ℝ)⁻¹, wave t' x)
      = ((N : ℝ)⁻¹ * wave t (a + v / N) - (N : ℝ)⁻¹ * wave t' (a + v / N))
        - ((∫ x in a..a + (N : ℝ)⁻¹, wave t x) - ∫ x in a..a + (N : ℝ)⁻¹, wave t' x) := by ring
  rw [hsplit]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add hpt hint
    _ = _ := by ring

/-- A uniformly placed atom has the cell's Lebesgue measure as mean: `∫₀¹ cellTerm dv = 0`. -/
theorem integral_cellTerm_eq_zero (hN : 1 ≤ N) (k : ℕ) (t : ℝ) :
    ∫ v in (0 : ℝ)..1, cellTerm N k v t = 0 := by
  set a := cellLeft N k with ha
  have hN0 : (N : ℝ)⁻¹ ≠ 0 := (inv_N_pos hN).ne'
  have hcomp : ∫ v in (0 : ℝ)..1, wave t ((N : ℝ)⁻¹ * v + a)
      = ((N : ℝ)⁻¹)⁻¹ • ∫ x in (N : ℝ)⁻¹ * 0 + a..(N : ℝ)⁻¹ * 1 + a, wave t x :=
    intervalIntegral.integral_comp_mul_add (wave t) hN0 a
  have hfun : (fun v => cellTerm N k v t)
      = fun v => (N : ℝ)⁻¹ * wave t ((N : ℝ)⁻¹ * v + a)
          - ∫ x in a..a + (N : ℝ)⁻¹, wave t x := by
    funext v
    unfold cellTerm
    rw [← ha]
    congr 2
    rw [div_eq_inv_mul, add_comm]
  have hint1 : IntervalIntegrable (fun v => (N : ℝ)⁻¹ * wave t ((N : ℝ)⁻¹ * v + a)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply (continuousOn_wave t).comp (by fun_prop)
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    have : 0 ≤ (N : ℝ)⁻¹ * v := mul_nonneg (inv_N_pos hN).le hv.1
    simp only [mem_Ioi]
    linarith [cellLeft_pos hN k]
  rw [hfun, intervalIntegral.integral_sub hint1 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hcomp, intervalIntegral.integral_const, smul_eq_mul,
    smul_eq_mul]
  simp only [mul_zero, zero_add, mul_one, sub_zero, one_mul]
  rw [add_comm (N : ℝ)⁻¹ a]
  field_simp
  ring

theorem cellTerm_neg_param (k : ℕ) (v t : ℝ) : cellTerm N k v (-t) = cellTerm N k v t := by
  simp [cellTerm, wave_neg]

theorem measurable_cellTerm (k : ℕ) (t : ℝ) : Measurable (fun v => cellTerm N k v t) := by
  unfold cellTerm
  exact (measurable_const.mul ((measurable_wave t).comp (by fun_prop))).sub measurable_const

end cell


section sums

/-- Telescoping bound `1/((m+1)√(m+1)) ≤ 2/√m − 2/√(m+1)` for `m ≥ 1`. -/
theorem inv_mul_sqrt_succ_le {m : ℝ} (hm : 1 ≤ m) :
    1 / ((m + 1) * Real.sqrt (m + 1)) ≤ 2 / Real.sqrt m - 2 / Real.sqrt (m + 1) := by
  have hm0 : 0 < m := by linarith
  set p := Real.sqrt m with hp
  set q := Real.sqrt (m + 1) with hq
  have hp0 : 0 < p := Real.sqrt_pos.mpr hm0
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hpq : p ≤ q := Real.sqrt_le_sqrt (by linarith)
  have hp2 : p ^ 2 = m := Real.sq_sqrt hm0.le
  have hq2 : q ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
  rw [← hq2]
  rw [div_sub_div _ _ hp0.ne' hq0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hdiff : (q - p) * (q + p) = 1 := by nlinarith
  have hkey : p * q * (p + q) ≤ 2 * q ^ 3 := by nlinarith [mul_pos hp0 hq0]
  nlinarith [mul_pos hp0 hq0, mul_pos (mul_pos hp0 hq0) hq0]

/-- `f m = 1/(m √m)`. -/
def invPow (m : ℝ) : ℝ := 1 / (m * Real.sqrt m)

theorem invPow_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ invPow m := by
  unfold invPow; positivity

/-- `Σ_{k<L} 1/(m_k √m_k) ≤ 2/√(N+K−1)` for `m_k = N + K + k`, `N + K ≥ 2`. -/
theorem sum_range_invPow_le (M : ℕ) (hM : 2 ≤ M) (L : ℕ) :
    ∑ k ∈ Finset.range L, invPow ((M + k : ℕ) : ℝ)
      ≤ 2 / Real.sqrt ((M : ℝ) - 1) - 2 / Real.sqrt ((M + L : ℕ) - 1 : ℝ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hstep := inv_mul_sqrt_succ_le (m := ((M + L : ℕ) : ℝ) - 1) (by
      have : (2 : ℝ) ≤ ((M + L : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ M + L by omega)
      linarith)
    have e1 : ((M + L : ℕ) : ℝ) - 1 + 1 = ((M + L : ℕ) : ℝ) := by ring
    rw [e1] at hstep
    have e2 : ((M + (L + 1) : ℕ) : ℝ) - 1 = ((M + L : ℕ) : ℝ) := by push_cast; ring
    rw [e2]
    simp only [invPow] at ih ⊢
    linarith

theorem summable_invPow (M : ℕ) (hM : 2 ≤ M) :
    Summable (fun k : ℕ => invPow ((M + k : ℕ) : ℝ)) := by
  apply summable_of_sum_range_le (c := 2 / Real.sqrt ((M : ℝ) - 1))
  · intro k; exact invPow_nonneg (by positivity)
  · intro L
    refine (sum_range_invPow_le M hM L).trans ?_
    have : 0 ≤ 2 / Real.sqrt (((M + L : ℕ) : ℝ) - 1) := by positivity
    linarith

theorem tsum_invPow_le (M : ℕ) (hM : 2 ≤ M) :
    ∑' k : ℕ, invPow ((M + k : ℕ) : ℝ) ≤ 2 / Real.sqrt ((M : ℝ) - 1) := by
  apply Real.tsum_le_of_sum_range_le
  · intro k; exact invPow_nonneg (by positivity)
  · intro L
    refine (sum_range_invPow_le M hM L).trans ?_
    have : 0 ≤ 2 / Real.sqrt (((M + L : ℕ) : ℝ) - 1) := by positivity
    linarith

variable {N : ℕ}

/-- The smooth bound in terms of `m = N + k`: `(|t|+1/2)/(a√a)·N⁻² = (|t|+1/2)/√N · 1/(m√m)`. -/
theorem smoothBound_eq (hN : 1 ≤ N) (k : ℕ) (t : ℝ) :
    (|t| + 1 / 2) / (cellLeft N k * Real.sqrt (cellLeft N k)) * ((N : ℝ)⁻¹ * (N : ℝ)⁻¹)
      = (|t| + 1 / 2) / Real.sqrt N * invPow ((N + k : ℕ) : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < ((N + k : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((N + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N + k by omega)
    linarith
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsm : 0 < Real.sqrt ((N + k : ℕ) : ℝ) := Real.sqrt_pos.mpr hm0
  have hNN : (N : ℝ) = Real.sqrt N ^ 2 := (Real.sq_sqrt hN0.le).symm
  unfold cellLeft invPow
  rw [Real.sqrt_div hm0.le]
  set s := Real.sqrt (N : ℝ)
  set m := ((N + k : ℕ) : ℝ)
  set r := Real.sqrt m
  rw [hNN]
  field_simp

theorem abs_cellTerm_le_invPow (hN : 1 ≤ N) (k : ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    |cellTerm N k v t| ≤ (|t| + 1 / 2) / Real.sqrt N * invPow ((N + k : ℕ) : ℝ) :=
  (abs_cellTerm_le_smooth hN k hv t).trans (le_of_eq (smoothBound_eq hN k t))

theorem summable_cellTerm (hN : 2 ≤ N) {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    Summable (fun k => cellTerm N k (u k) t) := by
  apply Summable.of_norm_bounded ((summable_invPow N hN).mul_left ((|t| + 1 / 2) / Real.sqrt N))
  intro k
  rw [Real.norm_eq_abs]
  exact abs_cellTerm_le_invPow (by omega) k (hu k) t

/-- Tail bound: `|cellSum − Σ_{k<K} cellTerm| ≤ (|t|+1/2)/√N · 2/√(N+K−1)`. -/
theorem abs_cellSum_sub_sum_range_le (hN : 2 ≤ N) {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1)
    (t : ℝ) (K : ℕ) :
    |cellSum N u t - ∑ k ∈ Finset.range K, cellTerm N k (u k) t|
      ≤ (|t| + 1 / 2) / Real.sqrt N * (2 / Real.sqrt (((N + K : ℕ) : ℝ) - 1)) := by
  have hs := summable_cellTerm hN hu t
  have hsplit := hs.sum_add_tsum_nat_add K
  have hdiff : cellSum N u t - ∑ k ∈ Finset.range K, cellTerm N k (u k) t
      = ∑' i : ℕ, cellTerm N (i + K) (u (i + K)) t := by
    unfold cellSum
    rw [← hsplit]
    ring
  rw [hdiff]
  have hc : 0 ≤ (|t| + 1 / 2) / Real.sqrt N := by positivity
  have hbd : ∀ i : ℕ, ‖cellTerm N (i + K) (u (i + K)) t‖
      ≤ (|t| + 1 / 2) / Real.sqrt N * invPow (((N + K) + i : ℕ) : ℝ) := by
    intro i
    rw [Real.norm_eq_abs]
    have h := abs_cellTerm_le_invPow (N := N) (by omega) (i + K) (hu (i + K)) t
    rwa [show N + (i + K) = (N + K) + i by omega] at h
  have hsum2 : Summable (fun i : ℕ => (|t| + 1 / 2) / Real.sqrt N * invPow (((N + K) + i : ℕ) : ℝ)) :=
    (summable_invPow (N + K) (by omega)).mul_left _
  have hnorm : Summable (fun i : ℕ => ‖cellTerm N (i + K) (u (i + K)) t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hsum2
  calc |∑' i : ℕ, cellTerm N (i + K) (u (i + K)) t|
      ≤ ∑' i : ℕ, ‖cellTerm N (i + K) (u (i + K)) t‖ := by
        rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i : ℕ, (|t| + 1 / 2) / Real.sqrt N * invPow (((N + K) + i : ℕ) : ℝ) :=
        hnorm.tsum_le_tsum hbd hsum2
    _ = (|t| + 1 / 2) / Real.sqrt N * ∑' i : ℕ, invPow (((N + K) + i : ℕ) : ℝ) := tsum_mul_left
    _ ≤ (|t| + 1 / 2) / Real.sqrt N * (2 / Real.sqrt (((N + K : ℕ) : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (tsum_invPow_le (N + K) (by omega)) hc

theorem abs_cellSum_le (hN : 2 ≤ N) {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    |cellSum N u t| ≤ (|t| + 1 / 2) / Real.sqrt N * (2 / Real.sqrt ((N : ℝ) - 1)) := by
  have h := abs_cellSum_sub_sum_range_le hN hu t 0
  simpa using h

theorem cellSum_neg_param (u : ℕ → ℝ) (t : ℝ) : cellSum N u (-t) = cellSum N u t := by
  simp [cellSum, cellTerm_neg_param]

end sums

end RandomCellWeil
end RHTower
