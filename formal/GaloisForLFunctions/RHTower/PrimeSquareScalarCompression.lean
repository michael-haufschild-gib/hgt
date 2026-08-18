import GaloisForLFunctions.RHTower.AdelicIntertwinerType

/-!
# The scalar prime-square reflected-line compression saturates the accelerated type

The critical-normalized local coefficient of the deformed reflection-line comparison is

```text
β_p(c) = ( p (p^c + p^{-c}) − (p − 1) ) / √((p + p^{2c})(p + p^{-2c})).
```

Two exact facts.  With `x = p^c + p^{-c}` the numerator `N` and the squared denominator `D²`
satisfy `N² − D² = p(p−1)x(x−2)`, so `β_p(c) ≥ 1` with equality exactly at `c = 0`: the local
coefficient is a genuine critical-line reporter.  And `log β_p(c) = c log p + O(p^{-c} + p^{2c−1})`,
so the finite product below the cutoff has logarithm `(|c| + o(1)) ϑ(N)` — a positive multiple of
`ϑ`, hence the maximal accelerated Wold type `e^{−γ}` whatever the drift.
-/

open Filter Topology

namespace RHTower

/-- The critical-normalized local reflected-line coefficient, in plain real coordinates. -/
theorem one_le_scalarCompressionRatio {P r : ℝ} (hP : 1 < P) (hr : 0 < r) :
    1 ≤ (P * (r + r⁻¹) - (P - 1)) / Real.sqrt ((P + r ^ 2) * (P + r⁻¹ ^ 2)) := by
  have hP0 : (0 : ℝ) < P := by linarith
  set x : ℝ := r + r⁻¹ with hxdef
  have hx2 : 2 ≤ x := by
    have h := sq_nonneg (r - 1)
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
    have hinvpos : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr
    rw [hxdef]
    nlinarith [h, hrr, hr, hinvpos]
  have hDsq : (P + r ^ 2) * (P + r⁻¹ ^ 2) = P ^ 2 + P * (x ^ 2 - 2) + 1 := by
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
    have hx : x ^ 2 = r ^ 2 + 2 + r⁻¹ ^ 2 := by
      rw [hxdef]
      nlinarith [hrr]
    rw [hx]
    nlinarith [hrr]
  have hDpos : (0 : ℝ) < (P + r ^ 2) * (P + r⁻¹ ^ 2) := by positivity
  set D : ℝ := Real.sqrt ((P + r ^ 2) * (P + r⁻¹ ^ 2)) with hDdef
  have hD0 : (0 : ℝ) < D := Real.sqrt_pos.mpr hDpos
  have hDsq' : D ^ 2 = P ^ 2 + P * (x ^ 2 - 2) + 1 := by
    rw [hDdef, Real.sq_sqrt hDpos.le, hDsq]
  set N : ℝ := P * x - (P - 1) with hNdef
  have hN0 : (0 : ℝ) < N := by
    rw [hNdef]
    nlinarith [hx2, hP0]
  have hkey : N ^ 2 - D ^ 2 = P * (P - 1) * x * (x - 2) := by
    rw [hNdef, hDsq']
    ring
  have hge : D ≤ N := by
    have hnn : (0 : ℝ) ≤ P * (P - 1) * x * (x - 2) := by
      have h1 : (0 : ℝ) ≤ P - 1 := by linarith
      have h2 : (0 : ℝ) ≤ x - 2 := by linarith
      have h3 : (0 : ℝ) ≤ x := by linarith
      positivity
    nlinarith [hkey, hN0, hD0]
  rw [le_div_iff₀ hD0]
  linarith

theorem scalarCompressionRatio_eq_one_iff {P r : ℝ} (hP : 1 < P) (hr : 0 < r) :
    (P * (r + r⁻¹) - (P - 1)) / Real.sqrt ((P + r ^ 2) * (P + r⁻¹ ^ 2)) = 1 ↔ r = 1 := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
  have hinvpos : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr
  set x : ℝ := r + r⁻¹ with hxdef
  have hx2 : 2 ≤ x := by
    have h := sq_nonneg (r - 1)
    rw [hxdef]
    nlinarith [h, hrr, hr, hinvpos]
  have hDsq : (P + r ^ 2) * (P + r⁻¹ ^ 2) = P ^ 2 + P * (x ^ 2 - 2) + 1 := by
    have hx : x ^ 2 = r ^ 2 + 2 + r⁻¹ ^ 2 := by rw [hxdef]; nlinarith [hrr]
    rw [hx]; nlinarith [hrr]
  have hDpos : (0 : ℝ) < (P + r ^ 2) * (P + r⁻¹ ^ 2) := by positivity
  set D : ℝ := Real.sqrt ((P + r ^ 2) * (P + r⁻¹ ^ 2)) with hDdef
  have hD0 : (0 : ℝ) < D := Real.sqrt_pos.mpr hDpos
  have hDsq' : D ^ 2 = P ^ 2 + P * (x ^ 2 - 2) + 1 := by
    rw [hDdef, Real.sq_sqrt hDpos.le, hDsq]
  set N : ℝ := P * x - (P - 1) with hNdef
  have hN0 : (0 : ℝ) < N := by rw [hNdef]; nlinarith [hx2, hP0]
  have hkey : N ^ 2 - D ^ 2 = P * (P - 1) * x * (x - 2) := by rw [hNdef, hDsq']; ring
  constructor
  · intro h
    have hND : N = D := by
      rw [div_eq_one_iff_eq (ne_of_gt hD0)] at h
      exact h
    have hzero : P * (P - 1) * x * (x - 2) = 0 := by
      rw [← hkey, hND]; ring
    have hx2' : x = 2 := by
      have hPpos : (0 : ℝ) < P * (P - 1) := by nlinarith [hP0]
      have hxpos : (0 : ℝ) < x := by linarith
      have hfac : (P * (P - 1) * x) * (x - 2) = 0 := by rw [← hzero]
      rcases mul_eq_zero.mp hfac with h' | h'
      · nlinarith [hPpos, hxpos, h']
      · linarith
    have hsum : r + r⁻¹ = 2 := by rw [← hxdef]; exact hx2'
    have hsq : (r - 1) ^ 2 = 0 := by nlinarith [hsum, hrr, hr]
    have : r - 1 = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith
  · intro h
    subst h
    have hx2' : x = 2 := by rw [hxdef]; norm_num
    have hzero : N ^ 2 - D ^ 2 = 0 := by rw [hkey, hx2']; ring
    have hND : N = D := by nlinarith [hzero, hN0, hD0]
    rw [div_eq_one_iff_eq (ne_of_gt hD0)]
    exact hND

/-- The relative defect of the local reflected-line coefficient's numerator. -/
noncomputable def scalarCompA (P u : ℝ) : ℝ := u⁻¹ ^ 2 - u⁻¹ + (P * u)⁻¹

/-- The relative defect of its squared denominator. -/
noncomputable def scalarCompB (P u : ℝ) : ℝ := u⁻¹ ^ 2 / P + u ^ 2 / P + 1 / P ^ 2

theorem scalarComp_num_factor {P u : ℝ} (hP0 : 0 < P) (hu0 : 0 < u) :
    P * (u + u⁻¹) - (P - 1) = P * u * (1 + scalarCompA P u) := by
  rw [scalarCompA]
  field_simp
  ring

theorem scalarComp_den_factor {P u : ℝ} (hP0 : 0 < P) (hu0 : 0 < u) :
    (P + u ^ 2) * (P + u⁻¹ ^ 2) = P ^ 2 * (1 + scalarCompB P u) := by
  rw [scalarCompB]
  field_simp
  ring

theorem scalarCompA_lb {P u : ℝ} (hP0 : 0 < P) (hu0 : 0 < u) :
    (3 : ℝ) / 4 ≤ 1 + scalarCompA P u := by
  rw [scalarCompA]
  have hsq : (0 : ℝ) ≤ (u⁻¹ - 1 / 2) ^ 2 := sq_nonneg _
  have hinv : (0 : ℝ) < (P * u)⁻¹ := by positivity
  nlinarith [hsq, hinv]

theorem scalarCompA_abs {P u : ℝ} (hP : 2 ≤ P) (hu1 : 1 ≤ u) :
    |scalarCompA P u| ≤ 5 / 2 * u⁻¹ := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have huinv0 : (0 : ℝ) < u⁻¹ := inv_pos.mpr hu0
  have huinv1 : u⁻¹ ≤ 1 := by rw [inv_le_one₀ hu0]; exact hu1
  rw [scalarCompA]
  have h1 : u⁻¹ ^ 2 ≤ u⁻¹ := by nlinarith [huinv0, huinv1]
  have h2 : (P * u)⁻¹ ≤ u⁻¹ / 2 := by
    rw [mul_inv]
    have hPinv : P⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hP0 (by norm_num)]
      linarith
    nlinarith [huinv0, hPinv, inv_pos.mpr hP0]
  have h3 : (0 : ℝ) ≤ (P * u)⁻¹ := by positivity
  rw [abs_le]
  constructor <;> nlinarith [h1, h2, h3, huinv0]

theorem scalarCompB_nonneg {P u : ℝ} (hP0 : 0 < P) (hu0 : 0 < u) : 0 ≤ scalarCompB P u := by
  rw [scalarCompB]; positivity

theorem scalarCompB_ub {P u : ℝ} (hP : 2 ≤ P) (hu1 : 1 ≤ u) :
    scalarCompB P u ≤ 5 / 2 * (u ^ 2 / P) := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have huinv0 : (0 : ℝ) < u⁻¹ := inv_pos.mpr hu0
  have huinv1 : u⁻¹ ≤ 1 := by rw [inv_le_one₀ hu0]; exact hu1
  rw [scalarCompB]
  have h1 : u⁻¹ ^ 2 / P ≤ u ^ 2 / P := by
    have hle : u⁻¹ ^ 2 ≤ u ^ 2 := by nlinarith [huinv0, huinv1, hu1]
    gcongr
  have h2 : (1 : ℝ) / P ^ 2 ≤ u ^ 2 / (2 * P) := by
    have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith [hu1]
    have hPP : 2 * P ≤ P ^ 2 := by nlinarith [hP, hP0]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hu2, hPP, hP0, mul_nonneg (sub_nonneg.mpr hu2) (sq_nonneg P)]
  have h3 : u ^ 2 / (2 * P) = 1 / 2 * (u ^ 2 / P) := by ring
  linarith [h1, h2, h3.le, h3.ge]

theorem scalarComp_log_eq {P u : ℝ} (hP0 : 0 < P) (hu0 : 0 < u)
    (ha0 : 0 < 1 + scalarCompA P u) (hb0 : 0 < 1 + scalarCompB P u) :
    Real.log ((P * (u + u⁻¹) - (P - 1)) / Real.sqrt ((P + u ^ 2) * (P + u⁻¹ ^ 2)))
      = Real.log u + Real.log (1 + scalarCompA P u)
        - 1 / 2 * Real.log (1 + scalarCompB P u) := by
  have hs0 : (0 : ℝ) < Real.sqrt (1 + scalarCompB P u) := Real.sqrt_pos.mpr hb0
  have hsqrt : Real.sqrt ((P + u ^ 2) * (P + u⁻¹ ^ 2)) = P * Real.sqrt (1 + scalarCompB P u) := by
    rw [scalarComp_den_factor hP0 hu0, Real.sqrt_mul (by positivity), Real.sqrt_sq hP0.le]
  have hratio : (P * (u + u⁻¹) - (P - 1)) / Real.sqrt ((P + u ^ 2) * (P + u⁻¹ ^ 2))
      = u * (1 + scalarCompA P u) / Real.sqrt (1 + scalarCompB P u) := by
    rw [scalarComp_num_factor hP0 hu0, hsqrt]
    field_simp
  rw [hratio, Real.log_div (by positivity : (0:ℝ) < u * (1 + scalarCompA P u)).ne' (ne_of_gt hs0),
    Real.log_mul (ne_of_gt hu0) (ne_of_gt ha0), Real.log_sqrt hb0.le]
  ring

theorem abs_log_one_add_le {a : ℝ} (ha : 3 / 4 ≤ 1 + a) : |Real.log (1 + a)| ≤ 4 / 3 * |a| := by
  have ha0 : (0 : ℝ) < 1 + a := by linarith
  have hup : Real.log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos ha0
    linarith
  have hlow : -(4 / 3 * |a|) ≤ Real.log (1 + a) := by
    have hinv := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 + a)⁻¹ by positivity)
    rw [Real.log_inv] at hinv
    have hstep : (1 + a)⁻¹ - 1 = -a / (1 + a) := by field_simp; ring
    rw [hstep] at hinv
    have hle : -a / (1 + a) ≤ 4 / 3 * |a| := by
      rcases le_or_gt a 0 with hneg | hpos
      · rw [abs_of_nonpos hneg, div_le_iff₀ ha0]
        nlinarith [ha, hneg]
      · rw [abs_of_pos hpos]
        have hnp : -a / (1 + a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha0.le
        nlinarith [hnp, hpos]
    linarith
  rw [abs_le]
  refine ⟨by linarith, ?_⟩
  have : a ≤ |a| := le_abs_self a
  linarith

/-- **The local reflected-line coefficient has logarithm `c log p` up to an absolutely summable
defect.**  Written with `u = p^c`, the numerator and the squared denominator are `p u` and `p²`
times factors that differ from one by `O(u⁻¹)` and `O(u²/p)`. -/
theorem abs_log_scalarCompressionRatio_sub_log_le {P u : ℝ} (hP : 2 ≤ P) (hu1 : 1 ≤ u) :
    |Real.log ((P * (u + u⁻¹) - (P - 1)) / Real.sqrt ((P + u ^ 2) * (P + u⁻¹ ^ 2)))
        - Real.log u|
      ≤ 4 * u⁻¹ + 3 * u ^ 2 / (2 * P) := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have huinv0 : (0 : ℝ) < u⁻¹ := inv_pos.mpr hu0
  have ha1 := scalarCompA_lb hP0 hu0
  have ha0 : (0 : ℝ) < 1 + scalarCompA P u := by linarith
  have hb0 : (0 : ℝ) ≤ scalarCompB P u := scalarCompB_nonneg hP0 hu0
  have hbpos : (0 : ℝ) < 1 + scalarCompB P u := by linarith
  have hlogeq := scalarComp_log_eq hP0 hu0 ha0 hbpos
  have hA := abs_log_one_add_le ha1
  have hAabs := scalarCompA_abs hP hu1
  have hfin1 : |Real.log (1 + scalarCompA P u)| ≤ 10 / 3 * u⁻¹ := by
    refine le_trans hA ?_
    linarith [hAabs]
  have hlogB : Real.log (1 + scalarCompB P u) ≤ 5 / 2 * (u ^ 2 / P) := by
    have hle := Real.log_le_sub_one_of_pos hbpos
    have := scalarCompB_ub hP hu1
    linarith
  have hlogB0 : (0 : ℝ) ≤ Real.log (1 + scalarCompB P u) := Real.log_nonneg (by linarith)
  have heq : 3 * u ^ 2 / (2 * P) = 3 / 2 * (u ^ 2 / P) := by field_simp
  have hA1 := (abs_le.mp hfin1).1
  have hA2 := (abs_le.mp hfin1).2
  have h4 : (10 : ℝ) / 3 * u⁻¹ ≤ 4 * u⁻¹ := by linarith [huinv0]
  have h6 : (0 : ℝ) ≤ 3 / 2 * (u ^ 2 / P) := by positivity
  rw [hlogeq, heq, abs_le]
  constructor
  · linarith
  · linarith


/-! ## The local coefficient -/

/-- The critical-normalized local reflected-line coefficient of the prime-square Fourier clock. -/
noncomputable def betaLocal (p : ℕ) (c : ℝ) : ℝ :=
  ((p : ℝ) * ((p : ℝ) ^ c + (p : ℝ) ^ (-c)) - ((p : ℝ) - 1)) /
    Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-(2 * c))))

theorem betaLocal_eq_ratio {p : ℕ} (hp : 2 ≤ p) (c : ℝ) :
    betaLocal p c = ((p : ℝ) * ((p : ℝ) ^ c + ((p : ℝ) ^ c)⁻¹) - ((p : ℝ) - 1)) /
      Real.sqrt (((p : ℝ) + ((p : ℝ) ^ c) ^ 2) * ((p : ℝ) + (((p : ℝ) ^ c)⁻¹) ^ 2)) := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hneg : (p : ℝ) ^ (-c) = ((p : ℝ) ^ c)⁻¹ := Real.rpow_neg hP0.le c
  have hsq : ((p : ℝ) ^ c) ^ 2 = (p : ℝ) ^ (2 * c) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ c) 2, ← Real.rpow_mul hP0.le]
    congr 1
    push_cast
    ring
  have hsqinv : (((p : ℝ) ^ c)⁻¹) ^ 2 = (p : ℝ) ^ (-(2 * c)) := by
    rw [← hneg, ← Real.rpow_natCast ((p : ℝ) ^ (-c)) 2, ← Real.rpow_mul hP0.le]
    congr 1
    push_cast
    ring
  rw [betaLocal, hneg, hsq, hsqinv]

/-- **`(8)`: the local coefficient is at least one.** -/
theorem one_le_betaLocal {p : ℕ} (hp : 2 ≤ p) (c : ℝ) : 1 ≤ betaLocal p c := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [betaLocal_eq_ratio hp c]
  exact one_le_scalarCompressionRatio (by linarith) (Real.rpow_pos_of_pos hP0 c)

/-- **`(8)`: it equals one exactly at the critical parameter.** -/
theorem betaLocal_eq_one_iff {p : ℕ} (hp : 2 ≤ p) (c : ℝ) : betaLocal p c = 1 ↔ c = 0 := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogP : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  rw [betaLocal_eq_ratio hp c,
    scalarCompressionRatio_eq_one_iff (by linarith) (Real.rpow_pos_of_pos hP0 c)]
  rw [Real.rpow_def_of_pos hP0, Real.exp_eq_one_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (ne_of_gt hlogP)
    · exact h'
  · intro h
    rw [h, mul_zero]

/-- **The local logarithm is `c log p` up to a summable defect.** -/
theorem abs_log_betaLocal_sub_le {c : ℝ} (hc0 : 0 < c) {p : ℕ} (hp : 2 ≤ p) :
    |Real.log (betaLocal p c) - c * Real.log (p : ℝ)|
      ≤ 4 * (p : ℝ) ^ (-c) + 3 / 2 * (p : ℝ) ^ (2 * c - 1) := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hu1 : (1 : ℝ) ≤ (p : ℝ) ^ c := Real.one_le_rpow hP1 hc0.le
  have hlogu : Real.log ((p : ℝ) ^ c) = c * Real.log (p : ℝ) := Real.log_rpow hP0 c
  have hinv : ((p : ℝ) ^ c)⁻¹ = (p : ℝ) ^ (-c) := (Real.rpow_neg hP0.le c).symm
  have hsq : ((p : ℝ) ^ c) ^ 2 = (p : ℝ) ^ (2 * c) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ c) 2, ← Real.rpow_mul hP0.le]
    congr 1
    push_cast
    ring
  have hkey := abs_log_scalarCompressionRatio_sub_log_le hP2 hu1
  rw [betaLocal_eq_ratio hp c, hlogu] at *
  refine le_trans hkey ?_
  rw [hinv, hsq]
  have hfrac : 3 * (p : ℝ) ^ (2 * c) / (2 * (p : ℝ)) = 3 / 2 * (p : ℝ) ^ (2 * c - 1) := by
    have hpow : (p : ℝ) ^ (2 * c - 1) = (p : ℝ) ^ (2 * c) / (p : ℝ) := by
      have h : (p : ℝ) ^ (2 * c - 1) * (p : ℝ) ^ (1 : ℝ) = (p : ℝ) ^ (2 * c) := by
        rw [← Real.rpow_add hP0]; congr 1; ring
      rw [Real.rpow_one] at h
      rw [eq_div_iff (ne_of_gt hP0)]
      exact h
    rw [hpow]
    field_simp
  rw [hfrac]

/-! ## The saturated accelerated type -/

/-- `(12)`: the logarithm of the finite compression grows linearly in the cutoff with slope `c`. -/
theorem tendsto_sum_log_betaLocal_div {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesBelow N, Real.log (betaLocal p c)) / (N : ℝ))
      atTop (nhds c) := by
  classical
  set E : ℕ → ℝ := fun N =>
    ∑ p ∈ Nat.primesBelow N, (Real.log (betaLocal p c) - c * Real.log (p : ℝ)) with hEdef
  have hEbound : ∀ N : ℕ, |E N|
      ≤ 4 * (1 + (N : ℝ) ^ (1 - c) / (1 - c)) + 3 / 2 * (1 + (N : ℝ) ^ (2 * c) / (2 * c)) := by
    intro N
    have hstep : |E N| ≤ ∑ p ∈ Nat.primesBelow N,
        (4 * (p : ℝ) ^ (-c) + 3 / 2 * (p : ℝ) ^ (2 * c - 1)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p hp => ?_)
      exact abs_log_betaLocal_sub_le hc0 (Nat.prime_of_mem_primesBelow hp).two_le
    refine le_trans hstep ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hsub : Nat.primesBelow N ⊆ Finset.Icc 1 N := by
      intro p hp
      have hp2 := (Nat.prime_of_mem_primesBelow hp).two_le
      have hlt := Nat.lt_of_mem_primesBelow hp
      rw [Finset.mem_Icc]
      omega
    have h1 : ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (-c)
        ≤ 1 + (N : ℝ) ^ (1 - c) / (1 - c) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => by positivity) ?_
      exact sum_rpow_neg_head_le hc0 (by linarith) N
    have h2 : ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (2 * c - 1)
        ≤ 1 + (N : ℝ) ^ (2 * c) / (2 * c) := by
      have hcongr : ∀ p ∈ Nat.primesBelow N,
          (p : ℝ) ^ (2 * c - 1) = (p : ℝ) ^ (-(1 - 2 * c)) := by
        intro p _; congr 1; ring
      rw [Finset.sum_congr rfl hcongr]
      have hhead := sum_rpow_neg_head_le (c := 1 - 2 * c) (by linarith) (by linarith) N
      have hexp : (1 : ℝ) - (1 - 2 * c) = 2 * c := by ring
      rw [hexp] at hhead
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => by positivity) hhead
    linarith
  have hzero : Tendsto (fun N : ℕ => E N / (N : ℝ)) atTop (nhds 0) := by
    have hup : Tendsto (fun N : ℕ =>
        (4 * (1 + (N : ℝ) ^ (1 - c) / (1 - c))
          + 3 / 2 * (1 + (N : ℝ) ^ (2 * c) / (2 * c))) / (N : ℝ)) atTop (nhds 0) := by
      have hone : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have hpow : ∀ {e : ℝ}, e < 1 → Tendsto (fun N : ℕ => (N : ℝ) ^ (e - 1)) atTop (nhds 0) := by
        intro e he
        have hneg : Tendsto (fun x : ℝ => x ^ (e - 1)) atTop (nhds 0) := by
          have := tendsto_rpow_neg_atTop (y := 1 - e) (by linarith)
          refine this.congr fun x => ?_
          congr 1
          ring
        exact hneg.comp tendsto_natCast_atTop_atTop
      have h1 := hpow (e := 1 - c) (by linarith)
      have h2 := hpow (e := 2 * c) (by linarith)
      have hsum : Tendsto (fun N : ℕ => 4 * ((1 : ℝ) / (N : ℝ) + (N : ℝ) ^ ((1 - c) - 1) / (1 - c))
          + 3 / 2 * ((1 : ℝ) / (N : ℝ) + (N : ℝ) ^ (2 * c - 1) / (2 * c))) atTop (nhds 0) := by
        have ha := (hone.add (h1.div_const (1 - c))).const_mul (4 : ℝ)
        have hb := (hone.add (h2.div_const (2 * c))).const_mul ((3 : ℝ) / 2)
        have := ha.add hb
        simpa using this
      refine hsum.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hsplit : ∀ e : ℝ, (N : ℝ) ^ (e - 1) = (N : ℝ) ^ e / (N : ℝ) := by
        intro e
        have h : (N : ℝ) ^ (e - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ e := by
          rw [← Real.rpow_add hNr]; congr 1; ring
        rw [Real.rpow_one] at h
        rw [eq_div_iff (ne_of_gt hNr)]
        exact h
      rw [hsplit (1 - c), hsplit (2 * c)]
      field_simp
    refine squeeze_zero_norm' ?_ hup
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hNr]
    gcongr
    exact hEbound N
  have hmain : ∀ N : ℕ,
      (∑ p ∈ Nat.primesBelow N, Real.log (betaLocal p c)) / (N : ℝ)
        = E N / (N : ℝ) + c * ((∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) / (N : ℝ)) := by
    intro N
    rw [hEdef]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp
    ring
  have hlim := hzero.add ((tendsto_sum_primesBelow_log_div).const_mul c)
  rw [zero_add, mul_one] at hlim
  exact hlim.congr fun N => (hmain N).symm

/-- **`(18)`: the scalar compression has the maximal accelerated type, whatever the drift.** -/
theorem tendsto_mertensProduct_mul_ell2_betaProduct {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N *
        ell2 (∏ p ∈ Nat.primesBelow N, betaLocal p c)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  classical
  have hfac : ∀ N : ℕ, ∀ p ∈ Nat.primesBelow N, 0 < betaLocal p c := by
    intro N p hp
    have := one_le_betaLocal (Nat.prime_of_mem_primesBelow hp).two_le c
    linarith
  have hSpos : ∀ N : ℕ, 0 < ∏ p ∈ Nat.primesBelow N, betaLocal p c :=
    fun N => Finset.prod_pos (hfac N)
  have hlogS : ∀ N : ℕ, Real.log (∏ p ∈ Nat.primesBelow N, betaLocal p c)
      = ∑ p ∈ Nat.primesBelow N, Real.log (betaLocal p c) :=
    fun N => Real.log_prod fun p hp => ne_of_gt (hfac N p hp)
  refine tendsto_mertensProduct_mul_ell2_of_log_linear hc0
    (Filter.Eventually.of_forall hSpos) ?_
  refine (tendsto_sum_log_betaLocal_div hc0 hc).congr fun N => ?_
  rw [hlogS N]

end RHTower
