import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Logarithms of polynomial size are negligible against the characteristic

Nevanlinna's error term is the logarithm of an expression that is polynomial in the radius and in
the characteristic.  For a transcendental function the characteristic outgrows every logarithm of
the radius, so such a term is `o(T(r))`: for every `ε > 0` it is eventually below `ε · T(r)`.

This is the packaging step that turns the explicit error bound of the logarithmic-derivative lemma
into the qualitative statement the second main theorem consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Real

/-- `1 + x^k ≤ (1 + x)^k` for `x ≥ 0` and `k ≥ 1`. -/
theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    1 + x ^ k ≤ (1 + x) ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have hstep := ih hn
        have hx1 : (0 : ℝ) ≤ (1 + x) ^ n := by positivity
        have hxn : (0 : ℝ) ≤ x ^ n := by positivity
        calc 1 + x ^ (n + 1) = 1 + x ^ n * x := by ring
          _ ≤ (1 + x ^ n) * (1 + x) := by nlinarith [hxn, hx]
          _ ≤ (1 + x) ^ n * (1 + x) := by
              exact mul_le_mul_of_nonneg_right hstep (by linarith)
          _ = (1 + x) ^ (n + 1) := by ring

/-- The logarithm of `1 + C·X·Y` splits. -/
theorem log_one_add_mul_le {C X Y : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.log (1 + C * X * Y) ≤ Real.log (1 + C) + Real.log (1 + X) + Real.log (1 + Y) := by
  have hprod : 1 + C * X * Y ≤ (1 + C) * (1 + X) * (1 + Y) := by nlinarith [hC, hX, hY]
  have h1 : (0 : ℝ) < 1 + C * X * Y := by positivity
  calc Real.log (1 + C * X * Y) ≤ Real.log ((1 + C) * (1 + X) * (1 + Y)) :=
        Real.log_le_log h1 hprod
    _ = Real.log (1 + C) + Real.log (1 + X) + Real.log (1 + Y) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
          (by positivity)]

/-- `log (x + 2) / x → 0`. -/
theorem tendsto_log_add_div_atTop : Tendsto (fun x : ℝ => Real.log (x + 2) / x) atTop (nhds 0) := by
  have h := Real.isLittleO_log_id_atTop
  have hcomp : (fun x : ℝ => Real.log (x + 2)) =o[atTop] fun x : ℝ => x := by
    have hshift : (fun x : ℝ => Real.log (x + 2)) =O[atTop] fun x : ℝ => Real.log x := by
      refine Asymptotics.IsBigO.of_bound 2 ?_
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := by linarith
      have hle : Real.log (x + 2) ≤ Real.log (x * x) := by
        refine Real.log_le_log (by linarith) ?_
        nlinarith
      have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
        abs_of_nonneg hlogx]
      rw [Real.log_mul (ne_of_gt hx0) (ne_of_gt hx0)] at hle
      linarith
    exact hshift.trans_isLittleO h
  have := hcomp.tendsto_div_nhds_zero
  exact this


/-- **The Nevanlinna error term is negligible.**  A quantity bounded by the logarithm of an
expression polynomial in `r` and in `T r` is eventually below `ε · T r`, for every `ε > 0`, as soon
as `T` outgrows every logarithm of the radius. -/
theorem eventually_le_of_log_poly_bound {S T : ℝ → ℝ} {C : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hk : 1 ≤ k)
    (hS : ∀ᶠ r in atTop, S r ≤ Real.log (1 + C * (r + 1) ^ k * (T r + 1) ^ k))
    (hT1 : ∀ᶠ r in atTop, 1 ≤ T r)
    (hTlog : Tendsto (fun r => Real.log r / T r) atTop (nhds 0))
    (hTtop : Tendsto T atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, S r ≤ ε * T r := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- the three pieces
  have hpart1 : ∀ᶠ r in atTop, Real.log (1 + C) ≤ ε / 3 * T r := by
    have hdiv : Tendsto (fun r => ε / 3 * T r) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) hTtop
    exact hdiv.eventually_ge_atTop _
  have hpart2 : ∀ᶠ r in atTop, (k : ℝ) * Real.log (r + 2) ≤ ε / 3 * T r := by
    have hlim : Tendsto (fun r => (k : ℝ) * (2 * (Real.log r / T r))) atTop (nhds 0) := by
      have h := hTlog.const_mul (2 : ℝ)
      rw [mul_zero] at h
      have h2 := h.const_mul ((k : ℝ))
      rwa [mul_zero] at h2
    filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)),
      hT1, eventually_ge_atTop (2 : ℝ)] with r hr hTr hr2
    have hTr0 : (0 : ℝ) < T r := by linarith
    have hlog2 : Real.log (r + 2) ≤ 2 * Real.log r := by
      have hle : r + 2 ≤ r * r := by nlinarith
      have hstep : Real.log (r + 2) ≤ Real.log (r * r) := Real.log_le_log (by linarith) hle
      rwa [Real.log_mul (by linarith) (by linarith), ← two_mul] at hstep
    have hkey : (k : ℝ) * (2 * (Real.log r / T r)) < ε / 3 := hr
    have hprod : (k : ℝ) * (2 * (Real.log r / T r)) * T r < ε / 3 * T r :=
      mul_lt_mul_of_pos_right hkey hTr0
    have hcancel : (k : ℝ) * (2 * (Real.log r / T r)) * T r = (k : ℝ) * (2 * Real.log r) := by
      field_simp
      ring
    rw [hcancel] at hprod
    have hmono : (k : ℝ) * Real.log (r + 2) ≤ (k : ℝ) * (2 * Real.log r) :=
      mul_le_mul_of_nonneg_left hlog2 hk0.le
    linarith [hprod, hmono]
  have hpart3 : ∀ᶠ r in atTop, (k : ℝ) * Real.log (T r + 2) ≤ ε / 3 * T r := by
    have hcomp : Tendsto (fun r => Real.log (T r + 2) / T r) atTop (nhds 0) :=
      tendsto_log_add_div_atTop.comp hTtop
    have hlim : Tendsto (fun r => (k : ℝ) * (Real.log (T r + 2) / T r)) atTop (nhds 0) := by
      have h := hcomp.const_mul ((k : ℝ))
      rwa [mul_zero] at h
    filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)), hT1]
      with r hr hTr
    have hTr0 : (0 : ℝ) < T r := by linarith
    have hprod : (k : ℝ) * (Real.log (T r + 2) / T r) * T r < ε / 3 * T r :=
      mul_lt_mul_of_pos_right hr hTr0
    have hcancel : (k : ℝ) * (Real.log (T r + 2) / T r) * T r = (k : ℝ) * Real.log (T r + 2) := by
      field_simp
    rw [hcancel] at hprod
    linarith [hprod]
  filter_upwards [hS, hT1, hpart1, hpart2, hpart3, eventually_ge_atTop (0 : ℝ)]
    with r hSr hTr h1 h2 h3 hr0
  have hTr0 : (0 : ℝ) ≤ T r := by linarith
  have hXY : Real.log (1 + C * (r + 1) ^ k * (T r + 1) ^ k)
      ≤ Real.log (1 + C) + Real.log (1 + (r + 1) ^ k) + Real.log (1 + (T r + 1) ^ k) := by
    refine log_one_add_mul_le hC ?_ ?_ <;> positivity
  have hr2 : Real.log (1 + (r + 1) ^ k) ≤ (k : ℝ) * Real.log (r + 2) := by
    have hbase : (1 : ℝ) + (r + 1) ^ k ≤ (r + 2) ^ k := by
      have := one_add_pow_le (x := r + 1) (by positivity) hk
      calc (1 : ℝ) + (r + 1) ^ k ≤ (1 + (r + 1)) ^ k := this
        _ = (r + 2) ^ k := by ring_nf
    calc Real.log (1 + (r + 1) ^ k) ≤ Real.log ((r + 2) ^ k) :=
          Real.log_le_log (by positivity) hbase
      _ = (k : ℝ) * Real.log (r + 2) := by
          rw [Real.log_pow]
  have hT2 : Real.log (1 + (T r + 1) ^ k) ≤ (k : ℝ) * Real.log (T r + 2) := by
    have hbase : (1 : ℝ) + (T r + 1) ^ k ≤ (T r + 2) ^ k := by
      have := one_add_pow_le (x := T r + 1) (by positivity) hk
      calc (1 : ℝ) + (T r + 1) ^ k ≤ (1 + (T r + 1)) ^ k := this
        _ = (T r + 2) ^ k := by ring_nf
    calc Real.log (1 + (T r + 1) ^ k) ≤ Real.log ((T r + 2) ^ k) :=
          Real.log_le_log (by positivity) hbase
      _ = (k : ℝ) * Real.log (T r + 2) := by rw [Real.log_pow]
  have hsplit : ε / 3 * T r + ε / 3 * T r + ε / 3 * T r = ε * T r := by ring
  linarith [hSr, hXY, hr2, hT2, h1, h2, h3, hsplit]

end GaloisForLFunctions.HTGeometry
