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


/-- **The counting conclusion.**  If `(q/2 − 2)·T(r) ≤ S(r) + C` eventually, the error `S` is
negligible against `T`, and `T → ∞`, then `q ≤ 4`. -/
theorem le_four_of_characteristic_bound {q : ℕ} {S T : ℝ → ℝ} {C : ℝ}
    (hbound : ∀ᶠ r in atTop, ((q : ℝ) / 2 - 2) * T r ≤ S r + C)
    (hS : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop, S r ≤ ε * T r)
    (hT : Tendsto T atTop atTop) : q ≤ 4 := by
  by_contra hcon
  push_neg at hcon
  have hq : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hcon
  set c : ℝ := (q : ℝ) / 2 - 2 with hc
  have hcpos : 0 < c := by
    rw [hc]
    linarith
  have hTbig : ∀ᶠ r in atTop, 2 * |C| / c + 1 ≤ T r := hT.eventually_ge_atTop _
  have hev : ∀ᶠ r in atTop, (c * T r ≤ S r + C ∧ S r ≤ c / 2 * T r) ∧ 2 * |C| / c + 1 ≤ T r := by
    filter_upwards [hbound, hS (c / 2) (by positivity), hTbig] with r h1 h2 h3
    exact ⟨⟨h1, h2⟩, h3⟩
  obtain ⟨r, ⟨hb, hs⟩, hTr⟩ := hev.exists
  have habs : (0 : ℝ) ≤ 2 * |C| / c := by positivity
  have hTr0 : (0 : ℝ) < T r := by linarith
  have hhalf : c / 2 * T r ≤ C := by linarith [hb, hs]
  have hCle : C ≤ |C| := le_abs_self C
  have hTle : T r ≤ 2 * |C| / c := by
    rw [le_div_iff₀ hcpos]
    linarith
  linarith [hTr, hTle]


/-- **The negligibility statement over an arbitrary filter.**  A quantity bounded by a constant
multiple of the logarithm of an expression polynomial in a radius `ρ` and in `T` is eventually below
`ε · T`, as soon as `T` outgrows every logarithm of `ρ`. -/
theorem eventually_le_of_log_poly_bound_filter {ι : Type*} {l : Filter ι} {S T ρ : ι → ℝ}
    {C c : ℝ} {k : ℕ} (hC : 0 ≤ C) (hk : 1 ≤ k) (hc : 0 < c)
    (hS : ∀ᶠ i in l, S i ≤ c * Real.log (1 + C * (ρ i + 1) ^ k * (T i + 1) ^ k))
    (hT1 : ∀ᶠ i in l, 1 ≤ T i) (hρ2 : ∀ᶠ i in l, 2 ≤ ρ i)
    (hTlog : Tendsto (fun i => Real.log (ρ i) / T i) l (nhds 0))
    (hTtop : Tendsto T l atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, S i ≤ ε * T i := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hεc : (0 : ℝ) < ε / c := by positivity
  have hpart1 : ∀ᶠ i in l, c * Real.log (1 + C) ≤ ε / 3 * T i := by
    have hdiv : Tendsto (fun i => ε / 3 * T i) l atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) hTtop
    exact hdiv.eventually_ge_atTop _
  have hpart2 : ∀ᶠ i in l, c * ((k : ℝ) * Real.log (ρ i + 2)) ≤ ε / 3 * T i := by
    have hlim : Tendsto (fun i => c * ((k : ℝ) * (2 * (Real.log (ρ i) / T i)))) l (nhds 0) := by
      have h := hTlog.const_mul (2 : ℝ)
      rw [mul_zero] at h
      have h2 := h.const_mul ((k : ℝ))
      rw [mul_zero] at h2
      have h3 := h2.const_mul c
      rwa [mul_zero] at h3
    filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)),
      hT1, hρ2] with i hi hTi hρi
    have hTi0 : (0 : ℝ) < T i := by linarith
    have hlog2 : Real.log (ρ i + 2) ≤ 2 * Real.log (ρ i) := by
      have hle : ρ i + 2 ≤ ρ i * ρ i := by nlinarith
      have hstep : Real.log (ρ i + 2) ≤ Real.log (ρ i * ρ i) :=
        Real.log_le_log (by linarith) hle
      rwa [Real.log_mul (by linarith) (by linarith), ← two_mul] at hstep
    have hprod : c * ((k : ℝ) * (2 * (Real.log (ρ i) / T i))) * T i < ε / 3 * T i :=
      mul_lt_mul_of_pos_right hi hTi0
    have hcancel : c * ((k : ℝ) * (2 * (Real.log (ρ i) / T i))) * T i
        = c * ((k : ℝ) * (2 * Real.log (ρ i))) := by
      field_simp
    rw [hcancel] at hprod
    have hmono : c * ((k : ℝ) * Real.log (ρ i + 2)) ≤ c * ((k : ℝ) * (2 * Real.log (ρ i))) := by
      have := mul_le_mul_of_nonneg_left hlog2 hk0.le
      exact mul_le_mul_of_nonneg_left this hc.le
    linarith [hprod, hmono]
  have hpart3 : ∀ᶠ i in l, c * ((k : ℝ) * Real.log (T i + 2)) ≤ ε / 3 * T i := by
    have hcomp : Tendsto (fun i => Real.log (T i + 2) / T i) l (nhds 0) :=
      tendsto_log_add_div_atTop.comp hTtop
    have hlim : Tendsto (fun i => c * ((k : ℝ) * (Real.log (T i + 2) / T i))) l (nhds 0) := by
      have h := hcomp.const_mul ((k : ℝ))
      rw [mul_zero] at h
      have h2 := h.const_mul c
      rwa [mul_zero] at h2
    filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)), hT1]
      with i hi hTi
    have hTi0 : (0 : ℝ) < T i := by linarith
    have hprod : c * ((k : ℝ) * (Real.log (T i + 2) / T i)) * T i < ε / 3 * T i :=
      mul_lt_mul_of_pos_right hi hTi0
    have hcancel : c * ((k : ℝ) * (Real.log (T i + 2) / T i)) * T i
        = c * ((k : ℝ) * Real.log (T i + 2)) := by
      field_simp
    rw [hcancel] at hprod
    linarith [hprod]
  filter_upwards [hS, hT1, hρ2, hpart1, hpart2, hpart3] with i hSi hTi hρi h1 h2 h3
  have hTi0 : (0 : ℝ) ≤ T i := by linarith
  have hρi0 : (0 : ℝ) ≤ ρ i := by linarith
  have hXY : Real.log (1 + C * (ρ i + 1) ^ k * (T i + 1) ^ k)
      ≤ Real.log (1 + C) + Real.log (1 + (ρ i + 1) ^ k) + Real.log (1 + (T i + 1) ^ k) := by
    refine log_one_add_mul_le hC ?_ ?_ <;> positivity
  have hr2 : Real.log (1 + (ρ i + 1) ^ k) ≤ (k : ℝ) * Real.log (ρ i + 2) := by
    have hbase : (1 : ℝ) + (ρ i + 1) ^ k ≤ (ρ i + 2) ^ k := by
      have hstep := one_add_pow_le (x := ρ i + 1) (by positivity) hk
      calc (1 : ℝ) + (ρ i + 1) ^ k ≤ (1 + (ρ i + 1)) ^ k := hstep
        _ = (ρ i + 2) ^ k := by ring_nf
    calc Real.log (1 + (ρ i + 1) ^ k) ≤ Real.log ((ρ i + 2) ^ k) :=
          Real.log_le_log (by positivity) hbase
      _ = (k : ℝ) * Real.log (ρ i + 2) := by rw [Real.log_pow]
  have hT2 : Real.log (1 + (T i + 1) ^ k) ≤ (k : ℝ) * Real.log (T i + 2) := by
    have hbase : (1 : ℝ) + (T i + 1) ^ k ≤ (T i + 2) ^ k := by
      have hstep := one_add_pow_le (x := T i + 1) (by positivity) hk
      calc (1 : ℝ) + (T i + 1) ^ k ≤ (1 + (T i + 1)) ^ k := hstep
        _ = (T i + 2) ^ k := by ring_nf
    calc Real.log (1 + (T i + 1) ^ k) ≤ Real.log ((T i + 2) ^ k) :=
          Real.log_le_log (by positivity) hbase
      _ = (k : ℝ) * Real.log (T i + 2) := by rw [Real.log_pow]
  have hscaled : c * Real.log (1 + C * (ρ i + 1) ^ k * (T i + 1) ^ k)
      ≤ c * Real.log (1 + C) + c * ((k : ℝ) * Real.log (ρ i + 2))
        + c * ((k : ℝ) * Real.log (T i + 2)) := by
    have := mul_le_mul_of_nonneg_left hXY hc.le
    nlinarith [this, hr2, hT2, hc.le, mul_le_mul_of_nonneg_left hr2 hc.le,
      mul_le_mul_of_nonneg_left hT2 hc.le]
  linarith [hSi, hscaled, h1, h2, h3]

/-- The negligibility statement with a constant multiple in front of the logarithm. -/
theorem eventually_le_of_log_poly_bound_const {S T : ℝ → ℝ} {C c : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hk : 1 ≤ k) (hc : 0 < c)
    (hS : ∀ᶠ r in atTop, S r ≤ c * Real.log (1 + C * (r + 1) ^ k * (T r + 1) ^ k))
    (hT1 : ∀ᶠ r in atTop, 1 ≤ T r)
    (hTlog : Tendsto (fun r => Real.log r / T r) atTop (nhds 0))
    (hTtop : Tendsto T atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, S r ≤ ε * T r := by
  have hS' : ∀ᶠ r in atTop, (fun r => S r / c) r
      ≤ Real.log (1 + C * (r + 1) ^ k * (T r + 1) ^ k) := by
    filter_upwards [hS] with r hr
    rw [div_le_iff₀ hc]
    linarith [hr]
  have hmain := eventually_le_of_log_poly_bound hC hk hS' hT1 hTlog hTtop
    (ε := ε / c) (by positivity)
  filter_upwards [hmain] with r hr
  have : S r / c ≤ ε / c * T r := hr
  rw [div_le_iff₀ hc] at this
  have hcancel : ε / c * T r * c = ε * T r := by field_simp
  linarith [this, hcancel]

/-- **The counting conclusion along a sequence of radii.**  The Borel exceptional set has finite
measure, so the good radii form an unbounded set and the conclusion is reached along a sequence. -/
theorem le_four_of_characteristic_bound_seq {q : ℕ} {S T : ℝ → ℝ} {C : ℝ} {rn : ℕ → ℝ}
    (hbound : ∀ᶠ n in atTop, ((q : ℝ) / 2 - 2) * T (rn n) ≤ S (rn n) + C)
    (hS : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, S (rn n) ≤ ε * T (rn n))
    (hT : Tendsto (fun n => T (rn n)) atTop atTop) : q ≤ 4 := by
  by_contra hcon
  push_neg at hcon
  have hq : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hcon
  set c : ℝ := (q : ℝ) / 2 - 2 with hc
  have hcpos : 0 < c := by
    rw [hc]
    linarith
  have hTbig : ∀ᶠ n in atTop, 2 * |C| / c + 1 ≤ T (rn n) := hT.eventually_ge_atTop _
  have hev : ∀ᶠ n in atTop, (S (rn n) ≤ c / 2 * T (rn n) ∧ 2 * |C| / c + 1 ≤ T (rn n))
      ∧ c * T (rn n) ≤ S (rn n) + C := by
    filter_upwards [hS (c / 2) (by positivity), hTbig, hbound] with n h1 h2 h3
    exact ⟨⟨h1, h2⟩, h3⟩
  obtain ⟨n, ⟨hs, hTr⟩, hb⟩ := hev.exists
  have habs : (0 : ℝ) ≤ 2 * |C| / c := by positivity
  have hTr0 : (0 : ℝ) < T (rn n) := by linarith
  have hhalf : c / 2 * T (rn n) ≤ C := by linarith [hb, hs]
  have hCle : C ≤ |C| := le_abs_self C
  have hTle : T (rn n) ≤ 2 * |C| / c := by
    rw [le_div_iff₀ hcpos]
    linarith
  linarith [hTr, hTle]

end GaloisForLFunctions.HTGeometry
