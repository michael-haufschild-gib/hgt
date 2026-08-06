import GaloisForLFunctions.HTGeometry.PeriodicFrequentBound

/-!
# A factor tending to one leaves a root limsup unchanged

Multiplying a bounded non-negative sequence by a factor converging to one does
not change its `limsup`.  Both halves are a squeeze: above, the factor is
eventually below any `d > 1` and the sequence eventually below any bound above
its own `limsup`; below, the factor is eventually above any `e < 1` while the
sequence is frequently above any `f < limsup`.

This is the combination step of the independent cusp-constant computation.  The
shifted `L`-value splits into a geometric factor, a Gamma ratio, an `L`-value and
an oscillating factor; three of them have `k`-th roots converging to one and only
the oscillating factor has a genuine `limsup`, so they cannot simply be
multiplied together.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section UnitFactor

variable {a b : ℕ → ℝ}

/-- **A unit factor does not move a `limsup` of one.** -/
theorem limsup_mul_eq_one_of_tendsto_one
    (ha : Tendsto a atTop (𝓝 1)) (hbnn : ∀ k, 0 ≤ b k)
    (hbbdd : IsBoundedUnder (· ≤ ·) atTop b) (hb : limsup b atTop = 1) :
    limsup (fun k => a k * b k) atTop = 1 := by
  obtain ⟨B, hB⟩ := id hbbdd
  rw [Filter.eventually_map] at hB
  have haev : ∀ᶠ k in atTop, 0 ≤ a k :=
    (ha.eventually_const_lt (by norm_num : (0 : ℝ) < 1)).mono fun k h => h.le
  have hprodnn : ∀ᶠ k in atTop, 0 ≤ a k * b k :=
    haev.mono fun k h => mul_nonneg h (hbnn k)
  have hprodcob : IsCoboundedUnder (· ≤ ·) atTop (fun k => a k * b k) := by
    refine IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
    rw [Filter.eventually_map]
    exact hprodnn
  have hprodbdd : IsBoundedUnder (· ≤ ·) atTop (fun k => a k * b k) := by
    refine ⟨max B 0 * 2, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hB, haev,
      ha.eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with k hBk h0 h2
    calc a k * b k ≤ 2 * (max B 0) := by
          refine mul_le_mul h2.le (le_trans hBk (le_max_left _ _)) (hbnn k) (by norm_num)
      _ = max B 0 * 2 := by ring
  have hbcob : IsCoboundedUnder (· ≤ ·) atTop b := by
    refine IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
    rw [Filter.eventually_map]
    exact Filter.Eventually.of_forall hbnn
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hcon
    obtain ⟨d, hd1, hd2⟩ := exists_between hc1
    have hdpos : (0 : ℝ) < d := by linarith
    have hcd : (1 : ℝ) < c / d := by
      rw [lt_div_iff₀ hdpos]
      linarith
    have hbev : ∀ᶠ k in atTop, b k < c / d := by
      refine eventually_lt_of_limsup_lt ?_ hbbdd
      rw [hb]
      exact hcd
    have haev2 : ∀ᶠ k in atTop, a k < d := ha.eventually_lt_const hd1
    have hle : limsup (fun k => a k * b k) atTop ≤ c := by
      refine limsup_le_of_le hprodcob ?_
      filter_upwards [hbev, haev2, haev] with k hbk hak h0
      have : a k * b k < d * (c / d) := by
        refine mul_lt_mul' hak.le hbk (hbnn k) hdpos
      calc a k * b k ≤ d * (c / d) := this.le
        _ = c := by field_simp
    linarith
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hcon
    rcases le_or_gt c 0 with hc0 | hc0
    · have h0 : (0 : ℝ) ≤ limsup (fun k => a k * b k) atTop :=
        le_limsup_of_frequently_le hprodnn.frequently hprodbdd
      linarith
    · obtain ⟨e, he1, he2⟩ := exists_between hc2
      have hepos : (0 : ℝ) < e := by linarith
      have hcf : c / e < 1 := by
        rw [div_lt_one hepos]
        exact he1
      obtain ⟨f, hf1, hf2⟩ := exists_between hcf
      have haev3 : ∀ᶠ k in atTop, e < a k := ha.eventually_const_lt he2
      have hbfreq : ∃ᶠ k in atTop, f < b k := by
        refine frequently_lt_of_lt_limsup hbcob ?_
        rw [hb]
        exact hf2
      have hfreq : ∃ᶠ k in atTop, c ≤ a k * b k := by
        refine (hbfreq.and_eventually haev3).mono fun k hk => ?_
        have hfpos : (0 : ℝ) < f := lt_of_le_of_lt (by positivity) hf1
        have hak : (0 : ℝ) < a k := lt_trans hepos hk.2
        have hlt : e * f < a k * b k :=
          mul_lt_mul' hk.2.le hk.1 (le_of_lt hfpos) hak
        have hdiv := (div_lt_iff₀ hepos).mp hf1
        linarith [mul_comm e f]
      have := le_limsup_of_frequently_le hfreq hprodbdd
      linarith

end UnitFactor

section Transfer

/-- The root sequence of a coefficient family is non-negative, hence
cobounded above. -/
theorem isCoboundedUnder_root (c : ℕ → ℂ) :
    IsCoboundedUnder (· ≤ ·) atTop (fun k => ‖c k‖ ^ (1 / (k : ℝ))) := by
  refine IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards with k
  positivity

/-- **The growth functional is the extended-real image of the root `limsup`.** -/
theorem hadamardLimsup_eq_ofReal_limsup {c : ℕ → ℂ}
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k => ‖c k‖ ^ (1 / (k : ℝ)))) :
    hadamardLimsup c
      = ENNReal.ofReal (limsup (fun k => ‖c k‖ ^ (1 / (k : ℝ))) atTop) := by
  have hmono : Monotone ENNReal.ofReal := fun _ _ h => ENNReal.ofReal_le_ofReal h
  have hmap := hmono.map_limsup_of_continuousAt
    (fun k : ℕ => ‖c k‖ ^ (1 / (k : ℝ)))
    ENNReal.continuous_ofReal.continuousAt hbdd (isCoboundedUnder_root c)
  rw [hmap, hadamardLimsup]
  refine limsup_congr (Filter.Eventually.of_forall fun k => ?_)
  rw [Function.comp_apply, ENNReal.ofReal_eq_coe_nnreal (by positivity)]
  congr 1

/-- **The growth functional is one when the root `limsup` is one.** -/
theorem hadamardLimsup_eq_one_of_limsup_eq_one {c : ℕ → ℂ}
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k => ‖c k‖ ^ (1 / (k : ℝ))))
    (h : limsup (fun k => ‖c k‖ ^ (1 / (k : ℝ))) atTop = 1) :
    hadamardLimsup c = 1 := by
  rw [hadamardLimsup_eq_ofReal_limsup hbdd, h, ENNReal.ofReal_one]

end Transfer

end GaloisForLFunctions.HTGeometry
