import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheChainIsHilbertSchmidtAboveInverseRootTwo

/-!
# Short-interval sums of the damped divisor coefficients

The coefficients `c_η(m) = Σ_{d|m} μ(d) d^{−η}` lie in `[0, 1]` with mean `ρ_η`; their prefix
`A_η` has centred remainder `P_η = A_η − ρ_η x`.  On a short interval `(a', a]` of length `J`, the
trivial bound is `|P(a) − P(a')| ≤ J` and the sign-blind one is `≲ a^{1−η}`.  The divisor
structure of `c_η` gives a third, interpolating bound (`abs_centeredPrefix_sub_le_short`): for
every `J ≤ D ≤ a` with `2J ≤ a`,

`|P(a) − P(a')| ≤ C_η (D^{1−η} + J D^{−η} + a D^{−1−η})`.

In floor form `P(a) − P(a') = Σ_{d ≤ a} μ(d) d^{−η} (n_d − J/d) − J τ_a` (`centeredPrefix_sub_eq`),
`n_d` the number of multiples of `d` in `(a', a]`.  Divisors `d ≤ D` cost `≲ D^{1−η}`.  A divisor
`d > D ≥ J` has at most one multiple `d e` in the interval, with `e = ⌊a/d⌋ ≤ a/D`, and for fixed
`e` the possible `d` lie in `((a−J)/e, a/e]` (`fiber_card_le`): the large divisors cost
`≲ Σ_{e ≤ a/D} (J/e + 1)(e/a)^η ≲ J D^{−η} + a D^{−1−η}`.  The signs of `μ` are not used.
-/

open Finset RHTower ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- The constant of the short-interval bound. -/
def shortIntervalConstant (η : ℝ) : ℝ := 2 + 1 / (1 - η) + 5 / η

/-- The Möbius tail beyond `a`. -/
def moebiusTail (η : ℝ) (a : ℕ) : ℝ :=
  ∑' j : ℕ, (moebius (j + (a + 1)) : ℝ) * (((j + (a + 1) : ℕ) : ℝ)) ^ (-(1 + η))

/-- **Floor form of a short-interval sum**: with `J = a − a'`,
`P(a) − P(a') = Σ_{d ≤ a} μ(d) d^{−η}(⌊a/d⌋ − ⌊a'/d⌋ − J/d) − J τ_a`. -/
theorem centeredPrefix_sub_eq {η : ℝ} (h0 : 0 < η) {a a' : ℕ} (h : a' ≤ a) :
    pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a' =
      ∑ d ∈ Icc 1 a, (moebius d : ℝ) * (d : ℝ) ^ (-η) *
        (((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ) - ((a : ℝ) - a') / d) -
        ((a : ℝ) - a') * moebiusTail η a := by
  set f : ℕ → ℝ := fun d => (moebius d : ℝ) * (d : ℝ) ^ (-(1 + η)) with hfdef
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hfb : ∀ d, ‖f d‖ ≤ (d : ℝ) ^ (-(1 + η)) := fun d => by
    have hμ : |(moebius d : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    rw [Real.norm_eq_abs, hfdef, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) hμ
  have hfs : Summable f := Summable.of_norm_bounded (Real.summable_nat_rpow.2 (by linarith)) hfb
  have hρ : (pmPowerDampedDivisorDensity η).re = ∑ d ∈ Icc 1 a, f d + moebiusTail η a := by
    rw [density_re_eq_tsum h0, ← hfs.sum_add_tsum_nat_add (a + 1)]
    congr 1
    rw [range_eq_Ico, show Ico 0 (a + 1) = insert 0 (Icc 1 a) by
      ext d; simp only [mem_Ico, mem_insert, mem_Icc]; omega, sum_insert (by simp), hf0, zero_add]
  -- extend the lower floor sum to `[1, a]`
  have hext : ∑ d ∈ Icc 1 a', (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((a' / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 a, (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((a' / d : ℕ) : ℝ) := by
    refine sum_subset (Icc_subset_Icc_right h) fun d hd hd' => ?_
    have : a' < d := by simp only [mem_Icc] at hd hd'; omega
    rw [Nat.div_eq_of_lt this]; simp
  have hhead : ∀ d ∈ Icc 1 a, f d * ((a : ℝ) - a') =
      (moebius d : ℝ) * (d : ℝ) ^ (-η) * (((a : ℝ) - a') / d) := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by have := (mem_Icc.1 hd).1; positivity
    simp only [hfdef]
    rw [show -(1 + η) = -η - 1 by ring, Real.rpow_sub_one hd0]
    field_simp
  rw [pmPowerDampedCenteredDivisorPrefix_eq_floor_sum, pmPowerDampedCenteredDivisorPrefix_eq_floor_sum,
    hext, hρ]
  have e : (∑ d ∈ Icc 1 a, f d + moebiusTail η a) * a - (∑ d ∈ Icc 1 a, f d + moebiusTail η a) * a' =
      ∑ d ∈ Icc 1 a, f d * ((a : ℝ) - a') + ((a : ℝ) - a') * moebiusTail η a := by
    rw [← sum_mul]; ring
  have e2 : ∑ d ∈ Icc 1 a, (moebius d : ℝ) * (d : ℝ) ^ (-η) *
      (((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ) - ((a : ℝ) - a') / d) =
      ∑ d ∈ Icc 1 a, (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((a / d : ℕ) : ℝ) -
        ∑ d ∈ Icc 1 a, (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((a' / d : ℕ) : ℝ) -
        ∑ d ∈ Icc 1 a, f d * ((a : ℝ) - a') := by
    rw [sum_congr rfl hhead, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by ring
  rw [e2]
  linarith [e]

/-- `|⌊a/d⌋ − ⌊a'/d⌋ − (a − a')/d| ≤ 1`. -/
theorem abs_floorCount_sub_le (a a' d : ℕ) (hd : 0 < d) :
    |((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ) - ((a : ℝ) - a') / d| ≤ 1 := by
  have h1 := natDiv_le_div a d
  have h2 := natDiv_le_div a' d
  have h3 := abs_natDiv_sub_div_le a d hd
  have h4 := abs_natDiv_sub_div_le a' d hd
  rw [abs_le] at h3 h4 ⊢
  have e : ((a : ℝ) - a') / d = (a : ℝ) / d - (a' : ℝ) / d := sub_div _ _ _
  constructor <;> linarith [h3.1, h4.1]

/-- A divisor beyond the interval length has at most one multiple in the interval. -/
theorem floorCount_le_one {a a' d : ℕ} (h : a' ≤ a) (hd : a - a' < d) : a / d - a' / d ≤ 1 := by
  have hd0 : 0 < d := by omega
  by_contra hcon
  push Not at hcon
  -- two multiples `d(q+1), d(q+2)` above `a'` and at most `a`
  have h1 : (a' / d + 2) * d ≤ a := by
    have := Nat.div_mul_le_self a d
    have h2 : a' / d + 2 ≤ a / d := by omega
    calc (a' / d + 2) * d ≤ a / d * d := Nat.mul_le_mul_right _ h2
      _ ≤ a := this
  have h3 : a' < (a' / d + 1) * d := by
    have := Nat.lt_div_mul_add (a := a') (b := d) hd0; nlinarith
  have h4 : (a' / d + 2) * d = (a' / d + 1) * d + d := by ring
  omega

/-- **The fiber of a quotient**: the divisors `d` with `⌊a/d⌋ = e` and a multiple in `(a', a]`
lie in `(⌊a'/e⌋, ⌊a/e⌋]`. -/
theorem fiber_subset {a a' e : ℕ} (he : 0 < e) :
    ((Icc 1 a).filter fun d => a' / d < a / d ∧ a / d = e) ⊆ Ioc (a' / e) (a / e) := by
  intro d hd
  simp only [mem_filter, mem_Icc] at hd
  obtain ⟨⟨hd1, -⟩, hlt, hq⟩ := hd
  simp only [mem_Ioc]
  constructor
  · -- `a' < d e`
    rw [Nat.div_lt_iff_lt_mul he]
    have : a' / d < e := hq ▸ hlt
    have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).1 this
    linarith [mul_comm d e]
  · rw [Nat.le_div_iff_mul_le he]
    have := Nat.div_mul_le_self a d
    rw [hq] at this
    linarith [mul_comm d e]

/-- The fiber has at most `J/e + 1` elements. -/
theorem fiber_card_le {a a' e : ℕ} (he : 0 < e) (h : a' ≤ a) :
    (((Icc 1 a).filter fun d => a' / d < a / d ∧ a / d = e).card : ℝ) ≤ ((a : ℝ) - a') / e + 1 := by
  have hc := card_le_card (fiber_subset (a := a) (a' := a') he)
  rw [Nat.card_Ioc] at hc
  have hle : a' / e ≤ a / e := Nat.div_le_div_right h
  have h1 := abs_floorCount_sub_le a a' e he
  rw [abs_le] at h1
  have hcast : ((a / e - a' / e : ℕ) : ℝ) = ((a / e : ℕ) : ℝ) - ((a' / e : ℕ) : ℝ) := by
    push_cast [hle]; ring
  calc (((Icc 1 a).filter fun d => a' / d < a / d ∧ a / d = e).card : ℝ)
      ≤ ((a / e - a' / e : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ _ := by rw [hcast]; linarith [h1.2]

/-- `(a/(2e))^{−η} = (2/a)^η e^η`. -/
theorem half_quotient_rpow_eq {a e η : ℝ} (ha : 0 < a) (he : 0 < e) :
    (a / (2 * e)) ^ (-η) = (2 / a) ^ η * e ^ η := by
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div,
    show 2 * e / a = 2 / a * e by ring, Real.mul_rpow (by positivity) he.le]

/-- **Large divisors**: `Σ_{D < d ≤ a, d | (a', a]} d^{−η} ≤ 2((1 + 1/η) J D^{−η} + a D^{−(1+η)})`. -/
theorem sum_large_divisors_le {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {a a' : ℕ} (h : a' ≤ a)
    (h2 : 2 * (a - a') ≤ a) {D : ℝ} (hD1 : 1 ≤ D) (hDa : D ≤ a) :
    ∑ d ∈ (Icc 1 a).filter (fun d : ℕ => D < d ∧ a' / d < a / d), (d : ℝ) ^ (-η) ≤
      2 * ((1 + 1 / η) * ((a : ℝ) - a') * D ^ (-η) + a * D ^ (-(1 + η))) := by
  have ha : (0 : ℝ) < a := by linarith
  have hD0 : 0 < D := by linarith
  set E := ⌊(a : ℝ) / D⌋₊ with hEdef
  have hE1 : 1 ≤ E := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hD0, one_mul]; exact hDa)
  have hEle : (E : ℝ) ≤ a / D := Nat.floor_le (by positivity)
  have hJ0 : (0 : ℝ) ≤ (a : ℝ) - a' := by
    have : (a' : ℝ) ≤ a := by exact_mod_cast h
    linarith
  have ha' : (a : ℝ) / 2 ≤ a' := by
    have : ((2 * (a - a') : ℕ) : ℝ) ≤ a := by exact_mod_cast h2
    push_cast [h] at this; linarith
  -- group by the quotient `e = ⌊a/d⌋`
  have hmaps : ∀ d ∈ (Icc 1 a).filter (fun d : ℕ => D < d ∧ a' / d < a / d), a / d ∈ Icc 1 E := by
    intro d hd
    simp only [mem_filter, mem_Icc] at hd
    obtain ⟨⟨hd1, -⟩, hDd, hlt⟩ := hd
    refine mem_Icc.2 ⟨by omega, Nat.le_floor ?_⟩
    calc ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := natDiv_le_div a d
      _ ≤ (a : ℝ) / D := div_le_div_of_nonneg_left ha.le hD0 hDd.le
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ e ∈ Icc 1 E, ∑ d ∈ ((Icc 1 a).filter (fun d : ℕ => D < d ∧ a' / d < a / d)).filter
      (fun d => a / d = e), (d : ℝ) ^ (-η) ≤
      (((a : ℝ) - a') / e + 1) * ((2 / a) ^ η * (e : ℝ) ^ η) := by
    intro e he
    have he0 : 0 < e := (mem_Icc.1 he).1
    have he0' : (0 : ℝ) < e := by exact_mod_cast he0
    set F := ((Icc 1 a).filter (fun d : ℕ => D < d ∧ a' / d < a / d)).filter (fun d => a / d = e)
    have hsub : F ⊆ (Icc 1 a).filter fun d => a' / d < a / d ∧ a / d = e := by
      intro d hd
      simp only [F, mem_filter] at hd ⊢
      exact ⟨hd.1.1, hd.1.2.2, hd.2⟩
    have hcard : (F.card : ℝ) ≤ ((a : ℝ) - a') / e + 1 :=
      le_trans (by exact_mod_cast card_le_card hsub) (fiber_card_le he0 h)
    -- each member is at least `a/(2e)`
    have hterm : ∀ d ∈ F, (d : ℝ) ^ (-η) ≤ (2 / a) ^ η * (e : ℝ) ^ η := by
      intro d hd
      have hd' := fiber_subset (a := a) (a' := a') he0 (hsub hd)
      simp only [mem_Ioc] at hd'
      have hlt : a' < d * e := (Nat.div_lt_iff_lt_mul he0).1 hd'.1
      have hde : (a : ℝ) / (2 * e) ≤ d := by
        rw [div_le_iff₀ (by positivity)]
        have : (a' : ℝ) + 1 ≤ (d : ℝ) * e := by exact_mod_cast hlt
        nlinarith
      rw [← half_quotient_rpow_eq ha he0']
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hde (by linarith)
    calc ∑ d ∈ F, (d : ℝ) ^ (-η) ≤ ∑ _d ∈ F, (2 / a) ^ η * (e : ℝ) ^ η := sum_le_sum hterm
      _ = (F.card : ℝ) * ((2 / a) ^ η * (e : ℝ) ^ η) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  refine (sum_le_sum hfib).trans ?_
  -- sum over the quotients
  have hsplit : ∑ e ∈ Icc 1 E, (((a : ℝ) - a') / e + 1) * ((2 / a) ^ η * (e : ℝ) ^ η) =
      (2 / a) ^ η * (((a : ℝ) - a') * ∑ e ∈ Icc 1 E, (e : ℝ) ^ (-(1 - η)) +
        ∑ e ∈ Icc 1 E, (e : ℝ) ^ η) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun e he => ?_
    have he0' : (0 : ℝ) < e := by have := (mem_Icc.1 he).1; exact_mod_cast this
    have : (e : ℝ) ^ η / e = (e : ℝ) ^ (-(1 - η)) := by
      rw [← Real.rpow_sub_one he0'.ne']; ring_nf
    rw [← this]; field_simp; ring
  rw [hsplit]
  have hhead := RHTower.sum_rpow_neg_head_le (c := 1 - η) (by linarith) (by linarith) E
  rw [show 1 - (1 - η) = η by ring] at hhead
  have hEη : 1 ≤ (E : ℝ) ^ η := Real.one_le_rpow (by exact_mod_cast hE1) h0.le
  have hpow : ∑ e ∈ Icc 1 E, (e : ℝ) ^ η ≤ (E : ℝ) * (E : ℝ) ^ η := by
    calc ∑ e ∈ Icc 1 E, (e : ℝ) ^ η ≤ ∑ _e ∈ Icc 1 E, (E : ℝ) ^ η :=
          sum_le_sum fun e he => Real.rpow_le_rpow (Nat.cast_nonneg _)
            (by exact_mod_cast (mem_Icc.1 he).2) h0.le
      _ = _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have hEa : (E : ℝ) ^ η ≤ (a / D) ^ η := Real.rpow_le_rpow (Nat.cast_nonneg _) hEle h0.le
  have hEa1 : (E : ℝ) * (E : ℝ) ^ η ≤ a / D * (a / D) ^ η :=
    mul_le_mul hEle hEa (by positivity) (by positivity)
  have hhead' : ∑ e ∈ Icc 1 E, (e : ℝ) ^ (-(1 - η)) ≤ (1 + 1 / η) * (a / D) ^ η := by
    have : 1 + (E : ℝ) ^ η / η ≤ (1 + 1 / η) * (E : ℝ) ^ η := by
      rw [add_mul, one_mul, div_eq_mul_one_div, mul_comm ((E : ℝ) ^ η)]; linarith
    calc _ ≤ 1 + (E : ℝ) ^ η / η := hhead
      _ ≤ (1 + 1 / η) * (E : ℝ) ^ η := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hEa (by positivity)
  have h2η : (2 : ℝ) ^ η ≤ 2 := by
    calc (2 : ℝ) ^ η ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
      _ = 2 := Real.rpow_one 2
  have e1 : (2 / a) ^ η * (a / D) ^ η = 2 ^ η * D ^ (-η) := by
    rw [← Real.mul_rpow (by positivity) (by positivity), show 2 / (a : ℝ) * (a / D) = 2 / D by
      field_simp, Real.div_rpow (by norm_num) hD0.le, Real.rpow_neg hD0.le, div_eq_mul_inv]
  have e2 : (2 / a) ^ η * (a / D * (a / D) ^ η) = 2 ^ η * (a * D ^ (-(1 + η))) := by
    rw [mul_left_comm, e1, show -(1 + η) = -η - 1 by ring, Real.rpow_sub_one hD0.ne']
    field_simp
  have hc : 0 ≤ (2 / (a : ℝ)) ^ η := by positivity
  calc (2 / a) ^ η * (((a : ℝ) - a') * ∑ e ∈ Icc 1 E, (e : ℝ) ^ (-(1 - η)) +
        ∑ e ∈ Icc 1 E, (e : ℝ) ^ η)
      ≤ (2 / a) ^ η * (((a : ℝ) - a') * ((1 + 1 / η) * (a / D) ^ η) + a / D * (a / D) ^ η) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hhead' hJ0)
          (hpow.trans hEa1)) hc
    _ = 2 ^ η * ((1 + 1 / η) * ((a : ℝ) - a') * D ^ (-η)) + 2 ^ η * (a * D ^ (-(1 + η))) := by
        rw [mul_add, ← e2, ← e1]; ring
    _ ≤ 2 * ((1 + 1 / η) * ((a : ℝ) - a') * D ^ (-η)) + 2 * (a * D ^ (-(1 + η))) := by
        have h3 : 0 ≤ (1 + 1 / η) * ((a : ℝ) - a') * D ^ (-η) := by positivity
        have h4 : 0 ≤ (a : ℝ) * D ^ (-(1 + η)) := by positivity
        nlinarith
    _ = _ := by ring

/-! ### Tails -/

/-- The shifted `p`-series beyond `q` is summable. -/
theorem summable_rpow_shift {η : ℝ} (hη : 0 < η) (q : ℕ) :
    Summable fun j : ℕ => ((j + q + 1 : ℕ) : ℝ) ^ (-(1 + η)) := by
  have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(1 + η))) (q + 1)).2
    (Real.summable_nat_rpow.2 (by linarith))
  simpa only [Nat.add_assoc] using this

/-- `Σ_{q < d ≤ a} d^{−(1+η)} ≤ q^{−η}/η`. -/
theorem sum_Ioc_rpow_le {η : ℝ} (hη : 0 < η) {q : ℕ} (hq : 1 ≤ q) (a : ℕ) :
    ∑ d ∈ Ioc q a, (d : ℝ) ^ (-(1 + η)) ≤ (q : ℝ) ^ (-η) / η := by
  have e : ∑ d ∈ Ioc q a, (d : ℝ) ^ (-(1 + η)) =
      ∑ j ∈ range (a - q), ((j + q + 1 : ℕ) : ℝ) ^ (-(1 + η)) := by
    rw [show Ioc q a = Ico (q + 1) (a + 1) by ext d; simp only [mem_Ioc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, show a + 1 - (q + 1) = a - q by omega]
    exact sum_congr rfl fun j _ => by rw [show q + 1 + j = j + q + 1 by omega]
  rw [e]
  exact ((summable_rpow_shift hη q).sum_le_tsum _
    fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (tsum_rpow_tail_le hη hq)

/-- `|τ_a| ≤ a^{−η}/η`. -/
theorem abs_moebiusTail_le {η : ℝ} (hη : 0 < η) {a : ℕ} (ha : 1 ≤ a) :
    |moebiusTail η a| ≤ (a : ℝ) ^ (-η) / η := by
  have hs : Summable fun j : ℕ => (((j + (a + 1) : ℕ) : ℝ)) ^ (-(1 + η)) := by
    simpa only [Nat.add_assoc] using summable_rpow_shift hη a
  have ht : ∑' j : ℕ, (((j + (a + 1) : ℕ) : ℝ)) ^ (-(1 + η)) ≤ (a : ℝ) ^ (-η) / η := by
    simpa only [Nat.add_assoc] using tsum_rpow_tail_le hη ha
  have hb : ∀ j : ℕ, ‖(moebius (j + (a + 1)) : ℝ) * (((j + (a + 1) : ℕ) : ℝ)) ^ (-(1 + η))‖ ≤
      (((j + (a + 1) : ℕ) : ℝ)) ^ (-(1 + η)) := fun j => by
    have hμ : |(moebius (j + (a + 1)) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hμ
  rw [← Real.norm_eq_abs, moebiusTail]
  exact (tsum_of_norm_bounded hs.hasSum hb).trans ht

/-- `⌊D⌋^{−η} ≤ 2 D^{−η}` for `D ≥ 1`, `0 ≤ η ≤ 1`. -/
theorem floor_rpow_neg_le {D η : ℝ} (hD1 : 1 ≤ D) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    (⌊D⌋₊ : ℝ) ^ (-η) ≤ 2 * D ^ (-η) := by
  have hfl1 : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hD1)
  have hfl : (1 : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast hfl1
  have hlt := Nat.lt_floor_add_one D
  have h2η : (2 : ℝ) ^ η ≤ 2 := by
    calc (2 : ℝ) ^ η ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 := Real.rpow_one 2
  calc (⌊D⌋₊ : ℝ) ^ (-η) ≤ (D / 2) ^ (-η) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    _ = 2 ^ η * D ^ (-η) := by
        rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
    _ ≤ 2 * D ^ (-η) := mul_le_mul_of_nonneg_right h2η (by positivity)

/-! ### The floor terms -/

/-- The `d`-th term of the floor form. -/
def floorTerm (η : ℝ) (a a' d : ℕ) : ℝ :=
  (moebius d : ℝ) * (d : ℝ) ^ (-η) * (((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ) - ((a : ℝ) - a') / d)

/-- **Small divisors**: `Σ_{d ≤ D} |term_d| ≤ (1 + 1/(1−η)) D^{1−η}`. -/
theorem sum_small_floorTerm_le {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (a a' : ℕ) {D : ℝ}
    (hD1 : 1 ≤ D) :
    ∑ d ∈ (Icc 1 a).filter (fun d : ℕ => (d : ℝ) ≤ D), |floorTerm η a a' d| ≤
      (1 + 1 / (1 - η)) * D ^ (1 - η) := by
  have hterm : ∀ d ∈ (Icc 1 a).filter (fun d : ℕ => (d : ℝ) ≤ D),
      |floorTerm η a a' d| ≤ (d : ℝ) ^ (-η) := by
    intro d hd
    have hd0 : 0 < d := (mem_Icc.1 (mem_filter.1 hd).1).1
    have hμ : |(moebius d : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    have hc := abs_floorCount_sub_le a a' d hd0
    rw [floorTerm, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    calc |(moebius d : ℝ)| * (d : ℝ) ^ (-η) *
          |((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ) - ((a : ℝ) - a') / d|
        ≤ 1 * (d : ℝ) ^ (-η) * 1 := by gcongr
      _ = _ := by ring
  have hsub : (Icc 1 a).filter (fun d : ℕ => (d : ℝ) ≤ D) ⊆ Icc 1 ⌊D⌋₊ := by
    intro d hd
    simp only [mem_filter, mem_Icc] at hd
    exact mem_Icc.2 ⟨hd.1.1, Nat.le_floor hd.2⟩
  have hfl : (⌊D⌋₊ : ℝ) ^ (1 - η) ≤ D ^ (1 - η) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by linarith)
  have hD : 1 ≤ D ^ (1 - η) := Real.one_le_rpow hD1 (by linarith)
  have hv : 0 ≤ 1 / (1 - η) := div_nonneg zero_le_one (by linarith)
  calc _ ≤ ∑ d ∈ (Icc 1 a).filter (fun d : ℕ => (d : ℝ) ≤ D), (d : ℝ) ^ (-η) := sum_le_sum hterm
    _ ≤ ∑ d ∈ Icc 1 ⌊D⌋₊, (d : ℝ) ^ (-η) :=
        sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => Real.rpow_nonneg (Nat.cast_nonneg d) _
    _ ≤ 1 + (⌊D⌋₊ : ℝ) ^ (1 - η) / (1 - η) := RHTower.sum_rpow_neg_head_le h0 h1 ⌊D⌋₊
    _ ≤ (1 + 1 / (1 - η)) * D ^ (1 - η) := by
        have e : (⌊D⌋₊ : ℝ) ^ (1 - η) / (1 - η) = (⌊D⌋₊ : ℝ) ^ (1 - η) * (1 / (1 - η)) :=
          div_eq_mul_one_div _ _
        have := mul_le_mul_of_nonneg_right hfl hv
        rw [e]; nlinarith

/-- A divisor `d > J` costs `d^{−η}` if it has a multiple in `(a', a]`, plus `J d^{−(1+η)}`. -/
theorem abs_floorTerm_le_large {η : ℝ} {a a' d : ℕ} (h : a' ≤ a) (hd : a - a' < d) :
    |floorTerm η a a' d| ≤
      (if a' / d < a / d then (d : ℝ) ^ (-η) else 0) + ((a : ℝ) - a') * (d : ℝ) ^ (-(1 + η)) := by
  have hd0 : (0 : ℝ) < d := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hJ0 : (0 : ℝ) ≤ ((a : ℝ) - a') / d := by
    have : (a' : ℝ) ≤ a := by exact_mod_cast h
    exact div_nonneg (by linarith) hd0.le
  have hμ : |(moebius d : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  have hle1 := floorCount_le_one h hd
  have hmono : a' / d ≤ a / d := Nat.div_le_div_right h
  have hpow : (d : ℝ) ^ (-η) * (((a : ℝ) - a') / d) = ((a : ℝ) - a') * (d : ℝ) ^ (-(1 + η)) := by
    rw [show -(1 + η) = -η - 1 by ring, Real.rpow_sub_one hd0.ne']
    ring
  rw [floorTerm, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  split_ifs with hlt
  · have hn : ((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ) = 1 := by
      rw [show a / d = a' / d + 1 by omega]; push_cast; ring
    rw [hn]
    calc |(moebius d : ℝ)| * (d : ℝ) ^ (-η) * |1 - ((a : ℝ) - a') / d|
        ≤ 1 * (d : ℝ) ^ (-η) * (1 + ((a : ℝ) - a') / d) := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ = _ := by rw [← hpow]; ring
  · have hn : ((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ) = 0 := by
      rw [show a / d = a' / d by omega, sub_self]
    rw [hn, zero_sub, abs_neg, abs_of_nonneg hJ0, zero_add, ← hpow]
    calc |(moebius d : ℝ)| * (d : ℝ) ^ (-η) * (((a : ℝ) - a') / d)
        ≤ 1 * (d : ℝ) ^ (-η) * (((a : ℝ) - a') / d) := by gcongr
      _ = _ := by ring

/-- **Large divisors in floor form**:
`Σ_{D < d ≤ a} |term_d| ≤ 2((1 + 1/η) J D^{−η} + a D^{−(1+η)}) + J · 2D^{−η}/η`. -/
theorem sum_large_floorTerm_le {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {a a' : ℕ} (h : a' ≤ a)
    (h2 : 2 * (a - a') ≤ a) {D : ℝ} (hD1 : 1 ≤ D) (hJD : (a : ℝ) - a' ≤ D) (hDa : D ≤ a) :
    ∑ d ∈ (Icc 1 a).filter (fun d : ℕ => ¬ (d : ℝ) ≤ D), |floorTerm η a a' d| ≤
      2 * ((1 + 1 / η) * ((a : ℝ) - a') * D ^ (-η) + a * D ^ (-(1 + η))) +
        ((a : ℝ) - a') * (2 * D ^ (-η) / η) := by
  set S := (Icc 1 a).filter (fun d : ℕ => ¬ (d : ℝ) ≤ D) with hSdef
  have hterm : ∀ d ∈ S, |floorTerm η a a' d| ≤
      (if a' / d < a / d then (d : ℝ) ^ (-η) else 0) + ((a : ℝ) - a') * (d : ℝ) ^ (-(1 + η)) := by
    intro d hd
    simp only [hSdef, mem_filter, not_le] at hd
    refine abs_floorTerm_le_large h ?_
    have : ((a - a' : ℕ) : ℝ) < d := by push_cast [h]; linarith [hd.2]
    exact_mod_cast this
  have hfilt : S.filter (fun d => a' / d < a / d) =
      (Icc 1 a).filter (fun d : ℕ => D < d ∧ a' / d < a / d) := by
    rw [hSdef, filter_filter]
    exact filter_congr fun d _ => by simp only [not_le]
  have hsubI : S ⊆ Ioc ⌊D⌋₊ a := by
    intro d hd
    simp only [hSdef, mem_filter, mem_Icc, not_le] at hd
    exact mem_Ioc.2 ⟨(Nat.floor_lt (by linarith)).2 hd.2, hd.1.2⟩
  have hfl1 : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hD1)
  have hJ0 : (0 : ℝ) ≤ (a : ℝ) - a' := by
    have : (a' : ℝ) ≤ a := by exact_mod_cast h
    linarith
  have htail : ∑ d ∈ S, (d : ℝ) ^ (-(1 + η)) ≤ 2 * D ^ (-η) / η :=
    calc ∑ d ∈ S, (d : ℝ) ^ (-(1 + η)) ≤ ∑ d ∈ Ioc ⌊D⌋₊ a, (d : ℝ) ^ (-(1 + η)) :=
          sum_le_sum_of_subset_of_nonneg hsubI fun d _ _ => Real.rpow_nonneg (Nat.cast_nonneg d) _
      _ ≤ (⌊D⌋₊ : ℝ) ^ (-η) / η := sum_Ioc_rpow_le h0 hfl1 a
      _ ≤ 2 * D ^ (-η) / η :=
          div_le_div_of_nonneg_right (floor_rpow_neg_le hD1 h0.le h1.le) h0.le
  calc ∑ d ∈ S, |floorTerm η a a' d|
      ≤ ∑ d ∈ S, ((if a' / d < a / d then (d : ℝ) ^ (-η) else 0) +
          ((a : ℝ) - a') * (d : ℝ) ^ (-(1 + η))) := sum_le_sum hterm
    _ = ∑ d ∈ (Icc 1 a).filter (fun d : ℕ => D < d ∧ a' / d < a / d), (d : ℝ) ^ (-η) +
          ((a : ℝ) - a') * ∑ d ∈ S, (d : ℝ) ^ (-(1 + η)) := by
        rw [sum_add_distrib, ← sum_filter, hfilt, mul_sum]
    _ ≤ _ := add_le_add (sum_large_divisors_le h0 h1 h h2 hD1 hDa)
        (mul_le_mul_of_nonneg_left htail hJ0)

/-- The bookkeeping of the constants. -/
theorem short_combine {X J E Z u v : ℝ} (hX : 0 ≤ X) (hJ : 0 ≤ J) (hE : 0 ≤ E) (hZ : 0 ≤ Z)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (1 + v) * X + (2 * ((1 + u) * J * E + Z) + J * (2 * E * u)) + J * (E * u) ≤
      (2 + v + 5 * u) * (X + J * E + Z) := by
  nlinarith [mul_nonneg hu hX, mul_nonneg hv (mul_nonneg hJ hE), mul_nonneg hu hZ,
    mul_nonneg hv hZ, mul_nonneg hu (mul_nonneg hJ hE)]

/-- **Short-interval bound**: for `J = a − a'` with `2J ≤ a` and `J ≤ D ≤ a`, `D ≥ 1`,
`|P_η(a) − P_η(a')| ≤ C_η (D^{1−η} + J D^{−η} + a D^{−(1+η)})`. -/
theorem abs_centeredPrefix_sub_le_short {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {a a' : ℕ}
    (h : a' ≤ a) (h2 : 2 * (a - a') ≤ a) {D : ℝ} (hD1 : 1 ≤ D) (hJD : (a : ℝ) - a' ≤ D)
    (hDa : D ≤ a) :
    |pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a'| ≤
      shortIntervalConstant η *
        (D ^ (1 - η) + ((a : ℝ) - a') * D ^ (-η) + a * D ^ (-(1 + η))) := by
  have hD0 : 0 < D := by linarith
  have ha1 : 1 ≤ a := by exact_mod_cast hD1.trans hDa
  have hJ0 : (0 : ℝ) ≤ (a : ℝ) - a' := by
    have : (a' : ℝ) ≤ a := by exact_mod_cast h
    linarith
  rw [centeredPrefix_sub_eq h0 h]
  change |∑ d ∈ Icc 1 a, floorTerm η a a' d - _| ≤ _
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 a) (fun d : ℕ => (d : ℝ) ≤ D)
    (fun d => |floorTerm η a a' d|)
  have hS := sum_small_floorTerm_le h0 h1 a a' hD1
  have hL := sum_large_floorTerm_le h0 h1 h h2 hD1 hJD hDa
  have hT : |((a : ℝ) - a') * moebiusTail η a| ≤ ((a : ℝ) - a') * (D ^ (-η) / η) := by
    rw [abs_mul, abs_of_nonneg hJ0]
    refine mul_le_mul_of_nonneg_left ((abs_moebiusTail_le h0 ha1).trans ?_) hJ0
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hD0 hDa (by linarith)) h0.le
  have hfin := short_combine (X := D ^ (1 - η)) (J := (a : ℝ) - a') (E := D ^ (-η))
    (Z := (a : ℝ) * D ^ (-(1 + η))) (u := 1 / η) (v := 1 / (1 - η)) (by positivity) hJ0
    (by positivity) (by positivity) (div_nonneg zero_le_one h0.le)
    (div_nonneg zero_le_one (by linarith))
  have e1 : 2 * D ^ (-η) / η = 2 * D ^ (-η) * (1 / η) := by ring
  have e2 : D ^ (-η) / η = D ^ (-η) * (1 / η) := by ring
  have e3 : shortIntervalConstant η = 2 + 1 / (1 - η) + 5 * (1 / η) := by
    unfold shortIntervalConstant; ring
  rw [e1] at hL
  rw [e2] at hT
  rw [e3]
  calc |∑ d ∈ Icc 1 a, floorTerm η a a' d - ((a : ℝ) - a') * moebiusTail η a|
      ≤ |∑ d ∈ Icc 1 a, floorTerm η a a' d| + |((a : ℝ) - a') * moebiusTail η a| := abs_sub _ _
    _ ≤ (∑ d ∈ (Icc 1 a).filter (fun d : ℕ => (d : ℝ) ≤ D), |floorTerm η a a' d| +
          ∑ d ∈ (Icc 1 a).filter (fun d : ℕ => ¬ (d : ℝ) ≤ D), |floorTerm η a a' d|) +
          |((a : ℝ) - a') * moebiusTail η a| := by
        rw [hsplit]; exact add_le_add_right (abs_sum_le_sum_abs _ _) _
    _ ≤ _ := (add_le_add (add_le_add hS hL) hT).trans hfin

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
