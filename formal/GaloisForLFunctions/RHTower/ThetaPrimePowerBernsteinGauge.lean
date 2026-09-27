import GaloisForLFunctions.RHTower.ThetaTranslationGaugeFlux

/-!
# Bernstein flux rigidity of symmetric prime-power theta gauges

For `p ≥ 2` and real `c : ℤ → ℝ` with `∑ |c_j| p^{|j|/2} < ∞`, consider the two-sided gauge
`g = ∑_j c_j k(· + j log p)` of the completed theta source `k`, with ordinary multiplier
`M₀ = ∑ c_j` and critical multiplier `M_{1/2} = ∑ c_j p^{j/2}`.

* **Valuation-prefix cone.**  The flux `b_g` is completely monotone iff every prefix
  `A_v = ∑_{j ≤ v} c_j p^{j/2}` is nonnegative.
* **Charge-gap identity.**  For symmetric `c`, `M_{1/2} - M₀ = ∑_{m ≥ 1} Q_m (F_m - F_{m-1})`
  with `Q_m = A_{-m} = ∑_{j ≥ m} c_j p^{-j/2}` and `F_m = (p^{m/2} - 1)²`; all increments are
  positive, so complete monotonicity forces `M_{1/2} ≥ M₀`, with equality iff `c_j = 0` for
  `j ≠ 0`.
* **Two-anchor rigidity.**  Complete monotonicity, `∫ g = ∫ k` and `∫ e^{x/2} g = ∫ e^{x/2} k`
  force `g = k`.
* **Quantitative stability.**  With `a = √p`, `C_p = (a² + 1)/(a - 1)²` and `Δ = M_{1/2} - M₀`:
  `|c_m| ≤ C_p Δ a^{-m}`, `‖M(w) - M₀‖ ≤ B_{p,σ} Δ` on `|Re w| ≤ σ < 1/2` at all heights,
  no new Mellin zeros when `M₀ = 1` and `B_{p,σ} Δ < 1`, and `‖g - M₀ k‖₁ ≤ 4 C_p Δ ‖k‖₁/(a - 1)`.
* **Signed example.**  `c₀ = 1`, `c_{±2} = ε`, `c_{±1} = -ε/(2√p)`, `0 < ε < 1`, has completely
  monotone flux and strictly positive charge gap.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-! ## Prime-power shifts -/

/-- The prime-power shift `j log p`. -/
noncomputable def primePowerShift (p : ℕ) (j : ℤ) : ℝ := j * Real.log p

theorem exp_primePowerShift {p : ℕ} (hp : 0 < p) (j : ℤ) :
    Real.exp (primePowerShift p j) = (p : ℝ) ^ j := by
  unfold primePowerShift
  rw [mul_comm, ← Real.rpow_def_of_pos (by exact_mod_cast hp), Real.rpow_intCast]

theorem exp_half_primePowerShift {p : ℕ} (hp : 0 < p) (j : ℤ) :
    Real.exp (primePowerShift p j / 2) = Real.sqrt p ^ j := by
  unfold primePowerShift
  rw [show (j : ℝ) * Real.log p / 2 = Real.log (Real.sqrt p) * j by
      rw [Real.log_sqrt (Nat.cast_nonneg _)]; ring,
    ← Real.rpow_def_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hp)), Real.rpow_intCast]

theorem exp_abs_half_primePowerShift {p : ℕ} (hp : 1 ≤ p) (j : ℤ) :
    Real.exp (|primePowerShift p j| / 2) = Real.sqrt p ^ j.natAbs := by
  unfold primePowerShift
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  rw [abs_mul, abs_of_nonneg hl, show |(j : ℝ)| = (j.natAbs : ℝ) by
      rw [Nat.cast_natAbs, Int.cast_abs],
    show (j.natAbs : ℝ) * Real.log p / 2 = j.natAbs * Real.log (Real.sqrt p) by
      rw [Real.log_sqrt (Nat.cast_nonneg _)]; ring,
    Real.exp_nat_mul, Real.exp_log (Real.sqrt_pos.mpr (by exact_mod_cast hp))]

theorem primePower_gauge_admissible {p : ℕ} (hp : 1 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) :
    Summable fun j => |c j| * Real.exp (|primePowerShift p j| / 2) :=
  hc.congr fun j => by rw [exp_abs_half_primePowerShift hp]

/-- The valuation prefix `A_v = ∑_{j ≤ v} c_j p^{j/2}`. -/
noncomputable def primePowerPrefix (p : ℕ) (c : ℤ → ℝ) (v : ℤ) : ℝ :=
  ∑' j : ℤ, if j ≤ v then c j * Real.sqrt p ^ j else 0

/-- The negative-valuation tail `Q_m = ∑_{j ≥ m} c_j p^{-j/2}`. -/
noncomputable def primePowerTail (p : ℕ) (c : ℤ → ℝ) (m : ℤ) : ℝ :=
  ∑' j : ℤ, if m ≤ j then c j * Real.sqrt p ^ (-j) else 0

/-! ## Valuation chains -/

theorem primePower_reach_down {p : ℕ} (hp : 0 < p) {r : ℝ} {j j' : ℤ}
    (hj : ∃ n : ℕ, (n : ℝ) * (p : ℝ) ^ j = r) (h : j' ≤ j) :
    ∃ n : ℕ, (n : ℝ) * (p : ℝ) ^ j' = r := by
  obtain ⟨n, hn⟩ := hj
  refine ⟨n * p ^ (j - j').toNat, ?_⟩
  push_cast
  rw [← hn, mul_assoc, ← zpow_natCast, ← zpow_add₀ (by positivity),
    Int.toNat_of_nonneg (by omega), sub_add_cancel]

theorem primePower_reach_bdd {p : ℕ} (hp : 2 ≤ p) {r : ℝ} (hr : 0 < r) :
    ∃ b : ℤ, ∀ j, (∃ n : ℕ, (n : ℝ) * (p : ℝ) ^ j = r) → j ≤ b := by
  refine ⟨⌈r⌉₊, fun j ⟨n, hn⟩ => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [Nat.cast_zero, zero_mul] at hn
      linarith
    · exact_mod_cast h
  have hpj : (p : ℝ) ^ j ≤ r := by
    rw [← hn]
    exact le_mul_of_one_le_left (zpow_pos (by positivity) j).le hn1
  rcases le_or_gt j 0 with hj | hj
  · exact hj.trans (Nat.cast_nonneg _)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj.le
    rw [zpow_natCast] at hpj
    have h1 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp) k
    have h3 : r ≤ ⌈r⌉₊ := Nat.le_ceil r
    have h4 : (k : ℝ) < ⌈r⌉₊ := by linarith
    have : k < ⌈r⌉₊ := by exact_mod_cast h4
    omega

theorem primePower_reach_pow {p : ℕ} (hp : 2 ≤ p) (v j : ℤ) :
    (∃ n : ℕ, (n : ℝ) * (p : ℝ) ^ j = (p : ℝ) ^ v) ↔ j ≤ v := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  constructor
  · rintro ⟨n, hn⟩
    have hn1 : (1 : ℝ) ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · rw [Nat.cast_zero, zero_mul] at hn
        exact absurd hn.symm (zpow_pos (by positivity) v).ne'
      · exact_mod_cast h
    have : (p : ℝ) ^ j ≤ (p : ℝ) ^ v := by
      rw [← hn]
      exact le_mul_of_one_le_left (zpow_pos (by positivity) j).le hn1
    exact (zpow_le_zpow_iff_right₀ hp1).mp this
  · intro h
    exact primePower_reach_down (by omega) ⟨1, by simp⟩ h

/-- **Valuation-prefix cone.**  For `p ≥ 2` and `∑ |c_j| p^{|j|/2} < ∞`, the flux of the
two-sided gauge `∑_j c_j k(· + j log p)` is completely monotone iff every valuation prefix
`A_v = ∑_{j ≤ v} c_j p^{j/2}` is nonnegative. -/
theorem completelyMonotoneOn_primePowerGauge_iff {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) :
    CompletelyMonotoneOn (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p))) ↔
      ∀ v : ℤ, 0 ≤ primePowerPrefix p c v := by
  classical
  have hp0 : 0 < p := by omega
  rw [completelyMonotoneOn_thetaNormalizedFlux_gauge_iff_rateCoeff
    (primePower_gauge_admissible (by omega) hc)]
  have hcoef : ∀ r, thetaGaugeRateCoeff c (primePowerShift p) r =
      ∑' j : ℤ, if (∃ n : ℕ, (n : ℝ) * (p : ℝ) ^ j = r) then c j * Real.sqrt p ^ j else 0 := by
    intro r
    unfold thetaGaugeRateCoeff
    refine tsum_congr fun j => ?_
    simp only [exp_primePowerShift hp0, exp_half_primePowerShift hp0]
  constructor
  · intro h v
    have := h _ (zpow_pos (by positivity : (0 : ℝ) < p) v)
    rw [hcoef] at this
    unfold primePowerPrefix
    convert this using 1
    refine tsum_congr fun j => ?_
    by_cases hj : j ≤ v
    · rw [if_pos hj, if_pos ((primePower_reach_pow hp v j).mpr hj)]
    · rw [if_neg hj, if_neg (fun h' => hj ((primePower_reach_pow hp v j).mp h'))]
  · intro h r hr
    rw [hcoef]
    by_cases hne : ∃ j : ℤ, ∃ n : ℕ, (n : ℝ) * (p : ℝ) ^ j = r
    · obtain ⟨v, hv, hmax⟩ := Int.exists_greatest_of_bdd (primePower_reach_bdd hp hr) hne
      have hiff : ∀ j, (∃ n : ℕ, (n : ℝ) * (p : ℝ) ^ j = r) ↔ j ≤ v :=
        fun j => ⟨hmax j, fun hj => primePower_reach_down hp0 hv hj⟩
      have := h v
      unfold primePowerPrefix at this
      convert this using 1
      refine tsum_congr fun j => ?_
      by_cases hj : j ≤ v
      · rw [if_pos ((hiff j).mpr hj), if_pos hj]
      · rw [if_neg (fun h' => hj ((hiff j).mp h')), if_neg hj]
    · have hz : (∑' j : ℤ, if (∃ n : ℕ, (n : ℝ) * (p : ℝ) ^ j = r) then
          c j * Real.sqrt p ^ j else 0) = 0 := by
        refine (tsum_congr fun j => ?_).trans tsum_zero
        rw [if_neg]
        rintro ⟨n, hn⟩
        exact hne ⟨j, n, hn⟩
      rw [hz]

/-- For a symmetric sequence the negative-valuation prefix is the tail `Q_m`. -/
theorem primePowerPrefix_neg_eq_tail (p : ℕ) {c : ℤ → ℝ} (hsym : ∀ j, c (-j) = c j) (m : ℤ) :
    primePowerPrefix p c (-m) = primePowerTail p c m := by
  unfold primePowerPrefix primePowerTail
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.neg_apply, hsym, neg_le_neg_iff]

/-- **Tail positivity.**  Complete monotonicity forces every negative-valuation tail
`Q_m = ∑_{j ≥ m} c_j p^{-j/2}` to be nonnegative. -/
theorem primePowerTail_nonneg {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j)
    (hCM : CompletelyMonotoneOn (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p))))
    (m : ℤ) : 0 ≤ primePowerTail p c m := by
  rw [← primePowerPrefix_neg_eq_tail p hsym]
  exact (completelyMonotoneOn_primePowerGauge_iff hp hc).mp hCM (-m)

/-! ## The charge-gap identity -/

/-- A summable `ℤ`-series splits into its central term and symmetric pairs. -/
theorem tsum_int_eq_zero_add_pairs {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℤ → E} (hf : Summable f) :
    ∑' j, f j = f 0 + ∑' n : ℕ, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) := by
  have h1 : Summable fun n : ℕ => f n := hf.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ => f (-((n : ℤ) + 1)) :=
    hf.comp_injective (fun a b h => by simpa using h)
  have h1' : Summable fun n : ℕ => f ((n : ℤ) + 1) := by
    have := (summable_nat_add_iff 1).mpr h1
    simpa using this
  rw [tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add, h1'.tsum_add h2]
  push_cast
  abel

theorem summable_int_pairs {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℤ → E} (hf : Summable f) :
    Summable fun n : ℕ => f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)) :=
  (hf.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (fun a b h => by simpa using h)).add
    (hf.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (fun a b h => by simpa using h))

theorem summable_of_primePower {p : ℕ} (hp : 1 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (e : ℤ → ℤ)
    (he : ∀ j, |e j| ≤ |j|) : Summable fun j : ℤ => c j * Real.sqrt p ^ e j := by
  have ha : (1 : ℝ) ≤ Real.sqrt p := Real.one_le_sqrt.mpr (by exact_mod_cast hp)
  refine Summable.of_norm_bounded hc fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (zpow_pos (by linarith : (0 : ℝ) < Real.sqrt p) _)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← zpow_natCast, Int.natCast_natAbs]
  exact zpow_le_zpow_right₀ ha ((le_abs_self _).trans (he j))

/-- Ordinary multiplier `M₀ = ∑ c_j`. -/
noncomputable def primePowerGaugeMass (c : ℤ → ℝ) : ℝ := ∑' j, c j

/-- Critical multiplier `M_{1/2} = ∑ c_j p^{j/2}`. -/
noncomputable def primePowerGaugeCharge (p : ℕ) (c : ℤ → ℝ) : ℝ := ∑' j, c j * Real.sqrt p ^ j

/-- The Abel weights `F_m = (p^{m/2} - 1)²`. -/
noncomputable def primePowerAbelWeight (p m : ℕ) : ℝ := (Real.sqrt p ^ m - 1) ^ 2

theorem primePowerAbelWeight_zero (p : ℕ) : primePowerAbelWeight p 0 = 0 := by
  simp [primePowerAbelWeight]

/-- The Abel increments are bounded below: `F_{m+1} - F_m ≥ p^m (√p - 1)²`. -/
theorem primePowerAbelWeight_increment_ge {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    Real.sqrt p ^ (2 * m) * (Real.sqrt p - 1) ^ 2 ≤
      primePowerAbelWeight p (m + 1) - primePowerAbelWeight p m := by
  have ha : (1 : ℝ) ≤ Real.sqrt p := Real.one_le_sqrt.mpr (by exact_mod_cast hp)
  have hx : (1 : ℝ) ≤ Real.sqrt p ^ m := one_le_pow₀ ha
  unfold primePowerAbelWeight
  rw [pow_succ (Real.sqrt p) m, pow_mul']
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt p ^ m) (sub_nonneg.mpr ha))
    (sub_nonneg.mpr hx)]

theorem primePowerAbelWeight_increment_pos {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    0 < primePowerAbelWeight p (m + 1) - primePowerAbelWeight p m := by
  have ha : (1 : ℝ) < Real.sqrt p := Real.lt_sqrt (by norm_num) |>.mpr (by
    rw [one_pow]; exact_mod_cast (by omega : 1 < p))
  exact lt_of_lt_of_le (mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _))
    (primePowerAbelWeight_increment_ge (by omega) m)

theorem primePowerAbelWeight_mono {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    primePowerAbelWeight p m ≤ primePowerAbelWeight p (m + 1) := by
  have := primePowerAbelWeight_increment_ge hp m
  have : 0 ≤ Real.sqrt p ^ (2 * m) * (Real.sqrt p - 1) ^ 2 := by positivity
  linarith

/-- The half-density weighted coefficient `v_m = c_m p^{-m/2}`. -/
noncomputable def primePowerHalfCoeff (p : ℕ) (c : ℤ → ℝ) (m : ℕ) : ℝ :=
  c m * Real.sqrt p ^ (-(m : ℤ))

theorem summable_primePowerHalfCoeff {p : ℕ} (hp : 1 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) :
    Summable (primePowerHalfCoeff p c) := by
  have h := (summable_of_primePower hp hc (fun j => -j) (fun j => by rw [abs_neg])).comp_injective
    Nat.cast_injective
  exact h.congr fun m => rfl

theorem primePowerTail_eq_tsum {p : ℕ} (c : ℤ → ℝ) (k : ℕ) :
    primePowerTail p c ((k : ℤ) + 1) = ∑' i : ℕ, primePowerHalfCoeff p c (i + k + 1) := by
  unfold primePowerTail primePowerHalfCoeff
  have hinj : Function.Injective fun i : ℕ => (i : ℤ) + k + 1 := fun a b h => by
    simpa using h
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun i => ?_
    rw [if_pos (by omega)]
    push_cast
    rfl
  · intro j hj
    have hj' : (k : ℤ) + 1 ≤ j := by
      by_contra h
      exact hj (by simp only; rw [if_neg h])
    exact ⟨(j - k - 1).toNat, by simp only; rw [Int.toNat_of_nonneg (by omega)]; ring⟩

theorem abs_primePowerHalfCoeff_mul_abelWeight_le {p : ℕ} (hp : 1 ≤ p) (c : ℤ → ℝ) (m : ℕ) :
    |primePowerHalfCoeff p c m| * primePowerAbelWeight p m ≤ |c m| * Real.sqrt p ^ m := by
  have ha : (1 : ℝ) ≤ Real.sqrt p := Real.one_le_sqrt.mpr (by exact_mod_cast hp)
  have hx : (1 : ℝ) ≤ Real.sqrt p ^ m := one_le_pow₀ ha
  have hx0 : (0 : ℝ) < Real.sqrt p ^ m := by linarith
  unfold primePowerHalfCoeff primePowerAbelWeight
  rw [abs_mul, zpow_neg, zpow_natCast, abs_of_pos (inv_pos.mpr hx0), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [inv_mul_le_iff₀ hx0]
  nlinarith

/-- `M_{1/2} - M₀ = ∑_{m ≥ 1} c_m p^{-m/2} F_m` for a symmetric sequence. -/
theorem primePowerGaugeCharge_sub_mass {p : ℕ} (hp : 1 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j) :
    primePowerGaugeCharge p c - primePowerGaugeMass c =
      ∑' n : ℕ, primePowerHalfCoeff p c (n + 1) * primePowerAbelWeight p (n + 1) := by
  have ha0 : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p))
  have hs1 := summable_of_primePower hp hc (fun j => j) (fun j => le_rfl)
  have hs0 : Summable c := (summable_of_primePower hp hc (fun _ => 0) (fun j => by simp)).congr
    fun j => by simp
  unfold primePowerGaugeCharge primePowerGaugeMass
  rw [tsum_int_eq_zero_add_pairs hs1, tsum_int_eq_zero_add_pairs hs0, zpow_zero, mul_one,
    add_sub_add_left_eq_sub, ← (summable_int_pairs hs1).tsum_sub (summable_int_pairs hs0)]
  refine tsum_congr fun n => ?_
  rw [hsym]
  unfold primePowerHalfCoeff primePowerAbelWeight
  have hx : (0 : ℝ) < Real.sqrt p ^ (n + 1) := pow_pos ha0 _
  have e1 : Real.sqrt p ^ ((n : ℤ) + 1) = Real.sqrt p ^ (n + 1) := by
    rw [← zpow_natCast]; push_cast; rfl
  have e2 : Real.sqrt p ^ (-((n : ℤ) + 1)) = (Real.sqrt p ^ (n + 1))⁻¹ := by
    rw [zpow_neg, e1]
  have e3 : Real.sqrt p ^ (-((n + 1 : ℕ) : ℤ)) = (Real.sqrt p ^ (n + 1))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [e1, e2, e3]
  push_cast
  field_simp
  ring

/-- **Charge-gap identity.**  For a symmetric sequence,
`M_{1/2} - M₀ = ∑_{m ≥ 1} Q_m (F_m - F_{m-1})`, absolutely convergent. -/
theorem hasSum_primePowerChargeGap {p : ℕ} (hp : 1 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j) :
    HasSum (fun k : ℕ => primePowerTail p c ((k : ℤ) + 1) *
        (primePowerAbelWeight p (k + 1) - primePowerAbelWeight p k))
      (primePowerGaugeCharge p c - primePowerGaugeMass c) := by
  set v := primePowerHalfCoeff p c
  set d : ℕ → ℝ := fun k => primePowerAbelWeight p (k + 1) - primePowerAbelWeight p k
  have hd : ∀ k, 0 ≤ d k := fun k => sub_nonneg.mpr (primePowerAbelWeight_mono hp k)
  set φ : ℕ × ℕ → ℝ := fun q => d q.1 * v (q.2 + q.1 + 1)
  have hv := summable_primePowerHalfCoeff hp hc
  have hφq : ∀ n, ∀ q ∈ Finset.HasAntidiagonal.antidiagonal n, φ q = d q.1 * v (n + 1) := by
    intro n q hq
    have : q.1 + q.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    simp only [φ]
    congr 2
    omega
  have hdsum : ∀ n, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, d q.1 =
      primePowerAbelWeight p (n + 1) := by
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k _ => d k) n,
      Finset.sum_range_sub (primePowerAbelWeight p), primePowerAbelWeight_zero, sub_zero]
  have hfib : ∀ n, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, |φ q| =
      |v (n + 1)| * primePowerAbelWeight p (n + 1) := by
    intro n
    rw [Finset.sum_congr rfl fun q hq => by rw [hφq n q hq, abs_mul, abs_of_nonneg (hd _)],
      ← Finset.sum_mul, hdsum, mul_comm]
  have hfib' : ∀ n, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, φ q =
      v (n + 1) * primePowerAbelWeight p (n + 1) := by
    intro n
    rw [Finset.sum_congr rfl (hφq n), ← Finset.sum_mul, hdsum, mul_comm]
  have hmaj : Summable fun n : ℕ => |c ((n : ℤ) + 1)| * Real.sqrt p ^ (n + 1) := by
    have h := hc.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (fun a b h => by simpa using h)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    congr 2
  set e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have habs : Summable fun q => |φ q| := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun x => abs_nonneg _)).mpr
      ⟨fun n => Summable.of_finite, ?_⟩
    have : (fun n => ∑' y : ↥(Finset.HasAntidiagonal.antidiagonal n), |φ (e ⟨n, y⟩)|) =
        fun n => |v (n + 1)| * primePowerAbelWeight p (n + 1) := by
      funext n
      rw [← hfib n, ← Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal n) (fun q => |φ q|)]
      rfl
    rw [this]
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _)
      (by unfold primePowerAbelWeight; positivity)) (fun n => ?_) hmaj
    have h := abs_primePowerHalfCoeff_mul_abelWeight_le hp c (n + 1)
    push_cast at h
    exact h
  have hφ : Summable φ := Summable.of_norm (habs.congr fun q => (Real.norm_eq_abs _).symm)
  have hS2 : ∑' q, φ q = ∑' n : ℕ, v (n + 1) * primePowerAbelWeight p (n + 1) := by
    rw [← e.tsum_eq, Summable.tsum_sigma' (f := fun x => φ (e x)) (fun n => Summable.of_finite)
      (e.summable_iff.mpr hφ)]
    refine tsum_congr fun n => ?_
    rw [← hfib' n, ← Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal n) φ]
    rfl
  have hS3 : HasSum (fun k => d k * primePowerTail p c ((k : ℤ) + 1)) (∑' q, φ q) := by
    refine hφ.hasSum.prod_fiberwise fun k => ?_
    have hvk : Summable fun i => v (i + k + 1) := by
      have := (summable_nat_add_iff (k + 1)).mpr hv
      simpa [add_assoc] using this
    rw [primePowerTail_eq_tsum]
    exact hvk.hasSum.mul_left (d k)
  rw [primePowerGaugeCharge_sub_mass hp hc hsym, ← hS2]
  exact hS3.congr_fun fun k => mul_comm _ _

theorem primePowerTail_succ {p : ℕ} (hp : 1 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (k : ℕ) :
    primePowerTail p c ((k : ℤ) + 1) =
      primePowerHalfCoeff p c (k + 1) + primePowerTail p c (((k + 1 : ℕ) : ℤ) + 1) := by
  have hv := summable_primePowerHalfCoeff hp hc
  have hvk : Summable fun i => primePowerHalfCoeff p c (i + k + 1) := by
    have := (summable_nat_add_iff (k + 1)).mpr hv
    simpa [add_assoc] using this
  rw [primePowerTail_eq_tsum, primePowerTail_eq_tsum, hvk.tsum_eq_zero_add]
  congr 1
  · simp
  · exact tsum_congr fun i => by congr 1; ring

/-- **Charge monotonicity.**  Complete monotonicity forces `M_{1/2} ≥ M₀`. -/
theorem primePowerChargeGap_nonneg {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j)
    (hCM : CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p)))) :
    0 ≤ primePowerGaugeCharge p c - primePowerGaugeMass c :=
  (hasSum_primePowerChargeGap (by omega) hc hsym).nonneg fun k =>
    mul_nonneg (primePowerTail_nonneg hp hc hsym hCM _)
      (primePowerAbelWeight_increment_pos hp k).le

/-- **Equality case.**  Under complete monotonicity, `M_{1/2} = M₀` iff every nonzero shift has
vanishing coefficient. -/
theorem primePowerChargeGap_eq_zero_iff {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j)
    (hCM : CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p)))) :
    primePowerGaugeCharge p c - primePowerGaugeMass c = 0 ↔ ∀ j, j ≠ 0 → c j = 0 := by
  have ha0 : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p))
  constructor
  · intro hΔ
    have hS := hasSum_primePowerChargeGap (by omega) hc hsym
    rw [hΔ] at hS
    have hz := (hasSum_zero_iff_of_nonneg fun k => mul_nonneg
      (primePowerTail_nonneg hp hc hsym hCM _)
      (primePowerAbelWeight_increment_pos hp k).le).mp hS
    have hQ : ∀ k : ℕ, primePowerTail p c ((k : ℤ) + 1) = 0 := fun k =>
      (mul_eq_zero.mp (congrFun hz k)).resolve_right (primePowerAbelWeight_increment_pos hp k).ne'
    have hpos : ∀ m : ℕ, c ((m : ℤ) + 1) = 0 := by
      intro m
      have h := primePowerTail_succ (by omega) hc m
      rw [hQ, hQ, add_zero] at h
      unfold primePowerHalfCoeff at h
      push_cast at h
      exact (mul_eq_zero.mp h.symm).resolve_right (zpow_ne_zero _ ha0.ne')
    intro j hj
    rcases lt_or_gt_of_ne hj with hneg | hpos'
    · rw [← hsym j, show -j = ((-j - 1).toNat : ℤ) + 1 by omega]
      exact hpos _
    · rw [show j = ((j - 1).toNat : ℤ) + 1 by omega]
      exact hpos _
  · intro h
    unfold primePowerGaugeCharge primePowerGaugeMass
    rw [tsum_eq_single 0 (fun j hj => by rw [h j hj, zero_mul]),
      tsum_eq_single 0 (fun j hj => h j hj), zpow_zero, mul_one, sub_self]

/-! ## Anchors and rigidity -/

theorem primePowerGauge_integral {p : ℕ} (hp : 1 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) :
    (∫ x, thetaTranslationGauge c (primePowerShift p) x) =
      primePowerGaugeMass c * ∫ x, thetaCuspFullSource x := by
  have h := (integral_exp_mul_thetaTranslationGauge (primePower_gauge_admissible hp hc)
    (w := 0) (by norm_num)).2
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, mul_one] at h
  exact h

theorem primePowerGauge_integral_exp_half {p : ℕ} (hp : 1 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j) :
    (∫ x, Real.exp (x / 2) * thetaTranslationGauge c (primePowerShift p) x) =
      primePowerGaugeCharge p c * ∫ x, Real.exp (x / 2) * thetaCuspFullSource x := by
  have hp0 : 0 < p := by omega
  have h := (integral_exp_mul_thetaTranslationGauge (primePower_gauge_admissible hp hc)
    (w := 1 / 2) (by norm_num [abs_of_pos])).2
  have e1 : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  simp only [e1] at h
  rw [h]
  congr 1
  unfold primePowerGaugeCharge
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.neg_apply, hsym]
  congr 1
  rw [show -(primePowerShift p (-j) / 2) = primePowerShift p j / 2 by
    unfold primePowerShift; push_cast; ring, exp_half_primePowerShift hp0]

/-- **Two-anchor rigidity.**  A weighted-summable symmetric prime-power gauge with completely
monotone flux, the ordinary mass of `k` and the critical half-density charge of `k` is `k`. -/
theorem primePowerGauge_rigidity {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j)
    (hCM : CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p))))
    (hmass : ∫ x, thetaTranslationGauge c (primePowerShift p) x = ∫ x, thetaCuspFullSource x)
    (hcharge : ∫ x, Real.exp (x / 2) * thetaTranslationGauge c (primePowerShift p) x =
      ∫ x, Real.exp (x / 2) * thetaCuspFullSource x) :
    thetaTranslationGauge c (primePowerShift p) = thetaCuspFullSource ∧ c 0 = 1 ∧
      ∀ j, j ≠ 0 → c j = 0 := by
  have hk0 : 0 < ∫ x, thetaCuspFullSource x := by
    simpa using integral_exp_mul_thetaCuspFullSource_pos 0
  have hk1 : 0 < ∫ x, Real.exp (x / 2) * thetaCuspFullSource x := by
    have := integral_exp_mul_thetaCuspFullSource_pos (1 / 2)
    simpa only [show ∀ x : ℝ, 1 / 2 * x = x / 2 from fun x => by ring] using this
  have hM0 : primePowerGaugeMass c = 1 := by
    rw [primePowerGauge_integral (by omega) hc] at hmass
    exact (mul_eq_right₀ hk0.ne').mp hmass
  have hM1 : primePowerGaugeCharge p c = 1 := by
    rw [primePowerGauge_integral_exp_half (by omega) hc hsym] at hcharge
    exact (mul_eq_right₀ hk1.ne').mp hcharge
  have hzero := (primePowerChargeGap_eq_zero_iff hp hc hsym hCM).mp (by rw [hM0, hM1, sub_self])
  have hc0 : c 0 = 1 := by
    rw [← hM0]
    unfold primePowerGaugeMass
    rw [tsum_eq_single 0 (fun j hj => hzero j hj)]
  refine ⟨funext fun x => ?_, hc0, hzero⟩
  unfold thetaTranslationGauge
  rw [tsum_eq_single 0 (fun j hj => by rw [hzero j hj, zero_mul]), hc0, one_mul]
  simp [primePowerShift]

/-! ## Quantitative stability -/

/-- The stability constant `C_p = (p + 1)/(√p - 1)²`. -/
noncomputable def primePowerStabilityConstant (p : ℕ) : ℝ :=
  (Real.sqrt p ^ 2 + 1) / (Real.sqrt p - 1) ^ 2

/-- **Coefficient decay.**  `|c_m| ≤ C_p Δ p^{-m/2}` for `m ≥ 1`. -/
theorem abs_primePowerCoeff_le {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j)
    (hCM : CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p)))) (k : ℕ) :
    |c ((k : ℤ) + 1)| ≤ primePowerStabilityConstant p *
      (primePowerGaugeCharge p c - primePowerGaugeMass c) / Real.sqrt p ^ (k + 1) := by
  set a := Real.sqrt p
  set Δ := primePowerGaugeCharge p c - primePowerGaugeMass c
  have ha : 1 < a := Real.lt_sqrt (by norm_num) |>.mpr (by
    rw [one_pow]; exact_mod_cast (by omega : 1 < p))
  have hS := hasSum_primePowerChargeGap (by omega) hc hsym
  have hterm : ∀ k : ℕ, 0 ≤ primePowerTail p c ((k : ℤ) + 1) *
      (primePowerAbelWeight p (k + 1) - primePowerAbelWeight p k) := fun k =>
    mul_nonneg (primePowerTail_nonneg hp hc hsym hCM _)
      (primePowerAbelWeight_increment_pos hp k).le
  have hQ : ∀ k : ℕ, primePowerTail p c ((k : ℤ) + 1) * (a ^ (2 * k) * (a - 1) ^ 2) ≤ Δ := by
    intro k
    exact (mul_le_mul_of_nonneg_left (primePowerAbelWeight_increment_ge (by omega) k)
      (primePowerTail_nonneg hp hc hsym hCM _)).trans (le_hasSum hS k fun j _ => hterm j)
  have h1 := hQ k
  have h2 := hQ (k + 1)
  have hQ1 := primePowerTail_nonneg hp hc hsym hCM ((k : ℤ) + 1)
  have hQ2 := primePowerTail_nonneg hp hc hsym hCM (((k + 1 : ℕ) : ℤ) + 1)
  have hrec := primePowerTail_succ (by omega) hc k
  set Q1 := primePowerTail p c ((k : ℤ) + 1)
  set Q2 := primePowerTail p c (((k + 1 : ℕ) : ℤ) + 1)
  have hv : primePowerHalfCoeff p c (k + 1) = Q1 - Q2 := by linarith
  have hx : 0 < a ^ k := pow_pos (by linarith) k
  have hcv : c ((k : ℤ) + 1) = (Q1 - Q2) * a ^ (k + 1) := by
    rw [← hv]
    unfold primePowerHalfCoeff
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (show (0 : ℝ) < a by linarith).ne']
    push_cast
    simp
  have ha0 : (0 : ℝ) < a := by linarith
  rw [hcv, abs_mul, abs_of_pos (pow_pos ha0 _)]
  have hQ12 : |Q1 - Q2| ≤ Q1 + Q2 := abs_sub_le_iff.mpr (by constructor <;> linarith)
  unfold primePowerStabilityConstant
  have hD : 0 < (a - 1) ^ 2 := by nlinarith
  rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add] at h2
  rw [pow_mul] at h1 h2
  rw [le_div_iff₀ (pow_pos ha0 _), div_mul_eq_mul_div, le_div_iff₀ hD]
  have e : a ^ (k + 1) = a ^ k * a := pow_succ a k
  rw [e]
  have hsq : (a ^ 2) ^ k = (a ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hsq] at h1 h2
  nlinarith [mul_le_mul_of_nonneg_right hQ12 (by positivity : (0 : ℝ) ≤ a ^ k * a * (a ^ k * a) * (a - 1) ^ 2)]

theorem tsum_geometric_succ {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    ∑' n : ℕ, q ^ (n + 1) = q / (1 - q) := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1, div_eq_inv_mul]

theorem summable_geometric_succ {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Summable fun n : ℕ => q ^ (n + 1) := by
  simp_rw [pow_succ]
  exact (summable_geometric_of_lt_one h0 h1).mul_right q

/-- The complex stability constant `B_{p,σ} = 2 C_p [(p^{(1-2σ)/2} - 1)^{-1} + (√p - 1)^{-1}]`. -/
noncomputable def primePowerComplexConstant (p : ℕ) (σ : ℝ) : ℝ :=
  2 * primePowerStabilityConstant p * ((Real.sqrt p ^ (1 - 2 * σ) - 1)⁻¹ + (Real.sqrt p - 1)⁻¹)

theorem primePowerShift_succ (p n : ℕ) :
    primePowerShift p ((n : ℤ) + 1) = ((n : ℝ) + 1) * Real.log p := by
  unfold primePowerShift; push_cast; ring

theorem primePowerShift_neg_succ (p n : ℕ) :
    primePowerShift p (-((n : ℤ) + 1)) = -(((n : ℝ) + 1) * Real.log p) := by
  unfold primePowerShift; push_cast; ring

/-- **Uniform complex stability.**  For `0 ≤ σ < 1/2` and every `w` with `|Re w| ≤ σ`, at all
imaginary heights, `‖M(w) - M₀‖ ≤ B_{p,σ} (M_{1/2} - M₀)`. -/
theorem norm_primePowerMultiplier_sub_mass_le {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j)
    (hCM : CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p))))
    {σ : ℝ} (hσ : σ < 1 / 2) {w : ℂ} (hw : |w.re| ≤ σ) :
    ‖thetaGaugeMultiplier c (primePowerShift p) w - (primePowerGaugeMass c : ℂ)‖ ≤
      primePowerComplexConstant p σ * (primePowerGaugeCharge p c - primePowerGaugeMass c) := by
  have hp0 : 0 < p := by omega
  set a := Real.sqrt p with ha_def
  set L := Real.log p with hL_def
  set C := primePowerStabilityConstant p
  set Δ := primePowerGaugeCharge p c - primePowerGaugeMass c
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have ha : 1 < a := Real.lt_sqrt (by norm_num) |>.mpr (by
    rw [one_pow]; exact_mod_cast (by omega : 1 < p))
  have ha0 : 0 < a := by linarith
  have haL : a = Real.exp (L / 2) := by
    have := exp_half_primePowerShift hp0 1
    simp only [primePowerShift, Int.cast_one, one_mul, zpow_one] at this
    exact this.symm
  have hC : 0 ≤ C := by
    unfold C primePowerStabilityConstant
    positivity
  have hΔ : 0 ≤ Δ := primePowerChargeGap_nonneg hp hc hsym hCM
  have hdecay : ∀ n : ℕ, |c ((n : ℤ) + 1)| ≤ C * Δ / a ^ (n + 1) :=
    abs_primePowerCoeff_le hp hc hsym hCM
  have hadm := primePower_gauge_admissible (by omega) hc
  have hf : Summable fun j : ℤ => (c j : ℂ) * Complex.exp (-(w * primePowerShift p j)) := by
    refine Summable.of_norm_bounded hadm fun j => ?_
    rw [norm_thetaGaugeMultiplier_term]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    calc -(w.re * primePowerShift p j) ≤ |w.re * primePowerShift p j| := neg_le_abs _
      _ = |w.re| * |primePowerShift p j| := abs_mul _ _
      _ ≤ 1 / 2 * |primePowerShift p j| := by gcongr; linarith
      _ = |primePowerShift p j| / 2 := by ring
  have hs0 : Summable c := (summable_of_primePower (by omega) hc (fun _ => 0)
    (fun j => by simp)).congr fun j => by simp
  have hg : Summable fun j : ℤ => ((c j : ℝ) : ℂ) := Complex.summable_ofReal.mpr hs0
  set t : ℕ → ℝ := fun n => ((n : ℝ) + 1) * L
  have ht : ∀ n, 0 ≤ t n := fun n => by positivity
  set T : ℕ → ℂ := fun n => (c ((n : ℤ) + 1) : ℂ) *
    (Complex.exp (-(w * t n)) + Complex.exp (w * t n) - 2)
  have hdiff : thetaGaugeMultiplier c (primePowerShift p) w - (primePowerGaugeMass c : ℂ) =
      ∑' n, T n := by
    unfold thetaGaugeMultiplier primePowerGaugeMass
    rw [Complex.ofReal_tsum, tsum_int_eq_zero_add_pairs hf, tsum_int_eq_zero_add_pairs hg]
    have h0 : primePowerShift p 0 = 0 := by simp [primePowerShift]
    rw [h0, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one,
      add_sub_add_left_eq_sub, ← (summable_int_pairs hf).tsum_sub (summable_int_pairs hg)]
    refine tsum_congr fun n => ?_
    simp only [T, t]
    rw [primePowerShift_succ, primePowerShift_neg_succ, hsym, Complex.ofReal_neg, ← hL_def]
    ring_nf
  have hexp1 : ∀ n, ‖Complex.exp (-(w * t n))‖ ≤ Real.exp (σ * t n) := by
    intro n
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    nlinarith [neg_le_abs w.re, ht n]
  have hexp2 : ∀ n, ‖Complex.exp (w * t n)‖ ≤ Real.exp (σ * t n) := by
    intro n
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [le_abs_self w.re, ht n]
  set q₁ := Real.exp (σ * L) / a
  set q₂ := a⁻¹
  have hq₁0 : 0 ≤ q₁ := by positivity
  have hq₁1 : q₁ < 1 := by
    rw [div_lt_one ha0, haL, Real.exp_lt_exp]
    nlinarith
  have hq₂0 : 0 ≤ q₂ := by positivity
  have hq₂1 : q₂ < 1 := inv_lt_one_of_one_lt₀ ha
  set G : ℕ → ℝ := fun n => C * Δ * (2 * q₁ ^ (n + 1) + 2 * q₂ ^ (n + 1))
  have hTle : ∀ n, ‖T n‖ ≤ G n := by
    intro n
    have hn : ‖Complex.exp (-(w * t n)) + Complex.exp (w * t n) - 2‖ ≤
        2 * Real.exp (σ * t n) + 2 := by
      calc _ ≤ ‖Complex.exp (-(w * t n)) + Complex.exp (w * t n)‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖Complex.exp (-(w * t n))‖ + ‖Complex.exp (w * t n)‖ + ‖(2 : ℂ)‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ Real.exp (σ * t n) + Real.exp (σ * t n) + 2 := by
            gcongr
            · exact hexp1 n
            · exact hexp2 n
            · simp
        _ = 2 * Real.exp (σ * t n) + 2 := by ring
    have hσt : Real.exp (σ * t n) = Real.exp (σ * L) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]; push_cast; simp only [t]; ring_nf
    simp only [T, G]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |c ((n : ℤ) + 1)| * ‖Complex.exp (-(w * t n)) + Complex.exp (w * t n) - 2‖
        ≤ C * Δ / a ^ (n + 1) * (2 * Real.exp (σ * t n) + 2) :=
          mul_le_mul (hdecay n) hn (norm_nonneg _) (by positivity)
      _ = C * Δ * (2 * q₁ ^ (n + 1) + 2 * q₂ ^ (n + 1)) := by
          rw [hσt]
          simp only [q₁, q₂]
          rw [div_pow, inv_pow]
          field_simp
  have hGs : Summable G :=
    (((summable_geometric_succ hq₁0 hq₁1).mul_left 2).add
      ((summable_geometric_succ hq₂0 hq₂1).mul_left 2)).mul_left (C * Δ)
  have hGsum : ∑' n, G n = primePowerComplexConstant p σ * Δ := by
    simp only [G]
    rw [tsum_mul_left, (((summable_geometric_succ hq₁0 hq₁1).mul_left 2)).tsum_add
      ((summable_geometric_succ hq₂0 hq₂1).mul_left 2), tsum_mul_left, tsum_mul_left,
      tsum_geometric_succ hq₁0 hq₁1, tsum_geometric_succ hq₂0 hq₂1]
    have hrp : a ^ (1 - 2 * σ) = a / Real.exp (σ * L) := by
      rw [Real.rpow_def_of_pos ha0, ha_def, Real.log_sqrt (Nat.cast_nonneg _), ← hL_def,
        ← ha_def, haL, ← Real.exp_sub]
      ring_nf
    unfold primePowerComplexConstant
    rw [← ha_def, hrp]
    simp only [q₁, q₂]
    have he : 0 < Real.exp (σ * L) := Real.exp_pos _
    have h1 : a / Real.exp (σ * L) - 1 ≠ 0 := by
      have : Real.exp (σ * L) < a := by rw [div_lt_one ha0] at hq₁1; exact hq₁1
      rw [sub_ne_zero, ne_eq, div_eq_one_iff_eq he.ne']
      exact this.ne'
    have h2 : a - 1 ≠ 0 := by linarith
    have h3 : 1 - Real.exp (σ * L) / a ≠ 0 := by linarith
    have h4 : 1 - a⁻¹ ≠ 0 := by linarith
    field_simp
    ring
  rw [hdiff]
  calc ‖∑' n, T n‖ ≤ ∑' n, ‖T n‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hTle hGs)
    _ ≤ ∑' n, G n := (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hTle hGs).tsum_le_tsum
        hTle hGs
    _ = _ := hGsum

/-- **No new zeros.**  If `M₀ = 1` and `B_{p,σ} Δ < 1`, the multiplier has no zero in the closed
substrip `|Re w| ≤ σ`, and there the Mellin transform of the gauge vanishes exactly where
`XiC(iw)` does, with the same analytic order. -/
theorem primePowerGauge_zero_transfer {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j)
    (hCM : CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p))))
    (hM0 : primePowerGaugeMass c = 1) {σ : ℝ} (hσ : σ < 1 / 2)
    (hB : primePowerComplexConstant p σ * (primePowerGaugeCharge p c - primePowerGaugeMass c) < 1)
    {w : ℂ} (hw : |w.re| ≤ σ) :
    thetaGaugeMultiplier c (primePowerShift p) w ≠ 0 ∧
      ((∫ x : ℝ, Complex.exp (w * x) *
          (thetaTranslationGauge c (primePowerShift p) x : ℂ)) = 0 ↔ XiC (I * w) = 0) ∧
      analyticOrderAt (fun z : ℂ => ∫ x : ℝ, Complex.exp (z * x) *
          (thetaTranslationGauge c (primePowerShift p) x : ℂ)) w =
        analyticOrderAt (fun z : ℂ => XiC (I * z)) w := by
  have hadm := primePower_gauge_admissible (by omega) hc
  have hne : thetaGaugeMultiplier c (primePowerShift p) w ≠ 0 := by
    intro h
    have hb := norm_primePowerMultiplier_sub_mass_le hp hc hsym hCM hσ hw
    rw [h, hM0] at hb
    rw [hM0] at hB
    norm_num at hb
    linarith
  have hw' : |w.re| < 1 / 2 := lt_of_le_of_lt hw hσ
  refine ⟨hne, ?_, analyticOrderAt_integral_cexp_mul_thetaTranslationGauge hadm hw' hne⟩
  rw [(integral_cexp_mul_thetaTranslationGauge hadm hw'.le).2, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hne, Or.inr⟩

/-- The Mellin multiplier is the Dirichlet-type sum `∑ c_j p^{-jw}`. -/
theorem thetaGaugeMultiplier_primePower {p : ℕ} (hp : 0 < p) (c : ℤ → ℝ) (w : ℂ) :
    thetaGaugeMultiplier c (primePowerShift p) w = ∑' j : ℤ, (c j : ℂ) * (p : ℂ) ^ (-(j * w)) := by
  unfold thetaGaugeMultiplier
  refine tsum_congr fun j => ?_
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.natCast_log]
  unfold primePowerShift
  push_cast
  ring_nf

/-! ## `L¹` stability -/

theorem integrable_thetaCuspFullSource' : Integrable thetaCuspFullSource :=
  (integrable_exp_mul_thetaCuspFullSource_real 0).congr (ae_of_all _ fun x => by simp)

/-- **`L¹` stability.**  `‖g - M₀ k‖₁ ≤ 4 C_p Δ ‖k‖₁/(√p - 1)`. -/
theorem integral_abs_primePowerGauge_sub_le {p : ℕ} (hp : 2 ≤ p) {c : ℤ → ℝ}
    (hc : Summable fun j : ℤ => |c j| * Real.sqrt p ^ j.natAbs) (hsym : ∀ j, c (-j) = c j)
    (hCM : CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaTranslationGauge c (primePowerShift p)))) :
    (∫ x, |thetaTranslationGauge c (primePowerShift p) x -
        primePowerGaugeMass c * thetaCuspFullSource x|) ≤
      4 * primePowerStabilityConstant p * (primePowerGaugeCharge p c - primePowerGaugeMass c) *
        (∫ x, thetaCuspFullSource x) / (Real.sqrt p - 1) := by
  set a := Real.sqrt p
  set L := Real.log p
  set C := primePowerStabilityConstant p
  set Δ := primePowerGaugeCharge p c - primePowerGaugeMass c
  set K := ∫ x, thetaCuspFullSource x
  have ha : 1 < a := Real.lt_sqrt (by norm_num) |>.mpr (by
    rw [one_pow]; exact_mod_cast (by omega : 1 < p))
  have ha0 : 0 < a := by linarith
  have hK : 0 ≤ K := integral_nonneg fun x => (thetaCuspFullSource_pos_all x).le
  have hkint := integrable_thetaCuspFullSource'
  have hadm := primePower_gauge_admissible (by omega) hc
  have hs0 : Summable c := (summable_of_primePower (by omega) hc (fun _ => 0)
    (fun j => by simp)).congr fun j => by simp
  have hcabs := summable_abs_of_gauge hadm
  have hdecay : ∀ n : ℕ, |c ((n : ℤ) + 1)| ≤ C * Δ / a ^ (n + 1) :=
    abs_primePowerCoeff_le hp hc hsym hCM
  set t : ℕ → ℝ := fun n => ((n : ℝ) + 1) * L
  set Φ : ℕ → ℝ → ℝ := fun n x => |c ((n : ℤ) + 1)| *
    (thetaCuspFullSource (x + t n) + thetaCuspFullSource (x - t n) + 2 * thetaCuspFullSource x)
  have hcn : Summable fun n : ℕ => |c ((n : ℤ) + 1)| :=
    hcabs.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (fun a b h => by simpa using h)
  obtain ⟨Ck, hCk⟩ := exists_abs_thetaCuspFullSource_le_const
  -- pointwise decomposition
  have hdec : ∀ x, thetaTranslationGauge c (primePowerShift p) x -
      primePowerGaugeMass c * thetaCuspFullSource x = ∑' n : ℕ, c ((n : ℤ) + 1) *
        (thetaCuspFullSource (x + t n) + thetaCuspFullSource (x - t n) -
          2 * thetaCuspFullSource x) := by
    intro x
    have hA := summable_thetaTranslationGauge (s := primePowerShift p) hcabs x
    have hB : Summable fun j : ℤ => c j * thetaCuspFullSource x := hs0.mul_right _
    unfold thetaTranslationGauge primePowerGaugeMass
    rw [tsum_mul_right.symm, tsum_int_eq_zero_add_pairs hA, tsum_int_eq_zero_add_pairs hB]
    have h0 : primePowerShift p 0 = 0 := by simp [primePowerShift]
    rw [h0, add_zero, add_sub_add_left_eq_sub,
      ← (summable_int_pairs hA).tsum_sub (summable_int_pairs hB)]
    refine tsum_congr fun n => ?_
    rw [primePowerShift_succ, primePowerShift_neg_succ, hsym]
    simp only [t, L, ← sub_eq_add_neg]
    ring
  have hterm_le : ∀ (n : ℕ) (x : ℝ), ‖c ((n : ℤ) + 1) * (thetaCuspFullSource (x + t n) +
      thetaCuspFullSource (x - t n) - 2 * thetaCuspFullSource x)‖ ≤ Φ n x := by
    intro n x
    have h1 := thetaCuspFullSource_pos_all (x + t n)
    have h2 := thetaCuspFullSource_pos_all (x - t n)
    have h3 := thetaCuspFullSource_pos_all x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)
  have hΦle : ∀ x, |thetaTranslationGauge c (primePowerShift p) x -
      primePowerGaugeMass c * thetaCuspFullSource x| ≤ ∑' n, Φ n x := by
    intro x
    have hΦs : Summable fun n => Φ n x := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hcn.mul_right (4 * Ck))
      · have := thetaCuspFullSource_pos_all
        simp only [Φ]
        exact mul_nonneg (abs_nonneg _) (by linarith [this (x + t n), this (x - t n), this x])
      · simp only [Φ]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h1 := hCk (x + t n)
        have h2 := hCk (x - t n)
        have h3 := hCk x
        rw [abs_of_pos (thetaCuspFullSource_pos_all _)] at h1 h2 h3
        linarith
    rw [hdec]
    calc |∑' n : ℕ, c ((n : ℤ) + 1) * (thetaCuspFullSource (x + t n) +
          thetaCuspFullSource (x - t n) - 2 * thetaCuspFullSource x)|
        ≤ ∑' n : ℕ, ‖c ((n : ℤ) + 1) * (thetaCuspFullSource (x + t n) +
          thetaCuspFullSource (x - t n) - 2 * thetaCuspFullSource x)‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
            (fun n => hterm_le n x) hΦs)
      _ ≤ ∑' n, Φ n x := (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
            (fun n => hterm_le n x) hΦs).tsum_le_tsum (fun n => hterm_le n x) hΦs
  have hΦint : ∀ n, Integrable (Φ n) := fun n =>
    (((hkint.comp_add_right (t n)).add (hkint.comp_sub_right (t n))).add
      (hkint.const_mul 2)).const_mul _
  have hΦval : ∀ n, (∫ x, Φ n x) = 4 * K * |c ((n : ℤ) + 1)| := by
    intro n
    simp only [Φ]
    have i1 : Integrable (fun x => thetaCuspFullSource (x + t n)) := hkint.comp_add_right _
    have i2 : Integrable (fun x => thetaCuspFullSource (x - t n)) := hkint.comp_sub_right _
    have i3 : Integrable (fun x => 2 * thetaCuspFullSource x) := hkint.const_mul 2
    have i12 : Integrable (fun x => thetaCuspFullSource (x + t n) +
      thetaCuspFullSource (x - t n)) := i1.add i2
    rw [integral_const_mul, integral_add i12 i3, integral_add i1 i2,
      integral_add_right_eq_self (fun x => thetaCuspFullSource x),
      integral_sub_right_eq_self (fun x => thetaCuspFullSource x), integral_const_mul]
    ring
  have hΦnorm : ∀ n, (∫ x, ‖Φ n x‖) = 4 * K * |c ((n : ℤ) + 1)| := by
    intro n
    rw [← hΦval n]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have h1 := thetaCuspFullSource_pos_all (x + t n)
    have h2 := thetaCuspFullSource_pos_all (x - t n)
    have h3 := thetaCuspFullSource_pos_all x
    simp only [Φ, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (abs_nonneg _) (by linarith))
  have hsumint : Summable fun n => ∫ x, ‖Φ n x‖ := by
    simp_rw [hΦnorm]
    exact hcn.mul_left _
  have hsumΦint := integrable_tsum_of_summable_integral_norm hΦint hsumint
  have hgint : Integrable (thetaTranslationGauge c (primePowerShift p)) :=
    (integral_exp_mul_thetaTranslationGauge hadm (w := 0) (by norm_num)).1.congr
      (ae_of_all _ fun x => by simp)
  have hmain : (∫ x, |thetaTranslationGauge c (primePowerShift p) x -
      primePowerGaugeMass c * thetaCuspFullSource x|) ≤ 4 * K * ∑' n : ℕ, |c ((n : ℤ) + 1)| := by
    calc _ ≤ ∫ x, ∑' n, Φ n x :=
          integral_mono ((hgint.sub (hkint.const_mul _)).abs) hsumΦint hΦle
      _ = ∑' n, ∫ x, Φ n x := (integral_tsum_of_summable_integral_norm hΦint hsumint).symm
      _ = 4 * K * ∑' n : ℕ, |c ((n : ℤ) + 1)| := by
          simp_rw [hΦval]
          rw [tsum_mul_left]
  have hq0 : 0 ≤ a⁻¹ := by positivity
  have hq1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hgeo : ∑' n : ℕ, |c ((n : ℤ) + 1)| ≤ C * Δ / (a - 1) := by
    have hmaj : ∀ n : ℕ, |c ((n : ℤ) + 1)| ≤ C * Δ * a⁻¹ ^ (n + 1) := fun n => by
      rw [inv_pow, ← div_eq_mul_inv]; exact hdecay n
    calc ∑' n : ℕ, |c ((n : ℤ) + 1)| ≤ ∑' n : ℕ, C * Δ * a⁻¹ ^ (n + 1) :=
          hcn.tsum_le_tsum hmaj ((summable_geometric_succ hq0 hq1).mul_left _)
      _ = C * Δ / (a - 1) := by
          rw [tsum_mul_left, tsum_geometric_succ hq0 hq1]
          have : a - 1 ≠ 0 := by linarith
          field_simp
  calc _ ≤ 4 * K * ∑' n : ℕ, |c ((n : ℤ) + 1)| := hmain
    _ ≤ 4 * K * (C * Δ / (a - 1)) := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 4 * C * Δ * K / (a - 1) := by ring

/-! ## Rescaling and the signed example -/

theorem primePowerPrefix_const_mul (p : ℕ) (c : ℤ → ℝ) (l : ℝ) (v : ℤ) :
    primePowerPrefix p (fun j => l * c j) v = l * primePowerPrefix p c v := by
  unfold primePowerPrefix
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  split_ifs <;> ring

theorem primePowerGaugeMass_const_mul (c : ℤ → ℝ) (l : ℝ) :
    primePowerGaugeMass (fun j => l * c j) = l * primePowerGaugeMass c := by
  unfold primePowerGaugeMass
  rw [tsum_mul_left]

theorem primePowerGaugeCharge_const_mul (p : ℕ) (c : ℤ → ℝ) (l : ℝ) :
    primePowerGaugeCharge p (fun j => l * c j) = l * primePowerGaugeCharge p c := by
  unfold primePowerGaugeCharge
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- The signed example `c₀ = 1`, `c_{±2} = ε`, `c_{±1} = -ε/(2√p)`. -/
noncomputable def primePowerSignedExample (p : ℕ) (ε : ℝ) (j : ℤ) : ℝ :=
  if j = 0 then 1 else if j = 2 ∨ j = -2 then ε else
    if j = 1 ∨ j = -1 then -(ε / (2 * Real.sqrt p)) else 0

theorem primePowerSignedExample_symm (p : ℕ) (ε : ℝ) (j : ℤ) :
    primePowerSignedExample p ε (-j) = primePowerSignedExample p ε j := by
  unfold primePowerSignedExample
  have h2 : (-j = 2 ∨ -j = -2) ↔ (j = 2 ∨ j = -2) := by omega
  have h1 : (-j = 1 ∨ -j = -1) ↔ (j = 1 ∨ j = -1) := by omega
  simp only [neg_eq_zero, h2, h1]

theorem primePowerSignedExample_eq_zero (p : ℕ) (ε : ℝ) {j : ℤ}
    (hj : j ∉ ({-2, -1, 0, 1, 2} : Finset ℤ)) : primePowerSignedExample p ε j = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  unfold primePowerSignedExample
  rw [if_neg hj.2.2.1, if_neg (by omega), if_neg (by omega)]

theorem tsum_primePowerSignedExample (p : ℕ) (ε : ℝ) (F : ℤ → ℝ → ℝ)
    (hF : ∀ j, F j 0 = 0) :
    ∑' j, F j (primePowerSignedExample p ε j) =
      F (-2) ε + F (-1) (-(ε / (2 * Real.sqrt p))) + F 0 1 +
        F 1 (-(ε / (2 * Real.sqrt p))) + F 2 ε := by
  rw [tsum_eq_sum (s := {-2, -1, 0, 1, 2}) (fun j hj => by
    rw [primePowerSignedExample_eq_zero p ε hj, hF])]
  simp [Finset.sum_insert, primePowerSignedExample]
  ring

theorem summable_primePowerSignedExample (p : ℕ) (ε : ℝ) :
    Summable fun j : ℤ => |primePowerSignedExample p ε j| * Real.sqrt p ^ j.natAbs :=
  summable_of_ne_finset_zero (s := {-2, -1, 0, 1, 2}) fun j hj => by
    rw [primePowerSignedExample_eq_zero p ε hj, abs_zero, zero_mul]

theorem primePowerSignedExample_prefix {p : ℕ} (hp : 2 ≤ p) (ε : ℝ) (v : ℤ) :
    primePowerPrefix p (primePowerSignedExample p ε) v =
      (if -2 ≤ v then ε / p else 0) + (if -1 ≤ v then -(ε / (2 * p)) else 0) +
        (if 0 ≤ v then 1 else 0) + (if 1 ≤ v then -(ε / 2) else 0) +
          (if 2 ≤ v then ε * p else 0) := by
  have ha0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p))
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  unfold primePowerPrefix
  rw [tsum_primePowerSignedExample p ε (fun j x => if j ≤ v then x * Real.sqrt p ^ j else 0)
    (fun j => by simp)]
  have e1 : ε * Real.sqrt p ^ (-2 : ℤ) = ε / p := by
    rw [zpow_neg, zpow_ofNat, hsq, div_eq_mul_inv]
  have e2 : -(ε / (2 * Real.sqrt p)) * Real.sqrt p ^ (-1 : ℤ) = -(ε / (2 * p)) := by
    rw [zpow_neg, zpow_one, show -(ε / (2 * (p : ℝ))) = -(ε / (2 * Real.sqrt p ^ 2)) by rw [hsq]]
    field_simp
  have e3 : -(ε / (2 * Real.sqrt p)) * Real.sqrt p ^ (1 : ℤ) = -(ε / 2) := by
    rw [zpow_one]; field_simp
  have e4 : ε * Real.sqrt p ^ (2 : ℤ) = ε * p := by rw [zpow_ofNat, hsq]
  simp only [e1, e2, e3, e4, zpow_zero, one_mul]

/-- The signed example has a completely monotone flux, although its shift coefficients at
`±log p` are negative. -/
theorem completelyMonotoneOn_primePowerSignedExample {p : ℕ} (hp : 2 ≤ p) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    CompletelyMonotoneOn (thetaNormalizedFlux
      (thetaTranslationGauge (primePowerSignedExample p ε) (primePowerShift p))) := by
  rw [completelyMonotoneOn_primePowerGauge_iff hp (summable_primePowerSignedExample p ε)]
  intro v
  rw [primePowerSignedExample_prefix hp]
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hA : 0 < ε / p := by positivity
  have hB : ε / (2 * p) = ε / p / 2 := by field_simp
  have hC : 0 ≤ ε * p := by positivity
  split_ifs <;> first | omega | linarith

theorem primePowerSignedExample_neg_coeff {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε0 : 0 < ε) :
    primePowerSignedExample p ε 1 < 0 := by
  have ha0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p))
  unfold primePowerSignedExample
  rw [if_neg one_ne_zero, if_neg (by norm_num), if_pos (Or.inl rfl)]
  exact neg_lt_zero.mpr (by positivity)

/-- The signed example has a strictly positive charge gap. -/
theorem primePowerSignedExample_chargeGap_pos {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε0 : 0 < ε) :
    0 < primePowerGaugeCharge p (primePowerSignedExample p ε) -
      primePowerGaugeMass (primePowerSignedExample p ε) := by
  set a := Real.sqrt p
  have ha : 1 < a := Real.lt_sqrt (by norm_num) |>.mpr (by
    rw [one_pow]; exact_mod_cast (by omega : 1 < p))
  have ha0 : 0 < a := by linarith
  have hsq : a ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  unfold primePowerGaugeCharge primePowerGaugeMass
  rw [tsum_primePowerSignedExample p ε (fun j x => x * Real.sqrt p ^ j) (fun j => by simp),
    tsum_primePowerSignedExample p ε (fun _ x => x) (fun _ => rfl)]
  have h1 : 0 < (a - 1) ^ 2 := by nlinarith
  have hpos : 0 < ε * (a - 1) ^ 2 * (2 * a ^ 2 + 4 * a + 1) / (2 * a ^ 2) := by positivity
  convert hpos using 1
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  ring

/-- **Nonvacuity.**  After positive rescaling to the ordinary mass of `k`, the signed example is a
symmetric weighted-summable gauge with a negative shift coefficient, completely monotone flux,
`M₀ = 1`, and strictly positive charge gap. -/
theorem primePowerSignedExample_normalized {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ l : ℝ, 0 < l ∧
      (∀ j, l * primePowerSignedExample p ε (-j) = l * primePowerSignedExample p ε j) ∧
      Summable (fun j : ℤ => |l * primePowerSignedExample p ε j| * Real.sqrt p ^ j.natAbs) ∧
      l * primePowerSignedExample p ε 1 < 0 ∧
      CompletelyMonotoneOn (thetaNormalizedFlux (thetaTranslationGauge
        (fun j => l * primePowerSignedExample p ε j) (primePowerShift p))) ∧
      primePowerGaugeMass (fun j => l * primePowerSignedExample p ε j) = 1 ∧
      0 < primePowerGaugeCharge p (fun j => l * primePowerSignedExample p ε j) -
        primePowerGaugeMass (fun j => l * primePowerSignedExample p ε j) := by
  set c := primePowerSignedExample p ε
  have ha : 1 < Real.sqrt p := Real.lt_sqrt (by norm_num) |>.mpr (by
    rw [one_pow]; exact_mod_cast (by omega : 1 < p))
  have hM : primePowerGaugeMass c = 1 + 2 * ε - ε / Real.sqrt p := by
    unfold primePowerGaugeMass
    rw [tsum_primePowerSignedExample p ε (fun _ x => x) (fun _ => rfl)]
    field_simp
    ring
  have hMpos : 0 < primePowerGaugeMass c := by
    rw [hM]
    have : ε / Real.sqrt p < ε := div_lt_self hε0 ha
    linarith
  have hsum := summable_primePowerSignedExample p ε
  refine ⟨(primePowerGaugeMass c)⁻¹, inv_pos.mpr hMpos, fun j => by
    simp only [c, primePowerSignedExample_symm], ?_, ?_, ?_, ?_, ?_⟩
  · exact (hsum.mul_left |(primePowerGaugeMass c)⁻¹|).congr fun j => by rw [abs_mul]; ring
  · exact mul_neg_of_pos_of_neg (inv_pos.mpr hMpos) (primePowerSignedExample_neg_coeff hp hε0)
  · rw [completelyMonotoneOn_primePowerGauge_iff hp
      ((hsum.mul_left |(primePowerGaugeMass c)⁻¹|).congr fun j => by rw [abs_mul]; ring)]
    intro v
    rw [primePowerPrefix_const_mul]
    exact mul_nonneg (inv_pos.mpr hMpos).le
      ((completelyMonotoneOn_primePowerGauge_iff hp hsum).mp
        (completelyMonotoneOn_primePowerSignedExample hp hε0 hε1) v)
  · rw [primePowerGaugeMass_const_mul, inv_mul_cancel₀ hMpos.ne']
  · rw [primePowerGaugeMass_const_mul, primePowerGaugeCharge_const_mul, ← mul_sub]
    exact mul_pos (inv_pos.mpr hMpos) (primePowerSignedExample_chargeGap_pos hp hε0)

end RHTower
