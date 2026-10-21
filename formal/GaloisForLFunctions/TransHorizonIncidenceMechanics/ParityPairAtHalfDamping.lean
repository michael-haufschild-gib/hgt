import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityTwinOfTheDampedMoebiusWeight

/-!
# The parity pair at half damping

For a weight `c` with mean `m = Σ_d c(d)/d` the pronic receiver energy is

`E_T(c) = Σ_{n ≤ T} A_c(n)²/(n(n+1))`,   `A_c(n) = Σ_{j ≤ n} Σ_{d | j} c(d) - m n`.

Counting multiples along the unit step `k ↦ k+1` gives `Σ_{j ≤ n} Σ_{d | j} c(d) = Σ_{d ≤ n} c(d)⌊n/d⌋`,
so `A_c(n) = -Σ_{d ≤ n} c(d){n/d} - n Σ_{d > n} c(d)/d`. For a nonnegative weight both terms have one
sign: the moduli `d > n`, which have not yet produced a divisibility event, leave the uncancelled drift
`A_c(n) ≤ -n Σ_{n < d ≤ 2n} c(d)/d`.

The parity twin `c'_ε` of the damped Möbius weight is nonnegative and dominates `μ²(d) d^{-ε}`, so on
the squarefree integers of `(n, 2n]` the drift is `≳ n^{1-ε}`, and `E_T(c'_ε) → ∞` for every
`0 < ε ≤ 1/2`. At `ε = 1/2` the damped weight itself has bounded receiver energy (the Mellin bound
`exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le`, which rests on `ζ(1 + it) ≠ 0`).

**The parity pair.** `c_{1/2}` and `c'_{1/2}` have Ramanujan coefficients `w(e)` and `μ(e) w(e)`:
identical amplitudes, hence identical diagonal data (mean, variance, every lag covariance
`Σ c_e(h) w(e)²`, successor energy, primitive energy, every pronic mode mass `w(e)² 𝒢(e,e)`), and
opposite receiver growth: bounded against divergent. The signs `μ(e)` are seen first at the prime
moduli, `W_{c'}(p) = -w(p) > 0 > w(p)`, i.e. by the mean of the signal along the dilation `k ↦ pk`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The receiver energy of a weight -/

/-- Centered divisor-sum prefix `A_c(n) = Σ_{j ≤ n} Σ_{d | j} c(d) - m n`. -/
def weightCenteredPrefix (c : ℕ → ℝ) (m : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 n, ∑ d ∈ j.divisors, c d) - m * n

/-- Pronic receiver energy `E_T(c) = Σ_{n ≤ T} A_c(n)²/(n(n+1))`. -/
def weightPronicEnergy (c : ℕ → ℝ) (m : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- The damped weight's receiver energy is the PM discrete energy. -/
theorem weightPronicEnergy_pmPowerDamped (ε : ℝ) (T : ℕ) :
    weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T =
      RHTower.pmPowerDampedDivisorDiscreteEnergy ε T := by
  unfold weightPronicEnergy RHTower.pmPowerDampedDivisorDiscreteEnergy
  refine sum_congr rfl fun n _ => ?_
  rw [weightCenteredPrefix, RHTower.pmPowerDampedCenteredDivisorPrefix_eq]
  congr 3

private theorem Icc_one_eq_Ioc_zero (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext d; simp only [mem_Icc, mem_Ioc]; omega

/-- Counting multiples: `Σ_{j ≤ n} Σ_{d | j} c(d) = Σ_{d ≤ n} c(d) ⌊n/d⌋`. -/
theorem sum_Icc_sum_divisors_eq_floor (c : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Icc 1 n, ∑ d ∈ j.divisors, c d = ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) := by
  have h1 : ∀ j ∈ Icc 1 n, ∑ d ∈ j.divisors, c d =
      ∑ d ∈ Icc 1 n, if d ∣ j then c d else 0 := by
    intro j hj
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc] at hj ⊢
    constructor
    · rintro ⟨hdj, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdj (by omega), (Nat.le_of_dvd (by omega) hdj).trans hj.2⟩, hdj⟩
    · rintro ⟨-, hdj⟩
      exact ⟨hdj, by omega⟩
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, Icc_one_eq_Ioc_zero,
    Nat.Ioc_filter_dvd_card_eq_div]

/-- **The drift of a nonnegative weight.** If `c ≥ 0` and `Σ_d c(d)/d = m`, then
`A_c(n) ≤ -n Σ_{n < d ≤ 2n} c(d)/d`. -/
theorem weightCenteredPrefix_le_neg_drift {c : ℕ → ℝ} {m : ℝ} (hc : ∀ d, 0 ≤ c d)
    (hm : HasSum (fun d : ℕ => c d / d) m) (n : ℕ) :
    weightCenteredPrefix c m n ≤ -((n : ℝ) * ∑ d ∈ Ioc n (2 * n), c d / d) := by
  have hfloor : ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) ≤ (n : ℝ) * ∑ d ∈ Ioc 0 n, c d / d := by
    rw [mul_sum, ← Icc_one_eq_Ioc_zero]
    refine sum_le_sum fun d _ => ?_
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := d)
    calc c d * ((n / d : ℕ) : ℝ) ≤ c d * ((n : ℝ) / d) := mul_le_mul_of_nonneg_left this (hc d)
      _ = (n : ℝ) * (c d / d) := by ring
  have hmass : ∑ d ∈ Ioc 0 n, c d / d + ∑ d ∈ Ioc n (2 * n), c d / d ≤ m := by
    rw [sum_Ioc_consecutive _ (Nat.zero_le n) (by omega)]
    exact sum_le_hasSum _ (fun d _ => div_nonneg (hc d) (Nat.cast_nonneg d)) hm
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hmass hn]

/-! ### Squarefree integers in a dyadic window -/

/-- At least `n/8` squarefree integers lie in `(n, 2n]` once `n ≥ 100`. -/
theorem squarefree_count_dyadic_ge {n : ℕ} (hn : 100 ≤ n) :
    (n : ℝ) / 8 ≤ ∑ d ∈ Ioc n (n + n), ((moebius d : ℤ) : ℝ) ^ (2 : ℕ) := by
  have hRsq : n + n ≤ (Nat.sqrt (2 * n) + 1) ^ (2 : ℕ) := by
    have := Nat.lt_succ_sqrt' (2 * n)
    simp only [Nat.succ_eq_add_one] at this
    omega
  set R := Nat.sqrt (2 * n) + 1 with hRdef
  have hR : 1 ≤ R := by omega
  have hw := RHTower.Sieve.abs_window_squarefree_sub_le hR hRsq
  have hD := RHTower.Sieve.squarefreeDensity_ge
  set s := Real.sqrt (2 * (n : ℝ))
  have hn0 : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hs2 : s ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by linarith)
  have hs14 : 14 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hRle : (R : ℝ) ≤ s + 1 := by
    have h := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
    push_cast at h ⊢
    simp only [R]; push_cast; linarith
  have hRge : s ≤ (R : ℝ) := by
    have h := Real.real_sqrt_le_nat_sqrt_succ (a := 2 * n)
    push_cast at h ⊢
    simp only [R]; push_cast; linarith
  have hspos : 0 < s := by linarith
  have hdiv : (n : ℝ) / R ≤ s / 2 := by
    calc (n : ℝ) / R ≤ n / s := div_le_div_of_nonneg_left (by linarith) hspos hRge
      _ = s / 2 := by rw [div_eq_div_iff hspos.ne' (by norm_num)]; nlinarith
  have habs := (abs_le.mp hw).1
  nlinarith

/-! ### Divergence of the parity twin -/

/-- On `(n, 2n]` the twin's tail carries at least `(K/16) (2n)^{-ε}` per unit, `K = ρ_ε/U_ε`. -/
theorem parityTwin_drift_ge {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 100 ≤ n) :
    dampedDensity ε / parityTwinCoprimeMass ε 1 / 16 * (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) ≤
      (n : ℝ) * ∑ d ∈ Ioc n (2 * n), parityTwinWeight ε d / d := by
  set K := dampedDensity ε / parityTwinCoprimeMass ε 1
  have hK : 0 < K := div_pos (RHTower.pmPowerDampedDivisorDensity_re_pos hε)
    (parityTwinCoprimeMass_one_pos hε)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have hterm : ∀ d ∈ Ioc n (2 * n),
      K * (2 * (n : ℝ)) ^ (-1 - ε) * ((moebius d : ℤ) : ℝ) ^ (2 : ℕ) ≤ parityTwinWeight ε d / d := by
    intro d hd
    rw [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hdle : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    by_cases hsq : Squarefree d
    · have hmu : ((moebius d : ℤ) : ℝ) ^ (2 : ℕ) = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      rw [hmu, mul_one]
      have hge := parityTwinWeight_ge hε hsq
      have hpow : (2 * (n : ℝ)) ^ (-1 - ε) ≤ (d : ℝ) ^ (-1 - ε) :=
        Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)
      have hdpow : (d : ℝ) ^ (-1 - ε) = (d : ℝ) ^ (-ε) / d := by
        rw [show -1 - ε = -ε - 1 by ring, Real.rpow_sub_one hd0.ne']
      calc K * (2 * (n : ℝ)) ^ (-1 - ε) ≤ K * ((d : ℝ) ^ (-ε) / d) :=
            mul_le_mul_of_nonneg_left (hdpow ▸ hpow) hK.le
        _ = K * (d : ℝ) ^ (-ε) / d := by ring
        _ ≤ parityTwinWeight ε d / d := div_le_div_of_nonneg_right hge hd0.le
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact div_nonneg (parityTwinWeight_nonneg hε d) hd0.le
  have hsum := sum_le_sum hterm
  rw [← mul_sum] at hsum
  have hcount : (n : ℝ) / 8 ≤ ∑ d ∈ Ioc n (2 * n), ((moebius d : ℤ) : ℝ) ^ (2 : ℕ) := by
    have h := squarefree_count_dyadic_ge hn
    rwa [← two_mul] at h
  have hpow : (2 * (n : ℝ)) ^ (-1 - ε) = (2 * (n : ℝ)) ^ (-ε) / (2 * n) := by
    rw [show -1 - ε = -ε - 1 by ring, Real.rpow_sub_one h2n.ne']
  have key : K * ((2 * (n : ℝ)) ^ (-ε) / (2 * n)) * ((n : ℝ) / 8) ≤
      ∑ d ∈ Ioc n (2 * n), parityTwinWeight ε d / d := by
    rw [← hpow]
    exact (mul_le_mul_of_nonneg_left hcount
      (mul_nonneg hK.le (Real.rpow_nonneg h2n.le _))).trans hsum
  have e1 : K / 16 * (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) =
      (n : ℝ) * (K * ((2 * (n : ℝ)) ^ (-ε) / (2 * n)) * ((n : ℝ) / 8)) := by
    have := hn0.ne'
    field_simp
    ring
  rw [e1]
  exact mul_le_mul_of_nonneg_left key hn0.le

/-- **Cell bound from the drift.** If a nonnegative weight of mean `m` carries
`K n (2n)^{-ε}` on the dyadic tail `(n, 2n]` and `ε ≤ 1/2`, its pronic cell `n` carries at least
`K²/(4n)`. -/
theorem weightCell_ge_of_drift {c : ℕ → ℝ} {m K ε : ℝ} (hc : ∀ d, 0 ≤ c d)
    (hm : HasSum (fun d : ℕ => c d / d) m) (hK : 0 ≤ K) (hε2 : ε ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n)
    (hdrift : K * n * (2 * (n : ℝ)) ^ (-ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), c d / d) :
    K ^ 2 / 4 / n ≤ weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (1 : ℝ) ≤ 2 * n := by linarith
  have hA := weightCenteredPrefix_le_neg_drift hc hm n
  set A := weightCenteredPrefix c m n with hAdef
  have hPnn : 0 ≤ (2 * (n : ℝ)) ^ (-ε) := Real.rpow_nonneg (by linarith) _
  -- `ε ≤ 1/2` gives `(2n)^{-2ε} ≥ 1/(2n)`
  have hP2 : 1 / (2 * (n : ℝ)) ≤ ((2 * (n : ℝ)) ^ (-ε)) ^ 2 := by
    have h1 : ((2 * (n : ℝ)) ^ (-ε)) ^ 2 = (2 * (n : ℝ)) ^ (-ε * 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [h1, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h2n (by linarith)
  have hlow : K * n * (2 * (n : ℝ)) ^ (-ε) ≤ -A := by linarith
  have hsq : (K * n * (2 * (n : ℝ)) ^ (-ε)) ^ 2 ≤ A ^ 2 := by
    have h0 : 0 ≤ K * n * (2 * (n : ℝ)) ^ (-ε) := by positivity
    nlinarith
  rw [div_le_div_iff₀ hn0 (by positivity)]
  have hexp : (K * n * (2 * (n : ℝ)) ^ (-ε)) ^ 2 * n =
      K ^ 2 * (n : ℝ) ^ 3 * ((2 * (n : ℝ)) ^ (-ε)) ^ 2 := by ring
  have h1 : K ^ 2 * (n : ℝ) ^ 3 * (1 / (2 * n)) = K ^ 2 * (n : ℝ) ^ 2 / 2 := by
    have := hn0.ne'
    field_simp
  have h2 : K ^ 2 * (n : ℝ) ^ 3 * (1 / (2 * n)) ≤
      K ^ 2 * (n : ℝ) ^ 3 * ((2 * (n : ℝ)) ^ (-ε)) ^ 2 :=
    mul_le_mul_of_nonneg_left hP2 (by positivity)
  have h3 : K ^ 2 / 4 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ K ^ 2 * (n : ℝ) ^ 2 / 2 := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg K) hn0.le) (show (0 : ℝ) ≤ n - 1 by linarith)]
  linarith [mul_le_mul_of_nonneg_right hsq hn0.le]

private theorem weightPronicEnergy_eq_sum_range (c : ℕ → ℝ) (m : ℝ) (T : ℕ) :
    weightPronicEnergy c m T = ∑ n ∈ range (T + 1),
      weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  induction T with
  | zero => simp [weightPronicEnergy]
  | succ T ih =>
    rw [weightPronicEnergy, Finset.sum_Icc_succ_top (by omega), ← weightPronicEnergy, ih,
      Finset.sum_range_succ _ (T + 1)]

/-- **Drift divergence.** A nonnegative weight whose dyadic tails carry `K (2n)^{-ε}` per unit,
`K > 0`, `ε ≤ 1/2`, has divergent receiver energy: the drift of the moduli beyond the prefix
cannot cancel. -/
theorem tendsto_weightPronicEnergy_of_drift {c : ℕ → ℝ} {m K ε : ℝ} (hc : ∀ d, 0 ≤ c d)
    (hm : HasSum (fun d : ℕ => c d / d) m) (hK : 0 < K) (hε2 : ε ≤ 1 / 2) (n₀ : ℕ)
    (hdrift : ∀ n, n₀ ≤ n → K * n * (2 * (n : ℝ)) ^ (-ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), c d / d) :
    Tendsto (fun T => weightPronicEnergy c m T) atTop atTop := by
  set e : ℕ → ℝ := fun n => weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
  have he0 : ∀ n, 0 ≤ e n := fun n => div_nonneg (sq_nonneg _)
    (mul_nonneg (Nat.cast_nonneg n) (by positivity))
  set N := n₀ + 1
  have hc4 : 0 < K ^ 2 / 4 := by positivity
  have hns : ¬ Summable e := by
    intro hs
    have hg : Summable (fun n : ℕ => if N ≤ n then K ^ 2 / 4 / n else 0) :=
      hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        (fun n => by
          split_ifs with h
          · exact weightCell_ge_of_drift hc hm hK.le hε2 (by omega) (hdrift n (by omega))
          · exact he0 n)
    have hg' : Summable (fun n : ℕ => K ^ 2 / 4 / ((n + N : ℕ) : ℝ)) := by
      refine ((summable_nat_add_iff N).mpr hg).congr fun n => ?_
      simp
    have hc0 := hc4.ne'
    have h1 : Summable (fun n : ℕ => 1 / ((n + N : ℕ) : ℝ)) :=
      (hg'.mul_left (K ^ 2 / 4)⁻¹).congr fun n => by field_simp
    exact Real.not_summable_one_div_natCast
      ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) N).mp h1)
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg he0).mp hns
  refine (ht.comp (tendsto_add_atTop_nat 1)).congr fun T => ?_
  simp only [Function.comp_apply, e]
  rw [weightPronicEnergy_eq_sum_range]

/-- **The twin's receiver energy diverges** for every `0 < ε ≤ 1/2`. -/
theorem tendsto_weightPronicEnergy_parityTwin {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Tendsto (fun T => weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T)
      atTop atTop :=
  tendsto_weightPronicEnergy_of_drift (parityTwinWeight_nonneg hε) (hasSum_parityTwinWeight_div hε)
    (by have := div_pos (RHTower.pmPowerDampedDivisorDensity_re_pos hε)
          (parityTwinCoprimeMass_one_pos hε)
        positivity) hε2 100 fun n hn => parityTwin_drift_ge hε hn

/-! ### The pair -/

/-- **The parity pair at half damping.** The damped Möbius weight `c_{1/2}` and its parity twin
`c'_{1/2}` have Ramanujan coefficients `w(e)` and `μ(e) w(e)` — identical amplitudes, hence identical
diagonal (translation, variance, primitive, pronic-mode) data — and opposite receiver growth: the
first energy is bounded, the second diverges. -/
theorem parityPair_at_half_damping :
    (∀ e : ℕ, 0 < e → weightRamanujanCoeff (parityTwinWeight (1 / 2)) e =
        (moebius e : ℝ) * weightRamanujanCoeff (pmPowerDampedRealWeight (1 / 2)) e) ∧
    (∀ e : ℕ, 0 < e → |weightRamanujanCoeff (parityTwinWeight (1 / 2)) e| =
        |weightRamanujanCoeff (pmPowerDampedRealWeight (1 / 2)) e|) ∧
    (∀ d : ℕ, 0 ≤ parityTwinWeight (1 / 2) d) ∧
    (∃ B : ℝ, ∀ T : ℕ,
        weightPronicEnergy (pmPowerDampedRealWeight (1 / 2)) (dampedDensity (1 / 2)) T ≤ B) ∧
    Tendsto (fun T => weightPronicEnergy (parityTwinWeight (1 / 2)) (dampedDensity (1 / 2)) T)
      atTop atTop := by
  have h : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨fun e he => ?_, fun e he => abs_weightRamanujanCoeff_parityTwin h he,
    parityTwinWeight_nonneg h, ?_, tendsto_weightPronicEnergy_parityTwin h le_rfl⟩
  · rw [weightRamanujanCoeff_parityTwin h e, weightRamanujanCoeff_pmPowerDamped h he]
  · obtain ⟨B, hB⟩ := RHTower.exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le
      (le_refl (1 / 2 : ℝ))
    exact ⟨B, fun T => (weightPronicEnergy_pmPowerDamped _ T).trans_le (hB T)⟩

/-- The squared coefficients agree, so every diagonal statistic `Σ_e f(e) W(e)²` coincides. -/
theorem sq_weightRamanujanCoeff_parityTwin {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    weightRamanujanCoeff (parityTwinWeight ε) e ^ 2 =
      weightRamanujanCoeff (pmPowerDampedRealWeight ε) e ^ 2 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [weightRamanujanCoeff]
  · rw [← sq_abs, abs_weightRamanujanCoeff_parityTwin hε he, sq_abs]

/-- The separating observable: at every prime modulus the twin's coefficient has the opposite sign,
`W_{c'_ε}(p) = -w_ε(p) > 0`. -/
theorem weightRamanujanCoeff_parityTwin_prime {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    weightRamanujanCoeff (parityTwinWeight ε) p = -dampedRamanujanCoeff ε p ∧
      dampedRamanujanCoeff ε p < 0 := by
  have hmu : (moebius p : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
  refine ⟨by rw [weightRamanujanCoeff_parityTwin hε p, hmu]; ring, ?_⟩
  rw [dampedRamanujanCoeff_eq_closed hε, hmu]
  have hD := RHTower.pmPowerDampedRamanujanDenominator_pos hε p
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have : dampedDensity ε * (-1) / RHTower.pmPowerDampedRamanujanDenominator ε p < 0 :=
    div_neg_of_neg_of_pos (by linarith) hD
  exact this

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
