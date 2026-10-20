import GaloisForLFunctions.ArithmeticIncidencePositivity.AntiDiagonalPolarCompensation

/-!
# The prime atom against the pole: collar measure and exact classification

Continuation of the continuum picture of `AntiDiagonalPolarCompensation`.

**Anti-diagonal decomposition.** On the anti-diagonal of sum `s > 0`, parametrized as `(−a, s − a)`,
the archimedean kernel is `ω(s) − P_s(a)` with the polar weight `P_s(a) = 2 sinh(a/2) sinh((s − a)/2)`:
the density of the jump length `s` minus the polar weight. The points of negative archimedean
conductance form the **collar** of the anti-diagonal, the set where the polar weight is below `ω(s)`.

* For `s ≥ 4 log 2` the collar has length `< 6 e^{−3s/4}`, and the archimedean conductance the pole
  leaves unpaid on the whole anti-diagonal has total mass `≤ 6 ω(s) e^{−3s/4}`.
* **Exact classification.** The atom `Λ(n)/√n` of the anti-diagonal of `n` exceeds the polar weight
  at *every* point of the anti-diagonal iff `n ∈ {2, 3, 4, 5, 7}`: the primes up to `7` and the
  square `4`. For every other `n ≥ 2` the pole pays the atom at the midpoint. The condition is
  `(√n − 1)² < 2Λ(n)`; the arithmetic input is `Λ(p^k) = log p`, the analysis is
  `log r ≤ sinh(log r)` on fourth roots for primes `p ≥ 11`, `log p ≤ p − 1` for `k ≥ 2`, and four
  explicit comparisons.
-/

open RHTower Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The collar of an anti-diagonal -/

/-- On the anti-diagonal the archimedean kernel never exceeds the density of the jump length. -/
theorem archPairKernel_antiDiagonal_le {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (has : a ≤ s) :
    archPairKernel (-a) (s - a) ≤ archLevyDensity s := by
  rw [archPairKernel_antiDiagonal_eq hs]
  linarith [crossingPolarWeight_nonneg ha has]

/-- The collar of the anti-diagonal of sum `s`: its points with negative archimedean conductance. -/
def antiDiagonalCollar (s : ℝ) : Set ℝ := {a | 0 < a ∧ a < s ∧ 0 < archPairKernel (-a) (s - a)}

theorem antiDiagonalCollar_eq {s : ℝ} (hs : 0 < s) :
    antiDiagonalCollar s = Ioo 0 s ∩ {a | crossingPolarWeight s a < archLevyDensity s} := by
  ext a
  simp only [antiDiagonalCollar, mem_setOf_eq, mem_inter_iff, mem_Ioo, and_assoc,
    archPairKernel_antiDiagonal_eq hs, sub_pos]

theorem measurableSet_antiDiagonalCollar {s : ℝ} (hs : 0 < s) :
    MeasurableSet (antiDiagonalCollar s) := by
  rw [antiDiagonalCollar_eq hs]
  exact measurableSet_Ioo.inter
    (measurableSet_lt (continuous_crossingPolarWeight s).measurable measurable_const)

/-- For `s ≥ 4 log 2` the collar lies within `3 e^{−3s/4}` of the two ends of the anti-diagonal. -/
theorem antiDiagonalCollar_subset {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    antiDiagonalCollar s ⊆
      Ioo 0 (3 * Real.exp (-(3 * s) / 4)) ∪ Ioo (s - 3 * Real.exp (-(3 * s) / 4)) s := by
  intro a ha
  obtain ⟨ha0, has, hk⟩ := ha
  have h16 : 4 * Real.log 2 ≤ (s - a) - -a := by linarith
  have h := min_lt_of_archPairKernel_pos (by linarith) (by linarith) h16 hk
  have e : s - a - -a = s := by ring
  rw [e] at h
  have h' : min a (s - a) < 3 * Real.exp (-(3 * s) / 4) := by simpa only [neg_neg] using h
  rcases min_lt_iff.mp h' with h1 | h1
  · exact Or.inl ⟨ha0, h1⟩
  · exact Or.inr ⟨by linarith, has⟩

/-- **Collar measure.** For `s ≥ 4 log 2` the collar has length at most `6 e^{−3s/4}`. -/
theorem volume_antiDiagonalCollar_le {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    volume (antiDiagonalCollar s) ≤ ENNReal.ofReal (6 * Real.exp (-(3 * s) / 4)) := by
  have hc : 0 < 3 * Real.exp (-(3 * s) / 4) := by positivity
  calc volume (antiDiagonalCollar s)
      ≤ volume (Ioo 0 (3 * Real.exp (-(3 * s) / 4)) ∪
          Ioo (s - 3 * Real.exp (-(3 * s) / 4)) s) := measure_mono (antiDiagonalCollar_subset hs)
    _ ≤ volume (Ioo 0 (3 * Real.exp (-(3 * s) / 4))) +
          volume (Ioo (s - 3 * Real.exp (-(3 * s) / 4)) s) := measure_union_le _ _
    _ = ENNReal.ofReal (3 * Real.exp (-(3 * s) / 4) - 0) +
          ENNReal.ofReal (s - (s - 3 * Real.exp (-(3 * s) / 4))) := by
        rw [Real.volume_Ioo, Real.volume_Ioo]
    _ = ENNReal.ofReal (6 * Real.exp (-(3 * s) / 4)) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

/-- **Unpaid archimedean mass of an anti-diagonal.** For `s ≥ 4 log 2` the archimedean conductance
not paid by the pole, integrated along the anti-diagonal, is at most `6 ω(s) e^{−3s/4}`. -/
theorem lintegral_antiDiagonalCollar_le {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    ∫⁻ a in antiDiagonalCollar s, ENNReal.ofReal (archPairKernel (-a) (s - a)) ≤
      ENNReal.ofReal (archLevyDensity s) * ENNReal.ofReal (6 * Real.exp (-(3 * s) / 4)) := by
  have hs0 : 0 < s := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  calc ∫⁻ a in antiDiagonalCollar s, ENNReal.ofReal (archPairKernel (-a) (s - a))
      ≤ ∫⁻ _ in antiDiagonalCollar s, ENNReal.ofReal (archLevyDensity s) := by
        refine setLIntegral_mono' (measurableSet_antiDiagonalCollar hs0) fun a ha => ?_
        obtain ⟨h1, h2, _⟩ := ha
        exact ENNReal.ofReal_le_ofReal (archPairKernel_antiDiagonal_le hs0 h1.le h2.le)
    _ = ENNReal.ofReal (archLevyDensity s) * volume (antiDiagonalCollar s) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (archLevyDensity s) * ENNReal.ofReal (6 * Real.exp (-(3 * s) / 4)) :=
        mul_le_mul' le_rfl (volume_antiDiagonalCollar_le hs)

/-! ### Explicit logarithm and square-root bounds -/

/-- `log m + (1 − m/p) ≤ log p` for `0 < m ≤ p`: the tangent bound of the logarithm at `m`. -/
theorem log_add_one_sub_div_le_log {m p : ℝ} (hm : 0 < m) (hmp : m ≤ p) :
    Real.log m + (1 - m / p) ≤ Real.log p := by
  have hp : 0 < p := lt_of_lt_of_le hm hmp
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hp hm)
  rw [Real.log_div hp.ne' hm.ne', inv_div] at h
  linarith

theorem log_eight_eq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring

theorem log_sixteen_eq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring

theorem sqrt_sub_one_sq_eq {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x - 1) ^ 2 = x + 1 - 2 * Real.sqrt x := by
  rw [sub_sq, Real.sq_sqrt hx]; ring

/-- A lower bound `L < √x` turns into the upper bound `(√x − 1)² < x + 1 − 2L`. -/
theorem sqrt_sub_one_sq_lt {x L B : ℝ} (hx : 0 ≤ x) (hL : L < Real.sqrt x)
    (hB : x + 1 - 2 * L ≤ B) : (Real.sqrt x - 1) ^ 2 < B := by
  rw [sqrt_sub_one_sq_eq hx]; linarith

/-- For the four primes `p ≤ 7`, `(√p − 1)² < 2 log p`. -/
theorem sqrt_sub_one_sq_lt_two_log_of_prime_le_seven {p : ℕ} (hp : p.Prime) (h7 : p ≤ 7) :
    (Real.sqrt p - 1) ^ 2 < 2 * Real.log p := by
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    have := hp.two_le
    interval_cases p <;> (revert hp; norm_num)
  have hl2 := Real.log_two_gt_d9
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals push_cast
  · have hL : (1.41 : ℝ) < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)
  · have hL : (1.73 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have := log_add_one_sub_div_le_log (m := 2) (p := 3) (by norm_num) (by norm_num)
    exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)
  · have hL : (2.23 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have := log_add_one_sub_div_le_log (m := 4) (p := 5) (by norm_num) (by norm_num)
    rw [log_four_eq] at this
    exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)
  · have hL : (2.64 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have := log_add_one_sub_div_le_log (m := 4) (p := 7) (by norm_num) (by norm_num)
    rw [log_four_eq] at this
    exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)

/-- The polynomial inequality behind the large-prime regime: `r³ − r ≥ 4` for `r ≥ 1.82`. -/
theorem large_prime_cubic_aux {t : ℝ} (ht : 0 ≤ t) :
    4 ≤ (1.82 + t) ^ 3 - (1.82 + t) := by
  nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, ht]

/-- For real `x ≥ 11`, `2 log x ≤ (√x − 1)²`. Through the fourth root `r` of `x`:
`log r ≤ sinh(log r)` gives `2 log x ≤ 4 (r² − 1)/r`, and `r³ − r ≥ 4` once `r⁴ ≥ 11`. -/
theorem two_mul_log_le_sqrt_sub_one_sq {x : ℝ} (hx : 11 ≤ x) :
    2 * Real.log x ≤ (Real.sqrt x - 1) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = Real.sqrt (Real.sqrt x) := ⟨_, rfl⟩
  have hr : 0 < r := hr_def ▸ Real.sqrt_pos.mpr hsx
  have hr2 : r ^ 2 = Real.sqrt x := by rw [hr_def]; exact Real.sq_sqrt hsx.le
  have hr4 : r ^ 4 = x := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2, Real.sq_sqrt hx0.le]
  have hr182 : (1.82 : ℝ) ≤ r := by
    by_contra hlt
    rw [not_le] at hlt
    have h4 : r ^ 4 < (1.82 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hr.le (by norm_num)
    rw [hr4] at h4
    norm_num at h4
    linarith
  have hr1 : 1 < r := by linarith
  have hlog : Real.log x = 4 * Real.log r := by
    rw [← hr4, Real.log_pow]; push_cast; ring
  have hsinh : Real.log r ≤ (r - r⁻¹) / 2 := by
    have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hr1.le)
    rwa [Real.sinh_eq, Real.exp_neg, Real.exp_log hr] at h
  have hcube := large_prime_cubic_aux (t := r - 1.82) (by linarith)
  rw [show (1.82 : ℝ) + (r - 1.82) = r by ring] at hcube
  have hsq : (Real.sqrt x - 1) ^ 2 = (r ^ 2 - 1) ^ 2 := by rw [hr2]
  rw [hsq, hlog]
  have h2 : 4 * (r ^ 2 - 1) / r = 4 * (r - r⁻¹) := by
    rw [mul_div_assoc, sub_div, pow_two, mul_div_assoc, div_self hr.ne', mul_one, one_div]
  have h3 : 4 * (r ^ 2 - 1) / r ≤ (r ^ 2 - 1) ^ 2 := by
    rw [div_le_iff₀ hr]
    have hpos : 0 ≤ r ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hpos (sub_nonneg.mpr hcube)]
  linarith

/-! ### The exact classification -/

/-- The five moduli whose prime atom exceeds the polar weight on the whole anti-diagonal. -/
def atomDominatedModuli : Finset ℕ := {2, 3, 4, 5, 7}

/-- **Classification.** For `n ≥ 2`: `(√n − 1)² < 2Λ(n)` iff `n ∈ {2, 3, 4, 5, 7}`. -/
theorem sqrt_sub_one_sq_lt_two_vonMangoldt_iff {n : ℕ} (hn : 2 ≤ n) :
    (Real.sqrt n - 1) ^ 2 < 2 * ArithmeticFunction.vonMangoldt n ↔ n ∈ atomDominatedModuli := by
  simp only [atomDominatedModuli, Finset.mem_insert, Finset.mem_singleton]
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hp2 := hp.two_le
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · -- `n = p` prime: the threshold is `p ≤ 7`
      obtain rfl : k = 1 := by omega
      simp only [pow_one]
      constructor
      · intro h
        rcases Nat.lt_or_ge p 11 with h11 | h11
        · interval_cases p <;> (revert hp; norm_num)
        · exfalso
          have := two_mul_log_le_sqrt_sub_one_sq (x := (p : ℝ)) (by exact_mod_cast h11)
          linarith
      · intro h
        exact sqrt_sub_one_sq_lt_two_log_of_prime_le_seven hp (by omega)
    · -- `n = p^k`, `k ≥ 2`: only `4` qualifies
      rcases Nat.lt_or_ge p 3 with hp3 | hp3
      · obtain rfl : p = 2 := by omega
        rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · obtain rfl : k = 2 := by omega
          refine iff_of_true ?_ (by norm_num)
          push_cast
          have h4 : Real.sqrt 4 = 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
          rw [h4]
          norm_num
          linarith [Real.log_two_gt_d9]
        · refine iff_of_false ?_ ?_
          · rw [not_lt]
            have h8 : (8 : ℕ) ≤ 2 ^ k := by
              calc (8 : ℕ) = 2 ^ 3 := by norm_num
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
            have h8r : (8 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h8
            have hL : (2.8 : ℝ) < Real.sqrt 8 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
            have hs : Real.sqrt 8 ≤ Real.sqrt ((2 ^ k : ℕ) : ℝ) := Real.sqrt_le_sqrt h8r
            have h2 : (1.8 : ℝ) ^ 2 ≤ (Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1) ^ 2 :=
              pow_le_pow_left₀ (by norm_num) (by linarith) 2
            have := Real.log_two_lt_d9
            simp only [Nat.cast_ofNat]
            have c2 : (1.8 : ℝ) ^ 2 = 3.24 := by norm_num
            linarith
          · have h8 : (8 : ℕ) ≤ 2 ^ k := by
              calc (8 : ℕ) = 2 ^ 3 := by norm_num
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
            omega
      · -- `p ≥ 3`, `k ≥ 2`: `(√n − 1)² ≥ (p − 1)² ≥ 2(p − 1) ≥ 2 log p`, and `p^k ≥ 9`
        refine iff_of_false ?_ ?_
        · rw [not_lt]
          have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          have hpk : (p : ℝ) ^ 2 ≤ ((p ^ k : ℕ) : ℝ) := by
            exact_mod_cast Nat.pow_le_pow_right hp.pos hk2
          have hs : (p : ℝ) ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) :=
            (Real.le_sqrt (by linarith) (by linarith)).mpr hpk
          have hC : ((p : ℝ) - 1) ^ 2 ≤ (Real.sqrt ((p ^ k : ℕ) : ℝ) - 1) ^ 2 :=
            pow_le_pow_left₀ (by linarith) (by linarith) 2
          have hlog : Real.log p ≤ (p : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
          nlinarith
        · have h9 : (9 : ℕ) ≤ p ^ k := by
            calc (9 : ℕ) = 3 ^ 2 := by norm_num
              _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
              _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
          omega
  · -- not a prime power: no atom, and none of the five moduli
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    refine iff_of_false ?_ ?_
    · rw [not_lt, mul_zero]
      exact sq_nonneg _
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact hpp Nat.prime_two.isPrimePow
      · exact hpp Nat.prime_three.isPrimePow
      · exact hpp ((isPrimePow_nat_iff 4).mpr ⟨2, 2, Nat.prime_two, by norm_num, by norm_num⟩)
      · exact hpp Nat.prime_five.isPrimePow
      · exact hpp (by norm_num : Nat.Prime 7).isPrimePow

theorem two_le_of_mem_atomDominatedModuli {n : ℕ} (hn : n ∈ atomDominatedModuli) : 2 ≤ n := by
  simp only [atomDominatedModuli, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

theorem two_sinh_log_div_four_sq_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < 2 * Real.sinh (Real.log n / 4) ^ 2 := by
  apply mul_pos two_pos
  apply pow_pos
  apply Real.sinh_pos_iff.mpr
  exact div_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < n))) (by norm_num)

/-- **Payment scale threshold.** `polarPaymentScale n > 1` iff `n` is one of the five moduli. -/
theorem one_lt_polarPaymentScale_iff {n : ℕ} (hn : 2 ≤ n) :
    1 < polarPaymentScale n ↔ n ∈ atomDominatedModuli := by
  rw [polarPaymentScale_eq hn, ← sqrt_sub_one_sq_lt_two_vonMangoldt_iff hn]
  have hs : 1 < Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast (by omega : 1 < n))
  exact one_lt_div (pow_pos (by linarith) 2)

/-- On the anti-diagonal of one of the five moduli the atom exceeds the polar weight at every
point: the pole pays none of it anywhere. -/
theorem crossingPolarWeight_lt_vonMangoldtAtom {n : ℕ} (hn : n ∈ atomDominatedModuli) (a : ℝ) :
    crossingPolarWeight (Real.log n) a < vonMangoldtAtom n := by
  have hn2 := two_le_of_mem_atomDominatedModuli hn
  have h := (one_lt_polarPaymentScale_iff hn2).mpr hn
  unfold polarPaymentScale at h
  rw [one_lt_div (two_sinh_log_div_four_sq_pos hn2)] at h
  exact lt_of_le_of_lt (crossingPolarWeight_le_midpoint _ _) h

/-- On the anti-diagonal of one of the five moduli the total crossing kernel, archimedean density
plus atom minus polar weight, is positive everywhere: negative conductance along the whole segment. -/
theorem antiDiagonal_total_pos_of_mem {n : ℕ} (hn : n ∈ atomDominatedModuli) (a : ℝ) :
    0 < archLevyDensity (Real.log n) + vonMangoldtAtom n - crossingPolarWeight (Real.log n) a := by
  have hn2 := two_le_of_mem_atomDominatedModuli hn
  have h1 := crossingPolarWeight_lt_vonMangoldtAtom hn a
  have h2 : 0 < archLevyDensity (Real.log n) :=
    archLevyDensity_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
  linarith

/-- For every other modulus `n ≥ 2` the pole pays the atom at the midpoint of the anti-diagonal. -/
theorem vonMangoldtAtom_le_crossingPolarWeight_midpoint {n : ℕ} (hn : 2 ≤ n)
    (hn' : n ∉ atomDominatedModuli) :
    vonMangoldtAtom n ≤ crossingPolarWeight (Real.log n) (Real.log n / 2) := by
  rw [crossingPolarWeight_midpoint]
  have h : ¬ 1 < polarPaymentScale n := fun h => hn' ((one_lt_polarPaymentScale_iff hn).mp h)
  unfold polarPaymentScale at h
  rw [one_lt_div (two_sinh_log_div_four_sq_pos hn)] at h
  exact not_lt.mp h

end GaloisForLFunctions.ArithmeticIncidencePositivity
