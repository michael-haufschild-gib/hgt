import GaloisForLFunctions.ArithmeticDiscreteness.EulerColumnsCollideOrRepelAtPolynomialScale

/-!
# Real Satake angles defeat polynomial repulsion

The converse of `IntegralPureEulerFactorsRepelAtPolynomialScale`: without integrality of the local
data the polynomial collide-or-repel law fails, even for pure local factors.

* **A Liouville angle** (`exists_liouville_angle`). There is a real `L` approximated by values of
  the linear form `Λ(k, j) = k log 3 − j log 2` with `0 < L − Λ(k_n, j_n) ≤ e^{−|k_n|}/4` and
  `|k_n| ≥ n`. The pairs `(k_n, j_n)` are built step by step: Dirichlet's theorem gives positive
  values of `Λ` below any `ε`, and the effective Baker bound (`lam23_ne_zero`, `exists_lam23_gap`)
  forces the coefficient of each step to exceed `3|k_n| + 1`, so the steps shrink like
  `e^{−|k|}`.
* **Super-polynomial near-coincidences** (`real_pure_carrier_not_polynomial_repulsion`). For
  `θ = 2πL/log 2` the pure carrier `(1 − 2^{−s})(1 − 2cos θ · 3^{−s} + 3^{−2s})` has, for every
  `c, C > 0`, two distinct zeros of height `≤ T` at distance `< c T^{−C}`: the column point
  `2πik_n/log 2` and the zero `i(θ + 2πj_n)/log 3` of the second factor are
  `2π(L − Λ(k_n, j_n))/(log 2 log 3) ≤ e^{−|k_n|}`-close.

With `a_p ∈ ℤ`, `|a_p| ≤ 2`, the Satake angles are rational multiples of `π` and the law holds at
polynomial scale; with `a_p = 2cos θ` real it fails. The discreteness that the polynomial law needs
is the integrality of the local data together with the transcendence of the prime logarithms.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The linear form `k log 3 − j log 2`. -/
def lam23 (k j : ℤ) : ℝ := k * Real.log 3 - j * Real.log 2

theorem lam23_add (k j k' j' : ℤ) : lam23 (k + k') (j + j') = lam23 k j + lam23 k' j' := by
  unfold lam23; push_cast; ring

theorem lam23_neg (k j : ℤ) : lam23 (-k) (-j) = -lam23 k j := by unfold lam23; push_cast; ring

/-- `k log 3 ≠ j log 2` unless `k = j = 0` (effective Baker bound for the primes `3, 2`). -/
theorem lam23_ne_zero {k j : ℤ} (h : k ≠ 0 ∨ j ≠ 0) : lam23 k j ≠ 0 := by
  have hinj : Function.Injective ![(3 : ℕ), 2] := by
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all
  have hpr : ∀ i, (![(3 : ℕ), 2] i).Prime := by intro i; fin_cases i <;> norm_num
  obtain ⟨c₀, C₀, hc₀, -, hB⟩ := RHTower.Matveev.effectiveBakerBound_holds ![3, 2] hinj hpr
  have hν : (![k, -j] : Fin 2 → ℤ) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 0
    have h2 := congrFun h0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h1 h2
    rcases h with h | h <;> omega
  have hb := hB _ hν
  have hform : RHTower.Matveev.primeLogForm ![3, 2] ![k, -j] = lam23 k j := by
    unfold RHTower.Matveev.primeLogForm lam23
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg, Nat.cast_ofNat]
    ring
  rw [hform] at hb
  intro h0
  rw [h0, abs_zero] at hb
  exact absurd hb (not_le.mpr (by positivity))

theorem lam23_eq_mul (k j : ℤ) :
    lam23 k j = Real.log 2 * (k * (Real.log 3 / Real.log 2) - j) := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold lam23; field_simp

/-- **A uniform gap below each coefficient bound.** -/
theorem exists_lam23_gap (K : ℕ) :
    ∃ η > 0, ∀ k j : ℤ, k ≠ 0 → k.natAbs ≤ K → η ≤ |lam23 k j| := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ξ := Real.log 3 / Real.log 2 with hξ
  -- for fixed `k ≠ 0`, `|Λ(k, j)| ≥ log 2 · |kξ − round(kξ)| > 0`
  have hval : ∀ k : ℤ, k ≠ 0 → 0 < Real.log 2 * |k * ξ - round (k * ξ)| := by
    intro k hk
    refine mul_pos hl2 (abs_pos.mpr fun h0 => ?_)
    refine lam23_ne_zero (j := round (k * ξ)) (Or.inl hk) ?_
    rw [lam23_eq_mul, ← hξ, h0, mul_zero]
  have hlow : ∀ k j : ℤ, Real.log 2 * |k * ξ - round (k * ξ)| ≤ |lam23 k j| := by
    intro k j
    rw [lam23_eq_mul, ← hξ, abs_mul, abs_of_pos hl2]
    exact mul_le_mul_of_nonneg_left (round_le _ j) hl2.le
  induction K with
  | zero => exact ⟨1, one_pos, fun k j hk hK => by omega⟩
  | succ K ih =>
    obtain ⟨η, hη, h⟩ := ih
    have hp : ((K : ℤ) + 1) ≠ 0 := by omega
    have hm : -((K : ℤ) + 1) ≠ 0 := by omega
    refine ⟨min η (min (Real.log 2 * |((K : ℤ) + 1 : ℤ) * ξ - round ((((K : ℤ) + 1 : ℤ) : ℝ) * ξ)|)
      (Real.log 2 * |((-((K : ℤ) + 1) : ℤ) : ℝ) * ξ - round ((((-((K : ℤ) + 1)) : ℤ) : ℝ) * ξ)|)),
      lt_min hη (lt_min (hval _ hp) (hval _ hm)), fun k j hk hK => ?_⟩
    rcases (show k.natAbs ≤ K ∨ k = (K : ℤ) + 1 ∨ k = -((K : ℤ) + 1) by omega) with h1 | h1 | h1
    · exact (min_le_left _ _).trans (h k j hk h1)
    · subst h1
      exact (min_le_right _ _).trans ((min_le_left _ _).trans (hlow _ j))
    · subst h1
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (hlow _ j))

/-- **Small positive values with large coefficient.** -/
theorem exists_small_positive_lam23 {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ k j : ℤ, K < k.natAbs ∧ 0 < lam23 k j ∧ lam23 k j < ε := by
  obtain ⟨η, hη, hgap⟩ := exists_lam23_gap K
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmin : 0 < min ε η := lt_min hε hη
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log 2 / min ε η)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  obtain ⟨j, k, hk0, -, hdir⟩ := Real.exists_int_int_abs_mul_sub_le (Real.log 3 / Real.log 2) hN0
  have hlam : |lam23 k j| ≤ Real.log 2 / (N + 1) := by
    rw [lam23_eq_mul, abs_mul, abs_of_pos hl2]
    calc Real.log 2 * |(k : ℝ) * (Real.log 3 / Real.log 2) - j| ≤ Real.log 2 * (1 / (N + 1)) :=
          mul_le_mul_of_nonneg_left hdir hl2.le
      _ = Real.log 2 / (N + 1) := by ring
  have hsmall : |lam23 k j| < min ε η := by
    refine hlam.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hmin] at hN
    nlinarith
  have hK : K < k.natAbs := by
    by_contra hle
    push Not at hle
    have := hgap k j (by omega) hle
    linarith [min_le_right ε η]
  have hne := lam23_ne_zero (j := j) (Or.inl (by omega : k ≠ 0))
  have hε' := (abs_lt.mp (hsmall.trans_le (min_le_left _ _)))
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact ⟨-k, -j, by rwa [Int.natAbs_neg], by rw [lam23_neg]; linarith,
      by rw [lam23_neg]; linarith⟩
  · exact ⟨k, j, hK, hpos, hε'.2⟩

/-- One step of the construction: a pair with coefficient above `3|k| + 1` and value in
`(0, e^{−|k|}/8)`. -/
def stepPair (n : ℤ × ℤ) : ℤ × ℤ :=
  (Classical.choose (exists_small_positive_lam23
      (ε := Real.exp (-(n.1.natAbs : ℝ)) / 8) (by positivity) (3 * n.1.natAbs + 1)),
    Classical.choose (Classical.choose_spec (exists_small_positive_lam23
      (ε := Real.exp (-(n.1.natAbs : ℝ)) / 8) (by positivity) (3 * n.1.natAbs + 1))))

theorem stepPair_spec (n : ℤ × ℤ) :
    3 * n.1.natAbs + 1 < (stepPair n).1.natAbs ∧ 0 < lam23 (stepPair n).1 (stepPair n).2 ∧
      lam23 (stepPair n).1 (stepPair n).2 < Real.exp (-(n.1.natAbs : ℝ)) / 8 :=
  Classical.choose_spec (Classical.choose_spec (exists_small_positive_lam23
      (ε := Real.exp (-(n.1.natAbs : ℝ)) / 8) (by positivity) (3 * n.1.natAbs + 1)))

/-- The pairs `(k_n, j_n)`. -/
def pairSeq : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => pairSeq n + stepPair (pairSeq n)

/-- The values `Λ(k_n, j_n)`. -/
def lamSeq (n : ℕ) : ℝ := lam23 (pairSeq n).1 (pairSeq n).2

theorem lamSeq_succ (n : ℕ) :
    lamSeq (n + 1) = lamSeq n + lam23 (stepPair (pairSeq n)).1 (stepPair (pairSeq n)).2 := by
  simp only [lamSeq, pairSeq, Prod.fst_add, Prod.snd_add, lam23_add]

theorem natAbs_pairSeq_succ (n : ℕ) :
    (pairSeq n).1.natAbs + 1 ≤ (pairSeq (n + 1)).1.natAbs := by
  have hs := (stepPair_spec (pairSeq n)).1
  have h := Int.natAbs_add_le ((pairSeq n).1 + (stepPair (pairSeq n)).1) (-(pairSeq n).1)
  rw [add_neg_cancel_comm, Int.natAbs_neg] at h
  simp only [pairSeq, Prod.fst_add]
  omega

theorem le_natAbs_pairSeq (n : ℕ) : n ≤ (pairSeq n).1.natAbs := by
  induction n with
  | zero => omega
  | succ n ih => have := natAbs_pairSeq_succ n; omega

theorem lamSeq_lt_succ (n : ℕ) : lamSeq n < lamSeq (n + 1) := by
  rw [lamSeq_succ]; linarith [(stepPair_spec (pairSeq n)).2.1]

/-- Telescoping tail bound: `Λ_{n+m} − Λ_n ≤ e^{−|k_n|}/4 − e^{−|k_{n+m}|}/4`. -/
theorem lamSeq_tail (n m : ℕ) :
    lamSeq (n + m) - lamSeq n ≤ Real.exp (-((pairSeq n).1.natAbs : ℝ)) / 4 -
      Real.exp (-((pairSeq (n + m)).1.natAbs : ℝ)) / 4 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, lamSeq_succ]
    have hinc := (stepPair_spec (pairSeq (n + m))).2.2
    have hgrow := natAbs_pairSeq_succ (n + m)
    have hexp : Real.exp (-((pairSeq (n + m + 1)).1.natAbs : ℝ)) ≤
        Real.exp (-((pairSeq (n + m)).1.natAbs : ℝ)) / 2 := by
      have h1 : (((pairSeq (n + m)).1.natAbs : ℝ) + 1) ≤ ((pairSeq (n + m + 1)).1.natAbs : ℝ) := by
        exact_mod_cast hgrow
      have h2 : Real.exp (-((pairSeq (n + m + 1)).1.natAbs : ℝ)) ≤
          Real.exp (-(((pairSeq (n + m)).1.natAbs : ℝ) + 1)) := Real.exp_le_exp.mpr (by linarith)
      rw [neg_add, Real.exp_add] at h2
      have he : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.add_one_le_exp (1 : ℝ); norm_num at this ⊢; linarith
      have hpos := Real.exp_pos (-((pairSeq (n + m)).1.natAbs : ℝ))
      nlinarith
    linarith

/-- **A Liouville angle.** -/
theorem exists_liouville_angle :
    ∃ L : ℝ, ∀ n : ℕ, 0 < L - lamSeq n ∧
      L - lamSeq n ≤ Real.exp (-((pairSeq n).1.natAbs : ℝ)) / 4 := by
  have hmono : Monotone lamSeq := monotone_nat_of_le_succ fun n => (lamSeq_lt_succ n).le
  have hbdd : BddAbove (Set.range lamSeq) := by
    refine ⟨lamSeq 0 + 1 / 4, ?_⟩
    rintro _ ⟨m, rfl⟩
    have := lamSeq_tail 0 m
    rw [zero_add] at this
    have h0 : (pairSeq 0).1.natAbs = 0 := rfl
    rw [h0, Nat.cast_zero, neg_zero, Real.exp_zero] at this
    linarith [Real.exp_pos (-((pairSeq m).1.natAbs : ℝ))]
  refine ⟨⨆ i, lamSeq i, fun n => ⟨?_, ?_⟩⟩
  · have := le_ciSup hbdd (n + 1)
    linarith [lamSeq_lt_succ n]
  · have : (⨆ i, lamSeq i) ≤ lamSeq n + Real.exp (-((pairSeq n).1.natAbs : ℝ)) / 4 := by
      refine ciSup_le fun m => ?_
      rcases le_total m n with hmn | hnm
      · linarith [hmono hmn, Real.exp_pos (-((pairSeq n).1.natAbs : ℝ))]
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
        linarith [lamSeq_tail n r, Real.exp_pos (-((pairSeq (n + r)).1.natAbs : ℝ))]
    linarith

/-- The pure carrier `(1 − 2^{−s})(1 − 2cos θ · 3^{−s} + 3^{−2s})`. -/
def realPureCarrier (θ : ℝ) (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-s)) * (1 - ((2 * Real.cos θ : ℝ) : ℂ) * (3 : ℂ) ^ (-s) + ((3 : ℂ) ^ (-s)) ^ 2)

/-- The points `i(θ + 2πj)/log 3` are zeros of the second factor. -/
theorem realPureCarrier_second_zero (θ : ℝ) (j : ℤ) :
    realPureCarrier θ (((θ + 2 * Real.pi * j) / Real.log 3 : ℝ) * I) = 0 := by
  have hl3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hl3c : ((Real.log 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl3
  have hw : (3 : ℂ) ^ (-((((θ + 2 * Real.pi * j) / Real.log 3 : ℝ) : ℂ) * I)) =
      Complex.exp (-(θ * I)) := by
    rw [cpow_def_of_ne_zero (by norm_num), show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_log (by norm_num)]
    have : ((Real.log 3 : ℝ) : ℂ) * -((((θ + 2 * Real.pi * j) / Real.log 3 : ℝ) : ℂ) * I) =
        -(θ * I) + ((-j : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  unfold realPureCarrier
  rw [hw]
  apply mul_eq_zero_of_right
  have hcos : ((2 * Real.cos θ : ℝ) : ℂ) = Complex.exp (θ * I) + Complex.exp (-θ * I) := by
    push_cast; rw [← Complex.ofReal_cos, ← Complex.two_cos]; push_cast; ring
  rw [hcos, neg_mul]
  have h1 : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination -h1

/-- **Real Satake angles defeat polynomial repulsion.** There is `θ` such that the pure carrier
`(1 − 2^{−s})(1 − 2cos θ · 3^{−s} + 3^{−2s})` satisfies no collide-or-repel law at polynomial
scale: for all `c, C > 0` there are `T ≥ 1` and distinct zeros of height `≤ T` at distance
`< c T^{−C}`. -/
theorem real_pure_carrier_not_polynomial_repulsion :
    ∃ θ : ℝ, ∀ c C : ℝ, 0 < c → 0 < C → ∃ T : ℝ, 1 ≤ T ∧ ∃ ρ ρ' : ℂ,
      realPureCarrier θ ρ = 0 ∧ realPureCarrier θ ρ' = 0 ∧ |ρ.im| ≤ T ∧ |ρ'.im| ≤ T ∧ ρ ≠ ρ' ∧
        ‖ρ - ρ'‖ < c * T ^ (-C) := by
  obtain ⟨L, hL⟩ := exists_liouville_angle
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set θ : ℝ := 2 * Real.pi * L / Real.log 2 with hθ
  refine ⟨θ, fun c C hc hC => ?_⟩
  set A : ℝ := 2 * Real.pi / Real.log 2 with hA
  set B : ℝ := 2 * Real.pi / (Real.log 2 * Real.log 3) + 1 with hB
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by positivity
  set K : ℝ := Real.pi / (2 * (Real.log 2 * Real.log 3)) with hK
  have hK0 : 0 < K := by positivity
  -- `x^C e^{−x}` is eventually below `c / (K (A+B)^C)`
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C 1 one_pos
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < c / (K * (A + B) ^ C))))
  obtain ⟨n, hn⟩ := exists_nat_gt (max X₀ 1)
  set k := (pairSeq n).1 with hk
  set j := (pairSeq n).2 with hj
  set x : ℝ := (k.natAbs : ℝ) with hx
  have hxn : (n : ℝ) ≤ x := by rw [hx]; exact_mod_cast le_natAbs_pairSeq n
  have hx1 : 1 ≤ x := by linarith [le_max_right X₀ 1]
  have hxX : X₀ ≤ x := by linarith [le_max_left X₀ 1]
  obtain ⟨hδ0, hδ⟩ := hL n
  set δ := L - lamSeq n with hδdef
  set ρ : ℂ := colPt 2 k
  set ρ' : ℂ := (((θ + 2 * Real.pi * j) / Real.log 3 : ℝ) : ℂ) * I
  have hdist : ρ - ρ' = ((-(2 * Real.pi * δ / (Real.log 2 * Real.log 3)) : ℝ) : ℂ) * I := by
    simp only [ρ, ρ', colPt, ← sub_mul, ← ofReal_sub]
    congr 2
    rw [hδdef, lamSeq, ← hk, ← hj, lam23, hθ]
    push_cast
    field_simp
    ring
  have hnorm : ‖ρ - ρ'‖ = 2 * Real.pi * δ / (Real.log 2 * Real.log 3) := by
    rw [hdist, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)]
  have hρim : |ρ.im| = A * x := by
    rw [colPt_im, Nat.cast_ofNat, abs_div, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hl2, hA, hx,
      Nat.cast_natAbs, Int.cast_abs]
    ring
  set T : ℝ := A * x + B with hT
  have hT1 : 1 ≤ T := by rw [hT, hB]; have : 0 ≤ A * x := by positivity
                         have : 0 ≤ 2 * Real.pi / (Real.log 2 * Real.log 3) := by positivity
                         linarith
  have hδ1 : 2 * Real.pi * δ / (Real.log 2 * Real.log 3) ≤ 2 * Real.pi / (Real.log 2 * Real.log 3) := by
    have : δ ≤ 1 := by
      have := Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)
      rw [hx] at this; linarith
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Real.pi_pos]
  refine ⟨T, hT1, ρ, ρ', ?_, realPureCarrier_second_zero θ j, ?_, ?_, ?_, ?_⟩
  · unfold realPureCarrier
    have h := (one_sub_cpow_neg_eq_zero_iff (p := 2) (by norm_num) ρ).mpr ⟨k, rfl⟩
    push_cast at h
    rw [h, zero_mul]
  · rw [hρim, hT]; linarith
  · have h1 : |ρ'.im| ≤ |ρ.im| + ‖ρ - ρ'‖ := by
      have := abs_im_le_norm (ρ - ρ')
      rw [sub_im] at this
      have := abs_sub_abs_le_abs_sub ρ'.im ρ.im
      rw [abs_sub_comm ρ'.im] at this
      linarith
    rw [hρim, hnorm] at h1
    rw [hT, hB]; linarith
  · intro heq
    have : ‖ρ - ρ'‖ = 0 := by rw [heq, sub_self, norm_zero]
    rw [hnorm] at this
    have : 0 < 2 * Real.pi * δ / (Real.log 2 * Real.log 3) := by positivity
    linarith
  · -- `‖ρ − ρ'‖ ≤ K e^{−x} < c T^{−C}`
    have hT0 : 0 < T := by linarith
    have hTC : T ^ C ≤ (A + B) ^ C * x ^ C := by
      rw [← Real.mul_rpow (by positivity) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) (by rw [hT]; nlinarith) hC.le
    have hsmall := hX₀ x hxX
    rw [neg_one_mul] at hsmall
    have hdist' : ‖ρ - ρ'‖ ≤ K * Real.exp (-x) := by
      rw [hnorm, hK]
      have : δ ≤ Real.exp (-x) / 4 := by rw [hx]; exact hδ
      rw [div_le_iff₀ (by positivity)]
      have h4 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      have : Real.pi / (2 * (Real.log 2 * Real.log 3)) * Real.exp (-x) * (Real.log 2 * Real.log 3)
          = Real.pi * Real.exp (-x) / 2 := by field_simp
      rw [this]; linarith
    have hTCpos : 0 < T ^ C := Real.rpow_pos_of_pos hT0 C
    rw [Real.rpow_neg hT0.le, ← div_eq_mul_inv, lt_div_iff₀ hTCpos]
    have hAB : 0 < (A + B) ^ C := Real.rpow_pos_of_pos (by linarith) C
    calc ‖ρ - ρ'‖ * T ^ C ≤ K * Real.exp (-x) * ((A + B) ^ C * x ^ C) :=
          mul_le_mul hdist' hTC hTCpos.le (by positivity)
      _ = K * (A + B) ^ C * (x ^ C * Real.exp (-x)) := by ring
      _ < K * (A + B) ^ C * (c / (K * (A + B) ^ C)) :=
          mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = c := by field_simp

end GaloisForLFunctions.ArithmeticDiscreteness
