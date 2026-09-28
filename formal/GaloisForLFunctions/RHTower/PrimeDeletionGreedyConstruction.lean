import GaloisForLFunctions.RHTower.PrimeDeletionResidueQuantization
import GaloisForLFunctions.RHTower.Sieve.ShortIntervalThetaEveryWindow

/-!
# Deleting primes with a prescribed Chebyshev mass

For `0 < κ < 1` the greedy rule — delete the prime `p` exactly when the deleted mass stays at or
below `p^κ/κ` — produces a set `Q` of primes with

`θ_Q(x) = ∑_{p ≤ x, p ∈ Q} log p = x^κ/κ + O(x^{κ-1+α} + log x)`,

whenever every window satisfies the short-interval prime-mass bound
`θ(y + L) − θ(y) ≥ (L − (y+L)^α)/c`.  Indeed the deficit `x^κ/κ − θ_Q(x)` is below `log p` at
every rejected prime `p`, and after the last rejected prime every prime is deleted: over a gap
shorter than `2x^α` the target grows by at most `4x^{κ-1+α}`, and over a longer gap the prime mass
outgrows the target.

Splitting the deleted Chebyshev function by prime powers,
`ψ_Q(x) = θ_Q(x) + θ_Q(x^{1/2}) + O(x^{κ/3} log² x)`, this gives the expansion
`ψ_Q(x) = (x^κ + x^{κ/2})/κ + O(x^η)` with some `η < κ/2` as soon as `α < 1 − κ/2`.

With the corpus window bound (any `α > 0.701299`, `c = 8192`) this covers every
`κ < 2(1 − 0.701299)`, in particular a range of `κ > 1/2`.  For each such `κ` the deletion `ℙ ∖ Q`
has integers with no power saving below `x^{κ/2}`
(`not_isBigO_qFreeCount_of_odd`): a concrete instance of the half-dimension uncertainty.
-/

open Filter Topology Asymptotics

namespace RHTower

noncomputable section

namespace PrimeDeletion

open scoped Classical in
/-- The deleted primes' `θ`: `∑_{p ≤ y, p ∈ Q} log p`. -/
def deletedTheta (Q : Set ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, if p ∈ Q then Real.log p else 0

theorem deletedTheta_nonneg (Q : Set ℕ) (y : ℝ) : 0 ≤ deletedTheta Q y := by
  classical
  unfold deletedTheta
  refine Finset.sum_nonneg fun p hp => ?_
  split_ifs
  · exact Real.log_natCast_nonneg p
  · exact le_rfl

theorem deletedTheta_mono (Q : Set ℕ) : Monotone (deletedTheta Q) := by
  classical
  intro a b hab
  unfold deletedTheta
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
  · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc le_rfl (Nat.floor_le_floor hab))
  · split_ifs
    · exact Real.log_natCast_nonneg p
    · exact le_rfl

/-- **Prime-power splitting.**  `ψ_Q(x) = ∑_{k ≥ 1} θ_Q(x^{1/k})`. -/
theorem deletedChebyshev_eq_sum_deletedTheta (Q : Set ℕ) {x : ℝ} (hx : 0 ≤ x) :
    deletedChebyshev Q x =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, deletedTheta Q (x ^ ((1 : ℝ) / k)) := by
  classical
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h1 : deletedChebyshev Q x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with IsPrimePow n,
      Real.log n.minFac * (1 - qFreeIndicator Q n) := by
    rw [deletedChebyshev, Finset.sum_filter, hIcc]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [deletedVonMangoldt, ArithmeticFunction.vonMangoldt_apply]
    split_ifs <;> simp
  rw [h1, Chebyshev.sum_PrimePow_eq_sum_sum _ hx]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  rw [deletedTheta]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  rw [hpp.pow_minFac hk0]
  have hq : qFreeIndicator Q (p ^ k) = if p ∈ Q then 0 else 1 := by
    unfold qFreeIndicator
    rw [Nat.primeFactors_prime_pow hk0 hpp]
    by_cases hpQ : p ∈ Q
    · rw [if_neg, if_pos hpQ]
      rintro ⟨_, h⟩
      exact h p (Finset.mem_singleton_self p) hpQ
    · rw [if_pos, if_neg hpQ]
      refine ⟨pow_ne_zero _ hpp.ne_zero, fun q hq => ?_⟩
      rw [Finset.mem_singleton.mp hq]
      exact hpQ
  rw [hq]
  split_ifs <;> simp

/-! ### The greedy deletion -/

/-- The target `t^κ/κ` for the deleted mass. -/
def greedyTarget (κ t : ℝ) : ℝ := t ^ κ / κ

open scoped Classical in
/-- The greedy deleted mass: a prime is deleted when the mass stays below the target. -/
def greedyMass (κ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      if (n + 1).Prime ∧
          greedyMass κ n + Real.log ((n + 1 : ℕ) : ℝ) ≤ greedyTarget κ ((n + 1 : ℕ) : ℝ) then
        greedyMass κ n + Real.log ((n + 1 : ℕ) : ℝ)
      else greedyMass κ n

/-- The greedily deleted primes. -/
def greedyDeletion (κ : ℝ) : Set ℕ :=
  {p | p.Prime ∧ greedyMass κ (p - 1) + Real.log (p : ℝ) ≤ greedyTarget κ (p : ℝ)}

theorem greedyDeletion_prime {κ : ℝ} {p : ℕ} (hp : p ∈ greedyDeletion κ) : p.Prime := hp.1

open scoped Classical in
theorem greedyMass_succ (κ : ℝ) (n : ℕ) :
    greedyMass κ (n + 1) =
      greedyMass κ n + if n + 1 ∈ greedyDeletion κ then Real.log ((n + 1 : ℕ) : ℝ) else 0 := by
  classical
  have hmem : n + 1 ∈ greedyDeletion κ ↔ (n + 1).Prime ∧
      greedyMass κ n + Real.log ((n + 1 : ℕ) : ℝ) ≤ greedyTarget κ ((n + 1 : ℕ) : ℝ) := by
    simp [greedyDeletion]
  rw [greedyMass]
  by_cases h : (n + 1).Prime ∧
      greedyMass κ n + Real.log ((n + 1 : ℕ) : ℝ) ≤ greedyTarget κ ((n + 1 : ℕ) : ℝ)
  · rw [if_pos h, if_pos (hmem.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hmem.mp h')), add_zero]

open scoped Classical in
theorem deletedTheta_natCast_succ (Q : Set ℕ) (n : ℕ) :
    deletedTheta Q ((n + 1 : ℕ) : ℝ) =
      deletedTheta Q (n : ℝ) + if n + 1 ∈ Q ∧ (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) else 0 := by
  classical
  unfold deletedTheta
  rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  congr 1
  by_cases h1 : (n + 1).Prime <;> by_cases h2 : n + 1 ∈ Q <;> simp [h1, h2]

theorem theta_natCast_succ (n : ℕ) :
    Chebyshev.theta ((n + 1 : ℕ) : ℝ) =
      Chebyshev.theta (n : ℝ) + if (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) else 0 := by
  classical
  unfold Chebyshev.theta
  rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_succ_top (Nat.zero_le n)]

/-- The deleted `θ` of the greedy set is the greedy mass. -/
theorem deletedTheta_greedyDeletion (κ : ℝ) (n : ℕ) :
    deletedTheta (greedyDeletion κ) (n : ℝ) = greedyMass κ n := by
  classical
  induction n with
  | zero => simp [deletedTheta, greedyMass]
  | succ n ih =>
      rw [deletedTheta_natCast_succ, ih, greedyMass_succ]
      congr 1
      by_cases h : n + 1 ∈ greedyDeletion κ
      · rw [if_pos h, if_pos ⟨h, h.1⟩]
      · rw [if_neg h, if_neg (fun h' => h h'.1)]

theorem greedyTarget_nonneg {κ : ℝ} (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ greedyTarget κ t :=
  div_nonneg (Real.rpow_nonneg ht κ) hκ.le

theorem greedyTarget_mono {κ : ℝ} (hκ : 0 < κ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    greedyTarget κ s ≤ greedyTarget κ t :=
  div_le_div_of_nonneg_right (Real.rpow_le_rpow hs hst hκ.le) hκ.le

/-- The greedy mass never exceeds the target. -/
theorem greedyMass_le {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    greedyMass κ n ≤ greedyTarget κ (n : ℝ) := by
  classical
  induction n with
  | zero =>
      simp [greedyMass, greedyTarget, Real.zero_rpow hκ.ne']
  | succ n ih =>
      rw [greedyMass]
      split_ifs with h
      · exact h.2
      · exact ih.trans (greedyTarget_mono hκ (Nat.cast_nonneg n) (by push_cast; linarith))

/-- At a rejected prime the deficit is below `log p`. -/
theorem deficit_lt_log_of_rejected {κ : ℝ} {m : ℕ} (hm : m.Prime) (hrej : m ∉ greedyDeletion κ) :
    greedyTarget κ (m : ℝ) - greedyMass κ m < Real.log (m : ℝ) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := hm.pos; omega⟩
  have hnot : ¬(greedyMass κ k + Real.log ((k + 1 : ℕ) : ℝ) ≤ greedyTarget κ ((k + 1 : ℕ) : ℝ)) := by
    intro h
    exact hrej ⟨hm, by simpa using h⟩
  rw [greedyMass_succ, if_neg hrej, add_zero]
  push_cast at hnot ⊢
  linarith

/-- After the last rejected prime, the greedy mass follows `θ`. -/
theorem greedyMass_sub_eq_theta_sub {κ : ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hall : ∀ k, m < k → k ≤ n → k.Prime → k ∈ greedyDeletion κ) :
    greedyMass κ n - greedyMass κ m = Chebyshev.theta (n : ℝ) - Chebyshev.theta (m : ℝ) := by
  classical
  induction n, hmn using Nat.le_induction with
  | base => ring
  | succ n hmn ih =>
      have ih' := ih fun k hk1 hk2 hk3 => hall k hk1 (by omega) hk3
      rw [greedyMass_succ, theta_natCast_succ]
      by_cases hp : (n + 1).Prime
      · rw [if_pos (hall (n + 1) (by omega) le_rfl hp), if_pos hp]
        linarith
      · have hnot : n + 1 ∉ greedyDeletion κ := fun h => hp h.1
        rw [if_neg hnot, if_neg hp]
        linarith

/-- Concavity of `t^κ`: `n^κ − m^κ ≤ κ m^{κ-1} (n − m)`. -/
theorem rpow_sub_rpow_le_concave {κ m n : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hm : 0 < m) (hmn : m ≤ n) :
    n ^ κ - m ^ κ ≤ κ * m ^ (κ - 1) * (n - m) := by
  have hs : -1 ≤ (n - m) / m := by
    have : 0 ≤ (n - m) / m := div_nonneg (by linarith) hm.le
    linarith
  have hB := rpow_one_add_le_one_add_mul_self hs hκ0 hκ1
  have hsplit : n = m * (1 + (n - m) / m) := by field_simp; ring
  have hpow : n ^ κ = m ^ κ * (1 + (n - m) / m) ^ κ := by
    conv_lhs => rw [hsplit]
    exact Real.mul_rpow hm.le (by linarith)
  have hmk : m ^ κ = m ^ (κ - 1) * m := by
    rw [← Real.rpow_add_one hm.ne']
    ring_nf
  rw [hpow]
  have hmκ0 : 0 ≤ m ^ κ := Real.rpow_nonneg hm.le κ
  calc m ^ κ * (1 + (n - m) / m) ^ κ - m ^ κ ≤ m ^ κ * (1 + κ * ((n - m) / m)) - m ^ κ := by
        gcongr
    _ = κ * (m ^ κ / m) * (n - m) := by ring
    _ = κ * m ^ (κ - 1) * (n - m) := by
        rw [hmk]
        field_simp

/-- `(n/2)^{κ-1} ≤ 2 n^{κ-1}` for `κ ≤ 1`. -/
theorem half_rpow_le {κ n : ℝ} (hκ0 : 0 ≤ κ) (hn : 0 < n) :
    (n / 2) ^ (κ - 1) ≤ 2 * n ^ (κ - 1) := by
  rw [Real.div_rpow hn.le (by norm_num)]
  have h2 : (2 : ℝ) ^ (κ - 1) ≥ 1 / 2 := by
    have : (2 : ℝ) ^ (κ - 1) ≥ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at this
    linarith
  have hpos : 0 < (2 : ℝ) ^ (κ - 1) := by positivity
  rw [div_le_iff₀ hpos]
  have hn0 : 0 ≤ n ^ (κ - 1) := Real.rpow_nonneg hn.le _
  nlinarith

/-- **Deficit bound at one height.**  Given the window bound and the listed size conditions on `n`,
the greedy deficit at `n` is at most `log n + 4 n^{κ-1+α}`. -/
theorem greedy_deficit_le_of {κ α c X : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hc : 0 < c) (hX0 : 0 ≤ X)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / c ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    {n : ℕ} (h1 : (2 : ℝ) ≤ n) (h2 : 2 * (n : ℝ) ^ α ≤ n / 2)
    (h3 : 2 * (n : ℝ) ^ (κ - 1) ≤ 1 / (2 * c))
    (h4 : (n : ℝ) ^ κ / κ + ((n : ℝ) ^ α + X) / c ≤ n / (2 * c)) (h5 : X ≤ (n : ℝ) / 2) :
    greedyTarget κ (n : ℝ) - greedyMass κ n ≤ Real.log n + 4 * (n : ℝ) ^ (κ - 1 + α) := by
  classical
  have hn0 : (0 : ℝ) < n := by linarith
  set rej := (Finset.range (n + 1)).filter (fun m => m.Prime ∧ m ∉ greedyDeletion κ) with hrej
  obtain ⟨m, hmn, hall, hDm⟩ : ∃ m : ℕ, m ≤ n ∧
      (∀ k, m < k → k ≤ n → k.Prime → k ∈ greedyDeletion κ) ∧
      greedyTarget κ (m : ℝ) - greedyMass κ m ≤ Real.log n := by
    by_cases hne : rej.Nonempty
    · have hmem := Finset.mem_filter.mp (rej.max'_mem hne)
      refine ⟨rej.max' hne, ?_, ?_, ?_⟩
      · have := Finset.mem_range.mp hmem.1
        omega
      · intro k hk1 hk2 hk3
        by_contra hk
        have hkrej : k ∈ rej := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk3, hk⟩
        have := rej.le_max' k hkrej
        omega
      · have hlt := deficit_lt_log_of_rejected hmem.2.1 hmem.2.2
        have hmpos : (0 : ℝ) < (rej.max' hne : ℕ) := by exact_mod_cast hmem.2.1.pos
        have hmle : ((rej.max' hne : ℕ) : ℝ) ≤ n := by
          have := Finset.mem_range.mp hmem.1
          exact_mod_cast (by omega : rej.max' hne ≤ n)
        have hle : Real.log ((rej.max' hne : ℕ) : ℝ) ≤ Real.log n := Real.log_le_log hmpos hmle
        linarith
    · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · intro k _ hk2 hk3
        by_contra hk
        exact hne ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk3, hk⟩⟩
      · simp only [greedyTarget, Nat.cast_zero, Real.zero_rpow hκ0.ne', zero_div, greedyMass,
          sub_zero]
        exact Real.log_nonneg (by linarith)
  have hsub := greedyMass_sub_eq_theta_sub hmn hall
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hθmono : Chebyshev.theta (m : ℝ) ≤ Chebyshev.theta (n : ℝ) := Chebyshev.theta_mono hmnR
  have hTm0 : 0 ≤ greedyTarget κ (m : ℝ) := greedyTarget_nonneg hκ0 (Nat.cast_nonneg m)
  have hnα : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg hn0.le α
  have hnκα : 0 ≤ (n : ℝ) ^ (κ - 1 + α) := Real.rpow_nonneg hn0.le _
  -- the target increment near `n`
  have hincr : ∀ {y : ℝ}, (n : ℝ) / 2 ≤ y → y ≤ n →
      greedyTarget κ (n : ℝ) - greedyTarget κ y ≤ 2 * (n : ℝ) ^ (κ - 1) * (n - y) := by
    intro y hy1 hy2
    have hy0 : 0 < y := by linarith
    have hconc := rpow_sub_rpow_le_concave hκ0.le hκ1.le hy0 hy2
    have hmono : y ^ (κ - 1) ≤ ((n : ℝ) / 2) ^ (κ - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hy1 (by linarith)
    have hhalf := half_rpow_le hκ0.le hn0
    unfold greedyTarget
    rw [← sub_div, div_le_iff₀ hκ0]
    calc (n : ℝ) ^ κ - y ^ κ ≤ κ * y ^ (κ - 1) * (n - y) := hconc
      _ ≤ κ * (2 * (n : ℝ) ^ (κ - 1)) * (n - y) := by
          have : 0 ≤ (n : ℝ) - y := by linarith
          have := hmono.trans hhalf
          gcongr
      _ = 2 * (n : ℝ) ^ (κ - 1) * (n - y) * κ := by ring
  have hkey : greedyTarget κ (n : ℝ) - greedyTarget κ (m : ℝ) -
      (Chebyshev.theta (n : ℝ) - Chebyshev.theta (m : ℝ)) ≤ 4 * (n : ℝ) ^ (κ - 1 + α) := by
    by_cases hA : (n : ℝ) - m ≤ 2 * (n : ℝ) ^ α
    · -- short final stretch
      have hmhalf : (n : ℝ) / 2 ≤ m := by linarith
      have hT := hincr hmhalf hmnR
      have hsplit : (n : ℝ) ^ (κ - 1 + α) = (n : ℝ) ^ (κ - 1) * (n : ℝ) ^ α :=
        Real.rpow_add hn0 _ _
      have hκn : 0 ≤ (n : ℝ) ^ (κ - 1) := Real.rpow_nonneg hn0.le _
      have : 2 * (n : ℝ) ^ (κ - 1) * ((n : ℝ) - m) ≤ 2 * (n : ℝ) ^ (κ - 1) * (2 * (n : ℝ) ^ α) := by
        gcongr
      nlinarith
    · rw [not_le] at hA
      by_cases hB : (n : ℝ) / 2 ≤ m
      · -- the prime mass outgrows the target
        have hmX : X ≤ (m : ℝ) := h5.trans hB
        have hw := hwin (m : ℝ) ((n : ℝ) - m) hmX (by linarith)
        rw [show (m : ℝ) + ((n : ℝ) - m) = n by ring] at hw
        have hT := hincr hB hmnR
        have hT' : 2 * (n : ℝ) ^ (κ - 1) * ((n : ℝ) - m) ≤ ((n : ℝ) - m) / (2 * c) := by
          have : 0 ≤ (n : ℝ) - m := by linarith
          calc 2 * (n : ℝ) ^ (κ - 1) * ((n : ℝ) - m) ≤ 1 / (2 * c) * ((n : ℝ) - m) := by gcongr
            _ = ((n : ℝ) - m) / (2 * c) := by ring
        have hfin : ((n : ℝ) - m) / (2 * c) - ((n : ℝ) - m - (n : ℝ) ^ α) / c ≤ 0 := by
          rw [div_sub_div _ _ (by positivity) hc.ne', div_nonpos_iff]
          right
          constructor
          · nlinarith
          · positivity
        linarith
      · -- a long final stretch starting far below `n`
        rw [not_le] at hB
        have hθlow : ((n : ℝ) / 2 - (n : ℝ) ^ α - X) / c ≤
            Chebyshev.theta (n : ℝ) - Chebyshev.theta (m : ℝ) := by
          by_cases hmX : X ≤ (m : ℝ)
          · have hw := hwin (m : ℝ) ((n : ℝ) - m) hmX (by linarith)
            rw [show (m : ℝ) + ((n : ℝ) - m) = n by ring] at hw
            refine le_trans ?_ hw
            apply div_le_div_of_nonneg_right _ hc.le
            linarith
          · rw [not_le] at hmX
            have hw := hwin X ((n : ℝ) - X) le_rfl (by linarith)
            rw [show X + ((n : ℝ) - X) = n by ring] at hw
            have hθX : Chebyshev.theta (m : ℝ) ≤ Chebyshev.theta X := Chebyshev.theta_mono hmX.le
            have : ((n : ℝ) / 2 - (n : ℝ) ^ α - X) / c ≤ ((n : ℝ) - X - (n : ℝ) ^ α) / c := by
              apply div_le_div_of_nonneg_right _ hc.le
              linarith
            linarith
        have hTn : greedyTarget κ (n : ℝ) ≤ ((n : ℝ) / 2 - (n : ℝ) ^ α - X) / c := by
          unfold greedyTarget
          have : ((n : ℝ) / 2 - (n : ℝ) ^ α - X) / c = (n : ℝ) / (2 * c) - ((n : ℝ) ^ α + X) / c := by
            field_simp
            ring
          rw [this]
          linarith
        linarith
  linarith

/-- **Deficit bound.**  Eventually the greedy deficit is at most `log n + 4 n^{κ-1+α}`. -/
theorem greedy_deficit_eventually {κ α c X : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hα1 : α < 1) (hc : 0 < c) (hX0 : 0 ≤ X)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / c ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∀ᶠ n : ℕ in atTop,
      greedyTarget κ (n : ℝ) - greedyMass κ n ≤ Real.log n + 4 * (n : ℝ) ^ (κ - 1 + α) := by
  -- the size conditions hold eventually along the reals
  have hlim1 : Tendsto (fun x : ℝ => x ^ (α - 1)) atTop (𝓝 0) := by
    simpa [neg_sub] using tendsto_rpow_neg_atTop (y := 1 - α) (by linarith)
  have hlim2 : Tendsto (fun x : ℝ => x ^ (κ - 1)) atTop (𝓝 0) := by
    simpa [neg_sub] using tendsto_rpow_neg_atTop (y := 1 - κ) (by linarith)
  have hlim3 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hc2 : 0 < 1 / (4 * c) := by positivity
  have hsum : Tendsto (fun x : ℝ => x ^ (κ - 1) / κ + x ^ (α - 1) / c + X / c * x⁻¹) atTop
      (𝓝 (0 / κ + 0 / c + X / c * 0)) :=
    ((hlim2.div_const κ).add (hlim1.div_const c)).add (hlim3.const_mul (X / c))
  simp only [zero_div, mul_zero, add_zero] at hsum
  have hE : ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ x ^ (α - 1) ≤ 1 / 4 ∧ x ^ (κ - 1) ≤ 1 / (4 * c) ∧
      x ^ (κ - 1) / κ + x ^ (α - 1) / c + X / c * x⁻¹ ≤ 1 / (2 * c) ∧ 2 * X ≤ x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hlim1.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1 / 4)),
      hlim2.eventually (ge_mem_nhds hc2), hsum.eventually (ge_mem_nhds (by positivity : (0:ℝ) < 1 / (2 * c))),
      eventually_ge_atTop (2 * X)] with x hx1 hx2 hx3 hx4 hx5
    exact ⟨hx1, hx2, hx3, hx4, hx5⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hE] with n hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hxα : (n : ℝ) ^ α = (n : ℝ) ^ (α - 1) * n := by
    rw [← Real.rpow_add_one hn0.ne']
    ring_nf
  have hxκ : (n : ℝ) ^ κ = (n : ℝ) ^ (κ - 1) * n := by
    rw [← Real.rpow_add_one hn0.ne']
    ring_nf
  refine greedy_deficit_le_of hκ0 hκ1 hc hX0 hwin h1 ?_ ?_ ?_ (by linarith)
  · rw [hxα]
    nlinarith
  · calc 2 * (n : ℝ) ^ (κ - 1) ≤ 2 * (1 / (4 * c)) := by linarith
      _ = 1 / (2 * c) := by field_simp; ring
  · have hmul : ((n : ℝ) ^ (κ - 1) / κ + (n : ℝ) ^ (α - 1) / c + X / c * (n : ℝ)⁻¹) * n ≤
        1 / (2 * c) * n := mul_le_mul_of_nonneg_right h4 hn0.le
    have hlhs : ((n : ℝ) ^ (κ - 1) / κ + (n : ℝ) ^ (α - 1) / c + X / c * (n : ℝ)⁻¹) * n =
        (n : ℝ) ^ κ / κ + ((n : ℝ) ^ α + X) / c := by
      rw [hxα, hxκ]
      field_simp
      ring
    rw [hlhs] at hmul
    calc (n : ℝ) ^ κ / κ + ((n : ℝ) ^ α + X) / c ≤ 1 / (2 * c) * n := hmul
      _ = n / (2 * c) := by ring

/-! ### The deleted Chebyshev expansion -/

theorem deletedTheta_eq_floor (Q : Set ℕ) (y : ℝ) :
    deletedTheta Q y = deletedTheta Q (⌊y⌋₊ : ℝ) := by
  simp [deletedTheta, Nat.floor_natCast]

/-- The greedy deleted `θ` stays below the target. -/
theorem deletedTheta_greedy_le {κ : ℝ} (hκ : 0 < κ) {y : ℝ} (hy : 0 ≤ y) :
    deletedTheta (greedyDeletion κ) y ≤ greedyTarget κ y := by
  rw [deletedTheta_eq_floor, deletedTheta_greedyDeletion]
  exact (greedyMass_le hκ _).trans (greedyTarget_mono hκ (Nat.cast_nonneg _) (Nat.floor_le hy))

/-- The greedy deleted `θ` follows the target up to `log y + 4 y^{κ-1+α} + 1`. -/
theorem greedy_theta_deficit_eventually {κ α c X : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hα1 : α < 1) (he : 0 ≤ κ - 1 + α) (hc : 0 < c) (hX0 : 0 ≤ X)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / c ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∀ᶠ y : ℝ in atTop, greedyTarget κ y - deletedTheta (greedyDeletion κ) y ≤
      Real.log y + 4 * y ^ (κ - 1 + α) + 1 := by
  filter_upwards [tendsto_nat_floor_atTop.eventually
      (greedy_deficit_eventually hκ0 hκ1 hα1 hc hX0 hwin),
    tendsto_nat_floor_atTop.eventually (eventually_ge_atTop 1), eventually_ge_atTop (1 : ℝ)]
    with y hdef hfl hy1
  set n := ⌊y⌋₊ with hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hfl
  have hny : (n : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyn : y < n + 1 := Nat.lt_floor_add_one y
  rw [deletedTheta_eq_floor, ← hn, deletedTheta_greedyDeletion]
  -- the target increment inside `[n, y]`
  have hTinc : greedyTarget κ y - greedyTarget κ (n : ℝ) ≤ 1 := by
    have hconc := rpow_sub_rpow_le_concave hκ0.le hκ1.le (by linarith) hny
    have hpow : (n : ℝ) ^ (κ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    unfold greedyTarget
    rw [← sub_div, div_le_iff₀ hκ0]
    have h0 : 0 ≤ (n : ℝ) ^ (κ - 1) := Real.rpow_nonneg (by linarith) _
    have hyn' : y - n ≤ 1 := by linarith
    have hy0 : 0 ≤ y - n := by linarith
    calc y ^ κ - (n : ℝ) ^ κ ≤ κ * (n : ℝ) ^ (κ - 1) * (y - n) := hconc
      _ ≤ κ * 1 * 1 := by gcongr
      _ = 1 * κ := by ring
  have hlog : Real.log (n : ℝ) ≤ Real.log y := Real.log_le_log (by linarith) hny
  have hpow : (n : ℝ) ^ (κ - 1 + α) ≤ y ^ (κ - 1 + α) :=
    Real.rpow_le_rpow (by linarith) hny he
  linarith

/-- **The greedy deletion has the prescribed Chebyshev expansion.**  If the window bound holds
with an exponent `α < 1 − κ/2`, then for some `η < κ/2`,
`ψ_Q(x) = (x^κ + x^{κ/2})/κ + O(x^η)`. -/
theorem greedy_chebyshev_expansion {κ α c X : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hα1 : α < 1) (he : 0 ≤ κ - 1 + α) (hακ : κ - 1 + α < κ / 2) (hc : 0 < c) (hX0 : 0 ≤ X)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / c ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∃ η < κ / 2, (fun x : ℝ => deletedChebyshev (greedyDeletion κ) x -
      (1 / κ) * (x ^ κ + x ^ (κ / 2))) =O[atTop] fun x => x ^ η := by
  classical
  set e := κ - 1 + α with he_def
  set Q := greedyDeletion κ with hQ
  set η := (max e (κ / 3) + κ / 2) / 2 with hη
  have hmax : max e (κ / 3) < κ / 2 := max_lt hακ (by linarith)
  have hηlt : η < κ / 2 := by rw [hη]; linarith
  have hηe : e < η := by rw [hη]; linarith [le_max_left e (κ / 3)]
  have hηk : κ / 3 < η := by rw [hη]; linarith [le_max_right e (κ / 3)]
  have hη0 : 0 < η := by linarith
  refine ⟨η, hηlt, ?_⟩
  have hD := greedy_theta_deficit_eventually hκ0 hκ1 hα1 he hc hX0 hwin
  have hDsqrt : ∀ᶠ x : ℝ in atTop, greedyTarget κ (x ^ ((1 : ℝ) / 2)) -
      deletedTheta Q (x ^ ((1 : ℝ) / 2)) ≤
        Real.log (x ^ ((1 : ℝ) / 2)) + 4 * (x ^ ((1 : ℝ) / 2)) ^ e + 1 :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually hD
  set C : ℝ := 3 / η + 10 + 1 / (Real.log 2 * κ * (η - κ / 3)) with hC
  refine IsBigO.of_bound C ?_
  filter_upwards [hD, hDsqrt, eventually_ge_atTop (4 : ℝ)] with x hx hxs hx4
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  -- the splitting
  set K := ⌊Real.log x / Real.log 2⌋₊ with hK
  have hK2 : 2 ≤ K := by
    rw [hK, Nat.le_floor_iff (div_nonneg hlogx hlog2.le), le_div_iff₀ hlog2]
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have := Real.log_le_log (by norm_num) hx4
    push_cast
    linarith
  have hKle : (K : ℝ) ≤ Real.log x / Real.log 2 := Nat.floor_le (div_nonneg hlogx hlog2.le)
  have h1mem : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have h2mem : 2 ∈ (Finset.Icc 1 K).erase 1 :=
    Finset.mem_erase.mpr ⟨by norm_num, Finset.mem_Icc.mpr ⟨by norm_num, hK2⟩⟩
  set f : ℕ → ℝ := fun k => deletedTheta Q (x ^ ((1 : ℝ) / k)) with hf
  have hsplit : deletedChebyshev Q x = f 1 + f 2 + ∑ k ∈ ((Finset.Icc 1 K).erase 1).erase 2, f k := by
    rw [deletedChebyshev_eq_sum_deletedTheta Q hx0.le, ← Finset.add_sum_erase _ _ h1mem,
      ← Finset.add_sum_erase _ _ h2mem]
    ring
  have hf1 : f 1 = deletedTheta Q x := by simp [hf]
  have hf2 : f 2 = deletedTheta Q (x ^ ((1 : ℝ) / 2)) := by simp [hf]
  -- the higher prime powers
  have hthird : x ^ ((1 : ℝ) / 3) ≥ 0 := Real.rpow_nonneg hx0.le _
  have hrest0 : 0 ≤ ∑ k ∈ ((Finset.Icc 1 K).erase 1).erase 2, f k :=
    Finset.sum_nonneg fun k _ => deletedTheta_nonneg Q _
  have hrest : ∑ k ∈ ((Finset.Icc 1 K).erase 1).erase 2, f k ≤
      Real.log x / Real.log 2 * (x ^ (κ / 3) / κ) := by
    have hterm : ∀ k ∈ ((Finset.Icc 1 K).erase 1).erase 2, f k ≤ x ^ (κ / 3) / κ := by
      intro k hk
      have hk3 : 3 ≤ k := by
        have h1 := Finset.mem_erase.mp hk
        have h2 := Finset.mem_erase.mp h1.2
        have h3 := (Finset.mem_Icc.mp h2.2).1
        omega
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hexp : (1 : ℝ) / k ≤ 1 / 3 := by
        rw [div_le_div_iff₀ hk0 (by norm_num)]
        have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
        linarith
      have hle : x ^ ((1 : ℝ) / k) ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow_of_exponent_le hx1 hexp
      calc f k ≤ deletedTheta Q (x ^ ((1 : ℝ) / 3)) := deletedTheta_mono Q hle
        _ ≤ greedyTarget κ (x ^ ((1 : ℝ) / 3)) := deletedTheta_greedy_le hκ0 hthird
        _ = x ^ (κ / 3) / κ := by
            unfold greedyTarget
            rw [← Real.rpow_mul hx0.le]
            ring_nf
    have hcard : ((((Finset.Icc 1 K).erase 1).erase 2).card : ℝ) ≤ Real.log x / Real.log 2 := by
      have h1 : (((Finset.Icc 1 K).erase 1).erase 2).card ≤ K := by
        calc (((Finset.Icc 1 K).erase 1).erase 2).card ≤ ((Finset.Icc 1 K).erase 1).card :=
              Finset.card_erase_le
          _ ≤ (Finset.Icc 1 K).card := Finset.card_erase_le
          _ = K := by simp
      calc ((((Finset.Icc 1 K).erase 1).erase 2).card : ℝ) ≤ K := by exact_mod_cast h1
        _ ≤ _ := hKle
    calc ∑ k ∈ ((Finset.Icc 1 K).erase 1).erase 2, f k
        ≤ ∑ _k ∈ ((Finset.Icc 1 K).erase 1).erase 2, x ^ (κ / 3) / κ := Finset.sum_le_sum hterm
      _ = ((((Finset.Icc 1 K).erase 1).erase 2).card : ℝ) * (x ^ (κ / 3) / κ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.log x / Real.log 2 * (x ^ (κ / 3) / κ) := by
          gcongr
  -- the two leading terms
  have hT1 : greedyTarget κ x = x ^ κ / κ := rfl
  have hT2 : greedyTarget κ (x ^ ((1 : ℝ) / 2)) = x ^ (κ / 2) / κ := by
    unfold greedyTarget
    rw [← Real.rpow_mul hx0.le]
    ring_nf
  have hup1 : deletedTheta Q x ≤ x ^ κ / κ := deletedTheta_greedy_le hκ0 hx0.le
  have hup2 : deletedTheta Q (x ^ ((1 : ℝ) / 2)) ≤ x ^ (κ / 2) / κ := by
    rw [← hT2]
    exact deletedTheta_greedy_le hκ0 (Real.rpow_nonneg hx0.le _)
  have hlogs : Real.log (x ^ ((1 : ℝ) / 2)) ≤ Real.log x := by
    rw [Real.log_rpow hx0]
    linarith
  have hpows : (x ^ ((1 : ℝ) / 2)) ^ e ≤ x ^ e := by
    rw [← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  -- the size of the error
  have herr : |deletedChebyshev Q x - 1 / κ * (x ^ κ + x ^ (κ / 2))| ≤
      2 * Real.log x + 8 * x ^ e + 2 + Real.log x / Real.log 2 * (x ^ (κ / 3) / κ) := by
    rw [hsplit, hf1, hf2]
    have hexp : 1 / κ * (x ^ κ + x ^ (κ / 2)) = x ^ κ / κ + x ^ (κ / 2) / κ := by ring
    rw [hexp, abs_le]
    rw [hT1] at hx
    rw [hT2] at hxs
    constructor <;> linarith
  -- compare each term with `x^η`
  have hxη : 1 ≤ x ^ η := Real.one_le_rpow hx1 hη0.le
  have hlogη : Real.log x ≤ x ^ η / η := Real.log_le_rpow_div hx0.le hη0
  have hxe : x ^ e ≤ x ^ η := Real.rpow_le_rpow_of_exponent_le hx1 hηe.le
  have hlog3 : Real.log x * x ^ (κ / 3) ≤ x ^ η / (η - κ / 3) := by
    have hl := Real.log_le_rpow_div hx0.le (by linarith : 0 < η - κ / 3)
    have hsplit' : x ^ η = x ^ (η - κ / 3) * x ^ (κ / 3) := by
      rw [← Real.rpow_add hx0]
      ring_nf
    rw [hsplit', mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hl (Real.rpow_nonneg hx0.le _)
  have hnorm : ‖x ^ η‖ = x ^ η := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [Real.norm_eq_abs, hnorm]
  refine herr.trans ?_
  have hl3 : Real.log x / Real.log 2 * (x ^ (κ / 3) / κ) =
      (Real.log x * x ^ (κ / 3)) / (Real.log 2 * κ) := by
    field_simp
  have hη3 : 0 < η - κ / 3 := by linarith
  have hlast : (Real.log x * x ^ (κ / 3)) / (Real.log 2 * κ) ≤
      1 / (Real.log 2 * κ * (η - κ / 3)) * x ^ η := by
    rw [div_le_iff₀ (by positivity)]
    calc Real.log x * x ^ (κ / 3) ≤ x ^ η / (η - κ / 3) := hlog3
      _ = 1 / (Real.log 2 * κ * (η - κ / 3)) * x ^ η * (Real.log 2 * κ) := by
          field_simp
  rw [hl3]
  have h1 : 2 * Real.log x ≤ 2 / η * x ^ η := by
    calc 2 * Real.log x ≤ 2 * (x ^ η / η) := by linarith
      _ = 2 / η * x ^ η := by ring
  have hCdef : C * x ^ η = 3 / η * x ^ η + 10 * x ^ η +
      1 / (Real.log 2 * κ * (η - κ / 3)) * x ^ η := by
    rw [hC]
    ring
  rw [hCdef]
  have h2 : 2 / η * x ^ η ≤ 3 / η * x ^ η := by
    gcongr
    norm_num
  linarith

/-- **A concrete half-dimension uncertainty with `κ > 1/2`.**  For every `κ` with
`1/2 < κ < 2(1 − 0.701299)` there is a set `Q` of primes whose deleted Chebyshev function is
`(x^κ + x^{κ/2})/κ + O(x^η)` with `η < κ/2`, and whose `Q`-free integers admit no power saving
`x^θ` with `θ < κ/2`.  The window input is the corpus short-interval prime-mass bound. -/
theorem exists_prime_deletion_half_dimension_uncertainty {κ : ℝ} (hκ : 1 / 2 < κ)
    (hκ' : κ < 2 * (1 - 701299 / 1000000)) :
    ∃ Q : Set ℕ, (∀ q ∈ Q, q.Prime) ∧
      (∃ η < κ / 2, (fun x : ℝ => deletedChebyshev Q x - (1 / κ) * (x ^ κ + x ^ (κ / 2)))
        =O[atTop] fun x => x ^ η) ∧
      ∀ a θ : ℝ, 0 ≤ θ → θ < κ / 2 →
        ¬(fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ := by
  set α : ℝ := (701299 / 1000000 + (1 - κ / 2)) / 2 with hαdef
  have hα : (701299 / 1000000 : ℝ) < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hακ : κ - 1 + α < κ / 2 := by rw [hαdef]; linarith
  have he : 0 ≤ κ - 1 + α := by rw [hαdef]; linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : κ < 1 := by linarith
  obtain ⟨X, hX1, hwin⟩ := RHTower.Sieve.exists_theta_window_lower hα hα1
  obtain ⟨η, hη, hO⟩ := greedy_chebyshev_expansion hκ0 hκ1 hα1 he hακ (by norm_num : (0 : ℝ) < 8192)
    (by linarith : (0 : ℝ) ≤ X) hwin
  refine ⟨greedyDeletion κ, fun q hq => hq.1, ⟨η, hη, hO⟩, ?_⟩
  intro a θ hθ hθκ
  refine not_isBigO_qFreeCount_of_odd (greedyDeletion κ) (l := 1) odd_one hθ hθκ hη hκ0 hκ1 ?_
  simpa using hO

end PrimeDeletion

end

end RHTower
