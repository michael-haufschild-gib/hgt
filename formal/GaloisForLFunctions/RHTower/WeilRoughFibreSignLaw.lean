import GaloisForLFunctions.RHTower.WeilLittleOVonMangoldtRigidity
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# The rough sign law of the Weil cone

**Theorem** (`roughSum_nonpos_of_weilPositiveFull`). Let `lam` be full-cone Weil-positive and suppose
`d = lam − Λ` is notch-small, which means:
- `Σ_{n≤x} |d(n)|/n = o(log x)`;
- `Σ_{n≤x} |d(n)|/√n = o(√x)`;
- `Σ_{n>x} |d(n)| n^{−3/2} = o(x^{−1/2})`.

This holds, for instance, for `d = o(Λ) + (a null sequence)`. Then for every `y ≥ 2`, the `y`-rough
harmonic partial sums `Σ_{n≤k, p∣n ⇒ p>y} d(n)/n` cannot stay above a positive level:
`liminf_k Σ_{n≤k, rough} d(n)/n ≤ 0`.

So a notch-small decoration of `Λ` can only remove harmonic mass from the rough integers, never add
it. The notch with `ε = 0` has exactly the rough sum as its main functional, and the refined notch
bounds its errors by `C_η + η K log L` against the main term `κ Y log L`.

**Corollary** (`not_weilPositiveFull_cramerProfile`). For `κ > 0` the Cramér-restored profile
`Λ(n) + κ(1_ℙ(n) − 1/log n)` is not Weil-positive. Its prime excess is balanced by a composite
deficit, both windows are pinned, and the deviation is sign-indefinite with `Σ|d|/n = ∞`. But its
odd harmonic sums grow like `κ(log log k − ½ log log k)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable
open RHTower.PrimeSmallDeviation

variable {P : Finset ℕ}

/-- With `ε = 0` the notch main weight is the indicator of the rough fibre: `v(n) mW(n) = v(n)/√n`
when `vecOf P n = 0`, and `0` otherwise. -/
theorem mul_mainWeight_zero_eq (v : ℕ → ℝ) (n₀ n : ℕ) :
    v n * mainWeight P 0 n₀ n = if vecOf P n = 0 then v n * (Real.sqrt n)⁻¹ else 0 := by
  unfold mainWeight
  split_ifs with h0 h1
  · rw [roughPart_eq_self h0]; ring
  · rw [roughPart_eq_self h0]; ring
  · ring
  · ring

/-- **The rough sign law, deviation form.** If `−ψ_v` is positive definite and `d(n) = √n v(n)` is
notch-small, then the rough partial sums `Σ_{n≤k, vecOf P n = 0} v(n)/√n` cannot stay above a
positive level. -/
theorem nonpos_of_roughSum_ge (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀)
    {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hd : NotchSmall (sqrtScaled v)) {Y : ℝ} {T : ℕ}
    (hc : ∀ k, T ≤ k → Y ≤ ∑ n ∈ Finset.range (k + 1),
      (if vecOf P n = 0 then v n * (Real.sqrt n)⁻¹ else 0)) : Y ≤ 0 := by
  by_contra hY
  push Not at hY
  set a : ℕ → ℝ := fun n => v n * mainWeight P 0 n₀ n with hadef
  have hS : ∀ k, rampPartial a k = ∑ n ∈ Finset.range (k + 1),
      (if vecOf P n = 0 then v n * (Real.sqrt n)⁻¹ else 0) := fun k =>
    Finset.sum_congr rfl fun n _ => mul_mainWeight_zero_eq v n₀ n
  set T' := max T 1 with hT'
  set B : ℝ := ∑ k ∈ Finset.range T', |rampPartial a k| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hlow : ∀ k, -B ≤ rampPartial a k := by
    intro k
    rcases lt_or_ge k T' with hk | hk
    · have := Finset.single_le_sum (f := fun k => |rampPartial a k|) (fun k _ => abs_nonneg _)
        (Finset.mem_range.mpr hk)
      linarith [neg_abs_le (rampPartial a k)]
    · have := hc k ((le_max_left T 1).trans hk)
      rw [← hS] at this
      linarith
  have hc' : ∀ k, T' ≤ k → Y ≤ rampPartial a k := fun k hk => by
    rw [hS]; exact hc k ((le_max_left T 1).trans hk)
  have := nonpos_of_rampPartial_ge hP hn₀ hv0 hA ha hPD hd (le_max_right T 1) hlow hc'
  linarith

/-- **The rough sign law of the Weil cone.** If `lam` is full-cone Weil-positive and `d = lam − Λ`
is notch-small, then for every `y ≥ 2` the `y`-rough harmonic partial sums of `d` cannot stay above
a positive level. -/
theorem roughSum_nonpos_of_weilPositiveFull {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hd : NotchSmall (WeilOneSided.coneDeviation lam)) {y : ℕ} (hy : 2 ≤ y) {Y : ℝ} {T : ℕ}
    (hc : ∀ k, T ≤ k → Y ≤ ∑ n ∈ Finset.range (k + 1),
      (if vecOf (WeilLogSummable.primesUpTo y) n = 0 then
        WeilOneSided.coneDeviation lam n / n else 0)) : Y ≤ 0 := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsc : ∀ n, sqrtScaled v n = WeilOneSided.coneDeviation lam n := by
    intro n
    simp only [sqrtScaled, hv, RHTower.WeilExcess.weilDeviation, WeilOneSided.coneDeviation]
    split_ifs with h2
    · have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      field_simp
    · simp
  have hdv : NotchSmall (sqrtScaled v) := by
    have e : sqrtScaled v = WeilOneSided.coneDeviation lam := funext hsc
    rw [e]; exact hd
  have hterm : ∀ n, v n * (Real.sqrt n)⁻¹ = WeilOneSided.coneDeviation lam n / n := by
    intro n
    rw [← hsc, sqrtScaled, mul_comm (Real.sqrt n), mul_div_assoc, Real.sqrt_div_self]
  refine nonpos_of_roughSum_ge (P := WeilLogSummable.primesUpTo y) prime_of_mem_primesUpTo
    (n₀ := 2) (isSmoothOver_primesUpTo le_rfl hy) hv0 hC0 hC hPD hdv (T := T) fun k hk => ?_
  refine (hc k hk).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  split_ifs
  · exact (hterm n).symm
  · rfl

/-! ## The Cramér-restored profiles with prime excess -/

/-- The Cramér-restored prime profile `Λ(n) + κ(1_ℙ(n) − 1/log n)`. -/
def cramerProfile (κ : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n + κ * ((if n.Prime then 1 else 0) - (Real.log n)⁻¹)

theorem coneDeviation_cramerProfile (κ : ℝ) (n : ℕ) :
    WeilOneSided.coneDeviation (cramerProfile κ) n =
      (if 2 ≤ n ∧ n.Prime then κ else 0) + (if 2 ≤ n then -(κ * (Real.log n)⁻¹) else 0) := by
  unfold WeilOneSided.coneDeviation cramerProfile
  by_cases h2 : 2 ≤ n
  · by_cases hp : n.Prime
    · simp [h2, hp]; ring
    · simp [h2, hp]
  · simp [h2]

theorem notchSmall_cramer (κ : ℝ) :
    NotchSmall (WeilOneSided.coneDeviation (cramerProfile κ)) := by
  have e : WeilOneSided.coneDeviation (cramerProfile κ) =
      (fun n : ℕ => if 2 ≤ n ∧ n.Prime then κ else 0) +
        (fun n : ℕ => if 2 ≤ n then -(κ * (Real.log n)⁻¹) else 0) :=
    funext fun n => coneDeviation_cramerProfile κ n
  rw [e]
  refine NotchSmall.add (IsLittleOVonMangoldt.notchSmall fun η hη => ?_)
    (notchSmall_of_tendsto_zero ?_)
  · refine ⟨⌈Real.exp (|κ| / η)⌉₊ + 2, fun n hn => ?_⟩
    split_ifs with h
    · rw [ArithmeticFunction.vonMangoldt_apply_prime h.2]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hexp : Real.exp (|κ| / η) ≤ n := by
        have h1 := Nat.le_ceil (Real.exp (|κ| / η))
        have h2 : ((⌈Real.exp (|κ| / η)⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega)
        linarith
      have hlog : |κ| / η ≤ Real.log n := by rw [Real.le_log_iff_exp_le hn0]; exact hexp
      rw [div_le_iff₀ hη] at hlog
      linarith
    · rw [abs_zero]; exact mul_nonneg hη.le ArithmeticFunction.vonMangoldt_nonneg
  · have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hinv := (hlog.inv_tendsto_atTop).const_mul (-κ)
    rw [mul_zero] at hinv
    refine hinv.congr' (eventually_atTop.mpr ⟨2, fun n hn => ?_⟩)
    simp only [Pi.inv_apply]
    rw [if_pos hn]; ring

/-- `g(n) = 1/(n log n)`. -/
def invNLogN (n : ℕ) : ℝ := ((n : ℝ) * Real.log n)⁻¹

theorem invNLogN_nonneg (n : ℕ) : 0 ≤ invNLogN n := by
  unfold invNLogN
  have := Real.log_natCast_nonneg n
  positivity

theorem invNLogN_antitone {n : ℕ} (hn : 2 ≤ n) : invNLogN (n + 1) ≤ invNLogN n := by
  unfold invNLogN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog1 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log hn0 (by push_cast; linarith)
  refine inv_anti₀ (by positivity) ?_
  exact mul_le_mul (by push_cast; linarith) hlog1 hlog.le (by positivity)

/-- `1/(n log n) ≤ log log n − log log (n − 1)` for `n ≥ 3`. -/
theorem invNLogN_le_logLog_sub {n : ℕ} (hn : 3 ≤ n) :
    invNLogN n ≤ Real.log (Real.log n) - Real.log (Real.log (n - 1 : ℕ)) := by
  unfold invNLogN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : (1 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - 1)
  have hm0 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
  have ha : 0 < Real.log ((n - 1 : ℕ) : ℝ) := Real.log_pos hm
  have hmn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hb : Real.log ((n - 1 : ℕ) : ℝ) < Real.log n := Real.log_lt_log hm0 (by rw [hmn]; linarith)
  have hb0 : 0 < Real.log n := ha.trans hb
  -- `log b − log a ≥ (b − a)/b` and `b − a = log(n/(n−1)) ≥ 1/n`
  have h1 : (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log n ≤
      Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) := by
    have := Real.log_le_sub_one_of_pos (div_pos ha hb0)
    rw [Real.log_div ha.ne' hb0.ne'] at this
    have e : Real.log ((n - 1 : ℕ) : ℝ) / Real.log n - 1 =
        -((Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log n) := by
      field_simp; ring
    linarith
  have h2 : (n : ℝ)⁻¹ ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos (div_pos hm0 hn0)
    rw [Real.log_div hm0.ne' hn0.ne', hmn] at this
    have e : ((n : ℝ) - 1) / n - 1 = -(n : ℝ)⁻¹ := by field_simp; ring
    rw [hmn]
    linarith
  calc ((n : ℝ) * Real.log n)⁻¹ = (n : ℝ)⁻¹ / Real.log n := by
        rw [mul_inv, div_eq_mul_inv]
    _ ≤ (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log n :=
        div_le_div_of_nonneg_right h2 hb0.le
    _ ≤ _ := h1

/-- `Σ_{2≤n≤k} 1/(n log n) ≤ log log k + 2`. -/
theorem sum_invNLogN_le {k : ℕ} (hk : 2 ≤ k) :
    ∑ n ∈ Finset.range (k + 1), (if 2 ≤ n then invNLogN n else 0) ≤
      Real.log (Real.log k) + 2 := by
  have hbase : invNLogN 2 - Real.log (Real.log 2) ≤ 2 := by
    have hl2 := Real.log_two_gt_d9
    have h1 : invNLogN 2 ≤ 1 := by
      unfold invNLogN; push_cast
      rw [inv_le_one_iff₀]; right; nlinarith
    have h2 : -1 ≤ Real.log (Real.log 2) := by
      have he : Real.exp (-1) ≤ Real.log 2 := by
        have := Real.add_one_le_exp 1
        rw [Real.exp_neg]
        have : (Real.exp 1)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
        linarith
      have := Real.log_le_log (Real.exp_pos (-1)) he
      rwa [Real.log_exp] at this
    linarith
  induction k, hk using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [show ¬ 2 ≤ 0 by omega, show ¬ 2 ≤ 1 by omega, le_refl, if_true, if_false]
    push_cast
    linarith
  | succ k hk ih =>
    rw [Finset.sum_range_succ, if_pos (by omega)]
    have h := invNLogN_le_logLog_sub (n := k + 1) (by omega)
    rw [show k + 1 - 1 = k by omega] at h
    push_cast at h ⊢
    linarith

/-- `2 Σ_{3≤n≤k, n odd} 1/(n log n) ≤ Σ_{2≤n≤k} 1/(n log n)`: each odd `n` is paired with `n − 1`. -/
theorem two_mul_sum_odd_invNLogN_le (k : ℕ) :
    2 * ∑ n ∈ Finset.range (k + 1), (if Odd n ∧ 3 ≤ n then invNLogN n else 0) +
        (if Even k ∧ 2 ≤ k then invNLogN k else 0) ≤
      ∑ n ∈ Finset.range (k + 1), (if 2 ≤ n then invNLogN n else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun n => if 2 ≤ n then invNLogN n else 0)]
    rcases Nat.even_or_odd k with hk | hk
    · -- `k` even, `k + 1` odd
      have hk1 : Odd (k + 1) := hk.add_one
      have hne : ¬ Even (k + 1) := Nat.not_even_iff_odd.mpr hk1
      rw [if_neg (show ¬ (Even (k + 1) ∧ 2 ≤ k + 1) from fun h => hne h.1)]
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk0 : k = 0 := by rcases hk with ⟨m, hm⟩; omega
        subst hk0
        simp
      · rw [if_pos (show Odd (k + 1) ∧ 3 ≤ k + 1 from ⟨hk1, by omega⟩),
          if_pos (show 2 ≤ k + 1 by omega)]
        rw [if_pos (show Even k ∧ 2 ≤ k from ⟨hk, hk2⟩)] at ih
        have := invNLogN_antitone hk2
        linarith
    · -- `k` odd, `k + 1` even
      have hk1 : Even (k + 1) := hk.add_one
      have hno : ¬ Odd (k + 1) := Nat.not_odd_iff_even.mpr hk1
      have hnk : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      rw [if_neg (show ¬ (Odd (k + 1) ∧ 3 ≤ k + 1) from fun h => hno h.1), add_zero]
      rw [if_neg (show ¬ (Even k ∧ 2 ≤ k) from fun h => hnk h.1), add_zero] at ih
      by_cases h2 : 2 ≤ k + 1
      · rw [if_pos (show Even (k + 1) ∧ 2 ≤ k + 1 from ⟨hk1, h2⟩), if_pos h2]; linarith
      · rw [if_neg (show ¬ (Even (k + 1) ∧ 2 ≤ k + 1) from fun h => h2 h.2), if_neg h2]
        linarith

theorem sum_odd_invNLogN_le {k : ℕ} (hk : 2 ≤ k) :
    ∑ n ∈ Finset.range (k + 1), (if Odd n ∧ 3 ≤ n then invNLogN n else 0) ≤
      Real.log (Real.log k) / 2 + 1 := by
  have h1 := two_mul_sum_odd_invNLogN_le k
  have h2 := sum_invNLogN_le hk
  have h3 : 0 ≤ (if Even k ∧ 2 ≤ k then invNLogN k else 0) := by
    split_ifs
    · exact invNLogN_nonneg k
    · exact le_rfl
  linarith

/-- The odd primes up to `k` carry harmonic mass `≥ log log (k + 1) − 3/2`. -/
theorem sum_odd_prime_inv_ge {k : ℕ} (hk : 2 ≤ k) :
    Real.log (Real.log ((k : ℝ) + 1)) - 3 / 2 ≤
      ∑ n ∈ Finset.range (k + 1), (if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0) := by
  have hM := RHTower.mertens_lower_add_one (M := k) (by omega)
  have hsplit : ∑ p ∈ Nat.primesBelow (k + 1), (p : ℝ)⁻¹ =
      ∑ n ∈ Finset.range (k + 1), (if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0) + 1 / 2 := by
    have e1 : ∑ p ∈ Nat.primesBelow (k + 1), (p : ℝ)⁻¹ =
        ∑ n ∈ Finset.range (k + 1), (if n.Prime then (n : ℝ)⁻¹ else 0) := by
      show ∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime, (p : ℝ)⁻¹ = _
      rw [Finset.sum_filter]
    have e2 : ∀ n : ℕ, (if n.Prime then (n : ℝ)⁻¹ else 0) =
        (if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0) + (if n = 2 then 1 / 2 else 0) := by
      intro n
      by_cases hp : n.Prime
      · rcases hp.eq_two_or_odd' with h2 | ho
        · subst h2
          have : ¬ Odd 2 := by decide
          simp [this, Nat.prime_two]
        · have : n ≠ 2 := by rintro rfl; exact absurd ho (by decide)
          simp [hp, ho, this]
      · have : n ≠ 2 := by rintro rfl; exact hp Nat.prime_two
        simp [hp, this]
    rw [e1, Finset.sum_congr rfl fun n _ => e2 n, Finset.sum_add_distrib, Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  linarith

theorem vecOf_primesUpTo_two_eq_zero_iff {n : ℕ} (hn : n ≠ 0) :
    vecOf (WeilLogSummable.primesUpTo 2) n = 0 ↔ ¬ 2 ∣ n := by
  have hP : WeilLogSummable.primesUpTo 2 = {2} := by decide
  constructor
  · intro h h2
    have h2mem : (2 : ℕ) ∈ WeilLogSummable.primesUpTo 2 := by rw [hP]; simp
    have := congrFun h ⟨2, h2mem⟩
    simp only [vecOf, Pi.zero_apply, Nat.cast_eq_zero] at this
    rw [Nat.factorization_eq_zero_iff] at this
    rcases this with h1 | h1 | h1
    · exact h1 Nat.prime_two
    · exact h1 h2
    · exact hn h1
  · intro h
    funext p
    have hp : (p : ℕ) = 2 := by
      have h' : (p : ℕ) ∈ ({2} : Finset ℕ) := by rw [← hP]; exact p.2
      exact Finset.mem_singleton.mp h'
    show ((n.factorization (p : ℕ) : ℤ)) = 0
    rw [hp]
    exact_mod_cast (Nat.factorization_eq_zero_iff n 2).mpr (Or.inr (Or.inl h))

/-- **Cramér profiles with prime excess are not Weil-positive.** For `κ > 0`,
`Λ(n) + κ(1_ℙ(n) − 1/log n)` is not full-cone Weil-positive. -/
theorem not_weilPositiveFull_cramerProfile {κ : ℝ} (hκ : 0 < κ) :
    ¬ RHTower.WeilPositiveFull (cramerProfile κ) := by
  intro hW
  set T : ℕ := ⌈Real.exp (Real.exp 7)⌉₊ with hT
  refine absurd (roughSum_nonpos_of_weilPositiveFull hW (notchSmall_cramer κ) le_rfl
    (Y := κ) (T := T) fun k hk => ?_) (not_le.mpr hκ)
  have hkT : Real.exp (Real.exp 7) ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := le_trans (by
      have := Real.add_one_le_exp (Real.exp 7)
      have := Real.add_one_le_exp 7
      linarith) hkT
    exact_mod_cast this
  -- the rough sum is `κ (odd prime mass − odd `1/(n log n)` mass)`
  have hterm : ∀ n, (if vecOf (WeilLogSummable.primesUpTo 2) n = 0 then
      WeilOneSided.coneDeviation (cramerProfile κ) n / n else 0) =
      κ * ((if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0) -
        (if Odd n ∧ 3 ≤ n then invNLogN n else 0)) := by
    intro n
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · simp [WeilOneSided.coneDeviation]
      · have : ¬ Odd 1 ∨ ¬ Nat.Prime 1 := Or.inr Nat.not_prime_one
        simp [WeilOneSided.coneDeviation, Nat.not_prime_one]
    · rw [coneDeviation_cramerProfile, if_pos h2]
      by_cases hodd : Odd n
      · have hn3 : 3 ≤ n := by rcases hodd with ⟨m, hm⟩; omega
        have h2n : ¬ 2 ∣ n := by
          rintro ⟨m, hm⟩; rcases hodd with ⟨j, hj⟩; omega
        rw [if_pos ((vecOf_primesUpTo_two_eq_zero_iff (by omega)).mpr h2n),
          if_pos (show Odd n ∧ 3 ≤ n from ⟨hodd, hn3⟩)]
        unfold invNLogN
        rw [mul_inv, div_eq_mul_inv]
        by_cases hp : n.Prime
        · rw [if_pos (show 2 ≤ n ∧ n.Prime from ⟨h2, hp⟩),
            if_pos (show Odd n ∧ n.Prime from ⟨hodd, hp⟩)]
          ring
        · rw [if_neg (show ¬ (2 ≤ n ∧ n.Prime) from fun h => hp h.2),
            if_neg (show ¬ (Odd n ∧ n.Prime) from fun h => hp h.2)]
          ring
      · have h2n : 2 ∣ n := by
          rcases Nat.even_or_odd n with he | ho
          · exact even_iff_two_dvd.mp he
          · exact absurd ho hodd
        rw [if_neg (fun h => ((vecOf_primesUpTo_two_eq_zero_iff (by omega)).mp h) h2n)]
        simp [hodd]
  rw [Finset.sum_congr rfl fun n _ => hterm n, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hP := sum_odd_prime_inv_ge hk2
  have hC := sum_odd_invNLogN_le hk2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlogk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hmono : Real.log (Real.log k) ≤ Real.log (Real.log ((k : ℝ) + 1)) :=
    Real.log_le_log hlogk (Real.log_le_log hk0 (by linarith))
  have hbig : 7 ≤ Real.log (Real.log k) := by
    rw [Real.le_log_iff_exp_le hlogk, Real.le_log_iff_exp_le hk0]
    exact hkT
  have hdiff : 1 ≤ ∑ n ∈ Finset.range (k + 1), (if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0) -
      ∑ n ∈ Finset.range (k + 1), (if Odd n ∧ 3 ≤ n then invNLogN n else 0) := by
    linarith
  nlinarith

end RHTower.WeilAbscissa
