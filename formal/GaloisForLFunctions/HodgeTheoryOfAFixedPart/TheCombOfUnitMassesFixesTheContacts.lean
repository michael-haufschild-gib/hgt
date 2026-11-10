import GaloisForLFunctions.HodgeTheoryOfAFixedPart.WeilsFormInTheGaugeOfTheFlatTail

/-!
# The comb of unit masses fixes the contacts

The arithmetic square does not see a multiplicative system with integer norms: it lifts through
its norms. The normal form of the pairing does, through the comb: unit masses on all integers,
with the counterterm `log(n/2π)`. This file replaces the contact orders `Λ` by arbitrary weights
`w` and reads the comb against them.

* **The balance of Zariski** (`sum_divisors_eq_log_iff`): the contacts of every `Γ_n` with the
  graphs below it sum to `log n`, the divergent part of the counterterm, iff `w = Λ`.
* **Unit multiplicities** (`multiplicity_eq_one_iff`): for a system with `a(n)` elements of norm
  `n` and von Mangoldt weights `w`, that is `a·log = w ∗ a`, every integer is a norm exactly once
  iff `w = Λ`. The comb of unit masses and the contacts of the square determine each other.
* **The flat tail weighs the contacts by `1/k`** (`combFormW_flatTail`): with the weights `w`,
  Weil's form of the flat tail is its value for `Λ` minus `2 Σ_k (w(k) − Λ(k))⌊N/k⌋`.
* **The tolerance of the flat tail is the first Li coefficient**
  (`tendsto_combFormW_flatTail_div`, `eventually_combFormW_flatTail_neg`): for weights that
  differ from `Λ` at finitely many integers the form per degree point tends to
  `2 + γ − log 4π − 2 Σ_k (w(k) − Λ(k))/k`; when the excess `Σ_k (w(k) − Λ(k))/k` of contact mass
  exceeds `1 + γ/2 − ½ log 4π`, the inequality `D·D ≤ 2 d₁ d₂` fails on the flat tail at every
  large scale.
* **A double contact at the prime `2`** (`eventually_combFormW_doubleTwo_neg`): with the weight
  `2 log 2` on the pairs `(m, 2m)` the flat tail violates the inequality at every large scale.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### The balance of Zariski -/

/-- **The balance of Zariski selects the contact orders.** The weights of the contacts of every
`Γ_n` with the graphs of its divisors sum to `log n` iff they are the von Mangoldt function. -/
theorem sum_divisors_eq_log_iff (w : ℕ → ℝ) :
    (∀ n : ℕ, 1 ≤ n → ∑ d ∈ n.divisors, w d = Real.log n) ↔ ∀ n : ℕ, 1 ≤ n → w n = Λ n := by
  constructor
  · intro h n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have h1 := h n hn
      have h2 : ∑ d ∈ n.divisors, (Λ d : ℝ) = Real.log n := ArithmeticFunction.vonMangoldt_sum
      rw [← Nat.cons_self_properDivisors (by omega : n ≠ 0), Finset.sum_cons] at h1 h2
      have hlow : ∑ d ∈ n.properDivisors, w d = ∑ d ∈ n.properDivisors, (Λ d : ℝ) :=
        Finset.sum_congr rfl fun d hd => by
          obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hd
          exact ih d hd2 (Nat.pos_of_dvd_of_pos hd1 (by omega))
      linarith
  · intro h n hn
    rw [← ArithmeticFunction.vonMangoldt_sum]
    exact Finset.sum_congr rfl fun d hd =>
      h d (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (by omega))

/-- **Unit multiplicities.** Let `a(n)` be the number of elements of norm `n` of a
multiplicative system with von Mangoldt weights `w`: `a(1) = 1` and
`a(n) log n = Σ_{d ∣ n} w(d) a(n/d)`. Every integer is a norm exactly once iff `w = Λ`. -/
theorem multiplicity_eq_one_iff {a w : ℕ → ℝ} (ha : a 1 = 1)
    (hsys : ∀ n : ℕ, 1 ≤ n → a n * Real.log n = ∑ d ∈ n.divisors, w d * a (n / d)) :
    (∀ n : ℕ, 1 ≤ n → a n = 1) ↔ ∀ n : ℕ, 1 ≤ n → w n = Λ n := by
  have hdiv : ∀ n d : ℕ, 1 ≤ n → d ∈ n.divisors → 1 ≤ n / d := fun n d hn hd =>
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd))
      (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (by omega))
  constructor
  · intro h
    rw [← sum_divisors_eq_log_iff]
    intro n hn
    have h1 := hsys n hn
    rw [h n hn, one_mul] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun d hd => by rw [h (n / d) (hdiv n d hn hd), mul_one]
  · intro h n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · obtain rfl : n = 1 := by omega
        exact ha
      have h1 := hsys n hn
      have hterm : ∀ d ∈ n.divisors, w d * a (n / d) = if d = 1 then 0 else (Λ d : ℝ) := by
        intro d hd
        have hd0 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (by omega)
        by_cases hd1 : d = 1
        · rw [if_pos hd1, h d hd0, hd1, ArithmeticFunction.vonMangoldt_apply_one, zero_mul]
        · rw [if_neg hd1, h d hd0, ih (n / d) (Nat.div_lt_self (by omega) (by omega))
            (hdiv n d hn hd), mul_one]
      have hsum : ∑ d ∈ n.divisors, (if d = 1 then 0 else (Λ d : ℝ)) = Real.log n := by
        rw [← ArithmeticFunction.vonMangoldt_sum]
        exact Finset.sum_congr rfl fun d _ => by
          split_ifs with hd1
          · rw [hd1, ArithmeticFunction.vonMangoldt_apply_one]
          · rfl
      rw [Finset.sum_congr rfl hterm, hsum] at h1
      have hlog : Real.log n ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
      exact mul_right_cancel₀ hlog (by rw [h1, one_mul])

/-! ### The normal form with arbitrary contact weights -/

/-- The contact of `Γ_m` and `Γ_n` with the weight `w` in place of the contact orders. -/
def contactW (w : ℕ → ℝ) (m n : ℕ) : ℝ :=
  (if m ∣ n then w (n / m) else 0) + (if n ∣ m then w (m / n) else 0)

/-- The pairing of the normal form with contact weights `w`. -/
def combPairingW (w : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * (jetKernel m n + contactW w m n) -
    ∑ n ∈ S, c n ^ 2 * counterterm n

/-- Weil's form on the comb with contact weights `w`. -/
def combFormW (w : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  2 * (degOne S c * degTwo S c) - combPairingW w S c

theorem combPairingW_vonMangoldt (S : Finset ℕ) (c : ℕ → ℝ) :
    combPairingW (fun k => (Λ k : ℝ)) S c = combPairing S c := rfl

theorem combFormW_vonMangoldt (S : Finset ℕ) (c : ℕ → ℝ) :
    combFormW (fun k => (Λ k : ℝ)) S c = combForm S c := rfl

theorem contactW_sub (w : ℕ → ℝ) (m n : ℕ) :
    contactW (fun k => w k - Λ k) m n = contactW w m n - contact m n := by
  unfold contactW contact
  split_ifs <;> ring

/-- The form with the weights `w` and the form of the square differ by the excess contacts. -/
theorem combFormW_eq (w : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℝ) :
    combFormW w S c = combForm S c -
      ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contactW (fun k => w k - Λ k) m n := by
  have h : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * (jetKernel m n + contactW w m n) =
      ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * pairKernel m n +
        ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contactW (fun k => w k - Λ k) m n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [contactW_sub, pairKernel]; ring
  rw [combFormW, combPairingW, h, combForm, combPairing]
  ring

/-! ### The contacts of the flat tail -/

/-- The contacts of `Γ_n` with the graphs of its proper divisors, for any weight. -/
theorem sum_ite_dvd_erase {N n : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) (v : ℕ → ℝ) :
    ∑ m ∈ (Icc 1 N).erase n, (if m ∣ n then v (n / m) else 0) =
      ∑ k ∈ Icc 2 N, if k ∣ n then v k else 0 := by
  have hfilter : ((Icc 1 N).erase n).filter (· ∣ n) = n.properDivisors := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, Nat.mem_properDivisors]
    constructor
    · rintro ⟨⟨hne, -⟩, hd⟩
      exact ⟨hd, lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) hne⟩
    · rintro ⟨hd, hlt⟩
      exact ⟨⟨hlt.ne, Nat.pos_of_dvd_of_pos hd (by omega), by omega⟩, hd⟩
  have hfilter' : (Icc 2 N).filter (· ∣ n) = n.divisors.erase 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hk, -⟩, hd⟩
      exact ⟨by omega, hd, by omega⟩
    · rintro ⟨hk1, hd, -⟩
      have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hd (by omega)
      exact ⟨⟨by omega, (Nat.le_of_dvd (by omega) hd).trans hN⟩, hd⟩
  rw [← Finset.sum_filter, ← Finset.sum_filter, hfilter, hfilter']
  have h := Nat.sum_div_divisors n v
  rw [← Nat.cons_self_properDivisors (by omega : n ≠ 0), Finset.sum_cons, Nat.div_self (by omega),
    Nat.cons_self_properDivisors (by omega : n ≠ 0),
    ← Finset.add_sum_erase n.divisors v (Nat.one_mem_divisors.mpr (by omega))] at h
  linarith

/-- **The contacts of the flat tail with any weight**: the pairs `(m, mk)`, `mk ≤ N`, are
`⌊N/k⌋` for each `k`, counted twice. -/
theorem sum_sum_contactW_Icc (v : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, contactW v m n =
      2 * ∑ k ∈ Icc 2 N, v k * ((N / k : ℕ) : ℝ) := by
  have hsplit : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, contactW v m n =
      ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (if m ∣ n then v (n / m) else 0) +
        ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (if n ∣ m then v (m / n) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    rfl
  have hswap : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (if n ∣ m then v (m / n) else 0) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).erase m, (if n ∣ m then v (m / n) else 0) :=
    Finset.sum_comm' (s' := fun m => (Icc 1 N).erase m) (t' := Icc 1 N) fun n m => by
      simp only [Finset.mem_erase]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨Ne.symm h2, h1⟩, h3⟩,
        fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, Ne.symm h1, h3⟩⟩
  have hrows : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (if m ∣ n then v (n / m) else 0) =
      ∑ k ∈ Icc 2 N, v k * ((N / k : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl fun n hn =>
      sum_ite_dvd_erase (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 v, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Icc_one_eq_Ioc_zero,
      Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
  rw [hsplit, hswap, hrows]
  ring

/-- **The flat tail weighs the contacts by `⌊N/k⌋`.** -/
theorem combFormW_flatTail (w : ℕ → ℝ) (N : ℕ) :
    combFormW w (Icc 1 N) (fun _ => 1) = combForm (Icc 1 N) (fun _ => 1) -
      2 * ∑ k ∈ Icc 2 N, (w k - Λ k) * ((N / k : ℕ) : ℝ) := by
  rw [combFormW_eq, ← sum_sum_contactW_Icc]
  congr 1
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring

/-! ### The tolerance of the flat tail -/

/-- `⌊N/k⌋/N → 1/k`. -/
theorem tendsto_natDiv_div {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((N / k : ℕ) : ℝ) / N) atTop (𝓝 (1 / (k : ℝ))) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hlow : Tendsto (fun N : ℕ => 1 / (k : ℝ) - 1 / (N : ℝ)) atTop (𝓝 (1 / (k : ℝ))) := by
    have h := (tendsto_const_nhds (x := 1 / (k : ℝ))).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : (N : ℝ) < (k : ℝ) * (((N / k : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ N hk
    rw [div_sub_div _ _ hk'.ne' hN'.ne', div_le_div_iff₀ (by positivity) hN']
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : ((N / k : ℕ) : ℝ) * k ≤ N := by exact_mod_cast Nat.div_mul_le_self N k
    rw [div_le_div_iff₀ hN' hk']
    linarith

/-- **The form of the flat tail with weights that differ from `Λ` at finitely many integers.**
Per degree point it tends to `2 + γ − log 4π − 2 Σ_k (w(k) − Λ(k))/k`. -/
theorem tendsto_combFormW_flatTail_div {w : ℕ → ℝ} {K : ℕ} (hw : ∀ k, K < k → w k = Λ k) :
    Tendsto (fun N : ℕ => combFormW w (Icc 1 N) (fun _ => 1) / N) atTop
      (𝓝 (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) -
        2 * ∑ k ∈ Icc 2 K, (w k - Λ k) / k)) := by
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Icc 2 K, (w k - Λ k) * (((N / k : ℕ) : ℝ) / N)) atTop
      (𝓝 (∑ k ∈ Icc 2 K, (w k - Λ k) * (1 / (k : ℝ)))) :=
    tendsto_finsetSum (Icc 2 K) fun k hk =>
      (tendsto_natDiv_div (by have := (Finset.mem_Icc.mp hk).1; omega : 1 ≤ k)).const_mul
        (w k - Λ k)
  have hval : ∑ k ∈ Icc 2 K, (w k - Λ k) * (1 / (k : ℝ)) = ∑ k ∈ Icc 2 K, (w k - Λ k) / k :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hval] at hsum
  refine (tendsto_combForm_flatTail_div.sub (hsum.const_mul 2)).congr' ?_
  filter_upwards [eventually_ge_atTop K] with N hN
  have hcut : ∑ k ∈ Icc 2 N, (w k - Λ k) * ((N / k : ℕ) : ℝ) =
      ∑ k ∈ Icc 2 K, (w k - Λ k) * ((N / k : ℕ) : ℝ) := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hN) fun k hk hk' => ?_).symm
    have hlt : K < k := by
      by_contra hle
      exact hk' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, not_lt.mp hle⟩)
    rw [hw k hlt, sub_self, zero_mul]
  rw [combFormW_flatTail, hcut, sub_div]
  congr 1
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The tolerance of the flat tail is the first Li coefficient.** If the weights differ from
`Λ` at finitely many integers and their excess `Σ_k (w(k) − Λ(k))/k` exceeds
`1 + γ/2 − ½ log 4π`, then `D·D > 2 d₁ d₂` for the flat tail at every large scale. -/
theorem eventually_combFormW_flatTail_neg {w : ℕ → ℝ} {K : ℕ} (hw : ∀ k, K < k → w k = Λ k)
    (hexc : 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 <
      ∑ k ∈ Icc 2 K, (w k - Λ k) / k) :
    ∀ᶠ N : ℕ in atTop, combFormW w (Icc 1 N) (fun _ => 1) < 0 := by
  have hlim := tendsto_combFormW_flatTail_div hw
  have hneg : 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) -
      2 * ∑ k ∈ Icc 2 K, (w k - Λ k) / k < 0 := by linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hneg), eventually_ge_atTop 1] with N hN hN1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  rwa [div_lt_iff₀ hN', zero_mul] at hN

/-- The contact orders of the square with a second contact at the prime `2`. -/
def doubleTwo (k : ℕ) : ℝ := Λ k + if k = 2 then Real.log 2 else 0

/-- **A double contact at the prime `2` violates the inequality on the flat tail.** -/
theorem eventually_combFormW_doubleTwo_neg :
    ∀ᶠ N : ℕ in atTop, combFormW doubleTwo (Icc 1 N) (fun _ => 1) < 0 := by
  refine eventually_combFormW_flatTail_neg (K := 2) (fun k hk => ?_) ?_
  · rw [doubleTwo, if_neg (by omega), add_zero]
  · have hsum : ∑ k ∈ Icc 2 2, (doubleTwo k - Λ k) / (k : ℝ) = Real.log 2 / 2 := by
      rw [Finset.Icc_self, Finset.sum_singleton, doubleTwo, if_pos rfl]
      push_cast
      ring
    rw [hsum]
    have hγ := Real.eulerMascheroniConstant_lt_two_thirds
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
    -- `log 4π > 2` since `4π > 12 > e²`
    have he : Real.exp 2 < 4 * Real.pi := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h3]
      nlinarith [Real.exp_pos 1]
    have hlog : 2 < Real.log (4 * Real.pi) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      exact he
    linarith

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
