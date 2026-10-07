import Mathlib

/-!
# Inversion of gcd-weighted series

Let `b : ℕ → ℝ` with `Σ |b(n)|/√n < ∞`. If `Σ_n b(n) gcd(m, n)/n = 0` for every `m ≥ 1`, then
`b(n) = 0` for every `n ≥ 1` (`eq_zero_of_tsum_gcd_mul_div_eq_zero`).

**Proof.**
* `gcd(m, n) = Σ_{d ∣ m, d ∣ n} φ(d)` turns the hypothesis into `Σ_{d ∣ m} φ(d) β(d) = 0`, where
  `β(d) = Σ_{d ∣ n} b(n)/n` (`tsum_gcd_mul_div_eq`). Since `φ(m) > 0`, strong induction on `m` gives
  `β ≡ 0` on `m ≥ 1` (`divSum_eq_zero`).
* **Sieve.** For a finite set `P` of primes put `S_P(n) = Σ_{n ∣ N, (N/n, ∏P) = 1} b(N)/N`. Then
  `S_∅ = β` and `S_{P ∪ {p}}(n) = S_P(n) − S_P(np)`, so `S_P ≡ 0` for every `P`
  (`sieveSum_eq_zero`). For `P` the primes `≤ y`, every `N ≠ n` in `S_P(n)` has `N/n > y`, so
  `|S_P(n) − b(n)/n| ≤ Σ_{N > y} |b(N)|/N → 0`. Hence `b(n) = 0`. No divisor bound is used.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {b : ℕ → ℝ}

theorem abs_div_le_abs_div_sqrt (b : ℕ → ℝ) (n : ℕ) : |b n| / n ≤ |b n| / Real.sqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.mpr (by positivity)) hs

theorem summable_abs_div (hb : Summable fun n => |b n| / Real.sqrt n) :
    Summable fun n => |b n| / n :=
  Summable.of_nonneg_of_le (fun n => by positivity) (abs_div_le_abs_div_sqrt b) hb

theorem summable_ite_div (hb : Summable fun n => |b n| / Real.sqrt n) (q : ℕ → Prop)
    [DecidablePred q] : Summable fun n => if q n then b n / n else 0 := by
  refine Summable.of_norm_bounded (summable_abs_div hb) fun n => ?_
  split_ifs
  · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  · simp; positivity

/-- `β(d) = Σ_{d ∣ n} b(n)/n`. -/
def divSum (b : ℕ → ℝ) (d : ℕ) : ℝ := ∑' n, if d ∣ n then b n / n else 0

/-- `gcd(m, n) = Σ_{d ∣ m, d ∣ n} φ(d)`. -/
theorem gcd_eq_sum_totient {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ((Nat.gcd m n : ℕ) : ℝ) = ∑ d ∈ m.divisors, if d ∣ n then (Nat.totient d : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  have hdiv : (Nat.gcd m n).divisors = m.divisors.filter (· ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h1, hm.ne'⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left n hm).ne'⟩
  rw [← hdiv, ← Nat.cast_sum, Nat.sum_totient]

/-- **The hypothesis in divisor form**: `Σ_n b(n) gcd(m,n)/n = Σ_{d ∣ m} φ(d) β(d)`. -/
theorem tsum_gcd_mul_div_eq (hb : Summable fun n => |b n| / Real.sqrt n) {m : ℕ} (hm : 0 < m) :
    ∑' n, b n * (Nat.gcd m n : ℝ) / n = ∑ d ∈ m.divisors, (Nat.totient d : ℝ) * divSum b d := by
  have hpt : ∀ n, b n * (Nat.gcd m n : ℝ) / n =
      ∑ d ∈ m.divisors, (Nat.totient d : ℝ) * (if d ∣ n then b n / n else 0) := by
    intro n
    rw [gcd_eq_sum_totient hm n, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  simp_rw [hpt]
  rw [Summable.tsum_finsetSum fun d _ => (summable_ite_div hb (fun n => d ∣ n) |>.mul_left _)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [tsum_mul_left]
  rfl

/-- **`β ≡ 0`** from the hypothesis, by strong induction. -/
theorem divSum_eq_zero (hb : Summable fun n => |b n| / Real.sqrt n)
    (h : ∀ m, 0 < m → ∑' n, b n * (Nat.gcd m n : ℝ) / n = 0) : ∀ d, 0 < d → divSum b d = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hsum := h m hm
    rw [tsum_gcd_mul_div_eq hb hm, ← Finset.sum_erase_add _ _ (Nat.mem_divisors_self m hm.ne')]
      at hsum
    have hrest : ∑ d ∈ m.divisors.erase m, (Nat.totient d : ℝ) * divSum b d = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      have hd' := Finset.mem_erase.mp hd
      have hdm := Nat.mem_divisors.mp hd'.2
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm.1 hm
      have hlt : d < m := lt_of_le_of_ne (Nat.le_of_dvd hm hdm.1) hd'.1
      rw [ih d hlt hdpos, mul_zero]
    rw [hrest, zero_add] at hsum
    have hφ : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
    exact (mul_eq_zero.mp hsum).resolve_left hφ.ne'

/-! ## The sieve -/

/-- `S_P(n) = Σ_{n ∣ N, (N/n, ∏P) = 1} b(N)/N`. -/
def sieveSum (b : ℕ → ℝ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑' N, if n ∣ N ∧ Nat.Coprime (N / n) (∏ p ∈ P, p) then b N / N else 0

theorem sieveSum_empty (b : ℕ → ℝ) (n : ℕ) : sieveSum b ∅ n = divSum b n := by
  unfold sieveSum divSum
  simp

theorem sieveSum_insert (hb : Summable fun n => |b n| / Real.sqrt n) {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) {n : ℕ} (hn : 0 < n) :
    sieveSum b (insert p P) n = sieveSum b P n - sieveSum b P (n * p) := by
  classical
  have hcop : Nat.Coprime p (∏ q ∈ P, q) :=
    Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp (hP q hq)).mpr fun h => hpP (h ▸ hq)
  unfold sieveSum
  rw [← Summable.tsum_sub (summable_ite_div hb _) (summable_ite_div hb _)]
  congr 1
  funext N
  rw [Finset.prod_insert hpP]
  by_cases hnN : n ∣ N
  · obtain ⟨j, rfl⟩ := hnN
    have hj : n * j / n = j := Nat.mul_div_cancel_left j hn
    rw [hj]
    by_cases hpj : p ∣ j
    · obtain ⟨i, rfl⟩ := hpj
      have hi : n * (p * i) / (n * p) = i := by
        rw [show n * (p * i) = (n * p) * i by ring]
        exact Nat.mul_div_cancel_left i (Nat.mul_pos hn hp.pos)
      have hdvd : n * p ∣ n * (p * i) := ⟨i, by ring⟩
      have h1 : ¬ Nat.Coprime (p * i) (p * ∏ q ∈ P, q) := by
        intro hc
        have := Nat.Coprime.coprime_dvd_left (dvd_mul_right p i) hc
        have := Nat.Coprime.coprime_dvd_right (dvd_mul_right p _) this
        have h1 := Nat.Coprime.gcd_eq_one this
        rw [Nat.gcd_self] at h1
        exact hp.ne_one h1
      have h2 : Nat.Coprime (p * i) (∏ q ∈ P, q) ↔ Nat.Coprime i (∏ q ∈ P, q) := by
        rw [Nat.coprime_mul_iff_left]
        exact ⟨fun h => h.2, fun h => ⟨hcop, h⟩⟩
      simp only [dvd_mul_right, true_and, h1, if_false, hi, hdvd, h2]
      split_ifs <;> ring
    · have hndvd : ¬ n * p ∣ n * j := by
        intro h
        exact hpj (Nat.dvd_of_mul_dvd_mul_left hn h)
      have h1 : Nat.Coprime j (p * ∏ q ∈ P, q) ↔ Nat.Coprime j (∏ q ∈ P, q) := by
        rw [Nat.coprime_mul_iff_right]
        refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
        exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpj))
      simp only [dvd_mul_right, true_and, h1, hndvd, false_and, if_false, sub_zero]
  · have hndvd : ¬ n * p ∣ N := fun h => hnN (dvd_trans (dvd_mul_right n p) h)
    simp [hnN, hndvd]

/-- **`S_P ≡ 0`** for every finite set of primes. -/
theorem sieveSum_eq_zero (hb : Summable fun n => |b n| / Real.sqrt n)
    (hβ : ∀ d, 0 < d → divSum b d = 0) :
    ∀ P : Finset ℕ, (∀ q ∈ P, q.Prime) → ∀ n, 0 < n → sieveSum b P n = 0 := by
  classical
  intro P
  induction P using Finset.induction_on with
  | empty => intro _ n hn; rw [sieveSum_empty]; exact hβ n hn
  | insert p P hpP ih =>
    intro hP n hn
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    rw [sieveSum_insert hb hP' (hP p (Finset.mem_insert_self p P)) hpP hn,
      ih hP' n hn, ih hP' (n * p) (Nat.mul_pos hn (hP p (Finset.mem_insert_self p P)).pos),
      sub_zero]

/-- The primes `≤ y`. -/
def primesLe (y : ℕ) : Finset ℕ := (Finset.range (y + 1)).filter Nat.Prime

/-- A number `j > 1` coprime to every prime `≤ y` exceeds `y`. -/
theorem lt_of_coprime_primesLe {y j : ℕ} (hj : 1 < j) (hc : Nat.Coprime j (∏ p ∈ primesLe y, p)) :
    y < j := by
  by_contra hle
  push Not at hle
  have hq := Nat.minFac_prime (by omega : j ≠ 1)
  have hqj : j.minFac ∣ j := Nat.minFac_dvd j
  have hqy : j.minFac ≤ y := (Nat.minFac_le (by omega)).trans hle
  have hmem : j.minFac ∈ primesLe y :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩
  have hdvd : j.minFac ∣ ∏ p ∈ primesLe y, p := Finset.dvd_prod_of_mem _ hmem
  exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hc hqj hdvd)

/-- `|S_P(n) − b(n)/n| ≤ Σ_{N > y} |b(N)|/N` for `P` the primes `≤ y`. -/
theorem abs_sieveSum_sub_le (hb : Summable fun n => |b n| / Real.sqrt n) {n : ℕ} (hn : 0 < n)
    (y : ℕ) :
    |sieveSum b (primesLe y) n - b n / n| ≤ ∑' N, if y < N then |b N| / N else 0 := by
  classical
  have hsplit : sieveSum b (primesLe y) n - b n / n =
      ∑' N, if N ≠ n ∧ n ∣ N ∧ Nat.Coprime (N / n) (∏ p ∈ primesLe y, p) then b N / N else 0 := by
    unfold sieveSum
    have hsingle : (∑' N, if N = n then b N / N else 0) = b n / n := by
      rw [tsum_ite_eq]
    rw [← hsingle, ← Summable.tsum_sub (summable_ite_div hb _) (summable_ite_div hb _)]
    congr 1
    funext N
    by_cases hN : N = n
    · subst hN
      simp [Nat.div_self hn]
    · simp [hN]
  rw [hsplit]
  have hle : ∀ N, ‖if N ≠ n ∧ n ∣ N ∧ Nat.Coprime (N / n) (∏ p ∈ primesLe y, p) then b N / N
      else 0‖ ≤ if y < N then |b N| / N else 0 := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp
    split_ifs with h1 h2
    · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    · exfalso
      obtain ⟨hNn, ⟨j, rfl⟩, hc⟩ := h1
      rw [Nat.mul_div_cancel_left j hn] at hc
      have hj0 : 0 < j := Nat.pos_of_mul_pos_left hNpos
      have hj1 : 1 < j := by
        rcases Nat.lt_or_ge 1 j with h | h
        · exact h
        · have : j = 1 := by omega
          subst this
          exact absurd (mul_one n) hNn
      have hyj := lt_of_coprime_primesLe hj1 hc
      have : j ≤ n * j := Nat.le_mul_of_pos_left j hn
      exact h2 (by omega)
    · simp only [norm_zero]; positivity
    · simp
  have hg : Summable fun N => if y < N then |b N| / N else 0 := by
    refine Summable.of_nonneg_of_le (fun N => by split_ifs <;> positivity) (fun N => ?_)
      (summable_abs_div hb)
    split_ifs
    · exact le_rfl
    · positivity
  have hf : Summable fun N => ‖if N ≠ n ∧ n ∣ N ∧ Nat.Coprime (N / n) (∏ p ∈ primesLe y, p) then
      b N / N else 0‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hg
  exact (norm_tsum_le_tsum_norm hf).trans (Summable.tsum_le_tsum hle hf hg)

/-- The tail `Σ_{N > y} |b(N)|/N` tends to `0`. -/
theorem tendsto_tail (hb : Summable fun n => |b n| / Real.sqrt n) :
    Tendsto (fun y : ℕ => ∑' N, if y < N then |b N| / N else 0) atTop (𝓝 0) := by
  classical
  set g : ℕ → ℝ := fun N => |b N| / N with hg
  have hgs : Summable g := summable_abs_div hb
  have e : ∀ y : ℕ, (∑' N, if y < N then |b N| / N else 0) =
      ∑' N, g N - ∑ N ∈ Finset.range (y + 1), g N := by
    intro y
    have h1 : Summable fun N => if y < N then g N else 0 :=
      Summable.of_nonneg_of_le (fun N => by split_ifs <;> positivity)
        (fun N => by split_ifs <;> simp [hg]; positivity) hgs
    have h2 : (∑' N, if N ∈ Finset.range (y + 1) then g N else 0) =
        ∑ N ∈ Finset.range (y + 1), g N := by
      rw [tsum_eq_sum (s := Finset.range (y + 1)) (fun N hN => if_neg hN)]
      exact Finset.sum_congr rfl fun N hN => if_pos hN
    have h3 : (∑' N, g N) = (∑' N, if y < N then g N else 0) +
        ∑' N, if N ∈ Finset.range (y + 1) then g N else 0 := by
      rw [← Summable.tsum_add h1 (summable_of_ne_finset_zero (s := Finset.range (y + 1))
        (fun N hN => if_neg hN))]
      congr 1
      funext N
      by_cases hN : y < N
      · have : N ∉ Finset.range (y + 1) := by simp; omega
        simp [hN, this]
      · have : N ∈ Finset.range (y + 1) := by simp; omega
        simp [hN, this]
    rw [h2] at h3
    simp only [hg] at h3 ⊢
    linarith
  simp_rw [e]
  have hlim := (hgs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have := (tendsto_const_nhds (x := ∑' N, g N)).sub hlim
  rw [sub_self] at this
  exact this

/-- **Inversion of gcd-weighted series.** If `Σ |b(n)|/√n < ∞` and `Σ_n b(n) gcd(m,n)/n = 0` for
every `m ≥ 1`, then `b(n) = 0` for every `n ≥ 1`. -/
theorem eq_zero_of_tsum_gcd_mul_div_eq_zero (hb : Summable fun n => |b n| / Real.sqrt n)
    (h : ∀ m, 0 < m → ∑' n, b n * (Nat.gcd m n : ℝ) / n = 0) : ∀ n, 0 < n → b n = 0 := by
  intro n hn
  have hβ := divSum_eq_zero hb h
  have hle : ∀ y : ℕ, |b n / n| ≤ ∑' N, if y < N then |b N| / N else 0 := by
    intro y
    have h1 := abs_sieveSum_sub_le hb hn y
    rw [sieveSum_eq_zero hb hβ (primesLe y) (fun q hq => (Finset.mem_filter.mp hq).2) n hn,
      zero_sub, abs_neg] at h1
    exact h1
  have h0 : |b n / n| ≤ 0 := ge_of_tendsto (tendsto_tail hb) (Eventually.of_forall hle)
  have h1 : b n / n = 0 := abs_nonpos_iff.mp h0
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (div_eq_zero_iff.mp h1).resolve_right hn0

end GaloisForLFunctions.HTGeometry
