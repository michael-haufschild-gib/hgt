import GaloisForLFunctions.PrimeTorusTheory.TheSavingAtEveryLength

/-!
# The saving away from small primes

The mean of the distance holds on every progression `r + qm`. Summing over `r` coprime to `q` keeps only integers without prime factors in
`q`, so the mass of misaligned primes survives the deletion of every prime dividing `q`, at the cost of the density `φ(q)/q`:

`Σ_{p ∤ q, p < qK} ‖t log p/2π‖/p ≥ (φ(q)/q)/(10⁵ L⁴ ℓ²)` for `K ≥ 48 L² ℓ` (`totient_div_le_sum_primes_coprime_of_large`).

If `q` contains every prime up to `P`, the critical weights then gain `√P`:

`Σ_{p ∤ q, p < qK} (1 − cos(t log p))/√p ≥ 4 √P ((φ(q)/q)/(10⁵ L⁴ ℓ²))²` (`le_sum_primes_critical_coprime_of_large`).

So the saving cannot sit on primes up to about `log N`, and its size grows with the length `N = qK`. The primes near `N` are not reached: the
progressions leave every prime above `log N` free.
-/

open Finset Filter Topology Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The primes below `N` that do not divide `q`. -/
def coprimePrimes (q N : ℕ) : Finset ℕ := N.primesBelow.filter fun p => ¬ p ∣ q

theorem mem_coprimePrimes {q N p : ℕ} :
    p ∈ coprimePrimes q N ↔ (p < N ∧ p.Prime) ∧ ¬ p ∣ q := by
  simp [coprimePrimes, Nat.mem_primesBelow]

/-- The distance over integers coprime to `q` is carried by the primes not dividing `q`. -/
theorem sum_coprime_phaseDist_le (t : ℝ) (q N : ℕ) :
    ∑ n ∈ range N, (if q.Coprime n then phaseDist t n else 0) ≤
      2 * (N : ℝ) * ∑ p ∈ coprimePrimes q N, phaseDist t p / p := by
  classical
  have hstep : ∀ n ∈ range N, (if q.Coprime n then phaseDist t n else 0) ≤
      ∑ p ∈ coprimePrimes q N, (n.factorization p : ℝ) * phaseDist t p := by
    intro n hn
    have hnn : 0 ≤ ∑ p ∈ coprimePrimes q N, (n.factorization p : ℝ) * phaseDist t p :=
      Finset.sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (phaseDist_nonneg t p)
    split_ifs with hco
    · refine (phaseDist_le_factorization t n).trans (le_of_eq ?_)
      refine Finset.sum_subset (fun p hp => ?_) fun p _ hp => ?_
      · have hp' := Nat.mem_primeFactors.mp hp
        refine mem_coprimePrimes.mpr ⟨⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1)
          (Finset.mem_range.mp hn), hp'.1⟩, fun hd => ?_⟩
        exact hp'.1.not_dvd_one (hco ▸ Nat.dvd_gcd hd hp'.2.1)
      · have : n.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
          exact hp
        rw [this]
        simp
    · exact hnn
  calc ∑ n ∈ range N, (if q.Coprime n then phaseDist t n else 0) ≤
        ∑ n ∈ range N, ∑ p ∈ coprimePrimes q N, (n.factorization p : ℝ) * phaseDist t p :=
        Finset.sum_le_sum hstep
    _ = ∑ p ∈ coprimePrimes q N, (∑ n ∈ range N, (n.factorization p : ℝ)) * phaseDist t p := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
    _ ≤ ∑ p ∈ coprimePrimes q N, (2 * (N : ℝ) / p) * phaseDist t p := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact mul_le_mul_of_nonneg_right
          (sum_factorization_le (mem_coprimePrimes.mp hp).1.2 N) (phaseDist_nonneg t p)
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

/-- **The mass away from `q`**, for a word of height `H`. -/
theorem WordSetup.totient_div_le_sum_primes_coprime {H R : ℝ} {M k N₁ q K : ℕ} {c : ℕ → ℤ} {t : ℝ}
    (S : WordSetup H R M k N₁ c t) (hq : 1 ≤ q) (hK : 6 * M + 6 ≤ K) :
    (q.totient : ℝ) / q / (96 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) ≤
      ∑ p ∈ coprimePrimes q (q * K), phaseDist t p / p := by
  classical
  have hH0 : 0 < H := by linarith [S.one_le_H]
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hK0 : (0 : ℝ) < K := by
    have : 0 < K := by omega
    exact_mod_cast this
  set C : ℝ := 48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2 with hC
  have hCpos : 0 < C := by positivity
  -- one residue class
  have hclass : ∀ r ∈ (range q).filter fun r => q.Coprime r,
      (K : ℝ) / C ≤ ∑ m ∈ range K, phaseDist t (r + q * m) := by
    intro r hr
    have hr' : r ≤ q := (Finset.mem_range.mp (Finset.mem_filter.mp hr).1).le
    have h := S.le_sum_rotDist_ap 0 hq hr' hK
    refine h.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun m _ => rotDist_zero t _
  have hlow : (q.totient : ℝ) * ((K : ℝ) / C) ≤
      ∑ r ∈ (range q).filter (fun r => q.Coprime r), ∑ m ∈ range K, phaseDist t (r + q * m) := by
    calc (q.totient : ℝ) * ((K : ℝ) / C) =
        ∑ _r ∈ (range q).filter (fun r => q.Coprime r), (K : ℝ) / C := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.totient_eq_card_coprime]
      _ ≤ _ := Finset.sum_le_sum hclass
  -- all integers coprime to `q`
  have hall : ∑ n ∈ range (q * K), (if q.Coprime n then phaseDist t n else 0) =
      ∑ r ∈ (range q).filter (fun r => q.Coprime r), ∑ m ∈ range K, phaseDist t (r + q * m) := by
    rw [sum_range_mul_eq, Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : q.Coprime r
    · rw [if_pos hr]
      refine Finset.sum_congr rfl fun m _ => ?_
      have : q.Coprime (q * m + r) := by simpa using hr
      rw [if_pos this, add_comm]
    · rw [if_neg hr]
      refine Finset.sum_eq_zero fun m _ => ?_
      have : ¬ q.Coprime (q * m + r) := by simpa using hr
      rw [if_neg this]
  have hup := sum_coprime_phaseDist_le t q (q * K)
  rw [hall] at hup
  set P : ℝ := ∑ p ∈ coprimePrimes q (q * K), phaseDist t p / p with hP
  have hmain : (q.totient : ℝ) * ((K : ℝ) / C) ≤ 2 * ((q : ℝ) * K) * P := by
    have e : ((q * K : ℕ) : ℝ) = (q : ℝ) * K := by push_cast; ring
    rw [e] at hup
    exact hlow.trans hup
  have e2 : (q.totient : ℝ) / q / (96 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) = (q.totient : ℝ) / q / (2 * C) := by
    rw [hC]
    ring
  rw [e2, div_div, div_le_iff₀ (by positivity)]
  have hdiv : (q.totient : ℝ) * ((K : ℝ) / C) = (K : ℝ) * ((q.totient : ℝ) / C) := by ring
  have hdiv2 : 2 * ((q : ℝ) * K) * P = (K : ℝ) * (2 * (q : ℝ) * P) := by ring
  rw [hdiv, hdiv2] at hmain
  have h3 := le_of_mul_le_mul_left hmain hK0
  rw [div_le_iff₀ hCpos] at h3
  nlinarith

/-- A telescoping bound for `1/(n√n)`. -/
theorem inv_mul_sqrt_le_sub {n : ℕ} (hn : 1 ≤ n) :
    1 / (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ)) ≤ 2 * (1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ)) := by
  set a : ℝ := √(n : ℝ) with ha
  set b : ℝ := √((n + 1 : ℕ) : ℝ) with hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hapos : 0 < a := Real.sqrt_pos.mpr hn0
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a * a = n := Real.mul_self_sqrt hn0.le
  have hb2 : b * b = (n : ℝ) + 1 := by
    rw [hb, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have hb2' : (((n + 1 : ℕ) : ℝ)) = b * b := by
    rw [hb2]
    push_cast
    ring
  have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
  rw [hb2']
  have h1 : b * b - a * a = 1 := by rw [ha2, hb2]; ring
  have e : 1 / a - 1 / b = (b - a) / (a * b) := by
    field_simp
  have h2 : b - a = 1 / (a + b) := by
    field_simp
    nlinarith
  rw [e, h2, div_div, mul_div_assoc', mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : a * b * (a + b) ≤ 2 * (b * b * b) := by nlinarith [mul_pos hapos hbpos]
  nlinarith

/-- `Σ_{n > P} n^{-3/2} ≤ 2/√P`, over any finite range. -/
theorem sum_Ioo_inv_mul_sqrt_le {P : ℕ} (hP : 1 ≤ P) (N : ℕ) :
    ∑ n ∈ Finset.Ioc P (P + N), 1 / ((n : ℝ) * √(n : ℝ)) ≤
      2 * (1 / √(P : ℝ) - 1 / √((P + N : ℕ) : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega)]
    have h := inv_mul_sqrt_le_sub (n := P + N) (by omega)
    linarith

/-- If `q` contains every prime up to `P`, the critical column sum gains `√P` over the square of the mass. -/
theorem sqrt_mul_sq_le_critical_coprime (t : ℝ) {q P N : ℕ} (hP : 1 ≤ P)
    (hq : ∀ p : ℕ, p.Prime → p ≤ P → p ∣ q) :
    4 * √(P : ℝ) * (∑ p ∈ coprimePrimes q N, phaseDist t p / p) ^ 2 ≤
      ∑ p ∈ coprimePrimes q N, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  classical
  set G := coprimePrimes q N with hG
  have hgt : ∀ p ∈ G, P < p ∧ p.Prime := by
    intro p hp
    have h := mem_coprimePrimes.mp hp
    refine ⟨?_, h.1.2⟩
    by_contra hle
    exact h.2 (hq p h.1.2 (not_lt.mp hle))
  set A : ℝ := ∑ p ∈ G, phaseDist t p / p with hA
  set D : ℝ := ∑ p ∈ G, phaseDist t p ^ 2 / √(p : ℝ) with hD
  have hp2 : ∀ p ∈ G, (0 : ℝ) < √(p : ℝ) := fun p hp =>
    Real.sqrt_pos.mpr (by exact_mod_cast (hgt p hp).2.pos)
  have hcauchy : A ^ 2 ≤ D * ∑ p ∈ G, 1 / ((p : ℝ) * √(p : ℝ)) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => by positivity)
      (fun p _ => by positivity) fun p hp => le_of_eq ?_
    have hs := hp2 p hp
    have hss : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
    have hpp : (0 : ℝ) < p := by
      rw [← hss]
      positivity
    field_simp
    nlinarith
  have hPr : (0 : ℝ) < √(P : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hP)
  have htail : ∑ p ∈ G, 1 / ((p : ℝ) * √(p : ℝ)) ≤ 2 / √(P : ℝ) := by
    have hsub : G ⊆ Finset.Ioc P (P + N) := by
      intro p hp
      have h1 := (hgt p hp).1
      have h2 := (mem_coprimePrimes.mp hp).1.1
      exact Finset.mem_Ioc.mpr ⟨h1, by omega⟩
    have h3 : ∑ p ∈ G, 1 / ((p : ℝ) * √(p : ℝ)) ≤
        ∑ p ∈ Finset.Ioc P (P + N), 1 / ((p : ℝ) * √(p : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    have h4 := sum_Ioo_inv_mul_sqrt_le hP N
    have h5 : (0 : ℝ) ≤ 1 / √((P + N : ℕ) : ℝ) := by positivity
    have e : 2 / √(P : ℝ) = 2 * (1 / √(P : ℝ)) := by ring
    rw [e]
    linarith
  have hDnn : 0 ≤ D := Finset.sum_nonneg fun p _ => by positivity
  have hA2 : √(P : ℝ) * A ^ 2 ≤ 2 * D := by
    have h1 : A ^ 2 ≤ D * (2 / √(P : ℝ)) :=
      hcauchy.trans (mul_le_mul_of_nonneg_left htail hDnn)
    have h2 := mul_le_mul_of_nonneg_left h1 hPr.le
    have e : √(P : ℝ) * (D * (2 / √(P : ℝ))) = 2 * D := by
      field_simp
    linarith
  have hcol : 8 * D ≤ ∑ p ∈ G, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
    rw [hD, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h1 := eight_mul_sq_le_one_sub_cos (t * Real.log p / (2 * π))
    have e : 2 * π * (t * Real.log p / (2 * π)) = t * Real.log p := by
      field_simp
    rw [e] at h1
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h1 (hp2 p hp).le
  linarith

/-- **The mass away from `q`.** With `L = log |t|` and `ℓ = log L`, for every `q ≥ 1` and `K ≥ 48 L² ℓ`. -/
theorem totient_div_le_sum_primes_coprime_of_large :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ q K : ℕ, 1 ≤ q →
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ K →
      (q.totient : ℝ) / q / (100000 * Real.log |t| ^ 4 * Real.log (Real.log |t|) ^ 2) ≤
        ∑ p ∈ coprimePrimes q (q * K), phaseDist t p / p := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht q K hq hK => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hK ⊢
  generalize Real.log L = ℓ at h hK ⊢
  have hL := h.hundred_le
  have hℓ := h.one_le
  obtain ⟨M, k, N₁, c, hS, hKnat, hsq⟩ := h.exists_data hexp hK
  refine le_trans ?_ (hS.totient_div_le_sum_primes_coprime hq hKnat)
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have hpos : 0 < L ^ 4 * ℓ ^ 2 := by positivity
  norm_num
  nlinarith

/-- **The critical saving away from `q`.** If `q` contains every prime up to `P`, the saving gains `√P`. -/
theorem le_sum_primes_critical_coprime_of_large :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ q K P : ℕ, 1 ≤ q → 1 ≤ P →
      (∀ p : ℕ, p.Prime → p ≤ P → p ∣ q) →
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ K →
      4 * √(P : ℝ) *
          ((q.totient : ℝ) / q / (100000 * Real.log |t| ^ 4 * Real.log (Real.log |t|) ^ 2)) ^ 2 ≤
        ∑ p ∈ coprimePrimes q (q * K), (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  obtain ⟨T₀, hT₀, hmass⟩ := totient_div_le_sum_primes_coprime_of_large
  refine ⟨T₀, hT₀, fun t ht q K P hq hP hqP hK => ?_⟩
  refine le_trans ?_ (sqrt_mul_sq_le_critical_coprime t hP hqP)
  have h1 := hmass t ht q K hq hK
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ h1 2) (by positivity)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hτ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  refine div_nonneg (div_nonneg hτ hq0) ?_
  have : 0 ≤ Real.log (Real.log |t|) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ Real.log |t| ^ 4 := by positivity
  positivity

end

end GaloisForLFunctions.PrimeTorusTheory
