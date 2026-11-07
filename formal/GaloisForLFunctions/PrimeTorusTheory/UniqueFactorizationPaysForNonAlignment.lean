import GaloisForLFunctions.PrimeTorusTheory.TheFiniteTimeBohrIsometry

/-!
# Unique factorization pays for non-alignment

Below the mixing time the orbit has not filled the torus, and nothing forces it into a given half-space.
This module gives the first obstruction to alignment that holds at every length.

**Theorem** (`le_of_aligned`). Let `G` be a set of primes `≤ y`. Suppose `t > 0` aligns every prime of `G` to
within `ε`: `|t log p − 2πm_p| ≤ ε`, with `2kε < π`. If `C(|G|, k) > ⌊t k log y / π⌋ + 1`, then
`t ≤ 2kε y^k`.

**Mechanism.** The `C(|G|, k)` squarefree products of `k` primes of `G` have logarithms in an interval of length
`k log y`. Past the diagonal range two of them, `a ≠ b`, fall in one box of width `π/t`. Alignment forces
`t log(a/b)` to be within `2kε` of `2πℤ`, hence within `2kε` of `0`. But `a ≠ b` are distinct integers by unique
factorization, so `|log(a/b)| ≥ y^{−k}`.

So at `y = (log T)^A` a time `t ≍ T` is at distance at least `T^{−1/(A−1)−o(1)}` from alignment. In the half-space
language (`defect_ge_of_not_aligned`, `defect_ge_of_pigeonhole`) the column sum at `p^{−½}` stays below its size by a
power of `T`: there *is* a saving against size at every length past the Kronecker scale, and it is polynomially
small.

The proof uses three things and each is necessary: time is a real number multiplying fixed logarithms (group
closure), the steps are logarithms of integers (the gap `y^{−k}`), and the steps are independent (the products are
distinct). It fails at rank one, where products collide, and on rounded orbits, where the steps have been moved
by `1/T`. See `TheRoundedOrbit` and `TheRankLaw`.
-/

open Finset Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- `t` aligns the prime `p` to within `ε`. -/
def AlignedAt (t ε : ℝ) (p : ℕ) : Prop := ∃ m : ℤ, |t * Real.log p - 2 * π * m| ≤ ε

/-- Products of distinct sets of primes are distinct. -/
theorem prod_injOn_primes {G : Finset ℕ} (hG : ∀ p ∈ G, p.Prime) {T T' : Finset ℕ} (hT : T ⊆ G)
    (hT' : T' ⊆ G) (h : ∏ p ∈ T, p = ∏ p ∈ T', p) : T = T' := by
  have h1 := Nat.primeFactors_prod (s := T) fun p hp => hG p (hT hp)
  have h2 := Nat.primeFactors_prod (s := T') fun p hp => hG p (hT' hp)
  rw [← h1, ← h2, h]

theorem log_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    Real.log ((∏ p ∈ T, p : ℕ) : ℝ) = ∑ p ∈ T, Real.log p := by
  push_cast
  exact Real.log_prod fun p hp => by exact_mod_cast (hT p hp).ne_zero

/-- A product of `k` primes `≤ y` is at most `y^k`. -/
theorem prod_primes_le {T : Finset ℕ} {y : ℕ} (hT : ∀ p ∈ T, p ≤ y) :
    ∏ p ∈ T, p ≤ y ^ T.card :=
  Finset.prod_le_pow_card T _ y hT

/-- Alignment of a set of primes transfers to the logarithm of their product. -/
theorem exists_int_abs_log_prod_sub_le {T : Finset ℕ} {t ε : ℝ} (hT : ∀ p ∈ T, p.Prime)
    (hal : ∀ p ∈ T, AlignedAt t ε p) :
    ∃ M : ℤ, |t * Real.log ((∏ p ∈ T, p : ℕ) : ℝ) - 2 * π * M| ≤ T.card * ε := by
  classical
  choose! m hm using hal
  refine ⟨∑ p ∈ T, m p, ?_⟩
  have e : t * Real.log ((∏ p ∈ T, p : ℕ) : ℝ) - 2 * π * ((∑ p ∈ T, m p : ℤ) : ℝ) =
      ∑ p ∈ T, (t * Real.log p - 2 * π * (m p : ℝ)) := by
    rw [log_prod_primes hT, Finset.mul_sum, Finset.sum_sub_distrib]
    push_cast
    rw [Finset.mul_sum]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul T _ ε fun p hp => hm p hp
  rwa [nsmul_eq_mul] at this

/-- **Pigeonhole non-alignment.** See the module docstring. -/
theorem le_of_aligned {G : Finset ℕ} {y k : ℕ} {t ε : ℝ} (ht : 0 < t) (hy : 1 ≤ y)
    (hG : ∀ p ∈ G, p.Prime) (hGy : ∀ p ∈ G, p ≤ y) (hε : 2 * (k : ℝ) * ε < π)
    (hal : ∀ p ∈ G, AlignedAt t ε p)
    (hcard : ⌊t * k * Real.log y / π⌋₊ + 1 < G.card.choose k) :
    t ≤ 2 * (k : ℝ) * ε * (y : ℝ) ^ k := by
  classical
  set box : Finset ℕ → ℕ := fun T => ⌊t * Real.log ((∏ p ∈ T, p : ℕ) : ℝ) / π⌋₊ with hbox
  have hpi : 0 < π := Real.pi_pos
  have hy' : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hmaps : Set.MapsTo box (G.powersetCard k : Set (Finset ℕ))
      (Finset.range (⌊t * k * Real.log y / π⌋₊ + 1) : Set ℕ) := by
    intro T hT
    have hT' := Finset.mem_powersetCard.mp hT
    simp only [Finset.coe_range, Set.mem_Iio, hbox]
    rw [Nat.lt_succ_iff]
    refine Nat.floor_le_floor (div_le_div_of_nonneg_right ?_ hpi.le)
    have hlog : Real.log ((∏ p ∈ T, p : ℕ) : ℝ) ≤ k * Real.log y := by
      have h1 : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (y : ℝ) ^ k := by
        have := prod_primes_le (T := T) (y := y) fun p hp => hGy p (hT'.1 hp)
        rw [hT'.2] at this
        exact_mod_cast this
      have hpos : (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by
        exact_mod_cast Finset.prod_pos fun p hp => (hG p (hT'.1 hp)).pos
      calc
        Real.log ((∏ p ∈ T, p : ℕ) : ℝ) ≤ Real.log ((y : ℝ) ^ k) := Real.log_le_log hpos h1
        _ = k * Real.log y := Real.log_pow _ _
    calc
      t * Real.log ((∏ p ∈ T, p : ℕ) : ℝ) ≤ t * (k * Real.log y) :=
        mul_le_mul_of_nonneg_left hlog ht.le
      _ = t * k * Real.log y := by ring
  have hcard' : (Finset.range (⌊t * k * Real.log y / π⌋₊ + 1)).card < (G.powersetCard k).card := by
    rw [Finset.card_range, Finset.card_powersetCard]
    exact hcard
  obtain ⟨T, hT, T', hT', hne, hsame⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard' hmaps
  have hT1 := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT)
  have hT2 := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT')
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hG p (hT1.1 hp)
  have hTp' : ∀ p ∈ T', p.Prime := fun p hp => hG p (hT2.1 hp)
  set a := ∏ p ∈ T, p with ha
  set b := ∏ p ∈ T', p with hb
  have ha0 : 0 < a := Finset.prod_pos fun p hp => (hTp p hp).pos
  have hb0 : 0 < b := Finset.prod_pos fun p hp => (hTp' p hp).pos
  have hab : a ≠ b := fun h => hne (prod_injOn_primes hG hT1.1 hT2.1 h)
  -- One box: the rotated logarithms differ by less than `π`.
  have hboxlt : |t * Real.log a - t * Real.log b| < π := by
    have hA0 : 0 ≤ t * Real.log a / π :=
      div_nonneg (mul_nonneg ht.le (Real.log_natCast_nonneg a)) hpi.le
    have hB0 : 0 ≤ t * Real.log b / π :=
      div_nonneg (mul_nonneg ht.le (Real.log_natCast_nonneg b)) hpi.le
    have h1 := Nat.floor_le hA0
    have h2 := Nat.lt_floor_add_one (t * Real.log a / π)
    have h3 := Nat.floor_le hB0
    have h4 := Nat.lt_floor_add_one (t * Real.log b / π)
    have hs : ⌊t * Real.log a / π⌋₊ = ⌊t * Real.log b / π⌋₊ := hsame
    rw [hs] at h1 h2
    have h5 : |t * Real.log a / π - t * Real.log b / π| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hpi, div_lt_one hpi] at h5
    exact h5
  -- Alignment: the difference is within `2kε` of `2πℤ`.
  obtain ⟨M, hM⟩ := exists_int_abs_log_prod_sub_le hTp fun p hp => hal p (hT1.1 hp)
  obtain ⟨M', hM'⟩ := exists_int_abs_log_prod_sub_le hTp' fun p hp => hal p (hT2.1 hp)
  rw [hT1.2] at hM
  rw [hT2.2] at hM'
  have hdiff : |(t * Real.log a - t * Real.log b) - 2 * π * ((M - M' : ℤ) : ℝ)| ≤ 2 * k * ε := by
    have e : (t * Real.log a - t * Real.log b) - 2 * π * ((M - M' : ℤ) : ℝ) =
        (t * Real.log a - 2 * π * M) - (t * Real.log b - 2 * π * M') := by
      push_cast
      ring
    rw [e]
    calc
      _ ≤ |t * Real.log a - 2 * π * M| + |t * Real.log b - 2 * π * M'| := abs_sub _ _
      _ ≤ 2 * k * ε := by linarith
  -- Hence the integer vanishes.
  have hint : M - M' = 0 := by
    by_contra hne0
    have h1 : (1 : ℝ) ≤ |((M - M' : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |M - M'| := Int.one_le_abs hne0
      exact_mod_cast this
    have h2 : 2 * π ≤ |2 * π * ((M - M' : ℤ) : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      nlinarith
    have h3 : |2 * π * ((M - M' : ℤ) : ℝ)| ≤
        |t * Real.log a - t * Real.log b| +
          |(t * Real.log a - t * Real.log b) - 2 * π * ((M - M' : ℤ) : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (2 * π * ((M - M' : ℤ) : ℝ)) (t * Real.log a - t * Real.log b)
      rw [abs_sub_comm (2 * π * ((M - M' : ℤ) : ℝ))] at this
      linarith
    linarith
  rw [hint] at hdiff
  simp only [Int.cast_zero, mul_zero, sub_zero] at hdiff
  -- The integer gap.
  have hgap := HTGeometry.inv_max_le_abs_log_sub_log ha0 hb0 hab
  have hmaxle : ((max a b : ℕ) : ℝ) ≤ (y : ℝ) ^ k := by
    have h1 : a ≤ y ^ k := by
      have := prod_primes_le (T := T) (y := y) fun p hp => hGy p (hT1.1 hp)
      rwa [hT1.2] at this
    have h2 : b ≤ y ^ k := by
      have := prod_primes_le (T := T') (y := y) fun p hp => hGy p (hT2.1 hp)
      rwa [hT2.2] at this
    exact_mod_cast max_le h1 h2
  have hmaxpos : (0 : ℝ) < ((max a b : ℕ) : ℝ) := by
    have : 0 < max a b := lt_max_of_lt_left ha0
    exact_mod_cast this
  have hypos : (0 : ℝ) < (y : ℝ) ^ k := pow_pos (by linarith) k
  have hinv : ((y : ℝ) ^ k)⁻¹ ≤ |Real.log a - Real.log b| :=
    (inv_anti₀ hmaxpos hmaxle).trans hgap
  have hfin : t * ((y : ℝ) ^ k)⁻¹ ≤ 2 * k * ε := by
    calc
      t * ((y : ℝ) ^ k)⁻¹ ≤ t * |Real.log a - Real.log b| := mul_le_mul_of_nonneg_left hinv ht.le
      _ = |t * Real.log a - t * Real.log b| := by
        rw [← mul_sub, abs_mul, abs_of_pos ht]
      _ ≤ 2 * k * ε := hdiff
  rw [← div_eq_mul_inv, div_le_iff₀ hypos] at hfin
  exact hfin

/-- Some prime of `G` is not aligned to within `ε`, for every `ε < t/(2k y^k)` with `2kε < π`. -/
theorem exists_not_aligned_of_pigeonhole {G : Finset ℕ} {y k : ℕ} {t ε : ℝ} (ht : 0 < t) (hy : 1 ≤ y)
    (hG : ∀ p ∈ G, p.Prime) (hGy : ∀ p ∈ G, p ≤ y) (hε : 2 * (k : ℝ) * ε < π)
    (hlt : 2 * (k : ℝ) * ε * (y : ℝ) ^ k < t)
    (hcard : ⌊t * k * Real.log y / π⌋₊ + 1 < G.card.choose k) :
    ∃ p ∈ G, ¬ AlignedAt t ε p := by
  by_contra hcon
  push Not at hcon
  exact absurd (le_of_aligned ht hy hG hGy hε hcon hcard) (not_le.mpr hlt)

open Classical in
/-- **Most primes are not aligned.** The aligned primes of `P` form a set whose `k`-subsets fit in the boxes. -/
theorem choose_card_aligned_le {P : Finset ℕ} {y k : ℕ} {t ε : ℝ} (ht : 0 < t) (hy : 1 ≤ y)
    (hP : ∀ p ∈ P, p.Prime) (hPy : ∀ p ∈ P, p ≤ y) (hε : 2 * (k : ℝ) * ε < π)
    (hlt : 2 * (k : ℝ) * ε * (y : ℝ) ^ k < t) :
    (P.filter (AlignedAt t ε)).card.choose k ≤ ⌊t * k * Real.log y / π⌋₊ + 1 := by
  by_contra hcon
  obtain ⟨p, hp, hnot⟩ := exists_not_aligned_of_pigeonhole (G := P.filter (AlignedAt t ε)) ht hy
    (fun p hp => hP p (Finset.mem_filter.mp hp).1) (fun p hp => hPy p (Finset.mem_filter.mp hp).1)
    hε hlt (not_le.mp hcon)
  exact hnot (Finset.mem_filter.mp hp).2

/-- A phase far from `2πℤ` costs a definite amount in its cosine. -/
theorem one_sub_cos_ge_of_not_aligned {t ε : ℝ} {p : ℕ} (hε : 0 ≤ ε) (h : ¬ AlignedAt t ε p) :
    2 / π ^ 2 * ε ^ 2 ≤ 1 - Real.cos (t * Real.log p) := by
  set x := t * Real.log p with hx
  set m : ℤ := round (x / (2 * π)) with hm
  have hpi : 0 < π := Real.pi_pos
  have h2pi : 0 < 2 * π := by positivity
  set δ := x - 2 * π * m with hδ
  have hδε : ε < |δ| := by
    by_contra hle
    exact h ⟨m, not_lt.mp hle⟩
  have hδpi : |δ| ≤ π := by
    have h1 := abs_sub_round (x / (2 * π))
    have e : δ = (2 * π) * (x / (2 * π) - m) := by
      rw [hδ]
      field_simp
    rw [e, abs_mul, abs_of_pos h2pi]
    nlinarith
  have hcos : Real.cos x = Real.cos δ := by
    have : x = δ + m * (2 * π) := by
      rw [hδ]
      ring
    rw [this, Real.cos_add_int_mul_two_pi]
  -- Jordan's inequality at half the angle.
  have hjordan : 2 / π * (|δ| / 2) ≤ |Real.sin (δ / 2)| := by
    have h0 : 0 ≤ |δ| / 2 := by positivity
    have h1 : |δ| / 2 ≤ π / 2 := by linarith
    have := Real.mul_le_sin h0 h1
    have e : |Real.sin (δ / 2)| = Real.sin (|δ| / 2) := by
      rcases le_total 0 δ with hs | hs
      · rw [abs_of_nonneg hs, abs_of_nonneg]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by
          rw [abs_of_nonneg hs] at hδpi
          linarith)
      · rw [abs_of_nonpos hs, abs_of_nonpos]
        · rw [show -δ / 2 = -(δ / 2) by ring, Real.sin_neg]
        · exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by
            rw [abs_of_nonpos hs] at hδpi
            linarith)
    rw [e]
    exact this
  have h1 : 1 - Real.cos δ = chord δ ^ 2 / 2 := one_sub_cos_eq_chord_sq δ
  have h2 : chord δ ^ 2 = 4 * |Real.sin (δ / 2)| ^ 2 := by
    unfold chord
    ring
  rw [hcos, h1, h2]
  have hb : (|δ| / π) ≤ |Real.sin (δ / 2)| := by
    calc
      |δ| / π = 2 / π * (|δ| / 2) := by field_simp
      _ ≤ _ := hjordan
  have hb2 : (|δ| / π) ^ 2 ≤ |Real.sin (δ / 2)| ^ 2 :=
    pow_le_pow_left₀ (by positivity) hb 2
  have hε2 : ε ^ 2 ≤ |δ| ^ 2 := pow_le_pow_left₀ hε hδε.le 2
  have e3 : 2 / π ^ 2 * ε ^ 2 ≤ 2 * (|δ| / π) ^ 2 := by
    rw [div_pow]
    have : 2 / π ^ 2 * ε ^ 2 = 2 * (ε ^ 2 / π ^ 2) := by ring
    rw [this]
    have h3 : ε ^ 2 / π ^ 2 ≤ |δ| ^ 2 / π ^ 2 :=
      div_le_div_of_nonneg_right hε2 (by positivity)
    linarith
  linarith

/-- The prime phase system: steps `log r`, weights `a r`. -/
def primeSystem (Q : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) : PhaseSystem Q where
  step r := Real.log (r : ℕ)
  weight r := a r
  weight_nonneg r := ha r r.2

theorem primeSystem_defect (Q : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) (t : ℝ) :
    (primeSystem Q a ha).defect t = ∑ r ∈ Q, a r * (1 - Real.cos (t * Real.log r)) := by
  rw [PhaseSystem.defect_eq_sum]
  exact Finset.sum_coe_sort Q fun r => a r * (1 - Real.cos (t * Real.log r))

theorem primeSystem_column (Q : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) (t : ℝ) :
    (primeSystem Q a ha).column t = ∑ r ∈ Q, a r * Real.cos (t * Real.log r) :=
  Finset.sum_coe_sort Q fun r => a r * Real.cos (t * Real.log r)

theorem primeSystem_size (Q : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) :
    (primeSystem Q a ha).size = ∑ r ∈ Q, a r :=
  Finset.sum_coe_sort Q a

/-- A prime off alignment contributes to the defect of a system containing it. -/
theorem defect_ge_of_not_aligned {Q : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ r ∈ Q, 0 ≤ a r) {t ε : ℝ}
    (hε : 0 ≤ ε) {p : ℕ} (hp : p ∈ Q) (hnot : ¬ AlignedAt t ε p) :
    a p * (2 / π ^ 2 * ε ^ 2) ≤ (primeSystem Q a ha).defect t := by
  rw [primeSystem_defect]
  have hnn : ∀ r ∈ Q, 0 ≤ a r * (1 - Real.cos (t * Real.log r)) := fun r hr =>
    mul_nonneg (ha r hr) (by linarith [Real.cos_le_one (t * Real.log r)])
  refine le_trans ?_ (Finset.single_le_sum hnn hp)
  exact mul_le_mul_of_nonneg_left (one_sub_cos_ge_of_not_aligned hε hnot) (ha p hp)

/-- **The saving against size.** Past the diagonal range the defect is at least the smallest weight times
`(2/π²) ε²`, with `ε` below `t/(2k y^k)`. -/
theorem defect_ge_of_pigeonhole {Q : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ r ∈ Q, 0 ≤ a r) {y k : ℕ}
    {t ε w : ℝ} (ht : 0 < t) (hy : 1 ≤ y) (hε0 : 0 ≤ ε) (hQ : ∀ p ∈ Q, p.Prime)
    (hQy : ∀ p ∈ Q, p ≤ y) (hw : ∀ p ∈ Q, w ≤ a p) (hε : 2 * (k : ℝ) * ε < π)
    (hlt : 2 * (k : ℝ) * ε * (y : ℝ) ^ k < t)
    (hcard : ⌊t * k * Real.log y / π⌋₊ + 1 < Q.card.choose k) :
    w * (2 / π ^ 2 * ε ^ 2) ≤ (primeSystem Q a ha).defect t := by
  obtain ⟨p, hp, hnot⟩ := exists_not_aligned_of_pigeonhole ht hy hQ hQy hε hlt hcard
  refine le_trans ?_ (defect_ge_of_not_aligned ha hε0 hp hnot)
  exact mul_le_mul_of_nonneg_right (hw p hp) (by positivity)

end

end GaloisForLFunctions.PrimeTorusTheory
