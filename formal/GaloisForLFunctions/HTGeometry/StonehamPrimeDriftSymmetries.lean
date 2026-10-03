import GaloisForLFunctions.HTGeometry.StonehamPrimeDriftLaw

/-!
# Symmetries of the window drift of `α_{2,p}`

Over a full period of the orbit `C = a⟨4⟩ mod pᵏ` the drift weight satisfies two exact laws:

* **doubling**: `F(C) + F(2C) = 0`, because `w(r) + w(2r) = b₁(r) − b₁(4r)` telescopes along the
  orbit (`w = b₁ − b₂` in binary digits);
* **reflection**: `F(−C) = −F(C)`.

Hence the window drift vanishes as soon as `2 ∈ ⟨4⟩` (the order of `2` modulo `p` is odd) or
`−1 ∈ ⟨4⟩` modulo `p`; no Wieferich-type condition is needed, since both memberships lift from `p`
to `pᵏ`.  Then the parity drift of `α_p` vanishes at every window end:

* `drift_stonehamP_windowEnd_of_two_mem` (e.g. `p = 7, 23, 31, 47, 73, 89, 127`);
* `drift_stonehamP_windowEnd_of_neg_one_mem` (e.g. `p = 5, 13, 17, 29, 37, 41`).

A nonzero slope therefore requires `2 ∉ ⟨4⟩` and `−1 ∉ ⟨4⟩`, as for `p ≡ 3 (mod 8)` with `4`
generating the squares, where the slope is `3p h(−p)`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.StonehamPrimeDrift

open BinaryParityDrift StonehamParityDrift

/-! ### The doubling law for the drift weight -/

theorem digitWeight_doubling {d e : ℕ} (hd : d < 4) (he : e = 2 * d ∨ e = 2 * d + 1) :
    digitWeight (d : ℤ) + digitWeight ((e - 4 * (d / 2) : ℕ) : ℤ) =
      ((d / 2 : ℕ) : ℤ) - ((e - 2 * d : ℕ) : ℤ) := by
  interval_cases d <;> rcases he with rfl | rfl <;> decide

/-- `w(r) + w(2r) = b₁(r) − b₁(4r)` for the first base-4 digit weight of `r/q`. -/
theorem quarterWeight_add_two_mul {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    quarterWeight q r + quarterWeight q (2 * r % q) =
      ((2 * r / q : ℕ) : ℤ) - ((2 * (4 * r % q) / q : ℕ) : ℤ) := by
  have h4 := Nat.div_add_mod (4 * r) q
  have hsq : 4 * r % q < q := Nat.mod_lt _ hq
  have hd4 : 4 * r / q < 4 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
  have he : 8 * r / q = 2 * (4 * r / q) + 2 * (4 * r % q) / q := by
    have : 8 * r = 2 * (4 * r % q) + q * (2 * (4 * r / q)) := by
      rw [show q * (2 * (4 * r / q)) = 2 * (q * (4 * r / q)) by ring]; omega
    rw [this, Nat.add_mul_div_left _ _ hq]; ring
  have he' : 2 * (4 * r % q) / q ≤ 1 := by
    have : 2 * (4 * r % q) / q < 2 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
    omega
  have hb1 : 2 * r / q = 4 * r / q / 2 := by
    rw [Nat.div_div_eq_div_mul, show 4 * r = 2 * (2 * r) by ring, show q * 2 = 2 * q by ring,
      Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
  have hm1 : 4 * (2 * r % q) / q = 8 * r / q - 4 * (2 * r / q) := by
    have h2 := Nat.div_add_mod (2 * r) q
    have hle : q * (4 * (2 * r / q)) ≤ 8 * r := by
      rw [show q * (4 * (2 * r / q)) = 4 * (q * (2 * r / q)) by ring]; omega
    have e : 4 * (2 * r % q) = 8 * r - q * (4 * (2 * r / q)) := by
      rw [show q * (4 * (2 * r / q)) = 4 * (q * (2 * r / q)) by ring]; omega
    rw [e, Nat.sub_mul_div (8 * r) q (4 * (2 * r / q))]
  have hm2 : 2 * (4 * r % q) / q = 8 * r / q - 2 * (4 * r / q) := by
    rw [he, Nat.add_sub_cancel_left]
  unfold quarterWeight
  rw [hm1, hm2, hb1]
  exact digitWeight_doubling hd4 (by rw [he]; omega)

/-! ### Period sums -/

theorem sum_range_shift_of_periodic {M : Type*} [AddCommGroup M] {f : ℕ → M} {L : ℕ}
    (hf : ∀ i, f (i + L) = f i) (s : ℕ) : ∑ i ∈ range L, f (i + s) = ∑ i ∈ range L, f i := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := Finset.sum_range_succ (fun i => f (i + s)) L
    have h2 := Finset.sum_range_succ' (fun i => f (i + s)) L
    rw [show L + s = s + L by ring, hf] at h1
    rw [zero_add] at h2
    have : ∑ i ∈ range L, f (i + (s + 1)) = ∑ i ∈ range L, f (i + 1 + s) :=
      sum_congr rfl fun i _ => by rw [show i + (s + 1) = i + 1 + s by ring]
    rw [this]
    have h3 : ∑ i ∈ range L, f (i + 1 + s) + f s = ∑ i ∈ range L, f (i + s) + f s := by
      rw [← h2, h1]
    rw [add_right_cancel h3, ih]

/-- **Doubling.**  If `2 ≡ 4ˢ` and `4^L ≡ 1 (mod q)`, the drift weight sums to zero over
`a 4ⁱ mod q`, `i < L`. -/
theorem sum_orbit_quarterWeight_of_two_mem {q a L s : ℕ} (hq : 0 < q)
    (h4L : 4 ^ L % q = 1 % q) (h2 : 4 ^ s % q = 2 % q) :
    ∑ i ∈ range L, quarterWeight q (a * 4 ^ i % q) = 0 := by
  set f : ℕ → ℤ := fun i => quarterWeight q (a * 4 ^ i % q) with hf
  have hper : ∀ i, f (i + L) = f i := by
    intro i
    simp only [hf]
    rw [pow_add, ← mul_assoc, Nat.mul_mod, h4L, ← Nat.mul_mod, mul_one]
  set g : ℕ → ℤ := fun i => ((2 * (a * 4 ^ i % q) / q : ℕ) : ℤ) with hg
  have hstep : ∀ i, 4 * (a * 4 ^ i % q) % q = a * 4 ^ (i + 1) % q := by
    intro i
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]; ring_nf
  have hdbl : ∀ i, 2 * (a * 4 ^ i % q) % q = a * 4 ^ (i + s) % q := by
    intro i
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, show 2 * (a * 4 ^ i) = a * 4 ^ i * 2 by ring,
      pow_add, ← mul_assoc, Nat.mul_mod (a * 4 ^ i) (4 ^ s), h2, ← Nat.mul_mod]
  have hsum : ∑ i ∈ range L, f i + ∑ i ∈ range L, f (i + s) = 0 := by
    rw [← sum_add_distrib]
    have : ∀ i, f i + f (i + s) = g i - g (i + 1) := by
      intro i
      simp only [hf, hg]
      rw [← hdbl, quarterWeight_add_two_mul hq (Nat.mod_lt _ hq), hstep]
    rw [sum_congr rfl fun i _ => this i]
    have ht : ∑ i ∈ range L, (g i - g (i + 1)) = g 0 - g L := by
      have := Finset.sum_range_sub g L
      rw [← neg_sub (g L) (g 0), ← this, ← sum_neg_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [ht]
    have : g L = g 0 := by
      simp only [hg]
      rw [Nat.mul_mod a, h4L, ← Nat.mul_mod, mul_one, pow_zero, mul_one]
    rw [this, sub_self]
  rw [sum_range_shift_of_periodic hper] at hsum
  change ∑ i ∈ range L, f i = 0
  linarith

/-- **Reflection.**  If `4ˢ ≡ −1 (mod q)`, `4^L ≡ 1`, `q` is odd and no orbit point vanishes,
the drift weight sums to zero over `a 4ⁱ mod q`, `i < L`. -/
theorem sum_orbit_quarterWeight_of_neg_one_mem {q a L s : ℕ} (hq : 0 < q)
    (h4L : 4 ^ L % q = 1 % q) (hs : q ∣ 4 ^ s + 1) (hnd : ∀ i, ¬ q ∣ 4 * (a * 4 ^ i % q))
    (hnz : ∀ i, a * 4 ^ i % q ≠ 0) :
    ∑ i ∈ range L, quarterWeight q (a * 4 ^ i % q) = 0 := by
  set f : ℕ → ℤ := fun i => quarterWeight q (a * 4 ^ i % q) with hf
  have hper : ∀ i, f (i + L) = f i := by
    intro i
    simp only [hf]
    rw [pow_add, ← mul_assoc, Nat.mul_mod, h4L, ← Nat.mul_mod, mul_one]
  have hflip : ∀ i, f (i + s) = -f i := by
    intro i
    simp only [hf]
    set y := a * 4 ^ i with hy
    have hr : y % q < q := Nat.mod_lt _ hq
    have hz : ((a * 4 ^ (i + s) : ℕ) : ℤ) ≡ ((q - y % q : ℕ) : ℤ) [ZMOD (q : ℤ)] := by
      have h1 : (4 : ℤ) ^ s ≡ -1 [ZMOD (q : ℤ)] := by
        refine (Int.modEq_iff_dvd.mpr ?_).symm
        have := Int.natCast_dvd_natCast.mpr hs
        push_cast at this
        simpa [sub_neg_eq_add] using this
      have h2 : (y : ℤ) ≡ ((y % q : ℕ) : ℤ) [ZMOD (q : ℤ)] := by
        rw [Int.natCast_mod]; exact (Int.mod_modEq _ _).symm
      have e : ((a * 4 ^ (i + s) : ℕ) : ℤ) = (y : ℤ) * 4 ^ s := by rw [hy]; push_cast; ring
      rw [e, Nat.cast_sub hr.le]
      calc (y : ℤ) * 4 ^ s ≡ ((y % q : ℕ) : ℤ) * (-1) [ZMOD (q : ℤ)] := h2.mul h1
        _ = ((q : ℕ) : ℤ) * 0 - ((y % q : ℕ) : ℤ) := by ring
        _ ≡ ((q : ℕ) : ℤ) * 1 - ((y % q : ℕ) : ℤ) [ZMOD (q : ℤ)] := by
            refine Int.ModEq.sub_right _ ?_
            rw [Int.modEq_iff_dvd]; exact ⟨1, by ring⟩
        _ = (q : ℤ) - ((y % q : ℕ) : ℤ) := by ring
    have hnat : a * 4 ^ (i + s) % q = q - y % q := by
      have := hz
      rw [Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod] at this
      have h' : a * 4 ^ (i + s) % q = (q - y % q) % q := by exact_mod_cast this
      have hnz' := hnz i
      rw [← hy] at hnz'
      rw [h', Nat.mod_eq_of_lt (by omega)]
    rw [hnat, quarterWeight_sub hr (hnd i)]
  have h := sum_range_shift_of_periodic hper s
  rw [sum_congr rfl fun i _ => hflip i, sum_neg_distrib] at h
  change ∑ i ∈ range L, f i = 0
  linarith

/-! ### Zero drift at the window ends -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- Euler: `4^{(p−1)/2 · p^{k−1}} = 2^{φ(pᵏ)} ≡ 1 (mod pᵏ)`. -/
theorem fourPeriod_euler (hp2 : p ≠ 2) : FourPeriod p := by
  intro k hk
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hcop : Nat.Coprime 2 (p ^ k) := Nat.Coprime.pow_right k
    ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime_pow hp.out (by omega)] at h
  have e : 4 ^ ((p - 1) / 2 * p ^ (k - 1)) = 2 ^ (p ^ (k - 1) * (p - 1)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1
    rw [← mul_assoc, show 2 * ((p - 1) / 2) = p - 1 by omega, mul_comm]
  rw [e]
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm

omit hp in
/-- Lifting `p ∣ x − y` to `pᵏ ∣ x^{p^{k−1}} − y^{p^{k−1}}` in `ℤ`. -/
theorem int_pow_dvd_pow_sub_pow {x y : ℤ} (h : (p : ℤ) ∣ x - y) {k : ℕ} (hk : 1 ≤ k) :
    (p : ℤ) ^ k ∣ x ^ p ^ (k - 1) - y ^ p ^ (k - 1) := by
  have := dvd_sub_pow_of_dvd_sub h (k - 1)
  rwa [show k - 1 + 1 = k by omega] at this

/-- **Zero drift when `2 ∈ ⟨4⟩`.**  If the order of `2` modulo `p` is odd (`p ∣ 2^m − 1` with `m`
odd), the parity drift of `α_p` vanishes at every window end. -/
theorem drift_stonehamP_windowEnd_of_two_mem (hp2 : p ≠ 2) {m : ℕ} (hmodd : Odd m)
    (hm : p ∣ 2 ^ m - 1) (k : ℕ) : drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) = 0 := by
  refine (drift_stonehamP_windowEnd_of_period hp2 (fourPeriod_euler hp2) (c := 0)
    (fun k hk => ?_) k).trans (by ring)
  have hq : 0 < p ^ k := pow_pos hp.out.pos k
  have h4L : 4 ^ ((p - 1) / 2 * p ^ (k - 1)) % p ^ k = 1 % p ^ k :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr (fourPeriod_euler hp2 k hk)).symm
  -- `2^N ≡ 1 (mod pᵏ)` for the odd exponent `N = m p^{k−1}`
  set N := m * p ^ (k - 1) with hN
  have hNodd : N % 2 = 1 := by
    rw [hN, Nat.mul_mod, Nat.odd_iff.mp hmodd,
      Nat.odd_iff.mp (Odd.pow (hp.out.odd_of_ne_two hp2))]
  have h2N : p ^ k ∣ 2 ^ N - 1 := by
    have hz : ((p : ℤ)) ∣ (2 : ℤ) ^ m - 1 := by
      have := Int.natCast_dvd_natCast.mpr hm
      rwa [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))] at this
    have := int_pow_dvd_pow_sub_pow (p := p) (x := (2 : ℤ) ^ m) (y := 1) hz hk
    rw [one_pow, ← pow_mul] at this
    have hcast : ((2 ^ N - 1 : ℕ) : ℤ) = (2 : ℤ) ^ N - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; rfl
    rw [← Int.natCast_dvd_natCast, hcast]
    push_cast
    exact this
  have h2 : 4 ^ ((N + 1) / 2) % p ^ k = 2 % p ^ k := by
    have e : 4 ^ ((N + 1) / 2) = 2 ^ N * 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]; congr 1; omega
    rw [e, Nat.mul_mod, ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr h2N).symm,
      ← Nat.mul_mod, one_mul]
  exact sum_orbit_quarterWeight_of_two_mem hq h4L h2

/-- **Zero drift when `−1 ∈ ⟨4⟩`.**  If `p ∣ 4ⁿ + 1`, the parity drift of `α_p` vanishes at every
window end. -/
theorem drift_stonehamP_windowEnd_of_neg_one_mem (hp2 : p ≠ 2) {n : ℕ} (hn : p ∣ 4 ^ n + 1)
    (k : ℕ) : drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) = 0 := by
  refine (drift_stonehamP_windowEnd_of_period hp2 (fourPeriod_euler hp2) (c := 0)
    (fun k hk => ?_) k).trans (by ring)
  have hq : 0 < p ^ k := pow_pos hp.out.pos k
  have h4L : 4 ^ ((p - 1) / 2 * p ^ (k - 1)) % p ^ k = 1 % p ^ k :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr (fourPeriod_euler hp2 k hk)).symm
  have hs : p ^ k ∣ 4 ^ (n * p ^ (k - 1)) + 1 := by
    have hz : ((p : ℤ)) ∣ (4 : ℤ) ^ n - (-1) := by
      have := Int.natCast_dvd_natCast.mpr hn
      push_cast at this
      simpa [sub_neg_eq_add] using this
    have := int_pow_dvd_pow_sub_pow (p := p) (x := (4 : ℤ) ^ n) (y := -1) hz hk
    rw [← pow_mul, Odd.neg_one_pow (Odd.pow (hp.out.odd_of_ne_two hp2)), sub_neg_eq_add] at this
    rw [← Int.natCast_dvd_natCast]
    push_cast
    exact this
  have h4p : ¬ p ∣ 4 := fun h => not_dvd_two_pow hp2 2 (by norm_num; exact h)
  have hpa : ¬ p ∣ 2 * stonehamPA p k := not_dvd_two_mul_stonehamPA hp2 hk
  have hnz : ∀ i, 2 * stonehamPA p k * 4 ^ i % p ^ k ≠ 0 := by
    intro i h0
    have hdvd : p ∣ 2 * stonehamPA p k * 4 ^ i :=
      (dvd_pow_self p (by omega)).trans (Nat.dvd_of_mod_eq_zero h0)
    exact (hp.out.dvd_mul.mp hdvd).elim hpa (fun h' => h4p (hp.out.dvd_of_dvd_pow h'))
  exact sum_orbit_quarterWeight_of_neg_one_mem hq h4L hs
    (fun i => not_pow_dvd_four_mul hp2 (Nat.pos_of_ne_zero (hnz i)) (Nat.mod_lt _ hq)) hnz

/-! ### Instances -/

/-- `2` has odd order modulo `31`: `D_{α_{31}}((31^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_thirty_one (k : ℕ) :
    drift (stonehamP 31) ((31 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_two_mem (by norm_num) (m := 5) (by decide) (by decide) k

/-- `2` has odd order modulo `73`: `D_{α_{73}}((73^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_seventy_three (k : ℕ) :
    drift (stonehamP 73) ((73 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_two_mem (by norm_num) (m := 9) (by decide) (by decide) k

/-- `−1 ∈ ⟨4⟩` modulo `29`: `D_{α_{29}}((29^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_twenty_nine (k : ℕ) :
    drift (stonehamP 29) ((29 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_neg_one_mem (by norm_num) (n := 7) (by decide) k

/-- `−1 ∈ ⟨4⟩` modulo `37`: `D_{α_{37}}((37^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_thirty_seven (k : ℕ) :
    drift (stonehamP 37) ((37 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_neg_one_mem (by norm_num) (n := 9) (by decide) k

/-- `−1 ∈ ⟨4⟩` modulo `17`: `D_{α_{17}}((17^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_seventeen (k : ℕ) :
    drift (stonehamP 17) ((17 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_neg_one_mem (by norm_num) (n := 2) (by decide) k

/-- `−1 ∈ ⟨4⟩` modulo `41`: `D_{α_{41}}((41^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_forty_one (k : ℕ) :
    drift (stonehamP 41) ((41 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_neg_one_mem (by norm_num) (n := 5) (by decide) k

end GaloisForLFunctions.HTGeometry.StonehamPrimeDrift
