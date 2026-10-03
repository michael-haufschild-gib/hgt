import GaloisForLFunctions.HTGeometry.StonehamPrimeSquareOrbit

/-!
# The general drift law of the Stoneham constants `α_{2,p}`

**Self-similarity of the drift weight.**  For odd `N` and `c < p`, the `N` lifts `c + pt` of `c`
modulo `pN` carry together exactly the drift weight of `c` modulo `p`:

`Σ_{t<N} w(⌊4(c + pt)/(pN)⌋) = w(⌊4c/p⌋)`  (`sum_quarterWeight_lift`).

**The law.**  Let `p` be an odd prime, `m` the order of `4` modulo `p`, and `p² ∤ 4^m − 1`.  The
orbit of `4` modulo `pᵏ` is then the full preimage of its image modulo `p`, so one period of the
`k`-th window carries exactly the drift `Δ(2/p) = Σ_{i<m} w(⌊4(2·4ⁱ mod p)/p⌋)` of the rational
`2/p` over one base-4 period, and a window carries `p (p − 1)/(2m)` periods:

`D_{α_p}((p^{k+1} + 1)/2) = k · p · ((p − 1)/(2m)) · Δ(2/p)`  (`drift_stonehamP_windowEnd_eq`).

For `p = 3` this is `3k`; for `p = 11`, `33k`; it vanishes when `2` or `−1` lies in `⟨4⟩`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.StonehamPrimeDrift

open BinaryParityDrift StonehamParityDrift

/-! ### Self-similarity of the drift weight -/

theorem sum_range_ite_le' (a N : ℕ) (h : a ≤ N) :
    ∑ t ∈ range N, (if a ≤ t then (1 : ℤ) else 0) = N - a := by
  rw [sum_boole]
  have : {t ∈ range N | a ≤ t} = Ico a N := by
    ext t; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]
  push_cast [h]
  ring

/-- `Σ_{t<N} w(⌊(4t + e)/N⌋) = w(e)` for odd `N` and `e < 4`. -/
theorem sum_digitWeight_div (N e : ℕ) (hN : N % 2 = 1) (he : e < 4) :
    ∑ t ∈ range N, digitWeight (((4 * t + e) / N : ℕ) : ℤ) = digitWeight (e : ℤ) := by
  have hN0 : 0 < N := by omega
  have hterm : ∀ t ∈ range N, digitWeight (((4 * t + e) / N : ℕ) : ℤ) =
      -(if (N - e + 3) / 4 ≤ t then 1 else 0) + 2 * (if (2 * N - e + 3) / 4 ≤ t then 1 else 0) -
        (if (3 * N - e + 3) / 4 ≤ t then 1 else 0) := by
    intro t ht
    rw [mem_range] at ht
    have h1 : 1 ≤ (4 * t + e) / N ↔ 1 * N ≤ 4 * t + e := Nat.le_div_iff_mul_le hN0
    have h2 : 2 ≤ (4 * t + e) / N ↔ 2 * N ≤ 4 * t + e := Nat.le_div_iff_mul_le hN0
    have h3 : 3 ≤ (4 * t + e) / N ↔ 3 * N ≤ 4 * t + e := Nat.le_div_iff_mul_le hN0
    have h4 : (4 * t + e) / N < 4 := (Nat.div_lt_iff_lt_mul hN0).mpr (by omega)
    unfold digitWeight
    split_ifs <;> omega
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum,
    sum_range_ite_le' _ _ (by omega), sum_range_ite_le' _ _ (by omega),
    sum_range_ite_le' _ _ (by omega)]
  unfold digitWeight
  interval_cases e <;> simp <;> omega

/-- **Self-similarity.**  `Σ_{t<N} w(⌊4(c + pt)/(pN)⌋) = w(⌊4c/p⌋)` for odd `N` and `c < p`. -/
theorem sum_quarterWeight_lift {p N c : ℕ} (hp : 0 < p) (hN : N % 2 = 1) (hc : c < p) :
    ∑ t ∈ range N, quarterWeight (p * N) (c + p * t) = quarterWeight p c := by
  have he : 4 * c / p < 4 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hdiv : ∀ t, 4 * (c + p * t) / (p * N) = (4 * t + 4 * c / p) / N := by
    intro t
    rw [← Nat.div_div_eq_div_mul, show 4 * (c + p * t) = 4 * c + p * (4 * t) by ring,
      Nat.add_mul_div_left _ _ hp, add_comm]
  unfold quarterWeight
  simp only [hdiv]
  exact sum_digitWeight_div N _ hN he

/-! ### The orbit modulo `pᵏ` is the preimage of the orbit modulo `p` -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- Under `p² ∤ 4^m − 1`, summing a function along one period of `a 4ⁱ mod pᵏ` is the same as
summing it over all lifts of the orbit modulo `p`. -/
theorem sum_orbit_eq_sum_lifts (hp2 : p ≠ 2) {m : ℕ} (hm0 : 0 < m) (hm1 : p ∣ 4 ^ m - 1)
    (hmin : ∀ d < m, 0 < d → ¬ p ∣ 4 ^ d - 1) (hw : ¬ p ^ 2 ∣ 4 ^ m - 1) {k : ℕ} (hk : 1 ≤ k)
    {a : ℕ} (ha : ¬ p ∣ a) {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ i ∈ range (m * p ^ (k - 1)), F (a * 4 ^ i % p ^ k) =
      ∑ i ∈ range m, ∑ t ∈ range (p ^ (k - 1)), F (a * 4 ^ i % p + p * t) := by
  set N := p ^ (k - 1) with hNdef
  set q := p ^ k with hqdef
  have hqN : q = p * N := by rw [hqdef, hNdef, ← pow_succ']; congr 1; omega
  have hp0 : 0 < p := hp.out.pos
  have hN0 : 0 < N := pow_pos hp0 _
  have hq0 : 0 < q := pow_pos hp0 _
  have h4p : ¬ p ∣ 4 := fun h => not_dvd_two_pow hp2 2 (by norm_num; exact h)
  have hpow4 : ∀ i, ¬ p ∣ 4 ^ i := fun i h => h4p (hp.out.dvd_of_dvd_pow h)
  have hLTE := fun {k d : ℕ} (hk : 1 ≤ k) =>
    pow_dvd_pow_sub_one_iff_of_order hp2 hm0 hm1 hmin h4p hw hk (d := d)
  have hcop : ∀ c, ¬ p ∣ c → ∀ j, Nat.Coprime (p ^ j) c := fun c hc j =>
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hc)
  -- injectivity of `i ↦ a 4ⁱ mod p^j` below the period
  have hinj : ∀ j, 1 ≤ j → Set.InjOn (fun i => a * 4 ^ i % p ^ j) (range (m * p ^ (j - 1))) := by
    intro j hj
    have key : ∀ i i', i < i' → i' < m * p ^ (j - 1) →
        a * 4 ^ i % p ^ j = a * 4 ^ i' % p ^ j → False := by
      intro i i' hlt hi' hii
      have hle : a * 4 ^ i ≤ a * 4 ^ i' :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlt.le)
      have hdvd := (Nat.modEq_iff_dvd' hle).mp hii
      rw [show a * 4 ^ i' - a * 4 ^ i = a * 4 ^ i * (4 ^ (i' - i) - 1) by
        rw [Nat.mul_sub_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]] at hdvd
      have hc4 : ¬ p ∣ a * 4 ^ i := fun h => (hp.out.dvd_mul.mp h).elim ha (hpow4 i)
      have h2 := (hcop _ hc4 j).dvd_of_dvd_mul_left hdvd
      exact absurd (Nat.le_of_dvd (by omega) ((hLTE hj).mp h2)) (by omega)
    intro i hi i' hi' hii
    simp only [coe_range, Set.mem_Iio] at hi hi' hii
    rcases lt_trichotomy i i' with h | h | h
    · exact (key i i' h hi' hii).elim
    · exact h
    · exact (key i' i h hi hii.symm).elim
  have hinj1 := hinj 1 le_rfl
  simp only [Nat.sub_self, pow_zero, mul_one, pow_one] at hinj1
  -- the set of lifts
  set S := (range m).biUnion fun i => (range N).image fun t => a * 4 ^ i % p + p * t with hS
  have hdisj : Set.PairwiseDisjoint (↑(range m)) fun i =>
      (range N).image fun t => a * 4 ^ i % p + p * t := by
    intro i hi i' hi' hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro r hr hr'
    obtain ⟨t, _, rfl⟩ := mem_image.mp hr
    obtain ⟨t', _, ht'⟩ := mem_image.mp hr'
    have hmod := congrArg (· % p) ht'
    simp only [Nat.add_mul_mod_self_left, Nat.mod_mod] at hmod
    exact hne (hinj1 hi hi' hmod.symm)
  have hinjt : ∀ i, Set.InjOn (fun t => a * 4 ^ i % p + p * t) (range N) := by
    intro i t _ t' _ h
    simp only at h
    have : p * t = p * t' := by omega
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  have hcardS : S.card = m * N := by
    rw [hS, card_biUnion hdisj]
    simp only [card_image_of_injOn (hinjt _), card_range, sum_const, card_range, smul_eq_mul]
  -- the orbit modulo `q` fills `S`
  have hm4 : 4 ^ m % p = 1 % p := ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr
    hm1).symm
  have himg : (range (m * N)).image (fun i => a * 4 ^ i % q) = S := by
    apply eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      rw [hS, mem_biUnion]
      refine ⟨i % m, mem_range.mpr (Nat.mod_lt _ hm0), mem_image.mpr
        ⟨a * 4 ^ i % q / p, ?_, ?_⟩⟩
      · rw [mem_range, Nat.div_lt_iff_lt_mul hp0, show N * p = q by rw [hqN, mul_comm]]
        exact Nat.mod_lt _ hq0
      · have hmodp : a * 4 ^ i % q % p = a * 4 ^ (i % m) % p := by
          rw [Nat.mod_mod_of_dvd _ (by rw [hqN]; exact dvd_mul_right p N)]
          conv_lhs => rw [← Nat.div_add_mod i m, pow_add, pow_mul, ← mul_assoc]
          rw [Nat.mul_mod, Nat.mul_mod a, Nat.pow_mod, hm4, Nat.one_mod_eq_one.mpr
            hp.out.one_lt.ne', one_pow, Nat.one_mod_eq_one.mpr hp.out.one_lt.ne', mul_one,
            Nat.mod_mod, Nat.mul_mod a]
        rw [← hmodp]
        exact Nat.mod_add_div _ p
    · rw [card_image_of_injOn (by rw [hqdef, hNdef]; exact hinj k hk), card_range, hcardS]
  rw [show m * p ^ (k - 1) = m * N from rfl, ← sum_image (hinj k hk), ← hqdef, himg, hS,
    sum_biUnion hdisj]
  exact sum_congr rfl fun i _ => sum_image (hinjt i)

/-! ### The general law -/

/-- The drift `Δ(2/p)` of the rational `2/p` over one base-4 period of length `m`. -/
def rationalDrift (p m : ℕ) : ℤ := ∑ i ∈ range m, quarterWeight p (2 * 4 ^ i % p)

/-- **The general drift law of the Stoneham constants.**  For an odd prime `p` such that `4` has
order `m` modulo `p` and `p² ∤ 4^m − 1`,
`D_{α_p}((p^{k+1} + 1)/2) = k · p · ((p − 1)/(2m)) · Δ(2/p)`. -/
theorem drift_stonehamP_windowEnd_eq (hp2 : p ≠ 2) {m : ℕ} (hm0 : 0 < m) (hm1 : p ∣ 4 ^ m - 1)
    (hmin : ∀ d < m, 0 < d → ¬ p ∣ 4 ^ d - 1) (hw : ¬ p ^ 2 ∣ 4 ^ m - 1) (k : ℕ) :
    drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) =
      p * k * (((p - 1) / 2 / m : ℕ) * rationalDrift p m) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have h4p : ¬ p ∣ 4 := fun h => not_dvd_two_pow hp2 2 (by norm_num; exact h)
  have hLTE := fun {k d : ℕ} (hk : 1 ≤ k) =>
    pow_dvd_pow_sub_one_iff_of_order hp2 hm0 hm1 hmin h4p hw hk (d := d)
  -- `m ∣ (p − 1)/2`
  obtain ⟨e, he⟩ : m ∣ (p - 1) / 2 := by
    have h : p ∣ 4 ^ ((p - 1) / 2) - 1 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by omega]
      exact dvd_two_pow_prime_sub_one_sub_one hp2
    exact (dvd_pow_sub_one_iff_of_order hm0 hm1 hmin (by norm_num)).mp h
  have hediv : (p - 1) / 2 / m = e := by rw [he, Nat.mul_div_cancel_left _ hm0]
  have hper : FourPeriod p := by
    intro k hk
    exact (hLTE hk).mpr ⟨e, by rw [he]; ring⟩
  rw [hediv]
  refine drift_stonehamP_windowEnd_of_period hp2 hper (fun k hk => ?_) k
  set N := p ^ (k - 1) with hNdef
  have hqN : p ^ k = p * N := by rw [hNdef, ← pow_succ']; congr 1; omega
  have hNodd : N % 2 = 1 := Nat.odd_iff.mp (Odd.pow (hp.out.odd_of_ne_two hp2))
  set a := 2 * stonehamPA p k with ha
  have hpa : ¬ p ∣ a := not_dvd_two_mul_stonehamPA hp2 hk
  set f : ℕ → ℤ := fun i => quarterWeight (p ^ k) (a * 4 ^ i % p ^ k) with hf
  -- periodicity with the true period `m N`
  have hfper : ∀ b i, f (b * (m * N) + i) = f i := by
    intro b i
    simp only [hf]
    congr 1
    have hmod : 4 ^ (m * N) % p ^ k = 1 % p ^ k :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr ((hLTE hk).mpr dvd_rfl)).symm
    induction b with
    | zero => simp
    | succ b ih =>
      rw [show (b + 1) * (m * N) + i = (b * (m * N) + i) + m * N by ring, pow_add, ← mul_assoc,
        Nat.mul_mod, hmod, ← Nat.mul_mod, mul_one, ih]
  -- one true period carries `Δ(2/p)`
  have hone : ∑ i ∈ range (m * N), f i = rationalDrift p m := by
    simp only [hf]
    rw [sum_orbit_eq_sum_lifts hp2 hm0 hm1 hmin hw hk hpa, hqN, rationalDrift]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_quarterWeight_lift hp.out.pos hNodd (Nat.mod_lt _ hp.out.pos)]
    congr 1
    rw [ha, show 2 * stonehamPA p k * 4 ^ i = 2 * 4 ^ i * stonehamPA p k by ring, Nat.mul_mod,
      stonehamPA_mod hp.out.two_le hk, mul_one, Nat.mod_mod]
  change ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)), f i = _
  rw [he, show m * e * p ^ (k - 1) = e * (m * N) by rw [hNdef]; ring,
    sum_range_mul_of_periodic hfper, hone]

/-- `p = 3`: `D_{α_3}((3^{k+1} + 1)/2) = 3k`. -/
theorem drift_stonehamP_three (k : ℕ) : drift (stonehamP 3) ((3 ^ (k + 1) + 1) / 2) = 3 * k := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [drift_stonehamP_windowEnd_eq (by norm_num) (m := 1) (by norm_num) (by decide) (by decide)
    (by decide) k]
  have : rationalDrift 3 1 = 1 := by decide
  rw [this]; push_cast; ring

/-- `p = 43` (`4` has order `7`; neither `2` nor `−1` lies in `⟨4⟩`):
`D_{α_{43}}((43^{k+1} + 1)/2) = 387k`. -/
theorem drift_stonehamP_forty_three (k : ℕ) :
    drift (stonehamP 43) ((43 ^ (k + 1) + 1) / 2) = 387 * k := by
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  rw [drift_stonehamP_windowEnd_eq (by norm_num) (m := 7) (by norm_num) (by decide) (by decide)
    (by decide) k]
  have : rationalDrift 43 7 = 3 := by decide
  rw [this]; push_cast; ring

end GaloisForLFunctions.HTGeometry.StonehamPrimeDrift
