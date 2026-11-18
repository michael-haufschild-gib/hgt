import GaloisForLFunctions.ExceptionalLayerTheory.SmoothCountsAndTheLargeFactorsOfTheCentralBinomialCoefficient

/-!
# Division trees of dyadic smooth counts and top-octave parity aliasing

For every cutoff `n` and smoothness bound `y ≥ 2`, the dyadic smooth difference
`2 Ψ(n, y) - Ψ(2n, y)` equals the alternating sum `∑_{j ≤ 2n, P⁺(j) ≤ y} (-1)^j`
without requiring `2n < (y + 1)²`. Along the `2`-adic division tree over odd
`y`-smooth roots `u`, the middle octave `u ∈ (n/2, n]` cancels identically, the
top octave `(n, 2n]` contributes `-1`, and deeper octaves `u ≤ n/2` contribute
`⌊log₂(2n/u)⌋ - 1 ≥ 1`. Along odd primes `p ∈ (z, y]`, the alternating sum obeys
an exact sign-preserving Buchstab tree recurrence down to `Φ(M, 2) = ⌊log₂ M⌋ - 1`.
While the raw complement identity `Ψ(x, y) + ∑_{m > y} g(m) ⌊x/m⌋ = x` uniquely
forces `g = 1_{prime}` on `(y, (y+1)²)`, the central-binomial carry aliases every
odd integer `2r - 1` with `2r` across the entire top octave `(N, 2N]`.
-/

noncomputable section

open Finset
open _root_.RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Odd positive integers up to `X` supported on primes at most `y`. -/
def oddSmoothIntegerCount (X y : ℕ) : ℕ :=
  ((Sieve.smoothUpTo (Nat.primesLE y) X).filter (fun n => ¬ 2 ∣ n)).card

/-- Parity-signed count of `y`-smooth positive integers up to `X`. -/
def alternatingSmoothSum (X y : ℕ) : ℝ :=
  ∑ j ∈ Sieve.smoothUpTo (Nat.primesLE y) X, (-1 : ℝ) ^ j

private theorem even_smooth_bijection (M : ℕ) {y : ℕ} (hy : 2 ≤ y) :
    ((Sieve.smoothUpTo (Nat.primesLE y) M).filter (fun j => 2 ∣ j)).card =
      smoothIntegerCount (M / 2) y := by
  symm
  rw [smoothIntegerCount]
  refine Finset.card_bij (fun m _ => 2 * m) ?_ ?_ ?_
  · intro m hm
    obtain ⟨⟨hm1, hmM⟩, hfac⟩ := mem_smoothUpTo_iff.mp hm
    refine mem_filter.mpr ⟨mem_smoothUpTo_iff.mpr ⟨⟨by omega, by omega⟩, ?_⟩, dvd_mul_right 2 m⟩
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    rcases hpp.dvd_mul.mp hpd with hp2 | hpm
    · have := Nat.le_of_dvd two_pos hp2
      omega
    · exact hfac p (Nat.mem_primeFactors.mpr ⟨hpp, hpm, by omega⟩)
  · intro m₁ _ m₂ _ heq
    omega
  · intro j hj
    obtain ⟨hjS, ⟨m, rfl⟩⟩ := mem_filter.mp hj
    obtain ⟨⟨hj1, hjM⟩, hfac⟩ := mem_smoothUpTo_iff.mp hjS
    refine ⟨m, mem_smoothUpTo_iff.mpr ⟨⟨by omega, by omega⟩, fun p hp => ?_⟩, rfl⟩
    obtain ⟨hpp, hpm, _⟩ := Nat.mem_primeFactors.mp hp
    exact hfac p (Nat.mem_primeFactors.mpr ⟨hpp, dvd_mul_of_dvd_right hpm 2, by omega⟩)

/-- Every `y`-smooth count (`y ≥ 2`) splits into even `y`-smooth integers (`Ψ(⌊M/2⌋, y)`)
and odd `y`-smooth integers (`Ψ_odd(M, y)`). -/
theorem smoothIntegerCount_eq_half_add_odd (M : ℕ) {y : ℕ} (hy : 2 ≤ y) :
    smoothIntegerCount M y = smoothIntegerCount (M / 2) y + oddSmoothIntegerCount M y := by
  rw [smoothIntegerCount, oddSmoothIntegerCount, ← even_smooth_bijection M hy]
  exact (card_filter_add_card_filter_not (fun n => 2 ∣ n)).symm

/-- For all `n` and `y ≥ 2` (without requiring `2n < (y + 1)²`), `2 Ψ(n, y) - Ψ(2n, y)`
equals `Ψ(n, y) - Ψ_odd(2n, y)` and equals `alternatingSmoothSum (2n) y`. -/
theorem two_mul_smoothIntegerCount_sub_eq_alternating (n : ℕ) {y : ℕ} (hy : 2 ≤ y) :
    2 * (smoothIntegerCount n y : ℝ) - (smoothIntegerCount (2 * n) y : ℝ) =
      (smoothIntegerCount n y : ℝ) - (oddSmoothIntegerCount (2 * n) y : ℝ) ∧
    2 * (smoothIntegerCount n y : ℝ) - (smoothIntegerCount (2 * n) y : ℝ) =
      alternatingSmoothSum (2 * n) y := by
  have hsplit := smoothIntegerCount_eq_half_add_odd (2 * n) hy
  rw [Nat.mul_div_right n two_pos] at hsplit
  have hsplitR : (smoothIntegerCount (2 * n) y : ℝ) =
      (smoothIntegerCount n y : ℝ) + (oddSmoothIntegerCount (2 * n) y : ℝ) := by
    exact_mod_cast hsplit
  refine ⟨by linarith only [hsplitR], ?_⟩
  let S := Sieve.smoothUpTo (Nat.primesLE y) (2 * n)
  have halt : alternatingSmoothSum (2 * n) y =
      ((S.filter (fun j => 2 ∣ j)).card : ℝ) - ((S.filter (fun j => ¬ 2 ∣ j)).card : ℝ) := by
    rw [alternatingSmoothSum, ← sum_filter_add_sum_filter_not S (fun j => 2 ∣ j)]
    have hev : ∑ j ∈ S.filter (fun j => 2 ∣ j), (-1 : ℝ) ^ j =
        ((S.filter (fun j => 2 ∣ j)).card : ℝ) := by
      calc
        _ = ∑ _j ∈ S.filter (fun j => 2 ∣ j), (1 : ℝ) := by
          refine sum_congr rfl fun j hj => ?_
          obtain ⟨_, k, rfl⟩ := mem_filter.mp hj
          rw [pow_mul, neg_one_sq, one_pow]
        _ = _ := by simp
    have hodd : ∑ j ∈ S.filter (fun j => ¬ 2 ∣ j), (-1 : ℝ) ^ j =
        -((S.filter (fun j => ¬ 2 ∣ j)).card : ℝ) := by
      calc
        _ = ∑ _j ∈ S.filter (fun j => ¬ 2 ∣ j), (-1 : ℝ) := by
          refine sum_congr rfl fun j hj => ?_
          have hnd := (mem_filter.mp hj).2
          have hjmod : j = 2 * (j / 2) + 1 := by omega
          rw [hjmod, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
        _ = _ := by simp
    rw [hev, hodd]
    ring
  rw [halt, even_smooth_bijection (2 * n) hy, Nat.mul_div_right n two_pos]
  change _ = (smoothIntegerCount n y : ℝ) - (oddSmoothIntegerCount (2 * n) y : ℝ)
  linarith only [hsplitR]

/-- Cancelling singly-even `y`-smooth integers against odd `y`-smooth integers up to `n`
reduces `2 Ψ(n, y) - Ψ(2n, y)` to `Ψ(⌊n/2⌋, y) - (Ψ_odd(2n, y) - Ψ_odd(n, y))`. -/
theorem two_mul_smoothIntegerCount_sub_eq_middle_octave_cancel (n : ℕ) {y : ℕ} (hy : 2 ≤ y) :
    2 * (smoothIntegerCount n y : ℝ) - (smoothIntegerCount (2 * n) y : ℝ) =
      (smoothIntegerCount (n / 2) y : ℝ) -
        ((oddSmoothIntegerCount (2 * n) y : ℝ) - (oddSmoothIntegerCount n y : ℝ)) := by
  have h1 := (two_mul_smoothIntegerCount_sub_eq_alternating n hy).1
  have h2 : (smoothIntegerCount n y : ℝ) =
      (smoothIntegerCount (n / 2) y : ℝ) + (oddSmoothIntegerCount n y : ℝ) := by
    exact_mod_cast smoothIntegerCount_eq_half_add_odd n hy
  linarith only [h1, h2]

/-- Exact `2`-adic division-tree decomposition over odd `y`-smooth roots `u ≤ M`. -/
theorem alternatingSmoothSum_eq_sum_odd_roots (M : ℕ) {y : ℕ} (hy : 2 ≤ y) :
    alternatingSmoothSum M y =
      ∑ u ∈ (Sieve.smoothUpTo (Nat.primesLE y) M).filter (fun u => ¬ 2 ∣ u),
        ((Nat.log 2 (M / u) : ℝ) - 1) := by
  classical
  let S := Sieve.smoothUpTo (Nat.primesLE y) M
  let OddS := S.filter (fun u => ¬ 2 ∣ u)
  let T := OddS.sigma (fun u => Icc 0 (Nat.log 2 (M / u)))
  have hbij : alternatingSmoothSum M y = ∑ x ∈ T, (-1 : ℝ) ^ (2 ^ x.2 * x.1) := by
    rw [alternatingSmoothSum]
    symm
    refine Finset.sum_bij (fun x _ => 2 ^ x.2 * x.1) ?_ ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨u, a⟩ hx
      obtain ⟨huOdd, ha⟩ := mem_sigma.mp hx
      obtain ⟨huS, _⟩ := mem_filter.mp huOdd
      obtain ⟨⟨hu1, huM⟩, hufac⟩ := mem_smoothUpTo_iff.mp huS
      have hdiv_pos : 0 < M / u := (Nat.one_le_div_iff hu1).mpr huM
      have hpow : 2 ^ a ≤ M / u :=
        Nat.pow_le_of_le_log hdiv_pos.ne' (mem_Icc.mp ha).2
      have hle : 2 ^ a * u ≤ M :=
        (Nat.mul_le_mul_right u hpow).trans (Nat.div_mul_le_self M u)
      have hpos : 1 ≤ 2 ^ a * u := Nat.mul_pos (Nat.pow_pos two_pos) hu1
      refine mem_smoothUpTo_iff.mpr ⟨⟨hpos, hle⟩, fun p hp => ?_⟩
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      rcases hpp.dvd_mul.mp hpd with hp2 | hpu
      · have := hpp.dvd_of_dvd_pow hp2
        have := Nat.le_of_dvd two_pos this
        omega
      · exact hufac p (Nat.mem_primeFactors.mpr ⟨hpp, hpu, by omega⟩)
    · rintro ⟨u₁, a₁⟩ hx₁ ⟨u₂, a₂⟩ hx₂ heq
      dsimp only at heq
      obtain ⟨hu₁, _⟩ := mem_sigma.mp hx₁
      obtain ⟨hu₂, _⟩ := mem_sigma.mp hx₂
      have hnd₁ := (mem_filter.mp hu₁).2
      have hnd₂ := (mem_filter.mp hu₂).2
      have hu₁0 : u₁ ≠ 0 := Nat.ne_of_gt (mem_smoothUpTo_iff.mp (mem_filter.mp hu₁).1).1.1
      have hu₂0 : u₂ ≠ 0 := Nat.ne_of_gt (mem_smoothUpTo_iff.mp (mem_filter.mp hu₂).1).1.1
      have hf := congrArg (fun n : ℕ => n.factorization 2) heq
      rw [Nat.factorization_mul (pow_ne_zero _ two_pos.ne') hu₁0,
        Nat.factorization_mul (pow_ne_zero _ two_pos.ne') hu₂0] at hf
      simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hnd₁,
        Nat.factorization_eq_zero_of_not_dvd hnd₂, add_zero] at hf
      subst hf
      have hu_eq : u₁ = u₂ := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos two_pos) heq
      subst hu_eq
      rfl
    · intro j hj
      obtain ⟨⟨hj1, hjM⟩, hjfac⟩ := mem_smoothUpTo_iff.mp hj
      let a := j.factorization 2
      let u := j / 2 ^ a
      have hmul : 2 ^ a * u = j := Nat.ordProj_mul_ordCompl_eq_self j 2
      have hcop : Nat.Coprime 2 u := Nat.coprime_ordCompl Nat.prime_two (by omega)
      have hnd : ¬ 2 ∣ u := Nat.prime_two.coprime_iff_not_dvd.mp hcop
      have hu1 : 1 ≤ u := Nat.pos_of_ne_zero fun hu0 => by
        rw [hu0, mul_zero] at hmul
        omega
      have huM : u ≤ M := (Nat.le_mul_of_pos_left u (Nat.pow_pos two_pos)).trans (hmul.le.trans hjM)
      have huS : u ∈ S := by
        refine mem_smoothUpTo_iff.mpr ⟨⟨hu1, huM⟩, fun p hp => ?_⟩
        obtain ⟨hpp, hpu, _⟩ := Nat.mem_primeFactors.mp hp
        refine hjfac p (Nat.mem_primeFactors.mpr ⟨hpp, ?_, by omega⟩)
        rw [← hmul]
        exact dvd_mul_of_dvd_right hpu _
      have hpow_le : 2 ^ a ≤ M / u :=
        (Nat.le_div_iff_mul_le hu1).mpr (hmul.le.trans hjM)
      have ha_le : a ≤ Nat.log 2 (M / u) :=
        Nat.le_log_of_pow_le (by decide : 1 < 2) hpow_le
      exact ⟨⟨u, a⟩, mem_sigma.mpr ⟨mem_filter.mpr ⟨huS, hnd⟩, mem_Icc.mpr ⟨Nat.zero_le a, ha_le⟩⟩, hmul⟩
  rw [hbij, sum_sigma]
  refine sum_congr rfl fun u hu => ?_
  have hnd := (mem_filter.mp hu).2
  let L := Nat.log 2 (M / u)
  have h0 : (-1 : ℝ) ^ (2 ^ 0 * u) = -1 := by
    have humod : u = 2 * (u / 2) + 1 := by omega
    rw [pow_zero, one_mul, humod, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
  have hpos (a : ℕ) (ha : 1 ≤ a) : (-1 : ℝ) ^ (2 ^ a * u) = 1 := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    rw [pow_succ', mul_assoc, pow_mul, neg_one_sq, one_pow]
  have hsplit_Icc : Icc 0 L = insert 0 (Icc 1 L) := by
    ext a
    simp only [mem_Icc, mem_insert]
    omega
  rw [hsplit_Icc, sum_insert (by simp), h0]
  have hrest : (∑ a ∈ Icc 1 L, (-1 : ℝ) ^ (2 ^ a * u)) = (L : ℝ) := by
    calc
      _ = ∑ _a ∈ Icc 1 L, (1 : ℝ) := sum_congr rfl fun a ha => hpos a (mem_Icc.mp ha).1
      _ = _ := by simp
  rw [hrest]
  ring

/-- Base of the smooth division tree at `y = 2`: `Φ(M, 2) = ⌊log₂ M⌋ - 1` for `M ≥ 1`. -/
theorem alternatingSmoothSum_two {M : ℕ} (hM : 1 ≤ M) :
    alternatingSmoothSum M 2 = (Nat.log 2 M : ℝ) - 1 := by
  rw [alternatingSmoothSum_eq_sum_odd_roots M le_rfl]
  have hset : (Sieve.smoothUpTo (Nat.primesLE 2) M).filter (fun u => ¬ 2 ∣ u) = {1} := by
    ext u
    simp only [mem_filter, mem_smoothUpTo_iff, mem_singleton]
    constructor
    · rintro ⟨⟨⟨hu1, _⟩, hfac⟩, hnd⟩
      by_contra hne
      have hu2 : 2 ≤ u := by omega
      let p := u.minFac
      have hp : p.Prime := Nat.minFac_prime hne
      have hpd : p ∣ u := Nat.minFac_dvd u
      have hple : p ≤ 2 := hfac p (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩)
      have hp2 : p = 2 := le_antisymm hple hp.two_le
      exact hnd (hp2 ▸ hpd)
    · rintro rfl
      exact ⟨⟨⟨le_rfl, hM⟩, by simp⟩, by omega⟩
  rw [hset, sum_singleton, Nat.div_one]

/-- Exact odd-prime Buchstab division-tree law for `alternatingSmoothSum` (`2 ≤ z ≤ y`). -/
theorem alternatingSmoothSum_buchstab (M : ℕ) {z y : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    alternatingSmoothSum M y =
      alternatingSmoothSum M z +
        ∑ p ∈ (Nat.primesLE y).filter (fun p => z < p), alternatingSmoothSum (M / p) p := by
  induction y, hzy using Nat.le_induction with
  | base =>
    have hempty : (Nat.primesLE z).filter (fun p => z < p) = ∅ := by
      ext p
      simp only [mem_filter, Nat.mem_primesLE, notMem_empty, iff_false]
      omega
    rw [hempty, sum_empty, add_zero]
  | succ y hzy ih =>
    by_cases hp : (y + 1).Prime
    · have hp_gt : z < y + 1 := by omega
      have hp_odd : ¬ 2 ∣ y + 1 := by
        intro hd
        have heq := (Nat.dvd_prime hp).mp hd
        omega
      have hfilter : (Nat.primesLE (y + 1)).filter (fun q => z < q) =
          insert (y + 1) ((Nat.primesLE y).filter (fun q => z < q)) := by
        ext q
        simp only [mem_filter, Nat.mem_primesLE, mem_insert]
        constructor
        · rintro ⟨⟨hqle, hqp⟩, hqz⟩
          rcases eq_or_lt_of_le hqle with rfl | hlt
          · exact Or.inl rfl
          · exact Or.inr ⟨⟨by omega, hqp⟩, hqz⟩
        · rintro (rfl | ⟨⟨hqle, hqp⟩, hqz⟩)
          · exact ⟨⟨le_rfl, hp⟩, hp_gt⟩
          · exact ⟨⟨by omega, hqp⟩, hqz⟩
      have hnotmem : y + 1 ∉ (Nat.primesLE y).filter (fun q => z < q) := by
        simp [Nat.mem_primesLE]
      rw [hfilter, sum_insert hnotmem, ← add_assoc, add_comm _ (alternatingSmoothSum _ _),
        add_assoc, ← ih]
      let S₁ := Sieve.smoothUpTo (Nat.primesLE (y + 1)) M
      let S₀ := Sieve.smoothUpTo (Nat.primesLE y) M
      have hpart_not : S₁.filter (fun j => ¬ (y + 1) ∣ j) = S₀ := by
        ext j
        simp only [S₁, S₀, mem_filter, mem_smoothUpTo_iff]
        constructor
        · rintro ⟨⟨hjM, hfac⟩, hnd⟩
          refine ⟨hjM, fun q hq => ?_⟩
          have hqle := hfac q hq
          have hqne : q ≠ y + 1 := fun h => hnd (h ▸ Nat.dvd_of_mem_primeFactors hq)
          omega
        · rintro ⟨hjM, hfac⟩
          refine ⟨⟨hjM, fun q hq => (hfac q hq).trans (Nat.le_succ y)⟩, fun hd => ?_⟩
          have hmem : y + 1 ∈ j.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩
          have := hfac (y + 1) hmem
          omega
      have hpart_dvd : ∑ j ∈ S₁.filter (fun j => (y + 1) ∣ j), (-1 : ℝ) ^ j =
          alternatingSmoothSum (M / (y + 1)) (y + 1) := by
        rw [alternatingSmoothSum]
        symm
        refine Finset.sum_bij (fun m _ => (y + 1) * m) ?_ ?_ ?_ ?_
        · intro m hm
          obtain ⟨⟨hm1, hmM⟩, hmfac⟩ := mem_smoothUpTo_iff.mp hm
          have hle : (y + 1) * m ≤ M :=
            (Nat.mul_le_mul_left (y + 1) hmM).trans (Nat.mul_div_le M (y + 1))
          have hpos : 1 ≤ (y + 1) * m := Nat.mul_pos (by omega) hm1
          refine mem_filter.mpr ⟨mem_smoothUpTo_iff.mpr ⟨⟨hpos, hle⟩, fun q hq => ?_⟩,
            dvd_mul_right (y + 1) m⟩
          obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
          rcases hqp.dvd_mul.mp hqd with hqy | hqm
          · exact Nat.le_of_dvd (by omega) hqy
          · exact hmfac q (Nat.mem_primeFactors.mpr ⟨hqp, hqm, by omega⟩)
        · intro m₁ _ m₂ _ heq
          exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < y + 1) heq
        · intro j hj
          obtain ⟨hjS, ⟨m, rfl⟩⟩ := mem_filter.mp hj
          obtain ⟨⟨hj1, hjM⟩, hjfac⟩ := mem_smoothUpTo_iff.mp hjS
          have hm1 : 1 ≤ m := by
            by_contra h0
            have hm0 : m = 0 := by omega
            rw [hm0, mul_zero] at hj1
            omega
          have hmM : m ≤ M / (y + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
          refine ⟨m, mem_smoothUpTo_iff.mpr ⟨⟨hm1, hmM⟩, fun q hq => ?_⟩, rfl⟩
          obtain ⟨hqp, hqm, _⟩ := Nat.mem_primeFactors.mp hq
          exact hjfac q (Nat.mem_primeFactors.mpr ⟨hqp, dvd_mul_of_dvd_right hqm _, by omega⟩)
        · intro m _
          have hyodd : y + 1 = 2 * ((y + 1) / 2) + 1 := by omega
          have heq : (y + 1) * m = 2 * (((y + 1) / 2) * m) + m := by
            calc (y + 1) * m = (2 * ((y + 1) / 2) + 1) * m := by rw [← hyodd]
              _ = 2 * (((y + 1) / 2) * m) + m := by ring
          rw [heq, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
      rw [alternatingSmoothSum, ← sum_filter_add_sum_filter_not S₁ (fun j => (y + 1) ∣ j),
        hpart_dvd, hpart_not, ← alternatingSmoothSum, add_comm]
    · have hprimes : Nat.primesLE (y + 1) = Nat.primesLE y := by
        ext q
        simp only [Nat.mem_primesLE]
        constructor
        · rintro ⟨hqle, hqp⟩
          refine ⟨?_, hqp⟩
          rcases eq_or_lt_of_le hqle with rfl | hlt
          · exact absurd hqp hp
          · omega
        · rintro ⟨hqle, hqp⟩
          exact ⟨by omega, hqp⟩
      simp only [alternatingSmoothSum, hprimes] at ih ⊢
      exact ih

/-- Exact first-total reduction of the dyadic smooth difference over `k < 2N`. -/
theorem sum_range_two_mul_smooth_dyadic_eq (N : ℕ) {y : ℕ} (hy : 2 ≤ y) :
    (∑ k ∈ range (2 * N),
      (2 * (smoothIntegerCount (k / 2) y : ℝ) - (smoothIntegerCount (2 * (k / 2)) y : ℝ))) =
      (∑ j ∈ Sieve.smoothUpTo (Nat.primesLE y) (2 * N), (-1 : ℝ) ^ j * ((2 * N : ℝ) - j)) +
        (oddSmoothIntegerCount (2 * N - 1) y : ℝ) := by
  induction N with
  | zero =>
    have hempty : Sieve.smoothUpTo (Nat.primesLE y) 0 = ∅ := by
      ext j
      simp only [mem_smoothUpTo_iff, notMem_empty, iff_false]
      omega
    simp [oddSmoothIntegerCount, hempty]
  | succ N ih =>
    have hrange : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
    rw [hrange, Finset.sum_range_succ, Finset.sum_range_succ]
    have hd₁ : (2 * N) / 2 = N := Nat.mul_div_right N two_pos
    have hd₂ : (2 * N + 1) / 2 = N := by omega
    rw [hd₁, hd₂, ih, (two_mul_smoothIntegerCount_sub_eq_alternating N hy).2]
    let P := fun j : ℕ => ∀ p ∈ j.primeFactors, p ≤ y
    let S₀ := Sieve.smoothUpTo (Nat.primesLE y) (2 * N)
    let S₁ := Sieve.smoothUpTo (Nat.primesLE y) (2 * N + 2)
    have hsub : S₀ ⊆ S₁ := by
      intro j hj
      obtain ⟨⟨h1, h2⟩, hf⟩ := mem_smoothUpTo_iff.mp hj
      exact mem_smoothUpTo_iff.mpr ⟨⟨h1, by omega⟩, hf⟩
    have hdiff : S₁ \ S₀ = ({2 * N + 1, 2 * N + 2} : Finset ℕ).filter P := by
      ext j
      simp only [S₁, S₀, mem_sdiff, mem_smoothUpTo_iff, mem_filter, mem_insert, mem_singleton, P]
      constructor
      · rintro ⟨⟨⟨hj1, hj2⟩, hf⟩, hnot⟩
        have hjgt : 2 * N < j := by
          by_contra hle
          exact hnot ⟨⟨hj1, by omega⟩, hf⟩
        exact ⟨by omega, hf⟩
      · rintro ⟨(rfl | rfl), hf⟩ <;> refine ⟨⟨⟨by omega, by omega⟩, hf⟩, ?_⟩ <;> omega
    have hsum_split : (∑ j ∈ S₁, (-1 : ℝ) ^ j * (((2 * (N + 1) : ℕ) : ℝ) - j)) =
        (∑ j ∈ S₀, (-1 : ℝ) ^ j * ((2 * N : ℝ) - j)) + 2 * alternatingSmoothSum (2 * N) y +
          ∑ j ∈ S₁ \ S₀, (-1 : ℝ) ^ j * (((2 * (N + 1) : ℕ) : ℝ) - j) := by
      rw [← sum_sdiff hsub]
      have hhead : (∑ j ∈ S₀, (-1 : ℝ) ^ j * (((2 * (N + 1) : ℕ) : ℝ) - j)) =
          (∑ j ∈ S₀, (-1 : ℝ) ^ j * ((2 * N : ℝ) - j)) + 2 * alternatingSmoothSum (2 * N) y := by
        rw [alternatingSmoothSum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        push_cast
        ring
      linarith only [hhead]
    have hsdiff_val : (∑ j ∈ S₁ \ S₀, (-1 : ℝ) ^ j * (((2 * (N + 1) : ℕ) : ℝ) - j)) =
        if P (2 * N + 1) then -1 else 0 := by
      classical
      rw [hdiff, sum_filter, sum_insert (by omega : 2 * N + 1 ≠ 2 * N + 2), sum_singleton]
      have htop : (if P (2 * N + 2) then (-1 : ℝ) ^ (2 * N + 2) *
          (((2 * (N + 1) : ℕ) : ℝ) - (2 * N + 2 : ℕ)) else 0) = 0 := by
        have hz : (((2 * (N + 1) : ℕ) : ℝ) - (2 * N + 2 : ℕ)) = 0 := by push_cast; ring
        rw [hz, mul_zero, ite_self]
      rw [htop, add_zero]
      split_ifs with hP
      · have hpow : (-1 : ℝ) ^ (2 * N + 1) = -1 := by
          rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
        rw [hpow]
        push_cast
        ring
      · rfl
    have hodd_step : (oddSmoothIntegerCount (2 * (N + 1) - 1) y : ℝ) =
        (oddSmoothIntegerCount (2 * N - 1) y : ℝ) + if P (2 * N + 1) then 1 else 0 := by
      classical
      have hidx : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
      rw [hidx]
      let Odd₀ := (Sieve.smoothUpTo (Nat.primesLE y) (2 * N - 1)).filter (fun n => ¬ 2 ∣ n)
      let Odd₁ := (Sieve.smoothUpTo (Nat.primesLE y) (2 * N + 1)).filter (fun n => ¬ 2 ∣ n)
      by_cases hP : P (2 * N + 1)
      · rw [if_pos hP]
        have heq_set : Odd₁ = insert (2 * N + 1) Odd₀ := by
          ext j
          simp only [Odd₁, Odd₀, mem_filter, mem_smoothUpTo_iff, mem_insert]
          constructor
          · rintro ⟨⟨⟨hj1, hjle⟩, hf⟩, hnd⟩
            by_cases hjeq : j = 2 * N + 1
            · exact Or.inl hjeq
            · have hjne2N : j ≠ 2 * N := fun h => hnd (h ▸ dvd_mul_right 2 N)
              exact Or.inr ⟨⟨⟨hj1, by omega⟩, hf⟩, hnd⟩
          · rintro (rfl | ⟨⟨⟨hj1, hjle⟩, hf⟩, hnd⟩)
            · exact ⟨⟨⟨by omega, le_rfl⟩, hP⟩, by omega⟩
            · exact ⟨⟨⟨hj1, by omega⟩, hf⟩, hnd⟩
        have hnot : 2 * N + 1 ∉ Odd₀ := by
          simp only [Odd₀, mem_filter, mem_smoothUpTo_iff]
          omega
        change (Odd₁.card : ℝ) = (Odd₀.card : ℝ) + 1
        rw [heq_set, card_insert_of_notMem hnot]
        push_cast
        ring
      · rw [if_neg hP, add_zero]
        have heq_set : Odd₁ = Odd₀ := by
          ext j
          simp only [Odd₁, Odd₀, mem_filter, mem_smoothUpTo_iff]
          constructor
          · rintro ⟨⟨⟨hj1, hjle⟩, hf⟩, hnd⟩
            have hjne1 : j ≠ 2 * N + 1 := fun h => hP (h ▸ hf)
            have hjne0 : j ≠ 2 * N := fun h => hnd (h ▸ dvd_mul_right 2 N)
            exact ⟨⟨⟨hj1, by omega⟩, hf⟩, hnd⟩
          · rintro ⟨⟨⟨hj1, hjle⟩, hf⟩, hnd⟩
            exact ⟨⟨⟨hj1, by omega⟩, hf⟩, hnd⟩
        change (Odd₁.card : ℝ) = (Odd₀.card : ℝ)
        rw [heq_set]
    change _ + _ = (∑ j ∈ S₁, (-1 : ℝ) ^ j * (((2 * (N + 1) : ℕ) : ℝ) - j)) +
      (oddSmoothIntegerCount (2 * (N + 1) - 1) y : ℝ)
    rw [hsum_split, hsdiff_val, hodd_step]
    split_ifs <;> ring

/-- The raw complement identity `Ψ(x, y) + ∑_{m ∈ (y, B]} g(m) ⌊x / m⌋ = x` across
`x ∈ (y, B]` (`B < (y + 1)²`) uniquely forces `g` to be the ordinary prime indicator. -/
theorem smooth_complement_uniquely_selects_primes {y B : ℕ} (hB : B < (y + 1) ^ 2)
    (g : ℕ → ℝ) :
    (∀ x ∈ Ioc y B, (smoothIntegerCount x y : ℝ) +
      ∑ m ∈ Ioc y B, g m * ((x / m : ℕ) : ℝ) = x) ↔
      ∀ m ∈ Ioc y B, g m = if m.Prime then 1 else 0 := by
  classical
  let indP : ℕ → ℝ := fun m => if m.Prime then 1 else 0
  have htrue : ∀ x ∈ Ioc y B, (smoothIntegerCount x y : ℝ) +
      ∑ m ∈ Ioc y B, indP m * ((x / m : ℕ) : ℝ) = x := by
    intro x hx
    obtain ⟨hxy, hxB⟩ := mem_Ioc.mp hx
    have hc := count_smooth_and_multiples hxB (hxB.trans_lt hB)
    have hsum : (∑ m ∈ Ioc y B, indP m * ((x / m : ℕ) : ℝ)) =
        ∑ p ∈ largePrimes B y, ((x / p : ℕ) : ℝ) := by
      have hfilt : (Ioc y B).filter Nat.Prime = largePrimes B y := by
        ext p
        simp only [mem_filter, mem_Ioc, mem_largePrimes]
        tauto
      rw [← hfilt, sum_filter]
      refine sum_congr rfl fun m _ => ?_
      dsimp only [indP]
      split_ifs <;> simp
    rw [hsum]
    exact_mod_cast hc
  constructor
  · intro hg m hm
    obtain ⟨hmy, hmB⟩ := mem_Ioc.mp hm
    -- Strong induction on `d = m - (y + 1)`
    suffices hall : ∀ k : ℕ, y + 1 + k ≤ B → g (y + 1 + k) = indP (y + 1 + k) by
      have heq : y + 1 + (m - (y + 1)) = m := by omega
      simpa only [heq] using hall (m - (y + 1)) (by omega)
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hkB
      let x := y + 1 + k
      have hxIoc : x ∈ Ioc y B := mem_Ioc.mpr ⟨by omega, hkB⟩
      have h1 := hg x hxIoc
      have h2 := htrue x hxIoc
      have hdiff : ∑ j ∈ Ioc y B, (g j - indP j) * ((x / j : ℕ) : ℝ) = 0 := by
        calc
          ∑ j ∈ Ioc y B, (g j - indP j) * ((x / j : ℕ) : ℝ) =
              ∑ j ∈ Ioc y B, (g j * ((x / j : ℕ) : ℝ) - indP j * ((x / j : ℕ) : ℝ)) :=
            sum_congr rfl fun j _ => sub_mul (g j) (indP j) _
          _ = (∑ j ∈ Ioc y B, g j * ((x / j : ℕ) : ℝ)) -
                ∑ j ∈ Ioc y B, indP j * ((x / j : ℕ) : ℝ) := sum_sub_distrib _ _
          _ = 0 := by linarith only [h1, h2]
      have hsingle : (∑ j ∈ Ioc y B, (g j - indP j) * ((x / j : ℕ) : ℝ)) = g x - indP x := by
        rw [sum_eq_single_of_mem x hxIoc]
        · rw [Nat.div_self (by omega : 0 < x), Nat.cast_one, mul_one]
        · intro j hj hjx
          obtain ⟨hjy, _⟩ := mem_Ioc.mp hj
          rcases lt_or_gt_of_ne hjx with hlt | hgt
          · have hjk : j - (y + 1) < k := by omega
            have hjeq : y + 1 + (j - (y + 1)) = j := by omega
            have hgj := ih (j - (y + 1)) hjk (by omega)
            rw [hjeq] at hgj
            rw [hgj, sub_self, zero_mul]
          · rw [Nat.div_eq_of_lt hgt, Nat.cast_zero, mul_zero]
      linarith only [hdiff, hsingle]
  · intro h x hx
    rw [← htrue x hx]
    congr 1
    exact sum_congr rfl fun m hm => by rw [h m hm]

/-- Top-octave parity aliasing: whenever `2r - 1 ∈ (N, 2N]` (`N < 2r - 1` and `r ≤ N`), for
every `n ≤ N` the odd integer `2r - 1` and the adjacent even integer `2r` have identical
central-binomial carry `1_{r ≤ n}`. -/
theorem centralBinom_carry_top_octave_aliasing {N r n : ℕ}
    (hr : N < 2 * r - 1) (hrN : r ≤ N) (hn : n ≤ N) :
    ((2 * n) / (2 * r - 1)) % 2 = ((2 * n) / (2 * r)) % 2 ∧
      ((2 * n) / (2 * r)) % 2 = if r ≤ n then 1 else 0 := by
  have hrpos : 0 < r := by omega
  have hdiv2 : (2 * n) / (2 * r) = n / r := Nat.mul_div_mul_left n r two_pos
  by_cases h : r ≤ n
  · have hlt_nr : n < 2 * r := by omega
    have hnr1 : n / r = 1 := le_antisymm
      (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hrpos).mpr (by omega)))
      ((Nat.one_le_div_iff hrpos).mpr h)
    have hlt_odd : 2 * n < 2 * (2 * r - 1) := by omega
    have hge_odd : 2 * r - 1 ≤ 2 * n := by omega
    have hodd1 : (2 * n) / (2 * r - 1) = 1 := le_antisymm
      (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr hlt_odd))
      ((Nat.one_le_div_iff (by omega)).mpr hge_odd)
    simp [hdiv2, hnr1, hodd1, h]
  · have hlt : n < r := by omega
    have h1 : (2 * n) / (2 * r - 1) = 0 := Nat.div_eq_of_lt (by omega)
    have h2 : n / r = 0 := Nat.div_eq_of_lt hlt
    simp [hdiv2, h1, h2, h]

#print axioms smoothIntegerCount_eq_half_add_odd
#print axioms two_mul_smoothIntegerCount_sub_eq_alternating
#print axioms alternatingSmoothSum_eq_sum_odd_roots
#print axioms alternatingSmoothSum_two
#print axioms alternatingSmoothSum_buchstab
#print axioms sum_range_two_mul_smooth_dyadic_eq
#print axioms smooth_complement_uniquely_selects_primes
#print axioms centralBinom_carry_top_octave_aliasing

end GaloisForLFunctions.ExceptionalLayerTheory
