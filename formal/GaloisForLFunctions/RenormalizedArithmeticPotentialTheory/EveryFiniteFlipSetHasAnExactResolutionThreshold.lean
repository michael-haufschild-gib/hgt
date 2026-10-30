import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheResolutionThresholdOfAFlippedPrimeIsExact
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.GcdProfilesHaveFiniteRamanujanExpansions

/-!
# Every finite flip set has an exact resolution threshold

Flip the odd powers of every prime of a finite set `S`. The defect is the sum of the single-prime
defects (`twistDefect_finiteFlip_eq_sum`), so it is summable and the limit twist energy is the
sum of the single-prime energies.

The product trial `Y_S = Π_{p∈S} F_p`, `F_p = 1 − 2·1_{p∣n} + 2·1_{p²∣n}`, has unit square, and
`Y_S(n) Y_S(q^k n) = F_q(n) F_q(q^k n)` for `q ∈ S`: the other primes do not see `q^k`. Hence its
energy for the flip at `q` is that of `F_q`, and

`4 log q Σ_j q^{-(2j+1)} M(F_q · F_q(q^{2j+1}·)) ≤ (4 log q/q)(−1 + 2/q² + 1/(q² − 1)) < 0`

(`twistLimitEnergy_primeFlip_primeSquareTrial_le`): the first lag gives `M = −1 + 2/q²`, the
others at most `1`. `Y_S` is a function of `gcd(n, Π p²)`, hence a finite Ramanujan packet; its
energy is negative for large overlap, so every finite flip set is seen and its resolution
threshold is exact (`finiteFlip_resolutionThreshold_spec`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry
  RenormalizedBiarithmeticGeometry CompletedShell ArithmeticCastelnuovoSeveri Zeta23
  ArithmeticCountingPositivity TransMetzlerWeilPositivity.BoundedOverlap
open _root_.RHTower (vonMangoldtAtom)

/-- The twist flipping the odd powers of every prime of `S`. -/
def finiteFlipWeight (S : Finset ℕ) (n : ℕ) : ℝ :=
  finiteFlip S n * ArithmeticFunction.vonMangoldt n

theorem twistDefect_finiteFlip (S : Finset ℕ) (k : ℕ) :
    twistDefect (finiteFlipWeight S) k = (1 - finiteFlip S k) * vonMangoldtAtom k := by
  unfold twistDefect vonMangoldtAtom twistCoeff finiteFlipWeight
  split_ifs <;> ring

theorem finiteFlip_prime_pow {S : Finset ℕ} {q : ℕ} (hq : q.Prime) (j : ℕ) :
    finiteFlip S (q ^ j) = if q ∈ S then (-1) ^ j else 1 := by
  unfold finiteFlip
  rw [Nat.Prime.factorization_pow hq]
  split_ifs with hqS
  · rw [Finset.prod_eq_single q (fun p _ hpq => by rw [Finsupp.single_eq_of_ne hpq, pow_zero])
      (fun h => absurd hqS h), Finsupp.single_eq_same]
  · exact Finset.prod_eq_one fun p hp => by
      rw [Finsupp.single_eq_of_ne (fun h => hqS (h ▸ hp)), pow_zero]

/-- **The defect of a flip set is the sum of its single-prime defects.** -/
theorem twistDefect_finiteFlip_eq_sum {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (k : ℕ) :
    twistDefect (finiteFlipWeight S) k = ∑ p ∈ S, twistDefect (primeFlipWeight p) k := by
  rw [twistDefect_finiteFlip]
  simp only [twistDefect_primeFlip]
  rw [← sum_mul]
  by_cases hΛ : (ArithmeticFunction.vonMangoldt k : ℝ) = 0
  · have : vonMangoldtAtom k = 0 := by unfold vonMangoldtAtom; split_ifs <;> simp [hΛ]
    rw [this, mul_zero, mul_zero]
  obtain ⟨q, j, hq, hj, rfl⟩ :=
    (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  congr 1
  rw [finiteFlip_prime_pow hq]
  simp only [finiteFlip_prime_pow (S := {_}) hq, Finset.mem_singleton]
  split_ifs with hqS
  · rw [Finset.sum_eq_single q (fun p hp hpq => by rw [if_neg (Ne.symm hpq), sub_self])
      (fun h => absurd hqS h), if_pos rfl]
  · refine (Finset.sum_eq_zero fun p hp => ?_).symm.trans_eq' (by ring)
    rw [if_neg (fun h => hqS (h ▸ hp)), sub_self]

/-- **A finite flip set has summable defect.** -/
theorem summable_abs_twistDefect_finiteFlip {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Summable fun k => |twistDefect (finiteFlipWeight S) k| := by
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    (summable_sum fun p hp => summable_abs_twistDefect_primeFlip (hS p hp))
  rw [twistDefect_finiteFlip_eq_sum hS]
  exact abs_sum_le_sum_abs _ _

/-- The limit twist energy of a flip set is the sum of its single-prime energies. -/
theorem twistLimitEnergy_finiteFlip {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {y : ℕ → ℝ}
    {P : ℕ} (hP : 0 < P) (hy : Function.Periodic y P) :
    twistLimitEnergy (finiteFlipWeight S) y P =
      ∑ p ∈ S, twistLimitEnergy (primeFlipWeight p) y P := by
  set B := ∑ i ∈ range P, |y i| with hB
  have hyB : ∀ n, |y n| ≤ B := fun n => abs_le_of_periodic hP hy n
  have hM : ∀ k, |shiftMean y P k| ≤ B ^ 2 := by
    intro k
    unfold shiftMean periodMean
    have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
    rw [abs_div, abs_of_pos hP0, div_le_iff₀ hP0]
    calc |∑ i ∈ range P, y i * y (k * i)| ≤ ∑ i ∈ range P, B ^ 2 := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
          rw [abs_mul, sq]
          exact mul_le_mul (hyB i) (hyB _) (abs_nonneg _) ((abs_nonneg _).trans (hyB 0))
      _ = B ^ 2 * P := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]
  have hsum : ∀ p ∈ S, Summable fun k =>
      twistDefect (primeFlipWeight p) k / Real.sqrt k * shiftMean y P k := by
    intro p hp
    refine Summable.of_norm_bounded ((summable_abs_twistDefect_primeFlip (hS p hp)).mul_right
      (B ^ 2)) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_div]
    have hsk : 1 ≤ Real.sqrt k ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact Or.inr h
      · left
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast h)
    rcases hsk with hsk | rfl
    · calc |twistDefect (primeFlipWeight p) k| / |Real.sqrt k| * |shiftMean y P k|
          ≤ |twistDefect (primeFlipWeight p) k| / 1 * B ^ 2 := by
            rw [abs_of_nonneg (Real.sqrt_nonneg _)]
            gcongr
            exact hM k
        _ = |twistDefect (primeFlipWeight p) k| * B ^ 2 := by ring
    · simp [twistDefect_of_lt_two]
  unfold twistLimitEnergy
  simp_rw [twistDefect_finiteFlip_eq_sum hS, sum_div, sum_mul]
  rw [Summable.tsum_finsetSum hsum, mul_sum]

/-! ### The product trial -/

/-- The product of the prime-square trials of a flip set. -/
def flipSetTrial (S : Finset ℕ) (n : ℕ) : ℝ := ∏ p ∈ S, primeSquareTrial p n

theorem primeSquareTrial_coprime_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k n : ℕ) : primeSquareTrial p (q ^ k * n) = primeSquareTrial p n := by
  have hc1 : Nat.Coprime p (q ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp hq).mpr hpq)
  have hc2 : Nat.Coprime (p ^ 2) (q ^ k) := Nat.Coprime.pow_left 2 hc1
  unfold primeSquareTrial
  rw [hc1.dvd_mul_left, hc2.dvd_mul_left]

theorem primeSquareTrial_sq_eq_one (p n : ℕ) : primeSquareTrial p n * primeSquareTrial p n = 1 := by
  rw [← sq, primeSquareTrial_sq]

/-- The other primes do not see `q^k`. -/
theorem flipSetTrial_mul_dilate {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℕ} (hqS : q ∈ S)
    (k n : ℕ) :
    flipSetTrial S n * flipSetTrial S (q ^ k * n) =
      primeSquareTrial q n * primeSquareTrial q (q ^ k * n) := by
  unfold flipSetTrial
  rw [← prod_mul_distrib, Finset.prod_eq_single q (fun p hp hpq => by
      rw [primeSquareTrial_coprime_mul (hS p hp) (hS q hqS) hpq, primeSquareTrial_sq_eq_one])
    (fun h => absurd hqS h)]

/-- The mean of a divisibility indicator over a multiple of the divisor. -/
theorem periodMean_dvd_indicator {d P : ℕ} (hd : 0 < d) (hdP : d ∣ P) (hP : 0 < P) :
    periodMean (fun a => if d ∣ a then (1 : ℝ) else 0) P = 1 / d := by
  have hper : ∀ k, (fun a => if d ∣ a then (1 : ℝ) else 0) (k + P) =
      (fun a => if d ∣ a then (1 : ℝ) else 0) k := by
    intro k
    simp only [(Nat.dvd_add_left hdP).symm, Nat.dvd_add_right hdP]
  unfold periodMean
  rw [← sum_range_shift_of_periodic hper 1]
  have hcount : ∑ i ∈ range P, (if d ∣ i + 1 then (1 : ℝ) else 0) = ((P / d : ℕ) : ℝ) := by
    rw [← Nat.card_multiples P d, Finset.sum_boole]
  rw [hcount, Nat.cast_div hdP (by exact_mod_cast hd.ne')]
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- **The flip energy of the prime-square trial is negative.** -/
theorem twistLimitEnergy_primeFlip_primeSquareTrial_le {q : ℕ} (hq : q.Prime) {P : ℕ}
    (hP : 0 < P) (hqP : q ^ 2 ∣ P) :
    twistLimitEnergy (primeFlipWeight q) (primeSquareTrial q) P ≤
      4 * Real.log q / q * (-1 + 2 / (q : ℝ) ^ 2 + 1 / ((q : ℝ) ^ 2 - 1)) := by
  have hper : Function.Periodic (primeSquareTrial q) P := by
    intro n
    obtain ⟨r, hr⟩ := hqP
    unfold primeSquareTrial
    have h1 : q ∣ n + P ↔ q ∣ n :=
      Nat.dvd_add_left ((dvd_pow_self q two_ne_zero).trans ⟨r, hr⟩)
    have h2 : q ^ 2 ∣ n + P ↔ q ^ 2 ∣ n := Nat.dvd_add_left ⟨r, hr⟩
    simp only [h1, h2]
  rw [twistLimitEnergy_primeFlip hq hP hper]
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  -- the first lag
  have hM1 : shiftMean (primeSquareTrial q) P (q ^ (2 * 0 + 1)) = -1 + 2 / (q : ℝ) ^ 2 := by
    unfold shiftMean
    simp only [mul_zero, zero_add, pow_one]
    have hfun : (fun a => primeSquareTrial q a * primeSquareTrial q (q * a)) =
        fun a => -1 + 2 * (if q ^ 2 ∣ a then (1 : ℝ) else 0) := by
      funext a
      exact primeSquareTrial_mul_correlation hq.pos a
    rw [hfun]
    have hmean := periodMean_dvd_indicator (pow_pos hq.pos 2) hqP hP
    unfold periodMean at hmean ⊢
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, add_div,
      mul_div_assoc, hmean]
    have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    field_simp
    push_cast
    ring
  -- every later lag has mean at most one
  have hMle : ∀ k, shiftMean (primeSquareTrial q) P k ≤ 1 := by
    intro k
    unfold shiftMean periodMean
    have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
    rw [div_le_one hP0]
    calc ∑ i ∈ range P, primeSquareTrial q i * primeSquareTrial q (k * i)
        ≤ ∑ i ∈ range P, (1 : ℝ) := sum_le_sum fun i _ => by
          have := abs_primeSquareTrial q i
          have := abs_primeSquareTrial q (k * i)
          have h := abs_mul (primeSquareTrial q i) (primeSquareTrial q (k * i))
          exact (le_abs_self _).trans (by rw [h]; nlinarith [abs_nonneg (primeSquareTrial q i)])
      _ = P := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]
  set g : ℕ → ℝ := fun j => shiftMean (primeSquareTrial q) P (q ^ (2 * j + 1)) /
    (q : ℝ) ^ (2 * j + 1) with hg
  have hgeom : Summable fun j : ℕ => (1 / (q : ℝ)) ^ (2 * j + 1) := by
    have h := summable_geometric_of_lt_one (r := (1 / (q : ℝ)) ^ 2) (by positivity)
      (by rw [_root_.one_div_pow, div_lt_one (by positivity)]; nlinarith)
    refine (h.mul_left (1 / (q : ℝ))).congr fun j => ?_
    rw [← pow_mul, pow_succ]
    ring
  have hgabs : ∀ j, |g j| ≤ (1 / (q : ℝ)) ^ (2 * j + 1) := by
    intro j
    simp only [hg]
    rw [abs_div, abs_of_pos (by positivity), _root_.one_div_pow, div_le_div_iff_of_pos_right
      (by positivity)]
    unfold shiftMean periodMean
    have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
    rw [abs_div, abs_of_pos hP0, div_le_one hP0]
    calc |∑ i ∈ range P, primeSquareTrial q i * primeSquareTrial q (q ^ (2 * j + 1) * i)|
        ≤ ∑ i ∈ range P, (1 : ℝ) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
          rw [abs_mul, abs_primeSquareTrial, abs_primeSquareTrial, mul_one]
      _ = P := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]
  have hgsum : Summable g := Summable.of_norm_bounded hgeom fun j => by
    rw [Real.norm_eq_abs]; exact hgabs j
  have htail : ∑' j, g (j + 1) ≤ 1 / ((q : ℝ) * ((q : ℝ) ^ 2 - 1)) := by
    have hq2 : (1 : ℝ) < (q : ℝ) ^ 2 := by nlinarith
    have hgeo := tsum_geometric_of_lt_one (r := (1 / (q : ℝ)) ^ 2) (by positivity)
      (by rw [_root_.one_div_pow, div_lt_one (by positivity)]; exact hq2)
    have hsumt : Summable fun j : ℕ => (1 / (q : ℝ)) ^ (2 * (j + 1) + 1) :=
      (summable_nat_add_iff 1).mpr hgeom
    calc ∑' j, g (j + 1) ≤ ∑' j : ℕ, (1 / (q : ℝ)) ^ (2 * (j + 1) + 1) :=
          Summable.tsum_le_tsum (fun j => (le_abs_self _).trans (hgabs (j + 1)))
            ((summable_nat_add_iff 1).mpr hgsum) hsumt
      _ = (1 / (q : ℝ)) ^ 3 * ∑' j : ℕ, ((1 / (q : ℝ)) ^ 2) ^ j := by
          rw [← tsum_mul_left]
          exact tsum_congr fun j => by rw [← pow_mul, ← pow_add]; ring_nf
      _ = 1 / ((q : ℝ) * ((q : ℝ) ^ 2 - 1)) := by
          rw [hgeo]
          have hqq : (q : ℝ) ^ 2 - 1 ≠ 0 := by linarith
          field_simp
          ring
  rw [hgsum.tsum_eq_zero_add]
  have hg0 : g 0 = (-1 + 2 / (q : ℝ) ^ 2) / q := by
    simp only [hg]
    rw [hM1]
    ring
  rw [hg0]
  have hfac : 0 ≤ 4 * Real.log q := by positivity
  calc 4 * Real.log q * ((-1 + 2 / (q : ℝ) ^ 2) / q + ∑' j, g (j + 1))
      ≤ 4 * Real.log q * ((-1 + 2 / (q : ℝ) ^ 2) / q + 1 / ((q : ℝ) * ((q : ℝ) ^ 2 - 1))) :=
        mul_le_mul_of_nonneg_left (by linarith) hfac
    _ = 4 * Real.log q / q * (-1 + 2 / (q : ℝ) ^ 2 + 1 / ((q : ℝ) ^ 2 - 1)) := by
        have hqq : (q : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
        field_simp

theorem flip_gain_bracket_neg {q : ℕ} (hq : q.Prime) :
    -1 + 2 / (q : ℝ) ^ 2 + 1 / ((q : ℝ) ^ 2 - 1) < 0 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have h4 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have h1 : 2 / (q : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h2 : 1 / ((q : ℝ) ^ 2 - 1) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

/-! ### The product trial as a Ramanujan packet -/

/-- `M_S = Π_{p∈S} p²`: the trial `Y_S` reads `n` only through `gcd(n, M_S)`. -/
def flipSetModulus (S : Finset ℕ) : ℕ := ∏ p ∈ S, p ^ 2

theorem flipSetModulus_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : 0 < flipSetModulus S :=
  Finset.prod_pos fun p hp => pow_pos (hS p hp).pos 2

theorem sq_dvd_flipSetModulus {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) : p ^ 2 ∣ flipSetModulus S :=
  Finset.dvd_prod_of_mem _ hp

theorem primeSquareTrial_of_sq_dvd {p n : ℕ} (h : p ^ 2 ∣ n) : primeSquareTrial p n = 1 := by
  unfold primeSquareTrial
  rw [if_pos ((dvd_pow_self p two_ne_zero).trans h), if_pos h]
  ring

theorem flipSetTrial_gcd {S : Finset ℕ} (n : ℕ) :
    flipSetTrial S (n.gcd (flipSetModulus S)) = flipSetTrial S n := by
  unfold flipSetTrial
  refine Finset.prod_congr rfl fun p hp => ?_
  have h2 := sq_dvd_flipSetModulus hp
  have h1 : p ∣ flipSetModulus S := (dvd_pow_self p two_ne_zero).trans h2
  unfold primeSquareTrial
  simp only [Nat.dvd_gcd_iff, h1, h2, and_true]

theorem flipSetTrial_of_dvd {S : Finset ℕ} {n : ℕ} (h : flipSetModulus S ∣ n) :
    flipSetTrial S n = 1 :=
  Finset.prod_eq_one fun p hp => primeSquareTrial_of_sq_dvd ((sq_dvd_flipSetModulus hp).trans h)

theorem flipSetTrial_periodic {S : Finset ℕ} {P : ℕ} (hP : flipSetModulus S ∣ P) :
    Function.Periodic (flipSetTrial S) P := by
  intro n
  unfold flipSetTrial
  refine Finset.prod_congr rfl fun p hp => ?_
  have h2 := (sq_dvd_flipSetModulus hp).trans hP
  have h1 := (dvd_pow_self p two_ne_zero).trans h2
  unfold primeSquareTrial
  simp only [Nat.dvd_add_left h1, Nat.dvd_add_left h2]

/-- **The product trial is a Ramanujan packet.** -/
theorem exists_flipSetTrial_packet {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∃ β : ℕ → ℝ, packetProfile (flipSetModulus S).divisors β = flipSetTrial S := by
  have hM := flipSetModulus_pos hS
  obtain ⟨a, ha⟩ := exists_gcdProfile_normalizedRamanujan_expansion (flipSetTrial S) hM
  refine ⟨a, funext fun n => ?_⟩
  have hT : ∀ m ∈ (flipSetModulus S).divisors, 0 < m := fun m hm => Nat.pos_of_mem_divisors hm
  have hMP : flipSetModulus S ∣ packetPeriod (flipSetModulus S).divisors :=
    Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self _ hM.ne')
  have hpos : ∀ n, 0 < n → packetProfile (flipSetModulus S).divisors a n = flipSetTrial S n := by
    intro n hn
    rw [packetProfile, ← ha n hn, flipSetTrial_gcd]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hper := packetProfile_periodic hT a
    have hP := packetPeriod_pos hT
    have h0 := hper 0
    rw [zero_add] at h0
    rw [← h0, hpos _ hP, flipSetTrial_of_dvd hMP, flipSetTrial_of_dvd (dvd_zero _)]
  · exact hpos n hn

/-- **The product trial has negative flip energy.** -/
theorem twistLimitEnergy_finiteFlip_flipSetTrial_neg {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) {P : ℕ} (hP : 0 < P) (hMP : flipSetModulus S ∣ P) :
    twistLimitEnergy (finiteFlipWeight S) (flipSetTrial S) P < 0 := by
  rw [twistLimitEnergy_finiteFlip hS hP (flipSetTrial_periodic hMP)]
  refine Finset.sum_neg (fun q hq => ?_) hne
  have hqP : q ^ 2 ∣ P := (sq_dvd_flipSetModulus hq).trans hMP
  have hqper : Function.Periodic (primeSquareTrial q) P := by
    have h := flipSetTrial_periodic (S := {q}) (P := P) (by
      simpa [flipSetModulus] using hqP)
    simpa [flipSetTrial] using h
  have heq : twistLimitEnergy (primeFlipWeight q) (flipSetTrial S) P =
      twistLimitEnergy (primeFlipWeight q) (primeSquareTrial q) P := by
    rw [twistLimitEnergy_primeFlip (hS q hq) hP (flipSetTrial_periodic hMP),
      twistLimitEnergy_primeFlip (hS q hq) hP hqper]
    congr 2
    funext j
    congr 1
    unfold shiftMean
    congr 1
    funext a
    exact flipSetTrial_mul_dilate hS hq _ a
  rw [heq]
  refine lt_of_le_of_lt (twistLimitEnergy_primeFlip_primeSquareTrial_le (hS q hq) hP hqP) ?_
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (hS q hq).pos
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (hS q hq).one_lt)
  exact mul_neg_of_pos_of_neg (by positivity) (flip_gain_bracket_neg (hS q hq))

/-! ### The exact threshold of a flip set -/

section Threshold

variable {φ : ℝ → ℝ}

/-- **Every nonempty finite flip set is seen.** -/
theorem exists_finiteFlip_resolutionBottom_neg (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ resolutionBottom (finiteFlipWeight S) φ c₁ < 0 := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  have hlam := summable_abs_twistDefect_finiteFlip hS
  obtain ⟨β, hβ⟩ := exists_flipSetTrial_packet hS
  set T := (flipSetModulus S).divisors with hTdef
  have hT : ∀ m ∈ T, 0 < m := fun m hm => Nat.pos_of_mem_divisors hm
  have hMP : flipSetModulus S ∣ packetPeriod T :=
    Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self _ (flipSetModulus_pos hS).ne')
  have hneg := twistLimitEnergy_finiteFlip_flipSetTrial_neg hS hne (packetPeriod_pos hT) hMP
  -- the conductor energies vanish at large overlap
  have hlim : Tendsto (fun c => packetEnergy (finiteFlipWeight S) φ c T β) atTop
      (𝓝 (twistLimitEnergy (finiteFlipWeight S) (flipSetTrial S) (packetPeriod T))) := by
    have h := tendsto_finsetSum T fun m _ =>
      (tendsto_completedConductorEnergy_atTop hφ hsupp hM m).const_mul (β m ^ 2)
    simp only [mul_zero, sum_const_zero] at h
    have h' := h.add_const (twistLimitEnergy (finiteFlipWeight S) (flipSetTrial S)
      (packetPeriod T))
    rw [zero_add] at h'
    refine h'.congr fun c => ?_
    unfold packetEnergy
    rw [hβ]
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hneg))
  set c₁ := max c₂ 1 with hc₁
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hE := hc₂ c₁ (le_max_left _ _)
  refine ⟨c₁, hc₁0, ?_⟩
  have hmul := resolutionBottom_mul_le hφ hsupp hM hc₁0 hlam hT β
  have hS0 : 0 < ∑ m ∈ T, β m ^ 2 := by
    rcases (sum_nonneg fun m (_ : m ∈ T) => sq_nonneg (β m)).lt_or_eq with h | h
    · exact h
    · have hβ0 : ∀ m ∈ T, β m = 0 := fun m hm =>
        pow_eq_zero_iff (by norm_num) |>.mp
          ((sum_eq_zero_iff_of_nonneg fun m _ => sq_nonneg (β m)).mp h.symm m hm)
      rw [packetEnergy_eq_zero hβ0] at hE
      exact absurd hE (lt_irrefl 0)
  by_contra hge
  push_neg at hge
  have := mul_nonneg hge hS0.le
  linarith

/-- **The exact resolution threshold of a finite flip set.** For every profile without real
Fourier zeros and every nonempty finite set `S` of primes, the threshold `c_0(ω_S)` is positive
and finite; below it the `S`-flipped complete Weil matrix is eventually positive definite, above
it a unit Ramanujan packet makes the flipped form eventually negative. -/
theorem finiteFlip_resolutionThreshold_spec (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    0 < resolutionThreshold (finiteFlipWeight S) φ ∧
      (∀ c, 0 < c → c < resolutionThreshold (finiteFlipWeight S) φ →
        ∀ᶠ N : ℕ in atTop, (twistedCompleteWeilMatrix (finiteFlipWeight S) φ c N).PosDef) ∧
      (∀ c, resolutionThreshold (finiteFlipWeight S) φ < c →
        ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 ∧
          ∀ᶠ N : ℕ in atTop, weilQuadTw (finiteFlipWeight S)
            (atomicTest N (packetCoeff (packetProfile T β) N) (atomDilate φ (c / N))) < 0) := by
  obtain ⟨c₁, hc₁, hseen⟩ := exists_finiteFlip_resolutionBottom_neg hφ hsupp hFT hS hne
  obtain ⟨h1, -, h3, h4⟩ := resolutionThreshold_spec hφ hsupp hFT
    (summable_abs_twistDefect_finiteFlip hS) hc₁ hseen
  exact ⟨h1, h3, h4⟩

end Threshold

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
