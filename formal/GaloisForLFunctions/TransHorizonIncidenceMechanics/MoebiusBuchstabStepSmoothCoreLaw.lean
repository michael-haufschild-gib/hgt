import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabSlopeLawAndPrimeHorizonDissipation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ComplementaryQuotientAndSecondOctaveLaw
import GaloisForLFunctions.BezoutValuationIncidence.QuotientDualOctaveReciprocityAndValuationSwitching

/-!
# The smooth-core law of Möbius Buchstab steps

Adding the horizon `m` changes the Möbius prefix energy by the band step
`E_m(M; μ) - E_{m-1}(M; μ) = Δ(m, B)`, `B = ⌊M/m⌋`, with

`Δ(m, B) = μ(m)² B + 2 μ(m) Σ_{j ≤ B} s_{m-1}(mj)`.

Past the horizon, `s_{m-1}(mj) = -Σ_{q | mj, q ≤ j} μ(mj/q)`: only the complementary quotients
`q ≤ j ≤ B` of `mj` matter, and these cannot see a prime factor of `m` larger than `B`. Hence
in band `B` a squarefree horizon `m = r m'` whose cofactor `m'` has only prime factors `> B`
satisfies

* `Δ(r m', B) = Δ(r, B)` when `r ≥ 2`, and
* `Δ(m', B) = B - 2` when `r = 1`.

So the step at a squarefree horizon depends only on its `B`-smooth core `gcd(m, B#)`: in every
band the Möbius step takes at most `2^{π(B)} + 1` values, one for each squarefree divisor of the
primorial `B#` and the value `0` of the non-squarefree horizons. The first octave (`B = 1`, step
`-1`), the parity dichotomy of the second band and the `(2,3)`-adic classification of the third
band are the cases `B ≤ 3`; explicit classes: `Δ(2, B) = -B`, `Δ(3, B) = 2⌊B/2⌋ - B`,
`Δ(6, B) = -B - 2⌊B/5⌋`.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The Möbius band step `Δ(m, B) = μ(m)² B + 2 μ(m) Σ_{j ≤ B} s_{m-1}(mj)`. -/
def moebiusBandStep (m B : ℕ) : ℝ :=
  moebiusReal m ^ 2 * (B : ℝ) +
    2 * moebiusReal m * ∑ j ∈ Icc 1 B, sieveSeq (m - 1) moebiusReal (m * j)

/-- The horizon step of the Möbius prefix energy is the band step at `B = ⌊M/(n+1)⌋`. -/
theorem sieveL2PrefixEnergy_moebius_step_eq_bandStep (n M : ℕ) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      moebiusBandStep (n + 1) (M / (n + 1)) := by
  rw [sieveL2PrefixEnergy_succ_horizon_sub_eq, moebiusBandStep, Nat.add_sub_cancel]

/-! ### Complementary quotients past the horizon -/

/-- Past the horizon `m - 1`, the response at `mj` is read from the complementary quotients
`q ≤ j`: `s_{m-1}(mj) = -Σ_{q | mj, q ≤ j} μ(mj/q)`. -/
theorem sieveSeq_moebius_mul_eq_neg_quotients {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j)
    (hmj : 2 ≤ m * j) :
    sieveSeq (m - 1) moebiusReal (m * j) =
      -∑ q ∈ (m * j).divisors.filter (· ≤ j), moebiusReal (m * j / q) := by
  rw [sieveSeq_moebiusReal_eq_neg_sum_gt _ hmj,
    sum_divisors_filter_gt_eq_complementaryQuotientTail, complementaryQuotientTail]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext q
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hq, hne⟩, hlt⟩
    refine ⟨⟨hq, hne⟩, ?_⟩
    have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hq (by omega)
    by_contra hqj
    push_neg at hqj
    have : m * j / q < m := by
      rw [Nat.div_lt_iff_lt_mul hq0]
      exact Nat.mul_lt_mul_of_pos_left hqj (by omega)
    omega
  · rintro ⟨⟨hq, hne⟩, hqj⟩
    refine ⟨⟨hq, hne⟩, ?_⟩
    have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hq (by omega)
    have : m ≤ m * j / q := by
      rw [Nat.le_div_iff_mul_le hq0]
      exact Nat.mul_le_mul_left m hqj
    omega

/-- Complementary quotients `q ≤ j ≤ B` do not see a cofactor `m'` whose prime factors all exceed
`B` and which is coprime to `r`: the quotient sum of `r m' j` is `μ(m')` times that of `r j`. -/
theorem sum_quotients_rough_cofactor {r m' j B : ℕ} (hjB : j ≤ B)
    (hrough : ∀ p, p.Prime → p ∣ m' → B < p) (hcop : Nat.Coprime r m') :
    ∑ q ∈ (r * m' * j).divisors.filter (· ≤ j), moebiusReal (r * m' * j / q) =
      moebiusReal m' * ∑ q ∈ (r * j).divisors.filter (· ≤ j), moebiusReal (r * j / q) := by
  -- primes up to `B` never divide `m'`
  have hsmall : ∀ x, 1 ≤ x → x ≤ B → Nat.Coprime x m' := fun x hx hxB =>
    Nat.coprime_of_dvd fun p hp hpx hpm => by
      have := hrough p hp hpm
      have := Nat.le_of_dvd (by omega) hpx
      omega
  have hjm : Nat.Coprime (r * j) m' := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [mul_zero, Nat.coprime_zero_left]
      rcases Nat.eq_zero_or_pos m' with rfl | hm'
      · exfalso
        exact absurd (hrough 2 Nat.prime_two (dvd_zero 2)) (by omega)
      · by_contra h1
        obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd h1
        exact absurd (hrough p hp hpm) (by omega)
    · exact Nat.Coprime.mul hcop (hsmall j hj hjB)
  have hset : (r * m' * j).divisors.filter (· ≤ j) = (r * j).divisors.filter (· ≤ j) := by
    ext q
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hq, hne⟩, hqj⟩
      have hq0 : 0 < q := Nat.pos_of_ne_zero fun h => by subst h; simp at hq; omega
      have hqm : Nat.Coprime q m' := hsmall q hq0 (hqj.trans hjB)
      refine ⟨⟨hqm.dvd_of_dvd_mul_left ?_, fun h => hne (by rw [mul_right_comm, h, zero_mul])⟩, hqj⟩
      rwa [mul_right_comm, mul_comm] at hq
    · rintro ⟨⟨hq, hne⟩, hqj⟩
      refine ⟨⟨?_, ?_⟩, hqj⟩
      · rw [mul_right_comm]; exact Dvd.dvd.mul_right hq m'
      · rw [mul_right_comm]; exact mul_ne_zero hne (fun h => by
          subst h; exact absurd (hrough 2 Nat.prime_two (dvd_zero 2)) (by omega))
  rw [hset, mul_sum]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨⟨hqd, -⟩, -⟩ := by simpa only [mem_filter, Nat.mem_divisors] using hq
  have hdiv : r * m' * j / q = m' * (r * j / q) := by
    rw [mul_right_comm, mul_comm, Nat.mul_div_assoc _ hqd]
  have hc : Nat.Coprime m' (r * j / q) :=
    (hjm.coprime_dvd_left (Nat.div_dvd_of_dvd hqd)).symm
  rw [hdiv]
  unfold moebiusReal
  rw [isMultiplicative_moebius.map_mul_of_coprime hc]
  push_cast; ring

/-! ### The smooth-core law -/

/-- **Rough-cofactor invariance.** In band `B`, a squarefree cofactor `m'` with all prime factors
`> B`, coprime to `r ≥ 2`, leaves the Möbius band step unchanged: `Δ(r m', B) = Δ(r, B)`. -/
theorem moebiusBandStep_mul_rough {r m' B : ℕ} (hr : 2 ≤ r) (hsq : Squarefree m')
    (hrough : ∀ p, p.Prime → p ∣ m' → B < p) (hcop : Nat.Coprime r m') :
    moebiusBandStep (r * m') B = moebiusBandStep r B := by
  have hm' : 1 ≤ m' := Nat.pos_of_ne_zero hsq.ne_zero
  have hμ2 : moebiusReal m' ^ 2 = 1 := by
    unfold moebiusReal
    have h1 : |(μ m' : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
    rw [← sq_abs, h1]; norm_num
  have hμ : moebiusReal (r * m') = moebiusReal r * moebiusReal m' := by
    unfold moebiusReal
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop]; push_cast; ring
  have hterm : ∀ j ∈ Icc 1 B, sieveSeq (r * m' - 1) moebiusReal (r * m' * j) =
      moebiusReal m' * sieveSeq (r - 1) moebiusReal (r * j) := by
    intro j hj
    obtain ⟨hj1, hjB⟩ := mem_Icc.mp hj
    have h2 : 2 ≤ r * j := by nlinarith
    have h2' : 2 ≤ r * m' * j := by nlinarith
    rw [sieveSeq_moebius_mul_eq_neg_quotients (by nlinarith) hj1 h2',
      sieveSeq_moebius_mul_eq_neg_quotients (by omega) hj1 h2,
      sum_quotients_rough_cofactor hjB hrough hcop]
    ring
  unfold moebiusBandStep
  rw [sum_congr rfl hterm, ← mul_sum, hμ]
  linear_combination (moebiusReal r ^ 2 * (B : ℝ) +
    2 * moebiusReal r * ∑ j ∈ Icc 1 B, sieveSeq (r - 1) moebiusReal (r * j)) * hμ2

/-- **The rough class.** A squarefree horizon `m ≥ 2` with all prime factors `> B` has band step
exactly `B - 2` in every band `B ≥ 1`: only the quotient `q = j = 1` is visible. -/
theorem moebiusBandStep_rough {m B : ℕ} (hm : 2 ≤ m) (hB : 1 ≤ B) (hsq : Squarefree m)
    (hrough : ∀ p, p.Prime → p ∣ m → B < p) :
    moebiusBandStep m B = (B : ℝ) - 2 := by
  have hμ2 : moebiusReal m ^ 2 = 1 := by
    unfold moebiusReal
    have h1 : |(μ m : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
    rw [← sq_abs, h1]; norm_num
  have hterm : ∀ j ∈ Icc 1 B, sieveSeq (m - 1) moebiusReal (m * j) =
      if j = 1 then -moebiusReal m else 0 := by
    intro j hj
    obtain ⟨hj1, hjB⟩ := mem_Icc.mp hj
    have hq := sum_quotients_rough_cofactor (r := 1) hjB hrough (Nat.coprime_one_left m)
    simp only [one_mul] at hq
    have hall : j.divisors.filter (· ≤ j) = j.divisors :=
      filter_true_of_mem fun q hq => Nat.divisor_le hq
    rw [sieveSeq_moebius_mul_eq_neg_quotients (by omega) hj1 (by nlinarith), hq, hall,
      Nat.sum_div_divisors]
    split_ifs with h1
    · subst h1; simp [moebiusReal]
    · rw [sum_divisors_moebiusReal_eq_zero (by omega)]; ring
  unfold moebiusBandStep
  rw [sum_congr rfl hterm, sum_ite_eq' (Icc 1 B) 1 (fun _ => -moebiusReal m),
    if_pos (mem_Icc.mpr ⟨le_rfl, hB⟩), hμ2]
  linear_combination (-2 : ℝ) * hμ2

/-- **Smooth-core law.** In band `B ≥ 1` the Möbius step at a squarefree horizon `m ≥ 2` depends
only on its `B`-smooth core `r = gcd(m, B#)`: it is `B - 2` if `r = 1` and `Δ(r, B)` otherwise. -/
theorem moebiusBandStep_eq_smoothCore {m B : ℕ} (hm : 2 ≤ m) (hB : 1 ≤ B) (hsq : Squarefree m) :
    moebiusBandStep m B =
      if Nat.gcd m (primorial B) = 1 then (B : ℝ) - 2
      else moebiusBandStep (Nat.gcd m (primorial B)) B := by
  set r := Nat.gcd m (primorial B) with hr_def
  have hrm : r * (m / r) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m _)
  have hsq' : Squarefree (r * (m / r)) := by rwa [hrm]
  have hcop : Nat.Coprime r (m / r) := Nat.coprime_of_squarefree_mul hsq'
  have hrough : ∀ p, p.Prime → p ∣ m / r → B < p := by
    intro p hp hpm
    by_contra hpB
    push_neg at hpB
    have hpr : p ∣ r := Nat.dvd_gcd (hpm.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m _)))
      ((hp.dvd_primorial_iff).mpr hpB)
    exact hp.one_lt.ne' ((hcop.coprime_dvd_left hpr).eq_one_of_dvd hpm)
  split_ifs with h1
  · have hmr : m / r = m := by rw [h1, Nat.div_one]
    exact moebiusBandStep_rough hm hB hsq (hmr ▸ hrough)
  · have hr0 : r ≠ 0 := Nat.gcd_ne_zero_left (by omega)
    rw [← hrm]
    exact moebiusBandStep_mul_rough (by omega) hsq'.of_mul_right hrough hcop

/-- In band `B ≥ 1` the step at any horizon `m ≥ 2` lies in the finite set made of `0`, `B - 2`
and the steps `Δ(r, B)` of the divisors `r` of the primorial `B#`. -/
theorem moebiusBandStep_mem_finite_values {m B : ℕ} (hm : 2 ≤ m) (hB : 1 ≤ B) :
    moebiusBandStep m B ∈
      insert 0 (insert ((B : ℝ) - 2) ((primorial B).divisors.image (moebiusBandStep · B))) := by
  by_cases hsq : Squarefree m
  · rw [moebiusBandStep_eq_smoothCore hm hB hsq]
    split_ifs
    · exact mem_insert_of_mem (mem_insert_self _ _)
    · refine mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr ⟨_, ?_, rfl⟩))
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, (primorial_pos B).ne'⟩
  · have h0 : moebiusReal m = 0 := moebiusReal_eq_zero_of_not_squarefree m hsq
    simp [moebiusBandStep, h0]

/-! ### Explicit classes -/

/-- The even class: `Δ(2, B) = -B`. -/
theorem moebiusBandStep_two (B : ℕ) : moebiusBandStep 2 B = -(B : ℝ) := by
  have hμ : moebiusReal 2 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hs : ∀ j ∈ Icc 1 B, sieveSeq (2 - 1) moebiusReal (2 * j) = 1 := by
    intro j _
    simp [sieveSeq, moebiusReal]
  unfold moebiusBandStep
  rw [sum_congr rfl hs, hμ]
  simp only [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
  ring

/-- The class of `3`: `Δ(3, B) = 2⌊B/2⌋ - B`. -/
theorem moebiusBandStep_three (B : ℕ) :
    moebiusBandStep 3 B = 2 * ((B / 2 : ℕ) : ℝ) - B := by
  have hμ : moebiusReal 3 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  have hI : Icc 1 2 = ({1, 2} : Finset ℕ) := by
    ext d; simp only [mem_Icc, mem_insert, mem_singleton]; omega
  have hs : ∀ j ∈ Icc 1 B, sieveSeq (3 - 1) moebiusReal (3 * j) =
      1 - if 2 ∣ j then 1 else 0 := by
    intro j _
    have h23 : 2 ∣ 3 * j ↔ 2 ∣ j :=
      (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 2 3))
    simp only [sieveSeq, show (3 : ℕ) - 1 = 2 by rfl, hI, sum_filter]
    rw [sum_insert (by decide), sum_singleton]
    simp only [one_dvd, if_true, h23]
    split_ifs <;>
      simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hcount : (∑ j ∈ Icc 1 B, (if 2 ∣ j then (1 : ℝ) else 0)) = ((B / 2 : ℕ) : ℝ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hIoc : Icc 1 B = Ioc 0 B := by ext; simp only [mem_Icc, mem_Ioc]; omega
    rw [hIoc, Nat.Ioc_filter_dvd_card_eq_div]
  unfold moebiusBandStep
  rw [sum_congr rfl hs, sum_sub_distrib, hcount, hμ]
  simp only [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
  ring

/-- The class of `6`: `Δ(6, B) = -B - 2⌊B/5⌋`. -/
theorem moebiusBandStep_six (B : ℕ) :
    moebiusBandStep 6 B = -(B : ℝ) - 2 * ((B / 5 : ℕ) : ℝ) := by
  have h := sieveL2PrefixEnergy_moebius_six_step (6 * B)
  rw [show (6 : ℕ) = 5 + 1 from rfl, sieveL2PrefixEnergy_moebius_step_eq_bandStep] at h
  simpa only [show 5 + 1 = 6 from rfl, Nat.mul_div_cancel_left B (by norm_num : 0 < 6)] using h

/-! ### The energy form -/

/-- **Smooth-core law for the Möbius prefix energy.** If `n + 1 ≥ 2` is squarefree and
`B = ⌊M/(n+1)⌋ ≥ 1`, the horizon step `E_{n+1}(M; μ) - E_n(M; μ)` equals `B - 2` when `n + 1` has
no prime factor `≤ B`, and otherwise the band step of the `B`-smooth core `gcd(n+1, B#)`. -/
theorem sieveL2PrefixEnergy_moebius_step_smoothCore {n M : ℕ} (hn : 1 ≤ n)
    (hsq : Squarefree (n + 1)) (hM : n + 1 ≤ M) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      if Nat.gcd (n + 1) (primorial (M / (n + 1))) = 1 then ((M / (n + 1) : ℕ) : ℝ) - 2
      else moebiusBandStep (Nat.gcd (n + 1) (primorial (M / (n + 1)))) (M / (n + 1)) := by
  rw [sieveL2PrefixEnergy_moebius_step_eq_bandStep]
  exact moebiusBandStep_eq_smoothCore (by omega)
    ((Nat.one_le_div_iff (by omega)).mpr hM) hsq

/-- **Even rough horizons dissipate a full band.** If `n + 1 = 2m'` with `m'` odd, squarefree and
all prime factors of `m'` exceeding `B = ⌊M/(n+1)⌋`, then `E_{n+1}(M; μ) = E_n(M; μ) - B`. -/
theorem sieveL2PrefixEnergy_moebius_step_even_rough {n M m' : ℕ} (hnm : n + 1 = 2 * m')
    (hodd : ¬ 2 ∣ m') (hsq : Squarefree m') (hrough : ∀ p, p.Prime → p ∣ m' → M / (n + 1) < p) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      -((M / (n + 1) : ℕ) : ℝ) := by
  rw [sieveL2PrefixEnergy_moebius_step_eq_bandStep, hnm,
    moebiusBandStep_mul_rough le_rfl hsq (hnm ▸ hrough)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd), moebiusBandStep_two]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
