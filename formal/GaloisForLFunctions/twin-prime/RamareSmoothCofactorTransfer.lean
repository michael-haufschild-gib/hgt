import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusTwistRate
import GaloisForLFunctions.RHTower.Sieve.DampedCofactorIntegral
import GaloisForLFunctions.RHTower.Sieve.DampedLocalFactor
import GaloisForLFunctions.RHTower.Sieve.DampedCorrectionMassBudget
import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeReciprocalTail
import GaloisForLFunctions.RHTower.DampedMobiusSumsZeroFree
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusFiniteSmoothSource
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.Sieve.MoebiusDiscRate
import GaloisForLFunctions.RHTower.Sieve.DampedCofactorLowFreqBound
import GaloisForLFunctions.RHTower.PerronPolyExpAbsorb

/-!
# Uniform Ramaré cofactor cancellation through smooth divisors

The prime-count damping is a convolution of the signed Möbius row with a
positive smooth-divisor kernel. The signed prefix estimate pays the small
divisors; a separate fractional moment pays the large divisors.
-/

namespace TwinPrime

open Finset ArithmeticFunction RHTower RHTower.Sieve
open Filter Topology

noncomputable section

/-- Retain the activity `u` on designated primes and activity one elsewhere. -/
def ramarePrimeActivity (P : Finset ℕ) (u : ℝ) (p : ℕ) : ℝ :=
  if p ∈ P then u else 1

/-- The nonnegative divisor kernel whose Möbius convolution gives prime-count damping. -/
def ramareSmoothKernel (P : Finset ℕ) (u : ℝ) : ArithmeticFunction ℝ :=
  DampedMobius.divisorSum (ramarePrimeActivity P u)

private theorem dampedOmegaMoebius_eq_real_dampedMobius {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (u : ℝ) (n : ℕ) :
    dampedOmegaMoebius P u n =
      (DampedMobius.dampedMobius (ramarePrimeActivity P u) n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dampedOmegaMoebius]
  have hset : primeFactorsIn P n = n.primeFactors.filter (· ∈ P) := by
    ext p
    simp only [mem_primeFactorsIn, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨⟨hP p hp, hd, hn⟩, hp⟩
    · rintro ⟨⟨_, hd, _⟩, hp⟩
      exact ⟨hp, hd⟩
  have hprod : (∏ p ∈ n.primeFactors, ramarePrimeActivity P u p) =
      u ^ (primeFactorsIn P n).card := by
    rw [hset, ← Finset.prod_const]
    exact (Finset.prod_filter (s := n.primeFactors) (fun p => p ∈ P) (fun _ => u)).symm
  rw [dampedOmegaMoebius, DampedMobius.dampedMobius, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.prodPrimeFactors_apply hn,
    hprod, Complex.ofReal_mul, Complex.ofReal_intCast]

private theorem ramareSmoothKernel_nonneg {P : Finset ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) : 0 ≤ ramareSmoothKernel P u n := by
  apply DampedMobius.divisorSum_nonneg
  intro p _
  unfold ramarePrimeActivity
  split_ifs
  · rwa [abs_of_nonneg hu0]
  · norm_num

private theorem ramareSmoothKernel_le_one {P : Finset ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) : ramareSmoothKernel P u n ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero]; norm_num
  rw [ramareSmoothKernel, DampedMobius.divisorSum,
    ArithmeticFunction.prodPrimeFactors_apply hn]
  apply Finset.prod_le_one
  · intro p _
    unfold ramarePrimeActivity
    split_ifs <;> linarith
  · intro p _
    unfold ramarePrimeActivity
    split_ifs <;> linarith

/-- Möbius inversion recovers the prime-count damping from the smooth kernel. -/
theorem ramareSmoothKernel_mul_moebius (P : Finset ℕ) (u : ℝ) :
    ramareSmoothKernel P u *
        ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) =
      DampedMobius.dampedMobius (ramarePrimeActivity P u) := by
  rw [ramareSmoothKernel, ← DampedMobius.dampedMobius_mul_zeta,
    mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]

private theorem ramareSmoothKernel_eq_zero_of_not_factoredNumbers
    (P : Finset ℕ) (u : ℝ) {n : ℕ} (hnP : n ∉ Nat.factoredNumbers P) :
    ramareSmoothKernel P u n = 0 := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · exact ArithmeticFunction.map_zero
  by_contra hv
  apply hnP
  refine Nat.mem_factoredNumbers.mpr ⟨hn, fun p hp => ?_⟩
  by_contra hpP
  apply hv
  rw [ramareSmoothKernel, DampedMobius.divisorSum,
    ArithmeticFunction.prodPrimeFactors_apply hn]
  exact Finset.prod_eq_zero (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)
    (by simp only [ramarePrimeActivity, if_neg hpP, sub_self])

private theorem ramareSmoothKernel_sum_moment_le_euler (P s : Finset ℕ) {u σ : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hσ : 0 < σ) :
    (∑ n ∈ s, ramareSmoothKernel P u n * (n : ℝ) ^ (-σ)) ≤
      ∏ p ∈ P with p.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  classical
  have hsub : ∀ n ∈ s.filter (· ∈ Nat.factoredNumbers P), n ∈ Nat.factoredNumbers P :=
    fun n hn => (Finset.mem_filter.mp hn).2
  calc
    (∑ n ∈ s, ramareSmoothKernel P u n * (n : ℝ) ^ (-σ)) ≤
        ∑ n ∈ s.filter (· ∈ Nat.factoredNumbers P), (n : ℝ) ^ (-σ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun n _ => ?_
      by_cases hn : n ∈ Nat.factoredNumbers P
      · rw [if_pos hn]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          (ramareSmoothKernel_le_one hu0 hu1 n)
      · rw [if_neg hn, ramareSmoothKernel_eq_zero_of_not_factoredNumbers P u hn,
          zero_mul]
    _ ≤ ∑' n : Nat.factoredNumbers P, (n : ℝ) ^ (-σ) := by
      rw [← Finset.sum_subtype_of_mem (fun n : ℕ => (n : ℝ) ^ (-σ)) hsub]
      exact sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (summable_pmFactoredNumbers_neg_rpow P hσ).hasSum
    _ = _ := pmFactoredNumbers_tsum_neg_rpow P hσ

private theorem ramare_euler_above_one_le (P : Finset ℕ) {a : ℝ} (ha : 0 < a) :
    (∏ p ∈ P with p.Prime, (1 - (p : ℝ) ^ (-(1 + a)))⁻¹) ≤ 1 + 1 / a := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + a))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  rw [← pmFactoredNumbers_tsum_neg_rpow P (by linarith : 0 < 1 + a)]
  calc
    (∑' n : Nat.factoredNumbers P, (n : ℝ) ^ (-(1 + a))) ≤
        ∑' n : ℕ, (n : ℝ) ^ (-(1 + a)) :=
      (hs.subtype (Nat.factoredNumbers P)).tsum_le_tsum_of_inj Subtype.val
        Subtype.val_injective (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (fun _ => le_rfl) hs
    _ ≤ 1 + 1 / a := by
      simpa only [add_sub_cancel_left] using
        (tsum_nat_rpow_neg_le (show 1 < 1 + a by linarith))

private theorem inv_one_sub_le_exp_four_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3 / 4) :
    (1 - x)⁻¹ ≤ Real.exp (4 * x) := by
  have hpos : 0 < 1 - x := by linarith
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  have he := Real.add_one_le_exp (4 * x)
  nlinarith [mul_le_mul_of_nonneg_right he hpos.le,
    mul_nonneg hx0 (show 0 ≤ 3 - 4 * x by linarith)]

private theorem ramare_shifted_euler_factor_le {p : ℕ} (hp : p.Prime) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) (hcut : Real.log p * a ≤ 1) :
    (1 - (p : ℝ) ^ (-(1 - a)))⁻¹ ≤
      ((1 - (p : ℝ) ^ (-(1 + a)))⁻¹) ^ 36 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let q : ℝ := (p : ℝ) ^ (-(1 - a))
  let r : ℝ := (p : ℝ) ^ (-(1 + a))
  have hq0 : 0 ≤ q := Real.rpow_nonneg hp0.le _
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by linarith)
  have hq2 : q * q ≤ 1 / 2 := by
    calc
      q * q = (p : ℝ) ^ (-(1 - a) + -(1 - a)) := (Real.rpow_add hp0 _ _).symm
      _ ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = 1 / 2 := by norm_num
  have hq34 : q ≤ 3 / 4 := by nlinarith [sq_nonneg (q - 3 / 4)]
  have hexp2 : Real.exp 2 ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hqr : q = Real.exp (2 * (Real.log p * a)) * r := by
    dsimp [q, r]
    rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0, ← Real.exp_add]
    congr 1
    ring
  have hqr9 : q ≤ 9 * r := by
    rw [hqr]
    exact mul_le_mul_of_nonneg_right
      ((Real.exp_le_exp.mpr (by linarith : 2 * (Real.log p * a) ≤ 2)).trans hexp2) hr0
  have hri : Real.exp r ≤ (1 - r)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (show 0 < 1 - r by linarith)]
    calc
      Real.exp r * (1 - r) ≤ Real.exp r * Real.exp (-r) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-r)])
          (Real.exp_pos r).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    (1 - q)⁻¹ ≤ Real.exp (4 * q) := inv_one_sub_le_exp_four_mul hq0 hq34
    _ ≤ Real.exp (36 * r) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp r) ^ 36 := Real.exp_nat_mul r 36
    _ ≤ ((1 - r)⁻¹) ^ 36 := pow_le_pow_left₀ (Real.exp_pos r).le hri _

/-- A moving fractional moment costs only a fixed power of its distance from one. -/
theorem ramareSmoothKernel_moment_le (P s : Finset ℕ) {u a : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ha0 : 0 < a) (ha1 : a ≤ 1 / 2)
    (hcut : ∀ p ∈ P, Real.log p * a ≤ 1) :
    (∑ n ∈ s, ramareSmoothKernel P u n * (n : ℝ) ^ (-(1 - a))) ≤
      (1 + 1 / a) ^ 36 := by
  have hprod0 : 0 ≤ ∏ p ∈ P with p.Prime, (1 - (p : ℝ) ^ (-(1 + a)))⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    apply inv_nonneg.mpr
    have hplt := Real.rpow_lt_one_of_one_lt_of_neg
      (show (1 : ℝ) < p by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt)
      (show -(1 + a) < 0 by linarith)
    linarith
  calc
    (∑ n ∈ s, ramareSmoothKernel P u n * (n : ℝ) ^ (-(1 - a))) ≤
        ∏ p ∈ P with p.Prime, (1 - (p : ℝ) ^ (-(1 - a)))⁻¹ :=
      ramareSmoothKernel_sum_moment_le_euler P s hu0 hu1 (by linarith)
    _ ≤ ∏ p ∈ P with p.Prime, ((1 - (p : ℝ) ^ (-(1 + a)))⁻¹) ^ 36 := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        have hplt := Real.rpow_lt_one_of_one_lt_of_neg
          (show (1 : ℝ) < p by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt)
          (show -(1 - a) < 0 by linarith)
        linarith
      · intro p hp
        exact ramare_shifted_euler_factor_le (Finset.mem_filter.mp hp).2 ha0 ha1
          (hcut p (Finset.mem_filter.mp hp).1)
    _ = (∏ p ∈ P with p.Prime, (1 - (p : ℝ) ^ (-(1 + a)))⁻¹) ^ 36 :=
      Finset.prod_pow _ _ _
    _ ≤ (1 + 1 / a) ^ 36 :=
      pow_le_pow_left₀ hprod0 (ramare_euler_above_one_le P ha0) _

private theorem nat_cpow_mul (d m : ℕ) (z : ℂ) :
    ((d * m : ℕ) : ℂ) ^ z = (d : ℂ) ^ z * (m : ℂ) ^ z := by
  simpa only [Nat.cast_mul, Complex.ofReal_natCast] using
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg m) z

/-- The exact prefix convolution retains the signed inner Möbius sum. -/
theorem ramareSmoothKernel_twisted_prefix {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (u τ X : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        dampedOmegaMoebius P u n * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))) =
      ∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
        (ramareSmoothKernel P u d : ℂ) * (d : ℂ) ^ (-((τ : ℂ) * Complex.I)) *
          ∑ m ∈ Finset.Icc 1 ⌊X / d⌋₊, moebiusTwist τ m := by
  have hcoeff (n : ℕ) :
      dampedOmegaMoebius P u n * (n : ℂ) ^ (-((τ : ℂ) * Complex.I)) =
        ∑ x ∈ n.divisorsAntidiagonal,
          (ramareSmoothKernel P u x.1 : ℂ) *
            (x.1 : ℂ) ^ (-((τ : ℂ) * Complex.I)) * moebiusTwist τ x.2 := by
    rw [dampedOmegaMoebius_eq_real_dampedMobius hP,
      ← ramareSmoothKernel_mul_moebius, ArithmeticFunction.mul_apply,
      Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Complex.ofReal_mul, ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast,
      ← (Nat.mem_divisorsAntidiagonal.mp hx).1, nat_cpow_mul, moebiusTwist]
    ring
  simp_rw [hcoeff]
  rw [sum_Icc_divisorsAntidiagonal_swap (fun d m =>
    (ramareSmoothKernel P u d : ℂ) * (d : ℂ) ^ (-((τ : ℂ) * Complex.I)) *
      moebiusTwist τ m) ⌊X⌋₊]
  simp_rw [← Finset.mul_sum, Nat.floor_div_natCast]

private theorem ramare_twisted_prefix_norm_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (τ X : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        dampedOmegaMoebius P u n * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ ≤
      ∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
        ramareSmoothKernel P u d * ‖∑ m ∈ Finset.Icc 1 ⌊X / d⌋₊, moebiusTwist τ m‖ := by
  rw [ramareSmoothKernel_twisted_prefix hP]
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hphase : ‖(d : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hd0]
    simp
  rw [norm_mul, norm_mul, hphase, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (ramareSmoothKernel_nonneg hu0 hu1 d)]

private theorem moebius_twisted_prefix_trivial (τ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∑ m ∈ Finset.Icc 1 ⌊T⌋₊, moebiusTwist τ m‖ ≤ T := by
  calc
    ‖∑ m ∈ Finset.Icc 1 ⌊T⌋₊, moebiusTwist τ m‖ ≤
        ∑ _m ∈ Finset.Icc 1 ⌊T⌋₊, (1 : ℝ) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => norm_moebiusTwist_le_one τ m)
    _ = (⌊T⌋₊ : ℝ) := by simp
    _ ≤ T := Nat.floor_le hT

private theorem ramare_reciprocal_le_moment {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 1 ≤ d) :
    (1 : ℝ) / d ≤ (d : ℝ) ^ (-(1 - a)) := by
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd) (by linarith)

private theorem ramare_reciprocal_tail_le_moment {a D : ℝ} (ha : 0 ≤ a)
    (hD : 0 < D) {d : ℕ} (hd : D ≤ d) :
    (1 : ℝ) / d ≤ D ^ (-a) * (d : ℝ) ^ (-(1 - a)) := by
  have hd0 : (0 : ℝ) < d := hD.trans_le hd
  calc
    (1 : ℝ) / d = (d : ℝ) ^ (-a) * (d : ℝ) ^ (-(1 - a)) := by
      rw [← Real.rpow_add hd0, show -a + -(1 - a) = (-1 : ℝ) by ring,
        Real.rpow_neg_one, one_div]
    _ ≤ D ^ (-a) * (d : ℝ) ^ (-(1 - a)) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hD hd (by linarith))
        (Real.rpow_nonneg hd0.le _)

/-- Two independent scales: signed cancellation above `H`, smooth-divisor tails below it. -/
theorem exists_ramare_damped_prefix_bound :
    ∃ K T₀ : ℝ, 0 < K ∧ 1 < T₀ ∧
      ∀ (X H a u τ : ℝ) (P : Finset ℕ),
        0 < X → T₀ ≤ H → 0 < a → a ≤ 1 / 2 → 0 ≤ u → u ≤ 1 →
        (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Real.log p * a ≤ 1) → |τ| ≤ H →
        ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          dampedOmegaMoebius P u n * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ ≤
          X * (1 + 1 / a) ^ 36 *
            (K * Real.exp (-((Real.log H) ^ ((1 : ℝ) / 20))) + (X / H) ^ (-a)) := by
  obtain ⟨K, hK, hprefix⟩ := exists_norm_sum_moebiusTwist_le_rate
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hprefix
  refine ⟨K, max T 2, hK, by simp, ?_⟩
  intro X H a u τ P hX hH ha0 ha1 hu0 hu1 hP hcut hτ
  have hH2 : 2 ≤ H := (le_max_right T 2).trans hH
  have hH0 : 0 < H := by linarith
  have hTH : T ≤ H := (le_max_left T 2).trans hH
  let E : ℝ := Real.exp (-((Real.log H) ^ ((1 : ℝ) / 20)))
  let D : ℝ := X / H
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hD : 0 < D := div_pos hX hH0
  have hDa : 0 ≤ D ^ (-a) := Real.rpow_nonneg hD.le _
  have hconstant : 0 ≤ X * (K * E + D ^ (-a)) := by positivity
  have hpoint : ∀ d ∈ Finset.Icc 1 ⌊X⌋₊,
      ramareSmoothKernel P u d * ‖∑ m ∈ Finset.Icc 1 ⌊X / d⌋₊, moebiusTwist τ m‖ ≤
        X * (K * E + D ^ (-a)) *
          (ramareSmoothKernel P u d * (d : ℝ) ^ (-(1 - a))) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
    have hkernel : 0 ≤ ramareSmoothKernel P u d := ramareSmoothKernel_nonneg hu0 hu1 d
    have hweight : 0 ≤ ramareSmoothKernel P u d * (d : ℝ) ^ (-(1 - a)) := by positivity
    by_cases hdD : (d : ℝ) ≤ D
    · have hHT : H ≤ X / d := by
        apply (le_div_iff₀ hd0).mpr
        have hh := (le_div_iff₀ hH0).mp hdD
        nlinarith only [hh]
      have hbound := hT (X / d) (hTH.trans hHT) τ (hτ.trans hHT)
      rw [sum_range_moebiusTwist_eq_Icc] at hbound
      have hexp : Real.exp (-((Real.log (X / d)) ^ ((1 : ℝ) / 20))) ≤ E := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (Real.rpow_le_rpow
          (Real.log_nonneg (by linarith)) (Real.log_le_log hH0 hHT) (by norm_num))
      have hbound' : ‖∑ m ∈ Finset.Icc 1 ⌊X / d⌋₊, moebiusTwist τ m‖ ≤
          K * (X / d) * E :=
        hbound.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
      have hrec := mul_le_mul_of_nonneg_left (ramare_reciprocal_le_moment ha0.le hd1) hkernel
      calc
        ramareSmoothKernel P u d * ‖∑ m ∈ Finset.Icc 1 ⌊X / d⌋₊, moebiusTwist τ m‖ ≤
            ramareSmoothKernel P u d * (K * (X / d) * E) :=
          mul_le_mul_of_nonneg_left hbound' hkernel
        _ = X * (K * E) * (ramareSmoothKernel P u d * (1 / d)) := by ring
        _ ≤ X * (K * E) * (ramareSmoothKernel P u d * (d : ℝ) ^ (-(1 - a))) :=
          mul_le_mul_of_nonneg_left hrec (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hDa) hX.le) hweight
    · have hbound := moebius_twisted_prefix_trivial τ (div_nonneg hX.le hd0.le)
      have hrec := mul_le_mul_of_nonneg_left
        (ramare_reciprocal_tail_le_moment ha0.le hD (le_of_not_ge hdD)) hkernel
      calc
        ramareSmoothKernel P u d * ‖∑ m ∈ Finset.Icc 1 ⌊X / d⌋₊, moebiusTwist τ m‖ ≤
            ramareSmoothKernel P u d * (X / d) :=
          mul_le_mul_of_nonneg_left hbound hkernel
        _ = X * (ramareSmoothKernel P u d * (1 / d)) := by ring
        _ ≤ X * (ramareSmoothKernel P u d * (D ^ (-a) * (d : ℝ) ^ (-(1 - a)))) :=
          mul_le_mul_of_nonneg_left hrec hX.le
        _ = X * D ^ (-a) * (ramareSmoothKernel P u d * (d : ℝ) ^ (-(1 - a))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hK.le hE)) hX.le)
          hweight
  calc
    ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        dampedOmegaMoebius P u n * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ ≤
        ∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
          ramareSmoothKernel P u d * ‖∑ m ∈ Finset.Icc 1 ⌊X / d⌋₊, moebiusTwist τ m‖ :=
      ramare_twisted_prefix_norm_le hP hu0 hu1 τ X
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
        X * (K * E + D ^ (-a)) * (ramareSmoothKernel P u d * (d : ℝ) ^ (-(1 - a))) :=
      Finset.sum_le_sum hpoint
    _ = X * (K * E + D ^ (-a)) *
        ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, ramareSmoothKernel P u d * (d : ℝ) ^ (-(1 - a)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ X * (K * E + D ^ (-a)) * (1 + 1 / a) ^ 36 :=
      mul_le_mul_of_nonneg_left
        (ramareSmoothKernel_moment_le P _ hu0 hu1 ha0 ha1 hcut) hconstant
    _ = _ := by dsimp [E, D]; ring

/-- Averaging the proved uniform damping estimate gives the actual Ramaré cofactor bound. -/
theorem exists_ramare_cofactor_prefix_bound :
    ∃ K T₀ : ℝ, 0 < K ∧ 1 < T₀ ∧
      ∀ (X H a w : ℝ) (P : Finset ℕ),
        0 < X → T₀ ≤ H → 0 < a → a ≤ 1 / 2 →
        (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Real.log p * a ≤ 1) →
        |2 * Real.pi * w| ≤ H →
        ‖logPoly (ramareCofactorCoeff P) (Finset.Icc 1 ⌊X⌋₊) w‖ ≤
          X * (1 + 1 / a) ^ 36 *
            (K * Real.exp (-((Real.log H) ^ ((1 : ℝ) / 20))) + (X / H) ^ (-a)) := by
  obtain ⟨K, T₀, hK, hT₀, hbound⟩ := exists_ramare_damped_prefix_bound
  refine ⟨K, T₀, hK, hT₀, ?_⟩
  intro X H a w P hX hH ha0 ha1 hP hcut hw
  apply norm_logPoly_ramareCofactorCoeff_le_of_uniform
  intro u hu
  rw [logPoly_dampedOmegaMoebius_eq_sum_dampedTwist]
  exact hbound X H a u (-(2 * Real.pi * w)) P hX hH ha0 ha1 hu.1 hu.2 hP hcut
    (by rwa [abs_neg])

private theorem exists_ramare_polynomial_absorption {β ρ b : ℝ}
    (hβ : β ≤ 1) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (1 + L ^ β) ^ 36 * Real.exp (-(b * L ^ ρ)) ≤
        C * Real.exp (-((b / 2) * L ^ ρ)) := by
  let N : ℕ := ⌈(36 : ℝ) / ρ⌉₊
  let C : ℝ := 2 ^ 36 * (N.factorial : ℝ) * (2 / b) ^ N
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro L hL
  have hL0 : 0 < L := by linarith
  have hN : (36 : ℝ) / ρ ≤ N := Nat.le_ceil _
  have hdegree : (36 : ℝ) ≤ ρ * N := by
    have hh := (div_le_iff₀ hρ).mp hN
    nlinarith only [hh]
  have hβL : L ^ β ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL hβ
  have hpoly : (1 + L ^ β) ^ 36 ≤ 2 ^ 36 * (L ^ ρ) ^ N := by
    calc
      (1 + L ^ β) ^ 36 ≤ (2 * L) ^ 36 :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 2 ^ 36 * L ^ 36 := mul_pow _ _ _
      _ ≤ 2 ^ 36 * (L ^ ρ) ^ N := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          L ^ 36 = L ^ (36 : ℝ) := (Real.rpow_natCast L 36).symm
          _ ≤ L ^ (ρ * N) := Real.rpow_le_rpow_of_exponent_le hL hdegree
          _ = (L ^ ρ) ^ N := Real.rpow_mul_natCast hL0.le ρ N
  calc
    (1 + L ^ β) ^ 36 * Real.exp (-(b * L ^ ρ)) ≤
        (2 ^ 36 * (L ^ ρ) ^ N) * Real.exp (-(b * L ^ ρ)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = 2 ^ 36 * ((L ^ ρ) ^ N * Real.exp (-(b * L ^ ρ))) := by ring
    _ ≤ 2 ^ 36 * ((N.factorial : ℝ) * (2 / b) ^ N *
        Real.exp (-(b * L ^ ρ / 2))) :=
      mul_le_mul_of_nonneg_left
        (pow_mul_exp_neg_le_absorb_half hb (Real.rpow_nonneg hL0.le _) N) (by positivity)
    _ = C * Real.exp (-((b / 2) * L ^ ρ)) := by
      dsimp [C]
      rw [show -(b * L ^ ρ / 2) = -((b / 2) * L ^ ρ) by ring]
      ring

/-- Subpolynomial prime cutoffs retain a uniform stretched-exponential cofactor saving. -/
theorem exists_ramare_cofactor_logPoly_rate {β κ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (P : Finset ℕ) (w : ℝ),
        (∀ p ∈ P, p.Prime) →
        (∀ p ∈ P, (p : ℝ) ≤ Real.exp ((Real.log X) ^ β)) →
        |2 * Real.pi * w| ≤ X ^ κ →
        ‖logPoly (ramareCofactorCoeff P) (Finset.Icc 1 ⌊X⌋₊) w‖ ≤
          C * X * Real.exp (-(c * (Real.log X) ^ min ((1 : ℝ) / 20) (1 - β))) := by
  obtain ⟨K, T₀, hK, hT₀, hbound⟩ := exists_ramare_cofactor_prefix_bound
  let ρ : ℝ := min ((1 : ℝ) / 20) (1 - β)
  let b : ℝ := min (κ ^ ((1 : ℝ) / 20)) (1 - κ)
  have hρ : 0 < ρ := lt_min (by norm_num) (by linarith)
  have hb : 0 < b := lt_min (Real.rpow_pos_of_pos hκ0 _) (by linarith)
  obtain ⟨A, hA, habsorb⟩ := exists_ramare_polynomial_absorption hβ1.le hρ hb
  refine ⟨b / 2, (K + 1) * A, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    (tendsto_rpow_atTop hκ0).eventually_ge_atTop T₀,
    ((tendsto_rpow_atTop hβ0).comp Real.tendsto_log_atTop).eventually_ge_atTop 2]
    with X hX1 hH hprimeScale
  intro P w hP hPcut hw
  have hX : 0 < X := (Real.exp_pos 1).trans_le hX1
  let L : ℝ := Real.log X
  have hL1 : 1 ≤ L := (Real.le_log_iff_exp_le hX).mpr hX1
  have hL : 0 < L := by linarith
  have hLβ : 0 < L ^ β := Real.rpow_pos_of_pos hL _
  let a : ℝ := (L ^ β)⁻¹
  have ha0 : 0 < a := inv_pos.mpr hLβ
  have ha1 : a ≤ 1 / 2 := by
    change (L ^ β)⁻¹ ≤ 1 / 2
    rw [inv_eq_one_div, div_le_div_iff₀ hLβ (by norm_num)]
    simpa only [one_mul] using hprimeScale
  have hcut : ∀ p ∈ P, Real.log p * a ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hlog : Real.log p ≤ L ^ β := by
      simpa only [Real.log_exp] using Real.log_le_log hp0 (hPcut p hp)
    calc
      Real.log p * a ≤ L ^ β * a := mul_le_mul_of_nonneg_right hlog ha0.le
      _ = 1 := mul_inv_cancel₀ hLβ.ne'
  have hH0 : 0 < X ^ κ := Real.rpow_pos_of_pos hX _
  have hlogH : Real.log (X ^ κ) = κ * L := by
    rw [Real.rpow_def_of_pos hX, Real.log_exp]
    dsimp [L]
    ring
  have hratio : L * a = L ^ (1 - β) := by
    rw [Real.rpow_sub hL, Real.rpow_one]
    simp only [a, div_eq_mul_inv]
  have htail : (X / X ^ κ) ^ (-a) = Real.exp (-((1 - κ) * L ^ (1 - β))) := by
    rw [Real.rpow_def_of_pos (div_pos hX hH0), Real.log_div hX.ne' hH0.ne', hlogH]
    calc
      Real.exp ((Real.log X - κ * L) * -a) = Real.exp (-((1 - κ) * (L * a))) := by
        congr 1
        change (L - κ * L) * -a = -((1 - κ) * (L * a))
        ring
      _ = _ := by rw [hratio]
  have hhead : Real.exp (-((κ * L) ^ ((1 : ℝ) / 20))) ≤
      Real.exp (-(b * L ^ ρ)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [Real.mul_rpow hκ0.le hL.le]
    exact mul_le_mul (min_le_left _ _)
      (Real.rpow_le_rpow_of_exponent_le hL1 (min_le_left _ _))
      (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hκ0.le _)
  have htail' : Real.exp (-((1 - κ) * L ^ (1 - β))) ≤
      Real.exp (-(b * L ^ ρ)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact mul_le_mul (min_le_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hL1 (min_le_right _ _))
      (Real.rpow_nonneg hL.le _) (by linarith)
  have hbracket :
      K * Real.exp (-((κ * L) ^ ((1 : ℝ) / 20))) +
          Real.exp (-((1 - κ) * L ^ (1 - β))) ≤
        (K + 1) * Real.exp (-(b * L ^ ρ)) := by
    calc
      _ ≤ K * Real.exp (-(b * L ^ ρ)) + Real.exp (-(b * L ^ ρ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hhead hK.le) htail'
      _ = _ := by ring
  have hfinite := hbound X (X ^ κ) a w P hX hH ha0 ha1 hP hcut hw
  have hpoly : (1 + 1 / a) ^ 36 = (1 + L ^ β) ^ 36 := by simp only [a, one_div, inv_inv]
  rw [hlogH, htail, hpoly] at hfinite
  calc
    ‖logPoly (ramareCofactorCoeff P) (Finset.Icc 1 ⌊X⌋₊) w‖ ≤
        X * (1 + L ^ β) ^ 36 *
          (K * Real.exp (-((κ * L) ^ ((1 : ℝ) / 20))) +
            Real.exp (-((1 - κ) * L ^ (1 - β)))) := hfinite
    _ ≤ X * (1 + L ^ β) ^ 36 * ((K + 1) * Real.exp (-(b * L ^ ρ))) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = X * (K + 1) * ((1 + L ^ β) ^ 36 * Real.exp (-(b * L ^ ρ))) := by ring
    _ ≤ X * (K + 1) * (A * Real.exp (-((b / 2) * L ^ ρ))) :=
      mul_le_mul_of_nonneg_left (habsorb L hL1) (by positivity)
    _ = _ := by dsimp [L, ρ]; ring

/-- The literal reciprocal factor-count Möbius sum, uniformly in its moving prime set. -/
theorem exists_ramare_cofactor_twisted_prefix_rate {β κ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (P : Finset ℕ) (τ : ℝ),
        (∀ p ∈ P, p.Prime) →
        (∀ p ∈ P, (p : ℝ) ≤ Real.exp ((Real.log X) ^ β)) → |τ| ≤ X ^ κ →
        ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ramareCofactorCoeff P n * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ ≤
          C * X * Real.exp (-(c * (Real.log X) ^ min ((1 : ℝ) / 20) (1 - β))) := by
  obtain ⟨c, C, hc, hC, hrate⟩ := exists_ramare_cofactor_logPoly_rate hβ0 hβ1 hκ0 hκ1
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hrate] with X hX
  intro P τ hP hPcut hτ
  have hfreq : 2 * Real.pi * (-τ / (2 * Real.pi)) = -τ := by
    field_simp [Real.pi_ne_zero]
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
      ramareCofactorCoeff P n * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))) =
      logPoly (ramareCofactorCoeff P) (Finset.Icc 1 ⌊X⌋₊) (-τ / (2 * Real.pi)) := by
    rw [logPoly]
    refine Finset.sum_congr rfl fun n hn => ?_
    change _ = ramareCofactorCoeff P n * unitLogPhase (-τ / (2 * Real.pi)) n
    rw [unitLogPhase_eq_cpow (Finset.mem_Icc.mp hn).1, hfreq,
      Complex.ofReal_neg, neg_mul]
  rw [hsum]
  exact hX P (-τ / (2 * Real.pi)) hP hPcut (by rwa [hfreq, abs_neg])

end

end TwinPrime

#print axioms TwinPrime.ramareSmoothKernel_moment_le
#print axioms TwinPrime.ramareSmoothKernel_twisted_prefix
#print axioms TwinPrime.exists_ramare_damped_prefix_bound
#print axioms TwinPrime.exists_ramare_cofactor_prefix_bound
#print axioms TwinPrime.exists_ramare_cofactor_logPoly_rate
#print axioms TwinPrime.exists_ramare_cofactor_twisted_prefix_rate
