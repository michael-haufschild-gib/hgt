import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeCoprimeLogExpansion
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusLimit
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Total mass of the smooth-prime reciprocal semigroup

The reciprocal coefficient supported on primes dividing a positive modulus is summable.  Dominated
convergence in the exact coprime-log expansion then identifies its total mass at every squarefree
modulus with the expected Euler ratio `r / φ(r)`.  This reuses the corpus's proved fixed-modulus
limit and avoids duplicating a separate finite totient-product calculation.
-/

namespace RHTower.Sieve

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

theorem primeSupportedReciprocal_nonneg (r n : ℕ) :
    0 ≤ primeSupportedReciprocal r n := by
  classical
  simp only [primeSupportedReciprocal, ArithmeticFunction.coe_mk]
  split_ifs
  · simp [reciprocalNatArithmetic]
    positivity
  · positivity

@[simp] theorem primeSupportedReciprocal_zero (r : ℕ) :
    primeSupportedReciprocal r 0 = 0 := by
  classical
  simp [primeSupportedReciprocal, reciprocalNatArithmetic]

theorem primeSupportedReciprocal_eq_zero_of_not_mem_smoothNumbers
    {r n : ℕ} (hr : 0 < r) (h : n ∉ (r + 1).smoothNumbers) :
    primeSupportedReciprocal r n = 0 := by
  apply primeSupportedReciprocal_apply_of_not_supported
  exact fun hs => h (primeSupportedOn_mem_smoothNumbers hr hs)

theorem summable_primeSupportedReciprocal_prime_pow
    {r p : ℕ} (hp : p.Prime) :
    Summable (fun i : ℕ => primeSupportedReciprocal r (p ^ i)) := by
  by_cases hpr : p ∣ r
  · have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hpR1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hpR : ‖(1 / (p : ℝ))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpR0)]
      exact (div_lt_one hpR0).2 hpR1
    apply (summable_geometric_of_norm_lt_one hpR).congr
    intro i
    rw [primeSupportedReciprocal_prime_pow hp, if_pos (Or.inr hpr)]
    push_cast
    simp only [one_div, inv_pow]
  · have htail : Summable (fun i : ℕ =>
        primeSupportedReciprocal r (p ^ (i + 1))) := by
      exact summable_zero.congr (fun i => by
        rw [primeSupportedReciprocal_prime_pow hp,
          if_neg (not_or_intro (by omega) hpr)])
    exact (summable_nat_add_iff 1).mp (by simpa only [Nat.add_comm] using htail)

theorem summable_primeSupportedReciprocal {r : ℕ} (hr : 0 < r) :
    Summable (fun n : ℕ => primeSupportedReciprocal r n) := by
  let S : Set ℕ := {n | n ∈ (r + 1).smoothNumbers}
  have heuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := fun n : ℕ => primeSupportedReciprocal r n)
    (primeSupportedReciprocal_one r)
    (fun {_ _} h =>
      (isMultiplicative_primeSupportedReciprocal r).map_mul_of_coprime h)
    (fun {p} hp => by
      exact (summable_primeSupportedReciprocal_prime_pow (r := r) hp).congr
        (fun i => by rw [Real.norm_eq_abs,
          abs_of_nonneg (primeSupportedReciprocal_nonneg r (p ^ i))]))
    (r + 1)
  have hind : HasSum
      (S.indicator (fun n : ℕ => primeSupportedReciprocal r n))
      (∏ p ∈ (r + 1).primesBelow,
        ∑' i : ℕ, primeSupportedReciprocal r (p ^ i)) :=
    (hasSum_subtype_iff_indicator (s := S)
      (f := fun n : ℕ => primeSupportedReciprocal r n)).mp heuler.2
  have hfun : S.indicator (fun n : ℕ => primeSupportedReciprocal r n) =
      fun n : ℕ => primeSupportedReciprocal r n := by
    funext n
    by_cases hn : n ∈ (r + 1).smoothNumbers
    · simp [S, hn]
    · simp [S, hn, primeSupportedReciprocal_eq_zero_of_not_mem_smoothNumbers hr hn]
  rw [hfun] at hind
  exact hind.summable

theorem summable_abs_primeSupportedReciprocal {r : ℕ} (hr : 0 < r) :
    Summable (fun n : ℕ => |primeSupportedReciprocal r n|) := by
  apply (summable_primeSupportedReciprocal hr).congr
  intro n
  rw [abs_of_nonneg (primeSupportedReciprocal_nonneg r n)]

private def primeSupportedCoprimeLogTerm (r N d : ℕ) : ℝ :=
  if d ∈ Finset.Icc 1 N then
    primeSupportedReciprocal r d *
      coprimeLogMoebius 1 ((N : ℝ) / (d : ℝ))
  else 0

private theorem tsum_primeSupportedCoprimeLogTerm_eq (r N : ℕ) :
    (∑' d : ℕ, primeSupportedCoprimeLogTerm r N d) =
      coprimeLogMoebius r (N : ℝ) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · rw [coprimeLogMoebius_eq_sum_primeSupportedReciprocal, Nat.floor_natCast]
    apply Finset.sum_congr rfl
    intro d hd
    rw [primeSupportedCoprimeLogTerm, if_pos hd]
  · intro d hd
    rw [primeSupportedCoprimeLogTerm, if_neg hd]

private theorem tendsto_primeSupportedCoprimeLogTerm
    (r d : ℕ) :
    Tendsto (fun N : ℕ => primeSupportedCoprimeLogTerm r N d) atTop
      (𝓝 (primeSupportedReciprocal r d)) := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simp [primeSupportedCoprimeLogTerm]
  · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hscaleR : Tendsto (fun Y : ℝ => Y / (d : ℝ)) atTop atTop := by
      have hinv : 0 < (d : ℝ)⁻¹ := by positivity
      simpa [div_eq_mul_inv] using
        (tendsto_mul_const_atTop_of_pos hinv).mpr
          (tendsto_id : Tendsto id atTop atTop)
    have hscale : Tendsto (fun N : ℕ => (N : ℝ) / (d : ℝ)) atTop atTop :=
      hscaleR.comp tendsto_natCast_atTop_atTop
    have hkernel : Tendsto
        (fun N : ℕ => coprimeLogMoebius 1 ((N : ℝ) / (d : ℝ))) atTop (𝓝 1) :=
      tendsto_coprimeLogMoebius_one.comp hscale
    have hmul := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => primeSupportedReciprocal r d) atTop
        (𝓝 (primeSupportedReciprocal r d))).mul hkernel
    have hmul' : Tendsto
        (fun N : ℕ => primeSupportedReciprocal r d *
          coprimeLogMoebius 1 ((N : ℝ) / (d : ℝ))) atTop
        (𝓝 (primeSupportedReciprocal r d)) := by
      simpa only [mul_one] using hmul
    apply hmul'.congr'
    filter_upwards [eventually_ge_atTop d] with N hN
    rw [primeSupportedCoprimeLogTerm, if_pos (Finset.mem_Icc.mpr ⟨hd, hN⟩)]

theorem tendsto_coprimeLogMoebius_nat_primeSupportedMass
    {r : ℕ} (hr : 0 < r) :
    Tendsto (fun N : ℕ => coprimeLogMoebius r (N : ℝ)) atTop
      (𝓝 (∑' d : ℕ, primeSupportedReciprocal r d)) := by
  let C : ℝ := coprimeLogMoebiusConst
  have hC : 0 ≤ C := coprimeLogMoebiusConst_nonneg
  have hdomSummable : Summable (fun d : ℕ =>
      C * primeSupportedReciprocal r d) :=
    (summable_primeSupportedReciprocal hr).mul_left C
  have hdom : ∀ N d : ℕ,
      ‖primeSupportedCoprimeLogTerm r N d‖ ≤
        C * primeSupportedReciprocal r d := by
    intro N d
    rw [primeSupportedCoprimeLogTerm]
    split_ifs with hdN
    · rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (primeSupportedReciprocal_nonneg r d)]
      have hk := abs_coprimeLogMoebius_le 1 (by simp)
        ((N : ℝ) / (d : ℝ))
      have hkC : |coprimeLogMoebius 1 ((N : ℝ) / (d : ℝ))| ≤ C := by
        simpa only [Nat.cast_one, Nat.totient_one, div_one, mul_one, C] using hk
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hkC
        (primeSupportedReciprocal_nonneg r d)
    · simp
      exact mul_nonneg hC (primeSupportedReciprocal_nonneg r d)
  have ht := tendsto_tsum_of_dominated_convergence hdomSummable
    (tendsto_primeSupportedCoprimeLogTerm r)
    (Filter.Eventually.of_forall hdom)
  refine ht.congr' ?_
  filter_upwards [] with N
  rw [tsum_primeSupportedCoprimeLogTerm_eq]

/-- Exact total reciprocal mass of the smooth prime semigroup at squarefree modulus. -/
theorem tsum_primeSupportedReciprocal_eq_totientRatio
    {r : ℕ} (hr : Squarefree r) :
    (∑' d : ℕ, primeSupportedReciprocal r d) =
      (r : ℝ) / (Nat.totient r : ℝ) := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  have hsmooth := tendsto_coprimeLogMoebius_nat_primeSupportedMass hrpos
  have htotient := (tendsto_coprimeLogMoebius_squarefree r hr).comp
    tendsto_natCast_atTop_atTop
  exact tendsto_nhds_unique hsmooth htotient

end

end RHTower.Sieve
