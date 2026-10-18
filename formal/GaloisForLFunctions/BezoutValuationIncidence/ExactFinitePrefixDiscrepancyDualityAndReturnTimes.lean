import GaloisForLFunctions.BezoutValuationIncidence.ExactSuccessorMomentRegionAndUniversalInequalities

/-!
# Exact finite-prefix discrepancy duality and return times

For every natural sieve level `N`, natural prefix `M`, and real weight `c`, the
prefix discrepancy after removing harmonic drift has exact dual coordinates
`L(N,M,c) = Σ_{2≤e≤N} Re(R_e(M)) Y_N(c,e)`, where `R_e` is the existing
Ramanujan primitive and `Y_N` is the truncated multiples transform.

Its squared norm in sieve variance is the explicit arithmetic energy
`A(N,M) = Σ_{2≤e≤N} Re(R_e(M))² / φ(e)`. Thus `L² ≤ V*A`, with a canonical
zero-harmonic weight attaining `V=L=A`. This gives the complete universal
constant classification, including the empty nonconstant levels `N≤1`.

The energy vanishes exactly when every positive denominator at most `N`
divides `M`. The proof combines the existing finite Möbius inverse and
Ramanujan primitive identity with weighted Cauchy; it asserts no asymptotic
cancellation or growth bound for `A`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

/-- The truncated multiples transform respects subtraction. -/
theorem selbergMultiplesCoord_sub (N e : ℕ) (c b : ℕ → ℝ) :
    selbergMultiplesCoord N (fun d => c d - b d) e =
      selbergMultiplesCoord N c e - selbergMultiplesCoord N b e := by
  simp only [selbergMultiplesCoord, sub_div, Finset.sum_sub_distrib]

/-- The existing finite inverse also recovers every original coefficient within the level. -/
theorem ramanujan_inverse_selbergCoords_eq (N : ℕ) (c : ℕ → ℝ)
    (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    pmRamanujanResidueCoeff (selbergMultiplesCoord N c) N d = c d := by
  let b := pmRamanujanResidueCoeff (selbergMultiplesCoord N c) N
  have hz : ∀ e ∈ Finset.Icc 1 N,
      selbergMultiplesCoord N (fun j => b j - c j) e = 0 := by
    intro e he
    rw [selbergMultiplesCoord_sub]
    dsimp only [b]
    rw [selbergMultiplesCoord_ramanujan_inverse, if_pos he, sub_self]
  have hc := (selbergMultiplesCoord_tail_zero_iff N 0 (fun j => b j - c j)).mp hz
  exact sub_eq_zero.mp (hc d hd)

/-- The fractional-part defect is the existing normalized residue combination. -/
theorem sievedFractSum_eq_residueCombination (N M : ℕ) (c : ℕ → ℝ) :
    sievedFractSum N c M =
      DeletionPeriodCovariance.residueCombination (Finset.Icc 1 N) c M := by
  unfold sievedFractSum DeletionPeriodCovariance.residueCombination fractDivSeq
  apply Finset.sum_congr rfl
  intro d hd
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  ring

/-- The actual finite-prefix discrepancy after removing its harmonic drift. -/
def sievePrefixDiscrepancy (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  finiteFloorSum N c (M : ℝ) - (M : ℝ) * finiteHarmonicSum N c

/-- The discrepancy is exactly the signed fractional-part defect, at every level. -/
theorem sievePrefixDiscrepancy_eq_neg_sievedFractSum (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M c = -sievedFractSum N c M := by
  unfold sievePrefixDiscrepancy
  rw [finiteFloorSum_nat_eq_selbergOne_sub_sievedFractSum,
    selbergMultiplesCoord_one_eq_finiteHarmonicSum]
  ring

/-- The same discrepancy written as a literal prefix of the sieved divisor sequence. -/
theorem sievePrefixDiscrepancy_eq_sum_sub_drift (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M c =
      (∑ k ∈ Finset.Icc 1 M, sievedDivisorSum N c k) -
        (M : ℝ) * finiteHarmonicSum N c := by
  unfold sievePrefixDiscrepancy
  rw [finiteFloorSum_nat_eq_sum_sievedDivisorSum]

private theorem prefix_mode_one (M : ℕ) :
    (pmRamanujanPrimitive 1 M).re = (M : ℝ) := by
  rw [pmRamanujanPrimitive_eq_floor]
  simp

/-- Exact dual-coordinate representation of every finite-prefix discrepancy. -/
theorem sievePrefixDiscrepancy_eq_ramanujan_diagonal (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M c =
      ∑ e ∈ Finset.Icc 2 N,
        (pmRamanujanPrimitive e M).re * selbergMultiplesCoord N c e := by
  cases N with
  | zero => simp [sievePrefixDiscrepancy_eq_neg_sievedFractSum, sievedFractSum]
  | succ N =>
    have hc : sievedFractSum (N + 1)
        (pmRamanujanResidueCoeff (selbergMultiplesCoord (N + 1) c) (N + 1)) M =
          sievedFractSum (N + 1) c M := by
      unfold sievedFractSum
      apply Finset.sum_congr rfl
      intro d hd
      rw [ramanujan_inverse_selbergCoords_eq (N + 1) c d hd]
    have h := pmRamanujan_sum_primitive_eq_residue
      (selbergMultiplesCoord (N + 1) c) (by omega : 1 ≤ N + 1) M
    rw [← sievedFractSum_eq_residueCombination, hc] at h
    have hI : Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) := by
      ext e
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp), prefix_mode_one] at h
    rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum]
    calc
      _ = ∑ e ∈ Finset.Icc 2 (N + 1),
          selbergMultiplesCoord (N + 1) c e * (pmRamanujanPrimitive e M).re := by linarith
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        ring

/-- Variance of an arbitrary prescribed finite coordinate profile. -/
theorem sieveVariance_ramanujan_inverse (N : ℕ) (y : ℕ → ℝ) :
    sieveVariance N (pmRamanujanResidueCoeff y N) =
      ∑ e ∈ Finset.Icc 2 N, (Nat.totient e : ℝ) * (y e)^2 := by
  unfold sieveVariance
  apply Finset.sum_congr rfl
  intro e he
  have heI : e ∈ Finset.Icc 1 N := by
    obtain ⟨he2, heN⟩ := Finset.mem_Icc.mp he
    exact Finset.mem_Icc.mpr ⟨by omega, heN⟩
  rw [selbergMultiplesCoord_ramanujan_inverse, if_pos heI]

/-- Exact variance dual energy of a fixed finite prefix. -/
def sievePrefixDualEnergy (N M : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 2 N, (pmRamanujanPrimitive e M).re^2 / (Nat.totient e : ℝ)

/-- The dual energy is nonnegative, including empty levels. -/
theorem sievePrefixDualEnergy_nonneg (N M : ℕ) : 0 ≤ sievePrefixDualEnergy N M :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

private theorem prefix_totient_pos {N e : ℕ} (he : e ∈ Finset.Icc 2 N) :
    0 < (Nat.totient e : ℝ) := by
  have he2 := (Finset.mem_Icc.mp he).1
  exact_mod_cast Nat.totient_pos.mpr (show 0 < e from by omega)

/-- The sharp discrepancy bound holds for every real sieve weight, without a mean-zero premise. -/
theorem sievePrefixDiscrepancy_sq_le_variance_mul_dualEnergy
    (N M : ℕ) (c : ℕ → ℝ) :
    (sievePrefixDiscrepancy N M c)^2 ≤ sieveVariance N c * sievePrefixDualEnergy N M := by
  rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal]
  unfold sieveVariance sievePrefixDualEnergy
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro e he
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  · intro e he
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  · intro e he
    have hp := (prefix_totient_pos he).ne'
    have h : ((pmRamanujanPrimitive e M).re * selbergMultiplesCoord N c e)^2 =
        ((Nat.totient e : ℝ) * (selbergMultiplesCoord N c e)^2) *
          ((pmRamanujanPrimitive e M).re^2 / (Nat.totient e : ℝ)) := by
      field_simp [hp]
    exact h.le

/-- A canonical attaining weight, with zero harmonic coordinate. -/
def sievePrefixExtremizer (N M : ℕ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff
    (fun e => if e = 1 then 0 else (pmRamanujanPrimitive e M).re / (Nat.totient e : ℝ)) N

/-- The exact dual energy is attained simultaneously as variance and discrepancy. -/
theorem sievePrefixExtremizer_attains_dualEnergy (N M : ℕ) :
    finiteHarmonicSum N (sievePrefixExtremizer N M) = 0 ∧
      sieveVariance N (sievePrefixExtremizer N M) = sievePrefixDualEnergy N M ∧
      sievePrefixDiscrepancy N M (sievePrefixExtremizer N M) = sievePrefixDualEnergy N M := by
  constructor
  · rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    unfold sievePrefixExtremizer
    rw [selbergMultiplesCoord_ramanujan_inverse]
    simp
  constructor
  · unfold sievePrefixExtremizer sievePrefixDualEnergy
    rw [sieveVariance_ramanujan_inverse]
    apply Finset.sum_congr rfl
    intro e he
    have he1 : e ≠ 1 := by have := (Finset.mem_Icc.mp he).1; omega
    rw [if_neg he1]
    have hp := (prefix_totient_pos he).ne'
    field_simp [hp]
  · rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal]
    unfold sievePrefixExtremizer sievePrefixDualEnergy
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨he2, heN⟩ := Finset.mem_Icc.mp he
    have heI : e ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, heN⟩
    have he1 : e ≠ 1 := by omega
    rw [selbergMultiplesCoord_ramanujan_inverse, if_pos heI, if_neg he1]
    ring

private theorem prefix_low_level_forms {N : ℕ} (hN : N ≤ 1) (M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M c = 0 ∧ sieveVariance N c = 0 := by
  constructor
  · rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal]
    apply Finset.sum_eq_zero
    intro e he
    have := Finset.mem_Icc.mp he
    omega
  · unfold sieveVariance
    apply Finset.sum_eq_zero
    intro e he
    have := Finset.mem_Icc.mp he
    omega

private theorem prefix_exists_variance_one {N : ℕ} (hN : 2 ≤ N) :
    ∃ c : ℕ → ℝ, sieveVariance N c = 1 := by
  refine ⟨pmRamanujanResidueCoeff (fun e => if e = 2 then 1 else 0) N, ?_⟩
  rw [sieveVariance_ramanujan_inverse]
  calc
    _ = ∑ e ∈ Finset.Icc 2 N, if e = 2 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : e = 2
      · subst e
        simp [Nat.totient_two]
      · simp [h]
    _ = 1 := by simp [hN]

/-- Complete best-constant classification, with the degenerate levels stated explicitly. -/
theorem universal_sievePrefixDiscrepancy_constant_iff (N M : ℕ) (K : ℝ) :
    (∀ c : ℕ → ℝ,
      (sievePrefixDiscrepancy N M c)^2 ≤ K * sieveVariance N c) ↔
        N ≤ 1 ∨ sievePrefixDualEnergy N M ≤ K := by
  constructor
  · intro h
    by_cases hN : N ≤ 1
    · exact Or.inl hN
    right
    have ha := sievePrefixDualEnergy_nonneg N M
    have ht := h (sievePrefixExtremizer N M)
    obtain ⟨_, hv, hl⟩ := sievePrefixExtremizer_attains_dualEnergy N M
    rw [hv, hl] at ht
    by_cases hz : sievePrefixDualEnergy N M = 0
    · obtain ⟨c, hc⟩ := prefix_exists_variance_one (by omega : 2 ≤ N)
      have htest := h c
      rw [hc] at htest
      rw [hz]
      nlinarith [sq_nonneg (sievePrefixDiscrepancy N M c)]
    · have hp : 0 < sievePrefixDualEnergy N M := by
        by_contra hle
        exact hz (le_antisymm (le_of_not_gt hle) ha)
      by_contra hk
      have hprod := mul_pos hp (sub_pos.mpr (lt_of_not_ge hk))
      nlinarith
  · intro h c
    rcases h with hN | hK
    · obtain ⟨hl, hv⟩ := prefix_low_level_forms hN M c
      rw [hl, hv]
      simp
    · have hv : 0 ≤ sieveVariance N c :=
        Finset.sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      have h := sievePrefixDiscrepancy_sq_le_variance_mul_dualEnergy N M c
      have hmul := mul_le_mul_of_nonneg_left hK hv
      nlinarith

/-- Zero dual energy characterizes precisely the common divisibility return times. -/
theorem sievePrefixDualEnergy_eq_zero_iff_common_return (N M : ℕ) :
    sievePrefixDualEnergy N M = 0 ↔ ∀ d ∈ Finset.Icc 1 N, d ∣ M := by
  constructor
  · intro hA d hd
    let c : ℕ → ℝ := fun k => if k = d then 1 else 0
    have hb := sievePrefixDiscrepancy_sq_le_variance_mul_dualEnergy N M c
    rw [hA, mul_zero] at hb
    have hl : sievePrefixDiscrepancy N M c = 0 :=
      sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _))
    rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum] at hl
    have hs : sievedFractSum N c M = fractDivSeq d M := by
      simp [sievedFractSum, c, ite_mul, hd]
    rw [hs] at hl
    have hf : fractDivSeq d M = 0 := neg_eq_zero.mp hl
    unfold fractDivSeq at hf
    rw [Int.fract_div_natCast_eq_div_natCast_mod] at hf
    have hdpos : 0 < (d : ℝ) := by
      exact_mod_cast (show 0 < d from by have := (Finset.mem_Icc.mp hd).1; omega)
    have hm : ((M % d : ℕ) : ℝ) = 0 :=
      (div_eq_zero_iff.mp hf).resolve_right (ne_of_gt hdpos)
    exact Nat.dvd_of_mod_eq_zero (by exact_mod_cast hm)
  · intro hperiod
    have hL : ∀ c : ℕ → ℝ, sievePrefixDiscrepancy N M c = 0 := by
      intro c
      rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum]
      have hs : sievedFractSum N c M = 0 := by
        unfold sievedFractSum
        apply Finset.sum_eq_zero
        intro d hd
        unfold fractDivSeq
        rw [Int.fract_div_natCast_eq_div_natCast_mod, Nat.mod_eq_zero_of_dvd (hperiod d hd)]
        simp
      rw [hs]
      simp
    have h := (sievePrefixExtremizer_attains_dualEnergy N M).2.2
    rw [hL] at h
    exact h.symm

end
end GaloisForLFunctions.BezoutValuationIncidence
