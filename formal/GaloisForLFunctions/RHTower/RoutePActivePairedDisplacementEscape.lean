import GaloisForLFunctions.RHTower.RoutePCompensatedMassRiccati
import GaloisForLFunctions.RHTower.RoutePOneSidedChebyshevOscillation
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarRelativeDisplacement
import GaloisForLFunctions.RHTower.CCMQuantileDisplacementMass

/-!
# Unbounded actual critical-mass and paired-cell displacement

The exact Abel primitive transfers any bounded critical-mass discrepancy to a
forbidden one-sided square-root Chebyshev bound. The mass staircase then transfers
this obstruction to active prime-power nodes: bounded jumps and monotone square
roots suffice. The actual matched-to-quantile displacement differs from the mass
discrepancy by a uniformly bounded local correction, so it too escapes every fixed
absolute bound on every active tail. No RH premise or prime-gap estimate is used.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators
open GaloisForLFunctions.RHTower
namespace RHTower
noncomputable section


theorem routeP_criticalMass_absolute_escape (B L : ℝ) :
    ∃ x : ℝ, L ≤ x ∧ B < |primeMassHalf x - 2 * Real.sqrt x| := by
  by_contra! h
  let A : ℝ := max L 1
  have hA : 1 ≤ A := le_max_right _ _
  have hbound (x : ℝ) (hx : A ≤ x) :
      -B ≤ primeMassHalf x - 2 * Real.sqrt x ∧
        primeMassHalf x - 2 * Real.sqrt x ≤ B :=
    abs_le.mp (h x ((le_max_left _ _).trans hx))
  let d : ℝ := routePAbelMassPrimitive A - A - B * Real.sqrt A
  have hF (x : ℝ) (hx : A ≤ x) :
      routePAbelMassPrimitive x ≤ x + B * Real.sqrt x + d := by
    apply image_le_of_deriv_right_le_deriv_boundary (a := A) (b := x)
      continuous_routePAbelMassPrimitive.continuousOn
      (fun y hy => routePAbelMassPrimitive_rightDerivative (hA.trans hy.1))
      (B' := fun y => 1 + B * (1 / (2 * Real.sqrt y)))
    · dsimp [d]; linarith
    · intro y hy
      fun_prop
    · intro y hy
      exact ((hasDerivAt_id y).add
        ((Real.hasDerivAt_sqrt (ne_of_gt (zero_lt_one.trans_le (hA.trans hy.1)))).const_mul B)).add_const d
        |>.hasDerivWithinAt
    · intro y hy
      have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr
        (zero_lt_one.trans_le (hA.trans hy.1))
      have hb := (hbound y hy.1).2
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt y)).mpr
      field_simp
      nlinarith
    · exact ⟨hx, le_rfl⟩
  obtain ⟨N, hN, hN3, hneg⟩ := ccmFuPsiRemainder_negative_escape
    (2 * B + |d| + 1) ⌈A⌉₊
  have hAN : A ≤ (N : ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast hN)
  have hn1 : 1 ≤ (N : ℝ) := hA.trans hAN
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hn1
  have hlo := (hbound N hAN).1
  have hmul := mul_le_mul_of_nonneg_left hlo (Real.sqrt_nonneg (N : ℝ))
  have hf := hF N hAN
  rw [routePAbelMassPrimitive_eq hn1] at hf
  have hs2 := Real.sq_sqrt (zero_le_one.trans hn1)
  have hd := mul_le_mul_of_nonneg_left hs1 (abs_nonneg d)
  rw [psiRemainder, chebyshevPsi_eq_psi] at hneg
  nlinarith [le_abs_self d]

theorem routeP_primeMass_nat_succ (n : ℕ) :
    primeMassHalf ((n + 1 : ℕ) : ℝ) =
      primeMassHalf (n : ℝ) + criticalMellinAtomWeight (n + 1) := by
  simp only [primeMassHalf, Nat.floor_natCast, criticalMellinAtomWeight_eq_div_sqrt]
  rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ n + 1)]

theorem routeP_activeMass_bound_transfer {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, IsPrimePow n → |primeMassHalf (n : ℝ) - 2 * Real.sqrt n| ≤ C) :
    ∀ n : ℕ, |primeMassHalf (n : ℝ) - 2 * Real.sqrt n| ≤ C + 2 := by
  have hwzero {n : ℕ} (hn : ¬IsPrimePow n) : criticalMellinAtomWeight n = 0 := by
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]
  have hupper (n : ℕ) : primeMassHalf (n : ℝ) ≤ 2 * Real.sqrt n + C := by
    induction n with
    | zero => simpa [primeMassHalf] using hC
    | succ n ih =>
      by_cases hn : IsPrimePow (n + 1)
      · have h := (abs_le.mp (hbound (n + 1) hn)).2
        linarith
      · rw [routeP_primeMass_nat_succ, hwzero hn, add_zero]
        have hs := Real.sqrt_le_sqrt (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by push_cast; linarith)
        linarith
  have hlower (n : ℕ) : 2 * Real.sqrt n - (C + 2) ≤ primeMassHalf (n : ℝ) := by
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
    apply Nat.decreasingInduction' (n := p) (m := n) (P := fun k =>
      2 * Real.sqrt k - (C + 2) ≤ primeMassHalf (k : ℝ)) ?_ hnp ?_
    · intro k hkp hnk ih
      have hs := Real.sqrt_le_sqrt (show (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by push_cast; linarith)
      by_cases hk : IsPrimePow (k + 1)
      · have hb := (abs_le.mp (hbound (k + 1) hk)).1
        have hw := criticalMellinAtomWeight_le_two_of_pos (Nat.succ_pos k)
        rw [routeP_primeMass_nat_succ] at hb
        linarith
      · rw [routeP_primeMass_nat_succ, hwzero hk, add_zero] at ih
        linarith
    · have hb := (abs_le.mp (hbound p hp.isPrimePow)).1
      linarith
  intro n
  exact abs_le.mpr ⟨by linarith [hlower n], by linarith [hupper n]⟩

theorem routeP_criticalMass_active_absolute_escape (B : ℝ) (L : ℕ) :
    ∃ n : ℕ, L ≤ n ∧ IsPrimePow n ∧
      B < |primeMassHalf (n : ℝ) - 2 * Real.sqrt n| := by
  by_contra! h
  let C : ℝ := |B| + ∑ k ∈ Finset.range L, |primeMassHalf (k : ℝ) - 2 * Real.sqrt k|
  have hsum : 0 ≤ ∑ k ∈ Finset.range L, |primeMassHalf (k : ℝ) - 2 * Real.sqrt k| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC : 0 ≤ C := add_nonneg (abs_nonneg B) hsum
  have hc (n : ℕ) (hn : IsPrimePow n) : |primeMassHalf (n : ℝ) - 2 * Real.sqrt n| ≤ C := by
    by_cases hLn : L ≤ n
    · exact (h n hLn hn).trans (by dsimp [C]; linarith [le_abs_self B])
    · have hs := Finset.single_le_sum (f := fun k : ℕ =>
        |primeMassHalf (k : ℝ) - 2 * Real.sqrt k|)
        (fun k _ => abs_nonneg _) (Finset.mem_range.mpr (lt_of_not_ge hLn))
      dsimp [C]
      linarith [abs_nonneg B]
  have hnat := routeP_activeMass_bound_transfer hC hc
  obtain ⟨x, hx, hbig⟩ := routeP_criticalMass_absolute_escape (C + 4) 1
  let n := ⌊x⌋₊
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hn : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have heq : primeMassHalf x = primeMassHalf (n : ℝ) := by
    simp only [primeMassHalf, Nat.floor_natCast]
    rfl
  have hs := Real.sqrt_le_sqrt hn
  have hx2 := Real.sq_sqrt hx0
  have hn2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hgap : Real.sqrt x - Real.sqrt (n : ℝ) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (n : ℝ), sq_nonneg (Real.sqrt x - Real.sqrt (n : ℝ) - 1)]
  have hb := abs_le.mp (hnat n)
  rw [heq] at hbig
  have hsmall : |primeMassHalf (n : ℝ) - 2 * Real.sqrt x| ≤ C + 4 := by
    apply abs_le.mpr
    constructor <;> linarith
  linarith

theorem routeP_activeDisplacement_absolute_escape (B : ℝ) (L : ℕ) :
    ∃ n : ℕ, L ≤ n ∧ IsPrimePow n ∧
      B < |ccmActualHeadMatchedQuantilePolarDisplacement n| := by
  obtain ⟨n, hnL, hn, hbig⟩ := routeP_criticalMass_active_absolute_escape (|B| + 4) L
  refine ⟨n, hnL, hn, ?_⟩
  have hnpos : 0 < n := hn.pos
  have hcenter := two_exp_log_half_sub_quantile_succ_eq_outgoingNodeError n hnpos
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative,
    ccmOutgoingPrimeCumulative_succ_eq_primeMassHalf] at hcenter
  have hs : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt n := by
    rw [Real.exp_half, Real.exp_log (by exact_mod_cast hnpos)]
  rw [hs] at hcenter
  have hcorr := ccmActualHeadMatchedQuantilePolarDisplacement_mem_errorCorridor n hnpos
  have hw := criticalMellinAtomWeight_le_two_of_pos hnpos
  by_contra! hsmall
  have hb := abs_le.mp hsmall
  have hmass : |primeMassHalf (n : ℝ) - 2 * Real.sqrt n| ≤ |B| + 4 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self B]
  linarith

end
end RHTower
