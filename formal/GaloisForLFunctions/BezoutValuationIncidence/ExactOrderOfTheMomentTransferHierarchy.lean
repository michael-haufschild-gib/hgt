import GaloisForLFunctions.BezoutValuationIncidence.QuadraticOrderL1ObservabilityConstant
import GaloisForLFunctions.BezoutValuationIncidence.TranslatedMomentTransferHierarchySharpness

/-!
# The exact order of the moment transfer hierarchy

A degree-`m` transfer constant `S` bounds the window error of every translated moment by
`S Q_Sel^{m/2}` at every phase and length. The quadratic inverse ℓ¹ inequality makes
`(e^{19/4} N)^m` admissible.

Conversely, the row with all Selberg coordinates equal to one has `Q_Sel = Φ(N)`, is bounded by
`Φ(N)` everywhere (each Ramanujan sum is at most `φ(q)` in size), and takes the value `Φ(N)` at the
common return `N!`. Its period moment of degree `m ≥ 2` is at most `Φ(N)^{m-2} Q_Sel = Φ(N)^{m-1}`,
so the one-point window at `N!` forces

`Φ(N)^m - Φ(N)^{m-1} ≤ S Φ(N)^{m/2}`,  hence  `S ≥ Φ(N)^{m/2} / 2`.

With `Φ(N) ≥ N²/8 + N - (N/2) H_N`, the optimal degree-`m` transfer constant has exact order `N^m`:
the observability horizon of the degree-`m` translated statistics is `N^m`, uniformly in `m`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- **Upper bound.** `(e^{19/4} N)^m` is a degree-`m` transfer constant. -/
theorem isTranslatedMomentTransferConstant_exp_mul (N m : ℕ) :
    IsTranslatedMomentTransferConstant N m ((Real.exp (19 / 4) * N) ^ m) := fun c h A K => by
  have h1 := abs_window_translatedMoment_sub_le_exp_mul_sq N c h A K
  have hsq : Real.sqrt (Real.exp (19 / 2) * (N : ℝ) ^ 2) = Real.exp (19 / 4) * N := by
    rw [show Real.exp (19 / 2) = Real.exp (19 / 4) ^ 2 by
      rw [← Real.exp_nat_mul]; norm_num]
    rw [← mul_pow, Real.sqrt_sq (by positivity)]
  rwa [Real.sqrt_mul (by positivity), hsq, mul_pow] at h1

/-! ## The unit Selberg row at the common return -/

theorem selbergMultiplesCoord_unitSelbergRow {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (unitSelbergRow N) q = 1 :=
  RHTower.pmRamanujanResidueCoeff_multiples _ (mem_Icc.mp hq).1 (mem_Icc.mp hq).2

theorem selbergTotientDiagonalForm_unitSelbergRow (N : ℕ) :
    selbergTotientDiagonalForm N (unitSelbergRow N) = cyclotomicIncidenceOrder N := by
  unfold selbergTotientDiagonalForm cyclotomicIncidenceOrder
  push_cast
  exact sum_congr rfl fun q hq => by rw [selbergMultiplesCoord_unitSelbergRow hq]; ring

theorem sieveSeq_unitSelbergRow_factorial (N : ℕ) :
    sieveSeq N (unitSelbergRow N) N.factorial = cyclotomicIncidenceOrder N := by
  rw [sieveSeq_factorial_eq_sum_totient_mul, cyclotomicIncidenceOrder]
  push_cast
  exact sum_congr rfl fun q hq => by rw [selbergMultiplesCoord_unitSelbergRow hq, mul_one]

theorem abs_sieveSeq_unitSelbergRow_le (N k : ℕ) :
    |sieveSeq N (unitSelbergRow N) k| ≤ cyclotomicIncidenceOrder N := by
  rw [SieveMoments.sieveSeq_ramanujan_expansion, cyclotomicIncidenceOrder]
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q hq => ?_)
  rw [selbergMultiplesCoord_unitSelbergRow hq, one_mul]
  exact SieveMoments.abs_ramanujanLagCoefficient_le_totient q k

/-- The period mean square of any row is its Selberg form. -/
theorem sum_Icc_factorial_sieveSeq_sq (N : ℕ) (c : ℕ → ℝ) :
    ∑ k ∈ Icc 1 N.factorial, sieveSeq N c k ^ 2 =
      (N.factorial : ℝ) * selbergTotientDiagonalForm N c := by
  rw [← sievedDivisorPrefixMeanSquare_eq_selberg_of_forall_dvd N N.factorial c
    fun d hd => Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2]
  exact sum_congr rfl fun k hk => by
    rw [sieveSeq_eq_sievedDivisorSum N c (mem_Icc.mp hk).1]

/-! ## The lower bound -/

/-- **Lower bound.** Every degree-`m` transfer constant, `m ≥ 2`, is at least `Φ(N)^{m/2}/2`. -/
theorem sqrt_cyclotomicIncidenceOrder_pow_div_two_le {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m)
    {S : ℝ} (hS : IsTranslatedMomentTransferConstant N m S) :
    Real.sqrt (cyclotomicIncidenceOrder N : ℝ) ^ m / 2 ≤ S := by
  set c := unitSelbergRow N
  set Φ : ℝ := (cyclotomicIncidenceOrder N : ℝ) with hΦdef
  have hΦ2 : (2 : ℝ) ≤ Φ := by
    have h1 := one_lt_cyclotomicIncidenceOrder hN
    have hint : 2 ≤ cyclotomicIncidenceOrder N := by exact_mod_cast h1
    rw [hΦdef]
    exact_mod_cast hint
  have hΦ0 : (0 : ℝ) < Φ := by linarith
  have hQ := selbergTotientDiagonalForm_unitSelbergRow N
  rw [← hΦdef] at hQ
  have hP : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  -- the period moment of degree `m` at zero shifts
  set T := SieveMoments.translatedMoment N c (fun _ : Fin m => 0) with hT
  have hTabs : |T| ≤ Φ ^ (m - 1) := by
    rw [hT, translatedMoment_eq_Icc]
    simp only [add_zero, prod_const, card_univ, Fintype.card_fin]
    rw [abs_div, abs_of_pos hP, div_le_iff₀ hP]
    calc |∑ k ∈ Icc 1 N.factorial, sieveSeq N c k ^ m|
        ≤ ∑ k ∈ Icc 1 N.factorial, Φ ^ (m - 2) * sieveSeq N c k ^ 2 := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
          have hb := abs_sieveSeq_unitSelbergRow_le N k
          rw [← hΦdef] at hb
          rw [abs_pow, show m = (m - 2) + 2 by omega, pow_add, ← sq_abs (sieveSeq N c k)]
          have h1 : |sieveSeq N c k| ^ (m - 2 + 2 - 2) ≤ Φ ^ (m - 2) := by
            rw [show m - 2 + 2 - 2 = m - 2 by omega]
            exact pow_le_pow_left₀ (abs_nonneg _) hb _
          rw [show m - 2 + 2 - 2 = m - 2 by omega] at h1
          exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = Φ ^ (m - 2) * ((N.factorial : ℝ) * Φ) := by
          rw [← mul_sum, sum_Icc_factorial_sieveSeq_sq, hQ]
      _ = Φ ^ (m - 1) * N.factorial := by
          rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
          ring
  -- the one-point window at the common return
  have hwin := hS c (fun _ => 0) (N.factorial - 1) 1
  have hP1 : N.factorial - 1 + 1 = N.factorial := Nat.sub_add_cancel (Nat.factorial_pos N)
  rw [hP1, Icc_self, sum_singleton] at hwin
  simp only [add_zero, prod_const, card_univ, Fintype.card_fin, Nat.cast_one, one_mul] at hwin
  rw [sieveSeq_unitSelbergRow_factorial, ← hΦdef, hQ, ← hT] at hwin
  have hlow : Φ ^ m - Φ ^ (m - 1) ≤ S * Real.sqrt Φ ^ m := by
    have := (abs_le.mp hwin).2
    have := neg_abs_le T
    linarith [le_abs_self T, (abs_le.mp hTabs).2]
  -- `Φ^m - Φ^{m-1} ≥ Φ^m / 2` and `Φ^m = √Φ^m · √Φ^m`
  have hsq : Φ ^ m = Real.sqrt Φ ^ m * Real.sqrt Φ ^ m := by
    rw [← mul_pow, Real.mul_self_sqrt hΦ0.le]
  have hhalf : Φ ^ m / 2 ≤ Φ ^ m - Φ ^ (m - 1) := by
    have : Φ ^ m = Φ ^ (m - 1) * Φ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hpos : 0 ≤ Φ ^ (m - 1) := by positivity
    nlinarith
  have hs0 : 0 < Real.sqrt Φ ^ m := pow_pos (Real.sqrt_pos.mpr hΦ0) m
  have key : Real.sqrt Φ ^ m * (Real.sqrt Φ ^ m / 2) ≤ Real.sqrt Φ ^ m * S := by
    calc Real.sqrt Φ ^ m * (Real.sqrt Φ ^ m / 2) = Φ ^ m / 2 := by rw [hsq]; ring
      _ ≤ S * Real.sqrt Φ ^ m := hhalf.trans hlow
      _ = Real.sqrt Φ ^ m * S := by ring
  exact le_of_mul_le_mul_left key hs0

/-- **The degree-`m` transfer constant has exact order `N^m`.** -/
theorem translatedMomentTransferConstant_exact_order {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m) :
    IsTranslatedMomentTransferConstant N m ((Real.exp (19 / 4) * N) ^ m) ∧
      ∀ S : ℝ, IsTranslatedMomentTransferConstant N m S →
        Real.sqrt ((N : ℝ) ^ 2 / 8 + N - (N : ℝ) / 2 * (harmonic N : ℝ)) ^ m / 2 ≤ S :=
  ⟨isTranslatedMomentTransferConstant_exp_mul N m, fun _ hS => by
    refine le_trans ?_ (sqrt_cyclotomicIncidenceOrder_pow_div_two_le hN hm hS)
    gcongr
    exact cyclotomicIncidenceOrder_ge N⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
