import GaloisForLFunctions.RHTower.ArithmeticFiniteSourceContour
import GaloisForLFunctions.RHTower.FiniteDirichletConvolutionOverflow

/-!
# Raw finite Möbius recovery does not glue at zeta zeros

The literal finite arithmetic continuation decays quadratically at every nontrivial zeta zero,
whereas the raw finite Möbius Dirichlet head has an unconditional linear norm bound.  The same
obstruction survives every fixed logarithmic jet and every fixed finite linear packet of those
jets.  Their products therefore tend to zero, so their formation/recovery gluing defects tend to
`-1`, not zero.

This closes the naive recovery candidate without any assumption about zero location.  Any recovery
process intended to approach reciprocal zeta at its zeros must contain genuinely cofinal data
beyond any fixed finite-order logarithmic enrichment of the raw Möbius head.
-/

noncomputable section

open Complex Filter Set
open scoped Topology BigOperators

namespace RHTower.DeletionMixedRefinement

/-- The `k`-th logarithmic jet of the finite Möbius recovery head. -/
def finiteMobiusRecoveryLogJet (k N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℂ) *
      (Real.log (n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-s)

/-- Raw finite Möbius recovery head. -/
def finiteMobiusRecoveryHead (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)

/-- The raw recovery head is the zeroth logarithmic jet. -/
@[simp] theorem finiteMobiusRecoveryLogJet_zero (N : ℕ) (s : ℂ) :
    finiteMobiusRecoveryLogJet 0 N s = finiteMobiusRecoveryHead N s := by
  simp [finiteMobiusRecoveryLogJet, finiteMobiusRecoveryHead]

/-- The raw Möbius head is exactly the finite Dirichlet head of the coerced Möbius coefficient
family. -/
theorem finiteMobiusRecoveryHead_eq_finiteDirichletHead (N : ℕ) (s : ℂ) :
    finiteMobiusRecoveryHead N s =
      finiteDirichletHead
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
          ArithmeticFunction ℂ) N s := by
  rw [finiteDirichletHead_eq_sum_mul_cpow]
  rfl

/-- Difference between literal finite continuation and its constant-coefficient Dirichlet head. -/
def finiteCutoffContinuationCorrection (N : ℕ) (s : ℂ) : ℂ :=
  finiteCutoffZeta N s -
    finiteDirichletHead
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
        ArithmeticFunction ℂ) N s

/-- Exact split of the finite formation/recovery failure into Dirichlet overflow and the
continuation-correction interaction.  The cutoff indicator makes the identity unconditional at
the empty cutoff. -/
theorem finiteCutoffZeta_mul_finiteMobiusRecoveryHead_boundary_split
    (N : ℕ) (s : ℂ) :
    finiteCutoffZeta N s * finiteMobiusRecoveryHead N s -
        (if 1 ≤ N then 1 else 0) =
      finiteDirichletOverflow
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
            ArithmeticFunction ℂ)
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℂ) N s +
        finiteCutoffContinuationCorrection N s * finiteMobiusRecoveryHead N s := by
  rw [finiteMobiusRecoveryHead_eq_finiteDirichletHead,
    finiteCutoffContinuationCorrection]
  have h := finiteMobiusHead_mul_zetaHead N s
  linear_combination h

/-- At a nontrivial zero, a fixed logarithmic Möbius jet grows at most by its elementary
term-counting majorant. -/
theorem norm_finiteMobiusRecoveryLogJet_le
    (rho : RiemannGaussian.NontrivialZetaZero) (k N : ℕ) :
    ‖finiteMobiusRecoveryLogJet k N rho.1‖ ≤
      N * Real.log (N : ℝ) ^ k := by
  by_cases hN : N = 0
  · simp [finiteMobiusRecoveryLogJet, hN]
  rw [finiteMobiusRecoveryLogJet]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ‖(ArithmeticFunction.moebius n : ℂ) *
          (Real.log (n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-rho.1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log (N : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
      have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
      have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log hnpos (by exact_mod_cast hnN)
      have hlogPow : Real.log (n : ℝ) ^ k ≤ Real.log (N : ℝ) ^ k :=
        pow_le_pow_left₀ hlog0 hlog k
      have hpow : (n : ℝ) ^ (-rho.1.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast hn1)
          (neg_nonpos.mpr
            (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho).le)
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hlog0,
        Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      have hab : ‖(ArithmeticFunction.moebius n : ℂ)‖ * Real.log (n : ℝ) ^ k ≤
          1 * Real.log (N : ℝ) ^ k :=
        mul_le_mul hmu hlogPow (pow_nonneg hlog0 k) zero_le_one
      calc
        ‖(ArithmeticFunction.moebius n : ℂ)‖ * Real.log (n : ℝ) ^ k *
            (n : ℝ) ^ (-rho.1.re)
            ≤ (1 * Real.log (N : ℝ) ^ k) * 1 :=
          mul_le_mul hab hpow (Real.rpow_nonneg (Nat.cast_nonneg n) _)
            (mul_nonneg zero_le_one (pow_nonneg hlogN0 k))
        _ = Real.log (N : ℝ) ^ k := by ring
    _ = N * Real.log (N : ℝ) ^ k := by simp

/-- At a nontrivial zero, the raw finite Möbius head grows at most linearly. -/
theorem norm_finiteMobiusRecoveryHead_le
    (rho : RiemannGaussian.NontrivialZetaZero) (N : ℕ) :
    ‖finiteMobiusRecoveryHead N rho.1‖ ≤ N := by
  simpa using norm_finiteMobiusRecoveryLogJet_le rho 0 N

/-- Literal finite continuation times any fixed logarithmic Möbius jet tends to zero at every
nontrivial zeta zero. -/
theorem tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryLogJet_at_zero
    (rho : RiemannGaussian.NontrivialZetaZero) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      finiteCutoffZeta N rho.1 * finiteMobiusRecoveryLogJet k N rho.1)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ := (‖rho.1‖ + 1) ^ 2 / 15
  have hlog : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ k / (N : ℝ)) atTop (nhds 0) := by
    have hbase :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
        tendsto_natCast_atTop_atTop
    refine hbase.congr' (Eventually.of_forall fun N => ?_)
    simp
  have hmajor : Tendsto (fun N : ℕ =>
      C * (Real.log (N : ℝ) ^ k / (N : ℝ))) atTop (nhds 0) := by
    simpa using hlog.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖rho.1‖))]
      with N hN hNrho
  rw [norm_mul]
  have hF := norm_finiteCutoffZeta_sub_zeta_le hN
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) rho.2.2.2
    (le_refl ‖rho.1‖) hNrho
  rw [rho.2.1, sub_zero] at hF
  have hR := norm_finiteMobiusRecoveryLogJet_le rho k N
  calc
    ‖finiteCutoffZeta N rho.1‖ * ‖finiteMobiusRecoveryLogJet k N rho.1‖
        ≤ ((‖rho.1‖ + 1) ^ 2 / (15 * (N : ℝ) ^ 2)) *
            (N * Real.log (N : ℝ) ^ k) :=
      mul_le_mul hF hR (norm_nonneg _)
        (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _)))
    _ = C * (Real.log (N : ℝ) ^ k / (N : ℝ)) := by
      dsimp [C]
      field_simp

/-- At every nontrivial zeta zero, literal finite continuation times raw finite Möbius recovery
tends to zero, not one. -/
theorem tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryHead_at_zero
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N : ℕ => finiteCutoffZeta N rho.1 * finiteMobiusRecoveryHead N rho.1)
      atTop (nhds 0) := by
  simpa using tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryLogJet_at_zero rho 0

/-- Consequently the raw formation/recovery gluing defect tends to `-1`. -/
theorem tendsto_finiteMobiusRecoveryGluingDefect_at_zero
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      finiteCutoffZeta N rho.1 * finiteMobiusRecoveryHead N rho.1 - 1)
      atTop (nhds (-1)) := by
  simpa using
    (tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryHead_at_zero rho).sub
      tendsto_const_nhds

/-- At every nontrivial zero, the combined overflow/correction boundary failure tends to `-1`.
This identifies the raw gluing obstruction with two separately sourced finite laws. -/
theorem tendsto_finiteMobiusBoundaryFailureTotal_at_zero
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      finiteDirichletOverflow
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
            ArithmeticFunction ℂ)
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℂ) N rho.1 +
        finiteCutoffContinuationCorrection N rho.1 *
          finiteMobiusRecoveryHead N rho.1) atTop (nhds (-1)) := by
  apply tendsto_finiteMobiusRecoveryGluingDefect_at_zero rho |>.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  simpa [hN] using
    finiteCutoffZeta_mul_finiteMobiusRecoveryHead_boundary_split N rho.1

/-- Consequently every fixed logarithmic-jet gluing defect tends to `-1`. -/
theorem tendsto_finiteMobiusRecoveryLogJetGluingDefect_at_zero
    (rho : RiemannGaussian.NontrivialZetaZero) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      finiteCutoffZeta N rho.1 * finiteMobiusRecoveryLogJet k N rho.1 - 1)
      atTop (nhds (-1)) := by
  simpa using
    (tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryLogJet_at_zero rho k).sub
      tendsto_const_nhds

/-- A fixed finite linear packet of logarithmic Möbius jets. -/
def finiteMobiusRecoveryJetPacket (K : ℕ) (a : Fin (K + 1) → ℂ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k : Fin (K + 1), a k * finiteMobiusRecoveryLogJet k N s

/-- Literal finite continuation times any fixed finite logarithmic-jet packet tends to zero at
every nontrivial zeta zero. -/
theorem tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryJetPacket_at_zero
    (rho : RiemannGaussian.NontrivialZetaZero) (K : ℕ)
    (a : Fin (K + 1) → ℂ) :
    Tendsto (fun N : ℕ =>
      finiteCutoffZeta N rho.1 * finiteMobiusRecoveryJetPacket K a N rho.1)
      atTop (nhds 0) := by
  have hsum : Tendsto (fun N : ℕ =>
      ∑ k : Fin (K + 1),
        a k * (finiteCutoffZeta N rho.1 *
          finiteMobiusRecoveryLogJet k N rho.1)) atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ fun (k : Fin (K + 1)) _ =>
      tendsto_const_nhds.mul
        (tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryLogJet_at_zero rho k)
  simpa [finiteMobiusRecoveryJetPacket, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using hsum

/-- Consequently every fixed finite logarithmic-jet-packet gluing defect tends to `-1`. -/
theorem tendsto_finiteMobiusRecoveryJetPacketGluingDefect_at_zero
    (rho : RiemannGaussian.NontrivialZetaZero) (K : ℕ)
    (a : Fin (K + 1) → ℂ) :
    Tendsto (fun N : ℕ =>
      finiteCutoffZeta N rho.1 * finiteMobiusRecoveryJetPacket K a N rho.1 - 1)
      atTop (nhds (-1)) := by
  simpa using
    (tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryJetPacket_at_zero rho K a).sub
      tendsto_const_nhds

end RHTower.DeletionMixedRefinement
