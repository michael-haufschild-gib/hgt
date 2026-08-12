import GaloisForLFunctions.RHTower.DeningerGammaSixShellPrincipalIdeal
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixTameReaderTransgression

/-!
# Moment-neutral Gamma-six index amplification

The Gamma-six Green carrier has shell `m` of rank `5 * 6^m` and critical trace mass exactly
`5`.  This module deforms that same carrier by the two coefficient-faithful horizontal shell
weights already forced by exceptional reflection.  On every complete shell the two masses are

`5 * 6^(m * delta)` and `5 * 6^(-m * delta)`.

Thus their product remains `25`, while every nonzero horizontal rate makes one orientation grow
geometrically through pairwise disjoint blocks.  This is index amplification without ordinary
tensor amplification: block rank grows exponentially, critical first moment stays fixed, prime
labels remain the ordered Gamma-six pair `(2,3)`, and an `XiZeroCopy` retains divisor
multiplicity.  The maximum of the two masses is subexponential exactly at horizontal rate zero.

The final global equivalence is an RH receiver.  New producer is now precise: derive the
subexponential two-orientation trace bound from the prime/Frobenius source.  No such bound is
assumed or asserted here.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Forward coefficient-faithful horizontal weight on the Gamma-six Green carrier. -/
def sourceHorizontalGammaSixForwardAmplifiedWeight (delta : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (1 - delta)

/-- Reflected coefficient-faithful horizontal weight on the same Gamma-six Green carrier. -/
def sourceHorizontalGammaSixReflectedAmplifiedWeight (delta : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (1 + delta)

/-- First-moment mass of the forward horizontal orientation on one complete Gamma-six shell. -/
def deningerGammaSixForwardShellTraceMass (delta : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ deningerGammaSixShellCoordinates m,
    sourceHorizontalGammaSixForwardAmplifiedWeight delta n

/-- First-moment mass of the reflected horizontal orientation on one complete Gamma-six shell. -/
def deningerGammaSixReflectedShellTraceMass (delta : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ deningerGammaSixShellCoordinates m,
    sourceHorizontalGammaSixReflectedAmplifiedWeight delta n

/-- Two-orientation trace seen before choosing a horizontal sign. -/
def deningerGammaSixTwoOrientationShellTraceMass (delta : ℝ) (m : ℕ) : ℝ :=
  max (deningerGammaSixForwardShellTraceMass delta m)
    (deningerGammaSixReflectedShellTraceMass delta m)

/-- Root-free subexponential trace condition for the two retained orientations. -/
def DeningerGammaSixTwoOrientationTraceSubexponential (delta : ℝ) : Prop :=
  ∀ r : ℝ, 1 < r →
    Tendsto
      (fun m : ℕ => deningerGammaSixTwoOrientationShellTraceMass delta m / r ^ m)
      atTop (nhds 0)

/-- Exact forward shell mass.  Multiplicity `5 * 6^m` cancels the critical factor `6^(-m)`
and leaves only horizontal amplification. -/
theorem deningerGammaSixForwardShellTraceMass_eq
    {m : ℕ} (hm : 3 ≤ m) (delta : ℝ) :
    deningerGammaSixForwardShellTraceMass delta m =
      5 * (6 : ℝ) ^ ((m : ℝ) * delta) := by
  rw [deningerGammaSixForwardShellTraceMass]
  calc
    ∑ n ∈ deningerGammaSixShellCoordinates m,
        sourceHorizontalGammaSixForwardAmplifiedWeight delta n =
        ∑ _n ∈ deningerGammaSixShellCoordinates m,
          ((1 / 6 : ℝ) ^ m) ^ (1 - delta) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sourceHorizontalGammaSixForwardAmplifiedWeight,
        deningerGammaSixShellEigenvalue_eq_on_shell hm hn]
    _ = ((deningerGammaSixShellCoordinates m).card : ℝ) *
          ((1 / 6 : ℝ) ^ m) ^ (1 - delta) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = 5 * (6 : ℝ) ^ m * ((1 / 6 : ℝ) ^ m) ^ (1 - delta) := by
      rw [deningerGammaSixShellCoordinates_card hm]
      push_cast
      ring
    _ = 5 * (6 : ℝ) ^ ((m : ℝ) * delta) := by
      rw [← Real.rpow_natCast (6 : ℝ) m,
        ← Real.rpow_natCast (1 / 6 : ℝ) m,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
      rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 6),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6),
        mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
      congr 1
      ring_nf

/-- Exact reflected shell mass, reciprocal to the forward mass around critical trace `5`. -/
theorem deningerGammaSixReflectedShellTraceMass_eq
    {m : ℕ} (hm : 3 ≤ m) (delta : ℝ) :
    deningerGammaSixReflectedShellTraceMass delta m =
      5 * (6 : ℝ) ^ (-(m : ℝ) * delta) := by
  rw [deningerGammaSixReflectedShellTraceMass]
  calc
    ∑ n ∈ deningerGammaSixShellCoordinates m,
        sourceHorizontalGammaSixReflectedAmplifiedWeight delta n =
        ∑ _n ∈ deningerGammaSixShellCoordinates m,
          ((1 / 6 : ℝ) ^ m) ^ (1 + delta) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sourceHorizontalGammaSixReflectedAmplifiedWeight,
        deningerGammaSixShellEigenvalue_eq_on_shell hm hn]
    _ = ((deningerGammaSixShellCoordinates m).card : ℝ) *
          ((1 / 6 : ℝ) ^ m) ^ (1 + delta) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = 5 * (6 : ℝ) ^ m * ((1 / 6 : ℝ) ^ m) ^ (1 + delta) := by
      rw [deningerGammaSixShellCoordinates_card hm]
      push_cast
      ring
    _ = 5 * (6 : ℝ) ^ (-(m : ℝ) * delta) := by
      rw [← Real.rpow_natCast (6 : ℝ) m,
        ← Real.rpow_natCast (1 / 6 : ℝ) m,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
      rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 6),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6),
        mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
      congr 1
      ring_nf

/-- Critical first moment stays exactly five in every exponentially growing block. -/
theorem deningerGammaSixShellTraceMass_momentNeutral
    {m : ℕ} (hm : 3 ≤ m) :
    deningerGammaSixForwardShellTraceMass 0 m = 5 ∧
      deningerGammaSixReflectedShellTraceMass 0 m = 5 := by
  rw [deningerGammaSixForwardShellTraceMass_eq hm,
    deningerGammaSixReflectedShellTraceMass_eq hm]
  norm_num

/-- The two horizontal first moments have constant geometric product. -/
theorem deningerGammaSixShellTraceMass_mul_reflected
    {m : ℕ} (hm : 3 ≤ m) (delta : ℝ) :
    deningerGammaSixForwardShellTraceMass delta m *
        deningerGammaSixReflectedShellTraceMass delta m = 25 := by
  rw [deningerGammaSixForwardShellTraceMass_eq hm,
    deningerGammaSixReflectedShellTraceMass_eq hm]
  rw [show
      (5 * (6 : ℝ) ^ ((m : ℝ) * delta)) *
          (5 * (6 : ℝ) ^ (-(m : ℝ) * delta)) =
        25 * ((6 : ℝ) ^ ((m : ℝ) * delta) *
          (6 : ℝ) ^ (-(m : ℝ) * delta)) by ring,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  norm_num

/-- Equality of the two amplified shell orientations at one complete shell already detects the
critical horizontal rate. -/
theorem deningerGammaSixForwardShellTraceMass_eq_reflected_iff
    {m : ℕ} (hm : 3 ≤ m) (delta : ℝ) :
    deningerGammaSixForwardShellTraceMass delta m =
        deningerGammaSixReflectedShellTraceMass delta m ↔
      delta = 0 := by
  rw [deningerGammaSixForwardShellTraceMass_eq hm,
    deningerGammaSixReflectedShellTraceMass_eq hm]
  constructor
  · intro hmass
    have hpow :
        (6 : ℝ) ^ ((m : ℝ) * delta) =
          (6 : ℝ) ^ (-(m : ℝ) * delta) := by
      linarith
    have hexp : (m : ℝ) * delta = -(m : ℝ) * delta :=
      (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 6)
        (by norm_num : (6 : ℝ) ≠ 1)).mp hpow
    have hmpos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hm)
    nlinarith
  · rintro rfl
    norm_num

/-- Distinct complete shells have disjoint coordinate support.  Hence the construction supplies
arbitrarily many genuinely independent blocks, not repeated tensor copies of one block. -/
theorem deningerGammaSixShellCoordinates_disjoint
    {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k) (hmk : m ≠ k) :
    Disjoint (deningerGammaSixShellCoordinates m)
      (deningerGammaSixShellCoordinates k) := by
  rw [Finset.disjoint_left]
  intro n hnm hnk
  have hdepthm : deningerGammaSixShellDepth n = m := by
    rw [deningerGammaSixShellCoordinates, Finset.mem_Ico] at hnm
    have hloPow := deningerGammaSix_pow_three_le hm
    have hhiPow : 216 ≤ 6 ^ (m + 1) := hloPow.trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m))
    apply deningerGammaSixShellDepth_eq_of_shell
    · omega
    · omega
  have hdepthk : deningerGammaSixShellDepth n = k := by
    rw [deningerGammaSixShellCoordinates, Finset.mem_Ico] at hnk
    have hloPow := deningerGammaSix_pow_three_le hk
    have hhiPow : 216 ≤ 6 ^ (k + 1) := hloPow.trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
    apply deningerGammaSixShellDepth_eq_of_shell
    · omega
    · omega
  exact hmk (hdepthm.symm.trans hdepthk)

/-- Positive horizontal rate makes the forward masses escape through independent shells. -/
theorem tendsto_deningerGammaSixForwardShellTraceMass_atTop
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (deningerGammaSixForwardShellTraceMass delta) atTop atTop := by
  have hbase : (1 : ℝ) < (6 : ℝ) ^ delta :=
    Real.one_lt_rpow (by norm_num) hdelta
  have hpow : Tendsto (fun m : ℕ => ((6 : ℝ) ^ delta) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hbase
  apply (hpow.const_mul_atTop (by norm_num : (0 : ℝ) < 5)).congr'
  filter_upwards [eventually_ge_atTop 3] with m hm
  rw [deningerGammaSixForwardShellTraceMass_eq hm]
  congr 1
  rw [← Real.rpow_natCast ((6 : ℝ) ^ delta) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  congr 1
  ring

/-- Negative horizontal rate makes the reflected masses escape through independent shells. -/
theorem tendsto_deningerGammaSixReflectedShellTraceMass_atTop
    {delta : ℝ} (hdelta : delta < 0) :
    Tendsto (deningerGammaSixReflectedShellTraceMass delta) atTop atTop := by
  have hneg : 0 < -delta := by linarith
  have hbase : (1 : ℝ) < (6 : ℝ) ^ (-delta) :=
    Real.one_lt_rpow (by norm_num) hneg
  have hpow : Tendsto (fun m : ℕ => ((6 : ℝ) ^ (-delta)) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hbase
  apply (hpow.const_mul_atTop (by norm_num : (0 : ℝ) < 5)).congr'
  filter_upwards [eventually_ge_atTop 3] with m hm
  rw [deningerGammaSixReflectedShellTraceMass_eq hm]
  congr 1
  rw [← Real.rpow_natCast ((6 : ℝ) ^ (-delta)) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  congr 1
  ring

/-- **Moment-neutral amplification classification.**  The two-orientation trace is
subexponential exactly at neutral horizontal rate.  Off-center proof tests the supposedly
subexponential bound at the source-forced geometric base itself. -/
theorem deningerGammaSixTwoOrientationTraceSubexponential_iff
    (delta : ℝ) :
    DeningerGammaSixTwoOrientationTraceSubexponential delta ↔ delta = 0 := by
  constructor
  · intro hsub
    by_contra hdelta
    rcases lt_or_gt_of_ne hdelta with hneg | hpos
    · let a : ℝ := (6 : ℝ) ^ (-delta)
      have ha : 1 < a :=
        Real.one_lt_rpow (by norm_num) (by linarith)
      have hlim := hsub a ha
      have hevent : ∀ᶠ m : ℕ in atTop,
          deningerGammaSixTwoOrientationShellTraceMass delta m / a ^ m < 5 :=
        (tendsto_order.1 hlim).2 5 (by norm_num)
      have hlower : ∀ᶠ m : ℕ in atTop,
          5 ≤ deningerGammaSixTwoOrientationShellTraceMass delta m / a ^ m := by
        filter_upwards [eventually_ge_atTop 3] with m hm
        have hmass : deningerGammaSixReflectedShellTraceMass delta m = 5 * a ^ m := by
          rw [deningerGammaSixReflectedShellTraceMass_eq hm]
          dsimp [a]
          congr 1
          rw [← Real.rpow_natCast ((6 : ℝ) ^ (-delta)) m,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
          congr 1
          ring
        have hpowpos : 0 < a ^ m := pow_pos (lt_trans zero_lt_one ha) m
        calc
          5 = deningerGammaSixReflectedShellTraceMass delta m / a ^ m := by
            rw [hmass]
            field_simp
          _ ≤ deningerGammaSixTwoOrientationShellTraceMass delta m / a ^ m :=
            div_le_div_of_nonneg_right (le_max_right _ _) hpowpos.le
      obtain ⟨m, hmLower, hmUpper⟩ := (hlower.and hevent).exists
      exact (not_lt_of_ge hmLower) hmUpper
    · let a : ℝ := (6 : ℝ) ^ delta
      have ha : 1 < a := Real.one_lt_rpow (by norm_num) hpos
      have hlim := hsub a ha
      have hevent : ∀ᶠ m : ℕ in atTop,
          deningerGammaSixTwoOrientationShellTraceMass delta m / a ^ m < 5 :=
        (tendsto_order.1 hlim).2 5 (by norm_num)
      have hlower : ∀ᶠ m : ℕ in atTop,
          5 ≤ deningerGammaSixTwoOrientationShellTraceMass delta m / a ^ m := by
        filter_upwards [eventually_ge_atTop 3] with m hm
        have hmass : deningerGammaSixForwardShellTraceMass delta m = 5 * a ^ m := by
          rw [deningerGammaSixForwardShellTraceMass_eq hm]
          dsimp [a]
          congr 1
          rw [← Real.rpow_natCast ((6 : ℝ) ^ delta) m,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
          congr 1
          ring
        have hpowpos : 0 < a ^ m := pow_pos (lt_trans zero_lt_one ha) m
        calc
          5 = deningerGammaSixForwardShellTraceMass delta m / a ^ m := by
            rw [hmass]
            field_simp
          _ ≤ deningerGammaSixTwoOrientationShellTraceMass delta m / a ^ m :=
            div_le_div_of_nonneg_right (le_max_left _ _) hpowpos.le
      obtain ⟨m, hmLower, hmUpper⟩ := (hlower.and hevent).exists
      exact (not_lt_of_ge hmLower) hmUpper
  · rintro rfl r hr
    have hpow : Tendsto (fun m : ℕ => (r ^ m)⁻¹) atTop (nhds 0) :=
      (tendsto_pow_atTop_atTop_of_one_lt hr).inv_tendsto_atTop
    have hscaled : Tendsto (fun m : ℕ => 5 * (r ^ m)⁻¹) atTop (nhds 0) := by
      simpa using hpow.const_mul 5
    apply hscaled.congr'
    filter_upwards [eventually_ge_atTop 3] with m hm
    rw [deningerGammaSixTwoOrientationShellTraceMass,
      deningerGammaSixForwardShellTraceMass_eq hm,
      deningerGammaSixReflectedShellTraceMass_eq hm]
    norm_num [div_eq_mul_inv]

/-! ## Coefficient-faithful hyperbolic block and the Hermitianization wall -/

/-- One coordinate of shell `m`, with both reciprocal orientations retained as ordered
off-diagonal coefficients. -/
def deningerGammaSixCoefficientFaithfulHyperbolicBlock
    (delta : ℝ) (m : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, ((1 / 6 : ℝ) ^ m) ^ (1 - delta);
     ((1 / 6 : ℝ) ^ m) ^ (1 + delta), 0]

/-- Critical Hermitian block obtained after balancing the two orientations. -/
def deningerGammaSixCriticalHyperbolicBlock
    (m : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, (1 / 6 : ℝ) ^ m; (1 / 6 : ℝ) ^ m, 0]

/-- Nonunitary diagonal gauge that balances the two ordered coefficients. -/
def deningerGammaSixHyperbolicBalancingGauge
    (delta : ℝ) (m : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, ((1 / 6 : ℝ) ^ m) ^ delta]

/-- Explicit inverse balancing gauge. -/
def deningerGammaSixHyperbolicBalancingGaugeInv
    (delta : ℝ) (m : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, ((1 / 6 : ℝ) ^ m) ^ (-delta)]

private theorem deningerGammaSixShellBase_pos (m : ℕ) :
    0 < (1 / 6 : ℝ) ^ m := by positivity

/-- Reciprocal coefficient product is exactly the square of the critical shell eigenvalue. -/
theorem deningerGammaSixAmplifiedShellWeights_mul (delta : ℝ) (m : ℕ) :
    (((1 / 6 : ℝ) ^ m) ^ (1 - delta)) *
        (((1 / 6 : ℝ) ^ m) ^ (1 + delta)) =
      ((1 / 6 : ℝ) ^ m) ^ 2 := by
  rw [← Real.rpow_add (deningerGammaSixShellBase_pos m),
    show (1 - delta) + (1 + delta) = (2 : ℝ) by ring,
    Real.rpow_two]

@[simp]
theorem trace_deningerGammaSixCoefficientFaithfulHyperbolicBlock
    (delta : ℝ) (m : ℕ) :
    Matrix.trace (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m) = 0 := by
  simp [deningerGammaSixCoefficientFaithfulHyperbolicBlock, Matrix.trace]

/-- Every coefficient-faithful block has the same square and spectral polynomial as the critical
Hermitian block.  Horizontal rate is invisible to trace moments before metric choice. -/
theorem deningerGammaSixCoefficientFaithfulHyperbolicBlock_sq
    (delta : ℝ) (m : ℕ) :
    deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m *
        deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m =
      (((1 / 6 : ℝ) ^ m) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerGammaSixCoefficientFaithfulHyperbolicBlock,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    rw [mul_comm]
    exact deningerGammaSixAmplifiedShellWeights_mul delta m

/-- Transposition exchanges the two retained horizontal orientations. -/
theorem deningerGammaSixCoefficientFaithfulHyperbolicBlock_transpose
    (delta : ℝ) (m : ℕ) :
    (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m)ᵀ =
      deningerGammaSixCoefficientFaithfulHyperbolicBlock (-delta) m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerGammaSixCoefficientFaithfulHyperbolicBlock]

/-- At every nontrivial shell, coefficient faithfulness and Hermitian symmetry coexist exactly at
neutral horizontal rate. -/
theorem deningerGammaSixCoefficientFaithfulHyperbolicBlock_transpose_eq_iff
    {m : ℕ} (hm : 0 < m) (delta : ℝ) :
    (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m)ᵀ =
        deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m ↔
      delta = 0 := by
  rw [deningerGammaSixCoefficientFaithfulHyperbolicBlock_transpose]
  constructor
  · intro hblock
    have hoffdiag := congrArg
      (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hblock
    simp only [deningerGammaSixCoefficientFaithfulHyperbolicBlock,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hoffdiag
    have hbaseLt : (1 / 6 : ℝ) ^ m < 1 :=
      pow_lt_one₀ (by positivity) (by norm_num) hm
    have hexp : 1 - (-delta) = 1 - delta :=
      (Real.rpow_right_inj (deningerGammaSixShellBase_pos m)
        (ne_of_lt hbaseLt)).mp hoffdiag
    linarith
  · rintro rfl
    norm_num [deningerGammaSixCoefficientFaithfulHyperbolicBlock]

/-- The balancing gauge and its displayed inverse multiply to the identity. -/
theorem deningerGammaSixHyperbolicBalancingGaugeInv_mul
    (delta : ℝ) (m : ℕ) :
    deningerGammaSixHyperbolicBalancingGaugeInv delta m *
        deningerGammaSixHyperbolicBalancingGauge delta m = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerGammaSixHyperbolicBalancingGaugeInv,
      deningerGammaSixHyperbolicBalancingGauge,
      Matrix.mul_apply, Fin.sum_univ_two]
  rw [← Real.rpow_add (deningerGammaSixShellBase_pos m)]
  norm_num

/-- **Hermitianization wall.**  The coefficient-faithful block is diagonally similar to the
critical Hermitian block for every horizontal rate.  The similarity is nonunitary off center;
hence a Hermitian rank--trace consumer either rejects the original block or balances away exactly
the horizontal information it was meant to detect. -/
theorem deningerGammaSixHyperbolicBalancing_similarity
    (delta : ℝ) (m : ℕ) :
    deningerGammaSixHyperbolicBalancingGaugeInv delta m *
        deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m *
          deningerGammaSixHyperbolicBalancingGauge delta m =
      deningerGammaSixCriticalHyperbolicBlock m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerGammaSixHyperbolicBalancingGaugeInv,
      deningerGammaSixCoefficientFaithfulHyperbolicBlock,
      deningerGammaSixHyperbolicBalancingGauge,
      deningerGammaSixCriticalHyperbolicBlock,
      Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← Real.rpow_add (deningerGammaSixShellBase_pos m)]
    congr 1
    ring
  · rw [← Real.rpow_add (deningerGammaSixShellBase_pos m)]
    congr 1
    ring

/-! ## Multiplicity-labelled Xi specialization -/

/-- Two-orientation mass of the retained multiplicity-labelled Xi divisor class. -/
def deningerXiGammaSixTwoOrientationShellTraceMass
    (q : XiZeroCopy) (m : ℕ) : ℝ :=
  deningerGammaSixTwoOrientationShellTraceMass
    (primeDepthBVWoldXiCenteredRate q.1) m

/-- Source-side subexponential target on one retained Xi divisor copy. -/
def DeningerXiGammaSixMomentNeutralTraceSubexponential (q : XiZeroCopy) : Prop :=
  DeningerGammaSixTwoOrientationTraceSubexponential
    (primeDepthBVWoldXiCenteredRate q.1)

/-- The coefficient-faithful trace target for one multiplicity copy is exactly critical-line
placement. -/
theorem deningerXiGammaSixMomentNeutralTraceSubexponential_iff
    (q : XiZeroCopy) :
    DeningerXiGammaSixMomentNeutralTraceSubexponential q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [DeningerXiGammaSixMomentNeutralTraceSubexponential,
    deningerGammaSixTwoOrientationTraceSubexponential_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global prime/Frobenius producer target after moment-neutral index amplification. -/
def DeningerXiGammaSixAllMomentNeutralTracesSubexponential : Prop :=
  ∀ q : XiZeroCopy, DeningerXiGammaSixMomentNeutralTraceSubexponential q

/-- **Frankenstein RH endpoint.**  A source-derived subexponential trace bound on the explicit
ordered `(2,3)` Gamma-six shells for both retained orientations and every Xi multiplicity copy is
equivalent to RH. -/
theorem deningerXiGammaSixAllMomentNeutralTracesSubexponential_iff_riemannHypothesis :
    DeningerXiGammaSixAllMomentNeutralTracesSubexponential ↔ RiemannHypothesis := by
  constructor
  · intro hsub
    have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
      intro q
      exact (deningerXiGammaSixMomentNeutralTraceSubexponential_iff q).1 (hsub q)
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline q]
  · intro hRH q
    apply (deningerXiGammaSixMomentNeutralTraceSubexponential_iff q).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower
