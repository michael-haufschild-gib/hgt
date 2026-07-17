import GaloisForLFunctions.RHTower.PrimeArchThetaReflectedBudgetTailTransfer

/-!
# Gaussian damping activates the reflected theta-tail budget

The uniform first-atom domination discards the factor measuring the extra Gaussian decay of every
higher theta atom.  Retaining that factor absorbs the reflected half-density weight.  The exact
higher reflected budget is therefore bounded by the old domination weight times the first-atom
mass, which proves that the reflected-budget transfer is the active low-degree interface.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Extra logarithmic damping rate of the `n`th theta atom relative to the first. -/
def thetaCuspSourceAtomDampingRate (n : ℕ) : ℝ :=
  2 * Real.pi * ((n : ℝ) ^ 2 - 1)

/-- Refined first-atom domination retaining the unused Gaussian cusp decay. -/
theorem thetaCuspSourceTerm_le_first_mul_exp_damping
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x n ≤
      (thetaCuspSourceAtomDominationWeight n *
        Real.exp (-thetaCuspSourceAtomDampingRate n * x)) *
          thetaCuspSourceTerm x 1 := by
  let u : ℝ := Real.exp x
  have hu : 1 ≤ u := by
    dsimp [u]
    simpa using Real.exp_le_exp.mpr hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnSq : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have huSq : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
  have huSqDamped : 1 + 2 * x ≤ u ^ 2 := by
    calc
      1 + 2 * x ≤ Real.exp (2 * x) := by
        simpa only [add_comm] using Real.add_one_le_exp (2 * x)
      _ = u ^ 2 := by
        dsimp [u]
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring
  have hprod :
      0 ≤ ((n : ℝ) ^ 2 - 1) * (u ^ 2 - 1 - 2 * x) :=
    mul_nonneg (sub_nonneg.mpr hnSq) (by linarith)
  have hexponent :
      -Real.pi * ((n : ℝ) * u) ^ 2 ≤
        -Real.pi * ((n : ℝ) ^ 2 - 1) +
          (-2 * Real.pi * ((n : ℝ) ^ 2 - 1) * x) +
            (-Real.pi * u ^ 2) := by
    nlinarith [Real.pi_pos]
  have hgauss :
      Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2) ≤
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) *
          (Real.exp (-2 * Real.pi * ((n : ℝ) ^ 2 - 1) * x) *
            Real.exp (-Real.pi * u ^ 2)) := by
    calc
      Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2) ≤
          Real.exp
            (-Real.pi * ((n : ℝ) ^ 2 - 1) +
              (-2 * Real.pi * ((n : ℝ) ^ 2 - 1) * x) +
                (-Real.pi * u ^ 2)) := Real.exp_le_exp.mpr hexponent
      _ = _ := by
        rw [show
          -Real.pi * ((n : ℝ) ^ 2 - 1) +
                (-2 * Real.pi * ((n : ℝ) ^ 2 - 1) * x) +
                  (-Real.pi * u ^ 2) =
              -Real.pi * ((n : ℝ) ^ 2 - 1) +
                ((-2 * Real.pi * ((n : ℝ) ^ 2 - 1) * x) +
                  (-Real.pi * u ^ 2)) by ring,
          Real.exp_add, Real.exp_add]
  have hpoly_u :
      0 ≤ 2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2) := by
    have hcore : 0 ≤ 2 * Real.pi * u ^ 2 - 3 := by
      nlinarith [Real.pi_gt_three]
    rw [show 2 * Real.pi * u ^ 4 - 3 * u ^ 2 =
      u ^ 2 * (2 * Real.pi * u ^ 2 - 3) by ring]
    positivity
  have hpoly_nu :
      0 ≤ 2 * Real.pi *
        (2 * Real.pi * ((n : ℝ) * u) ^ 4 -
          3 * ((n : ℝ) * u) ^ 2) := by
    have hnu : 1 ≤ (n : ℝ) * u := by nlinarith [Real.exp_pos x]
    have hnuSq : 1 ≤ ((n : ℝ) * u) ^ 2 := by nlinarith
    have hcore : 0 ≤ 2 * Real.pi * ((n : ℝ) * u) ^ 2 - 3 := by
      nlinarith [Real.pi_gt_three]
    rw [show 2 * Real.pi * ((n : ℝ) * u) ^ 4 -
        3 * ((n : ℝ) * u) ^ 2 =
      ((n : ℝ) * u) ^ 2 *
        (2 * Real.pi * ((n : ℝ) * u) ^ 2 - 3) by ring]
    positivity
  have hpolyUpper :
      2 * Real.pi *
          (2 * Real.pi * ((n : ℝ) * u) ^ 4 -
            3 * ((n : ℝ) * u) ^ 2) ≤
        2 * (n : ℝ) ^ 4 *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2)) := by
    have hcore : 0 ≤ 2 * Real.pi * u ^ 2 - 6 := by
      nlinarith [Real.pi_gt_three]
    have hbracket :
        0 ≤ (n : ℝ) ^ 2 * (2 * Real.pi * u ^ 2 - 6) + 3 := by
      positivity
    have hid :
        2 * (n : ℝ) ^ 4 *
              (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2)) -
            2 * Real.pi *
              (2 * Real.pi * ((n : ℝ) * u) ^ 4 -
                3 * ((n : ℝ) * u) ^ 2) =
          2 * Real.pi * (n : ℝ) ^ 2 * u ^ 2 *
            ((n : ℝ) ^ 2 * (2 * Real.pi * u ^ 2 - 6) + 3) := by
      ring
    apply sub_nonneg.mp
    rw [hid]
    positivity
  unfold thetaCuspSourceAtomDominationWeight thetaCuspSourceAtomDampingRate
  unfold thetaCuspSourceTerm thetaCuspSeed
  simp only [Nat.cast_one, one_mul]
  change Real.exp (x / 2) *
      (2 * Real.pi *
        (2 * Real.pi * ((n : ℝ) * u) ^ 4 -
          3 * ((n : ℝ) * u) ^ 2) *
            Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2)) ≤ _
  change _ ≤
    (2 * (n : ℝ) ^ 4 * Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) *
      Real.exp (-(2 * Real.pi * ((n : ℝ) ^ 2 - 1)) * x)) *
        (Real.exp (x / 2) *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2) *
            Real.exp (-Real.pi * u ^ 2)))
  calc
    _ ≤ Real.exp (x / 2) *
        ((2 * (n : ℝ) ^ 4 *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2))) *
            Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2)) := by
      gcongr
    _ ≤ Real.exp (x / 2) *
        ((2 * (n : ℝ) ^ 4 *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2))) *
            (Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) *
              (Real.exp (-2 * Real.pi * ((n : ℝ) ^ 2 - 1) * x) *
                Real.exp (-Real.pi * u ^ 2)))) := by
      gcongr
    _ = _ := by ring

/-- The extra Gaussian damping absorbs the reflected half-density weight for every higher atom. -/
theorem cosh_half_mul_exp_neg_thetaCuspSourceAtomDampingRate_le_one
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh (x / 2) *
        Real.exp (-thetaCuspSourceAtomDampingRate n * x) ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hrate : (1 / 2 : ℝ) ≤ thetaCuspSourceAtomDampingRate n := by
    have hnSq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have hgap : (3 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by linarith
    have hmul : (9 : ℝ) ≤ Real.pi * ((n : ℝ) ^ 2 - 1) := by
      have h := mul_le_mul Real.pi_gt_three.le hgap
        (by norm_num : (0 : ℝ) ≤ 3) Real.pi_pos.le
      norm_num at h ⊢
      exact h
    rw [thetaCuspSourceAtomDampingRate]
    nlinarith
  have hcosh : Real.cosh (x / 2) ≤ Real.exp (x / 2) := by
    rw [Real.cosh_eq]
    have hneg : Real.exp (-(x / 2)) ≤ Real.exp (x / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  calc
    Real.cosh (x / 2) *
          Real.exp (-thetaCuspSourceAtomDampingRate n * x) ≤
        Real.exp (x / 2) *
          Real.exp (-thetaCuspSourceAtomDampingRate n * x) :=
      mul_le_mul_of_nonneg_right hcosh (Real.exp_pos _).le
    _ = Real.exp ((1 / 2 - thetaCuspSourceAtomDampingRate n) * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrate) hx)
    _ = 1 := Real.exp_zero

/-- Every higher atom's half-density observation is controlled by its original undamped
first-atom weight. -/
theorem cosh_half_mul_thetaCuspSourceTerm_le_first_weight
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    Real.cosh (x / 2) * thetaCuspSourceTerm x n ≤
      thetaCuspSourceAtomDominationWeight n * thetaCuspSourceTerm x 1 := by
  have hatom := thetaCuspSourceTerm_le_first_mul_exp_damping
    (n := n) (by omega) hx.le
  have habsorb :=
    cosh_half_mul_exp_neg_thetaCuspSourceAtomDampingRate_le_one hn hx.le
  have hfactor :
      0 ≤ thetaCuspSourceAtomDominationWeight n * thetaCuspSourceTerm x 1 :=
    mul_nonneg (thetaCuspSourceAtomDominationWeight_nonneg n)
      (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  calc
    Real.cosh (x / 2) * thetaCuspSourceTerm x n ≤
        Real.cosh (x / 2) *
          ((thetaCuspSourceAtomDominationWeight n *
              Real.exp (-thetaCuspSourceAtomDampingRate n * x)) *
            thetaCuspSourceTerm x 1) :=
      mul_le_mul_of_nonneg_left hatom (Real.cosh_pos _).le
    _ = (thetaCuspSourceAtomDominationWeight n * thetaCuspSourceTerm x 1) *
        (Real.cosh (x / 2) *
          Real.exp (-thetaCuspSourceAtomDampingRate n * x)) := by ring
    _ ≤ (thetaCuspSourceAtomDominationWeight n * thetaCuspSourceTerm x 1) * 1 :=
      mul_le_mul_of_nonneg_left habsorb hfactor
    _ = thetaCuspSourceAtomDominationWeight n * thetaCuspSourceTerm x 1 := by ring

/-- Pointwise half-density domination of the complete higher theta tail. -/
theorem cosh_half_mul_thetaCuspHigherSource_le_first_weight
    {x : ℝ} (hx : 0 < x) :
    Real.cosh (x / 2) *
        (thetaCuspFullSource x - thetaCuspSourceTerm x 1) ≤
      thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1 := by
  have hs := summable_thetaCuspSourceTerm x
  have htail : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + 2)) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hleft : Summable (fun k : ℕ =>
      Real.cosh (x / 2) * thetaCuspSourceTerm x (k + 2)) :=
    htail.mul_left _
  have hweight : Summable
      (fun k : ℕ => thetaCuspSourceAtomDominationWeight (k + 2)) :=
    summable_thetaCuspSourceAtomDominationWeight.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hright : Summable (fun k : ℕ =>
      thetaCuspSourceAtomDominationWeight (k + 2) * thetaCuspSourceTerm x 1) :=
    hweight.mul_right _
  have hhead :
      (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) =
        thetaCuspSourceTerm x 1 := by
    calc
      (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) =
          thetaCuspSourceTerm x 0 + thetaCuspSourceTerm x 1 := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      _ = thetaCuspSourceTerm x 1 := by
        simp [thetaCuspSourceTerm, thetaCuspSeed]
  have htailEq :
      thetaCuspFullSource x - thetaCuspSourceTerm x 1 =
        ∑' k : ℕ, thetaCuspSourceTerm x (k + 2) := by
    rw [thetaCuspFullSource, ← hs.sum_add_tsum_nat_add 2, hhead]
    ring
  calc
    Real.cosh (x / 2) *
          (thetaCuspFullSource x - thetaCuspSourceTerm x 1) =
        ∑' k : ℕ,
          Real.cosh (x / 2) * thetaCuspSourceTerm x (k + 2) := by
      rw [htailEq, tsum_mul_left]
    _ ≤ ∑' k : ℕ,
        thetaCuspSourceAtomDominationWeight (k + 2) *
          thetaCuspSourceTerm x 1 :=
      Summable.tsum_le_tsum
        (fun k => cosh_half_mul_thetaCuspSourceTerm_le_first_weight
          (n := k + 2) (by omega) hx)
        hleft hright
    _ = thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1 := by
      rw [thetaCuspHigherAtomDominationWeight]
      exact Summable.tsum_mul_right _ hweight

/-- The exact reflected higher-atom budget is bounded by the old uniform domination weight times
the first-atom mass. -/
theorem thetaCuspHigherHalfDensityBudget_le_dominationWeight_mul_firstAtomZero :
    thetaCuspHigherHalfDensityBudget ≤
      thetaCuspHigherAtomDominationWeight * thetaCuspAtomRawEvenMoment 0 1 := by
  have hleft := integrableOn_cosh_half_mul_thetaCuspHigherSource
  have hfirst := integrableOn_pow_mul_thetaCuspSourceTerm 0 1
  have hright : IntegrableOn (fun x : ℝ =>
      thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1) (Ioi 0) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul] using
      hfirst.const_mul thetaCuspHigherAtomDominationWeight
  have hmono :
      (∫ x : ℝ in Ioi 0, Real.cosh (x / 2) *
          (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) ≤
        ∫ x : ℝ in Ioi 0,
          thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1 := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact cosh_half_mul_thetaCuspHigherSource_le_first_weight hx
  have hbudget := two_mul_integral_cosh_half_mul_thetaCuspHigherSource_eq_budget
  rw [thetaCuspAtomRawEvenMoment]
  norm_num only [Nat.mul_zero, pow_zero, one_mul]
  rw [integral_const_mul] at hmono
  nlinarith

/-- Rational form of the active reflected-budget comparison. -/
theorem thetaCuspHigherHalfDensityBudget_le_uniformLoss_mul_firstAtomZero :
    thetaCuspHigherHalfDensityBudget ≤
      (8 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1 := by
  calc
    thetaCuspHigherHalfDensityBudget ≤
        thetaCuspHigherAtomDominationWeight * thetaCuspAtomRawEvenMoment 0 1 :=
      thetaCuspHigherHalfDensityBudget_le_dominationWeight_mul_firstAtomZero
    _ ≤ (8 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1 :=
      mul_le_mul_of_nonneg_right
        thetaCuspHigherAtomDominationWeight_le_geometric_rational
        (thetaCuspAtomRawEvenMoment_nonneg 0 1)

/-- The reflected first-moment multiplier is no larger than the old single-loss multiplier. -/
theorem thetaCusp_pairBudget_add_higherBudget_le_singleLoss :
    thetaCuspFirstAtomHalfDensityPairBudget + thetaCuspHigherHalfDensityBudget ≤
      (3005 / 2997 : ℝ) * thetaCuspFirstAtomHalfDensityPairBudget := by
  have h0 := thetaCuspHigherHalfDensityBudget_le_uniformLoss_mul_firstAtomZero
  have ha1 : 0 ≤ thetaCuspAtomRawEvenMoment 1 1 :=
    thetaCuspAtomRawEvenMoment_nonneg 1 1
  rw [thetaCuspFirstAtomHalfDensityPairBudget]
  nlinarith

/-- The reflected zeroth-moment multiplier is no larger than the old single-loss multiplier. -/
theorem thetaCusp_firstAtomZero_add_higherBudget_le_singleLoss :
    thetaCuspAtomRawEvenMoment 0 1 + thetaCuspHigherHalfDensityBudget ≤
      (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1 := by
  have h := thetaCuspHigherHalfDensityBudget_le_uniformLoss_mul_firstAtomZero
  nlinarith

end

end RHTower
