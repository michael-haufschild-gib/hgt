import Mathlib
import GaloisForLFunctions.RHTower.GibbsScaleContraction

/-!
# The parity--energy source of the Gibbs dilation defect

The scale defect left open by the squarefree Gibbs programme is not an opaque remainder.
It is generated infinitesimally by the covariance between configuration parity and
multiplicative energy.  This file gives a division-free version of that statement and
computes its first nonzero jet at the free-gas boundary.

For every nonempty finite aperture `S`, the defect created by dilation through `p` has
derivative

`(p - 1) * 2^|S| * (-1)^(|S|+1) * ∏_{q∈S} (q-1)`

at coupling zero.  Its sign therefore alternates with aperture cardinality.  In particular,
no sign-definite covariance or monotone-dilation argument can control the cofinal all-prime
defect: the physical moving-aperture limit must overcome an alternating finite-volume jet.
-/

namespace RHTower.GibbsGas

open Real

/-- The unnormalised multiplicative-energy moment of the finite Gibbs gas. -/
noncomputable def gibbsEnergyMoment (S : Finset ℕ) (x z : ℝ) : ℝ :=
  ∑ T ∈ S.powerset,
    (∏ q ∈ T, (q : ℝ)) * z ^ T.card *
      Real.exp (-(x * ∏ q ∈ T, (q : ℝ)))

/-- Differentiating the coupling inserts minus the multiplicative energy. -/
theorem hasDerivAt_gibbsDiag_energy (S : Finset ℕ) (x z : ℝ) :
    HasDerivAt (fun y => gibbsDiag S y z) (-gibbsEnergyMoment S x z) x := by
  classical
  have hterm : ∀ T ∈ S.powerset,
      HasDerivAt
        (fun y => z ^ T.card * Real.exp (-(y * ∏ q ∈ T, (q : ℝ))))
        (z ^ T.card * (Real.exp (-(x * ∏ q ∈ T, (q : ℝ))) *
          -(∏ q ∈ T, (q : ℝ)))) x := by
    intro T _
    have hmul : HasDerivAt
        (fun y : ℝ => y * ∏ q ∈ T, (q : ℝ))
        (∏ q ∈ T, (q : ℝ)) x :=
      hasDerivAt_mul_const _
    have hlin : HasDerivAt
        (fun y : ℝ => -(y * ∏ q ∈ T, (q : ℝ)))
        (-(∏ q ∈ T, (q : ℝ))) x := hmul.neg
    have hexp := hlin.exp
    exact hexp.const_mul (z ^ T.card)
  have hsum := HasDerivAt.sum hterm
  have hvalue :
      ∑ T ∈ S.powerset,
          (z ^ T.card * (Real.exp (-(x * ∏ q ∈ T, (q : ℝ))) *
            -(∏ q ∈ T, (q : ℝ)))) =
        -gibbsEnergyMoment S x z := by
    rw [gibbsEnergyMoment, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [hvalue] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [gibbsDiag, Finset.sum_apply]

/-- Division-free covariance numerator between parity and multiplicative energy. -/
noncomputable def gibbsParityEnergyCovarianceNumerator (S : Finset ℕ) (x : ℝ) : ℝ :=
  gibbsEnergyMoment S x (-1) * gibbsDiag S x 1 -
    gibbsDiag S x (-1) * gibbsEnergyMoment S x 1

/-- Normalized covariance between configuration parity and multiplicative energy. -/
noncomputable def gibbsParityEnergyCovariance (S : Finset ℕ) (x : ℝ) : ℝ :=
  gibbsParityEnergyCovarianceNumerator S x / (gibbsDiag S x 1) ^ (2 : ℕ)

/-- The derivative of the normalized parity current is minus parity--energy covariance. -/
theorem hasDerivAt_normalized_gibbs_current (S : Finset ℕ) (x : ℝ) :
    HasDerivAt
      (fun y => gibbsDiag S y (-1) / gibbsDiag S y 1)
      (-gibbsParityEnergyCovarianceNumerator S x / (gibbsDiag S x 1) ^ (2 : ℕ)) x := by
  have hJ := hasDerivAt_gibbsDiag_energy S x (-1)
  have hZ := hasDerivAt_gibbsDiag_energy S x 1
  have hZne : gibbsDiag S x 1 ≠ 0 := ne_of_gt (gibbs_partition_pos S x)
  have hquot := hJ.div hZ hZne
  have hvalue :
      (-gibbsEnergyMoment S x (-1) * gibbsDiag S x 1 -
          gibbsDiag S x (-1) * (-gibbsEnergyMoment S x 1)) /
          gibbsDiag S x 1 ^ (2 : ℕ) =
        -gibbsParityEnergyCovarianceNumerator S x / gibbsDiag S x 1 ^ (2 : ℕ) := by
    unfold gibbsParityEnergyCovarianceNumerator
    ring
  rw [hvalue] at hquot
  exact hquot

/-- The covariance is continuous at every finite aperture. -/
theorem continuous_gibbsParityEnergyCovariance (S : Finset ℕ) :
    Continuous (gibbsParityEnergyCovariance S) := by
  classical
  have hdiag (z : ℝ) : Continuous (fun x => gibbsDiag S x z) := by
    unfold gibbsDiag
    fun_prop
  have henergy (z : ℝ) : Continuous (fun x => gibbsEnergyMoment S x z) := by
    unfold gibbsEnergyMoment
    fun_prop
  have hnum : Continuous (gibbsParityEnergyCovarianceNumerator S) := by
    unfold gibbsParityEnergyCovarianceNumerator
    exact ((henergy (-1)).mul (hdiag 1)).sub ((hdiag (-1)).mul (henergy 1))
  unfold gibbsParityEnergyCovariance
  exact hnum.div ((hdiag 1).pow 2) fun x =>
    pow_ne_zero 2 (ne_of_gt (gibbs_partition_pos S x))

/-- **Integrated covariance law.**  Every finite-scale change of normalized parity current
is exactly the accumulated parity--energy covariance across the coupling interval. -/
theorem integral_neg_covariance_eq_normalized_current_sub (S : Finset ℕ) (a b : ℝ) :
    (∫ t in a..b, -gibbsParityEnergyCovariance S t) =
      gibbsDiag S b (-1) / gibbsDiag S b 1 -
        gibbsDiag S a (-1) / gibbsDiag S a 1 := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun y => gibbsDiag S y (-1) / gibbsDiag S y 1)
        (-gibbsParityEnergyCovariance S t) t := by
    intro t _
    have h := hasDerivAt_normalized_gibbs_current S t
    have hvalue :
        -gibbsParityEnergyCovarianceNumerator S t / gibbsDiag S t 1 ^ (2 : ℕ) =
          -(gibbsParityEnergyCovarianceNumerator S t / gibbsDiag S t 1 ^ (2 : ℕ)) := by
      ring
    rw [hvalue] at h
    simpa only [gibbsParityEnergyCovariance] using h
  have hint : IntervalIntegrable (fun t => -gibbsParityEnergyCovariance S t)
      MeasureTheory.volume a b :=
    (continuous_gibbsParityEnergyCovariance S).neg.intervalIntegrable a b
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- The exact two-scale defect that carries all cancellation beyond the baseline contraction. -/
noncomputable def gibbsScaleDefect (p : ℕ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  gibbsDiag S ((p : ℝ) * x) (-1) * gibbsDiag S x 1 -
    gibbsDiag S x (-1) * gibbsDiag S ((p : ℝ) * x) 1

/-- The defect is the partition-mass product times the change of normalized current. -/
theorem gibbsScaleDefect_eq_normalized_current_difference (p : ℕ) (S : Finset ℕ)
    (x : ℝ) :
    gibbsScaleDefect p S x =
      gibbsDiag S x 1 * gibbsDiag S ((p : ℝ) * x) 1 *
        (gibbsDiag S ((p : ℝ) * x) (-1) /
            gibbsDiag S ((p : ℝ) * x) 1 -
          gibbsDiag S x (-1) / gibbsDiag S x 1) := by
  have hZx : gibbsDiag S x 1 ≠ 0 := ne_of_gt (gibbs_partition_pos S x)
  have hZpx : gibbsDiag S ((p : ℝ) * x) 1 ≠ 0 :=
    ne_of_gt (gibbs_partition_pos S ((p : ℝ) * x))
  unfold gibbsScaleDefect
  field_simp

/-- **The exact source formula for the open defect.**  The dilation defect is the
partition-mass product times integrated negative parity--energy covariance. -/
theorem gibbsScaleDefect_eq_integral_neg_covariance (p : ℕ) (S : Finset ℕ) (x : ℝ) :
    gibbsScaleDefect p S x =
      gibbsDiag S x 1 * gibbsDiag S ((p : ℝ) * x) 1 *
        (∫ t in x..(p : ℝ) * x, -gibbsParityEnergyCovariance S t) := by
  rw [gibbsScaleDefect_eq_normalized_current_difference,
    integral_neg_covariance_eq_normalized_current_sub]

/-- The named defect is exactly the remainder in `normalized_current_decomposition`. -/
theorem normalized_current_decomposition_defect (p : ℕ) (S : Finset ℕ)
    (hp : p ∉ S) (x : ℝ) :
    gibbsDiag (insert p S) x (-1) * gibbsDiag S x 1 =
      gibbsDiag S x (-1) *
        (gibbsDiag S x 1 - gibbsDiag S ((p : ℝ) * x) 1) -
          gibbsScaleDefect p S x := by
  simpa only [gibbsScaleDefect] using normalized_current_decomposition p S hp x

/-- The scale defect vanishes at the free-gas boundary. -/
theorem gibbsScaleDefect_zero (p : ℕ) (S : Finset ℕ) :
    gibbsScaleDefect p S 0 = 0 := by
  simp [gibbsScaleDefect, gibbsDiag_zero]

/-- **Parity--energy defect jet.**  The first nonzero jet of the dilation defect is an
explicit signed totient law.  Its sign alternates with the cardinality of the aperture. -/
theorem hasDerivAt_gibbsScaleDefect_zero (p : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    HasDerivAt (gibbsScaleDefect p S)
      (((p : ℝ) - 1) * 2 ^ S.card *
        ((-1 : ℝ) ^ (S.card + 1) * ∏ q ∈ S, ((q : ℝ) - 1))) 0 := by
  let c : ℝ := (-1 : ℝ) ^ (S.card + 1) * ∏ q ∈ S, ((q : ℝ) - 1)
  have hJ : HasDerivAt (fun x => gibbsDiag S x (-1)) c 0 := by
    simpa only [c] using hasDerivAt_gibbs_current S
  have hZ : HasDerivAt (fun x => gibbsDiag S x 1)
      (-gibbsEnergyMoment S 0 1) 0 := hasDerivAt_gibbsDiag_energy S 0 1
  have hmul : HasDerivAt (fun x : ℝ => (p : ℝ) * x) (p : ℝ) 0 := by
    simpa [id_eq] using (hasDerivAt_id (x := (0 : ℝ))).const_mul (p : ℝ)
  have hJ' : HasDerivAt (fun x => gibbsDiag S x (-1)) c ((p : ℝ) * 0) := by
    simpa using hJ
  have hZ' : HasDerivAt (fun x => gibbsDiag S x 1)
      (-gibbsEnergyMoment S 0 1) ((p : ℝ) * 0) := by
    simpa using hZ
  have hJp : HasDerivAt (fun x => gibbsDiag S ((p : ℝ) * x) (-1))
      ((p : ℝ) * c) 0 := by
    simpa [Function.comp_def, mul_comm] using hJ'.comp 0 hmul
  have hZp : HasDerivAt (fun x => gibbsDiag S ((p : ℝ) * x) 1)
      ((p : ℝ) * (-gibbsEnergyMoment S 0 1)) 0 := by
    simpa [Function.comp_def, mul_comm] using hZ'.comp 0 hmul
  have h := (hJp.mul hZ).sub (hJ.mul hZp)
  have hSne : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hS
  have hJzero : gibbsDiag S 0 (-1) = 0 := by
    rw [gibbsDiag_zero]
    norm_num [hSne]
  have hZzero : gibbsDiag S 0 1 = 2 ^ S.card := by
    rw [gibbsDiag_zero]
    norm_num
  change HasDerivAt (gibbsScaleDefect p S) _ 0 at h
  convert h using 1
  simp only [mul_zero, hJzero, hZzero, zero_mul, mul_zero, add_zero]
  simp only [c]
  ring

/-- At zero coupling the division-free covariance numerator is the negative current jet
times the free partition mass. -/
theorem gibbsParityEnergyCovarianceNumerator_zero (S : Finset ℕ) (hS : S.Nonempty) :
    gibbsParityEnergyCovarianceNumerator S 0 =
      -(((-1 : ℝ) ^ (S.card + 1) * ∏ q ∈ S, ((q : ℝ) - 1)) * 2 ^ S.card) := by
  have hunique := (hasDerivAt_gibbsDiag_energy S 0 (-1)).unique
    (hasDerivAt_gibbs_current S)
  have henergy : gibbsEnergyMoment S 0 (-1) =
      -((-1 : ℝ) ^ (S.card + 1) * ∏ q ∈ S, ((q : ℝ) - 1)) := by
    linarith
  have hSne : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hS
  have hJzero : gibbsDiag S 0 (-1) = 0 := by
    rw [gibbsDiag_zero]
    norm_num [hSne]
  have hZzero : gibbsDiag S 0 1 = 2 ^ S.card := by
    rw [gibbsDiag_zero]
    norm_num
  rw [gibbsParityEnergyCovarianceNumerator, hJzero, hZzero, henergy]
  ring

/-- The defect jet is exactly minus `(p-1)` times the parity--energy covariance numerator. -/
theorem deriv_gibbsScaleDefect_zero_eq_covariance (p : ℕ) (S : Finset ℕ)
    (hS : S.Nonempty) :
    deriv (gibbsScaleDefect p S) 0 =
      -((p : ℝ) - 1) * gibbsParityEnergyCovarianceNumerator S 0 := by
  rw [(hasDerivAt_gibbsScaleDefect_zero p S hS).deriv,
    gibbsParityEnergyCovarianceNumerator_zero S hS]
  ring

/-- For a natural prime aperture of odd cardinality, the infinitesimal dilation defect is
strictly positive. -/
theorem deriv_gibbsScaleDefect_zero_pos_of_odd (p : ℕ) (S : Finset ℕ)
    (hS : S.Nonempty) (hp : 2 ≤ p) (hmem : ∀ q ∈ S, 2 ≤ q)
    (hodd : Odd S.card) :
    0 < deriv (gibbsScaleDefect p S) 0 := by
  have hpcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp' : 0 < (p : ℝ) - 1 := by linarith
  have hprod : 0 < ∏ q ∈ S, ((q : ℝ) - 1) := by
    apply Finset.prod_pos
    intro q hq
    have hqcast : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hmem q hq
    linarith
  rw [(hasDerivAt_gibbsScaleDefect_zero p S hS).deriv,
    hodd.add_one.neg_one_pow]
  positivity

/-- For a natural prime aperture of even positive cardinality, the infinitesimal dilation
defect is strictly negative. -/
theorem deriv_gibbsScaleDefect_zero_neg_of_even (p : ℕ) (S : Finset ℕ)
    (hS : S.Nonempty) (hp : 2 ≤ p) (hmem : ∀ q ∈ S, 2 ≤ q)
    (heven : Even S.card) :
    deriv (gibbsScaleDefect p S) 0 < 0 := by
  have hpcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp' : 0 < (p : ℝ) - 1 := by linarith
  have hprod : 0 < ∏ q ∈ S, ((q : ℝ) - 1) := by
    apply Finset.prod_pos
    intro q hq
    have hqcast : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hmem q hq
    linarith
  have hpow : 0 < (2 : ℝ) ^ S.card := by positivity
  have hmain : 0 < ((p : ℝ) - 1) * (2 : ℝ) ^ S.card *
      (∏ q ∈ S, ((q : ℝ) - 1)) := mul_pos (mul_pos hp' hpow) hprod
  rw [(hasDerivAt_gibbsScaleDefect_zero p S hS).deriv,
    heven.add_one.neg_one_pow]
  nlinarith

end RHTower.GibbsGas
