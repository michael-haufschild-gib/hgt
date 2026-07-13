import GaloisForLFunctions.RHTower.XiPrimeSeamPairAsymptotics

/-!
# The Xi prime seam as a horizontal reflection energy

The reciprocal-prime square density of the canonical FE--Schwarz seam has an exact symmetric
second-difference formula.  Consequently, the full one-particle seam energy is independent of
zero height, is invariant under functional-equation reflection, and equals a centered second
difference of the prime logarithmic moment curve.

This identifies the positive slope in the cofinal pair-energy theorem as a horizontal convexity
defect rather than an unspecified norm.  No Xi zero-location information is used.
-/

namespace RHTower

noncomputable section

private lemma star_natPrime_cpow (p : Nat.Primes) (w : ℂ) :
    (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ w) =
      (((p : ℕ) : ℂ) ^ ((starRingEnd ℂ) w)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have harg : ((p : ℂ).arg ≠ Real.pi) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg hp.le]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (p : ℂ) w harg
  simpa using h.symm

/-- Exact per-prime horizontal reflection defect. -/
theorem orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference
    (rho : ℂ) (p : Nat.Primes) :
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ) =
      (Real.log (p : ℝ)) ^ 2 *
        ((p : ℝ) ^ (-(1 + 2 * rho.re)) +
          (p : ℝ) ^ (-(3 - 2 * rho.re)) -
          2 * (p : ℝ) ^ (-2 : ℝ)) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  let u : ℂ := (p : ℂ) ^ (-(starRingEnd ℂ) rho)
  let v : ℂ := (p : ℂ) ^ (-(1 - rho))
  have huNorm : ‖u‖ = (p : ℝ) ^ (-rho.re) := by
    dsimp [u]
    change ‖(((p : ℕ) : ℝ) : ℂ) ^ (-(starRingEnd ℂ) rho)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  have hvNorm : ‖v‖ = (p : ℝ) ^ (-(1 - rho.re)) := by
    dsimp [v]
    change ‖(((p : ℕ) : ℝ) : ℂ) ^ (-(1 - rho))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  have hcross : u * (starRingEnd ℂ) v = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
    dsimp [u, v]
    change (((p : ℕ) : ℂ) ^ (-(starRingEnd ℂ) rho)) *
      (starRingEnd ℂ) ((((p : ℕ) : ℂ) ^ (-(1 - rho)))) = _
    rw [star_natPrime_cpow p]
    rw [← Complex.cpow_add _ _ (by exact_mod_cast p.prop.ne_zero)]
    have hexp : -(starRingEnd ℂ) rho +
        (starRingEnd ℂ) (-(1 - rho)) = (-1 : ℂ) := by
      apply Complex.ext
      · simp
        ring_nf
      · simp
    rw [hexp, Complex.cpow_neg_one]
    norm_num
  have huSq : Complex.normSq u = (p : ℝ) ^ (-2 * rho.re) := by
    rw [Complex.normSq_eq_norm_sq, huNorm]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp.le]
    congr 1
    ring
  have hvSq : Complex.normSq v = (p : ℝ) ^ (-2 * (1 - rho.re)) := by
    rw [Complex.normSq_eq_norm_sq, hvNorm]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp.le]
    congr 1
    ring
  have hdiff : ‖u - v‖ ^ 2 =
      (p : ℝ) ^ (-2 * rho.re) +
        (p : ℝ) ^ (-2 * (1 - rho.re)) - 2 * (p : ℝ)⁻¹ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, huSq, hvSq, hcross]
    norm_num
  have hcharge : ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 =
      (Real.log (p : ℝ)) ^ 2 * ‖u - v‖ ^ 2 := by
    dsimp [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge, u, v]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hp1.le)]
    ring
  rw [hcharge, hdiff]
  rw [div_eq_mul_inv, ← Real.rpow_neg_one]
  have hmulLeft :
      (p : ℝ) ^ (-2 * rho.re) * (p : ℝ) ^ (-1 : ℝ) =
        (p : ℝ) ^ (-(1 + 2 * rho.re)) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hmulRight :
      (p : ℝ) ^ (-2 * (1 - rho.re)) * (p : ℝ) ^ (-1 : ℝ) =
        (p : ℝ) ^ (-(3 - 2 * rho.re)) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hmulCross :
      (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-1 : ℝ) = (p : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hp]
    norm_num
  calc
    (Real.log (p : ℝ)) ^ 2 *
          ((p : ℝ) ^ (-2 * rho.re) +
            (p : ℝ) ^ (-2 * (1 - rho.re)) - 2 * (p : ℝ) ^ (-1 : ℝ)) *
        (p : ℝ) ^ (-1 : ℝ) =
      (Real.log (p : ℝ)) ^ 2 *
        (((p : ℝ) ^ (-2 * rho.re) * (p : ℝ) ^ (-1 : ℝ)) +
          ((p : ℝ) ^ (-2 * (1 - rho.re)) * (p : ℝ) ^ (-1 : ℝ)) -
          2 * ((p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-1 : ℝ))) := by ring
    _ = _ := by rw [hmulLeft, hmulRight, hmulCross]

/-- The reciprocal-prime seam square density depends only on the horizontal coordinate. -/
theorem orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_of_re_eq
    {rho z : ℂ} (h : rho.re = z.re) (p : Nat.Primes) :
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ) =
      ‖orbitwiseNatPrimeSeamCharge (p : ℕ) z‖ ^ 2 / (p : ℝ) := by
  rw [orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference,
    orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference, h]

/-- The full seam square energy depends only on the horizontal coordinate. -/
theorem orbitwisePrimeSeamWeightedNormSq_eq_of_re_eq
    {rho z : ℂ} (h : rho.re = z.re) :
    orbitwisePrimeSeamWeightedNormSq rho = orbitwisePrimeSeamWeightedNormSq z := by
  unfold orbitwisePrimeSeamWeightedNormSq
  apply tsum_congr
  exact orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_of_re_eq h

/-- Functional-equation reflection preserves the full seam square energy. -/
theorem orbitwisePrimeSeamWeightedNormSq_one_sub_star
    (rho : ℂ) :
    orbitwisePrimeSeamWeightedNormSq (1 - (starRingEnd ℂ) rho) =
      orbitwisePrimeSeamWeightedNormSq rho := by
  unfold orbitwisePrimeSeamWeightedNormSq
  apply tsum_congr
  intro p
  rw [orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference,
    orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  congr 1
  ring

/-- Prime-only logarithmic second moment. -/
def primeLogSquareMoment (beta : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-beta)

theorem summable_primeLogSquareMoment {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun p : Nat.Primes =>
      (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-beta)) := by
  simpa only [sq_abs] using
    (summable_abs_log_natCast_pow_mul_rpow_neg 2 beta hbeta).comp_injective
      Subtype.coe_injective

/-- The full seam energy is the centered symmetric second difference of the prime logarithmic
moment curve. -/
theorem orbitwisePrimeSeamWeightedNormSq_eq_primeLogSquareMoment_secondDifference
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    orbitwisePrimeSeamWeightedNormSq rho =
      primeLogSquareMoment (1 + 2 * rho.re) +
        primeLogSquareMoment (3 - 2 * rho.re) -
          2 * primeLogSquareMoment 2 := by
  have hleft := summable_primeLogSquareMoment (by linarith : 1 < 1 + 2 * rho.re)
  have hright := summable_primeLogSquareMoment (by linarith : 1 < 3 - 2 * rho.re)
  have hcenter := summable_primeLogSquareMoment (by norm_num : (1 : ℝ) < 2)
  unfold orbitwisePrimeSeamWeightedNormSq primeLogSquareMoment
  calc
    (∑' p : Nat.Primes,
        ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ)) =
      ∑' p : Nat.Primes,
        ((Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-(1 + 2 * rho.re)) +
          (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-(3 - 2 * rho.re)) -
            2 * ((Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-2 : ℝ))) := by
      apply tsum_congr
      intro p
      rw [orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference]
      ring
    _ = (∑' p : Nat.Primes,
          ((Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-(1 + 2 * rho.re)) +
            (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-(3 - 2 * rho.re)))) -
          ∑' p : Nat.Primes,
            2 * ((Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-2 : ℝ)) :=
      (hleft.add hright).tsum_sub (hcenter.mul_left 2)
    _ = _ := by rw [hleft.tsum_add hright, tsum_mul_left]

/-- The prime-two curvature defect quantitatively controls the full seam energy from below. -/
theorem primeTwo_reflectionSecondDifference_le_orbitwisePrimeSeamWeightedNormSq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    (Real.log 2) ^ 2 *
        ((2 : ℝ) ^ (-(1 + 2 * rho.re)) +
          (2 : ℝ) ^ (-(3 - 2 * rho.re)) - 2 * (2 : ℝ) ^ (-2 : ℝ)) ≤
      orbitwisePrimeSeamWeightedNormSq rho := by
  have hsum := summable_orbitwisePrimeSeam_weighted_norm_sq hstrip
  have hle := hsum.le_tsum (⟨2, by norm_num⟩ : Nat.Primes) (fun p _ =>
    div_nonneg (sq_nonneg _) (by exact_mod_cast p.prop.pos.le))
  rw [orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference] at hle
  change (Real.log 2) ^ 2 *
      ((2 : ℝ) ^ (-(1 + 2 * rho.re)) +
        (2 : ℝ) ^ (-(3 - 2 * rho.re)) - 2 * (2 : ℝ) ^ (-2 : ℝ)) ≤
    orbitwisePrimeSeamWeightedNormSq rho at hle
  exact hle

/-- The cofinal pair-energy slope is twice the symmetric prime-curvature defect. -/
theorem tendsto_orbitwisePrimeSeamPairEnergy_div_mass_to_primeLogSquareMoment_secondDifference
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Filter.Tendsto
      (fun s : Finset Nat.Primes =>
        primePairDifferenceEnergy
          (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s /
            primeReciprocalMass s)
      Filter.atTop
      (nhds (2 *
        (primeLogSquareMoment (1 + 2 * rho.re) +
          primeLogSquareMoment (3 - 2 * rho.re) -
            2 * primeLogSquareMoment 2))) := by
  simpa [orbitwisePrimeSeamWeightedNormSq_eq_primeLogSquareMoment_secondDifference hstrip] using
    tendsto_orbitwisePrimeSeamPairEnergy_div_mass hstrip

end

end RHTower
