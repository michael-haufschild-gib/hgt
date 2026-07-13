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

/-- The prime logarithmic Hilbert feature at a right-half-plane node. -/
def primeLogHilbertFeature (s : ℂ) (p : ℕ) : ℂ :=
  (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
    ((Real.log (p : ℝ) : ℂ) * (((p : ℝ) : ℂ) ^ (-s)))

/-- The canonical seam is the difference of the Schwarz and FE prime features, coordinate by
coordinate. -/
theorem primeLogHilbertFeature_reflectionDifference
    (rho : ℂ) (p : Nat.Primes) :
    primeLogHilbertFeature ((starRingEnd ℂ) rho) (p : ℕ) -
        primeLogHilbertFeature (1 - rho) (p : ℕ) =
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
        orbitwiseNatPrimeSeamCharge (p : ℕ) rho := by
  simp only [primeLogHilbertFeature, orbitwiseNatPrimeSeamCharge,
    orbitwiseScaleSeamCharge]
  ring

/-- Per-coordinate squared-distance form of the seam energy. -/
theorem norm_sq_primeLogHilbertFeature_reflectionDifference
    (rho : ℂ) (p : Nat.Primes) :
    ‖primeLogHilbertFeature ((starRingEnd ℂ) rho) (p : ℕ) -
        primeLogHilbertFeature (1 - rho) (p : ℕ)‖ ^ 2 =
      ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ) := by
  rw [primeLogHilbertFeature_reflectionDifference, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hp : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.pos.le
  rw [mul_pow, inv_pow, Real.sq_sqrt hp]
  ring

/-- Squared prime-feature distance between the Schwarz and FE endpoints. -/
def primeLogHilbertReflectionDistanceSq (rho : ℂ) : ℝ :=
  ∑' p : Nat.Primes,
    ‖primeLogHilbertFeature ((starRingEnd ℂ) rho) (p : ℕ) -
      primeLogHilbertFeature (1 - rho) (p : ℕ)‖ ^ 2

/-- The limiting one-particle seam coefficient is exactly the Schwarz--FE prime-feature distance. -/
theorem primeLogHilbertReflectionDistanceSq_eq_orbitwisePrimeSeamWeightedNormSq
    (rho : ℂ) :
    primeLogHilbertReflectionDistanceSq rho = orbitwisePrimeSeamWeightedNormSq rho := by
  unfold primeLogHilbertReflectionDistanceSq orbitwisePrimeSeamWeightedNormSq
  apply tsum_congr
  exact norm_sq_primeLogHilbertFeature_reflectionDifference rho

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

private lemma exp_neg_two_add_exp_two_sub_two_eq_four_sinh_sq (x : ℝ) :
    Real.exp (-2 * x) + Real.exp (2 * x) - 2 = 4 * Real.sinh x ^ 2 := by
  have hneg : Real.exp (-2 * x) = Real.exp (-x) * Real.exp (-x) := by
    rw [show -2 * x = -x + -x by ring, Real.exp_add]
  have hpos : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [hneg, hpos, Real.sinh_eq]
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith

/-- Hyperbolic form of the per-prime reflection defect.  It makes both positivity and quadratic
coercivity in the horizontal displacement explicit. -/
theorem orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_sinh
    (rho : ℂ) (p : Nat.Primes) :
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ) =
      4 * (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-2 : ℝ) *
        Real.sinh ((rho.re - 1 / 2) * Real.log (p : ℝ)) ^ 2 := by
  rw [orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp,
    Real.rpow_def_of_pos hp]
  let x := (rho.re - 1 / 2) * Real.log (p : ℝ)
  have hleft : Real.exp (Real.log (p : ℝ) * (-(1 + 2 * rho.re))) =
      Real.exp (Real.log (p : ℝ) * (-2 : ℝ)) * Real.exp (-2 * x) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  have hright : Real.exp (Real.log (p : ℝ) * (-(3 - 2 * rho.re))) =
      Real.exp (Real.log (p : ℝ) * (-2 : ℝ)) * Real.exp (2 * x) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  rw [hleft, hright]
  calc
    (Real.log (p : ℝ)) ^ 2 *
        (Real.exp (Real.log (p : ℝ) * (-2 : ℝ)) * Real.exp (-2 * x) +
          Real.exp (Real.log (p : ℝ) * (-2 : ℝ)) * Real.exp (2 * x) -
          2 * Real.exp (Real.log (p : ℝ) * (-2 : ℝ))) =
      (Real.log (p : ℝ)) ^ 2 * Real.exp (Real.log (p : ℝ) * (-2 : ℝ)) *
        (Real.exp (-2 * x) + Real.exp (2 * x) - 2) := by ring
    _ = 4 * (Real.log (p : ℝ)) ^ 2 * Real.exp (Real.log (p : ℝ) * (-2 : ℝ)) *
        Real.sinh x ^ 2 := by rw [exp_neg_two_add_exp_two_sub_two_eq_four_sinh_sq]; ring
    _ = _ := by rfl

/-- Quantitative horizontal coercivity from the single prime `2`: the full seam energy dominates
the squared distance to the critical line with an explicit unconditional constant. -/
theorem horizontalDisplacement_sq_mul_log_two_pow_four_le_orbitwisePrimeSeamWeightedNormSq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    (rho.re - 1 / 2) ^ 2 * (Real.log 2) ^ 4 ≤
      orbitwisePrimeSeamWeightedNormSq rho := by
  have hterm := (summable_orbitwisePrimeSeam_weighted_norm_sq hstrip).le_tsum
    (⟨2, by norm_num⟩ : Nat.Primes) (fun p _ =>
      div_nonneg (sq_nonneg _) (by exact_mod_cast p.prop.pos.le))
  rw [orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_sinh] at hterm
  change 4 * (Real.log 2) ^ 2 * (2 : ℝ) ^ (-2 : ℝ) *
      Real.sinh ((rho.re - 1 / 2) * Real.log 2) ^ 2 ≤
    orbitwisePrimeSeamWeightedNormSq rho at hterm
  have hx : |(rho.re - 1 / 2) * Real.log 2| ≤
      |Real.sinh ((rho.re - 1 / 2) * Real.log 2)| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hx
  rw [sq_abs, sq_abs] at hsq
  norm_num at hterm
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [sq_nonneg (Real.log 2), sq_nonneg (rho.re - 1 / 2)]

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
