import GaloisForLFunctions.WindowTowerOfSpecZ.TheAliasingWeightPaysEveryWindow

/-!
# The aliasing norm retains the joint pole

The two Laplace moments are correlated in the exponentially weighted norm.
Balancing their representing vectors gives pole loss
`1 / (sqrt(p+1) * sqrt(p-1)) - 1/p`, strictly smaller than the sum of
the two separate moment costs. Keeping this correlation improves the
aperture-independent lower floor of the complete Weil form.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {A p : ℝ} {H : ℝ → ℝ}

private theorem exp_half_sq (x : ℝ) : Real.exp (x / 2) ^ 2 = Real.exp x := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The exact Gram bound for both Laplace moments in the aliasing norm. -/
theorem laplacePair_sq_le_exponentialMass (hH : IsWindowTest A H) (hp : 1 < p)
    (s t : ℝ) :
    (s * (∫ y, H y * Real.exp (y / 2)) +
        t * (∫ y, H y * Real.exp (-y / 2))) ^ 2 ≤
      exponentialMass p H * (s ^ 2 / (p + 1) + 2 * s * t / p + t ^ 2 / (p - 1)) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hpp : 0 < p + 1 := by linarith only [hp]
  have hpm : 0 < p - 1 := by linarith only [hp]
  let F : ℝ → ℝ := fun y => Real.exp (-(p * y) / 2) * H y
  let E : ℝ → ℝ → ℝ := fun q => (Iic (0 : ℝ)).indicator fun y => Real.exp (q * y)
  let D : ℝ → ℝ := (Iic (0 : ℝ)).indicator fun y =>
    s * Real.exp ((p + 1) * y / 2) + t * Real.exp ((p - 1) * y / 2)
  have iE (q : ℝ) (hq : 0 < q) : Integrable (E q) :=
    (integrable_indicator_iff measurableSet_Iic).mpr (integrableOn_exp_mul_Iic hq 0)
  have intE (q : ℝ) (hq : 0 < q) : (∫ y, E q y) = 1 / q := by
    dsimp only [E]
    rw [integral_indicator measurableSet_Iic, integral_exp_mul_Iic hq 0]
    simp only [mul_zero, Real.exp_zero]
  have hsquare (y : ℝ) :
      (s * Real.exp ((p + 1) * y / 2) + t * Real.exp ((p - 1) * y / 2)) ^ 2 =
        s ^ 2 * Real.exp ((p + 1) * y) +
          (2 * s * t) * Real.exp (p * y) + t ^ 2 * Real.exp ((p - 1) * y) := by
    have he : Real.exp ((p + 1) * y / 2) * Real.exp ((p - 1) * y / 2) =
        Real.exp (p * y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [add_sq, mul_pow, mul_pow, exp_half_sq, exp_half_sq]
    linear_combination (2 * s * t) * he
  have hD2 : (fun y => D y ^ 2) = fun y =>
      s ^ 2 * E (p + 1) y + (2 * s * t) * E p y + t ^ 2 * E (p - 1) y := by
    funext y
    by_cases hy : y ∈ Iic (0 : ℝ)
    · simpa only [D, E, indicator_of_mem hy] using hsquare y
    · simp only [D, E, indicator_of_notMem hy, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero]
  have iD2 : Integrable fun y => D y ^ 2 := by
    rw [hD2]
    exact (((iE (p + 1) hpp).const_mul _).add ((iE p hp0).const_mul _)).add
      ((iE (p - 1) hpm).const_mul _)
  have intD2 : (∫ y, D y ^ 2) =
      s ^ 2 / (p + 1) + 2 * s * t / p + t ^ 2 / (p - 1) := by
    have i1 : Integrable (fun y => s ^ 2 * E (p + 1) y) := (iE (p + 1) hpp).const_mul _
    have i2 : Integrable (fun y => (2 * s * t) * E p y) := (iE p hp0).const_mul _
    have i3 : Integrable (fun y => t ^ 2 * E (p - 1) y) := (iE (p - 1) hpm).const_mul _
    have i12 : Integrable (fun y => s ^ 2 * E (p + 1) y + (2 * s * t) * E p y) :=
      i1.add i2
    rw [hD2, integral_add i12 i3, integral_add i1 i2]
    simp only [integral_const_mul, intE (p + 1) hpp, intE p hp0, intE (p - 1) hpm]
    ring
  have hF2 (y : ℝ) : F y ^ 2 = Real.exp (-(p * y)) * H y ^ 2 := by
    dsimp only [F]
    rw [mul_pow, exp_half_sq]
  have iF2 : Integrable fun y => F y ^ 2 := by
    simpa only [hF2] using integrable_exponentialMass hH p
  have hFD (y : ℝ) : F y * D y =
      s * (H y * Real.exp (y / 2)) + t * (H y * Real.exp (-y / 2)) := by
    by_cases hy : y ∈ Iic (0 : ℝ)
    · have hePos : Real.exp (-(p * y) / 2) * Real.exp ((p + 1) * y / 2) =
          Real.exp (y / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have heNeg : Real.exp (-(p * y) / 2) * Real.exp ((p - 1) * y / 2) =
          Real.exp (-y / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [F, D, indicator_of_mem hy]
      linear_combination s * H y * hePos + t * H y * heNeg
    · have hz := hH.vanish y (fun hm => hy hm.2)
      simp only [F, D, indicator_of_notMem hy, hz, mul_zero, zero_mul, add_zero]
  have iPos : Integrable fun y => H y * Real.exp (y / 2) :=
    (hH.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hH.hasCompactSupport.mul_right
  have iNeg : Integrable fun y => H y * Real.exp (-y / 2) :=
    (hH.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hH.hasCompactSupport.mul_right
  have iFD : Integrable fun y => F y * D y := by
    rw [show (fun y => F y * D y) =
      (fun y => s * (H y * Real.exp (y / 2)) + t * (H y * Real.exp (-y / 2))) from funext hFD]
    exact (iPos.const_mul s).add (iNeg.const_mul t)
  have intFD : (∫ y, F y * D y) = s * (∫ y, H y * Real.exp (y / 2)) +
      t * (∫ y, H y * Real.exp (-y / 2)) := by
    simp only [hFD]
    rw [integral_add (iPos.const_mul s) (iNeg.const_mul t), integral_const_mul, integral_const_mul]
  have hcs := pow_le_pow_left₀ (abs_nonneg _) (abs_integral_mul_le iF2 iD2 iFD) 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg (F y)),
    Real.sq_sqrt (integral_nonneg fun y => sq_nonneg (D y)), intFD, intD2] at hcs
  simpa only [hF2, exponentialMass] using hcs

/-- The correlated pole cost in the exponential norm. -/
def jointExponentialPoleCost (p : ℝ) : ℝ :=
  1 / (Real.sqrt (p + 1) * Real.sqrt (p - 1)) - 1 / p

theorem jointExponentialPoleCost_pos (hp : 1 < p) : 0 < jointExponentialPoleCost p := by
  have hpp : 0 < p + 1 := by linarith only [hp]
  have hpm : 0 < p - 1 := by linarith only [hp]
  have hp0 : 0 < p := by linarith only [hp]
  have hs : 0 < Real.sqrt (p + 1) * Real.sqrt (p - 1) :=
    mul_pos (Real.sqrt_pos.mpr hpp) (Real.sqrt_pos.mpr hpm)
  have hs2 : (Real.sqrt (p + 1) * Real.sqrt (p - 1)) ^ 2 = p ^ 2 - 1 := by
    rw [mul_pow, Real.sq_sqrt hpp.le, Real.sq_sqrt hpm.le]
    ring
  have hlt : Real.sqrt (p + 1) * Real.sqrt (p - 1) < p := by
    nlinarith only [hs2, hs, hp0]
  exact sub_pos.mpr ((one_div_lt_one_div hp0 hs).mpr hlt)

theorem jointExponentialPoleCost_lt_separate (hp : 1 < p) :
    jointExponentialPoleCost p < 1 / (p + 1) + 1 / (p - 1) := by
  have hpp : 0 < p + 1 := by linarith only [hp]
  have hpm : 0 < p - 1 := by linarith only [hp]
  have hp0 : 0 < p := by linarith only [hp]
  have hs : 0 < Real.sqrt (p + 1) * Real.sqrt (p - 1) :=
    mul_pos (Real.sqrt_pos.mpr hpp) (Real.sqrt_pos.mpr hpm)
  have hs2 : (Real.sqrt (p + 1) * Real.sqrt (p - 1)) ^ 2 = p ^ 2 - 1 := by
    rw [mul_pow, Real.sq_sqrt hpp.le, Real.sq_sqrt hpm.le]
    ring
  have hlt : p - 1 < Real.sqrt (p + 1) * Real.sqrt (p - 1) := by
    nlinarith only [hs2, hs, hp]
  have hi := (one_div_lt_one_div hs hpm).mpr hlt
  have hip := one_div_pos.mpr hp0
  have hipp := one_div_pos.mpr hpp
  dsimp only [jointExponentialPoleCost]
  linarith only [hi, hip, hipp]

/-- The joint pole keeps the correlation between its two moment vectors. -/
theorem pole_ge_neg_jointExponentialMass (hH : IsWindowTest A H) (hp : 1 < p) :
    -(jointExponentialPoleCost p * exponentialMass p H) ≤
      coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2 := by
  let s := Real.sqrt (p + 1)
  let t := Real.sqrt (p - 1)
  have hpp : 0 < p + 1 := by linarith only [hp]
  have hpm : 0 < p - 1 := by linarith only [hp]
  have hp0 : 0 < p := by linarith only [hp]
  have hs : 0 < s := Real.sqrt_pos.mpr hpp
  have ht : 0 < t := Real.sqrt_pos.mpr hpm
  have hst : 0 < s * t := mul_pos hs ht
  have hs2 : s ^ 2 = p + 1 := Real.sq_sqrt hpp.le
  have ht2 : t ^ 2 = p - 1 := Real.sq_sqrt hpm.le
  have hpair := laplacePair_sq_le_exponentialMass hH hp s (-t)
  rw [neg_sq, hs2, ht2, div_self hpp.ne', div_self hpm.ne'] at hpair
  let a := ∫ y, H y * Real.exp (y / 2)
  let b := ∫ y, H y * Real.exp (-y / 2)
  change (s * a + -t * b) ^ 2 ≤
    exponentialMass p H * (1 + 2 * s * -t / p + 1) at hpair
  have hplus := sq_nonneg (s * a + t * b)
  rw [← pole_eq_pairings H hH.continuous hH.hasCompactSupport]
  change -((1 / (s * t) - 1 / p) * exponentialMass p H) ≤ 2 * (a * b)
  apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * (s * t) by positivity)).mp
  have hid : 2 * (s * t) * (-((1 / (s * t) - 1 / p) * exponentialMass p H)) =
      -(exponentialMass p H * (1 + 2 * s * -t / p + 1)) := by
    field_simp [hs.ne', ht.ne', hp0.ne']
    ring
  rw [hid]
  nlinarith only [hpair, hplus]

/-- The complete weighted floor after paying the poles jointly. -/
def jointExponentialWeilFloor (p : ℝ) : ℝ :=
  |EF.gammaBracket 0| + 2 * exponentialPrimeMass p + jointExponentialPoleCost p

theorem jointExponentialWeilFloor_pos (hp : 1 < p) : 0 < jointExponentialWeilFloor p :=
  add_pos_of_nonneg_of_pos
    (add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (exponentialPrimeMass_nonneg p)))
    (jointExponentialPoleCost_pos hp)

theorem jointExponentialWeilFloor_lt (hp : 1 < p) :
    jointExponentialWeilFloor p < exponentialWeilFloor p := by
  have h := jointExponentialPoleCost_lt_separate hp
  dsimp only [jointExponentialWeilFloor, exponentialWeilFloor]
  linarith only [h]

/-- Joint pole payment strictly improves the aperture-independent complete floor. -/
theorem weilQuad_ge_neg_jointExponentialMass (hH : IsWindowTest A H) (hp : 1 < p) :
    -(jointExponentialWeilFloor p * exponentialMass p H) ≤ weilQuad H := by
  have hmass := integral_sq_le_exponentialMass hH (by linarith only [hp] : 0 ≤ p)
  have hdiag : -(|EF.gammaBracket 0| * exponentialMass p H) ≤
      EF.gammaBracket 0 * (∫ u, H u ^ 2) := by
    have h₁ := mul_le_mul_of_nonneg_right (neg_abs_le (EF.gammaBracket 0))
      (integral_nonneg (μ := volume) fun u => sq_nonneg (H u))
    have h₂ := mul_le_mul_of_nonneg_left hmass (abs_nonneg (EF.gammaBracket 0))
    linarith only [h₁, h₂]
  have hprime := prime_correlation_sum_le_exponentialMass hH hp (windowLevel A)
  have hpole := pole_ge_neg_jointExponentialMass hH hp
  have hjump : 0 ≤ levyJump H := ENNReal.toReal_nonneg
  have hzero : RHTower.ArchimedeanAnomaly.autocorr H 0 = ∫ u, H u ^ 2 := by
    unfold RHTower.ArchimedeanAnomaly.autocorr
    simp only [add_zero, ← sq]
  have hterm (n : ℕ) : primeJumpWeight n * ∫ u, (H u - H (u + Real.log n)) ^ 2 =
      (2 * primeJumpWeight n) * (∫ u, H u ^ 2) -
        2 * (primeJumpWeight n * ∫ u, H u * H (u + Real.log n)) := by
    rw [RHTower.ArchimedeanAnomaly.integral_sub_shift_sq hH.hasCompactSupport hH.continuous,
      hzero]
    unfold RHTower.ArchimedeanAnomaly.autocorr
    ring
  rw [weilQuad_eq_markovForm_windowLevel hH, markovForm, creationPotential, primeJump]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  dsimp only [jointExponentialWeilFloor]
  nlinarith only [hdiag, hprime, hpole, hjump]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.laplacePair_sq_le_exponentialMass
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.pole_ge_neg_jointExponentialMass
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_neg_jointExponentialMass
