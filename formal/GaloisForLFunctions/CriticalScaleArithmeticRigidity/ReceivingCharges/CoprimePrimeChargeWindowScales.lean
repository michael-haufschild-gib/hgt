import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeWindows
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeWindowScales

/-!
# Fixed receiving modes survive a growing conductor projection

Multiplying the terminal contrast by a fixed normalized conductor changes
its square only by an endpoint error. Projection off all conductors through
`R X²`, for any fixed positive `R`, removes asymptotically no mass.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory ArithmeticEffectivityTheory CompletedArithmeticForms

/-- The conductor component removed from a fixed-mode terminal contrast. -/
def fibreChargeTerminalProjection (m R X : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex (X ^ 40)) :=
  (conductorSubspace (R * X ^ 2) (X ^ 40)).starProjection
    (fibreChargeWindowVector m (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40))

/-- A fixed receiving mode has the same terminal contrast square as the scalar mode. -/
theorem tendsto_fibreChargeTerminal_window_norm_sq {m : ℕ} (hm : 0 < m) :
    Tendsto (fun X : ℕ =>
      ‖fibreChargeWindowVector m (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)‖ ^ 2)
      atTop (𝓝 (1 / 20 : ℝ)) := by
  have hk := tendsto_primeChargeWindowRatio (a := 38) (by omega)
  have hp : Tendsto (fun X : ℕ => (X : ℝ) ^ 38) atTop atTop :=
    (tendsto_pow_atTop (by omega : (38 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).add (hk.pow 2)).mul
    (hp.const_div_atTop (8 * (m : ℝ) ^ 2))
  simp only [mul_zero] at hlim
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff : Tendsto (fun X : ℕ =>
      ‖fibreChargeWindowVector m (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)‖ ^ 2 -
        ‖primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)‖ ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 2, hlog.eventually (eventually_ge_atTop 1)] with X hX hL
    change 1 ≤ Real.log (X : ℝ) at hL
    have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hL40 : 1 ≤ Real.log (X ^ 40 : ℕ) := by
      simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
      linarith only [hL]
    have hb := abs_fibreChargeWindowVector_norm_sq_sub_le hm
      (Nat.pow_le_pow_right (by omega) (by omega : 38 ≤ 39))
      (Nat.pow_le_pow_right (by omega) (by omega : 39 ≤ 40)) le_rfl
      (zero_lt_one.trans_le hL40)
    have hden : (X : ℝ) ^ 38 ≤ ((X : ℝ) ^ 38 + 1) * Real.log (X ^ 40 : ℕ) := by
      have h := mul_le_mul_of_nonneg_left hL40
        (show 0 ≤ (X : ℝ) ^ 38 + 1 by positivity)
      linarith only [h]
    rw [Real.norm_eq_abs]
    simp only [Nat.cast_pow] at hb
    simp only [Nat.cast_pow] at hden
    have hfrac :
        8 * (m : ℝ) ^ 2 *
            (1 + (primeChargeWindowMass (X ^ 39) (X ^ 40) /
              primeChargeWindowMass (X ^ 38) (X ^ 39)) ^ 2) /
            (((X : ℝ) ^ 38 + 1) * Real.log ((X : ℝ) ^ 40)) ≤
          8 * (m : ℝ) ^ 2 *
            (1 + (primeChargeWindowMass (X ^ 39) (X ^ 40) /
              primeChargeWindowMass (X ^ 38) (X ^ 39)) ^ 2) / (X : ℝ) ^ 38 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hXR 38) hden
    exact hb.trans (hfrac.trans_eq (by ring))
  have hz : Tendsto (fun X : ℕ =>
      ‖primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)‖ ^ 2)
      atTop (𝓝 (1 / 20 : ℝ)) := by
    convert tendsto_primeChargeWindowVector_norm_sq (a := 38) (by omega) using 1
    norm_num
  have h := hdiff.add hz
  simpa only [sub_add_cancel, zero_add] using h

/-- Every fixed multiple of the prime cutoff removes vanishing mass from the fibre contrast. -/
theorem tendsto_fibreChargeTerminal_projection_norm_sq {m R : ℕ}
    (hm : 0 < m) (hR : 0 < R) :
    Tendsto (fun X : ℕ =>
      ‖fibreChargeTerminalProjection m R X‖ ^ 2)
      atTop (𝓝 0) := by
  have hk := tendsto_primeChargeWindowRatio (a := 38) (by omega)
  have hp : Tendsto (fun X : ℕ => (X : ℝ) ^ 70) atTop atTop :=
    (tendsto_pow_atTop (by omega : (70 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add hk.abs).pow 2).mul
    (hp.const_div_atTop (128 * (m : ℝ) ^ 2 * (R : ℝ) ^ 3))
  simp only [mul_zero] at hlim
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop R,
    hlog.eventually (eventually_ge_atTop (5 * (1 + Real.log R)))] with X hX hRX hL
  change 5 * (1 + Real.log R) ≤ Real.log (X : ℝ) at hL
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hL5 : 5 ≤ Real.log (X : ℝ) := by
    linarith only [hL, Real.log_natCast_nonneg R]
  have hQ : 2 ≤ R * X ^ 2 := by
    calc
      2 ≤ X ^ 2 := hX.trans (Nat.le_pow (by omega : 0 < 2))
      _ = 1 * X ^ 2 := by rw [one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ hR
  have hcut : R * X ^ 2 ≤ X ^ 3 := by
    calc
      _ ≤ X * X ^ 2 := Nat.mul_le_mul_right _ hRX
      _ = _ := by ring
  have hQN : (R * X ^ 2) * (R * X ^ 2) ≤ X ^ 40 := by
    calc
      _ ≤ X ^ 3 * X ^ 3 := Nat.mul_le_mul hcut hcut
      _ = X ^ 6 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega : 6 ≤ 40)
  have hframe : 18 * (1 + Real.log (R * X ^ 2 : ℕ)) ≤ Real.log (X ^ 40 : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hRR.ne' (pow_ne_zero 2 hXR.ne')]
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    linarith only [hL, Real.log_natCast_nonneg R]
  have hb := fibreChargeWindowVector_projection_sq_le hm hQ hQN hframe
    (Nat.pow_lt_pow_right (by omega) (by omega : 38 < 39))
    (Nat.pow_le_pow_right (by omega) (by omega : 39 ≤ 40)) le_rfl
  have hL40 : 1 ≤ Real.log (X ^ 40 : ℕ) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    linarith only [hL5]
  have hA : (X : ℝ) ^ 76 ≤ ((X : ℝ) ^ 38 + 1) ^ 2 := by
    have he : (X : ℝ) ^ 76 = ((X : ℝ) ^ 38) ^ 2 := by ring
    rw [he]
    nlinarith only [pow_nonneg hXR.le 38]
  have hden : (X : ℝ) ^ 76 ≤ ((X : ℝ) ^ 38 + 1) ^ 2 * Real.log (X ^ 40 : ℕ) ^ 2 := by
    calc
      _ ≤ ((X : ℝ) ^ 38 + 1) ^ 2 := hA
      _ = ((X : ℝ) ^ 38 + 1) ^ 2 * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (show 1 ≤ Real.log (X ^ 40 : ℕ) ^ 2 by nlinarith only [hL40]) (sq_nonneg _)
  simp only [Nat.cast_pow, Nat.cast_mul] at hb
  simp only [Nat.cast_pow] at hden
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hfrac :
      128 * (m : ℝ) ^ 2 * ((R : ℝ) * (X : ℝ) ^ 2) ^ 3 *
          (1 + |primeChargeWindowMass (X ^ 39) (X ^ 40) /
            primeChargeWindowMass (X ^ 38) (X ^ 39)|) ^ 2 /
          (((X : ℝ) ^ 38 + 1) ^ 2 * Real.log ((X : ℝ) ^ 40) ^ 2) ≤
        128 * (m : ℝ) ^ 2 * ((R : ℝ) * (X : ℝ) ^ 2) ^ 3 *
          (1 + |primeChargeWindowMass (X ^ 39) (X ^ 40) /
            primeChargeWindowMass (X ^ 38) (X ^ 39)|) ^ 2 / (X : ℝ) ^ 76 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hXR 76) hden
  refine hb.trans (hfrac.trans_eq ?_)
  change _ = (1 + |primeChargeWindowMass (X ^ 39) (X ^ 40) /
    primeChargeWindowMass (X ^ 38) (X ^ 39)|) ^ 2 *
      ((128 * (m : ℝ) ^ 2 * (R : ℝ) ^ 3) / (X : ℝ) ^ 70)
  field_simp [hXR.ne']

theorem tendsto_fibreChargeTerminal_projection_norm {m R : ℕ}
    (hm : 0 < m) (hR : 0 < R) :
    Tendsto (fun X : ℕ =>
      ‖fibreChargeTerminalProjection m R X‖)
      atTop (𝓝 0) := by
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (tendsto_fibreChargeTerminal_projection_norm_sq hm hR).sqrt

/-- The complementary part of a receiving-mode contrast at an arbitrary cutoff. -/
def fibreChargeWindowComplement (m Q A B C N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  fibreChargeWindowVector m A B C N -
    (conductorSubspace Q N).starProjection (fibreChargeWindowVector m A B C N)

theorem fibreChargeWindowComplement_mem (m Q A B C N : ℕ) :
    fibreChargeWindowComplement m Q A B C N ∈ (conductorSubspace Q N)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

theorem fibreChargeWindowComplement_norm_sq (m Q A B C N : ℕ) :
    ‖fibreChargeWindowComplement m Q A B C N‖ ^ 2 =
      ‖fibreChargeWindowVector m A B C N‖ ^ 2 -
        ‖(conductorSubspace Q N).starProjection (fibreChargeWindowVector m A B C N)‖ ^ 2 := by
  have h := norm_starProjection_sq_add_sub_sq (conductorSubspace Q N)
    (fibreChargeWindowVector m A B C N)
  change _ + ‖fibreChargeWindowComplement m Q A B C N‖ ^ 2 = _ at h
  linarith only [h]

/-- A fixed receiving mode projected off the common growing conductor cutoff. -/
def fibreChargeTerminalReceiver (m R X : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex (X ^ 40)) :=
  fibreChargeWindowComplement m (R * X ^ 2) (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)

theorem fibreChargeTerminalReceiver_mem (m R X : ℕ) :
    fibreChargeTerminalReceiver m R X ∈ (conductorSubspace (R * X ^ 2) (X ^ 40))ᗮ :=
  fibreChargeWindowComplement_mem m (R * X ^ 2) (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)

/-- Every fixed receiving mode retains the same positive mass in the exact complement. -/
theorem tendsto_fibreChargeTerminalReceiver_norm_sq {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    Tendsto (fun X : ℕ => ‖fibreChargeTerminalReceiver m R X‖ ^ 2)
      atTop (𝓝 (1 / 20 : ℝ)) := by
  simpa only [fibreChargeTerminalReceiver, fibreChargeWindowComplement_norm_sq,
    fibreChargeTerminalProjection, sub_zero] using
    (tendsto_fibreChargeTerminal_window_norm_sq hm).sub
      (tendsto_fibreChargeTerminal_projection_norm_sq hm hR)

theorem eventually_fibreChargeTerminalReceiver_norm_le_one {m R : ℕ}
    (hm : 0 < m) (hR : 0 < R) :
    ∀ᶠ X : ℕ in atTop, ‖fibreChargeTerminalReceiver m R X‖ ≤ 1 := by
  filter_upwards [(tendsto_fibreChargeTerminalReceiver_norm_sq hm hR).eventually
    (ge_mem_nhds (by norm_num : (1 / 20 : ℝ) < 1))] with X hX
  nlinarith only [hX, norm_nonneg (fibreChargeTerminalReceiver m R X)]

#print axioms tendsto_fibreChargeTerminalReceiver_norm_sq
#print axioms fibreChargeTerminalReceiver_mem

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
