import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeWindows
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowGeneralMoment

/-!
# Polynomial terminal contrasts retain a signed logarithmic moment

Adjacent intervals between consecutive powers of one integer have equal
leading harmonic mass. Their exactly balanced contrast has physical square
`2/(a+2)` and first logarithmic moment one after division by `log(X)^2`.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory ArithmeticEffectivityTheory
open CompletedArithmeticForms
open _root_.RHTower.Sieve

/-- Polynomial endpoints read every harmonic logarithmic moment without floor errors. -/
theorem tendsto_primeCharge_logMoment_power (m : ℕ) {a : ℕ} (ha : 0 < a) :
    Tendsto (fun X : ℕ => harmonicLogWindowMoment m 0 (X ^ a) / Real.log X ^ (m + 1))
      atTop (𝓝 ((a : ℝ) ^ (m + 1) / ((m : ℝ) + 1))) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hbase := (tendsto_harmonicLogWindowMoment_natDiv_div_log_pow m
    (c := 1) zero_lt_one).comp hXa
  simp only [Nat.div_one, Function.comp_def] at hbase
  have h : Tendsto (fun X : ℕ => (a : ℝ) ^ (m + 1) *
      (harmonicLogWindowMoment m 0 (X ^ a) / Real.log (X ^ a : ℕ) ^ (m + 1)))
      atTop (𝓝 ((a : ℝ) ^ (m + 1) / ((m : ℝ) + 1))) := by
    simpa only [mul_one_div] using hbase.const_mul ((a : ℝ) ^ (m + 1))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hL : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  rw [Nat.cast_pow, Real.log_pow, mul_pow]
  field_simp [haR, hL]

/-- Subtracting prefix moments gives the exact polynomial-window coefficient. -/
theorem tendsto_primeCharge_logMoment_window (m : ℕ) {a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun X : ℕ => harmonicLogWindowMoment m (X ^ a) (X ^ b) /
      Real.log X ^ (m + 1)) atTop
        (𝓝 (((b : ℝ) ^ (m + 1) - (a : ℝ) ^ (m + 1)) / ((m : ℝ) + 1))) := by
  have h := (tendsto_primeCharge_logMoment_power m (ha.trans_le hab)).sub
    (tendsto_primeCharge_logMoment_power m ha)
  simp only [← sub_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hs := harmonicLogWindowMoment_add m (A := 0) (B := X ^ a) (C := X ^ b)
    (Nat.zero_le _) (Nat.pow_le_pow_right hX hab)
  congr 1
  linarith only [hs]

/-- Each adjacent polynomial window has one logarithm of harmonic mass. -/
theorem tendsto_primeChargeWindowMass_adjacent {a : ℕ} (ha : 0 < a) :
    Tendsto (fun X : ℕ => primeChargeWindowMass (X ^ a) (X ^ (a + 1)) / Real.log X)
      atTop (𝓝 1) := by
  have h := tendsto_primeCharge_logMoment_window 0 ha (by omega : a ≤ a + 1)
  simpa only [harmonicLogWindowMoment, pow_zero, Nat.zero_add, pow_one,
    primeChargeWindowMass, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    zero_add, add_sub_cancel_left, div_one] using h

/-- The exact balancing ratio tends to one on adjacent polynomial windows. -/
theorem tendsto_primeChargeWindowRatio {a : ℕ} (ha : 0 < a) :
    Tendsto (fun X : ℕ =>
      primeChargeWindowMass (X ^ (a + 1)) (X ^ (a + 2)) /
        primeChargeWindowMass (X ^ a) (X ^ (a + 1))) atTop (𝓝 1) := by
  have hupper := tendsto_primeChargeWindowMass_adjacent (show 0 < a + 1 by omega)
  have hlower := tendsto_primeChargeWindowMass_adjacent ha
  have h := hupper.div hlower (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_div_one, show a + 1 + 1 = a + 2 by omega] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hL : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  rw [Pi.div_apply]
  by_cases hmass : primeChargeWindowMass (X ^ a) (X ^ (a + 1)) = 0
  · simp only [hmass, zero_div, div_zero]
  · field_simp [hL, hmass]

/-- The exactly neutral terminal contrast has positive limiting physical norm. -/
theorem tendsto_primeChargeWindowVector_norm_sq {a : ℕ} (ha : 0 < a) :
    Tendsto (fun X : ℕ =>
      ‖primeChargeWindowVector (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) (X ^ (a + 2))‖ ^ 2)
      atTop (𝓝 (2 / ((a : ℝ) + 2))) := by
  have hupper := tendsto_primeChargeWindowMass_adjacent (show 0 < a + 1 by omega)
  simp only [show a + 1 + 1 = a + 2 by omega] at hupper
  have h := (hupper.add ((tendsto_primeChargeWindowRatio ha).pow 2 |>.mul
    (tendsto_primeChargeWindowMass_adjacent ha))).div_const ((a : ℝ) + 2)
  norm_num only [one_pow, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [primeChargeWindowVector_norm_sq
    (Nat.pow_le_pow_right (by omega) (by omega : a + 1 ≤ a + 2)) le_rfl,
    Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_ofNat]
  rw [mul_comm ((a : ℝ) + 2), div_mul_eq_div_div]
  congr 1
  ring

/-- The first logarithmic moment of the neutral contrast retains a nonzero signed receiver. -/
theorem tendsto_primeChargeWindowContrast_log_pairing {a : ℕ} (ha : 0 < a) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Icc 1 (X ^ (a + 2)),
        primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n *
          (Real.log n / (n : ℝ))) / Real.log X ^ 2) atTop (𝓝 1) := by
  have hupper := tendsto_primeCharge_logMoment_window 1
    (show 0 < a + 1 by omega) (show a + 1 ≤ a + 2 by omega)
  have hlower := tendsto_primeCharge_logMoment_window 1 ha (show a ≤ a + 1 by omega)
  have h := hupper.sub ((tendsto_primeChargeWindowRatio ha).mul hlower)
  norm_num only [Nat.cast_one, Nat.cast_add, Nat.cast_ofNat] at h
  have he : (((a : ℝ) + 2) ^ 2 - ((a : ℝ) + 1) ^ 2) / 2 -
      1 * ((((a : ℝ) + 1) ^ 2 - (a : ℝ) ^ 2) / 2) = 1 := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [primeChargeWindowContrast_sum
    (Nat.pow_le_pow_right hX (show a + 1 ≤ a + 2 by omega)) le_rfl]
  simp only [harmonicLogWindowMoment, pow_one]
  ring

/-- The terminal contrast loses no limiting mass when projected off all conductors through `X²`. -/
theorem tendsto_primeChargeTerminal_projection_norm_sq :
    Tendsto (fun X : ℕ =>
      ‖(conductorSubspace (X ^ 2) (X ^ 40)).starProjection
        (primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40))‖ ^ 2)
      atTop (𝓝 0) := by
  have hk := tendsto_primeChargeWindowRatio (a := 38) (by omega)
  have hp : Tendsto (fun X : ℕ => (X : ℝ) ^ 70) atTop atTop :=
    (tendsto_pow_atTop (by omega : (70 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add hk.abs).pow 2).mul
    (hp.const_div_atTop 128)
  simp only [mul_zero] at hlim
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hlog.eventually (eventually_ge_atTop 5)] with X hX hL
  change 5 ≤ Real.log (X : ℝ) at hL
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hQ : 2 ≤ X ^ 2 := hX.trans (Nat.le_pow (by omega : 0 < 2))
  have hQN : X ^ 2 * X ^ 2 ≤ X ^ 40 := by
    calc
      _ = X ^ 4 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega : 4 ≤ 40)
  have hframe : 18 * (1 + Real.log (X ^ 2 : ℕ)) ≤ Real.log (X ^ 40 : ℕ) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    linarith only [hL]
  have hb := primeChargeWindowVector_projection_sq_le hQ hQN hframe
    (Nat.pow_lt_pow_right (by omega) (by omega : 38 < 39))
    (Nat.pow_le_pow_right (by omega) (by omega : 39 ≤ 40)) le_rfl
  have hL40 : 1 ≤ Real.log (X ^ 40 : ℕ) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    linarith only [hL]
  have hA : (X : ℝ) ^ 76 ≤ ((X : ℝ) ^ 38 + 1) ^ 2 := by
    have he : (X : ℝ) ^ 76 = ((X : ℝ) ^ 38) ^ 2 := by ring
    rw [he]
    nlinarith only [pow_nonneg hXR.le 38]
  have hden : (X : ℝ) ^ 76 ≤ ((X : ℝ) ^ 38 + 1) ^ 2 * Real.log (X ^ 40 : ℕ) ^ 2 := by
    calc
      _ ≤ ((X : ℝ) ^ 38 + 1) ^ 2 := hA
      _ = ((X : ℝ) ^ 38 + 1) ^ 2 * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (show 1 ≤ Real.log (X ^ 40 : ℕ) ^ 2 by
        nlinarith only [hL40]) (sq_nonneg _)
  simp only [Nat.cast_pow] at hb hden
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine hb.trans ((div_le_div_of_nonneg_left (by positivity) (pow_pos hXR 76) hden).trans_eq ?_)
  change _ = (1 + |primeChargeWindowMass (X ^ 39) (X ^ 40) /
    primeChargeWindowMass (X ^ 38) (X ^ 39)|) ^ 2 * (128 / (X : ℝ) ^ 70)
  field_simp [hXR.ne']

theorem tendsto_primeChargeTerminal_projection_norm :
    Tendsto (fun X : ℕ =>
      ‖(conductorSubspace (X ^ 2) (X ^ 40)).starProjection
        (primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40))‖)
      atTop (𝓝 0) := by
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    tendsto_primeChargeTerminal_projection_norm_sq.sqrt

/-- The exact complementary part of a finite terminal contrast. -/
def primeChargeWindowComplement (Q A B C N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  primeChargeWindowVector A B C N -
    (conductorSubspace Q N).starProjection (primeChargeWindowVector A B C N)

theorem primeChargeWindowComplement_mem (Q A B C N : ℕ) :
    primeChargeWindowComplement Q A B C N ∈ (conductorSubspace Q N)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

theorem primeChargeWindowComplement_norm_sq (Q A B C N : ℕ) :
    ‖primeChargeWindowComplement Q A B C N‖ ^ 2 =
      ‖primeChargeWindowVector A B C N‖ ^ 2 -
        ‖(conductorSubspace Q N).starProjection (primeChargeWindowVector A B C N)‖ ^ 2 := by
  have h := norm_starProjection_sq_add_sub_sq (conductorSubspace Q N)
    (primeChargeWindowVector A B C N)
  change _ + ‖primeChargeWindowComplement Q A B C N‖ ^ 2 = _ at h
  linarith only [h]

/-- An explicit receiver in the exact growing conductor complement. -/
def primeChargeTerminalReceiver (X : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex (X ^ 40)) :=
  primeChargeWindowComplement (X ^ 2) (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)

theorem primeChargeTerminalReceiver_mem (X : ℕ) :
    primeChargeTerminalReceiver X ∈ (conductorSubspace (X ^ 2) (X ^ 40))ᗮ :=
  primeChargeWindowComplement_mem (X ^ 2) (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)

/-- The exact complement retains the contrast's positive limiting mass. -/
theorem tendsto_primeChargeTerminalReceiver_norm_sq :
    Tendsto (fun X : ℕ => ‖primeChargeTerminalReceiver X‖ ^ 2) atTop (𝓝 (1 / 20 : ℝ)) := by
  have hz : Tendsto (fun X : ℕ =>
      ‖primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)‖ ^ 2)
      atTop (𝓝 (1 / 20 : ℝ)) := by
    convert tendsto_primeChargeWindowVector_norm_sq (a := 38) (by omega) using 1
    norm_num
  simpa only [primeChargeTerminalReceiver, primeChargeWindowComplement_norm_sq, sub_zero] using
    hz.sub tendsto_primeChargeTerminal_projection_norm_sq

theorem eventually_primeChargeTerminalReceiver_norm_le_one :
    ∀ᶠ X : ℕ in atTop, ‖primeChargeTerminalReceiver X‖ ≤ 1 := by
  filter_upwards [tendsto_primeChargeTerminalReceiver_norm_sq.eventually
    (ge_mem_nhds (by norm_num : (1 / 20 : ℝ) < 1))] with X hX
  nlinarith only [hX, norm_nonneg (primeChargeTerminalReceiver X)]

#print axioms tendsto_primeChargeWindowVector_norm_sq
#print axioms tendsto_primeChargeWindowContrast_log_pairing
#print axioms tendsto_primeChargeTerminalReceiver_norm_sq
#print axioms primeChargeTerminalReceiver_mem

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
