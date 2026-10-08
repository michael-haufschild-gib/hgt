import GaloisForLFunctions.RHTower.WeilPaperCauchyDensity
import GaloisForLFunctions.RHTower.WeilPaperGammaDensity

/-!
# Recoverable integer sampling of the actual Gamma phase energy

The paper's Cauchy lattice bounds and norm-one Gamma reflection work together:
all integer samples form an l1 profile whose mass is comparable to the actual
pole-free energy. The entire profile is recovered from interior data, with a
single recovery scale valid for every integer site and every allowed width.
-/

open Complex Set Filter MeasureTheory Topology
open scoped BigOperators

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity PhaseLockRigidity

/-- Discrete positive measurements of the actual pole-free phase-energy density. -/
def paperGammaCauchyProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (k : ℕ) : ℤ → ℝ :=
  paperCauchyDensitySample (paperGammaOddDensity hW) k

/-- The same measurements obtained solely from an interior vertical line. -/
def paperGammaCauchyInteriorProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (x : ℝ) (k : ℕ) : ℤ → ℝ :=
  paperCauchyDensitySample (paperGammaOddInteriorDensity hW x) k

theorem paperGammaCauchyProfile_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (n : ℤ) : 0 ≤ paperGammaCauchyProfile hW k n :=
  paperCauchyDensitySample_nonneg (paperGammaOddDensity_nonneg hW) k n

theorem summable_paperGammaCauchyProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) : Summable (paperGammaCauchyProfile hW k) :=
  paperCauchyDensitySample_summable_nonneg (integrable_paperGammaOddDensity hW)
    (paperGammaOddDensity_nonneg hW) k

/-- Lower and upper bounds relate the full discrete profile to actual phase energy. -/
theorem paperGammaCauchyProfile_energy_bounds {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) :
    paperCauchyKernel k (1 / 2) * paperGammaEnergy (paperGammaOdd (remainderTrace hW)) ≤
        (∑' n : ℤ, paperGammaCauchyProfile hW k n) ∧
      (∑' n : ℤ, paperGammaCauchyProfile hW k n) ≤
        (2 + Real.pi / ((k : ℝ) + 1)) * paperGammaEnergy (paperGammaOdd (remainderTrace hW)) :=
  ⟨paperCauchyDensitySample_mass_lower (integrable_paperGammaOddDensity hW)
      (paperGammaOddDensity_nonneg hW) k,
    tsum_paperCauchyDensitySample_le (integrable_paperGammaOddDensity hW)
      (paperGammaOddDensity_nonneg hW) k⟩

/-- Sampling does not lose the native reflection-symmetry obstruction. -/
theorem tsum_paperGammaCauchyProfile_eq_zero_iff {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) :
    (∑' n : ℤ, paperGammaCauchyProfile hW k n) = 0 ↔
      ∀ᵐ y : ℝ, remainderTrace hW y / paperPoleGamma y =
        remainderTrace hW (-y) / paperPoleGamma (-y) := by
  rw [← paperGammaEnergy_native_eq_zero_iff hW]
  have hb := paperGammaCauchyProfile_energy_bounds hW k
  have hc : 0 < paperCauchyKernel k (1 / 2) := by unfold paperCauchyKernel; positivity
  have he := paperGammaEnergy_nonneg (paperGammaOdd (remainderTrace hW))
  constructor
  · intro h
    rw [h] at hb
    nlinarith only [hb.1, hc, he]
  · intro h
    exact le_antisymm (by simpa only [h, mul_zero] using hb.2)
      (tsum_nonneg (paperGammaCauchyProfile_nonneg hW k))

theorem summable_paperGammaCauchyInteriorProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    Summable (paperGammaCauchyInteriorProfile hW x k) :=
  paperCauchyDensitySample_summable_nonneg (integrable_paperGammaOddInteriorDensity hW hx hx1)
    (fun _ => sq_nonneg _) k

theorem summable_abs_paperGammaCauchyProfile_error {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    Summable (fun n : ℤ =>
      |paperGammaCauchyInteriorProfile hW x k n - paperGammaCauchyProfile hW k n|) := by
  simpa only [Real.norm_eq_abs] using
    ((summable_paperGammaCauchyInteriorProfile hW hx hx1 k).sub
      (summable_paperGammaCauchyProfile hW k)).norm

/-- Full lattice error is paid by the native density error. -/
theorem tsum_abs_paperGammaCauchyProfile_error_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    (∑' n : ℤ, |paperGammaCauchyInteriorProfile hW x k n - paperGammaCauchyProfile hW k n|) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) *
        ∫ y, |paperGammaOddInteriorDensity hW x y - paperGammaOddDensity hW y| :=
  tsum_abs_paperCauchyDensitySample_sub_le (integrable_paperGammaOddInteriorDensity hW hx hx1)
    (integrable_paperGammaOddDensity hW) k

theorem tsum_abs_paperGammaCauchyProfile_error_le_uniform {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    (∑' n : ℤ, |paperGammaCauchyInteriorProfile hW x k n - paperGammaCauchyProfile hW k n|) ≤
      (2 + Real.pi) *
        ∫ y, |paperGammaOddInteriorDensity hW x y - paperGammaOddDensity hW y| := by
  apply (tsum_abs_paperGammaCauchyProfile_error_le hW hx hx1 k).trans
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => abs_nonneg _)
  have hden : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hpi : Real.pi / ((k : ℝ) + 1) ≤ Real.pi := div_le_self Real.pi_pos.le hden
  simpa only [add_comm] using add_le_add_left hpi 2

/-- The full countable profile is recovered in l1 from actual interior data. -/
theorem tendsto_tsum_abs_paperGammaCauchyProfile_error {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) :
    Tendsto (fun x : ℝ => ∑' n : ℤ,
      |paperGammaCauchyInteriorProfile hW x k n - paperGammaCauchyProfile hW k n|)
      (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => tsum_nonneg fun _ => abs_nonneg _) ?_
    (by simpa using (tendsto_integral_abs_paperGammaOddDensity_sub hW).const_mul (2 + Real.pi))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with x (hx : 0 < x) hx1
  exact tsum_abs_paperGammaCauchyProfile_error_le_uniform hW hx hx1.le k

/-- A single recovery scale works for every lattice width and all integer sites together. -/
theorem eventually_uniform_paperGammaCauchyProfile_recovery {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ k : ℕ,
      (∑' n : ℤ, |paperGammaCauchyInteriorProfile hW x k n -
        paperGammaCauchyProfile hW k n|) < ε := by
  have ht : Tendsto (fun x : ℝ => (2 + Real.pi) *
      ∫ y, |paperGammaOddInteriorDensity hW x y - paperGammaOddDensity hW y|)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_integral_abs_paperGammaOddDensity_sub hW).const_mul (2 + Real.pi)
  filter_upwards [ht.eventually (eventually_lt_nhds hε), self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with x hsmall (hx : 0 < x) hx1
  exact fun k => (tsum_abs_paperGammaCauchyProfile_error_le_uniform hW hx hx1.le k).trans_lt hsmall

end RHTower.WeilWorkSettledPhase
