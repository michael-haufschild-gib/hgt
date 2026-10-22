import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteSourceCovariance
import GaloisForLFunctions.RHTower.CCM.CCMFiniteSourceRemainder

open Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The literal source divided by the actual prescribed interval shift. -/
def ccmSourceShiftProfile (a : SuzukiPositiveAperture) (p : suzukiApertureHilbert a) :
    suzukiApertureHilbert a :=
  (((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a))⁻¹ : ℝ) : ℂ) • p

/-- The finite inverse has a source-uniform explicit physical profile. -/
theorem eventually_ccmFiniteNeumannVector_source_profile
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ p : suzukiApertureHilbert ⟨a, ha⟩, ∀ V : ℝ,
      ‖p‖ ≤ V → CCMFiniteExponentialBudget (p : SoninL2) V →
      Real.exp (2 * a) * ‖ccmFiniteNeumannVector ⟨a, ha⟩ p ⌈a⌉₊ -
        ccmSourceShiftProfile ⟨a, ha⟩ p‖ ^ 2 ≤ ε * V ^ 2 := by
  obtain ⟨M, E, _, hE, happ⟩ := eventually_ccmFiniteExponentialSource_neumann_decay
  filter_upwards [happ,
    eventually_ccmFiniteNeumannVector_remainder_norm (ε / 32) (by positivity),
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (32 * E ^ 2 / ε))]
    with a haApp haB haScale
  intro ha p V hpNorm hpBudget
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let u := ccmFiniteNeumannVector ap p ⌈a⌉₊
  let q := ccmSourceShiftProfile ap p
  let B := ccmRestrictedWeilBoundedRemainder ap
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
  let r := p - ccmShiftedBoundedWeil ap u
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hq : (c : ℂ) • q = p := by
    change (c : ℂ) • (((c⁻¹ : ℝ) : ℂ) • p) = p
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
  have hrEq : r = p - ((c : ℂ) • u + B u) := rfl
  have hvector : (c : ℂ) • (u - q) = -(B u + r) := by
    rw [smul_sub, hq, hrEq]
    module
  have hnorm : c * ‖u - q‖ ≤ ‖B u‖ + ‖r‖ := by
    calc
      _ = ‖(c : ℂ) • (u - q)‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      _ = ‖B u + r‖ := by rw [hvector, norm_neg]
      _ ≤ _ := norm_add_le _ _
  have hlower : Real.exp a * ‖u - q‖ ≤ 2 * (‖B u‖ + ‖r‖) := by
    have hs := mul_le_mul_of_nonneg_right
      (exp_aperture_le_twice_suzukiWeilIntervalShift ap) (norm_nonneg (u - q))
    change Real.exp a * ‖u - q‖ ≤ (2 * c) * ‖u - q‖ at hs
    nlinarith only [hs, hnorm]
  have hsquare : (Real.exp a) ^ 2 * ‖u - q‖ ^ 2 ≤ 8 * (‖B u‖ ^ 2 + ‖r‖ ^ 2) := by
    have hs := mul_self_le_mul_self
      (mul_nonneg (Real.exp_pos a).le (norm_nonneg (u - q))) hlower
    nlinarith only [hs, sq_nonneg (‖B u‖ - ‖r‖)]
  have hr2 : ‖r‖ ^ 2 ≤ E ^ 2 * V ^ 2 * Real.exp (-a) := by
    have hr := (haApp ha p V hpNorm hpBudget).2
    have hs := mul_self_le_mul_self (norm_nonneg r) hr
    have he : (Real.exp (-4 * a)) ^ 2 = Real.exp (-8 * a) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ (E * V * Real.exp (-4 * a)) ^ 2 := by
        change ‖r‖ * ‖r‖ ≤ (E * V * Real.exp (-4 * a)) * (E * V * Real.exp (-4 * a)) at hs
        nlinarith only [hs]
      _ = E ^ 2 * V ^ 2 * Real.exp (-8 * a) := by rw [mul_pow, mul_pow, he]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hexp : Real.exp (-a) * Real.exp a = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hrSmall : ‖r‖ ^ 2 ≤ (ε / 32) * V ^ 2 := by
    have hs : E ^ 2 ≤ (ε / 32) * Real.exp a := by
      have ht := (div_le_iff₀ hε).1 haScale
      nlinarith only [ht]
    calc
      _ ≤ E ^ 2 * V ^ 2 * Real.exp (-a) := hr2
      _ ≤ ((ε / 32) * Real.exp a) * V ^ 2 * Real.exp (-a) := by
        gcongr
      _ = (ε / 32) * V ^ 2 * (Real.exp (-a) * Real.exp a) := by ring
      _ = (ε / 32) * V ^ 2 := by rw [hexp, mul_one]
  have hB : ‖B u‖ ^ 2 ≤ (ε / 32) * V ^ 2 := haB ha p V hpNorm hpBudget
  have he : (Real.exp a) ^ 2 = Real.exp (2 * a) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he] at hsquare
  change Real.exp (2 * a) * ‖u - q‖ ^ 2 ≤ ε * V ^ 2
  nlinarith only [hsquare, hrSmall, hB, sq_nonneg V, hε]

/-- Uniform explicit profile of the actual completed covariance response.
Admission conditions are checked at the source; no condition on the unknown
response or its Fourier tail is assumed. -/
theorem eventually_suzukiTaSourceResponse_source_profile
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ p : suzukiApertureHilbert ⟨a, ha⟩, ∀ V : ℝ,
      ‖p‖ ≤ V → CCMFiniteExponentialBudget (p : SoninL2) V →
      Real.exp (2 * a) * ‖ccmArchimedeanFormToAperture ⟨a, ha⟩
        (suzukiTaToFormCLM ⟨a, ha⟩ (suzukiTaSourceResponse ⟨a, ha⟩ p)) -
          ccmSourceShiftProfile ⟨a, ha⟩ p‖ ^ 2 ≤ ε * V ^ 2 := by
  filter_upwards [eventually_ccmFiniteNeumannVector_source_profile (ε / 4) (by positivity),
    eventually_suzukiTaSourceResponse_neumann_relative_error (ε / 4) (by positivity)]
    with a haU haF
  intro ha p V hpNorm hpBudget
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let f := ccmArchimedeanFormToAperture ap (suzukiTaToFormCLM ap (suzukiTaSourceResponse ap p))
  let u := ccmFiniteNeumannVector ap p ⌈a⌉₊
  let q := ccmSourceShiftProfile ap p
  have hnorm : ‖f - q‖ ≤ ‖f - u‖ + ‖u - q‖ := by
    calc
      _ = ‖(f - u) + (u - q)‖ := congrArg norm (by abel)
      _ ≤ _ := norm_add_le _ _
  have hsquare : ‖f - q‖ ^ 2 ≤ 2 * ‖f - u‖ ^ 2 + 2 * ‖u - q‖ ^ 2 := by
    have hs := mul_self_le_mul_self (norm_nonneg (f - q)) hnorm
    nlinarith only [hs, sq_nonneg (‖f - u‖ - ‖u - q‖)]
  have hscaled := mul_le_mul_of_nonneg_left hsquare (Real.exp_pos (2 * a)).le
  have hu : Real.exp (2 * a) * ‖u - q‖ ^ 2 ≤ (ε / 4) * V ^ 2 := haU ha p V hpNorm hpBudget
  have hf : Real.exp (2 * a) * ‖f - u‖ ^ 2 ≤ (ε / 4) * V ^ 2 := haF ha p V hpNorm hpBudget
  change Real.exp (2 * a) * ‖f - q‖ ^ 2 ≤ ε * V ^ 2
  nlinarith only [hscaled, hu, hf]

/-- The same uniform profile stated directly for the existing interval covariance. -/
theorem eventually_suzukiWeilIntervalCovariance_source_profile
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ p : suzukiApertureHilbert ⟨a, ha⟩, ∀ V : ℝ,
      ‖p‖ ≤ V → CCMFiniteExponentialBudget (p : SoninL2) V →
      Real.exp (2 * a) * ‖suzukiWeilIntervalCovariance ⟨a, ha⟩
        ((suzukiApertureL2Equiv ⟨a, ha⟩).symm p) -
        (suzukiApertureL2Equiv ⟨a, ha⟩).symm (ccmSourceShiftProfile ⟨a, ha⟩ p)‖ ^ 2 ≤ ε * V ^ 2 := by
  filter_upwards [eventually_suzukiTaSourceResponse_source_profile ε hε] with a haProfile
  intro ha p V hpNorm hpBudget
  have h := haProfile ha p V hpNorm hpBudget
  have hn : ‖suzukiWeilIntervalCovariance ⟨a, ha⟩
      ((suzukiApertureL2Equiv ⟨a, ha⟩).symm p) -
      (suzukiApertureL2Equiv ⟨a, ha⟩).symm (ccmSourceShiftProfile ⟨a, ha⟩ p)‖ =
      ‖ccmArchimedeanFormToAperture ⟨a, ha⟩
        (suzukiTaToFormCLM ⟨a, ha⟩ (suzukiTaSourceResponse ⟨a, ha⟩ p)) -
          ccmSourceShiftProfile ⟨a, ha⟩ p‖ := by
    rw [← suzukiTaPhysicalEmbedding_sourceResponse]
    change ‖(suzukiApertureL2Equiv ⟨a, ha⟩).symm _ -
      (suzukiApertureL2Equiv ⟨a, ha⟩).symm _‖ = _
    rw [← map_sub, (suzukiApertureL2Equiv ⟨a, ha⟩).symm.norm_map]
    rfl
  rwa [hn]

end RHTower
end
