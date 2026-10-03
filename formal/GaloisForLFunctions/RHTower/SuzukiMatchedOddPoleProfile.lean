import GaloisForLFunctions.RHTower.CCMFiniteNeumannRemainderQuadratic
import GaloisForLFunctions.RHTower.SuzukiMatchedOddNeumannApproximation

open Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The literal odd pole source divided by the actual prescribed shift. -/
def ccmMatchedOddPoleProfile (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  (((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a))⁻¹ : ℝ) : ℂ) •
    ccmMatchedOddPoleSource a

/-- The canonical finite Neumann vector converges to its literal pole-source
profile in the naturally rescaled physical norm. -/
theorem eventually_ccmMatchedOddNeumannVector_pole_profile
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      Real.exp a * ‖ccmMatchedOddNeumannVector ⟨a, ha⟩ ⌈a⌉₊ -
        ccmMatchedOddPoleProfile ⟨a, ha⟩‖ ^ 2 < ε := by
  obtain ⟨M, E, _, hE, happ⟩ := eventually_ccmMatchedOddPoleSource_neumann_decay
  filter_upwards [happ,
    eventually_ccmMatchedOddNeumannVector_scaled_remainder_norm (ε / 32) (by positivity),
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (32 * E ^ 2 / ε))]
    with a haApp haB haScale
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let u := ccmMatchedOddNeumannVector ap ⌈a⌉₊
  let p := ccmMatchedOddPoleSource ap
  let q := ccmMatchedOddPoleProfile ap
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
  have hexp : Real.exp (-a) * Real.exp a = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hrE : ‖r‖ ≤ E := by
    calc
      _ ≤ E * Real.exp (-7 * a / 2) := (haApp ha).2
      _ ≤ E * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (by linarith)) hE.le
      _ = E := mul_one _
  have hr2 : ‖r‖ ^ 2 ≤ E ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg r) hrE
  have hrSmall : Real.exp (-a) * ‖r‖ ^ 2 ≤ ε / 32 := by
    have hs : E ^ 2 ≤ (ε / 32) * Real.exp a := by
      have ht := (div_le_iff₀ hε).1 haScale
      nlinarith only [ht]
    calc
      _ ≤ Real.exp (-a) * E ^ 2 := mul_le_mul_of_nonneg_left hr2 (Real.exp_pos _).le
      _ ≤ Real.exp (-a) * ((ε / 32) * Real.exp a) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = (ε / 32) * (Real.exp (-a) * Real.exp a) := by ring
      _ = ε / 32 := by rw [hexp, mul_one]
  have hB : Real.exp (-a) * ‖B u‖ ^ 2 < ε / 32 := haB ha
  calc
    _ = Real.exp (-a) * ((Real.exp a) ^ 2 * ‖u - q‖ ^ 2) := by
      rw [show Real.exp (-a) * ((Real.exp a) ^ 2 * ‖u - q‖ ^ 2) =
        (Real.exp (-a) * Real.exp a) * (Real.exp a * ‖u - q‖ ^ 2) by ring, hexp, one_mul]
    _ ≤ Real.exp (-a) * (8 * (‖B u‖ ^ 2 + ‖r‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hsquare (Real.exp_pos _).le
    _ = 8 * (Real.exp (-a) * ‖B u‖ ^ 2 + Real.exp (-a) * ‖r‖ ^ 2) := by ring
    _ < ε := by linarith only [hB, hrSmall, hε]

theorem tendsto_ccmMatchedOddNeumannVector_pole_profile :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp a.1 *
      ‖ccmMatchedOddNeumannVector a ⌈a.1⌉₊ - ccmMatchedOddPoleProfile a‖ ^ 2)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_ccmMatchedOddNeumannVector_pole_profile ε hε)]
      with a ha
    exact ha a.2

/-- The actual completed odd response has the explicit prescribed-shift
pole profile; its physical error vanishes even after exponential rescaling. -/
theorem eventually_suzukiTaMatchedOdd_pole_profile
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      Real.exp a * ‖ccmArchimedeanFormToAperture ⟨a, ha⟩
        (suzukiTaToFormCLM ⟨a, ha⟩ (suzukiTaRawCoalescingOdd ⟨a, ha⟩ (1 / 2))) -
          ccmMatchedOddPoleProfile ⟨a, ha⟩‖ ^ 2 < ε := by
  filter_upwards [eventually_ccmMatchedOddNeumannVector_pole_profile (ε / 8) (by positivity),
    eventually_suzukiTaMatchedOdd_neumann_relative_error (ε / 8) (by positivity)]
    with a haU haF
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let f := ccmArchimedeanFormToAperture ap
    (suzukiTaToFormCLM ap (suzukiTaRawCoalescingOdd ap (1 / 2)))
  let u := ccmMatchedOddNeumannVector ap ⌈a⌉₊
  let q := ccmMatchedOddPoleProfile ap
  have hnorm : ‖f - q‖ ≤ ‖f - u‖ + ‖u - q‖ := by
    calc
      _ = ‖(f - u) + (u - q)‖ := congrArg norm (by abel)
      _ ≤ _ := norm_add_le _ _
  have hsquare : ‖f - q‖ ^ 2 ≤ 2 * ‖f - u‖ ^ 2 + 2 * ‖u - q‖ ^ 2 := by
    have hs := mul_self_le_mul_self (norm_nonneg (f - q)) hnorm
    nlinarith only [hs, sq_nonneg (‖f - u‖ - ‖u - q‖)]
  have hscaled := mul_le_mul_of_nonneg_left hsquare (Real.exp_pos a).le
  have hu : Real.exp a * ‖u - q‖ ^ 2 < ε / 8 := haU ha
  have hf : Real.exp a * ‖f - u‖ ^ 2 < ε / 8 := haF ha
  change Real.exp a * ‖f - q‖ ^ 2 < ε
  nlinarith only [hscaled, hu, hf, hε]

theorem tendsto_suzukiTaMatchedOdd_pole_profile :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp a.1 *
      ‖ccmArchimedeanFormToAperture a
        (suzukiTaToFormCLM a (suzukiTaRawCoalescingOdd a (1 / 2))) -
          ccmMatchedOddPoleProfile a‖ ^ 2)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_suzukiTaMatchedOdd_pole_profile ε hε)] with a ha
    exact ha a.2

end RHTower
end
