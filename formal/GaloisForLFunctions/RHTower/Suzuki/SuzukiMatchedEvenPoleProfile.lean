import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteSourceProfile
import GaloisForLFunctions.RHTower.CCM.CCMMatchedEvenNeumannSource

open Filter
open scoped Topology InnerProduct
noncomputable section
namespace RHTower

/-- The admitted literal even source represents the actual cosh response. -/
theorem suzukiTaSourceResponse_matchedEven (a : SuzukiPositiveAperture) :
    suzukiTaSourceResponse a (ccmMatchedEvenPoleSource a) =
      suzukiTaRawCoalescingEven a (1 / 2) := by
  apply ext_inner_right ℂ
  intro z
  rw [suzukiTaSourceResponse_inner, suzukiTaRawCoalescingEven_inner]
  let e := suzukiApertureL2Equiv a
  have hp (s : ℝ) : e (suzukiTaExponentialL2 a s) = ccmPolarApertureVector a s := by
    apply Subtype.ext
    exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a s
  have hs : (suzukiApertureCoordinate a.2.le).coshVecC (1 / 2) =
      (1 / 2 : ℂ) • (suzukiTaExponentialL2 a (1 / 2) + suzukiTaExponentialL2 a (-1 / 2)) := by
    rw [suzukiTaExponentialL2_eq_cosh_add_sinh,
      show (-1 / 2 : ℝ) = -(1 / 2) by ring, suzukiTaExponentialL2_neg_eq_cosh_sub_sinh]
    module
  have hsource : e ((suzukiApertureCoordinate a.2.le).coshVecC (1 / 2)) =
      ccmMatchedEvenPoleSource a := by
    rw [hs, map_smul, map_add, hp, hp]
    rfl
  have hf : ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z) =
      e (suzukiTaPhysicalEmbedding a z) := by
    change _ = e (e.symm _)
    rw [e.apply_symm_apply]
    rfl
  rw [← hsource, hf, e.inner_map_map]

/-- The actual completed even response has the explicit prescribed-shift
pole profile, with no norm, budget or response-regularity premise. -/
theorem eventually_suzukiTaMatchedEven_pole_profile
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      Real.exp a * ‖ccmArchimedeanFormToAperture ⟨a, ha⟩
        (suzukiTaToFormCLM ⟨a, ha⟩ (suzukiTaRawCoalescingEven ⟨a, ha⟩ (1 / 2))) -
          ccmSourceShiftProfile ⟨a, ha⟩ (ccmMatchedEvenPoleSource ⟨a, ha⟩)‖ ^ 2 < ε := by
  filter_upwards [eventually_suzukiTaSourceResponse_source_profile (ε / 2) (by positivity)]
    with a haProfile
  intro ha
  have h := haProfile ha (ccmMatchedEvenPoleSource ⟨a, ha⟩) (Real.exp (a / 2))
    (norm_ccmMatchedEvenPoleSource_le ⟨a, ha⟩) (ccmMatchedEvenPoleSource_budget ⟨a, ha⟩)
  rw [suzukiTaSourceResponse_matchedEven] at h
  have he : (Real.exp (a / 2)) ^ 2 = Real.exp a := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, show (2 : ℝ) * a = a + a by ring, Real.exp_add] at h
  refine lt_of_le_of_lt ?_ (show ε / 2 < ε by linarith)
  apply le_of_mul_le_mul_left (a := Real.exp a) ?_ (Real.exp_pos a)
  simpa only [mul_assoc, mul_comm (ε / 2)] using h

theorem tendsto_suzukiTaMatchedEven_pole_profile :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp a.1 *
      ‖ccmArchimedeanFormToAperture a
        (suzukiTaToFormCLM a (suzukiTaRawCoalescingEven a (1 / 2))) -
          ccmSourceShiftProfile a (ccmMatchedEvenPoleSource a)‖ ^ 2)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_suzukiTaMatchedEven_pole_profile ε hε)] with a ha
    exact ha a.2

end RHTower
end
