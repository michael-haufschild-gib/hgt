import GaloisForLFunctions.RHTower.Suzuki.SuzukiOppositeShiftCrossSewnExterior
import GaloisForLFunctions.Bottcher.ArgumentPrinciple

/-!
# Suzuki cross-sewn double-jet divisor no-go

Cross-sewing two unrelated Suzuki source channels eliminates the opposite shifts and leaves the
zero-shift reciprocal target multiplied by

`P = 2 * WPlus * WMinus`.

At an Xi zero the shifted target is a genuine analytic simple zero, even when the Xi zero itself
has arbitrary multiplicity.  Its totalized reciprocal is nevertheless assigned value zero at the
pole.  Consequently a simple zero of `P` does not remove the singularity analytically: the
punctured quotient has a nonzero limiting value while the totalized value remains zero.  Exact
analytic removal occurs precisely when both the value and first derivative of `P` vanish.

For the cross-sewn product this double-jet condition has an exact channel classification: either
both channels vanish, or one channel already carries a double zero.  The final closed theorem
rules out every divisor-blind holomorphic regularization, with no assumption on RH, zero
simplicity, source origin, or the shift.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The totalized shifted target is genuinely simple -/

private theorem meromorphicAt_suzukiShiftedXiTarget
    (eta w : ℂ) : MeromorphicAt (suzukiShiftedXiTarget eta) w := by
  unfold suzukiShiftedXiTarget
  apply MeromorphicAt.div
  · exact ((by fun_prop : AnalyticAt ℂ (fun u : ℂ => u ^ (2 : ℕ)) w).mul
      (XiC_analytic w (Set.mem_univ w))).meromorphicAt
  · exact (((XiC_analytic w (Set.mem_univ w)).deriv.sub
      (analyticAt_const.mul (XiC_analytic w (Set.mem_univ w)))).meromorphicAt)

/-- At every Xi zero, the actual totalized shifted target is analytic.  This strengthens its
previously known meromorphic-normal-form order statement: the value chosen by field totalization
is exactly the removable value. -/
theorem analyticAt_suzukiShiftedXiTarget_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    AnalyticAt ℂ (suzukiShiftedXiTarget eta) z := by
  let T : ℂ → ℂ := suzukiShiftedXiTarget eta
  have hTmero : MeromorphicOn T Set.univ := by
    intro w _
    exact meromorphicAt_suzukiShiftedXiTarget eta w
  let F : ℂ → ℂ := toMeromorphicNFOn T Set.univ
  have hEqPunct : Filter.EventuallyEq (nhdsWithin z {z}ᶜ) F T := by
    exact hTmero.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hFNF : MeromorphicNFAt F z := by
    exact meromorphicNFOn_toMeromorphicNFOn T Set.univ (Set.mem_univ z)
  have hOrderF : meromorphicOrderAt F z = 1 := by
    rw [meromorphicOrderAt_congr hEqPunct]
    exact meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero hz
  have hFan : AnalyticAt ℂ F z := by
    apply hFNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [hOrderF]
    norm_num
  have hFzero : F z = 0 := by
    by_contra hne
    have hzeroOrder : analyticOrderAt F z = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hne)
    have hzeroMero : meromorphicOrderAt F z = 0 := by
      rw [hFan.meromorphicOrderAt_eq, hzeroOrder]
      rfl
    rw [hOrderF] at hzeroMero
    norm_num at hzeroMero
  have hTzero : T z = 0 := by
    simp [T, suzukiShiftedXiTarget, hz]
  have hEq : Filter.EventuallyEq (nhds z) F T := by
    change ∀ᶠ w in nhds z, F w = T w
    change ∀ᶠ w in nhdsWithin z {z}ᶜ, F w = T w at hEqPunct
    rw [eventually_nhdsWithin_iff] at hEqPunct
    filter_upwards [hEqPunct] with w hw
    by_cases hwz : w = z
    · subst w
      rw [hFzero, hTzero]
    · exact hw (by simpa using hwz)
  exact hFan.congr hEq

/-- Every shifted target has exact analytic order one at every Xi zero, independently of the Xi
zero's multiplicity. -/
theorem analyticOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    analyticOrderAt (suzukiShiftedXiTarget eta) z = (1 : ℕ) := by
  have hT := analyticAt_suzukiShiftedXiTarget_of_XiC_zero (eta := eta) hz
  have hM := meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero
    (eta := eta) hz
  rw [hT.meromorphicOrderAt_eq] at hM
  have hne : analyticOrderAt (suzukiShiftedXiTarget eta) z ≠ ⊤ := by
    intro htop
    rw [htop] at hM
    simp at hM
  generalize ha : analyticOrderAt (suzukiShiftedXiTarget eta) z = a at hM ⊢
  have hneA : a ≠ ⊤ := by
    rw [← ha]
    exact hne
  lift a to ℕ using hneA with n hn
  simp only [ENat.map_coe] at hM
  have hn1 : n = 1 := by exact_mod_cast hM
  subst n
  rfl

/-- The first spectral jet of every shifted target is nonzero at every Xi zero. -/
theorem deriv_suzukiShiftedXiTarget_ne_zero_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    deriv (suzukiShiftedXiTarget eta) z ≠ 0 := by
  have hT := analyticAt_suzukiShiftedXiTarget_of_XiC_zero (eta := eta) hz
  have hOrder := analyticOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero
    (eta := eta) hz
  have hjets :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hT (n := 1)).mp hOrder
  simpa [iteratedDeriv_one] using hjets.2

/-- Exact arbitrary-multiplicity first jet.  If Xi has multiplicity `m` at `z`, the target's
derivative is `z² / m`; in particular the jet is independent of the shift parameter. -/
theorem deriv_suzukiShiftedXiTarget_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    deriv (suzukiShiftedXiTarget eta) z =
      z ^ (2 : ℕ) / ((analyticOrderAt XiC z).toNat : ℂ) := by
  let T : ℂ → ℂ := suzukiShiftedXiTarget eta
  have hT : AnalyticAt ℂ T z :=
    analyticAt_suzukiShiftedXiTarget_of_XiC_zero (eta := eta) hz
  have hTzero : T z = 0 := by
    simp [T, suzukiShiftedXiTarget, hz]
  have hTderiv : deriv T z ≠ 0 := by
    exact deriv_suzukiShiftedXiTarget_ne_zero_of_XiC_zero (eta := eta) hz
  obtain ⟨Q, hQ, hTfac, hQz⟩ := Bottcher.analyticAt_simple_factor hT hTzero
  have hQzero : Q z ≠ 0 := by
    rw [hQz]
    exact hTderiv
  rw [show deriv (suzukiShiftedXiTarget eta) z = Q z by simpa [T] using hQz.symm]
  rw [← meromorphicTrailingCoeffAt_suzukiShiftedXiTarget_of_XiC_zero
    (eta := eta) hz]
  rw [hQ.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (f := suzukiShiftedXiTarget eta) (n := 1) hQzero]
  filter_upwards [] with w
  simpa [T] using hTfac w

/-! ## The wrong-center-value obstruction -/

/-- Once the source vanishes at an Xi zero, its product with the totalized reciprocal target is
analytic exactly when the source's first jet also vanishes.  A simple source zero cancels the pole
only on the punctured germ; totalization assigns zero at the center while that germ has nonzero
limit. -/
theorem analyticAt_suzukiShiftedXiMultiplier_mul_iff_deriv_eq_zero
    {eta z : ℂ} {W : ℂ → ℂ}
    (hz : XiC z = 0) (hW : AnalyticAt ℂ W z) (hWzero : W z = 0) :
    AnalyticAt ℂ (fun w => suzukiShiftedXiMultiplier eta w * W w) z ↔
      deriv W z = 0 := by
  let T : ℂ → ℂ := suzukiShiftedXiTarget eta
  have hT : AnalyticAt ℂ T z :=
    analyticAt_suzukiShiftedXiTarget_of_XiC_zero (eta := eta) hz
  have hTzero : T z = 0 := by
    simp [T, suzukiShiftedXiTarget, hz]
  have hTderiv : deriv T z ≠ 0 := by
    exact deriv_suzukiShiftedXiTarget_ne_zero_of_XiC_zero (eta := eta) hz
  obtain ⟨Q, hQ, hTfac, hQz⟩ := Bottcher.analyticAt_simple_factor hT hTzero
  obtain ⟨U, hU, hWfac, hUz⟩ := Bottcher.analyticAt_simple_factor hW hWzero
  have hQzero : Q z ≠ 0 := by
    rw [hQz]
    exact hTderiv
  let M : ℂ → ℂ := fun w => suzukiShiftedXiMultiplier eta w * W w
  let H : ℂ → ℂ := fun w => U w / Q w
  have hH : AnalyticAt ℂ H z := hU.div hQ hQzero
  have hMz : M z = 0 := by
    simp [M, suzukiShiftedXiMultiplier, T, hTzero]
  have hHz : H z = deriv W z / deriv T z := by
    simp [H, hUz, hQz]
  have hEqPunct : Filter.EventuallyEq (nhdsWithin z {z}ᶜ) M H := by
    filter_upwards [hQ.continuousAt.eventually_ne hQzero |>.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hQw hwz
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    change (T w)⁻¹ * W w = U w / Q w
    rw [hTfac w, hWfac w]
    field_simp [hwz', hQw]
  constructor
  · intro hM
    have hMlim : Tendsto M (nhdsWithin z {z}ᶜ) (nhds (M z)) :=
      hM.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hHlim : Tendsto H (nhdsWithin z {z}ᶜ) (nhds (H z)) :=
      hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hMlim' : Tendsto M (nhdsWithin z {z}ᶜ) (nhds (H z)) :=
      hHlim.congr' hEqPunct.symm
    have hvalues : M z = H z := tendsto_nhds_unique hMlim hMlim'
    rw [hMz, hHz] at hvalues
    exact (div_eq_zero_iff.mp hvalues.symm).resolve_right hTderiv
  · intro hderiv
    have hcenter : M z = H z := by
      rw [hMz, hHz, hderiv, zero_div]
    have hEq : Filter.EventuallyEq (nhds z) H M := by
      change ∀ᶠ w in nhds z, H w = M w
      change ∀ᶠ w in nhdsWithin z {z}ᶜ, M w = H w at hEqPunct
      rw [eventually_nhdsWithin_iff] at hEqPunct
      filter_upwards [hEqPunct] with w hw
      by_cases hwz : w = z
      · subst w
        exact hcenter.symm
      · exact (hw (by simpa using hwz)).symm
    exact hH.congr hEq

/-- Exact one-channel double-jet law.  An analytic interval correction neither creates nor removes
the totalization jump. -/
theorem analyticAt_suzukiExteriorRemainder_iff_doubleJet
    {eta z : ℂ} {W intervalPart : ℂ → ℂ}
    (hz : XiC z = 0) (hW : AnalyticAt ℂ W z)
    (hI : AnalyticAt ℂ intervalPart z) :
    AnalyticAt ℂ (suzukiExteriorRemainder eta W intervalPart) z ↔
      W z = 0 ∧ deriv W z = 0 := by
  constructor
  · intro hE
    have hWzero : W z = 0 := by
      by_contra hWzero
      have hpole := meromorphicOrderAt_suzukiExteriorRemainder_eq_neg_one
        (eta := eta) hz hW hWzero hI
      have hnonneg := hE.meromorphicOrderAt_nonneg
      rw [hpole] at hnonneg
      have hnot : ¬ (0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) := by
        exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
      exact hnot hnonneg
    refine ⟨hWzero, ?_⟩
    have hM : AnalyticAt ℂ
        (fun w => suzukiShiftedXiMultiplier eta w * W w) z := by
      apply (hE.add hI).congr
      filter_upwards [] with w
      simp [suzukiExteriorRemainder]
    exact (analyticAt_suzukiShiftedXiMultiplier_mul_iff_deriv_eq_zero
      (eta := eta) hz hW hWzero).mp hM
  · rintro ⟨hWzero, hWderiv⟩
    have hM := (analyticAt_suzukiShiftedXiMultiplier_mul_iff_deriv_eq_zero
      (eta := eta) hz hW hWzero).mpr hWderiv
    apply (hM.sub hI).congr
    filter_upwards [] with w
    rfl

/-! ## Cross-sewn incidence classification -/

/-- First jet of the cross-sewn product characteristic. -/
theorem deriv_suzukiCrossSewnCharacteristic
    {WPlus WMinus : ℂ → ℂ} {z : ℂ}
    (hWPlus : AnalyticAt ℂ WPlus z) (hWMinus : AnalyticAt ℂ WMinus z) :
    deriv (suzukiCrossSewnCharacteristic WPlus WMinus) z =
      2 * (deriv WPlus z * WMinus z + WPlus z * deriv WMinus z) := by
  have h2 : HasDerivAt (fun _ : ℂ => (2 : ℂ)) 0 z := hasDerivAt_const z 2
  have hp : HasDerivAt WPlus (deriv WPlus z) z :=
    hWPlus.differentiableAt.hasDerivAt
  have hm : HasDerivAt WMinus (deriv WMinus z) z :=
    hWMinus.differentiableAt.hasDerivAt
  change deriv (((fun _ : ℂ => (2 : ℂ)) * WPlus) * WMinus) z = _
  rw [((h2.mul hp).mul hm).deriv]
  simp only [Pi.mul_apply]
  ring

/-- A product characteristic has a double zero exactly through one of three channel incidences:
both channel values vanish, or one channel itself has a double zero. -/
theorem suzukiCrossSewn_doubleJet_iff_channelIncidence
    {WPlus WMinus : ℂ → ℂ} {z : ℂ}
    (hWPlus : AnalyticAt ℂ WPlus z) (hWMinus : AnalyticAt ℂ WMinus z) :
    (suzukiCrossSewnCharacteristic WPlus WMinus z = 0 ∧
        deriv (suzukiCrossSewnCharacteristic WPlus WMinus) z = 0) ↔
      (WPlus z = 0 ∧ WMinus z = 0) ∨
      (WPlus z = 0 ∧ deriv WPlus z = 0) ∨
      (WMinus z = 0 ∧ deriv WMinus z = 0) := by
  rw [deriv_suzukiCrossSewnCharacteristic hWPlus hWMinus]
  constructor
  · rintro ⟨hPzero, hPderiv⟩
    by_cases hp : WPlus z = 0
    · by_cases hm : WMinus z = 0
      · exact Or.inl ⟨hp, hm⟩
      · right
        left
        refine ⟨hp, ?_⟩
        simp [hp, hm] at hPderiv
        exact hPderiv
    · have hm : WMinus z = 0 := by
        simp [suzukiCrossSewnCharacteristic, hp] at hPzero
        exact hPzero
      right
      right
      refine ⟨hm, ?_⟩
      simp [hp, hm] at hPderiv
      exact hPderiv
  · rintro (hboth | hpdouble | hmdouble)
    · rcases hboth with ⟨hp, hm⟩
      simp [suzukiCrossSewnCharacteristic, hp, hm]
    · rcases hpdouble with ⟨hp, hdp⟩
      simp [suzukiCrossSewnCharacteristic, hp, hdp]
    · rcases hmdouble with ⟨hm, hdm⟩
      simp [suzukiCrossSewnCharacteristic, hm, hdm]

/-- Cross-sewn exterior analyticity at an Xi zero is exactly a double zero of the product
characteristic.  This is independent of the opposite shift and both analytic interval terms. -/
theorem analyticAt_suzukiCrossSewnExterior_iff_doubleJet
    {eta z : ℂ} {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (hz : XiC z = 0)
    (hWPlus : AnalyticAt ℂ WPlus z) (hWMinus : AnalyticAt ℂ WMinus z)
    (hIPlus : AnalyticAt ℂ intervalPlus z)
    (hIMinus : AnalyticAt ℂ intervalMinus z) :
    AnalyticAt ℂ
        (suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus) z ↔
      suzukiCrossSewnCharacteristic WPlus WMinus z = 0 ∧
        deriv (suzukiCrossSewnCharacteristic WPlus WMinus) z = 0 := by
  have hP := analyticAt_suzukiCrossSewnCharacteristic hWPlus hWMinus
  have hJ := analyticAt_suzukiCrossSewnIntervalPart
    hWPlus hWMinus hIPlus hIMinus
  have hfun :
      suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus =
        suzukiExteriorRemainder 0
          (suzukiCrossSewnCharacteristic WPlus WMinus)
          (suzukiCrossSewnIntervalPart
            WPlus WMinus intervalPlus intervalMinus) := by
    funext w
    exact suzukiCrossSewnExterior_eq_zeroShift
      eta WPlus WMinus intervalPlus intervalMinus w
  rw [hfun]
  exact analyticAt_suzukiExteriorRemainder_iff_doubleJet hz hP hJ

/-- Full channel classifier.  A holomorphic cross-sewn exterior at an Xi zero already contains
the Xi divisor through a two-channel value collision or a one-channel double jet. -/
theorem analyticAt_suzukiCrossSewnExterior_iff_channelIncidence
    {eta z : ℂ} {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (hz : XiC z = 0)
    (hWPlus : AnalyticAt ℂ WPlus z) (hWMinus : AnalyticAt ℂ WMinus z)
    (hIPlus : AnalyticAt ℂ intervalPlus z)
    (hIMinus : AnalyticAt ℂ intervalMinus z) :
    AnalyticAt ℂ
        (suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus) z ↔
      (WPlus z = 0 ∧ WMinus z = 0) ∨
      (WPlus z = 0 ∧ deriv WPlus z = 0) ∨
      (WMinus z = 0 ∧ deriv WMinus z = 0) := by
  rw [analyticAt_suzukiCrossSewnExterior_iff_doubleJet
    hz hWPlus hWMinus hIPlus hIMinus]
  exact suzukiCrossSewn_doubleJet_iff_channelIncidence hWPlus hWMinus

/-! ## Closed route kill -/

/-- Existence of a divisor-blind holomorphic cross-sewn regularization: analytic source channels
and interval terms would regularize some Xi zero without either a two-channel value collision or a
one-channel double zero. -/
def SuzukiCrossSewnDivisorBlindHolomorphicRegularization : Prop :=
  ∃ (eta z : ℂ)
    (WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ),
    XiC z = 0 ∧
    AnalyticAt ℂ WPlus z ∧ AnalyticAt ℂ WMinus z ∧
    AnalyticAt ℂ intervalPlus z ∧ AnalyticAt ℂ intervalMinus z ∧
    AnalyticAt ℂ
      (suzukiCrossSewnExterior eta
        WPlus WMinus intervalPlus intervalMinus) z ∧
    ¬ ((WPlus z = 0 ∧ WMinus z = 0) ∨
      (WPlus z = 0 ∧ deriv WPlus z = 0) ∨
      (WMinus z = 0 ∧ deriv WMinus z = 0))

/-- **Closed divisor-blind cross-sewing no-go.**  No analytic Suzuki source pair can regularize an
Xi zero while avoiding all three forced divisor-incidence mechanisms.  Thus the surviving
distinct-channel producer must derive Xi-zero incidence through source values or first jets; a
divisor-blind holomorphic sewing cannot close the Suzuki Ward-to-RH chain. -/
theorem not_suzukiCrossSewnDivisorBlindHolomorphicRegularization :
    ¬ SuzukiCrossSewnDivisorBlindHolomorphicRegularization := by
  rintro ⟨eta, z, WPlus, WMinus, intervalPlus, intervalMinus,
    hz, hWPlus, hWMinus, hIPlus, hIMinus, hExterior, hblind⟩
  apply hblind
  exact (analyticAt_suzukiCrossSewnExterior_iff_channelIncidence
    hz hWPlus hWMinus hIPlus hIMinus).mp hExterior

end


end RHTower
