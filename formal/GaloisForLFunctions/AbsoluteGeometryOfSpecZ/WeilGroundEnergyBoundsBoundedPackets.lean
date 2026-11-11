import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormIsContinuousUnderPacketSmoothing
import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSignIsCarriedByTheContacts

/-!
# The aperture ground energy bounds bounded packets

The closed-aperture Rayleigh bound survives simultaneous smoothing of
the full Weil form and its mass. The resulting floor depends only on
support width, not on the number of jumps of a step packet.
-/

noncomputable section

open Filter Topology MeasureTheory Set Zeta23

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open SquareRootThreshold

/-- Convolution with the bump is smooth at every order, even for a bounded
measurable packet. -/
theorem contDiff_top_mollify (φ : ContDiffBump (0 : ℝ))
    {g : ℝ → ℝ} (hgm : Measurable g) {M l r : ℝ}
    (hgb : ∀ u, |g u| ≤ M) (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify φ g) := by
  exact HasCompactSupport.contDiff_convolution_left (n := (⊤ : ℕ∞))
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.hasCompactSupport_normed (μ := volume))
    (φ.contDiff_normed (μ := volume)) (locallyIntegrable_packet hgm hgb hsupp)

/-- A bounded finite-energy packet inherits the ground-energy mass floor
of every strictly wider aperture. -/
theorem groundEnergy_mul_packetAutocorr_le_packetForm
    {g : ℝ → ℝ} (hgm : Measurable g) {M l r : ℝ}
    (hgb : ∀ u, |g u| ≤ M) (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r)
    {A : _root_.RHTower.SuzukiPositiveAperture} (hA : r - l < 2 * A.1)
    {Q : ℕ} (hQ : r - l < Real.log ((Q : ℝ) + 1))
    (hJ : IntegrableOn (levyJump g) (Ioi 0)) :
    _root_.RHTower.ccmRestrictedWeilGroundEnergy A * packetAutocorr g 0 ≤ packetForm Q g := by
  have hradius : ∀ᶠ i : ℕ in atTop, (shrinkingBump i).rOut ≤ A.1 - (r - l) / 2 := by
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iic_mem_nhds (by linarith only [hA]))
  have hbound : ∀ᶠ i : ℕ in atTop,
      _root_.RHTower.ccmRestrictedWeilGroundEnergy A *
        packetAutocorr (mollify (shrinkingBump i) g) 0 ≤
      zeroSum (mollify (shrinkingBump i) g) := by
    filter_upwards [hradius] with i hi
    let c := (l + r) / 2
    have hf := contDiff_top_mollify (shrinkingBump i) hgm hgb hsupp
    have hfc := hasCompactSupport_mollify (shrinkingBump i) hsupp
    have hs : tsupport (fun u => (mollify (shrinkingBump i) g (u - -c) : ℂ)) ⊆
        Icc (-A.1) A.1 := by
      apply closure_minimal _ isClosed_Icc
      intro u hu
      have hn : mollify (shrinkingBump i) g (u - -c) ≠ 0 := by
        intro hz
        exact hu (by simp only [hz, Complex.ofReal_zero])
      have hb := mollify_ne_zero (shrinkingBump i) hsupp (u - -c) hn
      constructor <;> dsimp only [c] at * <;> linarith only [hb.1, hb.2, hi]
    have hW := ccmRestrictedWeilGroundEnergy_mul_integral_norm_sq_le_re_W
      (Complex.ofRealCLM.contDiff.comp (hf.comp (contDiff_id.sub contDiff_const))) hs
    have hmass : (∫ u, ‖(mollify (shrinkingBump i) g (u - -c) : ℂ)‖ ^ 2) =
        packetAutocorr (mollify (shrinkingBump i) g) 0 := by
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [integral_sub_right_eq_self (fun u => mollify (shrinkingBump i) g u ^ 2) (-c)]
      simp only [packetAutocorr, add_zero, pow_two]
    change _root_.RHTower.ccmRestrictedWeilGroundEnergy A *
      (∫ u, ‖(mollify (shrinkingBump i) g (u - -c) : ℂ)‖ ^ 2) ≤
      zeroSum (fun u => mollify (shrinkingBump i) g (u - -c)) at hW
    rw [hmass, zeroSum_translate
      (hf.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hfc] at hW
    exact hW
  exact le_of_tendsto_of_tendsto
    ((tendsto_packetAutocorr_mollify hgm hgb hsupp 0).const_mul _)
    (tendsto_zeroSum_mollify hgm hgb hsupp hQ hJ) hbound

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
