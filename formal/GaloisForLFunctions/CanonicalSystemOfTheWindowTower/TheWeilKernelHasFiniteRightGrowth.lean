import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelIncrementHasItsCollarEnergyBound
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilCollarResidualsHaveTheirActualL2Limit
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEnergyContinuity

/-!
# Endpoint traces bound the right growth of the Weil kernel

The logarithmic collar floor and the exact residual mass asymptotic have
matching logarithms. Their quotient bounds every sufficiently short kernel
increment by its aperture length times the two endpoint trace energies.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy
namespace WeilHilbertBeforeContact

/-- The sum of the squared actual endpoint readouts. -/
def evalEndpointEnergy (a : PrecontactAperture) (z : ℂ) : ℝ :=
  ‖∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
    (evalVectorLeftEndpointForcing a z : RealLineL2) y‖^2 +
  ‖∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
    (evalVectorRightEndpointForcing a z : RealLineL2) y‖^2

/-- At every precontact aperture, the right upper kernel derivative is bounded
by the endpoint energy. The bound uses the actual complete Weil residual. -/
theorem eventually_kernel_increment_le_endpoint_energy
    {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) (z : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ (b : PrecontactAperture)
      (hab : a.1.1 ≤ b.1.1), b.1.1 = a.1.1+h →
      (kernel b z z - kernel a z z).re / h < evalEndpointEnergy a z + ε := by
  let L : ℝ → ℝ := fun h => Real.log (1/h)
  let E : ℝ := weilTwoCollarEnergyError a c
  let M : ℝ → ℝ := fun h =>
    ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
      (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hac.le z))‖^2 +
    ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
      (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hac.le z))‖^2
  have hL : Tendsto L (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [L, one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hM : Tendsto (fun h => M h / (h*L h)) (𝓝[>] (0 : ℝ))
      (𝓝 (evalEndpointEnergy a z)) := by
    simpa only [M, L, add_div, evalEndpointEnergy] using
      (evalVectorLeftCollarResidual_mass_limit hac z).add
        (evalVectorRightCollarResidual_mass_limit hac z)
  have hE : Tendsto (fun h => 1-E/L h) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hi := (tendsto_inv_atTop_zero.comp hL).const_mul E
    simpa only [div_eq_mul_inv, mul_zero, sub_zero, Function.comp_def] using
      tendsto_const_nhds.sub hi
  have hquot : Tendsto (fun h => (M h/(h*L h))/(1-E/L h))
      (𝓝[>] (0 : ℝ)) (𝓝 (evalEndpointEnergy a z)) := by
    have ht := hM.div hE (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at ht
    exact ht.congr' (Eventually.of_forall fun _ => rfl)
  have hsmall := hquot.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [hsmall, self_mem_nhdsWithin,
    hL.eventually (eventually_gt_atTop (max E 0)),
    (eventually_lt_nhds (sub_pos.mpr hac)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds]
      with h hs hh hlarge hhc hh1
  change 0 < h at hh
  have hLpos : 0 < L h := (le_max_right E 0).trans_lt hlarge
  have hLE : 0 < L h-E := sub_pos.mpr ((le_max_left E 0).trans_lt hlarge)
  intro b hab hb
  have hbc : b.1.1 ≤ c.1.1 := by rw [hb]; linarith only [hhc]
  have hfloor := norm_increment_sq_mul_collar_floor_le hab hbc hh hh1.le hb z
  change (L h-E)*‖evalVectorIncrement hab z‖^2 ≤ M h at hfloor
  rw [kernel_diagonal_sub_eq_norm_increment_sq hab]
  have hbound : ‖evalVectorIncrement hab z‖^2/h ≤ M h/(h*(L h-E)) := by
    apply (div_le_div_iff₀ hh (mul_pos hh hLE)).mpr
    convert mul_le_mul_of_nonneg_left hfloor hh.le using 1 <;> ring
  have heq : M h/(h*(L h-E)) = (M h/(h*L h))/(1-E/L h) := by
    field_simp [hh.ne', hLpos.ne', hLE.ne']
    <;> ring
  exact hbound.trans_lt (heq.trans_lt hs)

/-- Orthogonality makes the new component smaller than every approximation
from the old space. -/
theorem norm_evalVectorIncrement_le_approximation {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) (u : WeilHilbertBeforeContact a) :
    ‖evalVectorIncrement hab z‖ ≤ ‖evalVector b z-inclusion hab u‖ := by
  have hs : evalVector b z-inclusion hab u =
      evalVectorIncrement hab z + inclusion hab (evalVector a z-u) := by
    rw [map_sub, evalVectorIncrement]
    abel
  have hn := norm_add_sq (𝕜 := ℂ) (evalVectorIncrement hab z)
    (inclusion hab (evalVector a z-u))
  rw [inner_evalVectorIncrement_inclusion] at hn
  simp only [RCLike.re_to_complex, Complex.zero_re, mul_zero, add_zero] at hn
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hs, hn]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Approaching an aperture from below exhausts its evaluation vector:
compact smooth sources already belong to strictly smaller windows. -/
theorem exists_left_aperture_small_evalVectorIncrement (a : PrecontactAperture)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a₀ : PrecontactAperture, a₀.1.1 < a.1.1 ∧
      ∀ (b : PrecontactAperture) (_ : a₀.1.1 ≤ b.1.1)
        (hba : b.1.1 ≤ a.1.1), ‖evalVectorIncrement hba z‖ < ε := by
  obtain ⟨u, hu⟩ := (denseRange_smoothCore a).exists_dist_lt (evalVector a z) hε
  obtain ⟨a₀, h₀a, hs⟩ := exists_strict_smaller_aperture_of_compact_tsupport a.1 u
  have hcontact : (a₀.1 : EReal) < WindowVisibilityLaw.onsetAperture Zeta23.zetaZeroConfig :=
    (EReal.coe_lt_coe_iff.mpr h₀a).trans a.2
  let c : PrecontactAperture := ⟨a₀, hcontact⟩
  let v : WeilHilbertBeforeContact c := fromFormCLM c (u.restrictAperture a₀ hs).toCCMFormVector
  have hv : inclusion h₀a.le v = fromFormCLM a u.toCCMFormVector := by
    apply (toForm a).injective
    rw [toForm_inclusion, toForm_fromForm]
    apply Subtype.ext
    rw [apertureExt_val]
    exact u.restrictAperture_toCCMFormVector_val a₀ hs
  refine ⟨c, h₀a, fun b h₀b hba => ?_⟩
  have hn := norm_evalVectorIncrement_le_approximation hba z (inclusion h₀b v)
  rw [inclusion_trans, hv] at hn
  exact hn.trans_lt (by simpa only [dist_eq_norm] using hu)

#print axioms eventually_kernel_increment_le_endpoint_energy
#print axioms exists_left_aperture_small_evalVectorIncrement
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
