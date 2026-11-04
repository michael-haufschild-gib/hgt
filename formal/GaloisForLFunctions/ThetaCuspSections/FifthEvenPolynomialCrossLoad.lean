import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightSourceBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterCompensationFlux

/-!
# A polynomial flux profile for the fifth even cross-load

A nonnegative quartic profile preserves the center flux's zero integral.
Its differentiated source agrees with the fixed correction at the origin
and dominates the admissible half-load at theta scale eight.
-/

noncomputable section
open Matrix MeasureTheory Filter Topology RHTower RHTower.ThetaCuspGaussianLimit
open Set (Ioi)
namespace GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
open EvenFiveEndpoint EightCrossSource EightCrossData FifthNativeRay FifthCrossEnvelope

/-- Nonnegative profile vanishing at radius squared equal to two. -/
def profile (r : ℝ) : ℝ := (1-r^2/2)^2

/-- The polynomially weighted literal center flux. -/
def flux (a r : ℝ) : ℝ := profile r*thetaCuspCenterCompensationFlux a r

/-- Aperture-independent lower correction obtained by differentiating the profile. -/
def compensation (x : ℝ) : ℝ :=
  (1-2*x^2)^2*thetaCuspCenterCompensationSource x-
    8*x^2*(1-2*x^2)*thetaCuspFullSource x^2

/-- Complete fifth source with the polynomially profiled cross-load. -/
def repair (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 x+compensation x • crossLoad paidSevenSchur

/-- The literal center-weighted fifth even source with its exact flux derivative. -/
def weightedRepair (a r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (r*Real.sinh (a*r)) • nativeShiftedMatrix 5 0 (r/2)+
    deriv (flux a) r • crossLoad paidSevenSchur

theorem profile_nonneg (r : ℝ) : 0 ≤ profile r := sq_nonneg _

private theorem profile_hasDerivAt (r : ℝ) :
    HasDerivAt profile (-2*r*(1-r^2/2)) r := by
  have h := ((hasDerivAt_const r (1 : ℝ)).sub
    (((hasDerivAt_id r).pow 2).div_const 2)).pow 2
  exact h.congr_deriv (by dsimp; ring)

private theorem polynomial_differentiable (n : ℕ) (a : ℝ) :
    Differentiable ℝ (thetaCuspPolynomialFlux n a) := by
  intro r
  exact (((hasDerivAt_id r).pow n).mul
    (hasDerivAt_thetaCuspCenterCompensationFlux a r)).differentiableAt

/-- The quartic profile is an exact linear combination of polynomial center fluxes. -/
theorem flux_eq (a : ℝ) : flux a = fun r =>
    thetaCuspPolynomialFlux 0 a r-thetaCuspPolynomialFlux 2 a r+
      (1/4)*thetaCuspPolynomialFlux 4 a r := by
  funext r
  simp only [flux,profile,thetaCuspPolynomialFlux,pow_zero,one_mul]
  ring

/-- Differentiation preserves this exact polynomial-flux decomposition. -/
theorem deriv_flux_eq (a r : ℝ) : deriv (flux a) r =
    deriv (thetaCuspPolynomialFlux 0 a) r-deriv (thetaCuspPolynomialFlux 2 a) r+
      (1/4)*deriv (thetaCuspPolynomialFlux 4 a) r := by
  have h := ((polynomial_differentiable 0 a r).hasDerivAt.sub
    (polynomial_differentiable 2 a r).hasDerivAt).add
    ((polynomial_differentiable 4 a r).hasDerivAt.const_mul (1/4))
  have hf : (thetaCuspPolynomialFlux 0 a-thetaCuspPolynomialFlux 2 a+
      fun x => (1/4)*thetaCuspPolynomialFlux 4 a x) = flux a := by
    funext x
    change thetaCuspPolynomialFlux 0 a x-thetaCuspPolynomialFlux 2 a x+
      (1/4)*thetaCuspPolynomialFlux 4 a x=flux a x
    rw [flux_eq]
  rw [hf] at h
  exact h.deriv

/-- The profiled correction has absolutely integrable derivative. -/
theorem integrable_deriv_flux {a : ℝ} (ha : |a| < 1) :
    IntegrableOn (deriv (flux a)) (Ioi 0) := by
  have h0 := integrableOn_deriv_thetaCuspPolynomialFlux 0 ha
  have h2 := integrableOn_deriv_thetaCuspPolynomialFlux 2 ha
  have h4 := integrableOn_deriv_thetaCuspPolynomialFlux 4 ha
  change IntegrableOn (fun r => deriv (flux a) r) (Ioi 0)
  simp_rw [deriv_flux_eq]
  exact (h0.sub h2).add (h4.const_mul (1/4))

/-- The profiled flux changes no integrated source mass. -/
theorem integral_deriv_flux {a : ℝ} (ha : |a| < 1) :
    (∫ r : ℝ in Ioi 0, deriv (flux a) r)=0 := by
  have h0 := integrableOn_deriv_thetaCuspPolynomialFlux 0 ha
  have h2 := integrableOn_deriv_thetaCuspPolynomialFlux 2 ha
  have h4 := integrableOn_deriv_thetaCuspPolynomialFlux 4 ha
  simp_rw [deriv_flux_eq]
  have hs : IntegrableOn (fun r => deriv (thetaCuspPolynomialFlux 0 a) r-
      deriv (thetaCuspPolynomialFlux 2 a) r) (Ioi 0) := h0.sub h2
  rw [integral_add hs (h4.const_mul (1/4)),integral_sub h0 h2,
    integral_const_mul,integral_deriv_thetaCuspPolynomialFlux 0 ha,
    integral_deriv_thetaCuspPolynomialFlux 2 ha,integral_deriv_thetaCuspPolynomialFlux 4 ha]
  ring

private theorem deriv_flux_product (a r : ℝ) : deriv (flux a) r =
    (-2*r*(1-r^2/2))*thetaCuspCenterCompensationFlux a r+
      profile r*deriv (thetaCuspCenterCompensationFlux a) r := by
  have h := (profile_hasDerivAt r).mul (hasDerivAt_thetaCuspCenterCompensationFlux a r)
  have hf : profile*thetaCuspCenterCompensationFlux a=flux a := by funext x; rfl
  rw [hf] at h
  rw [(hasDerivAt_thetaCuspCenterCompensationFlux a r).deriv]
  exact h.deriv

/-- The nonnegative profile retains the aperture-independent lower source. -/
theorem deriv_flux_lower {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    r*Real.sinh (a*r)*compensation (r/2) ≤ deriv (flux a) r := by
  have h := mul_le_mul_of_nonneg_left
    (deriv_thetaCuspCenterCompensationFlux_lower ha hr) (profile_nonneg r)
  have he : r*Real.sinh (a*r)*compensation (r/2) =
      profile r*(r*Real.sinh (a*r)*(3*thetaCuspFullSource (r/2)^2+
        r*thetaCuspFullSource (r/2)*deriv thetaCuspFullSource (r/2)))+
      (-2*r*(1-r^2/2))*thetaCuspCenterCompensationFlux a r := by
    simp only [profile,compensation,thetaCuspCenterCompensationSource,
      thetaCuspCenterCompensationFlux]
    ring
  rw [he,deriv_flux_product]
  linarith only [h]

/-- Exact separation of the lower source and the aperture remainder. -/
theorem weightedRepair_decomposition (a r : ℝ) : weightedRepair a r =
    (r*Real.sinh (a*r)) • repair (r/2)+
      (deriv (flux a) r-r*Real.sinh (a*r)*compensation (r/2)) • crossLoad paidSevenSchur := by
  ext i j
  simp only [weightedRepair,repair,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

private theorem weighted_entry (a : ℝ) (i j : Fin 5) :
    (fun r => weightedRepair a r i j) = fun r => EvenFiveCoherent.weightedRepair a 0 r i j+
      crossLoad paidSevenSchur i j*deriv (flux a) r := by
  funext r
  simp only [weightedRepair,EvenFiveCoherent.weightedRepair,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,zero_mul]
  ring

/-- Every entry of the literal profiled fifth even block is integrable. -/
theorem weightedRepair_integrable {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (i j : Fin 5) : IntegrableOn (fun r => weightedRepair a r i j) (Ioi 0) := by
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  rw [weighted_entry]
  exact (EvenFiveCoherent.weightedRepair_integrable ha0 ha 0 i j).add
    ((integrable_deriv_flux habs).const_mul _)

/-- The profiled correction preserves the actual fifth even mixed matrix entry by entry. -/
theorem weightedRepair_integral {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (i j : Fin 5) : (∫ r in Ioi 0, weightedRepair a r i j) =
      thetaCuspCenterMixedSignedJet a (2*(i.val+j.val)) := by
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  rw [weighted_entry,integral_add (EvenFiveCoherent.weightedRepair_integrable ha0 ha 0 i j)
    ((integrable_deriv_flux habs).const_mul _),integral_const_mul,integral_deriv_flux habs,
    mul_zero,add_zero,EvenFiveCoherent.weightedRepair_integral ha0 ha]

private theorem compensation_strong_negative :
    thetaCuspCenterCompensationSource center ≤ -6*thetaCuspFullSource center^2 := by
  have hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 center := by rw [center_scale]; norm_num
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hF := thetaCuspFullSource_pos_all center
  have hm := mul_self_le_mul_self hF.le (mass_slope_bounds hq).2.1
  have hsq := first_mass_square center
  rw [center_scale] at hsq
  norm_num only [show (2*(8 : ℝ)-3)^2=169 by norm_num] at hsq
  have hG := (div_le_iff₀ hK).mp compensation_bounds.2
  have hu : upperCompensation ≤ -6*(1000001/1000000)^2*169 := by
    norm_num [upperCompensation]
  have huK := mul_le_mul_of_nonneg_right hu hK.le
  nlinarith only [hm,hsq,hG,huK]

private theorem profile_center_bound : (1-2*center^2)^2 ≤ (1/3 : ℝ) := by
  have hl : (7/15 : ℝ) ≤ center := by linarith only [center_bounds.1]
  have hu : center ≤ (1/2 : ℝ) := by linarith only [center_bounds.2]
  have hl2 := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7/15) hl
  have hu2 := mul_self_le_mul_self center_pos.le hu
  have hb0 : 0 ≤ 1-2*center^2 := by nlinarith only [hu2]
  have hb1 : 1-2*center^2 ≤ (127/225 : ℝ) := by nlinarith only [hl2]
  have hsq := mul_self_le_mul_self hb0 hb1
  nlinarith only [hsq]

/-- The profiled correction at scale eight dominates the admissible half-load. -/
theorem compensation_center_lower :
    thetaCuspCenterCompensationSource center/2 ≤ compensation center := by
  have hG := compensation_strong_negative
  have hp := mul_le_mul_of_nonpos_right profile_center_bound compensation_negative.le
  have hcoef : 8*center^2*(1-2*center^2) ≤ (1 : ℝ) := by
    nlinarith only [sq_nonneg (1-4*center^2)]
  have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (thetaCuspFullSource center))
  unfold compensation
  nlinarith only [hG,hp,hm]

private theorem load_nonneg : (crossLoad paidSevenSchur).PosSemidef :=
  crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap

private theorem repair_hermitian (x : ℝ) : (repair x).IsHermitian := by
  apply Matrix.IsHermitian.add
  · rw [Matrix.IsHermitian]
    ext i j
    simp [nativeShiftedMatrix,add_comm]
  · exact load_nonneg.isHermitian.smul (by rfl)

/-- The profile leaves the strictly positive repaired origin unchanged. -/
theorem repair_origin_posDef : (repair 0).PosDef := by
  have he : repair 0 = nativeShiftedMatrix 5 0 0+
      thetaCuspCenterCompensationSource 0 • crossLoad paidSevenSchur := by
    simp [repair,compensation]
  rw [he]
  exact origin_cross_load_posDef

/-- The complete profiled source is strictly positive at scale eight. -/
theorem repair_center_posDef : (repair center).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨repair_hermitian _,?_⟩
  intro v hv
  have hp := source_half_load_posDef.dotProduct_mulVec_pos hv
  have hB := load_nonneg.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hp hB ⊢
  have h := mul_le_mul_of_nonneg_right compensation_center_lower hB
  simp only [repair,scaledSource,Matrix.add_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul] at hp ⊢
  linarith only [hp,h]

/-- The literal weighted fifth even block is positive at scale eight for every positive aperture. -/
theorem weightedRepair_center_posDef {a : ℝ} (ha : 0 < a) :
    (weightedRepair a (2*center)).PosDef := by
  have hr : 0 < 2*center := mul_pos (by norm_num) center_pos
  have hw := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hl := deriv_flux_lower ha.le hr.le
  rw [show 2*center/2=center by ring] at hl
  rw [weightedRepair_decomposition,show 2*center/2=center by ring]
  exact (repair_center_posDef.smul hw).add_posSemidef (load_nonneg.smul (sub_nonneg.mpr hl))

private theorem repair_continuous : Continuous repair := by
  have hF : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hj := continuous_thetaCuspNativeReflectionJet
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold repair compensation thetaCuspCenterCompensationSource nativeShiftedMatrix
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  fun_prop

private theorem repair_near {y : ℝ} (hy : (repair y).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x-y| < δ → (repair x).PosDef := by
  have ht (i j : Fin 5) : Tendsto (fun x => repair x i j) (𝓝 y) (𝓝 (repair y i j)) :=
    ((continuous_apply j).comp ((continuous_apply i).comp repair_continuous)).continuousAt.tendsto
  have hp := GaloisForLFunctions.HTGeometry.posDef_eventually_of_tendsto hy
    (Filter.Eventually.of_forall repair_hermitian) ht
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨δ,hδ,fun x hx => hb (by simpa only [Real.dist_eq] using hx)⟩

/-- One lawful polynomial profile repairs neighborhoods of the origin and scale eight. -/
theorem repair_neighborhoods : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ,
    (|x| < δ ∨ |x-center| < δ) → (repair x).PosDef := by
  obtain ⟨δ0,hδ0,h0⟩ := repair_near repair_origin_posDef
  obtain ⟨δ8,hδ8,h8⟩ := repair_near repair_center_posDef
  refine ⟨min δ0 δ8,lt_min hδ0 hδ8,fun x hx => ?_⟩
  rcases hx with hx | hx
  · exact h0 x (by simpa only [sub_zero] using hx.trans_le (min_le_left _ _))
  · exact h8 x (hx.trans_le (min_le_right _ _))

end GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
