import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonTaylorBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingHorizonExpansion
import GaloisForLFunctions.HTGeometry.QuadraticEndpointProducts

/-! The original incoming Green pairing's two endpoint coefficients and pole-aware remainder. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original radial Jacobian times the two incoming Gauss factors, with the indicial power removed. -/
def incomingPairingFactor (w chi : ℂ) (z : ℝ) : ℂ :=
  (gaussFactor w chi false (z:ℂ))^(2 : ℕ)/(2*(Real.sqrt (1-z):ℂ))

/-- The Jacobian changes the linear Gauss coefficient by exactly one quarter. -/
theorem incomingPairingFactor_uniform_second_bound (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ R C L : ℝ, 0 < R ∧ 0 ≤ C ∧ 0 ≤ L ∧
      ∀ u ∈ ball w R, ‖horizonGaussFirstCoefficient u chi+(1/4:ℂ)‖ ≤ L ∧
        ∀ z ∈ Icc (0:ℝ) (1/2),
          ‖incomingPairingFactor u chi z-(1/2:ℂ)-
            (horizonGaussFirstCoefficient u chi+1/4)*(z:ℂ)‖ ≤ C*z^(2 : ℕ) := by
  obtain ⟨R,C,L,hR,hC,hL,hH⟩ := horizonGauss_uniform_second_bound w chi hw
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  let C₂ := C*(1+L+C)+(1+L)*C+L*L
  let C₃ := C₂*(1/2+1/4+2)+(1+2*L)*2+(2*L)*(1/4)
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp [C₃]; positivity
  refine ⟨R,C₃,L+1/4,hR,hC₃,by positivity,?_⟩
  intro u hu
  have hl := (hH u hu).1
  have hl2 : ‖2*horizonGaussFirstCoefficient u chi‖ ≤ 2*L := by
    rw [norm_mul,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
    gcongr
  refine ⟨?_,?_⟩
  · calc
      _ ≤ ‖horizonGaussFirstCoefficient u chi‖+‖(1/4:ℂ)‖ := norm_add_le _ _
      _ ≤ L+1/4 := by norm_num; exact hl
  intro z hz
  have hz' : z ∈ Icc (0:ℝ) 1 := ⟨hz.1,by linarith [hz.2]⟩
  have he := (hH u hu).2 z hz
  have hs : ‖(gaussFactor u chi false (z:ℂ))^(2 : ℕ)-1-
      (2*horizonGaussFirstCoefficient u chi)*(z:ℂ)‖ ≤ C₂*z^(2 : ℕ) := by
    have hh := quadratic_endpoint_product_bound hz' hC hC he he
    have hid : (1:ℂ)*horizonGaussFirstCoefficient u chi+
        horizonGaussFirstCoefficient u chi*1=2*horizonGaussFirstCoefficient u chi := by ring
    rw [hid,one_mul,← pow_two] at hh
    simp only [norm_one] at hh
    exact hh.trans (by dsimp [C₂]; gcongr)
  have hj := inverse_sqrt_jacobian_second_bound hz
  have hp := quadratic_endpoint_product_bound hz' hC₂ (by norm_num : (0:ℝ)≤2) hs hj
  have hid : (1:ℂ)*(1/4)+(2*horizonGaussFirstCoefficient u chi)*(1/2)=
      horizonGaussFirstCoefficient u chi+1/4 := by ring
  rw [hid,one_mul] at hp
  rw [show (gaussFactor u chi false (z:ℂ))^(2 : ℕ)*(1/(2*(Real.sqrt (1-z):ℂ)))=
    incomingPairingFactor u chi z by unfold incomingPairingFactor; ring] at hp
  change ‖incomingPairingFactor u chi z-(1/2:ℂ)-
    (horizonGaussFirstCoefficient u chi+1/4)*(z:ℂ)‖ ≤ _ at hp
  refine hp.trans ?_
  rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num,
    show ‖(1/4:ℂ)‖=(1/4:ℝ) by norm_num,norm_one]
  dsimp [C₃]
  gcongr

/-- The actual source fixes the linear term of the incoming Green quotient. -/
def incomingResponseSlope (s a J K w : ℂ) : ℂ :=
  sourceRemainder s w a J K 1 0*(1/(w-2*s)+D4BMModularCore.onsetCorrection (2*s) w)/(2*(w+1))

/-- The source-determined slope is analytic at every admissible nonreal frequency, including connection zeros. -/
theorem incomingResponseSlope_analyticAt (s a J K w : ℂ)
    (hw : w.im ≠ 0) (hs : w-2*s ≠ 0) :
    AnalyticAt ℂ (incomingResponseSlope s a J K) w := by
  have hw1 : w+1 ≠ 0 := by
    intro h; apply hw
    have hi := congrArg Complex.im h
    simpa using hi
  unfold incomingResponseSlope
  exact ((sourceRemainder_frequency_entire s a J K 1 0).analyticAt w).mul
    ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add
      ((D4BMModularCore.onsetCorrection_entire (2*s)).analyticAt w)) |>.div
      (by fun_prop) (mul_ne_zero (by norm_num) hw1)

/-- The incoming part of the original pairing density, with only its indicial power removed. -/
def incomingResponsePairingCore (s chi a J K w : ℂ) (z : ℝ) : ℂ :=
  (continuedResponse s chi a J K z w/horizon w chi z)*incomingPairingFactor w chi z

/-- Restoring the indicial power recovers the actual incoming radial pairing with the original Jacobian. -/
theorem incomingResponsePairingCore_density (s chi a J K w : ℂ) {z : ℝ}
    (hz : z ∈ Ioo (0:ℝ) 1) :
    (z:ℂ)^(w-1)*incomingResponsePairingCore s chi a J K w z=
      continuedResponse s chi a J K z w*horizon w chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)) := by
  by_cases hh : horizon w chi z=0
  · simp [incomingResponsePairingCore,hh]
  have hz0 : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)
  have hr0 : (Real.sqrt (1-z):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (by linarith [hz.2])))
  have hp : (horizon w chi z)^(2 : ℕ)=(z:ℂ)^w*(gaussFactor w chi false (z:ℂ))^(2 : ℕ) := by
    dsimp [horizon,dress,power]
    rw [mul_pow,pow_two,← Complex.cpow_add _ _ hz0,show w/2+w/2=w by ring]
  rw [Complex.cpow_sub _ _ hz0,Complex.cpow_one]
  unfold incomingResponsePairingCore incomingPairingFactor
  calc
    _ = continuedResponse s chi a J K z w*((z:ℂ)^w*(gaussFactor w chi false (z:ℂ))^(2 : ℕ))/
        (horizon w chi z*(2*(z:ℂ)*(Real.sqrt (1-z):ℂ))) := by ring
    _ = continuedResponse s chi a J K z w*(horizon w chi z)^(2 : ℕ)/
        (horizon w chi z*(2*(z:ℂ)*(Real.sqrt (1-z):ℂ))) := by rw [hp]
    _ = _ := by field_simp [hh,hz0,hr0]

/-- Both divergent power-channel coefficients come from the original response, and the remainder retains the size of its possible connection pole. -/
theorem incomingResponsePairingCore_uniform_second_bound (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b C : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 → ∀ z ∈ Ioc (0:ℝ) b,
        ‖incomingResponsePairingCore s chi a J K u z-incomingResponseEndpoint s chi a J K u b/2-
          ((horizonGaussFirstCoefficient u chi+1/4)*incomingResponseEndpoint s chi a J K u b+
            incomingResponseSlope s a J K u/2)*(z:ℂ)‖ ≤
          C*(‖incomingResponseEndpoint s chi a J K u b‖+‖incomingResponseSlope s a J K u‖+1)*z^(2 : ℕ) := by
  obtain ⟨RQ,b,CQ,hRQ,hb,hbhalf,hCQ,hQ⟩ := continuedResponse_horizon_quadratic_expansion s chi a J K w hw hwr hs
  obtain ⟨RF,CF,L,hRF,hCF,hL,hF⟩ := incomingPairingFactor_uniform_second_bound w chi hw
  let C := CQ*(1/2+L+CF)+CF+L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨min RQ RF,b,C,lt_min hRQ hRF,hb,hbhalf,hC,?_⟩
  intro u hu hc z hz
  have huQ : u ∈ ball w RQ := ball_subset_ball (min_le_left _ _) hu
  have huF : u ∈ ball w RF := ball_subset_ball (min_le_right _ _) hu
  have hz' : z ∈ Icc (0:ℝ) (1/2) := ⟨hz.1.le,hz.2.trans hbhalf⟩
  have heQ := hQ u huQ hc z hz
  change ‖continuedResponse s chi a J K z u/horizon u chi z-incomingResponseEndpoint s chi a J K u b-
    incomingResponseSlope s a J K u*(z:ℂ)‖ ≤ CQ*z^(2 : ℕ) at heQ
  have heF := (hF u huF).2 z hz'
  have hl := (hF u huF).1
  have hp := quadratic_endpoint_product_bound (show z ∈ Icc (0:ℝ) 1 from ⟨hz.1.le,by linarith [hz'.2]⟩)
    hCQ hCF heQ heF
  have hid : incomingResponseEndpoint s chi a J K u b*(horizonGaussFirstCoefficient u chi+1/4)+
      incomingResponseSlope s a J K u*(1/2)=
      (horizonGaussFirstCoefficient u chi+1/4)*incomingResponseEndpoint s chi a J K u b+
      incomingResponseSlope s a J K u/2 := by ring
  rw [hid] at hp
  rw [show incomingResponseEndpoint s chi a J K u b*(1/2)=
    incomingResponseEndpoint s chi a J K u b/2 by ring] at hp
  change ‖incomingResponsePairingCore s chi a J K u z-incomingResponseEndpoint s chi a J K u b/2-
    ((horizonGaussFirstCoefficient u chi+1/4)*incomingResponseEndpoint s chi a J K u b+
      incomingResponseSlope s a J K u/2)*(z:ℂ)‖ ≤ _ at hp
  refine hp.trans ?_
  have hcoef : CQ*(‖(1/2:ℂ)‖+‖horizonGaussFirstCoefficient u chi+1/4‖+CF)+
      (‖incomingResponseEndpoint s chi a J K u b‖+‖incomingResponseSlope s a J K u‖)*CF+
      ‖incomingResponseSlope s a J K u‖*‖horizonGaussFirstCoefficient u chi+1/4‖ ≤
      C*(‖incomingResponseEndpoint s chi a J K u b‖+‖incomingResponseSlope s a J K u‖+1) := by
    calc
      _ ≤ CQ*(1/2+L+CF)+(‖incomingResponseEndpoint s chi a J K u b‖+‖incomingResponseSlope s a J K u‖)*CF+
          ‖incomingResponseSlope s a J K u‖*L := by norm_num; gcongr
      _ ≤ _ := by
        dsimp [C]
        nlinarith [norm_nonneg (incomingResponseEndpoint s chi a J K u b),
          norm_nonneg (incomingResponseSlope s a J K u),
          mul_nonneg (norm_nonneg (incomingResponseEndpoint s chi a J K u b)) hL,
          mul_nonneg (norm_nonneg (incomingResponseEndpoint s chi a J K u b)) (mul_nonneg hCQ (by positivity : 0 ≤ 1/2+L+CF)),
          mul_nonneg (norm_nonneg (incomingResponseSlope s a J K u)) (mul_nonneg hCQ (by positivity : 0 ≤ 1/2+L+CF))]
  exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg z)

end
end RHTower.D4BMLaplaceRadial
