import GaloisForLFunctions.HTGeometry.L2SpatialReflectionMultipliers
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCompactPower
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalData

/-! The literal principal radial potentials as even bounded spatial operators. -/
open MeasureTheory Set GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section

theorem horizonCoordinate_nonneg (t : ℝ) : 0 ≤ horizonCoordinate t := by
  rw [horizonCoordinate_factor]
  positivity

theorem horizonCoordinate_le_one (t : ℝ) : horizonCoordinate t ≤ 1 := by
  unfold horizonCoordinate
  nlinarith [sq_nonneg (radialUnit t)]

theorem horizonCoordinate_even (t : ℝ) : horizonCoordinate (-t) = horizonCoordinate t := by
  simp [horizonCoordinate,radialUnit,Real.sinh_neg,Real.cosh_neg,neg_div]

theorem horizonCoordinate_continuous : Continuous horizonCoordinate := by
  have hu : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun t => (radialUnit_hasDerivAt t).continuousAt)
  exact continuous_const.sub (hu.pow 2)

/-- The added mass cancels the restored free generator's mass, leaving the original potential. -/
def principalWavePotential (q : XiZeroCopy) (i : Fin 3) (t : ℝ) : ℂ :=
  ((2*Real.pi)^(2 : ℕ):ℝ)+principalExponent q i*(principalExponent q i-1)*(horizonCoordinate t:ℂ)

theorem principalWavePotential_bound (q : XiZeroCopy) (i : Fin 3) (t : ℝ) :
    ‖principalWavePotential q i t‖ ≤ (2*Real.pi)^(2 : ℕ)+‖principalExponent q i*(principalExponent q i-1)‖ := by
  have hz : ‖(horizonCoordinate t:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (horizonCoordinate_nonneg t)]
    exact horizonCoordinate_le_one t
  unfold principalWavePotential
  calc
    _ ≤ ‖(((2*Real.pi)^(2 : ℕ):ℝ):ℂ)‖+
        ‖principalExponent q i*(principalExponent q i-1)‖*‖(horizonCoordinate t:ℂ)‖ := by
      simpa only [norm_mul] using norm_add_le (((2*Real.pi)^(2 : ℕ):ℝ):ℂ)
        (principalExponent q i*(principalExponent q i-1)*(horizonCoordinate t:ℂ))
    _ ≤ _ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hz
        (norm_nonneg (principalExponent q i*(principalExponent q i-1)))).trans_eq (mul_one _))

theorem principalWavePotential_measurable (q : XiZeroCopy) (i : Fin 3) :
    Measurable (principalWavePotential q i) :=
  (continuous_const.add (continuous_const.mul
    (Complex.continuous_ofReal.comp horizonCoordinate_continuous))).measurable

def principalWavePotentialOp (q : XiZeroCopy) (i : Fin 3) : FourierRealL2 →L[ℂ] FourierRealL2 :=
  lpBoundedMulCLM (principalWavePotential_measurable q i)
    (add_nonneg (sq_nonneg _) (norm_nonneg _)) (principalWavePotential_bound q i)

theorem principalWavePotentialOp_ae (q : XiZeroCopy) (i : Fin 3) (f : FourierRealL2) :
    principalWavePotentialOp q i f =ᵐ[volume] (fun t => principalWavePotential q i t*f t) :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem principalWavePotentialOp_reflection (q : XiZeroCopy) (i : Fin 3) (f : FourierRealL2) :
    principalWavePotentialOp q i (l2Reflection f) = l2Reflection (principalWavePotentialOp q i f) := by
  apply lpBoundedMulCLM_reflection
  intro t
  simp only [principalWavePotential,horizonCoordinate_even]

end
end RHTower.D4BMJointSource
