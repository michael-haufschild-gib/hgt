import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativePhysicalSourceValue
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalAngularCutoffCalibration

/-! Weighted representatives of the original physical angular field and every source channel. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMModularCore D4BMAngularSeries
noncomputable section
set_option autoImplicit false

/-- One inverse height makes the full physical testing field a vector in the original angular Hilbert space. -/
def physicalDualDensity (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  (z.im:ℂ)⁻¹ * scalar (physicalAngularParameter q) (coordinates z)

/-- The weight is applied to the full original field, including every Fourier mode. -/
theorem physicalDualDensity_memLp (q : XiZeroCopy) :
    MemLp (physicalDualDensity q) 2 D4BMModularCore.measure := by
  let u := physicalAngularParameter q
  obtain ⟨C,hC,hb⟩ := weighted_tail_bounded u (-1) 3 (by norm_num)
  have hc : ContinuousOn (fun z : Fin 2 → ℝ => (z 1:ℂ)^(-1:ℂ)*scalar u z) domain :=
    (height_cpow_contDiffOn (-1) 0).continuousOn.mul (cuspLeg_contDiffOn .scalar u).continuousOn
  have hm := cuspBound_memLp _ hc (‖reflectedCompletedLambda ((q.1:ℂ)-1)‖+C) (by
    intro z hz
    have hy : 0 < z 1 := by linarith
    have hn : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have he : (z 1:ℂ)^(-1:ℂ)*scalar u z =
        reflectedCompletedLambda ((q.1:ℂ)-1)*(z 1:ℂ)^(-((q.1:ℂ)/2))+
        (z 1:ℂ)^(-1:ℂ)*tail u z := by
      change (z 1:ℂ)^(-1:ℂ)*(principal u z+tail u z)=_
      rw [mul_add,physicalScalar_principal,mul_left_comm,← Complex.cpow_add _ _ hn]
      rw [show (-1:ℂ)+(1-(q.1:ℂ)/2) = -((q.1:ℂ)/2) by ring]
    have hew : ‖(z 1:ℂ)^(-((q.1:ℂ)/2))‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      simp only [Complex.neg_re,Complex.div_ofNat_re]
      linarith [(xi_divisor_support_re_mem_open_unit q.1).1]
    rw [he]
    calc
      _ ≤ ‖reflectedCompletedLambda ((q.1:ℂ)-1)*(z 1:ℂ)^(-((q.1:ℂ)/2))‖+
          ‖(z 1:ℂ)^(-1:ℂ)*tail u z‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul]
        exact add_le_add
          (by simpa using mul_le_mul_of_nonneg_left hew (norm_nonneg _)) (hb z hz.le))
  apply hm.ae_eq
  filter_upwards with z
  change (z.im:ℂ)^(-1:ℂ)*scalar u (coordinates z) =
    (z.im:ℂ)⁻¹*scalar u (coordinates z)
  rw [Complex.cpow_neg_one]

/-- Every fixed height power of the actual residual is admitted in the original quotient Hilbert space. -/
theorem weightedSquareResidual_memLp (q : XiZeroCopy) (w : ℂ) :
    MemLp (fun z : UpperHalfPlane => (z.im:ℂ)^w * squareResidual q (coordinates z))
      2 D4BMModularCore.measure := by
  obtain ⟨C,_,hb⟩ := squareResidual_fd_weighted_bound q w
  have hcoords : Continuous coordinates := by
    apply continuous_pi; intro i; fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have hc : Continuous (fun z : UpperHalfPlane => (z.im:ℂ)^w * squareResidual q (coordinates z)) :=
    ((height_cpow_contDiffOn w 0).continuousOn.mul (squareResidual_continuousOn q)).comp_continuous
      hcoords (fun z => z.im_pos)
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  exact hb z hz

/-- Each original differential cutoff channel remains admitted after any fixed height power. -/
theorem weightedCutoffCommutator_memLp (w k : ℂ) :
    MemLp (fun z : UpperHalfPlane => (z.im:ℂ)^w * cutoffCommutator k (coordinates z))
      2 D4BMModularCore.measure := by
  apply cuspBound_memLp _ ((height_cpow_contDiffOn w 0).continuousOn.mul
    (cutoffCommutator_continuousOn k)) 0
  intro z hz
  change ‖(z 1:ℂ)^w * cutoffCommutator k z‖ ≤ 0
  rw [cutoffCommutator_high k z hz,mul_zero,norm_zero]

end
end RHTower.D4BMJointSource
