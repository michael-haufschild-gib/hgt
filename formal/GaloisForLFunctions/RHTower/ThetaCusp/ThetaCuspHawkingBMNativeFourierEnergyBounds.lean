import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspScalarEnergy
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspPositiveMean

/-! Native scalar energy and complete Fourier mass bounds at both height ends. -/
open Complex MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMModularCore D4BMAngularSeries D4BMCuspProjection
noncomputable section

/-- The original modular square identity controls the full scalar's squared norm. -/
theorem nativeScalar_norm_sq_bound (q : XiZeroCopy) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z : UpperHalfPlane,
      ‖scalar (center q) (coordinates z)‖^(2 : ℕ) ≤ A+B*positiveCuspRows 2 z := by
  obtain ⟨A,hA,ha⟩ := globalSquareResidual_bounded q
  obtain ⟨B,hB,hb⟩ := nativeSquareCutoffHeight_quadratic_bound q
  refine ⟨2*A,2*B,by positivity,by positivity,?_⟩
  intro z
  have hcut : ‖periodize (squareCutoffSeed q) z‖ ≤ B*positiveCuspRows 2 z := by
    rw [squareCutoffSeed_eq_heightSeed]
    exact highCuspHeight_periodize_norm_le _ (nativeSquareCutoffHeight_zero q) B hb z
  have he : fullSquarePotential q (coordinates z) = globalSquareResidual q z+periodize (squareCutoffSeed q) z := by
    rw [globalSquareResidual_eq_periodized]
    ring
  have hn : ‖fullSquarePotential q (coordinates z)‖ ≤ A+B*positiveCuspRows 2 z := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (ha z) hcut)
  simp only [fullSquarePotential,norm_mul,norm_div,norm_one,Complex.norm_ofNat] at hn
  nlinarith

/-- The entire coefficient norm mass has the original low-height two-power envelope. -/
theorem nativeAmplitudeMass_bound (q : XiZeroCopy) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ y : ℝ, 0 < y →
      amplitudeMass (center q) y ≤ A+B*(y^(2 : ℕ)+cuspReflectionNorm 2*y^(-1:ℝ)) := by
  obtain ⟨A,B,hA,hB,hb⟩ := nativeScalar_norm_sq_bound q
  refine ⟨A,B,hA,hB,?_⟩
  intro y hy
  have hs : Continuous (fun x : ℝ => scalar (center q) ![x,y]) :=
    (cuspLeg_contDiffOn .scalar (center q)).continuousOn.comp_continuous
      (by fun_prop) (fun _ => hy)
  have he (x : ℝ) : coordinates (ofComplex (⟨x,y⟩:ℂ)) = ![x,y] := by
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  have hline (x : ℝ) : ‖scalar (center q) ![x,y]‖^(2 : ℕ) ≤
      A+B*positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ)) := by
    simpa only [he x] using hb (ofComplex (⟨x,y⟩:ℂ))
  have hi : (∫ x in Ico (0:ℝ) 1, ‖scalar (center q) ![x,y]‖^(2 : ℕ)) ≤
      ∫ x in Ico (0:ℝ) 1, A+B*positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ)) :=
    integral_mono ((hs.norm.pow 2).integrableOn_Icc.mono_set Ico_subset_Icc_self)
    ((integrable_const A).add ((positiveCuspRows_horizontal_integrable 2 (by norm_num) hy).const_mul B)) hline
  have hsum : (∫ x in Ico (0:ℝ) 1, A+B*positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ))) =
      (∫ _x in Ico (0:ℝ) 1, A)+∫ x in Ico (0:ℝ) 1, B*positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ)) :=
    integral_add (integrable_const A) ((positiveCuspRows_horizontal_integrable 2 (by norm_num) hy).const_mul B)
  rw [unit_mean_scalar_norm_sq _ hy,hsum,integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left (positiveCuspRows_mean_le 2 (by norm_num) hy) hB
  norm_num only [Real.rpow_two,show (1:ℝ)-2 = -1 by norm_num] at hm
  have hc : (∫ _x in Ico (0:ℝ) 1, A) = A := by simp
  rw [hc] at hi
  nlinarith [amplitudeMass_nonneg (center q) y,sq_nonneg ‖principal (center q) ![0,y]‖]

/-- Every real power times the original full coefficient mass is bounded above height one. -/
theorem amplitudeMass_weighted_bounded (u : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → y^r*amplitudeMass u y ≤ C := by
  obtain ⟨C,hC,hb⟩ := weighted_tail_bounded u ((r/2:ℝ):ℂ) 1 (by norm_num)
  refine ⟨C^(2 : ℕ)/8,by positivity,?_⟩
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hy
  have he : (y^(r/2))^(2 : ℕ) = y^r := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hy0.le]
    congr 1
    norm_num
  have hpt (x : ℝ) : y^r*‖tail u ![x,y]‖^(2 : ℕ) ≤ C^(2 : ℕ) := by
    have h := hb ![x,y] hy
    change ‖(y:ℂ)^((r/2:ℝ):ℂ)*tail u ![x,y]‖ ≤ C at h
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy0] at h
    have hh := mul_self_le_mul_self (mul_nonneg (Real.rpow_nonneg hy0.le _) (norm_nonneg _)) h
    simpa only [Complex.ofReal_re,← pow_two,mul_pow,he] using hh
  have ht : Continuous (fun x : ℝ => tail u ![x,y]) :=
    (cuspTailPart_contDiffOn .scalar u).continuousOn.comp_continuous (by fun_prop) (fun _ => hy0)
  have hi : (∫ x in Ioc (-1/2:ℝ) (1/2), y^r*‖tail u ![x,y]‖^(2 : ℕ)) ≤
      ∫ _x in Ioc (-1/2:ℝ) (1/2), C^(2 : ℕ) :=
    integral_mono ((ht.norm.pow 2).integrableOn_Ioc.const_mul (y^r))
    (integrable_const (C^(2 : ℕ))) hpt
  rw [integral_const_mul,mean_tail_norm_sq u hy0] at hi
  have hc : (∫ _x in Ioc (-1/2:ℝ) (1/2), C^(2 : ℕ)) = C^(2 : ℕ) := by norm_num
  rw [hc] at hi
  nlinarith

end
end RHTower.D4BMJointSource
