import GaloisForLFunctions.CountingHolography.Sections.TheDyadicPrimeWeightOfSquareConductors
import GaloisForLFunctions.RHTower.NymanMellinGaugeCollapse
import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth
import GaloisForLFunctions.CountingHolography.TheIntegerProbesAreNotIntegerValued

/-!
# Critical zeros separate the square prime profile from factorial kernels

The logarithmic profile is twice the spline autocorrelation minus its
log-four translate. Its Mellin transform is nonzero at each critical zero
seen by the spline. Finite fractional-part combinations vanish there.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Complex MeasureTheory Filter Finset Topology Zeta23 ArithmeticCastelnuovoSeveri
open BiScaleUncertainty.ChebyshevGauge ArithmeticWeightTheory ArithmeticOrientationGeometry
open RenormalizedIntersectionTheory

private theorem lift_autocorr : cx splineAutoCorr = EF.weilTest (cx cubicSpline) (cx cubicSpline) := by
  funext t
  simp only [cx,splineAutoCorr,weilTest_ofReal,Complex.ofReal_re]

private theorem transform_profile (t : ℂ) :
    paperFT (cx squareLogProfile) t =
      (2-cexp (I*t*(Real.log 4:ℝ)))*
        (paperFT (cx cubicSpline) t*starRingEnd ℂ (paperFT (cx cubicSpline) (starRingEnd ℂ t))) := by
  let H := EF.weilTest (cx cubicSpline) (cx cubicSpline)
  let c : Fin 2 → ℂ := ![2,-1]
  let x : Fin 2 → ℝ := ![0,Real.log 4]
  have hH (v : ℝ) : H v = (splineAutoCorr v:ℂ) := congrFun lift_autocorr.symm v
  have he : cx squareLogProfile = fun u => ∑ i : Fin 2, c i*H (u-x i) := by
    funext u
    simp only [c,x,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,sub_zero,
      hH,cx,squareLogProfile,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat,neg_one_mul,sub_eq_add_neg]
  have hc := (cx_contDiff contDiff_cubicSpline).continuous
  have hs := cx_hasCompactSupport hasCompactSupport_cubicSpline
  rw [he,_root_.RHTower.EvenSector.paperFT_sum_translate univ c x
    (EF.weilTest_contDiff (cx_contDiff contDiff_cubicSpline) hc hs).continuous (EF.weilTest_hasCompactSupport hs hs)]
  rw [show H = EF.weilTest (cx cubicSpline) (cx cubicSpline) from rfl,EF.paperFT_weilTest hc hc hs hs]
  simp only [c,x,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,mul_one,neg_one_mul,Complex.conj_ofReal,sub_eq_add_neg]

private theorem mellin_prime_weight (t : ℂ) :
    mellin squarePrimeWeight (1/2+t*I) = paperFT (cx squareLogProfile) t := by
  rw [_root_.RHTower.mellin_eq_integral_exp_neg_mul_log,paperFT]
  rw [← integral_neg_eq_self (fun u : ℝ => cx squareLogProfile u * cexp (I*t*u)) volume]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  change cexp (-(1/2+t*I)*u)*squarePrimeWeight (Real.exp (-u)) =
    (squareLogProfile (-u):ℂ)*cexp (I*t*(-u:ℝ))
  rw [squarePrimeWeight,Real.log_exp,neg_neg,Complex.ofReal_mul,Complex.ofReal_exp]
  rw [← mul_assoc,← Complex.exp_add]
  have he : -(1/2+t*I)*u+((u/2:ℝ):ℂ) = I*t*(-u:ℝ) := by push_cast; ring
  rw [he,mul_comm]

/-- The pole at one cancels exactly in the dyadic profile. -/
theorem squarePrimeWeight_mean_zero :
    (∫ v in Set.Ioi 0, squarePrimeWeight v) = 0 := by
  have hl : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have hi : I*(-I/2)=1/2 := by
    calc I*(-I/2) = -(I*I)/2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have hs : 1/2+(-I/2)*I=1 := by rw [mul_comm _ I,hi]; norm_num
  have hphase : cexp (I*(-I/2)*(Real.log 4:ℝ))=2 := by
    rw [hi,hl,Complex.ofReal_mul,Complex.ofReal_ofNat,
      show (1/2:ℂ)*(2*(Real.log 2:ℝ))=(Real.log 2:ℝ) by ring,← Complex.ofReal_exp,
      Real.exp_log (by norm_num : (0:ℝ)<2),Complex.ofReal_ofNat]
  have h := mellin_prime_weight (-I/2)
  rw [hs,transform_profile,hphase,sub_self,zero_mul] at h
  simpa only [mellin,sub_self,Complex.cpow_zero,one_smul] using h

/-- Every critical zero seen by the cubic spline survives the subtraction
of the second conductor. -/
theorem mellin_squarePrimeWeight_ne_zero {ρ : ℂ} (hρ : ρ ∈ criticalSeen) :
    mellin squarePrimeWeight ρ ≠ 0 := by
  obtain ⟨_,hre,hseen⟩ := hρ
  have he : 1/2+(ρ.im:ℂ)*I = ρ := Complex.ext (by simp [hre]) (by simp)
  rw [← he,mellin_prime_weight,transform_profile,Complex.conj_ofReal]
  have hu : ‖cexp (I*(ρ.im:ℂ)*(Real.log 4:ℝ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re,Complex.mul_im]
  have hphase : (2:ℂ)-cexp (I*(ρ.im:ℂ)*(Real.log 4:ℝ)) ≠ 0 := by
    intro hh
    rw [← sub_eq_zero.mp hh] at hu
    norm_num at hu
  exact mul_ne_zero hphase (mul_ne_zero hseen (map_ne_zero (starRingEnd ℂ) hseen))

/-- Away from the critical line the four-box transform and its conjugate
are nonzero. The phase can only have modulus two on the boundary Re s = 1. -/
theorem mellin_squarePrimeWeight_off_line {ρ : ℂ} (h₁ : ρ.re < 1) (hhalf : ρ.re ≠ 1/2) :
    mellin squarePrimeWeight ρ ≠ 0 := by
  let z : ℂ := ⟨ρ.im,1/2-ρ.re⟩
  have he : 1/2+z*I = ρ := by
    apply Complex.ext <;> simp [z,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  have hz : z.im ≠ 0 := sub_ne_zero.mpr (Ne.symm hhalf)
  have hzc : (starRingEnd ℂ z).im ≠ 0 := by simpa only [Complex.conj_im,neg_ne_zero] using hz
  have hl : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hr : (I*z*(Real.log 4:ℝ)).re = (ρ.re-1/2)*Real.log 4 := by
    simp [Complex.mul_re,Complex.mul_im,z,sub_neg_eq_add] <;> ring
  have hu : ‖cexp (I*z*(Real.log 4:ℝ))‖ < 2 := by
    rw [Complex.norm_exp,hr]
    apply lt_of_lt_of_eq _ (Real.exp_log (by norm_num : (0:ℝ)<2))
    apply Real.exp_lt_exp.mpr
    rw [hl]
    have hh : 2*(ρ.re-1/2) < 1 := by linarith only [h₁]
    linarith only [mul_lt_mul_of_pos_right hh (Real.log_pos (by norm_num : (1:ℝ)<2))]
  have hp : (2:ℂ)-cexp (I*z*(Real.log 4:ℝ)) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h] at hu
    norm_num at hu
  rw [← he,mellin_prime_weight,transform_profile]
  exact mul_ne_zero hp (mul_ne_zero (paperFT_cubicSpline_ne_zero hz)
    (map_ne_zero (starRingEnd ℂ) (paperFT_cubicSpline_ne_zero hzc)))

/-- No finite sum of fractional-part kernels agrees with the square
prime test on the positive half-line, even almost everywhere. -/
theorem nymanCombination_ne_squarePrimeWeight {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) :
    ¬ (NymanMellin.nymanCombination c a =ᵐ[volume.restrict (Set.Ioi 0)] squarePrimeWeight) := by
  obtain ⟨ρ,hρ⟩ := criticalSeen_infinite.nonempty
  have hZ : IsNontrivialZero ρ := hρ.1
  have hre := hρ.2.1
  have h₀ := NymanMellin.mellin_nymanCombination c a ha
    (s := ρ) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  rw [hZ.1,mul_zero,zero_div,neg_zero] at h₀
  intro he
  apply mellin_squarePrimeWeight_ne_zero hρ
  refine Eq.trans ?_ h₀
  unfold mellin
  exact integral_congr_ae (he.mono fun x hx => by rw [hx])

#print axioms squarePrimeWeight_mean_zero
#print axioms mellin_squarePrimeWeight_ne_zero
#print axioms mellin_squarePrimeWeight_off_line
#print axioms nymanCombination_ne_squarePrimeWeight

end GaloisForLFunctions.CountingHolography.Sections
