import GaloisForLFunctions.CountingHolography.Sections.ThreeSquareConductorsWithZeroPoleDegree
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.UnboundedOverlapIsTheRiemannHypothesis
import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth
import GaloisForLFunctions.HeckeKreinToeplitz.TheGoldenCurveIsDecidedOnItsTowerButNotOnTheLattice

/-!
# A three-graph spline killing both poles

On the conductors 1, 4 and 16 take coefficients 2, −5 and 2. The
Fourier multiplier has its only roots at the two boundary moduli.
Thus both pole samples vanish and every interior off-line zero remains
visible to the integer translates of this fixed signed spline.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Complex Zeta23 ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open SquareRootThreshold BiScaleUncertainty.ChebyshevGauge SpacingScaleHarmonicAnalysis

/-- The signed divisor whose two exponential degrees vanish. -/
def twoPoleDivisor : Fin 16 → ℤ := threeGraphDivisor 0 3 15 2 (-5) (-2)

def negativePoleDegree {N : ℕ} (a : Fin N → ℤ) : ℝ :=
  ∑ i : Fin N, (Real.sqrt ((i : ℝ)+1))⁻¹*(a i : ℝ)

theorem twoPoleDivisor_degrees :
    positivePoleDegree twoPoleDivisor = 0 ∧ negativePoleDegree twoPoleDivisor = 0 := by
  unfold positivePoleDegree negativePoleDegree twoPoleDivisor
  constructor <;> rw [sum_threeGraphDivisor] <;> norm_num

/-- The common spline on the three conductors. -/
def twoPoleAtom := splineSource twoPoleDivisor

private theorem atom_mem : twoPoleAtom ∈ realTests := by
  unfold twoPoleAtom splineSource
  constructor
  · exact ContDiff.sum fun i _ => contDiff_const.mul
      (contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const))
  · let F (i : Fin 16) := fun u : ℝ => (twoPoleDivisor i : ℝ)*cubicSpline (u-Real.log ((i : ℝ)+1))
    have he : (fun u => ∑ i, F i u) = ∑ i, F i := by
      funext u
      simp only [Finset.sum_apply]
    change HasCompactSupport (fun u => ∑ i, F i u)
    rw [he]
    exact HasCompactSupport.finset_sum fun i _ =>
      (hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight (Real.log ((i : ℝ)+1)))).mul_left

private theorem atom_sum (F : Fin 16 → ℂ) :
    ∑ i, (twoPoleDivisor i : ℂ)*F i = 2*F 0-5*F 3+2*F 15 := by
  simp only [twoPoleDivisor,threeGraphDivisor,Pi.add_apply,Pi.single_apply,Int.cast_add,
    Int.cast_ite,Int.cast_zero,Int.cast_neg,Int.cast_ofNat,add_mul,ite_mul,zero_mul,
    sum_add_distrib,sum_ite_eq',mem_univ,if_true]
  ring

/-- Translation by the log of four in Fourier coordinates. -/
def twoPolePhase (z : ℂ) := Complex.exp (Complex.I*z*(Real.log 4 : ℝ))

/-- Factorization of the multiplier on the entire Fourier plane. -/
theorem paperFT_twoPoleAtom (z : ℂ) : paperFT (cx twoPoleAtom) z =
    ((2*twoPolePhase z-1)*(twoPolePhase z-2))*paperFT (cx cubicSpline) z := by
  have hc : cx twoPoleAtom = fun u =>
      ∑ i : Fin 16, (twoPoleDivisor i : ℂ)*cx cubicSpline (u-Real.log ((i : ℝ)+1)) := by
    funext u
    simp only [cx,twoPoleAtom,splineSource,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_intCast]
  rw [hc,_root_.RHTower.EvenSector.paperFT_sum_translate _ _ _
    (cx_contDiff contDiff_cubicSpline).continuous (cx_hasCompactSupport hasCompactSupport_cubicSpline),atom_sum]
  congr 1
  have h16 : Real.log 16 = 2*Real.log 4 := by
    rw [show (16:ℝ) = 4^2 by norm_num,Real.log_pow]
    norm_num
  have h₀ : ((0 : Fin 16) : ℝ)+1=1 := by change ((0:ℕ):ℝ)+1=1; norm_num
  have h₃ : ((3 : Fin 16) : ℝ)+1=4 := by change ((3:ℕ):ℝ)+1=4; norm_num
  have h₁₅ : ((15 : Fin 16) : ℝ)+1=16 := by change ((15:ℕ):ℝ)+1=16; norm_num
  rw [h₀,h₃,h₁₅,Real.log_one,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
  rw [h16,Complex.ofReal_mul]
  rw [show Complex.I*z*((↑(2:ℝ):ℂ)*↑(Real.log 4)) =
    Complex.I*z*↑(Real.log 4)+Complex.I*z*↑(Real.log 4) by push_cast; ring,Complex.exp_add]
  unfold twoPolePhase
  ring

private theorem log_four : Real.log 4 = 2*Real.log 2 := by
  rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
  norm_num

theorem paperFT_twoPoleAtom_poles : paperFT (cx twoPoleAtom) (Complex.I/2) = 0 ∧
    paperFT (cx twoPoleAtom) (-(Complex.I/2)) = 0 := by
  have hplus : twoPolePhase (Complex.I/2) = 1/2 := by
    unfold twoPolePhase
    rw [log_four,Complex.ofReal_mul]
    have he : Complex.I*(Complex.I/2)*((↑(2:ℝ):ℂ)*↑(Real.log 2)) = -↑(Real.log 2) := by
      push_cast
      linear_combination (Real.log 2 : ℂ)*Complex.I_sq
    rw [he,Complex.exp_neg,← Complex.ofReal_exp,Real.exp_log (by norm_num : 0<(2:ℝ))]
    norm_num
  have hminus : twoPolePhase (-(Complex.I/2)) = 2 := by
    unfold twoPolePhase
    rw [log_four,Complex.ofReal_mul]
    have he : Complex.I*(-(Complex.I/2))*((↑(2:ℝ):ℂ)*↑(Real.log 2)) = ↑(Real.log 2) := by
      push_cast
      linear_combination -(Real.log 2 : ℂ)*Complex.I_sq
    rw [he,← Complex.ofReal_exp,Real.exp_log (by norm_num : 0<(2:ℝ))]
    norm_num
  rw [paperFT_twoPoleAtom,paperFT_twoPoleAtom,hplus,hminus]
  constructor <;> ring

private theorem phase_bounds {z : ℂ} (hz : |z.im| < 1/2) :
    (1:ℝ)/2 < ‖twoPolePhase z‖ ∧ ‖twoPolePhase z‖ < 2 := by
  have hl := Real.log_pos (by norm_num : (1:ℝ)<2)
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hz
  have hp := mul_lt_mul_of_pos_right hhi hl
  have hm := mul_lt_mul_of_pos_right hlo hl
  have he : ‖twoPolePhase z‖ = Real.exp (-z.im*(2*Real.log 2)) := by
    rw [twoPolePhase,Complex.norm_exp,log_four]
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,mul_zero,sub_zero,zero_sub]
  rw [he]
  have h₁ := Real.exp_lt_exp.mpr (show -Real.log 2 < -z.im*(2*Real.log 2) by linarith only [hp])
  have h₂ := Real.exp_lt_exp.mpr (show -z.im*(2*Real.log 2) < Real.log 2 by linarith only [hm])
  rw [Real.exp_neg,Real.exp_log (by norm_num : 0<(2:ℝ))] at h₁
  rw [Real.exp_log (by norm_num : 0<(2:ℝ))] at h₂
  simpa only [one_div] using And.intro h₁ h₂

/-- On either open half of the critical strip the atom sees every spectral parameter. -/
theorem paperFT_twoPoleAtom_ne_zero {z : ℂ} (hz : |z.im| < 1/2) (hne : z.im ≠ 0) :
    paperFT (cx twoPoleAtom) z ≠ 0 := by
  rw [paperFT_twoPoleAtom]
  obtain ⟨hl,hu⟩ := phase_bounds hz
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (paperFT_cubicSpline_ne_zero hne)
  · intro he
    have hphase : twoPolePhase z = 1/2 := by linear_combination he/2
    rw [hphase] at hl
    norm_num at hl
  · intro he
    rw [sub_eq_zero.mp he] at hu
    norm_num at hu

private theorem sees_strip_point {ρ : ℂ} (hr : 1/2 < ρ.re) (hu : ρ.re < 1) : Sees twoPoleAtom ρ := by
  have he : (gammaOf ρ).im = 1/2-ρ.re := by simp [gammaOf,Complex.div_I]
  have hb : |(gammaOf ρ).im| < 1/2 := by rw [he,abs_lt]; constructor <;> linarith only [hr,hu]
  have hn := im_gammaOf_ne_zero hr.ne'
  refine ⟨paperFT_twoPoleAtom_ne_zero hb hn,paperFT_twoPoleAtom_ne_zero ?_ ?_⟩
  · simpa only [Complex.conj_im,abs_neg] using hb
  · simpa only [Complex.conj_im,neg_ne_zero] using hn

theorem seenRightZeros_twoPoleAtom : seenRightZeros zetaZeroConfig twoPoleAtom = SquareRootThreshold.rightZeros zetaZeroConfig := by
  ext ρ
  simp only [seenRightZeros,SquareRootThreshold.rightZeros,Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz,hr,_⟩
    exact ⟨hz,hr⟩
  · rintro ⟨hz,hr⟩
    exact ⟨hz,hr,sees_strip_point hr (show IsNontrivialZero ρ from hz).2.2⟩

/-- The full number of distinct right zeros is already carried by translates
of one explicitly integral two-pole-free atom at integer conductors. -/
theorem twoPoleAtom_integer_index (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ logShifts ∧ n ≤ HTGeometry.hermNegIndex (weilGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx twoPoleAtom))) ↔
      (n : ℕ∞) ≤ (SquareRootThreshold.rightZeros zetaZeroConfig).encard := by
  rw [← seenRightZeros_twoPoleAtom,← zeta_orientationIndex_law atom_mem denseShifts_ratHecke n]
  constructor
  · rintro ⟨S,hS,hn⟩
    exact ⟨S,hS.trans logShifts_subset_ratHeckeShifts,hn⟩
  · rintro ⟨S,hS,hn⟩
    obtain ⟨c,hc⟩ := exists_add_mem_logShifts S hS
    refine ⟨S.image (·+c),fun t ht => ?_,by rw [negIndex_translate_add]; exact hn⟩
    obtain ⟨s,hs,rfl⟩ := mem_image.mp ht
    exact hc s hs

/-- The same two-pole-free atom detects infinitely many negative squares
for the golden datum, already on any pair of distinct prime dilations. -/
theorem twoPoleAtom_golden_index {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    HeckeKreinToeplitz.negIndex (HeckeKreinToeplitz.orbitKernel goldenConfig twoPoleAtom ∘
      (HeckeKreinToeplitz.twoPrimeLattice hp hq).subtype) = ⊤ := by
  rw [HeckeKreinToeplitz.negIndex_orbitKernel_twoPrime _ temperedConfig_goldenConfig atom_mem hp hq hne]
  apply Set.encard_eq_top_iff.mpr
  have hβ : ‖goldenDatum.β 0‖ = Real.goldenRatio := by
    change ‖((Real.goldenRatio : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.goldenRatio_pos]
  have hq' := Real.log_lt_log (by norm_num : (0:ℝ)<4) (by norm_num : (4:ℝ)<5)
  rw [log_four] at hq'
  have hφ := Real.log_lt_log Real.goldenRatio_pos Real.goldenRatio_lt_two
  have hφ' : Real.log Real.goldenRatio/Real.log 5 < 1/2 :=
    (div_lt_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<5))).mpr (by linarith only [hφ,hq'])
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℤ => goldenDatum.zetaZero 0 k)
  · intro k k' he
    have hi := congrArg Complex.im he
    simp only [CurveDatum.im_zetaZero,add_right_inj] at hi
    exact_mod_cast mul_right_cancel₀ goldenDatum.period_pos.ne' hi
  · intro k
    have hr := (goldenDatum.re_zetaZero_gt_iff 0 k).mpr (hβ.symm ▸ Real.one_lt_goldenRatio)
    refine ⟨⟨(0,k),rfl⟩,hr,sees_strip_point hr ?_⟩
    rw [CurveDatum.re_zetaZero,hβ]
    change 1/2+Real.log Real.goldenRatio/Real.log 5 < 1
    linarith only [hφ']

#print axioms twoPoleAtom_golden_index
#print axioms twoPoleAtom_integer_index
#print axioms paperFT_twoPoleAtom_poles
#print axioms twoPoleDivisor_degrees

end GaloisForLFunctions.CountingHolography.Sections
