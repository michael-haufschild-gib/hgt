import GaloisForLFunctions.ArithmeticCouplingTheory.TheConeCouplingHasNoDeepestZero
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineWeilCoefficient
import GaloisForLFunctions.RHTower.ThetaRenewalCoshFactorization

/-!
# Sixth-moment decay of the actual spline residues

The exact eighth-power spline coefficient, together with tempered zero
energy, gives a finite sixth ordinate moment. One mixed clock difference
preserves this moment and yields a sixth-power tail bound.
-/

open Complex Finset Filter Topology
open Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
open ConeCoupling ConeMoments


/-- Eighth-power decay of the actual multiplicity-weighted spline summand. -/
lemma norm_wt_le_eighth (ρ : zetaZeroConfig.carrier)
    (hγ : 0 < |(ρ : ℂ).im|) :
    ‖wt ρ‖ ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp (1/2))^8 /
      |(ρ : ℂ).im|^8 := by
  let z : ℂ := (ρ : ℂ)-1/2
  have hz : z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [z,Complex.sub_im,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero,Complex.zero_im] at hi
    exact hγ.ne' (by rw [hi,abs_zero])
  have hs := zetaZeroConfig.strip ρ.1 ρ.2
  have hr : |z.re| ≤ 1/2 := by
    simp only [z,Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]
    rw [abs_le]
    constructor <;> linarith [hs.1,hs.2]
  have hnum : ‖Complex.sinh z‖ ≤ Real.exp (1/2) :=
    (_root_.RHTower.norm_sinh_le_exp_abs_re' z).trans (Real.exp_le_exp.mpr hr)
  have hden : |(ρ : ℂ).im| ≤ ‖z‖ := by
    simpa only [z,Complex.sub_im,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero] using Complex.abs_im_le_norm z
  have hw := cubicSpline_Wsummand hz
  have he : (1/2:ℂ)+z=(ρ:ℂ) := by dsimp only [z]; ring
  rw [he] at hw
  change ‖zetaZeroConfig.Wsummand (fun x => (cubicSpline x:ℂ))
    (fun x => (cubicSpline x:ℂ)) ρ‖ ≤ _
  rw [hw,norm_mul,Complex.norm_natCast,norm_pow,norm_div,div_pow]
  calc
    _ ≤ (zetaZeroConfig.mult ρ : ℝ)*((Real.exp (1/2))^8/|(ρ:ℂ).im|^8) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        _ ≤ (Real.exp (1/2))^8/‖z‖^8 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnum 8)
            (pow_nonneg (norm_nonneg _) 8)
        _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg (Real.exp_pos _).le 8)
          (pow_pos hγ 8) (pow_le_pow_left₀ hγ.le hden 8)
    _ = _ := by ring

lemma sixth_eighth_ratio_le {y δ : ℝ} (hy : 1 ≤ y) (hδ : |δ| ≤ 1/2) :
    (1+y)^6/y^8 ≤ 256/(1+y^2+δ^2) := by
  have hy0 : 0 < y := by linarith only [hy]
  have hδ2 : δ^2 ≤ 1/4 := by
    have hh := abs_le.mp hδ
    nlinarith only [hh.1,hh.2,sq_nonneg (δ-1/2),sq_nonneg (δ+1/2)]
  have hy2 : 1 ≤ y^2 := one_le_pow₀ hy
  have hden : 1+y^2+δ^2 ≤ 4*y^2 := by linarith only [hδ2,hy2]
  have hpow : (1+y)^6 ≤ (2*y)^6 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hy]) 6
  rw [div_le_div_iff₀ (pow_pos hy0 8) (by positivity)]
  calc
    _ ≤ (2*y)^6*(4*y^2) := mul_le_mul hpow hden (by positivity) (by positivity)
    _ = _ := by ring

/-- Actual spline weights have a finite sixth ordinate moment. -/
theorem summable_sixth_height_wt :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (1+|(ρ:ℂ).im|)^6*‖wt ρ‖ := by
  have he := SquareRootThreshold.temperedConfig_zetaZeroConfig
  have hs := (summable_norm_wt.mul_left 64).add (he.mul_left (256*(Real.exp (1/2))^8))
  refine hs.of_nonneg_of_le (fun ρ => by positivity) fun ρ => ?_
  by_cases hγ : |(ρ:ℂ).im| ≤ 1
  · have hpow : (1+|(ρ:ℂ).im|)^6 ≤ 64 := by
      calc
        _ ≤ (2:ℝ)^6 := pow_le_pow_left₀ (by positivity) (by linarith only [hγ]) 6
        _ = _ := by norm_num
    have hmain := mul_le_mul_of_nonneg_right hpow (norm_nonneg (wt ρ))
    exact hmain.trans (le_add_of_nonneg_right (by
      change 0 ≤ 256*(Real.exp (1/2))^8*((zetaZeroConfig.mult ρ:ℝ)/(1+Complex.normSq (gammaOf ρ)))
      have hn := Complex.normSq_nonneg (gammaOf ρ)
      positivity))
  · have hγ1 : 1 ≤ |(ρ:ℂ).im| := (lt_of_not_ge hγ).le
    have hγ0 : 0 < |(ρ:ℂ).im| := lt_of_lt_of_le zero_lt_one hγ1
    have hstrip := zetaZeroConfig.strip ρ.1 ρ.2
    have hδ : |1/2-(ρ:ℂ).re| ≤ 1/2 := by
      rw [abs_le]; constructor <;> linarith [hstrip.1,hstrip.2]
    have hratio := sixth_eighth_ratio_le hγ1 hδ
    have hn : Complex.normSq (gammaOf ρ)=|(ρ:ℂ).im|^2+(1/2-(ρ:ℂ).re)^2 := by
      rw [Complex.normSq_apply,SquareRootThreshold.re_gammaOf,SquareRootThreshold.im_gammaOf,sq_abs]
      ring
    have hmain : (1+|(ρ:ℂ).im|)^6*‖wt ρ‖ ≤
        256*(Real.exp (1/2))^8*((zetaZeroConfig.mult ρ:ℝ)/(1+Complex.normSq (gammaOf ρ))) := by
      calc
        _ ≤ (1+|(ρ:ℂ).im|)^6*((zetaZeroConfig.mult ρ:ℝ)*(Real.exp (1/2))^8/|(ρ:ℂ).im|^8) :=
          mul_le_mul_of_nonneg_left (norm_wt_le_eighth ρ hγ0) (by positivity)
        _ = ((zetaZeroConfig.mult ρ:ℝ)*(Real.exp (1/2))^8)*
            ((1+|(ρ:ℂ).im|)^6/|(ρ:ℂ).im|^8) := by ring
        _ ≤ ((zetaZeroConfig.mult ρ:ℝ)*(Real.exp (1/2))^8)*
            (256/(1+|(ρ:ℂ).im|^2+(1/2-(ρ:ℂ).re)^2)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := by rw [hn]; ring
    exact hmain.trans (le_add_of_nonneg_left (by positivity))

/-- The residue read by one mixed difference of the cone coupling. -/
def mixedResidue (a b : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  (mult a ρ-1)*(mult b ρ-1)*wt ρ

lemma norm_mixedResidue_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ρ : zetaZeroConfig.carrier) :
    ‖mixedResidue a b ρ‖ ≤ (Real.exp (a/2)+1)*(Real.exp (b/2)+1)*‖wt ρ‖ := by
  simp only [mixedResidue,norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
  · exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith only [norm_mult_le ha ρ])
  · exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith only [norm_mult_le hb ρ])

/-- Mixed differencing retains the finite sixth ordinate moment. -/
theorem summable_sixth_height_mixedResidue {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (1+|(ρ:ℂ).im|)^6*‖mixedResidue a b ρ‖ := by
  refine (summable_sixth_height_wt.mul_left
    ((Real.exp (a/2)+1)*(Real.exp (b/2)+1))).of_nonneg_of_le
    (fun ρ => by positivity) fun ρ => ?_
  calc
    _ ≤ (1+|(ρ:ℂ).im|)^6*((Real.exp (a/2)+1)*(Real.exp (b/2)+1)*‖wt ρ‖) :=
      mul_le_mul_of_nonneg_left (norm_mixedResidue_le ha hb ρ) (by positivity)
    _ = _ := by ring

lemma summable_norm_mixedResidue {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable fun ρ : zetaZeroConfig.carrier => ‖mixedResidue a b ρ‖ := by
  exact (summable_norm_wt.mul_left ((Real.exp (a/2)+1)*(Real.exp (b/2)+1))).of_nonneg_of_le
    (fun ρ => norm_nonneg _) (norm_mixedResidue_le ha hb)

/-- The actual mixed residues have a sixth-power tail bound. -/
theorem mixedResidue_tail_le {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T) :
    (∑' ρ : zetaZeroConfig.carrier, if T < |(ρ:ℂ).im| then ‖mixedResidue a b ρ‖ else 0) ≤
      (∑' ρ : zetaZeroConfig.carrier, (1+|(ρ:ℂ).im|)^6*‖mixedResidue a b ρ‖)/(1+T)^6 := by
  classical
  have hs := summable_sixth_height_mixedResidue ha hb
  have ht : Summable fun ρ : zetaZeroConfig.carrier =>
      if T < |(ρ:ℂ).im| then ‖mixedResidue a b ρ‖ else 0 := by
    refine (summable_norm_mixedResidue ha hb).of_nonneg_of_le
      (fun ρ => by positivity) fun ρ => ?_
    split_ifs <;> simp only [le_refl,norm_nonneg]
  have hden : 0 < (1+T)^6 := by positivity
  rw [← tsum_div_const]
  apply Summable.tsum_le_tsum _ ht (hs.div_const _)
  intro ρ
  split_ifs with hγ
  · apply (le_div_iff₀ hden).2
    have hp : (1+T)^6 ≤ (1+|(ρ:ℂ).im|)^6 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hγ]) 6
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hp (norm_nonneg (mixedResidue a b ρ))
  · positivity

#print axioms summable_sixth_height_wt
#print axioms summable_sixth_height_mixedResidue
#print axioms mixedResidue_tail_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
