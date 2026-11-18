import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity

/-!
# A quadratic depth bound for both confined rungs

The two reflected Laplace samples have the same frequency. Their
confinement modes have inner product independent of the depth. Subtracting
suitably scaled modes before applying Bessel's inequality accounts for
this common part in the joint trace bound for a single quartet.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExceptionalLayerTheory

open ExclusionOfTheCriticalState ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry

private theorem w8_restrict (F G : ℝ → ℝ) (hF : CriticalHalfLineEnergyDomain F) :
    (∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8*u))) = w8Pair F G :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
    rw [hF.support u (not_lt.mp hu), zero_mul, zero_mul]

/-- At a common frequency the combined cosine and sine inner product
is the half-line Laplace kernel for the sum of the two real rates. -/
theorem w8_quartet_mode_pair {z w : ℂ} (hz : -4 < z.re) (hw : -4 < w.re) (hi : z.im = w.im) :
    w8Pair (modeCos z) (modeCos w) + w8Pair (modeSin z) (modeSin w) = 1 / (8+z.re+w.re) := by
  have hr : 0 < 8+z.re+w.re := by linarith only [hz,hw]
  unfold w8Pair
  rw [← integral_add (integrable_w8Pair (isW8Target_modeCos hz) (isW8Target_modeCos hw))
    (integrable_w8Pair (isW8Target_modeSin hz) (isW8Target_modeSin hw))]
  have hfun : (fun u : ℝ => modeCos z u * modeCos w u * Real.exp (-(8*u)) +
      modeSin z u * modeSin w u * Real.exp (-(8*u))) =
      (Iio (0 : ℝ)).indicator (fun u => Real.exp ((8+z.re+w.re)*u)) := by
    funext u
    by_cases hu : u ∈ Iio (0 : ℝ)
    · simp only [modeCos,modeSin,hu,indicator_of_mem,hi]
      have he : Real.exp ((z.re+8)*u) * Real.exp ((w.re+8)*u) * Real.exp (-(8*u)) =
          Real.exp ((8+z.re+w.re)*u) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      calc
        _ = ((Real.cos (w.im*u))^2 + (Real.sin (w.im*u))^2) *
            (Real.exp ((z.re+8)*u) * Real.exp ((w.re+8)*u) * Real.exp (-(8*u))) := by ring
        _ = _ := by rw [Real.cos_sq_add_sin_sq,one_mul,he]
    · simp [modeCos,modeSin,hu]
  rw [hfun, integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_Iic hr, mul_zero, Real.exp_zero]

private def mix (s t : ℝ) (F G : ℝ → ℝ) := fun u => s*F u + t*G u

private theorem mix_target {F G : ℝ → ℝ} (hF : IsW8Target F) (hG : IsW8Target G) (s t : ℝ) :
    IsW8Target (mix s t F G) := isW8Target_add (isW8Target_const_mul hF s) (isW8Target_const_mul hG t)

private theorem mix_pair {F G H : ℝ → ℝ} (hF : IsW8Target F) (hG : IsW8Target G)
    (hH : IsW8Target H) (s t : ℝ) :
    w8Pair (mix s t F G) H = s*w8Pair F H + t*w8Pair G H := by
  exact (w8Pair_add_left (isW8Target_const_mul hF s) (isW8Target_const_mul hG t) hH).trans
    (congrArg₂ (· + ·) (w8Pair_const_mul_left s F H) (w8Pair_const_mul_left t G H))

private theorem mix_mass {F G : ℝ → ℝ} (hF : IsW8Target F) (hG : IsW8Target G) (s t : ℝ) :
    w8Mass (mix s t F G) = s^2*w8Mass F + 2*s*t*w8Pair F G + t^2*w8Mass G := by
  rw [← w8Pair_self, mix_pair hF hG (mix_target hF hG s t), w8Pair_comm F, w8Pair_comm G,
    mix_pair hF hG hF, mix_pair hF hG hG, w8Pair_self, w8Pair_self, w8Pair_comm G F]
  ring

private theorem bessel_pair {F G y : ℝ → ℝ} (hF : IsW8Target F) (hG : IsW8Target G)
    (hy : IsW8Target y) (hFm : 0 < w8Mass F) (hGm : 0 < w8Mass G) (ho : w8Pair F G = 0) :
    w8Pair y F ^ 2 / w8Mass F + w8Pair y G ^ 2 / w8Mass G ≤ w8Mass y := by
  let s := -w8Pair y F / w8Mass F
  let t := -w8Pair y G / w8Mass G
  have hn := w8Mass_nonneg (mix 1 t (mix 1 s y F) G)
  rw [mix_mass (mix_target hy hF 1 s) hG, mix_mass hy hF, mix_pair hy hF hG, ho] at hn
  have he : w8Mass y - (w8Pair y F ^ 2 / w8Mass F + w8Pair y G ^ 2 / w8Mass G) =
      1^2 * (1^2*w8Mass y + 2*1*s*w8Pair y F + s^2*w8Mass F) +
      2*1*t*(1*w8Pair y G + s*0) + t^2*w8Mass G := by
    dsimp only [s,t]
    field_simp [hFm.ne',hGm.ne']
    ring
  rw [← he] at hn
  exact sub_nonneg.mp hn

private abbrev sam (F : ℝ → ℝ) (z : ℂ) := negativeHalfLineLaplace (cx F) z

private theorem null_coefficient_le_difference {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ)
    {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) {s t : ℝ} (hst : 0 ≤ s*t) :
    (s*t)*criticalAliasCoefficient R ≤ (quartetCopyMult ρ : ℝ) *
      (((s* (sam F (ρ-1/2)).re - t*(sam F (1/2-conj ρ)).re)^2 +
        (s* (sam F (ρ-1/2)).im - t*(sam F (1/2-conj ρ)).im)^2) / w8Mass F) := by
  let a := sam F (ρ-1/2)
  let b := sam F (1/2-conj ρ)
  let m := (quartetCopyMult ρ : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hmass : 0 < w8Mass F := nullVector_confinementMass_pos hF
  have hnull := hF.2.2 F hF.1
  rw [criticalHalfLineMixedEnergy_eq_bare_add, bareMixedEnergy_self_singleQuartet hq hF.1,
    w8_restrict F F hF.1, w8Pair_self] at hnull
  change onLineEnergy F + 4*m*(a*conj b).re + criticalAliasCoefficient R*w8Mass F = 0 at hnull
  have hbase : criticalAliasCoefficient R*w8Mass F ≤ -4*m*(a.re*b.re + a.im*b.im) := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add] at hnull
    linarith only [hnull,onLineEnergy_nonneg F]
  change s*t*criticalAliasCoefficient R ≤ m * (_ / w8Mass F)
  rw [← mul_div_assoc, le_div_iff₀ hmass, mul_assoc (s*t)]
  apply (mul_le_mul_of_nonneg_left hbase hst).trans
  have hsq := mul_nonneg hm (add_nonneg (sq_nonneg (s*a.re+t*b.re)) (sq_nonneg (s*a.im+t*b.im)))
  change _ ≤ m * ((s*a.re-t*b.re)^2 + (s*a.im-t*b.im)^2)
  linarith only [hsq]

/-- A single quartet of depth `δ` and multiplicity `m` pays at most
`m ((16-δ²)^(-1/2) - 1/4)` for the sum of the two confinement coefficients. -/
theorem singleQuartet_alias_sum_le_depth {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ)
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S) (hne : R ≠ S) {F G : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hG : IsConfinedNullVector S G) :
    criticalAliasCoefficient R + criticalAliasCoefficient S ≤
      (quartetCopyMult ρ : ℝ) * (1 / Real.sqrt (16-(ρ.re-1/2)^2) - 1/4) := by
  let z := ρ - 1/2
  let w := 1/2 - conj ρ
  let δ := ρ.re-1/2
  have hz : z.re = δ := by simp [z,δ]
  have hw : w.re = -δ := by simp [w,δ]
  have hi : z.im = w.im := by simp [z,w]
  have hd0 : 0 < δ := sub_pos.mpr hq.1
  have hd1 : δ < 1/2 := by dsimp only [δ]; linarith only [hq.re_lt_one]
  have hz4 : -4 < z.re := by rw [hz]; linarith only [hd0]
  have hw4 : -4 < w.re := by rw [hw]; linarith only [hd1]
  let s := Real.sqrt (8+2*δ)
  let t := Real.sqrt (8-2*δ)
  have hs0 : 0 < 8+2*δ := by linarith only [hd0]
  have ht0 : 0 < 8-2*δ := by linarith only [hd1]
  have hst : 0 < s*t := mul_pos (Real.sqrt_pos.mpr hs0) (Real.sqrt_pos.mpr ht0)
  let yc := mix s (-t) (modeCos z) (modeCos w)
  let ys := mix s (-t) (modeSin z) (modeSin w)
  have hFT := isW8Target_of_domain hF.1
  have hGT := isW8Target_of_domain hG.1
  have ho := (confinedNullVectors_orthogonal hR hS hne hF hG).1
  rw [w8_restrict F G hF.1] at ho
  have hb (y : ℝ → ℝ) (hy : IsW8Target y) := bessel_pair hFT hGT hy
    (nullVector_confinementMass_pos hF) (nullVector_confinementMass_pos hG) ho
  have hbc := hb yc (mix_target (isW8Target_modeCos hz4) (isW8Target_modeCos hw4) s (-t))
  have hbs := hb ys (mix_target (isW8Target_modeSin hz4) (isW8Target_modeSin hw4) s (-t))
  have heval (H : ℝ → ℝ) (hH : CriticalHalfLineEnergyDomain H) :
      w8Pair yc H = s*(sam H z).re - t*(sam H w).re ∧
      w8Pair ys H = s*(sam H z).im - t*(sam H w).im := by
    constructor
    · simp only [yc, mix_pair (isW8Target_modeCos hz4) (isW8Target_modeCos hw4) (isW8Target_of_domain hH),
        w8Pair_modeCos_eq_re_laplace hH hz4, w8Pair_modeCos_eq_re_laplace hH hw4, neg_mul, sub_eq_add_neg, sam]
    · simp only [ys, mix_pair (isW8Target_modeSin hz4) (isW8Target_modeSin hw4) (isW8Target_of_domain hH),
        w8Pair_modeSin_eq_im_laplace hH hz4, w8Pair_modeSin_eq_im_laplace hH hw4, neg_mul, sub_eq_add_neg, sam]
  have hzsum := w8_quartet_mode_pair hz4 hz4 rfl
  have hwsum := w8_quartet_mode_pair hw4 hw4 rfl
  have hzw := w8_quartet_mode_pair hz4 hw4 hi
  simp only [w8Pair_self,hz,hw] at hzsum hwsum hzw
  have hmass : w8Mass yc + w8Mass ys = 2 - s*t/4 := by
    dsimp only [yc,ys]
    rw [mix_mass (isW8Target_modeCos hz4) (isW8Target_modeCos hw4),
      mix_mass (isW8Target_modeSin hz4) (isW8Target_modeSin hw4)]
    calc
      _ = s^2*(w8Mass (modeCos z) + w8Mass (modeSin z)) -
          2*s*t*(w8Pair (modeCos z) (modeCos w) + w8Pair (modeSin z) (modeSin w)) +
          t^2*(w8Mass (modeCos w) + w8Mass (modeSin w)) := by ring
      _ = _ := by
        rw [hzsum,hwsum,hzw, show 8+δ+δ = 8+2*δ by ring,
          show 8 + -δ + -δ = 8-2*δ by ring, show 8 + δ + -δ = 8 by ring,
          show s^2 = 8+2*δ from Real.sq_sqrt hs0.le, show t^2 = 8-2*δ from Real.sq_sqrt ht0.le]
        field_simp [hs0.ne',ht0.ne']
        ring
  have hbound (H : ℝ → ℝ) {T : ℝ} (hH : IsConfinedNullVector T H) :
      s*t*criticalAliasCoefficient T ≤ (quartetCopyMult ρ : ℝ) *
        (w8Pair yc H ^2 / w8Mass H + w8Pair ys H ^2 / w8Mass H) := by
    rw [(heval H hH.1).1, (heval H hH.1).2, ← add_div]
    exact null_coefficient_le_difference hq hH hst.le
  have htot := add_le_add (hbound F hF) (hbound G hG)
  have hcost := mul_le_mul_of_nonneg_left (add_le_add hbc hbs) (Nat.cast_nonneg (quartetCopyMult ρ) : (0:ℝ) ≤ _)
  rw [hmass] at hcost
  have hfinal : s*t*(criticalAliasCoefficient R + criticalAliasCoefficient S) ≤
      (quartetCopyMult ρ : ℝ)*(2-s*t/4) := by linarith only [htot,hcost]
  have hprod : s*t = 2*Real.sqrt (16-δ^2) := by
    rw [show s*t = Real.sqrt ((8+2*δ)*(8-2*δ)) from (Real.sqrt_mul hs0.le _).symm,
      show (8+2*δ)*(8-2*δ) = 4*(16-δ^2) by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  rw [hprod] at hfinal hst
  have hk : Real.sqrt (16-δ^2) ≠ 0 := right_ne_zero_of_mul hst.ne'
  change _ ≤ (quartetCopyMult ρ : ℝ)*(1/Real.sqrt (16-δ^2)-1/4)
  calc
    _ ≤ ((quartetCopyMult ρ : ℝ)*(2-2*Real.sqrt (16-δ^2)/4)) / (2*Real.sqrt (16-δ^2)) :=
      (le_div_iff₀ hst).mpr (by simpa only [mul_comm (2*Real.sqrt (16-δ^2)) (_+_)] using hfinal)
    _ = _ := by field_simp

#print axioms singleQuartet_alias_sum_le_depth

end GaloisForLFunctions.ExceptionalLayerTheory
