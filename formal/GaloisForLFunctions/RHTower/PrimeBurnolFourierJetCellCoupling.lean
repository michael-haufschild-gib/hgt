import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetBalancedCubic
import GaloisForLFunctions.RHTower.GaussianEvenCarrier

/-!
# Actual two-output Fourier-jet coupling along a prime-depth tail

The literal Euler amplitude and square-position output are retained. An exact
Fourier integral and dominated convergence show that the normalized Gram coupling
tends to zero through nonzero values. Exact mixed-column Fourier and jet inner
products retain the cross terms needed for packet refinement. These supply the
source input for complete modular-cubic invertibility, without a substitute Gram.
-/

open Complex Set MeasureTheory Filter Topology
open scoped InnerProductSpace FourierTransform
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower


private def radialLaplace (m : ℕ) (l x : ℝ) : ℝ :=
  |x|^m * Real.exp (-(l*|x|))

private theorem radialLaplace_integrable {l : ℝ} (hl : 0<l) (m : ℕ) :
    Integrable (radialLaplace m l) := by
  have hc : IntegrableOn (fun x : ℝ =>
      ((x : ℂ)^m*Complex.exp (-((l : ℂ)*x))).re) (Ioi 0) :=
    (integrableOn_natPow_mul_cexp (c := (l : ℂ)) hl m).re
  have hi : IntegrableOn (radialLaplace m l) (Ioi 0) := by
    apply hc.congr_fun _ measurableSet_Ioi
    intro x hx
    simp [radialLaplace,abs_of_pos (show 0<x from hx),← Complex.ofReal_mul,
      ← Complex.ofReal_neg,← Complex.ofReal_exp,← Complex.ofReal_pow]
  have hn : IntegrableOn (radialLaplace m l) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simpa only [Function.comp_def,radialLaplace,abs_neg,neg_preimage,neg_Iic,neg_zero]
      using! (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi)
  simpa only [Iic_union_Ioi,integrableOn_univ] using hn.union hi

private theorem radialLaplace_integral {l : ℝ} (hl : 0<l) (m : ℕ) :
    (∫ x,radialLaplace m l x)=2*(m.factorial : ℝ)/l^(m+1) := by
  have hh : (∫ x in Ioi (0 : ℝ),radialLaplace m l x)=(m.factorial : ℝ)/l^(m+1) := by
    have he := congrArg Complex.re (integral_Ioi_pow_mul_cexp (c := (l : ℂ)) hl m)
    change RCLike.re (∫ x in Ioi (0 : ℝ), (x : ℂ)^m*Complex.exp (-((l : ℂ)*x))) = _ at he
    rw [← integral_re (integrableOn_natPow_mul_cexp (c := (l : ℂ)) hl m)] at he
    convert he using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp [radialLaplace,abs_of_pos (show 0<x from hx),← Complex.ofReal_mul,
        ← Complex.ofReal_neg,← Complex.ofReal_exp,← Complex.ofReal_pow]
    · norm_cast
  rw [← integral_add_compl measurableSet_Ioi (radialLaplace_integrable hl m),compl_Ioi]
  have hn : (∫ x in Iic (0 : ℝ),radialLaplace m l x)=
      ∫ x in Ioi (0 : ℝ),radialLaplace m l x := by
    rw [← neg_zero,← integral_comp_neg_Ioi]
    simp only [radialLaplace,abs_neg,neg_zero]
  rw [hn,hh]
  ring

def burnolFourierCrossKernel (s : ℝ) : ℝ := (1-s^2)/(1+s^2)^2

theorem burnolFourierCrossKernel_abs_le (s : ℝ) : |burnolFourierCrossKernel s|≤1 := by
  have hd : 0<(1+s^2)^2 := sq_pos_of_pos (by positivity)
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg s,sq_nonneg (s^2)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg s,sq_nonneg (s^2)]

def burnolFourierCrossIntegral (t : ℝ) : ℝ :=
  ∫ x,radialLaplace 1 1 x*burnolFourierCrossKernel (2*Real.pi*t*x)

theorem burnolFourierCrossIntegral_tendsto :
    Tendsto burnolFourierCrossIntegral (𝓝 0) (𝓝 2) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 (0 : ℝ))
    (F := fun t x : ℝ => radialLaplace 1 1 x*burnolFourierCrossKernel (2*Real.pi*t*x))
    (f := radialLaplace 1 1) (radialLaplace 1 1) ?_ ?_
      (radialLaplace_integrable (by norm_num) 1) ?_
  · simpa only [burnolFourierCrossIntegral,radialLaplace_integral (by norm_num : (0:ℝ)<1),
      Nat.factorial_one,Nat.cast_one,one_pow,mul_one,div_one] using! h
  · apply Eventually.of_forall
    intro t
    have hc : Continuous (fun x : ℝ =>
        radialLaplace 1 1 x*burnolFourierCrossKernel (2*Real.pi*t*x)) := by
      unfold radialLaplace burnolFourierCrossKernel
      apply Continuous.mul (by fun_prop)
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro x
      positivity
    exact hc.aestronglyMeasurable
  · filter_upwards with t
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by unfold radialLaplace; positivity)]
    exact mul_le_of_le_one_right (by unfold radialLaplace; positivity)
      (burnolFourierCrossKernel_abs_le _)
  · filter_upwards with x
    have hc : ContinuousAt (fun t : ℝ =>
        radialLaplace 1 1 x*burnolFourierCrossKernel (2*Real.pi*t*x)) 0 := by
      unfold burnolFourierCrossKernel
      fun_prop (disch := norm_num)
    simpa only [burnolFourierCrossKernel,mul_zero,zero_mul,zero_pow (by decide : 2≠0),
      sub_zero,add_zero,one_pow,div_one,mul_one] using hc.tendsto

private theorem feature_real (pe : Nat.Primes × ℕ) (x : ℝ) :
    primeBurnolEvenFeature pe x =
      primeBurnolAmplitude pe*(radialLaplace 1 (primeBurnolLogFrequency pe) x : ℝ) := by
  simp only [primeBurnolEvenFeature,primeBurnolWindowFeature,primeBurnolComplexExponent,
    Complex.ofReal_zero,mul_zero,add_zero,radialLaplace,pow_one,
    Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg]
  ring

theorem primeBurnolFourierCross_inner_pair (pe qe : Nat.Primes × ℕ) :
    ⟪primeBurnolEvenFeatureLp pe,fourierUnitary (primeBurnolEvenFeatureLp qe)⟫_ℂ =
      2*primeBurnolAmplitude pe*primeBurnolAmplitude qe/
        ((primeBurnolLogFrequency pe : ℂ)^2*(primeBurnolLogFrequency qe : ℂ)^2) *
        (burnolFourierCrossIntegral ((primeBurnolLogFrequency pe*primeBurnolLogFrequency qe)⁻¹) : ℝ) := by
  let l := primeBurnolLogFrequency pe
  let m := primeBurnolLogFrequency qe
  have hl : 0<l := primeBurnolLogFrequency_pos pe
  have hm : 0 < m := primeBurnolLogFrequency_pos qe
  have hlc : (l : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hl.ne'
  have hmc : (m : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hm.ne'
  rw [L2.inner_def]
  have he : (fun x : ℝ => ⟪primeBurnolEvenFeatureLp pe x,
      (fourierUnitary (primeBurnolEvenFeatureLp qe)) x⟫_ℂ) =ᵐ[volume]
      fun x => 2*primeBurnolAmplitude pe*primeBurnolAmplitude qe/(m : ℂ)^2 *
        ((radialLaplace 1 l x*burnolFourierCrossKernel (2*Real.pi*x/m) : ℝ) : ℂ) := by
    filter_upwards [primeBurnolEvenFeatureLp_coeFn pe,
      fourier_primeBurnolEvenFeatureLp_coeFn qe] with x hx hF
    rw [hx,hF,fourier_primeBurnolEvenFeature,feature_real,RCLike.inner_apply,
      starRingEnd_apply,star_mul,star_primeBurnolAmplitude,Complex.star_def,Complex.conj_ofReal]
    have hd : (m : ℂ)^2+(2*Real.pi*x)^2≠0 := by
      have h : m^2+(2*Real.pi*x)^2≠0 := by positivity
      exact_mod_cast h
    have hk : (1+(2*Real.pi*x/m)^2 : ℝ)≠0 := by positivity
    simp only [burnolFourierCrossKernel,Complex.ofReal_mul,Complex.ofReal_div,
      Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_pow,Complex.ofReal_one]
    dsimp only [l,m] at *
    push_cast
    field_simp [hmc,hd]
  rw [integral_congr_ae he,integral_const_mul,integral_complex_ofReal]
  have hscale : (∫ x,radialLaplace 1 l x*burnolFourierCrossKernel (2*Real.pi*x/m)) =
      l⁻¹^2*burnolFourierCrossIntegral ((l*m)⁻¹) := by
    have hc := MeasureTheory.Measure.integral_comp_mul_left
      (fun x : ℝ => radialLaplace 1 1 x*burnolFourierCrossKernel (2*Real.pi*x/(l*m))) l
    rw [abs_of_pos (inv_pos.mpr hl),smul_eq_mul] at hc
    have hf : (fun x : ℝ => radialLaplace 1 l x*burnolFourierCrossKernel (2*Real.pi*x/m)) =
        fun x => l⁻¹*(radialLaplace 1 1 (l*x)*burnolFourierCrossKernel (2*Real.pi*(l*x)/(l*m))) := by
      funext x
      have hk : 2*Real.pi*(l*x)/(l*m)=2*Real.pi*x/m := by field_simp
      rw [hk]
      simp only [radialLaplace,pow_one,one_mul,abs_mul,abs_of_pos hl]
      field_simp
    rw [hf,integral_const_mul,hc]
    have hk : (fun x : ℝ => radialLaplace 1 1 x*burnolFourierCrossKernel (2*Real.pi*x/(l*m))) =
        fun x => radialLaplace 1 1 x*burnolFourierCrossKernel (2*Real.pi*((l*m)⁻¹)*x) := by
      funext x
      congr 2
      field_simp
    rw [hk]
    unfold burnolFourierCrossIntegral
    ring
  rw [hscale]
  push_cast
  change _ = 2*primeBurnolAmplitude pe*primeBurnolAmplitude qe/((l : ℂ)^2*(m : ℂ)^2) * _
  field_simp
  rfl

theorem primeBurnolFourierCross_inner (pe : Nat.Primes × ℕ) :
    ⟪primeBurnolEvenFeatureLp pe,fourierUnitary (primeBurnolEvenFeatureLp pe)⟫_ℂ =
      2*primeBurnolAmplitude pe^2/(primeBurnolLogFrequency pe : ℂ)^4 *
        (burnolFourierCrossIntegral ((primeBurnolLogFrequency pe)^(-2 : ℤ)) : ℝ) := by
  rw [primeBurnolFourierCross_inner_pair]
  have he : (primeBurnolLogFrequency pe*primeBurnolLogFrequency pe)⁻¹=
      primeBurnolLogFrequency pe^(-2 : ℤ) := by rw [← pow_two,zpow_neg,zpow_ofNat]
  rw [he]
  congr 1
  ring


private theorem radialLaplace_mul (m n : ℕ) (l r x : ℝ) :
    radialLaplace m l x*radialLaplace n r x=radialLaplace (m+n) (l+r) x := by
  simp only [radialLaplace,pow_add,add_mul,neg_add,Real.exp_add]
  ring

private theorem inner_radial {f g : SoninL2} (pe qe : Nat.Primes × ℕ) (m n : ℕ)
    (hf : (f : ℝ → ℂ) =ᵐ[volume] fun x =>
      primeBurnolAmplitude pe*(radialLaplace m (primeBurnolLogFrequency pe) x : ℝ))
    (hg : (g : ℝ → ℂ) =ᵐ[volume] fun x =>
      primeBurnolAmplitude qe*(radialLaplace n (primeBurnolLogFrequency qe) x : ℝ)) :
    ⟪f,g⟫_ℂ=primeBurnolAmplitude pe*primeBurnolAmplitude qe *
      ((2*((m+n).factorial : ℝ)/(primeBurnolLogFrequency pe+primeBurnolLogFrequency qe)^(m+n+1) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have he : (fun x : ℝ => ⟪f x,g x⟫_ℂ) =ᵐ[volume] fun x =>
      (primeBurnolAmplitude pe*primeBurnolAmplitude qe)*
        (radialLaplace (m+n) (primeBurnolLogFrequency pe+primeBurnolLogFrequency qe) x : ℝ) := by
    filter_upwards [hf,hg] with x hx hy
    rw [hx,hy,RCLike.inner_apply,starRingEnd_apply,star_mul,star_primeBurnolAmplitude,
      Complex.star_def,Complex.conj_ofReal]
    rw [← radialLaplace_mul]
    push_cast
    ring
  rw [integral_congr_ae he,integral_const_mul,integral_complex_ofReal,
    radialLaplace_integral (add_pos (primeBurnolLogFrequency_pos pe) (primeBurnolLogFrequency_pos qe))]

theorem primeBurnolEvenFeatureLp_inner_pair (pe qe : Nat.Primes × ℕ) :
    ⟪primeBurnolEvenFeatureLp pe,primeBurnolEvenFeatureLp qe⟫_ℂ=
      4*primeBurnolAmplitude pe*primeBurnolAmplitude qe/
        (primeBurnolLogFrequency pe+primeBurnolLogFrequency qe : ℂ)^3 := by
  have hf := (primeBurnolEvenFeatureLp_coeFn pe).trans (Eventually.of_forall (feature_real pe))
  have hg := (primeBurnolEvenFeatureLp_coeFn qe).trans (Eventually.of_forall (feature_real qe))
  rw [inner_radial pe qe 1 1 hf hg]
  norm_num
  ring

private theorem squareColumn_radial (pe : Nat.Primes × ℕ) :
    (burnolSquarePosition (primeBurnolSquareColumn pe) : ℝ → ℂ) =ᵐ[volume]
      fun x => primeBurnolAmplitude pe*(radialLaplace 3 (primeBurnolLogFrequency pe) x : ℝ) := by
  filter_upwards [burnolSquarePosition_primeBurnolSquareColumn pe] with x hx
  rw [hx]
  simp only [primeBurnolRadialJet,radialLaplace,Nat.reduceAdd,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_exp,Complex.ofReal_neg]

theorem burnolSquarePosition_primeBurnolSquareColumn_inner_pair (pe qe : Nat.Primes × ℕ) :
    ⟪burnolSquarePosition (primeBurnolSquareColumn pe),burnolSquarePosition (primeBurnolSquareColumn qe)⟫_ℂ=
      1440*primeBurnolAmplitude pe*primeBurnolAmplitude qe/
        (primeBurnolLogFrequency pe+primeBurnolLogFrequency qe : ℂ)^7 := by
  rw [inner_radial pe qe 3 3 (squareColumn_radial pe) (squareColumn_radial qe)]
  norm_num
  ring

private theorem norm_sq_radial {f : SoninL2} (pe : Nat.Primes × ℕ) (m : ℕ)
    (hf : (f : ℝ → ℂ) =ᵐ[volume] fun x =>
      primeBurnolAmplitude pe*(radialLaplace m (primeBurnolLogFrequency pe) x : ℝ)) :
    ‖f‖^2=‖primeBurnolAmplitude pe‖^2 *
      (2*((2*m).factorial : ℝ)/(2*primeBurnolLogFrequency pe)^(2*m+1)) := by
  rw [norm_sq_eq_integral]
  have he : (fun x : ℝ => ‖f x‖^2) =ᵐ[volume] fun x =>
      ‖primeBurnolAmplitude pe‖^2*radialLaplace (2*m) (2*primeBurnolLogFrequency pe) x := by
    filter_upwards [hf] with x hx
    rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by unfold radialLaplace; positivity),mul_pow]
    congr 1
    unfold radialLaplace
    rw [mul_pow,← pow_mul,show m*2=2*m by omega,
      pow_two (Real.exp _),← Real.exp_add]
    congr 2
    ring
  rw [integral_congr_ae he,integral_const_mul,
    radialLaplace_integral (mul_pos (by norm_num) (primeBurnolLogFrequency_pos pe))]

theorem primeBurnolEvenFeatureLp_norm_sq (pe : Nat.Primes × ℕ) :
    ‖primeBurnolEvenFeatureLp pe‖^2 =
      ‖primeBurnolAmplitude pe‖^2/(2*primeBurnolLogFrequency pe^3) := by
  have hf := (primeBurnolEvenFeatureLp_coeFn pe).trans
    (Eventually.of_forall (feature_real pe))
  rw [norm_sq_radial pe 1 hf]
  norm_num
  ring

theorem burnolSquarePosition_primeBurnolSquareColumn_norm_sq (pe : Nat.Primes × ℕ) :
    ‖burnolSquarePosition (primeBurnolSquareColumn pe)‖^2 =
      45*‖primeBurnolAmplitude pe‖^2/(4*primeBurnolLogFrequency pe^7) := by
  have hf : (burnolSquarePosition (primeBurnolSquareColumn pe) : ℝ → ℂ) =ᵐ[volume]
      fun x => primeBurnolAmplitude pe*(radialLaplace 3 (primeBurnolLogFrequency pe) x : ℝ) := by
    filter_upwards [burnolSquarePosition_primeBurnolSquareColumn pe] with x hx
    rw [hx]
    simp only [primeBurnolRadialJet,radialLaplace,Nat.reduceAdd,Complex.ofReal_mul,
      Complex.ofReal_pow,Complex.ofReal_exp,Complex.ofReal_neg]
  rw [norm_sq_radial pe 3 hf]
  norm_num
  ring

theorem primeBurnolLogFrequency_tendsto (p : Nat.Primes) :
    Tendsto (fun n => primeBurnolLogFrequency (p,n)) atTop atTop := by
  have hp : 0<Real.log (p : ℝ) := (primeBurnolLogRate p).property
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  convert hn.atTop_mul_const hp using 1
  funext n
  simp [primeBurnolLogFrequency,primeBurnolValuation,Real.log_pow]

def burnolJetCellMass (pe : Nat.Primes × ℕ) : ℝ :=
  ‖primeBurnolEvenFeatureLp pe‖^2+‖burnolSquarePosition (primeBurnolSquareColumn pe)‖^2

def burnolJetCellCoupling (pe : Nat.Primes × ℕ) : ℝ :=
  (⟪primeBurnolEvenFeatureLp pe,fourierUnitary (primeBurnolEvenFeatureLp pe)⟫_ℂ+
    ⟪burnolSquarePosition (primeBurnolSquareColumn pe),
      fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn pe))⟫_ℂ).re

def burnolJetCellNormalizedCoupling (pe : Nat.Primes × ℕ) : ℝ :=
  burnolJetCellCoupling pe/burnolJetCellMass pe

theorem burnolJetCellMass_pos (pe : Nat.Primes × ℕ) : 0<burnolJetCellMass pe := by
  have hA : 0<‖primeBurnolAmplitude pe‖ := norm_pos_iff.mpr (primeBurnolAmplitude_ne_zero pe)
  have hl := primeBurnolLogFrequency_pos pe
  unfold burnolJetCellMass
  rw [primeBurnolEvenFeatureLp_norm_sq]
  positivity

private theorem amplitude_sq_norm (pe : Nat.Primes × ℕ) :
    primeBurnolAmplitude pe^2 = ((‖primeBurnolAmplitude pe‖^2 : ℝ) : ℂ) := by
  have h : ⟪primeBurnolAmplitude pe,primeBurnolAmplitude pe⟫_ℂ =
      (‖primeBurnolAmplitude pe‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K _
  simpa only [RCLike.inner_apply,starRingEnd_apply,star_primeBurnolAmplitude,pow_two,
    Complex.ofReal_pow, Complex.ofReal_mul] using h

private theorem normalized_first_cross (pe : Nat.Primes × ℕ) :
    primeBurnolLogFrequency pe^4/‖primeBurnolAmplitude pe‖^2 *
      (⟪primeBurnolEvenFeatureLp pe,fourierUnitary (primeBurnolEvenFeatureLp pe)⟫_ℂ).re =
      2*burnolFourierCrossIntegral (primeBurnolLogFrequency pe^(-2 : ℤ)) := by
  have hl := primeBurnolLogFrequency_pos pe
  have hA : ‖primeBurnolAmplitude pe‖≠0 := norm_ne_zero_iff.mpr (primeBurnolAmplitude_ne_zero pe)
  rw [primeBurnolFourierCross_inner,amplitude_sq_norm]
  norm_cast
  field_simp

private theorem normalized_second_cross_bound (pe : Nat.Primes × ℕ) :
    ‖primeBurnolLogFrequency pe^4/‖primeBurnolAmplitude pe‖^2 *
      (⟪burnolSquarePosition (primeBurnolSquareColumn pe),
        fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn pe))⟫_ℂ).re‖ ≤
      (45/4 : ℝ)*(primeBurnolLogFrequency pe)⁻¹^3 := by
  let f := burnolSquarePosition (primeBurnolSquareColumn pe)
  have hl := primeBurnolLogFrequency_pos pe
  have hA : ‖primeBurnolAmplitude pe‖≠0 := norm_ne_zero_iff.mpr (primeBurnolAmplitude_ne_zero pe)
  have hbound : |(⟪f,fourierUnitary f⟫_ℂ).re|≤‖f‖^2 := by
    calc
      _ ≤ ‖⟪f,fourierUnitary f⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖f‖*‖fourierUnitary f‖ := norm_inner_le_norm _ _
      _ = _ := by rw [fourierUnitary.norm_map,pow_two]
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity)]
  calc
    _ ≤ primeBurnolLogFrequency pe^4/‖primeBurnolAmplitude pe‖^2 * ‖f‖^2 :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      rw [burnolSquarePosition_primeBurnolSquareColumn_norm_sq]
      field_simp

theorem burnolJetCellCoupling_normalized_tendsto (p : Nat.Primes) :
    Tendsto (fun n => primeBurnolLogFrequency (p,n)^4/‖primeBurnolAmplitude (p,n)‖^2 *
      burnolJetCellCoupling (p,n)) atTop (𝓝 4) := by
  have hi : Tendsto (fun n => (primeBurnolLogFrequency (p,n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (primeBurnolLogFrequency_tendsto p)
  have hpow : Tendsto (fun n => primeBurnolLogFrequency (p,n)^(-2 : ℤ)) atTop (𝓝 0) := by
    simpa only [zpow_neg,zpow_ofNat,inv_pow,zero_pow (by decide : 2≠0)] using hi.pow 2
  have hfirst : Tendsto (fun n => primeBurnolLogFrequency (p,n)^4/‖primeBurnolAmplitude (p,n)‖^2 *
      (⟪primeBurnolEvenFeatureLp (p,n),fourierUnitary (primeBurnolEvenFeatureLp (p,n))⟫_ℂ).re)
        atTop (𝓝 4) := by
    simp_rw [normalized_first_cross]
    convert (burnolFourierCrossIntegral_tendsto.comp hpow).const_mul 2 using 1 <;> norm_num
  have hsecond : Tendsto (fun n => primeBurnolLogFrequency (p,n)^4/‖primeBurnolAmplitude (p,n)‖^2 *
      (⟪burnolSquarePosition (primeBurnolSquareColumn (p,n)),
        fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn (p,n)))⟫_ℂ).re)
        atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => normalized_second_cross_bound (p,n))
    simpa using (hi.pow 3).const_mul (45/4 : ℝ)
  simpa only [burnolJetCellCoupling,Complex.add_re,mul_add,add_zero] using hfirst.add hsecond

private theorem normalized_mass (pe : Nat.Primes × ℕ) :
    primeBurnolLogFrequency pe^3/‖primeBurnolAmplitude pe‖^2 * burnolJetCellMass pe =
      (1/2 : ℝ)+(45/4 : ℝ)*(primeBurnolLogFrequency pe)⁻¹^4 := by
  have hl := primeBurnolLogFrequency_pos pe
  have hA : ‖primeBurnolAmplitude pe‖≠0 := norm_ne_zero_iff.mpr (primeBurnolAmplitude_ne_zero pe)
  rw [burnolJetCellMass,primeBurnolEvenFeatureLp_norm_sq,
    burnolSquarePosition_primeBurnolSquareColumn_norm_sq]
  field_simp

theorem burnolJetCellMass_normalized_tendsto (p : Nat.Primes) :
    Tendsto (fun n => primeBurnolLogFrequency (p,n)^3/‖primeBurnolAmplitude (p,n)‖^2 *
      burnolJetCellMass (p,n)) atTop (𝓝 (1/2)) := by
  simp_rw [normalized_mass]
  have hi := tendsto_inv_atTop_zero.comp (primeBurnolLogFrequency_tendsto p)
  convert ((hi.pow 4).const_mul (45/4 : ℝ)).const_add (1/2) using 1 <;> norm_num

theorem burnolJetCellNormalizedCoupling_scaled_tendsto (p : Nat.Primes) :
    Tendsto (fun n => primeBurnolLogFrequency (p,n)*burnolJetCellNormalizedCoupling (p,n))
      atTop (𝓝 8) := by
  have h := (burnolJetCellCoupling_normalized_tendsto p).div
    (burnolJetCellMass_normalized_tendsto p) (by norm_num : (1/2 : ℝ)≠0)
  have he (n : ℕ) :
      primeBurnolLogFrequency (p,n)*burnolJetCellNormalizedCoupling (p,n) =
      (primeBurnolLogFrequency (p,n)^4/‖primeBurnolAmplitude (p,n)‖^2 * burnolJetCellCoupling (p,n)) /
      (primeBurnolLogFrequency (p,n)^3/‖primeBurnolAmplitude (p,n)‖^2 * burnolJetCellMass (p,n)) := by
    have hl := primeBurnolLogFrequency_pos (p,n)
    have hA : ‖primeBurnolAmplitude (p,n)‖≠0 :=
      norm_ne_zero_iff.mpr (primeBurnolAmplitude_ne_zero (p,n))
    have hm := burnolJetCellMass_pos (p,n)
    unfold burnolJetCellNormalizedCoupling
    field_simp
  simp_rw [he]
  simpa only [Pi.div_apply,show (4/(1/2 : ℝ))=8 by norm_num] using! h

theorem burnolJetCellNormalizedCoupling_tendsto (p : Nat.Primes) :
    Tendsto (fun n => burnolJetCellNormalizedCoupling (p,n)) atTop (𝓝 0) := by
  have h := (burnolJetCellNormalizedCoupling_scaled_tendsto p).mul
    (tendsto_inv_atTop_zero.comp (primeBurnolLogFrequency_tendsto p))
  have he (n : ℕ) :
      primeBurnolLogFrequency (p,n)*burnolJetCellNormalizedCoupling (p,n)*
        (primeBurnolLogFrequency (p,n))⁻¹=burnolJetCellNormalizedCoupling (p,n) := by
    have hl := primeBurnolLogFrequency_pos (p,n)
    field_simp
  simpa only [Function.comp_apply,he,mul_zero] using! h

theorem burnolJetCellNormalizedCoupling_eventually_ne_zero (p : Nat.Primes) :
    ∀ᶠ n in atTop, burnolJetCellNormalizedCoupling (p,n)≠0 := by
  filter_upwards [(burnolJetCellNormalizedCoupling_scaled_tendsto p).eventually_ne
    (by norm_num : (8 : ℝ)≠0)] with n hn
  intro he
  exact hn (by rw [he,mul_zero])

theorem burnolSquarePosition_normalized_fourier_cross_bound (pe qe : Nat.Primes × ℕ) :
    ‖⟪burnolSquarePosition (primeBurnolSquareColumn pe),
        fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn qe))⟫_ℂ /
      (primeBurnolAmplitude pe*primeBurnolAmplitude qe)‖ ≤
      45/(8*primeBurnolLogFrequency pe^7)+45/(8*primeBurnolLogFrequency qe^7) := by
  let f := burnolSquarePosition (primeBurnolSquareColumn pe)
  let g := burnolSquarePosition (primeBurnolSquareColumn qe)
  have hA : ‖primeBurnolAmplitude pe‖≠0 := norm_ne_zero_iff.mpr (primeBurnolAmplitude_ne_zero pe)
  have hB : ‖primeBurnolAmplitude qe‖≠0 := norm_ne_zero_iff.mpr (primeBurnolAmplitude_ne_zero qe)
  have hl := primeBurnolLogFrequency_pos pe
  have hm := primeBurnolLogFrequency_pos qe
  have hinner : ‖⟪f,fourierUnitary g⟫_ℂ‖≤‖f‖*‖fourierUnitary g‖ :=
    norm_inner_le_norm f (fourierUnitary g)
  rw [fourierUnitary.norm_map] at hinner
  calc
    _ = ‖⟪f,fourierUnitary g⟫_ℂ‖/(‖primeBurnolAmplitude pe‖*‖primeBurnolAmplitude qe‖) := by
      rw [norm_div,norm_mul]
    _ ≤ (‖f‖*‖g‖)/(‖primeBurnolAmplitude pe‖*‖primeBurnolAmplitude qe‖) :=
      div_le_div_of_nonneg_right hinner (by positivity)
    _ = (‖f‖/‖primeBurnolAmplitude pe‖)*(‖g‖/‖primeBurnolAmplitude qe‖) := by field_simp
    _ ≤ ((‖f‖/‖primeBurnolAmplitude pe‖)^2+(‖g‖/‖primeBurnolAmplitude qe‖)^2)/2 := by
      nlinarith [sq_nonneg (‖f‖/‖primeBurnolAmplitude pe‖-‖g‖/‖primeBurnolAmplitude qe‖)]
    _ = _ := by
      simp only [div_pow,f,g,burnolSquarePosition_primeBurnolSquareColumn_norm_sq]
      field_simp
      ring

end RHTower
