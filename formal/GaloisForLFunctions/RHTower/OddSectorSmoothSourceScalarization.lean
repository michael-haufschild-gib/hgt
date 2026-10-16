import GaloisForLFunctions.RHTower.EvenSectorSmoothSourceScalarization
import GaloisForLFunctions.HTGeometry.CompactPrimitive

/-!
# Exact scalarization of smooth odd mixtures

A positive finite mixture of smooth compact odd autocorrelations is one smooth
compact odd autocorrelation. The entire lag profile is preserved, so arithmetic
blindness and every linear Weil pairing survive without a correction term.

Take compact even primitives, factor their Hermitian mixture using positivity
on both axes, recover a compact even source, and differentiate it. No positivity
of the Weil functional or hypothesis on zeta zeros enters the construction.
-/

open Complex Filter Topology Set MeasureTheory Zeta23
open scoped ComplexConjugate NNReal ContDiff FourierTransform
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.EvenHermitianFactor

noncomputable section
namespace RHTower.OddSector
open WeilOneSided EvenSector

private theorem compact_even_primitive {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (ho : Function.Odd f) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ Function.Even g ∧ deriv g = f := by
  have hodd (x : ℝ) : f (-x) = -f x := ho x
  obtain ⟨B,hB⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  let R := |B|+1
  have hs : ∀ x ∉ Ioo (-R) R, f x=0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hb := hB hm
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hb
    apply hx
    dsimp [R]
    constructor <;> linarith [le_abs_self B,(abs_le.mp hb).1,(abs_le.mp hb).2]
  have hz : (∫ x in -R..R, f x)=0 := by
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R) f
    simp_rw [hodd,intervalIntegral.integral_neg,neg_neg] at h
    linear_combination -h / 2
  let g : ℝ → ℂ := fun x => ∫ t in -R..x, f t
  have hd (x : ℝ) : HasDerivAt g (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable _ _)
      (hf.continuous.stronglyMeasurableAtFilter _ _) hf.continuous.continuousAt
  refine ⟨g,contDiff_primitive hf _,?_,?_,funext fun x => (hd x).deriv⟩
  · apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
    intro x hx
    exact primitive_eq_zero_outside hf.continuous hs hz x
      (fun h => hx ⟨h.1.le,h.2.le⟩)
  · intro x
    have hn := intervalIntegral.integral_comp_neg (a := R) (b := x) f
    simp_rw [hodd,intervalIntegral.integral_neg] at hn
    have hr := intervalIntegral.integral_symm (f := f) (μ := volume) (a := -x) (b := -R)
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (hf.continuous.intervalIntegrable (-R) R) (hf.continuous.intervalIntegrable R x)
    rw [hz,zero_add] at ha
    dsimp [g]
    linear_combination hn + hr + ha

private def evenSpectrum {N : ℕ} (g : Fin N → ℝ → ℂ) (a : Fin N → ℝ≥0) (z : ℂ) : ℂ :=
  ∑ i, (a i : ℂ)*paperFT (g i) z*conj (paperFT (g i) (conj z))

private theorem evenSpectrum_axis {N : ℕ} (g : Fin N → ℝ → ℂ) (a : Fin N → ℝ≥0)
    (he : ∀ i, Function.Even (g i)) (z : ℂ) (hz : z.re=0 ∨ z.im=0) :
    evenSpectrum g a z=((∑ i, (a i : ℝ)*‖paperFT (g i) z‖^2 : ℝ) : ℂ) := by
  unfold evenSpectrum
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  have hc : paperFT (g i) (conj z)=paperFT (g i) z := by
    rcases hz with hz | hz
    · rw [show conj z=-z by apply Complex.ext <;> simp [hz],paperFT_neg_of_even (he i)]
    · rw [show conj z=z by apply Complex.ext <;> simp [hz]]
  rw [hc,mul_assoc,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_pow]

private theorem compact_transform_exponential {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∃ M A : ℝ, 0≤M ∧ 0≤A ∧ ∀ z, ‖paperFT g z‖≤M*Real.exp (A*‖z‖) := by
  obtain ⟨R,hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨∫ u, ‖g u‖,|R|,integral_nonneg (fun _ => norm_nonneg _),abs_nonneg _,fun z => ?_⟩
  have hs (u : ℝ) (hu : |R| < |u|) : g u=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh := hR hm
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
    linarith [le_abs_self R]
  simpa only [testTransform,Zeta23.paperFT,mul_comm] using
    norm_testTransform_le_exp hg hgc (abs_nonneg R) hs z (Complex.abs_im_le_norm z)

private theorem evenSpectrum_exponential {N : ℕ} (g : Fin N → ℝ → ℂ) (a : Fin N → ℝ≥0)
    (hg : ∀ i, Continuous (g i)) (hgc : ∀ i, HasCompactSupport (g i)) :
    ∃ M A : ℝ, 0≤M ∧ 0≤A ∧ ∀ z, ‖evenSpectrum g a z‖≤M*Real.exp (A*‖z‖) := by
  classical
  choose M A hM hA hb using fun i => compact_transform_exponential (hg i) (hgc i)
  let B := ∑ i, 2*A i
  let D := ∑ i, (a i : ℝ)*(M i)^2
  refine ⟨D,B,Finset.sum_nonneg (fun i _ => mul_nonneg (a i).coe_nonneg (sq_nonneg _)),
    Finset.sum_nonneg (fun i _ => mul_nonneg (by norm_num) (hA i)),fun z => ?_⟩
  apply (norm_sum_le _ _).trans
  rw [show D*Real.exp (B*‖z‖)=∑ i, ((a i : ℝ)*(M i)^2)*Real.exp (B*‖z‖) by
    rw [Finset.sum_mul]]
  apply Finset.sum_le_sum
  intro i hi
  have hAB : 2*A i≤B := Finset.single_le_sum
    (fun i _ => mul_nonneg (by norm_num) (hA i)) hi
  have hp : ‖paperFT (g i) z‖*‖paperFT (g i) (conj z)‖≤
      (M i)^2*Real.exp ((2*A i)*‖z‖) := by
    calc
      _ ≤ (M i*Real.exp (A i*‖z‖))*(M i*Real.exp (A i*‖conj z‖)) :=
        mul_le_mul (hb i z) (hb i (conj z)) (norm_nonneg _)
          (mul_nonneg (hM i) (Real.exp_nonneg _))
      _ = _ := by
        rw [Complex.norm_conj,show (2*A i)*‖z‖=A i*‖z‖+A i*‖z‖ by ring,Real.exp_add]
        ring
  rw [norm_mul,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (a i).coe_nonneg,mul_assoc]
  exact (mul_le_mul_of_nonneg_left hp (a i).coe_nonneg).trans (by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAB (norm_nonneg z)))
      (mul_nonneg (a i).coe_nonneg (sq_nonneg _)))

private theorem orderOne_exponential {H : ℂ → ℂ} {M A : ℝ}
    (hM : 0≤M) (hA : 0≤A) (hb : ∀ z, ‖H z‖≤M*Real.exp (A*‖z‖)) :
    ∃ C : ℝ, 0≤C ∧ ∀ z, ‖H z‖≤Real.exp (C*(1+‖z‖)*Real.log (2+‖z‖)) := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(M+A)/Real.log 2,by positivity,fun z => ?_⟩
  have hl : Real.log 2≤Real.log (2+‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  apply (hb z).trans
  calc
    M*Real.exp (A*‖z‖) ≤ Real.exp M*Real.exp (A*‖z‖) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp M]) (Real.exp_nonneg _)
    _ = Real.exp (M+A*‖z‖) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hl (div_nonneg (add_nonneg hM hA) hl2.le)
      rw [div_mul_cancel₀ _ hl2.ne'] at hh
      have hx := mul_le_mul_of_nonneg_left hh (show 0≤1+‖z‖ by positivity)
      nlinarith [mul_nonneg hM (norm_nonneg z)]

private theorem scalarize_even {N : ℕ} (g : Fin N → ℝ → ℂ) (a : Fin N → ℝ≥0)
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hgc : ∀ i, HasCompactSupport (g i))
    (he : ∀ i, Function.Even (g i)) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ Function.Even G ∧
      ∀ z, evenSpectrum g a z=paperFT G z*conj (paperFT G (conj z)) := by
  have hH : Differentiable ℂ (evenSpectrum g a) := by
    apply Differentiable.fun_sum
    intro i _
    have h := differentiable_testTransform (hg i).continuous (hgc i)
    exact ((differentiable_const _).mul h).mul (RHTower.differentiable_conj_reflect h)
  have hHe : Function.Even (evenSpectrum g a) := by
    intro z
    apply Finset.sum_congr rfl
    intro i _
    rw [map_neg,paperFT_neg_of_even (he i),paperFT_neg_of_even (he i)]
  have hHa : AxisNonnegative (evenSpectrum g a) := by
    intro z hz
    rw [evenSpectrum_axis g a he z hz]
    refine ⟨rfl,?_⟩
    simp only [Complex.ofReal_re]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (a i).coe_nonneg (sq_nonneg _))
  obtain ⟨M,A,hM,hA,hb⟩ := evenSpectrum_exponential g a (fun i => (hg i).continuous) hgc
  obtain ⟨C,hC,horder⟩ := orderOne_exponential hM hA hb
  obtain ⟨q,hq,hqe,hi,hqs⟩ := exists_even_entire_factor_subquadratic hC hH hHe hHa horder
  have hnorm (z : ℂ) (hz : z.re=0 ∨ z.im=0) :
      ‖q z‖^2=∑ i, (a i : ℝ)*‖paperFT (g i) z‖^2 := by
    have hc : q (conj z)=q z := by
      rcases hz with hz | hz
      · rw [show conj z=-z by apply Complex.ext <;> simp [hz],hqe]
      · rw [show conj z=z by apply Complex.ext <;> simp [hz]]
    have hh := hi z
    rw [evenSpectrum_axis g a he z hz,hc,Complex.mul_conj,Complex.normSq_eq_norm_sq] at hh
    exact_mod_cast hh.symm
  have hdec (n : ℕ) : ∃ D : ℝ, ∀ x : ℝ, ‖q x‖*(1+|x|)^n≤D := by
    choose K hK hKb using fun i => exists_testTransform_decay_order (hg i) (hgc i) 0 0 n
    let D := ∑ i, (a i : ℝ)*(K i)^2
    refine ⟨D+1,fun x => ?_⟩
    have hsq : (‖q x‖*(1+|x|)^n)^2≤D := by
      rw [mul_pow,hnorm (x : ℂ) (Or.inr (by simp))]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have hd := hKb i (x : ℂ) (by simp)
      rw [le_div_iff₀ (by positivity)] at hd
      simp only [testTransform,Complex.norm_real,Real.norm_eq_abs] at hd
      calc
        _ = (a i : ℝ)*(‖paperFT (g i) x‖*(1+|x|)^n)^2 := by ring
        _ ≤ (a i : ℝ)*(K i)^2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hd 2) (a i).coe_nonneg
    nlinarith [sq_nonneg (‖q x‖*(1+|x|)^n-1/2)]
  have him (y : ℝ) (hy : 0≤y) : ‖q ((y : ℂ)*I)‖≤(M+1)*Real.exp (A*y) := by
    have hc : conj ((y : ℂ)*I)=-((y : ℂ)*I) := by simp
    have hh := hb ((y : ℂ)*I)
    rw [hi,hc,hqe,norm_mul,Complex.norm_conj,norm_mul,Complex.norm_I,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hy] at hh
    have he1 : 1≤Real.exp (A*y) := Real.one_le_exp (mul_nonneg hA hy)
    have hh' : ‖q ((y : ℂ)*I)‖≤M*Real.exp (A*y)+1 := by
      nlinarith [sq_nonneg (‖q ((y : ℂ)*I)‖-1/2)]
    nlinarith
  obtain ⟨G,hG,hGc,hGe,hGt⟩ := exists_smooth_compact_source hq hqe hqs hdec
    (show 0≤M+1 by linarith) hA him
  exact ⟨G,hG,hGc,hGe,fun z => by rw [hGt,hGt]; exact hi z⟩

/-- Smooth compact odd tests, with the same underlying test type as odd Farkas. -/
def SmoothOddTestFn : Type := {f : WeilOddTestFn // ContDiff ℝ ∞ f.1.1}

/-- The whole lag profile of a finite positive odd mixture. -/
def oddMixtureProfile {N : ℕ} (F : Fin N → SmoothOddTestFn) (a : Fin N → ℝ≥0) (u : ℝ) : ℂ :=
  ∑ i, (a i : ℂ)*EF.weilTest (F i).1.1.1 (F i).1.1.1 u

/-- One actual smooth compact odd source realizes the entire mixture spectrum. -/
theorem exists_smoothOdd_spectral_scalarization {N : ℕ}
    (F : Fin N → SmoothOddTestFn) (a : Fin N → ℝ≥0) :
    ∃ f : SmoothOddTestFn, ∀ z : ℂ,
      (∑ i, (a i : ℂ)*paperFT (F i).1.1.1 z*conj (paperFT (F i).1.1.1 (conj z)))=
        paperFT f.1.1.1 z*conj (paperFT f.1.1.1 (conj z)) := by
  choose g hg hgc he hgd using fun i =>
    compact_even_primitive (F i).2 (F i).1.1.2.2 (F i).1.2
  obtain ⟨G,hG,hGc,hGe,hGi⟩ := scalarize_even g a hg hgc he
  have hD : ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.mp hG).2
  have hDo : Function.Odd (deriv G) := by
    intro x
    have h := congrArg (fun h : ℝ → ℂ => deriv h x) (funext hGe)
    rw [deriv_comp_neg] at h
    linear_combination -h
  let f : SmoothOddTestFn :=
    ⟨⟨⟨deriv G,hD.of_le (by exact_mod_cast (show (2 : ℕ∞)≤⊤ from le_top)),hGc.deriv⟩,hDo⟩,hD⟩
  have hp (i : Fin N) (z : ℂ) :
      paperFT (F i).1.1.1 z=-(I*z)*paperFT (g i) z := by
    rw [← hgd i]
    exact paperFT_deriv_of_compact ((hg i).of_le (by
      exact_mod_cast (show (1 : ℕ∞)≤⊤ from le_top))) (hgc i) z
  have hGp (z : ℂ) : paperFT f.1.1.1 z=-(I*z)*paperFT G z :=
    paperFT_deriv_of_compact (hG.of_le (by
      exact_mod_cast (show (1 : ℕ∞)≤⊤ from le_top))) hGc z
  refine ⟨f,fun z => ?_⟩
  calc
    _ = z^2*evenSpectrum g a z := by
      unfold evenSpectrum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hp,hp]
      simp only [map_mul,map_neg,Complex.conj_I,Complex.conj_conj]
      ring_nf
      rw [Complex.I_sq]
      ring
    _ = paperFT f.1.1.1 z*conj (paperFT f.1.1.1 (conj z)) := by
      rw [hGi,hGp,hGp]
      simp only [map_mul,map_neg,Complex.conj_I,Complex.conj_conj]
      ring_nf
      rw [Complex.I_sq]
      ring

private theorem oddMixtureProfile_contDiff {N : ℕ}
    (F : Fin N → SmoothOddTestFn) (a : Fin N → ℝ≥0) :
    ContDiff ℝ 2 (oddMixtureProfile F a) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul
    (EF.weilTest_contDiff (F i).1.1.2.1 (F i).1.1.2.1.continuous (F i).1.1.2.2)

private theorem oddMixtureProfile_compact {N : ℕ}
    (F : Fin N → SmoothOddTestFn) (a : Fin N → ℝ≥0) :
    HasCompactSupport (oddMixtureProfile F a) := by
  classical
  exact HasCompactSupport.finset_sum fun i _ =>
    (EF.weilTest_hasCompactSupport (F i).1.1.2.2 (F i).1.1.2.2).mul_left

private theorem oddMixtureProfile_transform {N : ℕ}
    (F : Fin N → SmoothOddTestFn) (a : Fin N → ℝ≥0) (z : ℂ) :
    paperFT (oddMixtureProfile F a) z=
      ∑ i, (a i : ℂ)*paperFT (F i).1.1.1 z*conj (paperFT (F i).1.1.1 (conj z)) := by
  classical
  unfold paperFT oddMixtureProfile
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    simp_rw [mul_assoc]
    rw [Zeta23.integral_const_mul_C]
    simp_rw [← mul_assoc I z]
    change (a i : ℂ)*paperFT (EF.weilTest (F i).1.1.1 (F i).1.1.1) z=_
    rw [EF.paperFT_weilTest (F i).1.1.2.1.continuous (F i).1.1.2.1.continuous
      (F i).1.1.2.2 (F i).1.1.2.2]
    ring
  · intro i _
    have hc := (EF.weilTest_contDiff (F i).1.1.2.1 (F i).1.1.2.1.continuous
      (F i).1.1.2.2).continuous
    have hs := EF.weilTest_hasCompactSupport (F i).1.1.2.2 (F i).1.1.2.2
    have hh := (integrable_mul_cexp_of_hasCompactSupport hc hs (I*z)).const_mul (a i : ℂ)
    convert hh using 1
    funext u
    ring

private theorem eq_of_compact_paperFT_eq {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (he : ∀ z, paperFT f z=paperFT g z) : f=g := by
  have hfi := hf.continuous.integrable_of_hasCompactSupport hfc
  have hgi := hg.continuous.integrable_of_hasCompactSupport hgc
  have hF : 𝓕 f=𝓕 g := by
    funext x
    rw [Zeta23.fourier_eq_paperFT,Zeta23.fourier_eq_paperFT,he]
  calc
    f = 𝓕⁻ (𝓕 f) :=
      (hf.continuous.fourierInv_fourier_eq hfi (EF.integrable_fourier_of_contDiff_two hf hfc)).symm
    _ = 𝓕⁻ (𝓕 g) := by rw [hF]
    _ = g := hg.continuous.fourierInv_fourier_eq hgi (EF.integrable_fourier_of_contDiff_two hg hgc)

/-- **Exact odd source scalarization.** Every finite positive mixture of smooth
compact odd autocorrelations is one smooth compact odd autocorrelation, with
equality at every real lag. -/
theorem exists_smoothOdd_exact_autocorrelation {N : ℕ}
    (F : Fin N → SmoothOddTestFn) (a : Fin N → ℝ≥0) :
    ∃ f : SmoothOddTestFn, EF.weilTest f.1.1.1 f.1.1.1=oddMixtureProfile F a := by
  obtain ⟨f,hf⟩ := exists_smoothOdd_spectral_scalarization F a
  refine ⟨f,eq_of_compact_paperFT_eq
    (EF.weilTest_contDiff f.1.1.2.1 f.1.1.2.1.continuous f.1.1.2.2)
    (oddMixtureProfile_contDiff F a) (EF.weilTest_hasCompactSupport f.1.1.2.2 f.1.1.2.2)
    (oddMixtureProfile_compact F a) (fun z => ?_)⟩
  rw [EF.paperFT_weilTest f.1.1.2.1.continuous f.1.1.2.1.continuous
    f.1.1.2.2 f.1.1.2.2,oddMixtureProfile_transform,hf]

end RHTower.OddSector
