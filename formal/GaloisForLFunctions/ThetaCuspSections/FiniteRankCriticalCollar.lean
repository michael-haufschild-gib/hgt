import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSignedJetCompleteness
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmExteriorGaussianHankel
import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit
import GaloisForLFunctions.HTGeometry.MomentInnerProduct

/-!
# Finite-rank critical collars

At aperture one half the Xi logarithmic derivative gives a strictly positive
Fourier current. Its moments represent the actual signed theta jets. Uniform
exponential decay makes each moment continuous in the aperture, so every
finite rank stays strict on a neighborhood reaching into the critical strip.
-/

noncomputable section
open Complex MeasureTheory Matrix Filter Topology Set RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ThetaCuspSections.CriticalCollar

/-- The Xi current without a proof-dependent aperture parameter. -/
def current (a b : ℝ) : ℝ :=
  2*((starRingEnd ℂ) (XiC ((b:ℂ)-(a:ℂ)*I)) *
    (-I*deriv XiC ((b:ℂ)-(a:ℂ)*I))).re

private theorem current_eq (a : ℝ) (ha : |a|<1) (b : ℝ) :
    current a b=thetaCuspCenterMixedFourierCurrent a ha b := by
  symm
  rw [thetaCuspCenterMixedFourierCurrent,
    fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm,
    Complex.ofReal_re,thetaXiHankelOrbit_kreinForm_eq]
  rfl

private theorem derivative_continuous : Continuous (deriv XiC) := by
  have h : AnalyticOnNhd ℂ XiC Set.univ := fun z _ => XiC_differentiable.analyticAt z
  exact (h.deriv.continuousOn).comp_continuous continuous_id (fun _ => Set.mem_univ _)

/-- The Fourier current is continuous in frequency. -/
theorem current_continuous (a : ℝ) : Continuous (current a) := by
  have hz : Continuous (fun b : ℝ => (b:ℂ)-(a:ℂ)*I) := by fun_prop
  have h₀ := XiC_differentiable.continuous.comp hz
  have h₁ := derivative_continuous.comp hz
  exact continuous_const.mul (Complex.continuous_re.comp
    (h₀.star.mul (continuous_const.mul h₁)))

private theorem current_aperture_continuous (b : ℝ) : Continuous (fun a => current a b) := by
  have hz : Continuous (fun a : ℝ => (b:ℂ)-(a:ℂ)*I) := by fun_prop
  have h₀ := XiC_differentiable.continuous.comp hz
  have h₁ := derivative_continuous.comp hz
  exact continuous_const.mul (Complex.continuous_re.comp
    (h₀.star.mul (continuous_const.mul h₁)))

/-- The strip-edge Xi logarithmic derivative gives a strictly positive boundary current. -/
theorem current_boundary_pos (b : ℝ) : 0<current (1/2) b := by
  let z : ℂ := (b:ℂ)-((1/2:ℝ):ℂ)*I
  have hline : 1 ≤ (1/2+z*I).re := by
    norm_num [z,Complex.mul_re,Complex.mul_im]
  have hXi : XiC z ≠ 0 := by
    rw [XiC]
    exact xi_ne_zero_of_one_le_re hline
  have hlog : 0<(logDeriv XiC z).im := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
    simpa using re_logDeriv_xi_pos_of_one_le_re hline
  change 0<2*((starRingEnd ℂ) (XiC z)*(-I*deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im _ _ hXi,← logDeriv_apply]
  exact mul_pos (mul_pos (by norm_num) (Complex.normSq_pos.mpr hXi)) hlog

/-- Raw Fourier moments of the Xi current. -/
def rawMoment (a : ℝ) (n : ℕ) : ℝ := ∫ b : ℝ, b^n*current a b

private theorem rawMoment_eq_signedJet (a : ℝ) (ha : |a|<1) (n : ℕ) :
    rawMoment a n=(2*Real.pi)*(1/2:ℝ)^n*thetaCuspCenterMixedSignedJet a n := by
  have he : current a=thetaCuspCenterMixedFourierCurrent a ha := funext (current_eq a ha)
  change weightedMoment volume (current a) n = _
  rw [he]
  exact thetaCuspCenterMixed_rawMoment_eq_signedJet a ha n

/-- Exponential strip decay makes every raw moment absolutely integrable. -/
theorem raw_integrable (a : ℝ) (ha : |a|<1) (n : ℕ) :
    Integrable (fun b : ℝ => b^n*current a b) := by
  have he : current a=thetaCuspCenterMixedFourierCurrent a ha := funext (current_eq a ha)
  rw [he]
  exact integrable_rawMoment_thetaCuspCenterMixedFourierCurrent a ha n

private theorem raw_boundary_strict : _root_.HTGeometry.PositiveMomentForm (rawMoment (1/2)) := by
  refine ⟨fun p hp => ?_⟩
  have hint := raw_integrable (1/2) (by norm_num)
  change 0<_root_.HTGeometry.momentInner (weightedMoment volume (current (1/2))) p p
  rw [_root_.HTGeometry.momentInner_self,momentFunctional_rawMoment_eq_integral hint]
  simp only [Polynomial.eval_pow]
  have hi : Integrable (fun b : ℝ => p.eval b^2*current (1/2) b) := by
    have hi := integrable_polynomial_mul_of_rawMoments hint (p^2)
    convert hi using 1
    funext b
    rw [Polynomial.eval_pow]
  have hc : Continuous (fun b : ℝ => p.eval b^2*current (1/2) b) :=
    (p.continuous.pow 2).mul (current_continuous _)
  have hnn : (0:ℝ→ℝ)≤fun b => p.eval b^2*current (1/2) b :=
    fun b => mul_nonneg (sq_nonneg _) (current_boundary_pos b).le
  obtain ⟨b,hb⟩ : ∃ b : ℝ, p.eval b ≠ 0 := by
    by_contra h
    push Not at h
    have hs : (Set.univ : Set ℝ) ⊆ {b | p.IsRoot b} := fun b _ => h b
    exact hp (Polynomial.eq_zero_of_infinite_isRoot p (Set.infinite_univ.mono hs))
  rw [integral_pos_iff_support_of_nonneg hnn hi]
  exact hc.isOpen_support.measure_pos volume
    ⟨b,(mul_pos (sq_pos_of_ne_zero hb) (current_boundary_pos b)).ne'⟩

/-- The Hankel matrix of raw Xi-current moments. -/
def rawHankel (a : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => rawMoment a (i.val+j.val)

private theorem raw_boundary_posDef (N : ℕ) : (rawHankel (1/2) N).PosDef :=
  _root_.HTGeometry.positiveMomentForm_iff_momentHankelMatrix_posDef.mp raw_boundary_strict N

/-- The moment index depends only on the sum of row and column. -/
theorem raw_hermitian (a : ℝ) (N : ℕ) : (rawHankel a N).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [rawHankel,add_comm]

/-- A common exponential majorant gives continuity of each raw moment through the strip edge. -/
private theorem rawMoment_continuousAt_half (n : ℕ) :
    ContinuousAt (fun a => rawMoment a n) (1/2:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_abs_thetaCuspCenterMixedFourierCurrent_le_exp
    (A:=3/4) (δ:=Real.pi/8) (by norm_num) (by positivity) (by linarith only [Real.pi_pos])
  let ε : ℝ := 2*(Real.pi/8)
  let bound : ℝ→ℝ := fun b => C*(|b|^n*Real.exp (-(ε*|b|)))
  have hε : 0<ε := by dsimp only [ε]; positivity
  have hbase : Integrable (fun b : ℝ => b^n*Real.exp (-(ε*|b|))) :=
    integrable_rawMoment_of_expDecay (by fun_prop) (C:=1) (by norm_num) hε
      (fun b => by simp only [abs_of_pos (Real.exp_pos _),one_mul]; exact le_rfl) n
  have hbi : Integrable bound := by
    simpa only [bound,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using
      hbase.norm.const_mul C
  have hnear : ∀ᶠ a : ℝ in 𝓝 (1/2), |a|<3/4 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun a b : ℝ => b^n*current a b) (bound:=bound)
  · exact Filter.Eventually.of_forall fun a =>
      ((continuous_pow n).mul (current_continuous a)).aestronglyMeasurable
  · filter_upwards [hnear] with a ha
    have ha1 : |a|<1 := ha.trans (by norm_num)
    exact Filter.Eventually.of_forall fun b => by
      have hb := hbound a ha1 ha.le b
      rw [← current_eq a ha1 b] at hb
      have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg b) n)
      simpa only [bound,ε,Real.norm_eq_abs,abs_mul,abs_pow,mul_assoc,mul_left_comm C] using hm
  · exact hbi
  · exact Filter.Eventually.of_forall fun b =>
      (continuous_const.mul (current_aperture_continuous b)).continuousAt

private theorem raw_posDef_near_half (N : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ a : ℝ, |a-1/2|<δ → (rawHankel a N).PosDef := by
  have ht (i j : Fin N) : Tendsto (fun a => rawHankel a N i j)
      (𝓝 (1/2)) (𝓝 (rawHankel (1/2) N i j)) :=
    (rawMoment_continuousAt_half (i.val+j.val)).tendsto
  have hp := posDef_eventually_of_tendsto (raw_boundary_posDef N)
    (Filter.Eventually.of_forall fun a => raw_hermitian a N) ht
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨δ,hδ,fun a ha => hb (by simpa only [Real.dist_eq] using ha)⟩

/-- The exact moment normalization is a positive scalar and a geometric diagonal congruence. -/
theorem signed_posDef_of_raw {a : ℝ} (ha : |a|<1) (N : ℕ)
    (hraw : (rawHankel a N).PosDef) : (thetaCuspCenterMixedSignedHankel a N).PosDef := by
  let E : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (fun i => (2:ℝ)^i.val)
  have hE : Function.Injective E.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [E,Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)) hi
  have he : thetaCuspCenterMixedSignedHankel a N =
      (2*Real.pi)⁻¹ • (Eᴴ*rawHankel a N*E) := by
    ext i j
    simp only [E,Matrix.diagonal_conjTranspose,star_trivial,Matrix.diagonal_mul,
      Matrix.mul_diagonal,Matrix.smul_apply,smul_eq_mul,rawHankel,
      thetaCuspCenterMixedSignedHankel,rawMoment_eq_signedJet a ha,pow_add,one_div,inv_pow]
    field_simp [Real.pi_ne_zero]
  rw [he]
  exact (hraw.conjTranspose_mul_mul_same hE).smul (inv_pos.mpr (by positivity))

/-- Every finite actual signed theta section is strict at the strip-boundary aperture. -/
theorem signedHankel_boundary_posDef (N : ℕ) :
    (thetaCuspCenterMixedSignedHankel (1/2) N).PosDef :=
  signed_posDef_of_raw (by norm_num) N (raw_boundary_posDef N)

/-- Each finite rank remains strict on an aperture neighborhood crossing into the critical strip. -/
theorem signedHankel_posDef_near_half (N : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1/4 ∧ ∀ a : ℝ, |a-1/2|<δ →
      (thetaCuspCenterMixedSignedHankel a N).PosDef := by
  obtain ⟨δ,hδ,hp⟩ := raw_posDef_near_half N
  refine ⟨min δ (1/4),lt_min hδ (by norm_num),min_le_right _ _,fun a ha => ?_⟩
  have hsmall : |a-1/2|<1/4 := ha.trans_le (min_le_right _ _)
  have habs : |a|<1 := by
    rcases abs_lt.mp hsmall with ⟨hlo,hhi⟩
    have ha0 : 0<a := by linarith only [hlo]
    rw [abs_of_pos ha0]
    linarith only [hhi]
  exact signed_posDef_of_raw habs N (hp a (ha.trans_le (min_le_left _ _)))

/-- A single critical collar works simultaneously for every rank up to any prescribed finite bound. -/
theorem signedHankel_posDef_near_half_upto (N : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1/4 ∧ ∀ n≤N, ∀ a : ℝ, |a-1/2|<δ →
      (thetaCuspCenterMixedSignedHankel a n).PosDef := by
  obtain ⟨δ,hδ,hδU,hp⟩ := signedHankel_posDef_near_half N
  refine ⟨δ,hδ,hδU,fun n hn a ha => ?_⟩
  have hinj : Function.Injective (Fin.castLE hn) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin N => k.val) hij
  have he : (thetaCuspCenterMixedSignedHankel a N).submatrix (Fin.castLE hn) (Fin.castLE hn) =
      thetaCuspCenterMixedSignedHankel a n := by ext i j; rfl
  simpa only [he] using (hp a ha).submatrix hinj

end GaloisForLFunctions.ThetaCuspSections.CriticalCollar
