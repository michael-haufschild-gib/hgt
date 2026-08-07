import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.EMAnnulusSupply

/-!
# A source-side anti-Herglotz gate to RH

The centered continued prime--archimedean trace is the logarithmic derivative of `XiC` away from
its natural poles.  If its imaginary part is nonpositive throughout the centered upper half-strip,
then an off-line zero is impossible: reflect a hypothetical right-half `xi` zero into the left
half-strip and approach it from the right.  The normalized local logarithmic derivative has positive
residue equal to the full zero multiplicity, producing a point where the source trace has strictly
positive imaginary part.

The resulting implication uses no zero enumeration, trace-Hankel form, or operator spectrum.  Its
open premise is the concrete accretivity inequality for the continued von-Mangoldt flux minus the
fixed archimedean logarithmic derivative.  This file proves the top-down gate, not that inequality.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- The centered abscissa `1/2 + z i` has real part `1/2 - Im z`, so it stays in the right half
plane exactly while `Im z < 1/2`. -/
theorem centeredAbscissa_re_pos {z : ℂ} (hzHalf : z.im < 1 / 2) :
    0 < (1 / 2 + z * I).re := by
  simp [mul_re]
  linarith

/-- The centered abscissa never reaches the zeta pole: `Re (1/2 + z i) = 1` would need
`Im z = -1/2`, which the upper half plane excludes. -/
theorem centeredAbscissa_ne_one {z : ℂ} (hzIm : 0 < z.im) :
    1 / 2 + z * I ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [mul_re] at hre
  linarith

/-- The continued prime--archimedean trace is anti-Herglotz on the centered upper half-strip. -/
def ContinuedPrimeArchUpperAntiHerglotz : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0

/-- Accretivity of the completed prime--Gamma flux on the left half of the critical strip. -/
def CompletedPrimeGammaLeftHalfAccretive : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → riemannZeta s ≠ 0 →
    0 ≤ (infinitePrimeFlux s - logDeriv archFactor s).re

/-- Left-half accretivity is exactly the anti-Herglotz sign after passing to the centered
coordinate `s = 1/2 + z I`. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_completedPrimeGammaLeftHalfAccretive
    (hacc : CompletedPrimeGammaLeftHalfAccretive) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  let s : ℂ := 1 / 2 + z * I
  have hsre : s.re = 1 / 2 - z.im := by
    simp [s, mul_re]
    ring
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have hshalf : s.re < 1 / 2 := by rw [hsre]; linarith
  have hflux := hacc s hspos hshalf (by simpa [s] using hzeta)
  rw [continuedPrimeArchSourceRelativeTrace]
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ 0
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul]
  linarith

/-- Anti-Herglotzness of the continued source excludes every off-line zero and therefore proves
RH. The contradiction uses the full positive multiplicity of a reflected zero's local pole. -/
theorem riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (hanti : ContinuedPrimeArchUpperAntiHerglotz) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  have hρgt : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
  have hρpos : 0 < ρ.re := lt_trans (by norm_num) hρgt
  have hρlt : ρ.re < 1 := xi_zero_re_lt_one hzero
  let σ : ℂ := 1 - ρ
  have hσzero : xi σ = 0 := by
    dsimp only [σ]
    rw [xi_one_sub, hzero]
  have hσpos : 0 < σ.re := by
    dsimp only [σ]
    simp only [sub_re, one_re]
    linarith
  have hσhalf : σ.re < 1 / 2 := by
    dsimp only [σ]
    simp only [sub_re, one_re]
    linarith
  obtain ⟨R, hR, h, hhan, hh0, hlocal⟩ :=
    exists_xi_normalizedLogDeriv_factorization σ
  let ε : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ)⁻¹)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp only [ε]
    positivity
  have hε0 : Tendsto ε atTop (nhds 0) := by
    dsimp only [ε]
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hshift : Tendsto (fun n : ℕ => σ + (ε n : ℂ)) atTop (nhds σ) := by
    have hcast : Tendsto (fun n : ℕ => (ε n : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hε0
    simpa using tendsto_const_nhds.add hcast
  have hσball : σ ∈ ball σ R := mem_ball_self hR
  have hhAt : AnalyticAt ℂ h σ := hhan σ hσball
  have hlogcont : ContinuousAt (logDeriv h) σ := by
    rw [show logDeriv h = fun z => deriv h z / h z by
      funext z
      rw [logDeriv_apply]]
    exact hhAt.deriv.continuousAt.div hhAt.continuousAt (hh0 σ hσball)
  have hlogtend : Tendsto (fun n : ℕ => logDeriv h (σ + (ε n : ℂ)))
      atTop (nhds (logDeriv h σ)) := hlogcont.tendsto.comp hshift
  have hεcast0 : Tendsto (fun n : ℕ => (ε n : ℂ)) atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp hε0
  have hrem : Tendsto
      (fun n : ℕ => (ε n : ℂ) * logDeriv h (σ + (ε n : ℂ)))
      atTop (nhds 0) := by
    simpa using hεcast0.mul hlogtend
  let m : ℕ := (analyticOrderAt xi σ).toNat
  have hmpos : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hσzero)
  have hremRe : Tendsto
      (fun n : ℕ => ((ε n : ℂ) * logDeriv h (σ + (ε n : ℂ))).re)
      atTop (nhds 0) := Complex.continuous_re.continuousAt.tendsto.comp hrem
  have hevRe : ∀ᶠ n in atTop,
      -((m : ℝ) / 2) <
        ((ε n : ℂ) * logDeriv h (σ + (ε n : ℂ))).re :=
    hremRe.eventually (eventually_gt_nhds (by exact neg_neg_of_pos (by positivity)))
  have hevBall : ∀ᶠ n in atTop, σ + (ε n : ℂ) ∈ ball σ R :=
    hshift (isOpen_ball.mem_nhds hσball)
  have hevGap : ∀ᶠ n in atTop, ε n < 1 / 2 - σ.re := by
    have hgap : 0 < (1 / 2 - σ.re) := by linarith
    exact hε0.eventually (eventually_lt_nhds hgap)
  obtain ⟨n, hnRe, hnBall, hnGap⟩ := (hevRe.and (hevBall.and hevGap)).exists
  let s : ℂ := σ + (ε n : ℂ)
  let z : ℂ := (s - 1 / 2) * (-I)
  have hsre : s.re = σ.re + ε n := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; linarith [hεpos n]
  have hshalf : s.re < 1 / 2 := by rw [hsre]; linarith
  have hzne : z.im = 1 / 2 - s.re := by simp [z]
  have hzimpos : 0 < z.im := by rw [hzne]; linarith
  have hzimhalf : z.im < 1 / 2 := by rw [hzne]; linarith
  have hsnσ : s ≠ σ := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [hsre] at hre
    linarith [hεpos n]
  have hnorm := hlocal s hnBall hsnσ
  have hsub : s - σ = (ε n : ℂ) := by simp [s]
  rw [hsub] at hnorm
  have hnormRe := congrArg Complex.re hnorm
  have hlogpos : 0 < (logDeriv xi s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, add_re] at hnormRe
    change ε n * (logDeriv xi s).re =
      (m : ℝ) + ε n * (logDeriv h s).re at hnormRe
    have hnRe' : -((m : ℝ) / 2) < ε n * (logDeriv h s).re := by
      simpa [s] using hnRe
    nlinarith [hεpos n, show (0 : ℝ) < m by exact_mod_cast hmpos]
  have hxiS : xi s ≠ 0 := by
    intro hs0
    have hld0 : logDeriv xi s = 0 := by simp [logDeriv_apply, hs0]
    rw [hld0, zero_re] at hlogpos
    linarith
  have hs1 : s ≠ 1 := by
    intro hsone
    have hre := congrArg Complex.re hsone
    rw [one_re] at hre
    linarith
  have hzetaS : riemannZeta s ≠ 0 := by
    exact (xi_eq_zero_iff hspos hs1).not.mp hxiS
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hsource : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (by rw [hcoord]; exact hspos)
      (by rw [hcoord]; exact hs1)
      (by rw [hcoord]; exact hzetaS)]
    symm
    apply logDeriv_XiC_eq_relativeResolventTrace
    rw [XiC, hcoord]
    exact hxiS
  have hsourcePos : 0 < (continuedPrimeArchSourceRelativeTrace z).im := by
    rw [hsource, logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord]
    simpa using hlogpos
  have hsourceNonpos := hanti z hzimpos hzimhalf (by rw [hcoord]; exact hzetaS)
  linarith

/-- Completed prime--Gamma accretivity on the left half-strip proves RH. -/
theorem riemannHypothesis_of_completedPrimeGammaLeftHalfAccretive
    (hacc : CompletedPrimeGammaLeftHalfAccretive) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_completedPrimeGammaLeftHalfAccretive hacc)

/-! ## Countable Gaussian-rational source criterion -/

/-- A Gaussian-rational point, indexed by a pair of rational numbers. -/
def gaussianRatPoint (q : ℚ × ℚ) : ℂ :=
  ((q.1 : ℝ) : ℂ) + ((q.2 : ℝ) : ℂ) * I

/-- Gaussian-rational points are dense in the complex plane. -/
theorem denseRange_gaussianRatPoint : DenseRange gaussianRatPoint := by
  have hprod : DenseRange (fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hsymm : DenseRange Complex.equivRealProdCLM.symm :=
    Complex.equivRealProdCLM.symm.surjective.denseRange
  have hcomp := hsymm.comp hprod Complex.equivRealProdCLM.symm.continuous
  simpa [gaussianRatPoint, Function.comp_def, Complex.equivRealProdCLM_symm_apply] using! hcomp

/-- The completed continued prime--Gamma flux in the original `s` coordinate. -/
def completedPrimeGammaFlux (s : ℂ) : ℂ :=
  infinitePrimeFlux s - logDeriv archFactor s

/-- Away from its natural poles, the completed prime--Gamma flux is continuous. -/
theorem continuousAt_completedPrimeGammaFlux {s : ℂ}
    (hspos : 0 < s.re) (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    ContinuousAt completedPrimeGammaFlux s := by
  have hzetaAn : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hlogz : ContinuousAt (logDeriv riemannZeta) s := by
    rw [show logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z by
      funext z
      rw [logDeriv_apply]]
    exact hzetaAn.deriv.continuousAt.div hzetaAn.continuousAt hzeta
  have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) s := by fun_prop
  have harch : AnalyticAt ℂ archFactor s :=
    hpoly.mul (Gammaℝ_analyticAt (Gammaℝ_ne_zero_of_re_pos hspos))
  have harch0 : archFactor s ≠ 0 := archFactor_ne_zero
    (by intro h; subst s; norm_num at hspos)
    hs1 (Gammaℝ_ne_zero_of_re_pos hspos)
  have hloga : ContinuousAt (logDeriv archFactor) s := by
    rw [show logDeriv archFactor = fun z => deriv archFactor z / archFactor z by
      funext z
      rw [logDeriv_apply]]
    exact harch.deriv.continuousAt.div harch.continuousAt harch0
  simpa [completedPrimeGammaFlux, infinitePrimeFlux] using! hlogz.neg.sub hloga

/-- Countable source accretivity: only Gaussian-rational values in the left half-strip are tested. -/
def CompletedPrimeGammaGaussianRatLeftHalfAccretive : Prop :=
  ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      0 ≤ (completedPrimeGammaFlux (gaussianRatPoint q)).re

/-- Continuity and Gaussian-rational density upgrade the countable source tests to the full
left-half-strip accretivity condition. -/
theorem completedPrimeGammaLeftHalfAccretive_of_gaussianRat
    (hrat : CompletedPrimeGammaGaussianRatLeftHalfAccretive) :
    CompletedPrimeGammaLeftHalfAccretive := by
  intro s hspos hshalf hzeta
  by_contra hnonneg
  have hneg : (completedPrimeGammaFlux s).re < 0 := lt_of_not_ge hnonneg
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    linarith
  have hcont := continuousAt_completedPrimeGammaFlux hspos hs1 hzeta
  have hrePos : {w : ℂ | 0 < w.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hspos
  have hreHalf : {w : ℂ | w.re < 1 / 2} ∈ nhds s :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hshalf
  have hzetaAn : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hzetaNe : {w : ℂ | riemannZeta w ≠ 0} ∈ nhds s :=
    hzetaAn.continuousAt.eventually_ne hzeta
  have hfre : ContinuousAt (fun w => (completedPrimeGammaFlux w).re) s :=
    Complex.continuous_re.continuousAt.comp hcont
  have hfluxNeg : {w : ℂ | (completedPrimeGammaFlux w).re < 0} ∈ nhds s :=
    hfre.tendsto (Iio_mem_nhds hneg)
  have hall : {w : ℂ | 0 < w.re} ∩ {w : ℂ | w.re < 1 / 2} ∩
      {w : ℂ | riemannZeta w ≠ 0} ∩
      {w : ℂ | (completedPrimeGammaFlux w).re < 0} ∈ nhds s :=
    inter_mem (inter_mem (inter_mem hrePos hreHalf) hzetaNe) hfluxNeg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  obtain ⟨q, hqball⟩ := denseRange_gaussianRatPoint.exists_mem_open isOpen_ball
    ⟨s, mem_ball_self hr⟩
  have hq := hball hqball
  have hqnonneg := hrat q hq.1.1.1 hq.1.1.2 hq.1.2
  exact (not_lt_of_ge hqnonneg) hq.2

/-- Countable source-value gate to RH: it is enough to prove completed prime--Gamma
accretivity at the Gaussian-rational points of the left half-strip. -/
theorem riemannHypothesis_of_completedPrimeGammaGaussianRatLeftHalfAccretive
    (hrat : CompletedPrimeGammaGaussianRatLeftHalfAccretive) :
    RiemannHypothesis :=
  riemannHypothesis_of_completedPrimeGammaLeftHalfAccretive
    (completedPrimeGammaLeftHalfAccretive_of_gaussianRat hrat)

end

end RHTower
