import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate

/-!
# A finite upper-bound gate for the continued prime--archimedean source

The anti-Herglotz sign can be weakened substantially.  If RH fails, reflection of a right-half Xi
zero produces a source pole in the centered upper half-strip.  The positive multiplicity residue
forces the imaginary part of the continued prime--archimedean trace above every prescribed real
constant along a regular sequence approaching that pole.

Consequently RH is equivalent to the mere existence of a finite global upper bound for the source
imaginary part on its upper-half-strip pole-free domain.  No sign, Pick minor, or Cauchy-packet
positivity is required.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- The continued prime--archimedean source has some finite imaginary-part upper bound on the
centered upper half-strip, away from its natural poles. -/
def ContinuedPrimeArchUpperImBoundedAbove : Prop :=
  ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ C

/-- Any finite upper bound for the source imaginary part excludes off-line zeros and proves RH. -/
theorem riemannHypothesis_of_continuedPrimeArchUpperImBoundedAbove
    (hbounded : ContinuedPrimeArchUpperImBoundedAbove) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := hbounded
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
  have hshiftWithin : Tendsto (fun n : ℕ => σ + (ε n : ℂ)) atTop
      (nhdsWithin σ ({σ}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hshift, Eventually.of_forall (fun n => ?_)⟩
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : (ε n : ℂ) = 0 := by linear_combination h
    exact (ofReal_ne_zero.mpr (hεpos n).ne') this
  let m : ℕ := (analyticOrderAt xi σ).toNat
  have hmpos : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hσzero)
  have hnorm := (xi_normalizedLogDeriv_tendsto_order σ).comp hshiftWithin
  have hnorm' : Tendsto
      (fun n : ℕ => (ε n : ℂ) * logDeriv xi (σ + (ε n : ℂ)))
      atTop (nhds (m : ℂ)) := by
    simpa [m, Function.comp_def] using hnorm
  have hnormRe : Tendsto
      (fun n : ℕ => ε n * (logDeriv xi (σ + (ε n : ℂ))).re)
      atTop (nhds (m : ℝ)) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hnorm'
    simpa [mul_re, Function.comp_def] using hre
  let B : ℝ := max C 0 + 1
  have hBpos : 0 < B := by dsimp [B]; linarith [le_max_right C 0]
  have hCB : C < B := by dsimp [B]; linarith [le_max_left C 0]
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hevLower : ∀ᶠ n in atTop,
      (m : ℝ) / 2 < ε n * (logDeriv xi (σ + (ε n : ℂ))).re :=
    hnormRe.eventually (eventually_gt_nhds (by linarith))
  have hsmallPos : 0 < (m : ℝ) / (2 * B) := by positivity
  have hevSmall : ∀ᶠ n in atTop, ε n < (m : ℝ) / (2 * B) :=
    hε0.eventually (eventually_lt_nhds hsmallPos)
  have hgapPos : 0 < 1 / 2 - σ.re := by linarith
  have hevGap : ∀ᶠ n in atTop, ε n < 1 / 2 - σ.re :=
    hε0.eventually (eventually_lt_nhds hgapPos)
  obtain ⟨n, hnLower, hnSmall, hnGap⟩ :=
    (hevLower.and (hevSmall.and hevGap)).exists
  let s : ℂ := σ + (ε n : ℂ)
  let z : ℂ := (s - 1 / 2) * (-I)
  have hsre : s.re = σ.re + ε n := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; linarith [hεpos n]
  have hshalf : s.re < 1 / 2 := by rw [hsre]; linarith
  have hlogB : B < (logDeriv xi s).re := by
    have hεB : ε n * B < (m : ℝ) / 2 := by
      have h := mul_lt_mul_of_pos_right hnSmall hBpos
      field_simp [ne_of_gt hBpos] at h
      nlinarith
    dsimp only [s]
    nlinarith [hεpos n]
  have hxiS : xi s ≠ 0 := by
    intro hs0
    have hld0 : logDeriv xi s = 0 := by simp [logDeriv_apply, hs0]
    rw [hld0, zero_re] at hlogB
    linarith
  have hs1 : s ≠ 1 := by
    intro hsone
    have hre := congrArg Complex.re hsone
    rw [one_re] at hre
    linarith
  have hzetaS : riemannZeta s ≠ 0 :=
    (xi_eq_zero_iff hspos hs1).not.mp hxiS
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hzim : z.im = 1 / 2 - s.re := by simp [z]
  have hzimpos : 0 < z.im := by rw [hzim]; linarith
  have hzimhalf : z.im < 1 / 2 := by rw [hzim]; linarith
  have hsource : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (by rw [hcoord]; exact hspos)
      (by rw [hcoord]; exact hs1)
      (by rw [hcoord]; exact hzetaS)]
    symm
    apply logDeriv_XiC_eq_relativeResolventTrace
    rw [XiC, hcoord]
    exact hxiS
  have himEq : (continuedPrimeArchSourceRelativeTrace z).im =
      (logDeriv xi s).re := by
    rw [hsource, logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord]
    simp
  have hsourceGt : C < (continuedPrimeArchSourceRelativeTrace z).im := by
    rw [himEq]
    exact hCB.trans hlogB
  exact (not_lt_of_ge (hC z hzimpos hzimhalf (by rw [hcoord]; exact hzetaS))) hsourceGt

/-- RH gives the sharp upper bound zero through the anti-Herglotz sign. -/
theorem continuedPrimeArchUpperImBoundedAbove_of_riemannHypothesis
    (hRH : RiemannHypothesis) : ContinuedPrimeArchUpperImBoundedAbove := by
  refine ⟨0, ?_⟩
  exact continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mp
    (continuedPrimeArchUpperCauchyDiagonalNonnegative_of_riemannHypothesis hRH)

/-- Exact finite-upper-bound criterion for RH. -/
theorem continuedPrimeArchUpperImBoundedAbove_iff_riemannHypothesis :
    ContinuedPrimeArchUpperImBoundedAbove ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_continuedPrimeArchUpperImBoundedAbove,
    continuedPrimeArchUpperImBoundedAbove_of_riemannHypothesis⟩

/-- Positive failure law: if RH fails, the source imaginary part exceeds every prescribed bound
somewhere in the centered upper half-strip pole-free domain. -/
theorem exists_continuedPrimeArchSource_im_gt_of_not_riemannHypothesis
    (hnot : ¬ RiemannHypothesis) (C : ℝ) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧
      riemannZeta (1 / 2 + z * I) ≠ 0 ∧
      C < (continuedPrimeArchSourceRelativeTrace z).im := by
  by_contra h
  push Not at h
  apply hnot
  apply riemannHypothesis_of_continuedPrimeArchUpperImBoundedAbove
  refine ⟨C, fun z hzpos hzhalf hzeta => ?_⟩
  exact h z hzpos hzhalf hzeta

/-- A finite lower bound for the completed prime--Gamma flux on the full left half-strip. -/
def CompletedPrimeGammaLeftHalfBoundedBelow : Prop :=
  ∃ L : ℝ, ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
    riemannZeta s ≠ 0 → L ≤ (completedPrimeGammaFlux s).re

/-- Countable finite lower boundedness: only Gaussian-rational points of the left half-strip are
tested. -/
def CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow : Prop :=
  ∃ L : ℝ, ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      L ≤ (completedPrimeGammaFlux (gaussianRatPoint q)).re

/-- Continuity and Gaussian-rational density upgrade a countable finite lower bound to the full
left half-strip. -/
theorem completedPrimeGammaLeftHalfBoundedBelow_of_gaussianRat
    (hrat : CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow) :
    CompletedPrimeGammaLeftHalfBoundedBelow := by
  obtain ⟨L, hL⟩ := hrat
  refine ⟨L, ?_⟩
  intro s hspos hshalf hzeta
  by_contra hge
  have hlt : (completedPrimeGammaFlux s).re < L := lt_of_not_ge hge
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
  have hfluxLt : {w : ℂ | (completedPrimeGammaFlux w).re < L} ∈ nhds s :=
    hfre.tendsto (Iio_mem_nhds hlt)
  have hall : {w : ℂ | 0 < w.re} ∩ {w : ℂ | w.re < 1 / 2} ∩
      {w : ℂ | riemannZeta w ≠ 0} ∩
      {w : ℂ | (completedPrimeGammaFlux w).re < L} ∈ nhds s :=
    inter_mem (inter_mem (inter_mem hrePos hreHalf) hzetaNe) hfluxLt
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  obtain ⟨q, hqball⟩ := denseRange_gaussianRatPoint.exists_mem_open isOpen_ball
    ⟨s, mem_ball_self hr⟩
  have hq := hball hqball
  exact (not_lt_of_ge (hL q hq.1.1.1 hq.1.1.2 hq.1.2)) hq.2

/-- A full left-half-strip lower bound becomes an upper bound for the centered source imaginary
part. -/
theorem continuedPrimeArchUpperImBoundedAbove_of_completedPrimeGammaLeftHalfBoundedBelow
    (hfull : CompletedPrimeGammaLeftHalfBoundedBelow) :
    ContinuedPrimeArchUpperImBoundedAbove := by
  obtain ⟨L, hL⟩ := hfull
  refine ⟨-L, ?_⟩
  intro z hzpos hzhalf hzeta
  let s : ℂ := 1 / 2 + z * I
  have hsre : s.re = 1 / 2 - z.im := by simp [s, mul_re]; ring
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have hshalf : s.re < 1 / 2 := by rw [hsre]; linarith
  have hbound := hL s hspos hshalf (by simpa [s] using hzeta)
  change L ≤ (infinitePrimeFlux s - logDeriv archFactor s).re at hbound
  rw [continuedPrimeArchSourceRelativeTrace]
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ -L
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul]
  linarith

/-- Countable finite-lower-bound source criterion implies RH. -/
theorem riemannHypothesis_of_completedPrimeGammaGaussianRatLeftHalfBoundedBelow
    (hrat : CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperImBoundedAbove
    (continuedPrimeArchUpperImBoundedAbove_of_completedPrimeGammaLeftHalfBoundedBelow
      (completedPrimeGammaLeftHalfBoundedBelow_of_gaussianRat hrat))

/-- RH supplies the sharp Gaussian-rational lower bound zero. -/
theorem completedPrimeGammaGaussianRatLeftHalfBoundedBelow_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow := by
  let hanti : ContinuedPrimeArchUpperAntiHerglotz :=
    continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mp
      (continuedPrimeArchUpperCauchyDiagonalNonnegative_of_riemannHypothesis hRH)
  refine ⟨0, ?_⟩
  intro q hqpos hqhalf hqzeta
  let s : ℂ := gaussianRatPoint q
  let z : ℂ := (s - 1 / 2) * (-I)
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hzim : z.im = 1 / 2 - s.re := by simp [z]
  have hzpos : 0 < z.im := by rw [hzim]; dsimp only [s]; linarith
  have hzhalf : z.im < 1 / 2 := by rw [hzim]; dsimp only [s]; linarith
  have ha := hanti z hzpos hzhalf (by rw [hcoord]; exact hqzeta)
  rw [continuedPrimeArchSourceRelativeTrace, hcoord] at ha
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ 0 at ha
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul] at ha
  change 0 ≤ (infinitePrimeFlux s - logDeriv archFactor s).re
  linarith

/-- Exact countable finite-lower-bound criterion for RH. -/
theorem completedPrimeGammaGaussianRatLeftHalfBoundedBelow_iff_riemannHypothesis :
    CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_completedPrimeGammaGaussianRatLeftHalfBoundedBelow,
    completedPrimeGammaGaussianRatLeftHalfBoundedBelow_of_riemannHypothesis⟩

/-- A finite lower bound on the full left half-strip is exactly RH. -/
theorem completedPrimeGammaLeftHalfBoundedBelow_iff_riemannHypothesis :
    CompletedPrimeGammaLeftHalfBoundedBelow ↔ RiemannHypothesis := by
  constructor
  · intro hfull
    exact riemannHypothesis_of_continuedPrimeArchUpperImBoundedAbove
      (continuedPrimeArchUpperImBoundedAbove_of_completedPrimeGammaLeftHalfBoundedBelow hfull)
  · intro hRH
    exact completedPrimeGammaLeftHalfBoundedBelow_of_gaussianRat
      (completedPrimeGammaGaussianRatLeftHalfBoundedBelow_of_riemannHypothesis hRH)

end

end RHTower
