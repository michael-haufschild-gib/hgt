import GaloisForLFunctions.RHTower.XiSquareDescentVerticalModulus
import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion
import GaloisForLFunctions.HTGeometry.MassDispersionUnitExpansion

/-!
# The localized vertical modulus criterion forces the Riemann hypothesis

An off-critical Xi zero can be moved by functional-equation and Schwarz reflection into the open
upper-right chamber, beyond any certified quartet-accretive radius and below the half-unit ceiling.
Its square is a nonreal zero of the square descent inside the principal-root chamber, which is
open.  Vertical modulus monotonicity there would force the descent to vanish along a whole vertical
segment, and the identity theorem would then make it identically zero, contradicting the nonzero
central value.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The principal-root chamber of a radius: squares of upper-right centered points with ordinate
below one half. -/
def xiSquareChamber (R : ℝ) : Set ℂ :=
  {w : ℂ | R < (Complex.sqrt w).re ∧ 0 < (Complex.sqrt w).im ∧
    (Complex.sqrt w).im < 1 / 2}

/-- Localized vertical modulus monotonicity on a principal-root chamber. -/
def XiSquareDescentVerticalModulusOn (R : ℝ) : Prop :=
  ∀ x t₁ t₂ : ℝ, t₁ ≤ t₂ →
    (∀ t ∈ Set.Icc t₁ t₂, ((x : ℂ) + (t : ℂ) * Complex.I) ∈ xiSquareChamber R) →
    ‖xiSquareDescent ((x : ℂ) + (t₁ : ℂ) * Complex.I)‖ ≤
      ‖xiSquareDescent ((x : ℂ) + (t₂ : ℂ) * Complex.I)‖

theorem continuousAt_complex_sqrt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContinuousAt Complex.sqrt w := by
  have h : Complex.sqrt = fun z : ℂ => z ^ (2⁻¹ : ℂ) := by
    funext z
    exact Complex.ext rfl rfl
  rw [h]
  exact continuousAt_cpow_const hw

theorem complex_sqrt_sq_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.sqrt (z ^ (2 : ℕ)) = z := by
  have hsq : Complex.sqrt (z ^ (2 : ℕ)) ^ (2 : ℕ) = z ^ (2 : ℕ) :=
    GaloisForLFunctions.HTGeometry.complex_sqrt_sq (z ^ (2 : ℕ))
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · exfalso
    have hre := GaloisForLFunctions.HTGeometry.sqrt_re_nonneg (z ^ (2 : ℕ))
    rw [h] at hre
    simp only [Complex.neg_re] at hre
    linarith

/-! ## Selecting an upper-right off-critical zero -/

theorem exists_XiC_zero_upperRight_of_not_rh {R : ℝ}
    (hband : XiOffLineQuartetAccretiveBand R) (hnot : ¬ RiemannHypothesis) :
    ∃ z : ℂ, XiC z = 0 ∧ R < z.re ∧ 0 < z.im ∧ z.im < 1 / 2 := by
  classical
  have hexists : ∃ rho : XiDivisorSupport, ((rho : ℂ)).re ≠ 1 / 2 := by
    by_contra hcon
    push Not at hcon
    exact hnot (riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half hcon)
  obtain ⟨rho, hrho⟩ := hexists
  have hxi : xi ((rho : ℂ)) = 0 := xi_eq_zero_of_mem_divisor_support rho
  set z₁ : ℂ := ((rho : ℂ) - 1 / 2) * (-Complex.I) with hz₁
  have hXz₁ : XiC z₁ = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z₁ * Complex.I = (rho : ℂ) := by
      rw [hz₁]
      have : (((rho : ℂ) - 1 / 2) * (-Complex.I)) * Complex.I =
          -(Complex.I * Complex.I) * ((rho : ℂ) - 1 / 2) := by ring
      rw [this, Complex.I_mul_I]
      ring
    rw [harg]
    exact hxi
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z₁).mp hXz₁
  have hqval : ((q.1 : ℂ)) = (rho : ℂ) := by
    have hpt : ((q.1 : ℂ) - 1 / 2) * (-Complex.I) = ((rho : ℂ) - 1 / 2) * (-Complex.I) := by
      rw [← xiSpectralPoint, hq, hz₁]
    have hI : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    have := mul_right_cancel₀ hI hpt
    linear_combination this
  have hoff : ((q.1 : ℂ)).re ≠ 1 / 2 := by rw [hqval]; exact hrho
  have hgap0 := xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine R hband q hoff
  obtain ⟨hlow, hhigh⟩ := xi_zero_re_mem_open_unit hxi
  set gamma : ℝ := ((rho : ℂ)).im with hgamma
  set beta : ℝ := ((rho : ℂ)).re with hbeta
  have hgap : R + 1 / 2 < |gamma| := by rw [hqval] at hgap0; exact hgap0
  have hb : beta - 1 / 2 ≠ 0 := sub_ne_zero.mpr hrho
  have hbabs : |beta - 1 / 2| < 1 / 2 := by
    rw [abs_lt]; constructor <;> linarith
  have hbpos : 0 < |beta - 1 / 2| := abs_pos.mpr hb
  have hRnonneg : 0 ≤ R := hband.1
  have hgabs : R < |gamma| := by linarith
  refine ⟨((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I, ?_,
    by simpa using hgabs, by simpa using hbpos, by simpa using hbabs⟩
  have hz₁val : z₁ = (gamma : ℂ) + (-(beta - 1 / 2) : ℝ) * Complex.I := by
    rw [hz₁]
    apply Complex.ext <;> simp [hgamma, hbeta]
  have hcandidates : ((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I = z₁ ∨
      ((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I = -z₁ ∨
      ((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I = (starRingEnd ℂ) z₁ ∨
      ((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I =
        -((starRingEnd ℂ) z₁) := by
    rw [hz₁val]
    rcases abs_cases gamma with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases (beta - 1 / 2) with ⟨hbv, _⟩ | ⟨hbv, _⟩ <;>
      rw [hg, hbv]
    · right; right; left; apply Complex.ext <;> simp
    · left; apply Complex.ext <;> simp
    · right; left; apply Complex.ext <;> simp
    · right; right; right; apply Complex.ext <;> simp
  rcases hcandidates with h | h | h | h
  · rw [h]; exact hXz₁
  · rw [h, XiC_even]; exact hXz₁
  · rw [h, XiC_conj, hXz₁, map_zero]
  · rw [h, XiC_even, XiC_conj, hXz₁, map_zero]

/-! ## The contradiction -/

private def upperRightSquareTarget (R : ℝ) : Set ℂ :=
  {w : ℂ | R < w.re} ∩ ({w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < 1 / 2})

private theorem isOpen_upperRightSquareTarget (R : ℝ) : IsOpen (upperRightSquareTarget R) := by
  refine (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

/-- **The localized vertical modulus criterion.**  Vertical modulus monotonicity of the square
descent on one certified principal-root chamber forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_xiSquareDescentVerticalModulusOn {R : ℝ}
    (hband : XiOffLineQuartetAccretiveBand R)
    (hvm : XiSquareDescentVerticalModulusOn R) : RiemannHypothesis := by
  by_contra hnot
  obtain ⟨z, hz0, hzR, hzim, hzhalf⟩ := exists_XiC_zero_upperRight_of_not_rh hband hnot
  have hzre : 0 < z.re := lt_of_le_of_lt hband.1 hzR
  set w0 : ℂ := z ^ (2 : ℕ) with hw0
  have hsqrt : Complex.sqrt w0 = z := complex_sqrt_sq_of_re_pos hzre
  have hw0im : 0 < w0.im := by
    rw [hw0, pow_two]
    simp only [Complex.mul_im]
    nlinarith
  have hF0 : xiSquareDescent w0 = 0 := by
    rw [hw0]
    exact (xiSquaredSeamEntireQuotient_sq z).trans hz0
  set W : ℝ → ℂ := fun t => ((w0.re : ℝ) : ℂ) + (t : ℂ) * Complex.I with hW
  have hWval : W w0.im = w0 := by
    rw [hW]
    apply Complex.ext <;> simp
  have hWcont : Continuous W := by rw [hW]; fun_prop
  have hsqcont : ContinuousAt Complex.sqrt (W w0.im) := by
    rw [hWval]
    exact continuousAt_complex_sqrt (Or.inr hw0im.ne')
  have hcomp : ContinuousAt (fun t : ℝ => Complex.sqrt (W t)) w0.im :=
    hsqcont.comp hWcont.continuousAt
  have hmemS : Complex.sqrt (W w0.im) ∈ upperRightSquareTarget R := by
    rw [hWval, hsqrt]
    exact ⟨hzR, hzim, hzhalf⟩
  have hev : ∀ᶠ t : ℝ in nhds w0.im, Complex.sqrt (W t) ∈ upperRightSquareTarget R :=
    hcomp.preimage_mem_nhds ((isOpen_upperRightSquareTarget R).mem_nhds hmemS)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hchamber : ∀ t : ℝ, |t - w0.im| < δ → W t ∈ xiSquareChamber R := by
    intro t ht
    have := hball (by rwa [Real.dist_eq])
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hzeros : ∀ t : ℝ, |t - w0.im| < δ → t ≤ w0.im → xiSquareDescent (W t) = 0 := by
    intro t ht hle
    have hseg : ∀ u ∈ Set.Icc t w0.im, ((w0.re : ℝ) : ℂ) + (u : ℂ) * Complex.I ∈
        xiSquareChamber R := by
      intro u hu
      refine hchamber u ?_
      rw [abs_lt] at ht ⊢
      constructor <;> [linarith [hu.1, ht.1]; linarith [hu.2]]
    have hstep := hvm w0.re t w0.im hle hseg
    rw [show ((w0.re : ℝ) : ℂ) + ((w0.im : ℝ) : ℂ) * Complex.I = w0 from hWval, hF0,
      norm_zero] at hstep
    exact norm_eq_zero.mp (le_antisymm hstep (norm_nonneg _))
  -- a sequence of zeros accumulating at `w0`
  set u : ℕ → ℂ := fun n => W (w0.im - δ / ((n : ℝ) + 2)) with hu
  have hpos : ∀ n : ℕ, 0 < δ / ((n : ℝ) + 2) := by
    intro n; positivity
  have hsmall : ∀ n : ℕ, δ / ((n : ℝ) + 2) < δ := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact div_lt_self hδ (by linarith)
  have huzero : ∀ n : ℕ, xiSquareDescent (u n) = 0 := by
    intro n
    refine hzeros _ ?_ (by linarith [hpos n])
    rw [show w0.im - δ / ((n : ℝ) + 2) - w0.im = -(δ / ((n : ℝ) + 2)) by ring, abs_neg,
      abs_of_pos (hpos n)]
    exact hsmall n
  have htend0 : Filter.Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have htendt : Filter.Tendsto (fun n : ℕ => w0.im - δ / ((n : ℝ) + 2))
      Filter.atTop (nhds w0.im) := by
    simpa using tendsto_const_nhds.sub htend0
  have htendu : Filter.Tendsto u Filter.atTop (nhds w0) := by
    have h : Filter.Tendsto (fun n : ℕ => W (w0.im - δ / ((n : ℝ) + 2))) Filter.atTop
        (nhds (W w0.im)) := (hWcont.continuousAt (x := w0.im)).tendsto.comp htendt
    rw [hWval] at h
    exact h
  have hune : ∀ n : ℕ, u n ≠ w0 := by
    intro n hcon
    have him := congrArg Complex.im hcon
    rw [hu] at him
    simp only [hW, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_add, mul_one, mul_zero, add_zero] at him
    linarith [hpos n]
  have htendw : Filter.Tendsto u Filter.atTop (nhdsWithin w0 {w0}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u htendu
      (Filter.Eventually.of_forall fun n => hune n)
  have hfreq : ∃ᶠ w in nhdsWithin w0 {w0}ᶜ, xiSquareDescent w = 0 :=
    htendw.frequently (Filter.Eventually.of_forall huzero).frequently
  have hanalytic : AnalyticOnNhd ℂ xiSquareDescent Set.univ :=
    differentiable_xiSquaredSeamEntireQuotient.differentiableOn.analyticOnNhd isOpen_univ
  have hzeroAll := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isPreconnected_univ) (Set.mem_univ w0) hfreq
  have hcenter : xiSquareDescent 0 = XiC 0 := by
    have := xiSquaredSeamEntireQuotient_sq 0
    simpa using this
  have : xiSquareDescent 0 = 0 := hzeroAll (Set.mem_univ 0)
  rw [hcenter] at this
  exact XiC_zero_ne this

/-- Global vertical modulus monotonicity restricts to every chamber of nonnegative radius. -/
theorem xiSquareDescentVerticalModulusOn_of_global {R : ℝ} (hR : 0 ≤ R)
    (hvm : XiSquareDescentVerticalModulus) : XiSquareDescentVerticalModulusOn R := by
  intro x t₁ t₂ h12 hseg
  have hmem := hseg t₁ (Set.left_mem_Icc.mpr h12)
  obtain ⟨hre, him, _⟩ := hmem
  have hzsq := GaloisForLFunctions.HTGeometry.complex_sqrt_sq ((x : ℂ) + (t₁ : ℂ) * Complex.I)
  have hpos : 0 < ((x : ℂ) + (t₁ : ℂ) * Complex.I).im := by
    rw [← hzsq, pow_two]
    simp only [Complex.mul_im]
    nlinarith [lt_of_le_of_lt hR hre, him]
  have ht₁ : 0 < t₁ := by simpa using hpos
  exact hvm x t₁ t₂ ht₁.le h12

/-- **The square-descent vertical modulus criterion at the certified quartet radius.** -/
theorem riemannHypothesis_iff_xiSquareDescentVerticalModulusOn_twoHundredEighteen_twentyFifths :
    RiemannHypothesis ↔ XiSquareDescentVerticalModulusOn (218 / 25) := by
  constructor
  · intro hRH
    exact xiSquareDescentVerticalModulusOn_of_global (by norm_num)
      (xiSquareDescentVerticalModulus_of_rh hRH)
  · exact riemannHypothesis_of_xiSquareDescentVerticalModulusOn
      xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

/-- **RH is exactly global vertical modulus monotonicity of the square descent.** -/
theorem riemannHypothesis_iff_xiSquareDescentVerticalModulus :
    RiemannHypothesis ↔ XiSquareDescentVerticalModulus := by
  constructor
  · exact xiSquareDescentVerticalModulus_of_rh
  · intro hvm
    exact riemannHypothesis_of_xiSquareDescentVerticalModulusOn
      xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths
      (xiSquareDescentVerticalModulusOn_of_global (by norm_num) hvm)

end

end RHTower
