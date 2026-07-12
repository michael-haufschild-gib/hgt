import GaloisForLFunctions.RHTower.XiHurwitzAnchoredVandermondeOrientation
import GaloisForLFunctions.RHTower.HardySignChange
import GaloisForLFunctions.RHTower.DictionarySign

/-!
# Hardy moment data supplies the Xi anchor for Hurwitz orientation

A sign bracket for the real Xi restriction on the critical line produces an actual point of the
Xi divisor on that line.  The existing Hardy second-moment/first-moment gap theorem supplies such
a bracket from scalar integral data.  This discharges the anchor face of the anchored two-node
Hurwitz Vandermonde criterion.
-/

open Complex Set Function
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A sign bracket for the real Xi restriction produces an actual critical-line Xi-divisor
anchor. -/
theorem exists_xiHurwitzCriticalLineAnchor_of_sign_bracket
    {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hsign : (xi (linePt t₁)).re * (xi (linePt t₂)).re ≤ 0) :
    ∃ τ : XiDivisorSupport, (τ : ℂ).re = 1 / 2 := by
  have hcont : Continuous fun t : ℝ => (xi (linePt t)).re := by
    have hline : Continuous linePoint := by
      unfold linePoint
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact Complex.continuous_re.comp (xi_differentiable.continuous.comp hline)
  have hzero : ∃ t ∈ Set.Icc t₁ t₂, (xi (linePt t)).re = 0 := by
    rcases mul_nonpos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨t, ht, hxt⟩ :=
        intermediate_value_Icc' h12 hcont.continuousOn ⟨h2, h1⟩
      exact ⟨t, ht, hxt⟩
    · obtain ⟨t, ht, hxt⟩ :=
        intermediate_value_Icc h12 hcont.continuousOn ⟨h1, h2⟩
      exact ⟨t, ht, hxt⟩
  obtain ⟨t, _ht, hre⟩ := hzero
  have hreal : (xi (linePt t)).im = 0 := by
    apply xi_im_eq_zero_on_line
    simp only [linePt, Complex.add_re, ofReal_re, ofReal_im,
      Complex.mul_re, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hxi : xi (linePt t) = 0 := Complex.ext hre hreal
  let τ : XiDivisorSupport :=
    ⟨linePt t, mem_xi_divisor_support_of_eq_zero hxi⟩
  refine ⟨τ, ?_⟩
  simp only [τ, linePt, Complex.add_re, ofReal_re, ofReal_im,
    Complex.mul_re, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]

/-- The existing Hardy moment-gap criterion produces an actual critical-line Xi-divisor anchor. -/
theorem exists_xiHurwitzCriticalLineAnchor_of_hardy_moment_gap
    {α β S M_line : ℝ} (hαβ : α ≤ β) (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, ((xi (linePt u)).re) ^ 2)
    (hsup : ∀ u ∈ Set.Icc α β, |(xi (linePt u)).re| ≤ M_line)
    (hfm : M_line * |∫ u in α..β, (xi (linePt u)).re| < S) :
    ∃ τ : XiDivisorSupport, (τ : ℂ).re = 1 / 2 := by
  have hcont : Continuous fun u : ℝ => (xi (linePt u)).re := by
    have hline : Continuous linePoint := by
      unfold linePoint
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact Complex.continuous_re.comp (xi_differentiable.continuous.comp hline)
  obtain ⟨t₁, t₂, _ht₁, _ht₂, h12, hsign⟩ :=
    exists_sign_bracket_of_moment_gap
      (F := fun u : ℝ => (xi (linePt u)).re)
      hαβ hcont.continuousOn hS hsupply hsup hfm
  exact exists_xiHurwitzCriticalLineAnchor_of_sign_bracket h12 hsign

/-- Reality of the anchored Hurwitz separators for every possible critical-line anchor. -/
def XiHurwitzEveryCriticalAnchorPairVandermondeReal : Prop :=
  ∀ τ : XiDivisorSupport, (τ : ℂ).re = 1 / 2 →
    XiHurwitzAnchoredPairVandermondeReal τ

/-- A single Xi sign bracket plus reality of the two-node separators at critical-line anchors
proves RH. -/
theorem riemannHypothesis_of_xi_sign_bracket_and_allCriticalAnchorPairVandermondeReal
    {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hsign : (xi (linePt t₁)).re * (xi (linePt t₂)).re ≤ 0)
    (hreal : XiHurwitzEveryCriticalAnchorPairVandermondeReal) :
    RiemannHypothesis := by
  obtain ⟨τ, hτ⟩ :=
    exists_xiHurwitzCriticalLineAnchor_of_sign_bracket h12 hsign
  exact riemannHypothesis_of_exists_xiHurwitzAnchor_pairVandermondeReal
    ⟨τ, hτ, hreal τ hτ⟩

/-- **Hardy-to-Hurwitz top-down chain.**  One finite Hardy moment packet produces the critical-line
anchor; reality of all anchored two-node Hurwitz separators then proves RH. -/
theorem riemannHypothesis_of_xi_hardy_moment_gap_and_allCriticalAnchorPairVandermondeReal
    {α β S M_line : ℝ} (hαβ : α ≤ β) (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, ((xi (linePt u)).re) ^ 2)
    (hsup : ∀ u ∈ Set.Icc α β, |(xi (linePt u)).re| ≤ M_line)
    (hfm : M_line * |∫ u in α..β, (xi (linePt u)).re| < S)
    (hreal : XiHurwitzEveryCriticalAnchorPairVandermondeReal) :
    RiemannHypothesis := by
  obtain ⟨τ, hτ⟩ :=
    exists_xiHurwitzCriticalLineAnchor_of_hardy_moment_gap
      hαβ hS hsupply hsup hfm
  exact riemannHypothesis_of_exists_xiHurwitzAnchor_pairVandermondeReal
    ⟨τ, hτ, hreal τ hτ⟩

end

end RHTower
