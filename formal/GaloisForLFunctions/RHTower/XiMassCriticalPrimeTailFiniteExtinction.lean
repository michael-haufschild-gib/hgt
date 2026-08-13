import GaloisForLFunctions.RHTower.XiMassRadialRiemannLebesgue
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge

/-!
# Finite prime-tail extinction and the nonuniform infinite remainder

Every fixed critical half-density prime-power atom decays in future vertical mass time by the
radial Riemann--Lebesgue theorem.  Hence every finite arithmetic Green current decays, and it is
uniformly bounded by its literal finite von-Mangoldt mass.

The full current behaves differently.  Uniform boundedness of its remainder after subtracting
even one arbitrary finite prime-power packet is equivalent to RH, and therefore equivalent to
vanishing of the canonical reflection self-intersection charge.  Under false RH that remainder is
unbounded for every finite packet.  This isolates the exact noncommuting-limit obstruction: no
finite prime truncation can carry or cancel the horizontal divisor charge; the missing producer
must control the infinite prime tail uniformly in vertical time.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Finite critical half-density cross current on a labelled prime-power packet. -/
def xiMassCriticalHalfDensityCrossSeriesFinite
    (a sigma u : ℝ) (S : Finset DeningerPrimePowerIndex) : ℂ :=
  ∑ n ∈ S, xiMassCriticalHalfDensityCrossAtom a sigma u n

/-- Finite Green--Stokes current on the same labelled prime-power packet. -/
def xiMassCriticalPrimeTailGreenCurrentFinite
    (a sigma u : ℝ) (S : Finset DeningerPrimePowerIndex) : ℂ :=
  ∑ n ∈ S, xiMassCriticalPrimeTailGreenAtomPairing a sigma u n

/-- Each fixed critical half-density prime-power atom becomes extinct in future vertical time. -/
theorem tendsto_xiMassCriticalHalfDensityCrossAtom_vertical_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (n : DeningerPrimePowerIndex) :
    Tendsto (fun u : ℝ => xiMassCriticalHalfDensityCrossAtom a sigma u n)
      atTop (nhds 0) := by
  unfold xiMassCriticalHalfDensityCrossAtom
  have hprofile : Tendsto
      (fun u : ℝ => xiMassSpectralCrossProfile a sigma u
        (deningerPrimePowerTime n)) atTop (nhds 0) := by
    simpa only [xiMassSpectralCrossProfile_eq_stripFourier] using
      tendsto_stripFourier_xiMassAnalyticTest_vertical_atTop_zero
        ha hsigma (deningerPrimePowerTime n)
  simpa only [mul_zero] using
    hprofile.const_mul (criticalMellinAtomWeight (n : ℕ) : ℂ)

/-- Every finite critical half-density cross current becomes extinct in future vertical time. -/
theorem tendsto_xiMassCriticalHalfDensityCrossSeriesFinite_vertical_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (S : Finset DeningerPrimePowerIndex) :
    Tendsto
      (fun u : ℝ => xiMassCriticalHalfDensityCrossSeriesFinite a sigma u S)
      atTop (nhds 0) := by
  unfold xiMassCriticalHalfDensityCrossSeriesFinite
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum S
      (fun n _hn =>
        tendsto_xiMassCriticalHalfDensityCrossAtom_vertical_atTop_zero
          ha hsigma n)

/-- Every finite prime-tail Green current becomes extinct in future vertical time. -/
theorem tendsto_xiMassCriticalPrimeTailGreenCurrentFinite_vertical_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (S : Finset DeningerPrimePowerIndex) :
    Tendsto
      (fun u : ℝ => xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S)
      atTop (nhds 0) := by
  unfold xiMassCriticalPrimeTailGreenCurrentFinite
  simpa only [xiMassCriticalPrimeTailGreenAtomPairing_eq_neg_crossAtom ha hsigma,
    neg_zero, Finset.sum_const_zero] using
      tendsto_finsetSum S
        (fun n _hn =>
          (tendsto_xiMassCriticalHalfDensityCrossAtom_vertical_atTop_zero
            ha hsigma n).neg)

/-- Uniform vertical-time bound for one critical half-density prime-power atom. -/
theorem norm_xiMassCriticalHalfDensityCrossAtom_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ)
    (n : DeningerPrimePowerIndex) :
    ‖xiMassCriticalHalfDensityCrossAtom a sigma u n‖ ≤
      criticalMellinAtomWeight (n : ℕ) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  rw [xiMassCriticalHalfDensityCrossAtom, norm_mul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (criticalMellinAtomWeight_nonneg (n : ℕ)),
    xiMassSpectralCrossProfile_eq_stripFourier]
  exact mul_le_mul_of_nonneg_left
    (norm_stripFourier_xiMassAnalyticTest_vertical_le ha hsigma u
      (deningerPrimePowerTime n))
    (criticalMellinAtomWeight_nonneg (n : ℕ))

/-- A finite Green current is uniformly bounded by its literal finite von-Mangoldt mass. -/
theorem norm_xiMassCriticalPrimeTailGreenCurrentFinite_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ)
    (S : Finset DeningerPrimePowerIndex) :
    ‖xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ ≤
      (∑ n ∈ S, criticalMellinAtomWeight (n : ℕ)) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  rw [xiMassCriticalPrimeTailGreenCurrentFinite]
  calc
    ‖∑ n ∈ S, xiMassCriticalPrimeTailGreenAtomPairing a sigma u n‖ ≤
        ∑ n ∈ S, ‖xiMassCriticalPrimeTailGreenAtomPairing a sigma u n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ S, criticalMellinAtomWeight (n : ℕ) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
      apply Finset.sum_le_sum
      intro n _hn
      rw [xiMassCriticalPrimeTailGreenAtomPairing_eq_neg_crossAtom ha hsigma,
        norm_neg]
      exact norm_xiMassCriticalHalfDensityCrossAtom_le ha hsigma u n
    _ = (∑ n ∈ S, criticalMellinAtomWeight (n : ℕ)) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
      rw [Finset.sum_mul]

/-- One fixed finite packet leaves a uniformly bounded full-current remainder on future time. -/
def XiMassCriticalPrimeTailUniformFiniteRemainderBounded
    (a sigma : ℝ) : Prop :=
  ∃ S : Finset DeningerPrimePowerIndex, ∃ C : ℝ,
    ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalPrimeTailGreenCurrent a sigma u -
        xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ ≤ C

/-- The missing uniform infinite-tail estimate is exactly RH; finite source pieces are harmless. -/
theorem riemannHypothesis_iff_xiMassCriticalPrimeTailUniformFiniteRemainderBounded
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔
      XiMassCriticalPrimeTailUniformFiniteRemainderBounded a sigma := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ :=
      (riemannHypothesis_iff_xiMassCriticalPrimeTailGreenCurrentLineBound
        ha hsigma).mp hRH
    refine ⟨∅, C, fun u hu => ?_⟩
    simpa [xiMassCriticalPrimeTailGreenCurrentFinite] using hC u hu
  · rintro ⟨S, C, htail⟩
    apply (riemannHypothesis_iff_xiMassCriticalPrimeTailGreenCurrentLineBound
      ha hsigma).mpr
    let B : ℝ :=
      (∑ n ∈ S, criticalMellinAtomWeight (n : ℕ)) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|)))
    have ha0 : 0 < a := lt_trans (by norm_num) ha
    refine ⟨C + B, fun u hu => ?_⟩
    have hfinite :=
      norm_xiMassCriticalPrimeTailGreenCurrentFinite_le
        (a := a) (sigma := sigma) ha0 hsigma u S
    calc
      ‖xiMassCriticalPrimeTailGreenCurrent a sigma u‖ =
          ‖(xiMassCriticalPrimeTailGreenCurrent a sigma u -
              xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S) +
            xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ := by
              ring_nf
      _ ≤ ‖xiMassCriticalPrimeTailGreenCurrent a sigma u -
              xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ +
            ‖xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ :=
        norm_add_le _ _
      _ ≤ C + B := add_le_add (htail u hu) (by simpa only [B] using hfinite)

/-- Uniform control of the infinite prime tail is equivalent to annihilating every discrete
reflection self-intersection charge. -/
theorem xiMassCriticalPrimeTailUniformFiniteRemainderBounded_iff_reflectionCharge_zero
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    XiMassCriticalPrimeTailUniformFiniteRemainderBounded a sigma ↔
      ∀ T : ℝ, xiReflectionSelfIntersectionCharge T = 0 := by
  rw [← riemannHypothesis_iff_forall_reflectionSelfIntersectionCharge_eq_zero,
    riemannHypothesis_iff_xiMassCriticalPrimeTailUniformFiniteRemainderBounded
      ha hsigma]

/-- Under false RH every finite prime-power subtraction leaves an unbounded future-time tail. -/
theorem xiMassCriticalPrimeTailGreenRemainder_unbounded_of_not_riemannHypothesis
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hnot : ¬ RiemannHypothesis)
    (S : Finset DeningerPrimePowerIndex) (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖xiMassCriticalPrimeTailGreenCurrent a sigma u -
        xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ := by
  by_contra h
  push Not at h
  apply hnot
  exact
    (riemannHypothesis_iff_xiMassCriticalPrimeTailUniformFiniteRemainderBounded
      ha hsigma).mpr ⟨S, C, fun u hu => h u hu⟩

/-- Any nonzero discrete reflection charge forces the full mass current to escape every finite
prime-power subtraction.  This is the direct charge-to-source-tail form of the obstruction. -/
theorem xiMassCriticalPrimeTailGreenRemainder_unbounded_of_reflectionCharge_ne_zero
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    {T : ℝ} (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0)
    (S : Finset DeningerPrimePowerIndex) (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖xiMassCriticalPrimeTailGreenCurrent a sigma u -
        xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ := by
  apply xiMassCriticalPrimeTailGreenRemainder_unbounded_of_not_riemannHypothesis
    ha hsigma
  intro hRH
  exact hcharge
    (xiReflectionSelfIntersectionCharge_eq_zero_of_riemannHypothesis hRH T)

end

end RHTower
