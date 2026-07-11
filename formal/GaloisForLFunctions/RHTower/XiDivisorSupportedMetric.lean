import GaloisForLFunctions.RHTower.XiWeilHilbertCore

/-!
# Positive metrics supported on the real Xi divisor

This file builds the atomic metric class forced by the Hedenmalm theta-pair classification.
A weight is attached to every analytic-multiplicity copy of the actual Xi divisor, is nonnegative,
and is required to vanish off the real centered divisor.  The resulting polarization is Hermitian,
annihilates the completed theta transform, and symmetrizes multiplication by the centered spectral
coordinate without assuming RH.

For every actual Xi zero, the removable Hedenmalm quotient has exactly the weighted fiber mass
times `‖XiC'‖²` as its diagonal value.  Consequently, conservativity on every theta eigenfunction
forces every Xi zero to be real and simple, hence implies RH plus simplicity.  This is the complete
atomic-divisor portion of the metric-classification card; the preceding Bochner--Schwartz passage
from an arbitrary continuous translation-invariant Schwartz form to such a weight is separate
infrastructure.
-/

open Complex

namespace RHTower

noncomputable section

/-- A nonnegative multiplicity-exact Xi-divisor weight which vanishes away from real centered
spectral points. -/
structure XiRealDivisorWeight where
  weight : XiZeroCopy → NNReal
  supported_real : ∀ q, weight q ≠ 0 → ∃ t : ℝ, xiSpectralPoint q = (t : ℂ)

instance : CoeFun XiRealDivisorWeight (fun _ => XiZeroCopy → NNReal) :=
  ⟨XiRealDivisorWeight.weight⟩

/-- Any weight at a nonreal centered divisor copy is zero. -/
theorem XiRealDivisorWeight.eq_zero_of_not_real
    (c : XiRealDivisorWeight) (q : XiZeroCopy)
    (hq : ¬ ∃ t : ℝ, xiSpectralPoint q = (t : ℂ)) :
    c q = 0 := by
  by_contra hc
  exact hq (c.supported_real q hc)

/-- The positive atomic polarization carried by the real part of the actual Xi divisor. -/
def xiDivisorSupportedPolarization
    (c : XiRealDivisorWeight) (F G : ℂ → ℂ) : ℂ :=
  ∑' q : XiZeroCopy,
    ((c q : ℝ) : ℂ) * F (xiSpectralPoint q) *
      (starRingEnd ℂ) (G (xiSpectralPoint q))

/-- Every real-divisor atomic polarization is Hermitian. -/
theorem xiDivisorSupportedPolarization_conj_symm
    (c : XiRealDivisorWeight) (F G : ℂ → ℂ) :
    xiDivisorSupportedPolarization c G F =
      (starRingEnd ℂ) (xiDivisorSupportedPolarization c F G) := by
  unfold xiDivisorSupportedPolarization
  calc
    (∑' q : XiZeroCopy,
        ((c q : ℝ) : ℂ) * G (xiSpectralPoint q) *
          (starRingEnd ℂ) (F (xiSpectralPoint q))) =
        ∑' q : XiZeroCopy, (starRingEnd ℂ)
          (((c q : ℝ) : ℂ) * F (xiSpectralPoint q) *
            (starRingEnd ℂ) (G (xiSpectralPoint q))) := by
      apply tsum_congr
      intro q
      simp
      ring
    _ = (starRingEnd ℂ) (∑' q : XiZeroCopy,
        ((c q : ℝ) : ℂ) * F (xiSpectralPoint q) *
          (starRingEnd ℂ) (G (xiSpectralPoint q))) := by
      exact (Complex.conj_tsum _).symm

/-- Multiplication by the centered real spectral coordinate is formally symmetric for every
real-divisor atomic metric. -/
theorem xiDivisorSupportedPolarization_spectralMultiply
    (c : XiRealDivisorWeight) (F G : ℂ → ℂ) :
    xiDivisorSupportedPolarization c (fun z => -z * F z) G =
      xiDivisorSupportedPolarization c F (fun z => -z * G z) := by
  unfold xiDivisorSupportedPolarization
  apply tsum_congr
  intro q
  by_cases hc : c q = 0
  · simp [hc]
  · obtain ⟨t, ht⟩ := c.supported_real q hc
    rw [ht]
    simp
    ring

/-- The completed theta transform is in the left radical of every divisor-supported metric. -/
theorem xiDivisorSupportedPolarization_XiC_left
    (c : XiRealDivisorWeight) (G : ℂ → ℂ) :
    xiDivisorSupportedPolarization c XiC G = 0 := by
  unfold xiDivisorSupportedPolarization
  simp [XiC_xiSpectralPoint_eq_zero]

/-- The completed theta transform is also in the right radical. -/
theorem xiDivisorSupportedPolarization_XiC_right
    (c : XiRealDivisorWeight) (F : ℂ → ℂ) :
    xiDivisorSupportedPolarization c F XiC = 0 := by
  rw [xiDivisorSupportedPolarization_conj_symm,
    xiDivisorSupportedPolarization_XiC_left]
  simp

/-- Total weight, including analytic multiplicity copies, at one centered spectral point. -/
def xiRealDivisorMass (c : XiRealDivisorWeight) (alpha : ℂ) : ℝ :=
  ∑ q ∈ (finite_xiSpectralPoint_fiber alpha).toFinset, (c q : ℝ)

theorem xiRealDivisorMass_nonneg (c : XiRealDivisorWeight) (alpha : ℂ) :
    0 ≤ xiRealDivisorMass c alpha := by
  unfold xiRealDivisorMass
  positivity

/-- A weight supported on the real divisor has zero mass at every nonreal point. -/
theorem xiRealDivisorMass_eq_zero_of_not_real
    (c : XiRealDivisorWeight) {alpha : ℂ}
    (halpha : ¬ ∃ t : ℝ, alpha = (t : ℂ)) :
    xiRealDivisorMass c alpha = 0 := by
  unfold xiRealDivisorMass
  apply Finset.sum_eq_zero
  intro q hq
  have hqalpha : xiSpectralPoint q = alpha := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
  have hnotreal : ¬ ∃ t : ℝ, xiSpectralPoint q = (t : ℂ) := by
    rintro ⟨t, ht⟩
    exact halpha ⟨t, hqalpha.symm.trans ht⟩
  rw [c.eq_zero_of_not_real q hnotreal]
  rfl

/-- Exact weighted sampling law for every Hedenmalm theta eigenfunction. -/
theorem xiDivisorSupportedPolarization_thetaEigen_diagonal
    (c : XiRealDivisorWeight) {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiDivisorSupportedPolarization c (xiThetaEigenFourier alpha)
      (xiThetaEigenFourier alpha) =
      (((xiRealDivisorMass c alpha) * ‖deriv XiC alpha‖ ^ 2 : ℝ) : ℂ) := by
  unfold xiDivisorSupportedPolarization
  let T : Finset XiZeroCopy := (finite_xiSpectralPoint_fiber alpha).toFinset
  calc
    (∑' q : XiZeroCopy,
        ((c q : ℝ) : ℂ) * xiThetaEigenFourier alpha (xiSpectralPoint q) *
          (starRingEnd ℂ) (xiThetaEigenFourier alpha (xiSpectralPoint q))) =
        ∑ q ∈ T,
          ((c q : ℝ) : ℂ) * xiThetaEigenFourier alpha (xiSpectralPoint q) *
            (starRingEnd ℂ) (xiThetaEigenFourier alpha (xiSpectralPoint q)) := by
      apply tsum_eq_sum
      intro q hq
      have hne : xiSpectralPoint q ≠ alpha := by
        intro heq
        apply hq
        simpa only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using heq
      rw [xiThetaEigenFourier_spectralPoint_eq_zero halpha q hne]
      simp
    _ = ∑ q ∈ T, (((c q : ℝ) * ‖deriv XiC alpha‖ ^ 2 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have heq : xiSpectralPoint q = alpha := by
        simpa only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
      rw [heq, xiThetaEigenFourier_self, mul_assoc, Complex.mul_conj]
      rw [← Complex.sq_norm, norm_mul, norm_I, one_mul]
      norm_cast
    _ = (((xiRealDivisorMass c alpha) * ‖deriv XiC alpha‖ ^ 2 : ℝ) : ℂ) := by
      unfold xiRealDivisorMass
      push_cast
      rw [Finset.sum_mul]

/-- A theta eigenfunction attached to a nonreal zero is null for every positive real-divisor
metric. -/
theorem xiDivisorSupportedPolarization_thetaEigen_eq_zero_of_not_real
    (c : XiRealDivisorWeight) {alpha : ℂ} (halpha : XiC alpha = 0)
    (hnotreal : ¬ ∃ t : ℝ, alpha = (t : ℂ)) :
    xiDivisorSupportedPolarization c (xiThetaEigenFourier alpha)
      (xiThetaEigenFourier alpha) = 0 := by
  rw [xiDivisorSupportedPolarization_thetaEigen_diagonal c halpha,
    xiRealDivisorMass_eq_zero_of_not_real c hnotreal]
  simp

/-- Positivity on every actual theta eigenfunction: the exact conservativity condition in the
Hedenmalm metric card. -/
def XiThetaMetricConservative (c : XiRealDivisorWeight) : Prop :=
  ∀ {alpha : ℂ}, XiC alpha = 0 →
    0 < (xiDivisorSupportedPolarization c (xiThetaEigenFourier alpha)
      (xiThetaEigenFourier alpha)).re

/-- If every multiplicity copy has real centered spectral coordinate, then RH holds. -/
theorem riemannHypothesis_of_xiSpectralPoint_real
    (hreal : ∀ q : XiZeroCopy, ∃ t : ℝ, xiSpectralPoint q = (t : ℂ)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  let ρ : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
  obtain ⟨t, ht⟩ := hreal q
  have him := congrArg Complex.im ht
  have hre : z.re = 1 / 2 := by
    dsimp only [q, ρ, xiSpectralPoint] at him
    simp at him
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hz)) hre

/-- Conservativity of a real-divisor atomic metric forces RH and simplicity of every Xi zero. -/
theorem xiThetaMetricConservative_implies_rh_and_simple
    (c : XiRealDivisorWeight) (hcon : XiThetaMetricConservative c) :
    RiemannHypothesis ∧
      ∀ {alpha : ℂ}, XiC alpha = 0 → deriv XiC alpha ≠ 0 := by
  have hallreal : ∀ q : XiZeroCopy, ∃ t : ℝ, xiSpectralPoint q = (t : ℂ) := by
    intro q
    by_contra hnotreal
    have hpos := hcon (XiC_xiSpectralPoint_eq_zero q)
    rw [xiDivisorSupportedPolarization_thetaEigen_eq_zero_of_not_real c
      (XiC_xiSpectralPoint_eq_zero q) hnotreal] at hpos
    norm_num at hpos
  refine ⟨riemannHypothesis_of_xiSpectralPoint_real hallreal, ?_⟩
  intro alpha halpha
  have hpos := hcon halpha
  rw [xiDivisorSupportedPolarization_thetaEigen_diagonal c halpha] at hpos
  simp only [Complex.ofReal_re] at hpos
  have hmass := xiRealDivisorMass_nonneg c alpha
  intro hderiv
  rw [hderiv, norm_zero] at hpos
  norm_num at hpos

/-- Exact atomic classification of conservativity: every zero fiber must carry positive mass and
every Xi zero must be simple. -/
theorem xiThetaMetricConservative_iff_mass_pos_and_simple
    (c : XiRealDivisorWeight) :
    XiThetaMetricConservative c ↔
      ∀ {alpha : ℂ}, XiC alpha = 0 →
        0 < xiRealDivisorMass c alpha ∧ deriv XiC alpha ≠ 0 := by
  constructor
  · intro hcon alpha halpha
    have hpos := hcon halpha
    rw [xiDivisorSupportedPolarization_thetaEigen_diagonal c halpha] at hpos
    simp only [Complex.ofReal_re] at hpos
    have hmass := xiRealDivisorMass_nonneg c alpha
    constructor
    · by_contra hmasspos
      have hmasszero : xiRealDivisorMass c alpha = 0 := le_antisymm
        (le_of_not_gt hmasspos) hmass
      rw [hmasszero] at hpos
      norm_num at hpos
    · intro hderiv
      rw [hderiv, norm_zero] at hpos
      norm_num at hpos
  · intro h alpha halpha
    obtain ⟨hmass, hderiv⟩ := h halpha
    rw [xiDivisorSupportedPolarization_thetaEigen_diagonal c halpha]
    simp only [Complex.ofReal_re]
    exact mul_pos hmass (sq_pos_of_pos (norm_pos_iff.mpr hderiv))

end

end RHTower
