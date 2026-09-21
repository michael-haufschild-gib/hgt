import GaloisForLFunctions.RHTower.CCMRestrictedWeilCanonicalGroundRemainderExpansion
import GaloisForLFunctions.RHTower.WeilPrimeMeasureRigidityFinite

/-!
# Numerical-range frontier for the canonical CCM ground remainder

The exact canonical ground equation is

`E · G u - D u = u`,

where `G = J†J` is the positive Gamma--Slepian Gram and `D` is the literal
compressed scalar--polar--prime remainder.  Taking its numerical range on the
ground itself gives the exact identity

`Re ⟪D u,u⟫ = E ‖J u‖² - ‖u‖²`.

Thus the sharp lower numerical-range wall `Re ⟪D u,u⟫ ≥ -‖u‖²` is equivalent
to nonnegative restricted-Weil ground energy.  By canonical-head convergence,
its epsilon-relaxation on the actual finite Gamma--Slepian heads is equivalent
to RH.  This removes the unnecessary norm-contraction target: the remaining
source-faithful hard problem is one signed quadratic lower bound for
`scalar + polar - prime`, with arbitrarily small cofinal slack.

No positivity, RH, spectral, or numerical premise is used in the identities or
in the equivalence below.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- The numerical range of the compressed remainder is exactly the numerical range of the
literal physical scalar--polar--prime remainder after the aperture embedding. -/
theorem ccmRestrictedWeilFormRemainder_re_inner_eq_physical
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (inner ℂ (ccmRestrictedWeilFormRemainder a u) u).re =
      (inner ℂ
        (ccmRestrictedWeilBoundedRemainder a
          (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  unfold ccmRestrictedWeilFormRemainder
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- The compressed remainder retains the literal scalar, polar, and prime contributions
separately in its numerical range. Thus a lower-wall proof for this operator has to control
the completed signed source rather than a hidden surrogate. -/
theorem ccmRestrictedWeilFormRemainder_re_inner_eq_scalar_polar_sub_prime
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (inner ℂ (ccmRestrictedWeilFormRemainder a u) u).re =
      (2 * gammaHardyPhaseRate 0 - 1) *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
        (inner ℂ (ccmPolarOperator a (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re -
        (inner ℂ (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
  rw [ccmRestrictedWeilFormRemainder_re_inner_eq_physical,
    inner_ccmRestrictedWeilBoundedRemainder]
  have hscalar :
      (ccmArchimedeanRemainderScalar *
        inner ℂ (ccmArchimedeanFormToAperture a u)
          (ccmArchimedeanFormToAperture a u)).re =
        (2 * gammaHardyPhaseRate 0 - 1) *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    have hself :
        inner ℂ (ccmArchimedeanFormToAperture a u)
          (ccmArchimedeanFormToAperture a u) =
          (‖ccmArchimedeanFormToAperture a u‖ : ℂ) ^ 2 :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmArchimedeanFormToAperture a u)
    have hnorm :
        ((‖ccmArchimedeanFormToAperture a u‖ : ℂ) ^ 2).re =
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
      rw [← Complex.ofReal_pow]
      exact Complex.ofReal_re _
    rw [hself]
    unfold ccmArchimedeanRemainderScalar
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hnorm]
    ring
  rw [Complex.sub_re, Complex.add_re, hscalar]

/-- Exact signed numerical-range identity on the canonical ground. -/
theorem ccmRestrictedWeilCanonicalGround_remainder_re_inner_eq
    (a : SuzukiPositiveAperture) :
    (inner ℂ
      (ccmRestrictedWeilFormRemainder a
        (ccmRestrictedWeilCanonicalGroundFormLift a))
      (ccmRestrictedWeilCanonicalGroundFormLift a)).re =
      ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a
          (ccmRestrictedWeilCanonicalGroundFormLift a)‖ ^ 2 -
        ‖ccmRestrictedWeilCanonicalGroundFormLift a‖ ^ 2 := by
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  let G := ccmArchimedeanGammaSlepianGram a
  let D := ccmRestrictedWeilFormRemainder a
  let E : ℝ := ccmRestrictedWeilGroundEnergy a
  have hfixed := ccmRestrictedWeilCanonicalGroundFormLift_birmanSchwinger_fixed a
  rw [ccmRestrictedWeilFormBirmanSchwinger_eq_gammaSlepian_sub_remainder] at hfixed
  change (E : ℂ) • G u - D u = u at hfixed
  have hD : D u = (E : ℂ) • G u - u := by
    rw [eq_sub_iff_add_eq]
    rw [sub_eq_iff_eq_add] at hfixed
    simpa [add_comm] using hfixed.symm
  have henergy := ccmArchimedeanGammaSlepianGram_reApplyInnerSelf a u
  rw [ContinuousLinearMap.reApplyInnerSelf_apply] at henergy
  change (inner ℂ (G u) u).re =
    ‖ccmArchimedeanFormToAperture a u‖ ^ 2 at henergy
  have hreal : (inner ℂ ((E : ℂ) • G u) u).re =
      E * (inner ℂ (G u) u).re := by
    simp [Complex.mul_re]
  change (inner ℂ (D u) u).re = E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 - ‖u‖ ^ 2
  rw [hD, inner_sub_left, Complex.sub_re, hreal, henergy,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- On the exact canonical ground, the sharp numerical lower wall is equivalent to nonnegative
ground energy. -/
theorem ccmRestrictedWeilCanonicalGround_remainder_numericalLower_iff_groundEnergy_nonneg
    (a : SuzukiPositiveAperture) :
    -‖ccmRestrictedWeilCanonicalGroundFormLift a‖ ^ 2 ≤
      (inner ℂ
        (ccmRestrictedWeilFormRemainder a
          (ccmRestrictedWeilCanonicalGroundFormLift a))
        (ccmRestrictedWeilCanonicalGroundFormLift a)).re ↔
      0 ≤ ccmRestrictedWeilGroundEnergy a := by
  rw [ccmRestrictedWeilCanonicalGround_remainder_re_inner_eq]
  have hu : ccmRestrictedWeilCanonicalGroundFormLift a ≠ 0 := by
    intro hu
    have he := ccmRestrictedWeilCanonicalGroundFormLift_embedding a
    rw [hu, map_zero] at he
    exact ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a he.symm
  have hphysical : 0 < ‖ccmArchimedeanFormToAperture a
      (ccmRestrictedWeilCanonicalGroundFormLift a)‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz
    apply hu
    exact ccmArchimedeanFormToAperture_injective a (by simpa using hz)
  constructor
  · intro h
    by_contra hE
    have hneg : ccmRestrictedWeilGroundEnergy a < 0 := lt_of_not_ge hE
    have hmul : ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a
          (ccmRestrictedWeilCanonicalGroundFormLift a)‖ ^ 2 < 0 :=
      mul_neg_of_neg_of_pos hneg hphysical
    linarith
  · intro hE
    have hmul : 0 ≤ ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a
          (ccmRestrictedWeilCanonicalGroundFormLift a)‖ ^ 2 :=
      mul_nonneg hE hphysical.le
    linarith

/-- Cofinal epsilon-numerical nonexpansion of the literal compressed prime--polar remainder.
The positive slack is a subtype, so this condition has no side hypothesis. -/
def CCMRestrictedWeilCanonicalGroundHeadRemainderNumericalLowerBound : Prop :=
  ∀ (a : SuzukiPositiveAperture) (epsilon : {x : ℝ // 0 < x}),
    ∀ᶠ n in atTop,
      -‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 - epsilon.1 ≤
        (inner ℂ
          (ccmRestrictedWeilFormRemainder a
            (ccmRestrictedWeilCanonicalGroundHead a n))
          (ccmRestrictedWeilCanonicalGroundHead a n)).re

/-- **Sharp canonical numerical-range criterion.** RH is equivalent to arbitrarily small
cofinal lower numerical-range slack for the actual finite heads and the intact compressed
scalar--polar--prime remainder. -/
theorem ccmRestrictedWeilCanonicalGroundHead_remainderNumericalLowerBound_iff_riemannHypothesis :
    CCMRestrictedWeilCanonicalGroundHeadRemainderNumericalLowerBound ↔ RiemannHypothesis := by
  let Q : ∀ a : SuzukiPositiveAperture, CCMArchimedeanFormDomain a → ℝ :=
    fun a u => (inner ℂ (ccmRestrictedWeilFormRemainder a u) u).re + ‖u‖ ^ 2
  have hcont : ∀ a : SuzukiPositiveAperture, Continuous (Q a) := by
    intro a
    dsimp only [Q]
    exact (Complex.continuous_re.comp
      ((ccmRestrictedWeilFormRemainder a).continuous.inner continuous_id)).add
        (continuous_norm.pow 2)
  constructor
  · intro h
    by_contra hnot
    obtain ⟨a, hE⟩ := exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hnot
    let u := ccmRestrictedWeilCanonicalGroundFormLift a
    let M := ‖ccmArchimedeanFormToAperture a u‖ ^ 2
    let q := ccmRestrictedWeilGroundEnergy a * M
    have hu : u ≠ 0 := by
      intro hu
      have he := ccmRestrictedWeilCanonicalGroundFormLift_embedding a
      rw [show ccmRestrictedWeilCanonicalGroundFormLift a = 0 by simpa [u] using hu,
        map_zero] at he
      exact ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a he.symm
    have hM : 0 < M := by
      dsimp only [M]
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro hz
      apply hu
      exact ccmArchimedeanFormToAperture_injective a (by simpa [u] using hz)
    have hq : q < 0 := by
      dsimp only [q]
      exact mul_neg_of_neg_of_pos hE hM
    let epsilon : {x : ℝ // 0 < x} := ⟨-q / 2, by linarith⟩
    have hlimit : Q a u = q := by
      dsimp only [Q, q, M, u]
      rw [ccmRestrictedWeilCanonicalGround_remainder_re_inner_eq]
      ring
    have hQ : Tendsto (fun n : ℕ => Q a (ccmRestrictedWeilCanonicalGroundHead a n))
        atTop (nhds q) := by
      have hhead := tendsto_ccmRestrictedWeilCanonicalGroundHead a
      have hq' := (hcont a).tendsto u
      rw [hlimit] at hq'
      exact hq'.comp hhead
    have hlt : ∀ᶠ n in atTop,
        Q a (ccmRestrictedWeilCanonicalGroundHead a n) < -epsilon.1 :=
      hQ.eventually (Iio_mem_nhds (by dsimp only [epsilon]; linarith))
    have hbound := h a epsilon
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlt.and hbound)
    have hpair := hN N le_rfl
    dsimp only [Q] at hpair
    linarith [hpair.1, hpair.2]
  · intro hRH a epsilon
    let u := ccmRestrictedWeilCanonicalGroundFormLift a
    have hE : 0 ≤ ccmRestrictedWeilGroundEnergy a :=
      WeilDeletion.ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis hRH a
    have hbase : 0 ≤ Q a u := by
      dsimp only [Q, u]
      rw [ccmRestrictedWeilCanonicalGround_remainder_re_inner_eq]
      have hM : 0 ≤ ‖ccmArchimedeanFormToAperture a
          (ccmRestrictedWeilCanonicalGroundFormLift a)‖ ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hE hM]
    have hQ : Tendsto (fun n : ℕ => Q a (ccmRestrictedWeilCanonicalGroundHead a n))
        atTop (nhds (Q a u)) :=
      ((hcont a).tendsto u).comp (tendsto_ccmRestrictedWeilCanonicalGroundHead a)
    filter_upwards [hQ.eventually
      (Ioi_mem_nhds (by have := epsilon.property; linarith : -epsilon.1 < Q a u))]
      with n hn
    dsimp only [Q] at hn ⊢
    linarith

end RHTower
