import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaSlepianDecomposition
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilMixedSourceForm
import GaloisForLFunctions.RHTower.SoninAlternatingBlockStrict

/-!
# Strict Gamma--Slepian spectrum and literal ground-source matrix

The exact Gamma weight is strictly larger than one away from the null singleton at frequency
zero.  Equality in the weighted-to-physical contraction therefore forces the source vector to
vanish.  Compactness upgrades this pointwise strictness to a genuine finite-aperture spectral
gap: the Gamma--Slepian Gram has norm strictly below one, and every nonzero eigenvalue is real and
lies in the open interval `(0,1)`.

The second half removes the bounded-remainder black box from the whole-ground modal equation.
It splits the compressed remainder into its scalar Gamma, rank-two polar, and finite von Mangoldt
translation blocks and writes every ground-mode equation in those literal source coordinates.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped ENNReal InnerProduct BigOperators

noncomputable section

namespace RHTower

theorem one_lt_ccmArchimedeanFormWeight_of_ne_zero {xi : ℝ} (hxi : xi ≠ 0) :
    1 < ccmArchimedeanFormWeight xi := by
  have harg : 2 * Real.pi * |xi| ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (abs_ne_zero.mpr hxi)
  have hgamma := gammaHardyPhaseRate_zero_lt harg
  unfold ccmArchimedeanFormWeight
  linarith

private theorem integrable_ccmArchimedeanWeightedPhysicalDensity
    (f : CCMArchimedeanFourierL2) :
    Integrable (fun xi : ℝ => ccmArchimedeanFormWeight xi *
      ‖(ccmArchimedeanWeightedToL2 f : ℝ → ℂ) xi‖ ^ 2) := by
  have hfint : Integrable (fun xi : ℝ => ‖(f : ℝ → ℂ) xi‖ ^ 2)
      ccmArchimedeanFormMeasure :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  have hw : Integrable
      (fun xi : ℝ => Real.toNNReal (ccmArchimedeanFormWeight xi) •
        ‖(f : ℝ → ℂ) xi‖ ^ 2) volume :=
    (integrable_withDensity_iff_integrable_smul
      measurable_ccmArchimedeanFormWeightNNReal).mp hfint
  refine hw.congr ?_
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn f] with xi hxi
  rw [hxi, NNReal.smul_def, smul_eq_mul,
    coe_ccmArchimedeanFormWeightNNReal]

private theorem integral_ccmArchimedeanWeightedPhysicalDensity_eq_norm_sq
    (f : CCMArchimedeanFourierL2) :
    (∫ xi : ℝ, ccmArchimedeanFormWeight xi *
      ‖(ccmArchimedeanWeightedToL2 f : ℝ → ℂ) xi‖ ^ 2) = ‖f‖ ^ 2 := by
  rw [norm_sq_ccmArchimedeanFourierL2]
  apply integral_congr_ae
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn f] with xi hxi
  rw [hxi]

/-- Forgetting the exact Gamma weight is contractive. -/
theorem norm_ccmArchimedeanWeightedToL2_le (f : CCMArchimedeanFourierL2) :
    ‖ccmArchimedeanWeightedToL2 f‖ ≤ ‖f‖ := by
  let g := ccmArchimedeanWeightedToL2 f
  have hplain : Integrable (fun xi : ℝ => ‖(g : ℝ → ℂ) xi‖ ^ 2) :=
    (Lp.memLp g).integrable_norm_pow (by norm_num)
  have hweighted : Integrable
      (fun xi : ℝ => ccmArchimedeanFormWeight xi * ‖(g : ℝ → ℂ) xi‖ ^ 2) :=
    integrable_ccmArchimedeanWeightedPhysicalDensity f
  have hpoint : ∀ xi : ℝ,
      ‖(g : ℝ → ℂ) xi‖ ^ 2 ≤
        ccmArchimedeanFormWeight xi * ‖(g : ℝ → ℂ) xi‖ ^ 2 := by
    intro xi
    nlinarith [one_le_ccmArchimedeanFormWeight xi,
      sq_nonneg ‖(g : ℝ → ℂ) xi‖]
  have hint := integral_mono hplain hweighted hpoint
  have hsquares : ‖g‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    exact hint.trans_eq
      (integral_ccmArchimedeanWeightedPhysicalDensity_eq_norm_sq f)
  nlinarith [norm_nonneg g, norm_nonneg f]

/-- The Gamma-weight contraction has no nonzero equality vector. -/
theorem eq_zero_of_norm_ccmArchimedeanWeightedToL2_eq
    (f : CCMArchimedeanFourierL2)
    (hnorm : ‖ccmArchimedeanWeightedToL2 f‖ = ‖f‖) : f = 0 := by
  let g := ccmArchimedeanWeightedToL2 f
  have hplain : Integrable (fun xi : ℝ => ‖(g : ℝ → ℂ) xi‖ ^ 2) :=
    (Lp.memLp g).integrable_norm_pow (by norm_num)
  have hweighted : Integrable
      (fun xi : ℝ => ccmArchimedeanFormWeight xi * ‖(g : ℝ → ℂ) xi‖ ^ 2) :=
    integrable_ccmArchimedeanWeightedPhysicalDensity f
  let defect := fun xi : ℝ =>
    (ccmArchimedeanFormWeight xi - 1) * ‖(g : ℝ → ℂ) xi‖ ^ 2
  have hdefInt : Integrable defect := by
    have heq : defect = fun xi : ℝ =>
        ccmArchimedeanFormWeight xi * ‖(g : ℝ → ℂ) xi‖ ^ 2 -
          ‖(g : ℝ → ℂ) xi‖ ^ 2 := by
      funext xi
      dsimp [defect]
      ring
    rw [heq]
    exact hweighted.sub hplain
  have hdefNonneg : ∀ xi, 0 ≤ defect xi := by
    intro xi
    exact mul_nonneg (sub_nonneg.mpr (one_le_ccmArchimedeanFormWeight xi))
      (sq_nonneg _)
  have hdefIntegral : (∫ xi : ℝ, defect xi) = 0 := by
    have heq : defect = fun xi : ℝ =>
        ccmArchimedeanFormWeight xi * ‖(g : ℝ → ℂ) xi‖ ^ 2 -
          ‖(g : ℝ → ℂ) xi‖ ^ 2 := by
      funext xi
      dsimp [defect]
      ring
    rw [heq, integral_sub hweighted hplain,
      integral_ccmArchimedeanWeightedPhysicalDensity_eq_norm_sq,
      ← norm_sq_eq_integral g]
    dsimp [g] at hnorm ⊢
    rw [hnorm]
    ring
  have hdefZero : defect =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hdefNonneg hdefInt).mp hdefIntegral
  have hne : ∀ᵐ xi : ℝ, xi ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hgZero : (g : ℝ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hdefZero, hne] with xi hzero hxi
    have hw : 0 < ccmArchimedeanFormWeight xi - 1 :=
      sub_pos.mpr (one_lt_ccmArchimedeanFormWeight_of_ne_zero hxi)
    have hs : ‖(g : ℝ → ℂ) xi‖ ^ 2 = 0 := by
      dsimp [defect] at hzero
      nlinarith [sq_nonneg ‖(g : ℝ → ℂ) xi‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  apply ccmArchimedeanWeightedToL2_injective
  change g = ccmArchimedeanWeightedToL2 0
  rw [map_zero]
  apply Lp.ext
  filter_upwards [hgZero] with xi hxi
  simpa using hxi

theorem norm_ccmArchimedeanFormToAperture_le
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormToAperture a u‖ ≤ ‖u‖ := by
  rw [norm_ccmArchimedeanFormToAperture]
  exact norm_ccmArchimedeanWeightedToL2_le u.1

theorem eq_zero_of_norm_ccmArchimedeanFormToAperture_eq
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hnorm : ‖ccmArchimedeanFormToAperture a u‖ = ‖u‖) : u = 0 := by
  rw [norm_ccmArchimedeanFormToAperture] at hnorm
  exact Subtype.ext (eq_zero_of_norm_ccmArchimedeanWeightedToL2_eq u.1 hnorm)

theorem norm_ccmArchimedeanFormToAperture_le_one
    (a : SuzukiPositiveAperture) :
    ‖ccmArchimedeanFormToAperture a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa using norm_ccmArchimedeanFormToAperture_le a u

theorem norm_ccmArchimedeanGammaSlepianGram_le_one
    (a : SuzukiPositiveAperture) :
    ‖ccmArchimedeanGammaSlepianGram a‖ ≤ 1 := by
  rw [ccmArchimedeanGammaSlepianGram,
    ContinuousLinearMap.norm_adjoint_comp_self]
  nlinarith [norm_ccmArchimedeanFormToAperture_le_one a,
    norm_nonneg (ccmArchimedeanFormToAperture a)]

theorem not_hasEigenvalue_one_ccmArchimedeanGammaSlepianGram
    (a : SuzukiPositiveAperture) :
    ¬ Module.End.HasEigenvalue
      (ccmArchimedeanGammaSlepianGram a :
        Module.End ℂ (CCMArchimedeanFormDomain a)) 1 := by
  intro h
  obtain ⟨u, hu, hune⟩ := h.exists_hasEigenvector
  simp only [Module.End.mem_genEigenspace_one, one_smul] at hu
  change ccmArchimedeanGammaSlepianGram a u = u at hu
  have hsq : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 = ‖u‖ ^ 2 := by
    have henergy := ccmArchimedeanGammaSlepianGram_reApplyInnerSelf a u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at henergy
    change (inner ℂ (ccmArchimedeanGammaSlepianGram a u) u).re = _ at henergy
    rw [hu] at henergy
    have hself : (inner ℂ u u).re = ‖u‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]
      norm_cast
    rw [hself] at henergy
    exact henergy.symm
  have hnorm : ‖ccmArchimedeanFormToAperture a u‖ = ‖u‖ := by
    nlinarith [norm_nonneg (ccmArchimedeanFormToAperture a u), norm_nonneg u]
  exact hune (eq_zero_of_norm_ccmArchimedeanFormToAperture_eq a u hnorm)

/-- **Finite-aperture Gamma uncertainty gap.**  The exact Gamma--Slepian Gram is a strict
contraction at every positive aperture. -/
theorem norm_ccmArchimedeanGammaSlepianGram_lt_one
    (a : SuzukiPositiveAperture) :
    ‖ccmArchimedeanGammaSlepianGram a‖ < 1 := by
  have hJne : ccmArchimedeanFormToAperture a ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := exists_ne (0 : suzukiApertureHilbert a)
    apply hx
    apply (denseRange_ccmArchimedeanFormToAperture a).eq_zero_of_inner_right (𝕜 := ℂ)
    intro u
    rw [hzero]
    simp
  have hex : ∃ u : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a u ≠ 0 := by
    by_contra h
    push Not at h
    apply hJne
    apply ContinuousLinearMap.ext
    intro u
    exact h u
  obtain ⟨u, hu⟩ := hex
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hu
    exact hu rfl
  letI : Nontrivial (CCMArchimedeanFormDomain a) := nontrivial_of_ne u 0 hu0
  apply norm_lt_one_of_compact_of_symmetric_of_nonnegative_of_not_eigenvalue_one
  · exact norm_ccmArchimedeanGammaSlepianGram_le_one a
  · exact isCompactOperator_ccmArchimedeanGammaSlepianGram a
  · exact isSymmetric_ccmArchimedeanGammaSlepianGram a
  · intro v
    have hpos := (ccmArchimedeanGammaSlepianGram_isPositive a).2 v
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at hpos
    have hs : (inner ℂ v (ccmArchimedeanGammaSlepianGram a v)).re =
        (inner ℂ (ccmArchimedeanGammaSlepianGram a v) v).re := by
      simpa using (inner_re_symm (𝕜 := ℂ) v
        (ccmArchimedeanGammaSlepianGram a v))
    rw [hs]
    exact hpos
  · exact not_hasEigenvalue_one_ccmArchimedeanGammaSlepianGram a

/-- A nonzero exact Gamma--Slepian mode, with eigenvalue and eigenvector kept dependent. -/
structure CCMGammaSlepianMode (a : SuzukiPositiveAperture) where
  eigenvalue : ℂ
  vector : ccmGammaSlepianEigenspace a eigenvalue
  ne_zero : (vector : CCMArchimedeanFormDomain a) ≠ 0

private theorem ccmGammaSlepian_eigenvalue_range_of_ne
    (a : SuzukiPositiveAperture) (mu : ℂ)
    (w : ccmGammaSlepianEigenspace a mu)
    (hw : (w : CCMArchimedeanFormDomain a) ≠ 0) :
    ((mu.re : ℝ) : ℂ) = mu ∧ 0 < mu.re ∧ ‖mu‖ < 1 := by
  let G := ccmArchimedeanGammaSlepianGram a
  have heig : G (w : CCMArchimedeanFormDomain a) = mu • w :=
    mem_ccmGammaSlepianEigenspace_iff.mp w.property
  have hhas : Module.End.HasEigenvalue
      (G : Module.End ℂ (CCMArchimedeanFormDomain a)) mu := by
    rw [Module.End.hasEigenvalue_iff]
    intro hbot
    have hmem : (w : CCMArchimedeanFormDomain a) ∈
        Module.End.eigenspace
          (G : Module.End ℂ (CCMArchimedeanFormDomain a)) mu :=
      Module.End.mem_eigenspace_iff.mpr heig
    rw [hbot] at hmem
    exact hw hmem
  have hreal : ((mu.re : ℝ) : ℂ) = mu :=
    RCLike.conj_eq_iff_re.mp
      ((isSymmetric_ccmArchimedeanGammaSlepianGram a).conj_eigenvalue_eq_self hhas)
  have hmune : mu ≠ 0 := by
    intro hmu
    subst mu
    simp only [zero_smul] at heig
    have hwzero := ccmArchimedeanGammaSlepianGram_injective a
      (show G (w : CCMArchimedeanFormDomain a) = G 0 by simpa [G] using heig)
    exact hw hwzero
  have hreig : Module.End.HasEigenvalue
      (G : Module.End ℂ (CCMArchimedeanFormDomain a)) mu.re := by
    simpa [hreal] using hhas
  have hnonneg : 0 ≤ mu.re := by
    apply eigenvalue_nonneg_of_nonneg hreig
    intro v
    have hpos := (ccmArchimedeanGammaSlepianGram_isPositive a).2 v
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at hpos
    change 0 ≤ (inner ℂ (G v) v).re at hpos
    change 0 ≤ (inner ℂ v (G v)).re
    have hs : (inner ℂ v (G v)).re = (inner ℂ (G v) v).re := by
      simpa using (inner_re_symm (𝕜 := ℂ) v (G v))
    rw [hs]
    exact hpos
  have hpos : 0 < mu.re := lt_of_le_of_ne hnonneg (by
    intro hz
    apply hmune
    rw [← hreal, ← hz]
    simp)
  have hnormApply := G.le_opNorm (w : CCMArchimedeanFormDomain a)
  rw [heig, norm_smul] at hnormApply
  have hGlt : ‖G‖ < 1 := norm_ccmArchimedeanGammaSlepianGram_lt_one a
  have hwpos : 0 < ‖(w : CCMArchimedeanFormDomain a)‖ := norm_pos_iff.mpr hw
  have hmul : ‖mu‖ * ‖(w : CCMArchimedeanFormDomain a)‖ <
      1 * ‖(w : CCMArchimedeanFormDomain a)‖ :=
    hnormApply.trans_lt (mul_lt_mul_of_pos_right hGlt hwpos)
  refine ⟨hreal, hpos, ?_⟩
  nlinarith

/-- Every actual nonzero Gamma--Slepian mode has a strictly positive real eigenvalue below one. -/
theorem CCMGammaSlepianMode.eigenvalue_range
    {a : SuzukiPositiveAperture} (M : CCMGammaSlepianMode a) :
    (((M.eigenvalue.re : ℝ) : ℂ) = M.eigenvalue) ∧
      0 < M.eigenvalue.re ∧ ‖M.eigenvalue‖ < 1 :=
  ccmGammaSlepian_eigenvalue_range_of_ne a M.eigenvalue M.vector M.ne_zero

/-! ## Literal compressed prime--polar matrix -/

/-- Rank-two polar block compressed to the exact Gamma form domain. -/
def ccmRestrictedWeilFormPolarCompression (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  (ccmArchimedeanFormToAperture a).adjoint ∘L
    ccmPolarOperator a ∘L ccmArchimedeanFormToAperture a

/-- Finite von Mangoldt translation block compressed to the exact Gamma form domain. -/
def ccmRestrictedWeilFormPrimeCompression (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  (ccmArchimedeanFormToAperture a).adjoint ∘L
    ccmFinitePrimeOperator a ∘L ccmArchimedeanFormToAperture a

/-- Exact scalar--polar--prime splitting of the compressed source remainder. -/
theorem ccmRestrictedWeilFormRemainder_eq_scalarGamma_add_polar_sub_prime
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilFormRemainder a =
      ccmArchimedeanRemainderScalar • ccmArchimedeanGammaSlepianGram a +
        ccmRestrictedWeilFormPolarCompression a -
          ccmRestrictedWeilFormPrimeCompression a := by
  apply ContinuousLinearMap.ext
  intro u
  change (ccmArchimedeanFormToAperture a).adjoint
      (ccmArchimedeanRemainderScalar • ccmArchimedeanFormToAperture a u +
        ccmPolarOperator a (ccmArchimedeanFormToAperture a u) -
        ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u)) = _
  rw [map_sub, map_add, map_smul]
  rfl

theorem inner_ccmRestrictedWeilFormPolarCompression
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmRestrictedWeilFormPolarCompression a u) v =
      star (inner ℂ (ccmPolarApertureVector a (-1 / 2))
          (ccmArchimedeanFormToAperture a u)) *
        inner ℂ (ccmPolarApertureVector a (1 / 2))
          (ccmArchimedeanFormToAperture a v) +
      star (inner ℂ (ccmPolarApertureVector a (1 / 2))
          (ccmArchimedeanFormToAperture a u)) *
        inner ℂ (ccmPolarApertureVector a (-1 / 2))
          (ccmArchimedeanFormToAperture a v) := by
  change inner ℂ ((ccmArchimedeanFormToAperture a).adjoint
    (ccmPolarOperator a (ccmArchimedeanFormToAperture a u))) v = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact inner_ccmPolarOperator_mixed a _ _

theorem inner_ccmRestrictedWeilFormPrimeCompression
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmRestrictedWeilFormPrimeCompression a u) v =
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (((1 / Real.sqrt n : ℝ) : ℂ) *
            (inner ℂ (logTranslationCLM (Real.log n)
                (ccmArchimedeanFormToAperture a u).1)
              (ccmArchimedeanFormToAperture a v).1 +
             inner ℂ (logTranslationCLM (-Real.log n)
                (ccmArchimedeanFormToAperture a u).1)
              (ccmArchimedeanFormToAperture a v).1)) := by
  change inner ℂ ((ccmArchimedeanFormToAperture a).adjoint
    (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u))) v = _
  rw [ContinuousLinearMap.adjoint_inner_left,
    inner_ccmFinitePrimeOperator_mixed]
  apply Finset.sum_congr rfl
  intro n hn
  rw [inner_ccmPrimeTransportOperator]

/-- Scalar-shifted Gamma--Slepian ground equation with separate compressed polar and prime
blocks. -/
theorem ccmRestrictedWeilCanonicalGround_gammaSlepian_shifted_mode_balance
    (a : SuzukiPositiveAperture) (mu : ℂ)
    (w : ccmGammaSlepianEigenspace a mu) :
    ((1 : ℂ) -
          ((ccmRestrictedWeilGroundEnergy a : ℂ) -
            ccmArchimedeanRemainderScalar) * mu) *
        inner ℂ (ccmRestrictedWeilCanonicalGroundFormLift a)
          (w : CCMArchimedeanFormDomain a) +
      inner ℂ
        (ccmRestrictedWeilFormPolarCompression a
          (ccmRestrictedWeilCanonicalGroundFormLift a)) w -
      inner ℂ
        (ccmRestrictedWeilFormPrimeCompression a
          (ccmRestrictedWeilCanonicalGroundFormLift a)) w = 0 := by
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  let G := ccmArchimedeanGammaSlepianGram a
  let E : ℂ := ccmRestrictedWeilGroundEnergy a
  let c : ℂ := ccmArchimedeanRemainderScalar
  have h := ccmRestrictedWeilCanonicalGround_gammaSlepian_mode_balance a mu w
  rw [ccmRestrictedWeilFormRemainder_eq_scalarGamma_add_polar_sub_prime] at h
  have heig : G (w : CCMArchimedeanFormDomain a) = mu • w :=
    mem_ccmGammaSlepianEigenspace_iff.mp w.property
  have hsym := isSymmetric_ccmArchimedeanGammaSlepianGram a u
    (w : CCMArchimedeanFormDomain a)
  change inner ℂ (G u) w = inner ℂ u (G w) at hsym
  rw [heig, inner_smul_right u (w : CCMArchimedeanFormDomain a) mu] at hsym
  change ((1 : ℂ) - E * mu) * inner ℂ u w +
    inner ℂ ((c • G + ccmRestrictedWeilFormPolarCompression a -
      ccmRestrictedWeilFormPrimeCompression a) u) w = 0 at h
  simp only [sub_apply, add_apply, smul_apply, inner_sub_left,
    inner_add_left] at h
  rw [inner_smul_left (G u) w c] at h
  change ((1 : ℂ) - E * mu) * inner ℂ u w +
    (star c * inner ℂ (G u) w +
      inner ℂ (ccmRestrictedWeilFormPolarCompression a u) w -
      inner ℂ (ccmRestrictedWeilFormPrimeCompression a u) w) = 0 at h
  have hc : star c = c := by
    dsimp [c]
    simpa only [starRingEnd_apply] using star_ccmArchimedeanRemainderScalar
  rw [hc, hsym] at h
  change ((1 : ℂ) - (E - c) * mu) * inner ℂ u w +
      inner ℂ (ccmRestrictedWeilFormPolarCompression a u) w -
        inner ℂ (ccmRestrictedWeilFormPrimeCompression a u) w = 0
  linear_combination h

/-- **Literal all-mode source equation.**  Every actual nonzero Gamma--Slepian mode of the true
restricted-Weil ground satisfies the scalar-shifted equation with the two polar evaluations and
every finite von Mangoldt translation matrix coefficient displayed explicitly. -/
theorem CCMGammaSlepianMode.canonicalGround_literal_primePolar_balance
    {a : SuzukiPositiveAperture} (M : CCMGammaSlepianMode a) :
    ((1 : ℂ) -
          ((ccmRestrictedWeilGroundEnergy a : ℂ) -
            ccmArchimedeanRemainderScalar) * M.eigenvalue) *
        inner ℂ (ccmRestrictedWeilCanonicalGroundFormLift a)
          (M.vector : CCMArchimedeanFormDomain a) +
      (star (inner ℂ (ccmPolarApertureVector a (-1 / 2))
          (ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundFormLift a))) *
        inner ℂ (ccmPolarApertureVector a (1 / 2))
          (ccmArchimedeanFormToAperture a M.vector) +
       star (inner ℂ (ccmPolarApertureVector a (1 / 2))
          (ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundFormLift a))) *
        inner ℂ (ccmPolarApertureVector a (-1 / 2))
          (ccmArchimedeanFormToAperture a M.vector)) -
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (((1 / Real.sqrt n : ℝ) : ℂ) *
            (inner ℂ (logTranslationCLM (Real.log n)
                (ccmArchimedeanFormToAperture a
                  (ccmRestrictedWeilCanonicalGroundFormLift a)).1)
              (ccmArchimedeanFormToAperture a M.vector).1 +
             inner ℂ (logTranslationCLM (-Real.log n)
                (ccmArchimedeanFormToAperture a
                  (ccmRestrictedWeilCanonicalGroundFormLift a)).1)
              (ccmArchimedeanFormToAperture a M.vector).1)) = 0 := by
  rw [← inner_ccmRestrictedWeilFormPolarCompression,
    ← inner_ccmRestrictedWeilFormPrimeCompression]
  exact ccmRestrictedWeilCanonicalGround_gammaSlepian_shifted_mode_balance
    a M.eigenvalue M.vector

end RHTower
