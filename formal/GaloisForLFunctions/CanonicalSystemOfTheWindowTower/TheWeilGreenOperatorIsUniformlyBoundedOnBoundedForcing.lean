import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheCompletedWeightedFormHasBoundedExtremals
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowBoundIsExplicit
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilFormIsCompleteBeforeContact

/-!
# The Green operator of the Weil form is uniformly bounded on `L^∞`

Before contact the Weil form is a Hilbert norm, so every `g ∈ L²` of the window has a Riesz vector `u = G_a g`:
`Q_a(u, x) = ⟨g, x⟩`. Writing the equation in logarithmic form, its forcing is `g` plus a constant plus finitely many
translates of `u`. The explicit window bound then gives:

**Theorem** (`exists_uniform_source_bound`). On a compact precontact interval there is one constant `A` such that
`|g| ≤ 1` implies `‖G_a g‖₁ ≤ A`, `‖G_a g‖_∞ ≤ A`, and that the total logarithmic forcing of `G_a g` is `≤ A`.

The constant depends on the ground energy at the top of the interval.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

local notation "V" => logarithmicRenewalMass

/-- The von Mangoldt weight. -/
abbrev vonMangoldtWeight : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)

theorem weightedForm_vonMangoldt (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    weightedForm vonMangoldtWeight a u v = ccmRestrictedWeilForm a u v := rfl

/-- `L²` mass controls `L¹` mass on the window. -/
theorem integral_norm_aperture_le (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∫ x, ‖(f : RealLineL2) x‖ ≤ a.1 + ‖(f : RealLineL2)‖ ^ 2 / 2 := by
  have hi := integrable_aperture a f
  have hsq : Integrable (fun x => ‖(f : RealLineL2) x‖ ^ 2) :=
    (Lp.memLp (f : RealLineL2)).integrable_norm_pow (by norm_num)
  have hc : Integrable ((centralInterval a.1).indicator fun _ => (1 : ℝ) / 2) :=
    (continuous_const.integrableOn_Icc).integrable_indicator (measurableSet_centralInterval a.1)
  have hzero : ∀ᵐ x ∂volume, x ∉ centralInterval a.1 → (f : RealLineL2) x = 0 := by
    have hcut := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
    rw [indicatorCutoff_suzukiApertureHilbert] at hcut
    filter_upwards [hcut] with x hx hn
    rw [hx, indicator_of_notMem hn]
  have hle : ∫ x, ‖(f : RealLineL2) x‖ ≤ ∫ x, ((centralInterval a.1).indicator (fun _ => (1 : ℝ) / 2) x +
      ‖(f : RealLineL2) x‖ ^ 2 / 2) := by
    apply integral_mono_ae hi.norm (hc.add (hsq.div_const 2))
    filter_upwards [hzero] with x hx
    change ‖(f : RealLineL2) x‖ ≤ (centralInterval a.1).indicator (fun _ => (1 : ℝ) / 2) x +
      ‖(f : RealLineL2) x‖ ^ 2 / 2
    by_cases hm : x ∈ centralInterval a.1
    · rw [indicator_of_mem hm]
      nlinarith only [sq_nonneg (‖(f : RealLineL2) x‖ - 1)]
    · rw [indicator_of_notMem hm, hx hm, norm_zero]
      norm_num
  rw [integral_add hc (hsq.div_const 2), integral_indicator (measurableSet_centralInterval a.1),
    setIntegral_const, integral_div] at hle
  have hvol : (volume : Measure ℝ).real (centralInterval a.1) = 2 * a.1 := by
    rw [measureReal_def, centralInterval, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith only [a.2])]
    ring
  rw [hvol, smul_eq_mul, ← Lp_two_norm_sq_eq_integral] at hle
  linarith only [hle]

/-- A polar coordinate is controlled by the `L¹` mass. -/
theorem norm_inner_polar_le (a : SuzukiPositiveAperture) {s : ℝ} (hs : |s| ≤ 1 / 2)
    (f : suzukiApertureHilbert a) :
    ‖inner ℂ (ccmPolarApertureVector a s) f‖ ≤ Real.exp (a.1 / 2) * ∫ x, ‖(f : RealLineL2) x‖ := by
  change ‖inner ℂ (ccmPolarL2Vector a s : RealLineL2) (f : RealLineL2)‖ ≤ _
  rw [L2.inner_def]
  have hi := integrable_aperture a f
  calc
    _ ≤ ∫ x, Real.exp (a.1 / 2) * ‖(f : RealLineL2) x‖ := by
      apply norm_integral_le_of_norm_le (hi.norm.const_mul _)
      filter_upwards [ccmPolarL2Vector_coeFn a s] with x hx
      rw [hx, RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      by_cases hm : x ∈ centralInterval a.1
      · rw [indicator_of_mem hm, ccmPolarProfile, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le]
        apply Real.exp_le_exp.mpr
        have hxa : |x| ≤ a.1 := abs_le.mpr hm
        calc
          _ ≤ |s * x| := le_abs_self _
          _ = |s| * |x| := abs_mul _ _
          _ ≤ 1 / 2 * a.1 := mul_le_mul hs hxa (abs_nonneg _) (by norm_num)
          _ = _ := by ring
      · rw [indicator_of_notMem hm, norm_zero]
        exact (Real.exp_pos _).le
    _ = _ := integral_const_mul _ _

theorem sum_weightedCoeff (lam : ℕ → ℝ) (D : ℝ) (a : SuzukiPositiveAperture) :
    ∑ j ∈ weightedIndexSet a, weightedCoeff lam D j =
      D + ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, |lam n| * (1 / Real.sqrt n) * 2 := by
  rw [weightedIndexSet, Finset.sum_insertNone, Finset.sum_product]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fintype.sum_bool]
  change |lam n| * (1 / Real.sqrt n) + |lam n| * (1 / Real.sqrt n) = _
  ring

namespace WeilHilbertBeforeContact

/-- The functional `x ↦ ⟨g, x⟩` on the Weil Hilbert space. -/
def sourceFunctional (a : PrecontactAperture) (g : suzukiApertureHilbert a.1) :
    WeilHilbertBeforeContact a →L[ℂ] ℂ :=
  (innerSL ℂ g).comp ((ccmArchimedeanFormToAperture a.1).comp (toFormCLM a))

/-- The Riesz vector `G_a g`. -/
def sourceVector (a : PrecontactAperture) (g : suzukiApertureHilbert a.1) :
    WeilHilbertBeforeContact a :=
  (sourceFunctional a g).adjoint 1

theorem inner_sourceVector (a : PrecontactAperture) (g : suzukiApertureHilbert a.1)
    (x : WeilHilbertBeforeContact a) :
    inner ℂ (sourceVector a g) x = inner ℂ g (ccmArchimedeanFormToAperture a.1 (toForm a x)) := by
  rw [sourceVector, ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (1 : ℂ) (inner ℂ g (ccmArchimedeanFormToAperture a.1 (toForm a x))) = _
  simp

/-- The physical source of `G_a g`. -/
def sourcePhysical (a : PrecontactAperture) (g : suzukiApertureHilbert a.1) :
    suzukiApertureHilbert a.1 :=
  ccmArchimedeanFormToAperture a.1 (toForm a (sourceVector a g))

/-- The total logarithmic forcing of `G_a g`. -/
def sourceForcing (a : PrecontactAperture) (g : suzukiApertureHilbert a.1) :
    suzukiApertureHilbert a.1 :=
  weightedForcing vonMangoldtWeight a.1 (toForm a (sourceVector a g)) g

theorem sourceVector_weightedForm (a : PrecontactAperture) (g : suzukiApertureHilbert a.1)
    (v : CCMArchimedeanFormDomain a.1) :
    weightedForm vonMangoldtWeight a.1 (toForm a (sourceVector a g)) v =
      inner ℂ g (ccmArchimedeanFormToAperture a.1 v) := by
  have h := inner_sourceVector a g ((toForm a).symm v)
  rw [inner_eq_weil, LinearEquiv.apply_symm_apply] at h
  rw [weightedForm_vonMangoldt]
  exact h

theorem hasLogarithmicEnergy_sourcePhysical (a : PrecontactAperture)
    (g : suzukiApertureHilbert a.1) :
    HasLogarithmicEnergy (sourcePhysical a g : RealLineL2) :=
  hasLogarithmicEnergy_ccm_form a.1 _

/-- The Riesz vector solves the logarithmic equation. -/
theorem sourcePhysical_logarithmicFullForm (a : PrecontactAperture)
    (g : suzukiApertureHilbert a.1) (f : suzukiApertureHilbert a.1)
    (hf : HasLogarithmicEnergy (f : RealLineL2)) :
    logarithmicFullForm (f : RealLineL2) (sourcePhysical a g : RealLineL2) =
      inner ℂ (f : RealLineL2) (sourceForcing a g : RealLineL2) :=
  logarithmicFullForm_of_weighted (sourceVector_weightedForm a g) f hf

/-- `‖G_a g‖₂² ≤ 2a/μ²` when `|g| ≤ 1`. -/
theorem norm_sourcePhysical_sq_le (a : PrecontactAperture) (g : suzukiApertureHilbert a.1)
    (hg : ∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤ 1) :
    ccmRestrictedWeilGroundEnergy a.1 ^ 2 * ‖(sourcePhysical a g : RealLineL2)‖ ^ 2 ≤ 2 * a.1.1 := by
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = ccmRestrictedWeilGroundEnergy a.1 := ⟨_, rfl⟩
  have hμ : 0 < μ := hμd ▸ precontact_groundEnergy_pos a
  rw [← hμd]
  obtain ⟨U, hU⟩ : ∃ U, U = sourcePhysical a g := ⟨_, rfl⟩
  rw [← hU]
  obtain ⟨n, hn⟩ : ∃ n, n = ‖(U : RealLineL2)‖ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = ‖(g : RealLineL2)‖ := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := hn ▸ norm_nonneg _
  have hm0 : 0 ≤ m := hm ▸ norm_nonneg _
  -- The norm of the vector is the pairing with `g`.
  have hfloor := groundEnergy_mul_mass_le a (sourceVector a g)
  rw [← hμd] at hfloor
  have hpair : ‖sourceVector a g‖ ^ 2 ≤ m * n := by
    have h1 := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (sourceVector a g)
    have h2 : inner ℂ (sourceVector a g) (sourceVector a g) = inner ℂ g U := by
      rw [inner_sourceVector, hU]
      rfl
    have h3 : ‖inner ℂ g U‖ ≤ m * n := by
      rw [hm, hn]
      exact norm_inner_le_norm (𝕜 := ℂ) (E := suzukiApertureHilbert a.1) g U
    rw [h1, h2]
    exact (Complex.re_le_norm _).trans h3
  have hUn : ‖ccmArchimedeanFormToAperture a.1 (toForm a (sourceVector a g))‖ = n := by
    rw [hn, hU]
    rfl
  rw [hUn] at hfloor
  have hmn : μ * n ^ 2 ≤ m * n := hfloor.trans hpair
  have hm2 : m ^ 2 ≤ 2 * a.1.1 := by
    rw [hm, Lp_two_norm_sq_eq_integral]
    have hzero : ∀ᵐ x ∂volume, x ∉ centralInterval a.1.1 → (g : RealLineL2) x = 0 := by
      have hcut := indicatorCutoff_ae (centralInterval a.1.1) (measurableSet_centralInterval a.1.1) g.1
      rw [indicatorCutoff_suzukiApertureHilbert] at hcut
      filter_upwards [hcut] with x hx hn
      rw [hx, indicator_of_notMem hn]
    have hc : Integrable ((centralInterval a.1.1).indicator fun _ => (1 : ℝ)) :=
      (continuous_const.integrableOn_Icc).integrable_indicator (measurableSet_centralInterval a.1.1)
    calc
      _ ≤ ∫ x, (centralInterval a.1.1).indicator (fun _ => (1 : ℝ)) x := by
        apply integral_mono_ae ((Lp.memLp (g : RealLineL2)).integrable_norm_pow (by norm_num)) hc
        filter_upwards [hg, hzero] with x h1 h2
        change ‖(g : RealLineL2) x‖ ^ 2 ≤ (centralInterval a.1.1).indicator (fun _ => (1 : ℝ)) x
        by_cases hx : x ∈ centralInterval a.1.1
        · rw [indicator_of_mem hx]
          exact pow_le_one₀ (norm_nonneg _) h1
        · rw [indicator_of_notMem hx, h2 hx, norm_zero]
          norm_num
      _ = 2 * a.1.1 := by
        rw [integral_indicator (measurableSet_centralInterval a.1.1), setIntegral_const, smul_eq_mul,
          mul_one, measureReal_def, centralInterval, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith only [a.1.2])]
        ring
  have hle : μ * n ≤ m := by
    by_cases hn00 : n = 0
    · rw [hn00, mul_zero]
      exact hm0
    have hnpos : 0 < n := lt_of_le_of_ne hn0 (Ne.symm hn00)
    have : (μ * n) * n ≤ m * n := by nlinarith only [hmn]
    exact le_of_mul_le_mul_right this hnpos
  have hsq : (μ * n) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (mul_nonneg hμ.le hn0) hle 2
  rw [mul_pow] at hsq
  rw [← hn]
  exact hsq.trans hm2

/-- The ground energy is antitone in the aperture. -/
theorem groundEnergy_anti {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) :
    ccmRestrictedWeilGroundEnergy b.1 ≤ ccmRestrictedWeilGroundEnergy a.1 :=
  ArithmeticContinuationAndCriticalEnergy.strictAnti_ccmRestrictedWeilGroundEnergy.antitone
    (Subtype.coe_le_coe.mp hab)

/-- **The Green operator is uniformly bounded on `L^∞`.** -/
theorem exists_uniform_source_bound (a₁ a₂ : PrecontactAperture) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a : PrecontactAperture, a₁.1.1 ≤ a.1.1 → a.1.1 ≤ a₂.1.1 →
      ∀ g : suzukiApertureHilbert a.1, (∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤ 1) →
        (∫ x, ‖(sourcePhysical a g : RealLineL2) x‖) ≤ A ∧
        (∀ᵐ x ∂volume, ‖(sourcePhysical a g : RealLineL2) x‖ ≤ A) ∧
        (∀ᵐ x ∂volume, ‖(sourceForcing a g : RealLineL2) x‖ ≤ A) := by
  obtain ⟨μ₂, hμ₂d⟩ : ∃ μ₂, μ₂ = ccmRestrictedWeilGroundEnergy a₂.1 := ⟨_, rfl⟩
  have hμ₂ : 0 < μ₂ := hμ₂d ▸ precontact_groundEnergy_pos a₂
  obtain ⟨L, hLd⟩ : ∃ L, L = a₂.1.1 + a₂.1.1 / μ₂ ^ 2 := ⟨_, rfl⟩
  have ha₂ : 0 < a₂.1.1 := a₂.1.2
  have ha₁ : 0 < a₁.1.1 := a₁.1.2
  have hL0 : 0 ≤ L := by
    rw [hLd]
    positivity
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = 0 + |logarithmicFormScalar| + ‖ccmArchimedeanRemainderScalar‖ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDd]
    positivity
  obtain ⟨K, hKd⟩ : ∃ K, K = D + ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊,
      |vonMangoldtWeight n| * (1 / Real.sqrt n) * 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKd]
    exact add_nonneg hD0 (Finset.sum_nonneg fun n _ => by positivity)
  -- The scale at which the prime terms are absorbed.
  obtain ⟨ρ, hρ, hsmall⟩ : ∃ ρ : ℝ, 0 < ρ ∧ K * V ρ ≤ 1 / 2 := by
    have ht := tendsto_logarithmicRenewalMass_zero.const_mul K
    rw [mul_zero] at ht
    have hev := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨ρ, hb, hp⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨ρ, hp, (show K * V ρ < 1 / 2 from hb).le⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = 1 + 3 / 4 * L + (Real.exp (a₂.1.1 / 2) * L + Real.exp (a₂.1.1 / 2) * L) *
      Real.exp (a₂.1.1 / 2) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCd]
    positivity
  obtain ⟨M, hMd⟩ : ∃ M, M = 2 * (C + 2 / a₁.1.1 * L + K * L / ρ) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMd]
    positivity
  refine ⟨L + M + (C + K * M), by positivity, fun a h1 h2 g hg => ?_⟩
  obtain ⟨U, hU⟩ : ∃ U, U = sourcePhysical a g := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = sourceForcing a g := ⟨_, rfl⟩
  rw [← hU, ← hF]
  have ha0 : 0 < a.1.1 := a.1.2
  have hμa : μ₂ ≤ ccmRestrictedWeilGroundEnergy a.1 := by
    rw [hμ₂d]
    exact groundEnergy_anti h2
  -- The `L¹` mass.
  have hnorm : ‖(U : RealLineL2)‖ ^ 2 ≤ 2 * (a₂.1.1 / μ₂ ^ 2) := by
    have hsq := norm_sourcePhysical_sq_le a g hg
    rw [← hU] at hsq
    have hmono : μ₂ ^ 2 ≤ ccmRestrictedWeilGroundEnergy a.1 ^ 2 := pow_le_pow_left₀ hμ₂.le hμa 2
    have hnn := sq_nonneg ‖(U : RealLineL2)‖
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    have ha : a.1.1 ≤ a₂.1.1 := h2
    nlinarith only [hsq, mul_le_mul_of_nonneg_right hmono hnn, ha]
  have hUL : (∫ x, ‖(U : RealLineL2) x‖) ≤ L := by
    have h := integral_norm_aperture_le a.1 U
    have ha : a.1.1 ≤ a₂.1.1 := h2
    rw [hLd]
    linarith only [h, hnorm, ha]
  have hUi := integrable_aperture a.1 U
  have hUL' : ∫⁻ z, ‖(U : RealLineL2) z‖ₑ ≤ ENNReal.ofReal L := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hUi]
    exact ENNReal.ofReal_le_ofReal hUL
  -- The domination.
  have hI0 : 0 ≤ ∫ x, ‖(U : RealLineL2) x‖ := integral_nonneg fun _ => norm_nonneg _
  have hexp : Real.exp (a.1.1 / 2) ≤ Real.exp (a₂.1.1 / 2) :=
    Real.exp_le_exp.mpr (by linarith only [show a.1.1 ≤ a₂.1.1 from h2])
  have hE0 := Real.exp_pos (a.1.1 / 2)
  have hdom := weightedForcing_dominated vonMangoldtWeight a.1 (toForm a (sourceVector a g)) g
    (C₀ := 1) (c₀ := 0) (hg.mono fun x hx => by simpa using hx)
  rw [show ccmArchimedeanFormToAperture a.1 (toForm a (sourceVector a g)) = U from hU.symm, ← hDd] at hdom
  have hF' : weightedForcing vonMangoldtWeight a.1 (toForm a (sourceVector a g)) g = F := hF.symm
  rw [hF'] at hdom
  have hpolar : (‖inner ℂ (ccmPolarApertureVector a.1 (-1 / 2)) U‖ +
      ‖inner ℂ (ccmPolarApertureVector a.1 (1 / 2)) U‖) * Real.exp (a.1.1 / 2) ≤
      (Real.exp (a₂.1.1 / 2) * L + Real.exp (a₂.1.1 / 2) * L) * Real.exp (a₂.1.1 / 2) := by
    have hp₁ := norm_inner_polar_le a.1 (s := -1 / 2) (by norm_num [abs_le]) U
    have hp₂ := norm_inner_polar_le a.1 (s := 1 / 2) (by norm_num [abs_le]) U
    have hb : Real.exp (a.1.1 / 2) * ∫ x, ‖(U : RealLineL2) x‖ ≤ Real.exp (a₂.1.1 / 2) * L :=
      mul_le_mul hexp hUL hI0 (Real.exp_pos _).le
    exact mul_le_mul (add_le_add (hp₁.trans hb) (hp₂.trans hb)) hexp hE0.le (by positivity)
  have hconst : 1 + 3 / 4 * (∫ x, ‖(U : RealLineL2) x‖) +
      (‖inner ℂ (ccmPolarApertureVector a.1 (-1 / 2)) U‖ +
        ‖inner ℂ (ccmPolarApertureVector a.1 (1 / 2)) U‖) * Real.exp (a.1.1 / 2) ≤ C := by
    rw [hCd]
    linarith only [hUL, hpolar]
  have hdom' : ∀ᵐ x ∂volume, ‖(F : RealLineL2) x‖ ≤ C + ∑ j ∈ weightedIndexSet a.1,
      weightedCoeff vonMangoldtWeight D j * ‖(U : RealLineL2) (x - weightedShift j)‖ := by
    filter_upwards [hdom] with x hx
    linarith only [hx, hconst]
  have hsum : ∑ j ∈ weightedIndexSet a.1, weightedCoeff vonMangoldtWeight D j ≤ K := by
    rw [sum_weightedCoeff, hKd]
    refine add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor (Real.exp_le_exp.mpr ?_)))
      fun n _ _ => by positivity)
    linarith only [show a.1.1 ≤ a₂.1.1 from h2]
  have hUE : HasLogarithmicEnergy (U : RealLineL2) := by
    rw [hU]
    exact hasLogarithmicEnergy_sourcePhysical a g
  have hsolve : ∀ f : suzukiApertureHilbert a.1, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (U : RealLineL2) = inner ℂ (f : RealLineL2) (F : RealLineL2) := by
    rw [hU, hF]
    exact sourcePhysical_logarithmicFullForm a g
  have hsup := ae_norm_le_of_window_equation_explicit a.1 U F hUE hsolve (weightedIndexSet a.1)
    weightedShift (weightedCoeff_nonneg vonMangoldtWeight hD0) hC0 hK0 hL0 hsum hρ hsmall hUL' hdom'
  have hsupM : ∀ᵐ x ∂volume, ‖(U : RealLineL2) x‖ ≤ M := by
    filter_upwards [hsup] with x hx
    refine hx.trans ?_
    rw [hMd]
    have hdiv : 2 / a.1.1 ≤ 2 / a₁.1.1 := div_le_div_of_nonneg_left zero_le_two ha₁ h1
    have := mul_le_mul_of_nonneg_right hdiv hL0
    linarith only [this]
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ j ∈ weightedIndexSet a.1,
      ‖(U : RealLineL2) (x - weightedShift j)‖ ≤ M :=
    (Filter.eventually_all_finset _).mpr fun j _ =>
      (measurePreserving_sub_right (volume : Measure ℝ) (weightedShift j)).quasiMeasurePreserving.ae hsupM
  have hLMC : 0 ≤ C + K * M := by positivity
  refine ⟨?_, ?_, ?_⟩
  · linarith only [hUL, hM0, hLMC]
  · filter_upwards [hsupM] with x hx
    linarith only [hx, hL0, hLMC]
  · filter_upwards [hdom', hall] with x h3 h4
    have hs : ∑ j ∈ weightedIndexSet a.1, weightedCoeff vonMangoldtWeight D j *
        ‖(U : RealLineL2) (x - weightedShift j)‖ ≤ K * M := by
      calc
        _ ≤ ∑ j ∈ weightedIndexSet a.1, weightedCoeff vonMangoldtWeight D j * M :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (h4 j hj)
            (weightedCoeff_nonneg vonMangoldtWeight hD0 j)
        _ = (∑ j ∈ weightedIndexSet a.1, weightedCoeff vonMangoldtWeight D j) * M :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hsum hM0
    linarith only [h3, hs, hL0, hM0]

end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
