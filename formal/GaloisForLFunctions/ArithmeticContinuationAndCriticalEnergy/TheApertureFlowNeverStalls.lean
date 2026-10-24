import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFlowIsAShellFlux
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarStrictDomain
import GaloisForLFunctions.RHTower.WeilInsertionAnyWeight
import GaloisForLFunctions.SquareRootThreshold.TheContactApertureOfTheGroundEnergyPath

/-!
# The aperture flow of the restricted Weil ground energy never stalls

For the literal restricted Weil operator the shell flux of `TheApertureFlowIsAShellFlux` is never
zero, and the flow `A ↦ μ(A)` is strictly decreasing.

* **Translation invariance of the full form.** Physical translation preserves the complete literal
  quadratic without any pole constraint: the two exponential pole coordinates pick up the
  reciprocal characters `e^{∓h/2}` and their product is invariant, while the archimedean
  multiplier and the prime correlations are invariant by unitarity
  (`ccmRestrictedWeilSourceQuadratic_translate_full`); by polarization the sesquilinear form is
  invariant (`apertureForm_literal_translate`).
* **No non-radiating eigenvector.** For `a < b` no nonzero form vector supported in the aperture `a`
  is a form eigenvector at the aperture `b`, whatever the eigenvalue
  (`not_isFormEigen_apertureExt`). Otherwise every small translate would be an eigenvector with the
  same eigenvalue at an intermediate aperture; that eigenspace is the kernel of `1 − K` for the
  compact Birman–Schwinger pencil `K`, hence finite-dimensional, while distinct equally spaced
  `L²` translates are linearly independent.
* **Consequences for the flow.** Every shell flux of a ground state is nonzero
  (`exists_shellFlux_ne_zero`); `μ` is strictly antitone (`strictAnti_ccmRestrictedWeilGroundEnergy`);
  RH holds iff `μ(A) > 0` at every aperture (`riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos`);
  and if RH fails the contact aperture is the unique zero of the flow, with `μ > 0` before it and
  `μ < 0` after it (`riemannHypothesis_or_unique_groundEnergyCrossing`).

The argument uses translation invariance, compactness and Fourier independence only; it decides the
shape of the flow (strict, at most one transversal crossing), not its sign.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.RHTower _root_.RHTower.WeilDeletion GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ## Translation invariance of the full literal form -/

/-- **Translation invariance of the full literal quadratic.** The pole coordinates transform by
`e^{h/2}` and `e^{−h/2}`, so their product is invariant; no pole constraint is needed. -/
theorem ccmRestrictedWeilSourceQuadratic_translate_full {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic b (ccmArchimedeanFormTranslate h hab u) =
      ccmRestrictedWeilSourceQuadratic a u := by
  have hab' : a.1 ≤ b.1 := by linarith [abs_nonneg h]
  set w := apertureExt hab' u with hw
  have hwval : w.1 = u.1 := apertureExt_val hab' u
  set v := ccmArchimedeanFormTranslate h hab u with hv
  have hgamma :
      (∫ x, 2 * gammaHardyPhaseRate (2 * Real.pi * x) * ‖(v.1 : ℝ → ℂ) x‖ ^ 2) =
      ∫ x, 2 * gammaHardyPhaseRate (2 * Real.pi * x) * ‖(w.1 : ℝ → ℂ) x‖ ^ 2 := by
    rw [hwval]
    apply integral_congr_ae
    have hp := (ccmArchimedeanPhaseMul_coeFn h u.1).filter_mono
      (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [hp] with x hx
    change _ * ‖ccmArchimedeanPhaseMul h u.1 x‖ ^ 2 = _
    rw [hx, norm_mul, MellinL2.norm_fourierPhase, one_mul]
  have hp : ∀ t : ℝ,
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b v : SoninL2))
        (ccmArchimedeanFormToAperture b v : SoninL2) =
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b w : SoninL2))
        (ccmArchimedeanFormToAperture b w : SoninL2) := by
    intro t
    rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq hwval, hv,
      ccmArchimedeanFormTranslate_physical, logTranslationCLM_add_apply, add_comm t h,
      ← logTranslationCLM_add_apply]
    exact (MellinL2.additiveTranslationUnitary h).inner_map_map _ _
  have hpol : ∀ s : ℝ,
      inner ℂ (ccmPolarApertureVector b s) (ccmArchimedeanFormToAperture b v) =
        (Real.exp (-s * h) : ℂ) *
          inner ℂ (ccmPolarApertureVector b s) (ccmArchimedeanFormToAperture b w) := fun s => by
    rw [hv, inner_polar_ccmArchimedeanFormTranslate,
      inner_ccmPolarApertureVector_eq_of_val_eq hab' s hwval]
  have hchar : (Real.exp (-(-1 / 2) * h) : ℂ) * (Real.exp (-(1 / 2) * h) : ℂ) = 1 := by
    have h0 : -(-1 / 2) * h + -(1 / 2) * h = 0 := by ring
    rw [← Complex.ofReal_mul, ← Real.exp_add, h0, Real.exp_zero, Complex.ofReal_one]
  have hpolar : ∀ A B : ℂ,
      (starRingEnd ℂ) ((Real.exp (-(-1 / 2) * h) : ℂ) * A) * ((Real.exp (-(1 / 2) * h) : ℂ) * B) +
          (starRingEnd ℂ) ((Real.exp (-(1 / 2) * h) : ℂ) * B) *
            ((Real.exp (-(-1 / 2) * h) : ℂ) * A) =
        (starRingEnd ℂ) A * B + (starRingEnd ℂ) B * A := fun A B => by
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination ((starRingEnd ℂ) A * B + (starRingEnd ℂ) B * A) * hchar
  calc ccmRestrictedWeilSourceQuadratic b v = ccmRestrictedWeilSourceQuadratic b w := by
        simp only [ccmRestrictedWeilSourceQuadratic]
        simp_rw [hp]
        rw [hgamma, hpol (-1 / 2), hpol (1 / 2), hpolar]
    _ = ccmRestrictedWeilSourceQuadratic a u :=
        ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab' hwval

theorem literalFamily_Q_translate {a b : SuzukiPositiveAperture} (h : ℝ) (hab : a.1 + |h| ≤ b.1)
    (u : CCMArchimedeanFormDomain a) :
    literalFamily.Q b (ccmArchimedeanFormTranslate h hab u) = literalFamily.Q a u := by
  rw [literalFamily_Q_eq, literalFamily_Q_eq, ccmRestrictedWeilSourceQuadratic_translate_full]

/-- The translation defect of the literal form, with swapped arguments (linear in the first). -/
private def translateDefect {a b : SuzukiPositiveAperture} (h : ℝ) (hab : a.1 + |h| ≤ b.1)
    (x y : CCMArchimedeanFormDomain a) : ℂ :=
  apertureForm literalFamily b (ccmArchimedeanFormTranslate h hab y)
      (ccmArchimedeanFormTranslate h hab x) - apertureForm literalFamily a y x

private theorem isHermitianForm_translateDefect {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) : IsHermitianForm (translateDefect h hab) where
  add_left x x' z := by
    rw [translateDefect, translateDefect, translateDefect, map_add, apertureForm_add_right,
      apertureForm_add_right]
    ring
  smul_left c x z := by
    rw [translateDefect, translateDefect, map_smul, apertureForm_smul_right,
      apertureForm_smul_right]
    ring
  symm x z := by
    rw [translateDefect, translateDefect, Complex.star_def, map_sub, ← apertureForm_conj,
      ← apertureForm_conj]

/-- **Translation invariance of the literal sesquilinear form.** -/
theorem apertureForm_literal_translate {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (x y : CCMArchimedeanFormDomain a) :
    apertureForm literalFamily b (ccmArchimedeanFormTranslate h hab x)
        (ccmArchimedeanFormTranslate h hab y) = apertureForm literalFamily a x y := by
  have hdiag : ∀ z, (translateDefect h hab z z).re = 0 := fun z => by
    rw [translateDefect, sub_re, apertureForm_self_re, apertureForm_self_re,
      literalFamily_Q_translate, sub_self]
  have hz := (isHermitianForm_translateDefect h hab).eq_zero_of_self_re_eq_zero
    (fun z => (hdiag z).ge) (hdiag y) x
  rw [translateDefect] at hz
  exact sub_eq_zero.mp hz

/-- Translation preserves the physical inner product of form vectors. -/
theorem inner_embedding_translate {a b : SuzukiPositiveAperture} (h : ℝ) (hab : a.1 + |h| ≤ b.1)
    (x y : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab x))
        (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab y)) =
      inner ℂ (ccmArchimedeanFormToAperture a x) (ccmArchimedeanFormToAperture a y) := by
  rw [Submodule.coe_inner, Submodule.coe_inner, ccmArchimedeanFormTranslate_physical,
    ccmArchimedeanFormTranslate_physical]
  exact (MellinL2.additiveTranslationUnitary h).inner_map_map _ _

/-- Translating forth and back is the extension to the final aperture. -/
theorem translate_neg_translate {a c b : SuzukiPositiveAperture} (s : ℝ) (h₁ : a.1 + |s| ≤ c.1)
    (h₂ : c.1 + |-s| ≤ b.1) (hab : a.1 ≤ b.1) (v : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormTranslate (-s) h₂ (ccmArchimedeanFormTranslate s h₁ v) = apertureExt hab v := by
  apply ccmArchimedeanFormToAperture_injective b
  apply Subtype.ext
  rw [ccmArchimedeanFormTranslate_physical, ccmArchimedeanFormTranslate_physical,
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq (apertureExt_val hab v),
    logTranslationCLM_add_apply, neg_add_cancel, logTranslationCLM_zero_apply]

/-! ## Form eigenvectors and their finite multiplicity -/

/-- `v` is a form eigenvector of the literal restricted Weil operator at aperture `b` with
eigenvalue `E`: the form shifted by `E` annihilates it. -/
def IsFormEigen (b : SuzukiPositiveAperture) (E : ℝ) (v : CCMArchimedeanFormDomain b) : Prop :=
  ∀ z : CCMArchimedeanFormDomain b, shiftedForm literalFamily b E v z = 0

/-- A form eigenvector lies in the kernel of `1 − K`, `K` the compact Birman–Schwinger pencil. -/
theorem mem_radical_of_isFormEigen {b : SuzukiPositiveAperture} {E : ℝ}
    {v : CCMArchimedeanFormDomain b} (hv : IsFormEigen b E v) :
    v ∈ compactConstrainedRadical ⊤ (ccmRestrictedWeilFormBirmanSchwinger b E) := by
  rw [mem_compactConstrainedRadical]
  refine ⟨Submodule.mem_top, fun z _ => ?_⟩
  have hbs := ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger b E v z
  rw [inner_smul_left (ccmArchimedeanFormToAperture b v) (ccmArchimedeanFormToAperture b z) (E : ℂ),
    Complex.conj_ofReal] at hbs
  have h0 : inner ℂ ((ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain b) -
      ccmRestrictedWeilFormBirmanSchwinger b E) v) z = 0 := by
    rw [← hbs]
    exact hv z
  rw [sub_apply, ContinuousLinearMap.id_apply] at h0
  rw [← inner_conj_symm z (v - ccmRestrictedWeilFormBirmanSchwinger b E v), h0, map_zero]

/-- **No non-radiating eigenvector.** For `a < b`, no nonzero form vector supported in the
aperture `a` is a form eigenvector of the literal operator at the aperture `b`. -/
theorem not_isFormEigen_apertureExt {a b : SuzukiPositiveAperture} (hab : a.1 < b.1)
    {v : CCMArchimedeanFormDomain a} (hv : ccmArchimedeanFormToAperture a v ≠ 0) (E : ℝ) :
    ¬ IsFormEigen b E (apertureExt hab.le v) := by
  intro heig
  set δ : ℝ := (b.1 - a.1) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  let c : SuzukiPositiveAperture := ⟨a.1 + δ, by linarith [a.2]⟩
  let K := ccmRestrictedWeilFormBirmanSchwinger c E
  let N := compactConstrainedRadical (⊤ : Submodule ℂ (CCMArchimedeanFormDomain c)) K
  haveI : FiniteDimensional ℂ N := finiteDimensional_compactConstrainedRadical ⊤
    (by simp only [Submodule.top_coe, isClosed_univ]) K
    (isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger c E)
  let n := Module.finrank ℂ N + 1
  let t : ℝ := δ / (n + 1)
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have ht : 0 < t := div_pos hδ hn0
  have hstep : ∀ i : Fin n, |(i : ℝ) * t| ≤ δ := by
    intro i
    have hi : (i : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : i.val ≤ n + 1)
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg i.val) ht.le)]
    have hprod := mul_le_mul_of_nonneg_right hi ht.le
    have he : ((n : ℝ) + 1) * t = δ := by
      dsimp only [t]
      exact mul_div_cancel₀ _ hn0.ne'
    linarith
  have hfit : ∀ i : Fin n, a.1 + |(i : ℝ) * t| ≤ c.1 := fun i => by
    change a.1 + |(i : ℝ) * t| ≤ a.1 + δ
    linarith [hstep i]
  have hback : ∀ i : Fin n, c.1 + |-((i : ℝ) * t)| ≤ b.1 := fun i => by
    change a.1 + δ + |-((i : ℝ) * t)| ≤ b.1
    rw [abs_neg]
    linarith [hstep i]
  let w (i : Fin n) := ccmArchimedeanFormTranslate ((i : ℝ) * t) (hfit i) v
  have hweig : ∀ i, IsFormEigen c E (w i) := by
    intro i z
    have hwb : ccmArchimedeanFormTranslate (-((i : ℝ) * t)) (hback i) (w i) = apertureExt hab.le v :=
      translate_neg_translate ((i : ℝ) * t) (hfit i) (hback i) hab.le v
    have hform := apertureForm_literal_translate (-((i : ℝ) * t)) (hback i) (w i) z
    have hinner := inner_embedding_translate (-((i : ℝ) * t)) (hback i) (w i) z
    rw [hwb] at hform hinner
    have hz := heig (ccmArchimedeanFormTranslate (-((i : ℝ) * t)) (hback i) z)
    rw [shiftedForm, hform, hinner] at hz
    exact hz
  let wN (i : Fin n) : N := ⟨w i, mem_radical_of_isFormEigen (hweig i)⟩
  have hvne : (ccmArchimedeanFormToAperture a v : SoninL2) ≠ 0 := fun hz =>
    hv (Subtype.ext hz)
  have hli := linearIndependent_arithmetic_L2_translates n ht.ne' hvne
  have hwli : LinearIndependent ℂ wN := by
    rw [Fintype.linearIndependent_iff]
    intro coef hc
    have hm := congrArg (fun z : N => (ccmArchimedeanFormToAperture c z.1 : SoninL2)) hc
    have hm' : ∑ i : Fin n, coef i •
        (ccmArchimedeanFormToAperture c (w i) : SoninL2) = 0 := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        map_sum, map_smul, map_zero] using hm
    simp only [w, ccmArchimedeanFormTranslate_physical] at hm'
    exact (Fintype.linearIndependent_iff.mp hli) coef hm'
  have hdim := hwli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hdim
  dsimp only [n] at hdim
  omega

/-! ## Consequences for the flow -/

/-- **Every shell flux of the literal flow is nonzero.** For `a < b` the ground state at `a`
radiates into the shell: its shell flux is a nonzero functional on the form domain at `b`. -/
theorem exists_shellFlux_ne_zero {a b : SuzukiPositiveAperture} (hab : a.1 < b.1) :
    ∃ v : CCMArchimedeanFormDomain b, shellFlux literalFamily hab.le v ≠ 0 := by
  by_contra hall
  push Not at hall
  have hne : ccmArchimedeanFormToAperture a (literalFamily.normalizedGround a) ≠ 0 := by
    intro hz
    have h1 := literalFamily.norm_normalizedGround_embedding a
    rw [hz, norm_zero] at h1
    exact zero_ne_one h1
  exact not_isFormEigen_apertureExt hab hne (literalFamily.energy a) hall

/-- **The flow is strictly decreasing.** A flat step would make the extended ground state a ground
state, hence a non-radiating eigenvector. -/
theorem strictAnti_ccmRestrictedWeilGroundEnergy : StrictAnti ccmRestrictedWeilGroundEnergy := by
  intro a b hab
  have habv : a.1 < b.1 := hab
  rcases (ccmRestrictedWeilGroundEnergy_antitone habv.le).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨v, hv⟩ := exists_shellFlux_ne_zero habv
    exact hv (shellFlux_eq_zero_of_energy_eq literalFamily habv.le heq v)

/-- On every step `a < b` the relaxation energy of the extended ground state is strictly
positive, whatever multiple of the larger ground state is subtracted. -/
theorem shiftedForm_ext_ground_pos {a b : SuzukiPositiveAperture} (hab : a.1 < b.1) (c : ℂ) :
    0 < (shiftedForm literalFamily b (literalFamily.energy b)
      (apertureExt hab.le (literalFamily.normalizedGround a) - c • literalFamily.normalizedGround b)
      (apertureExt hab.le (literalFamily.normalizedGround a) -
        c • literalFamily.normalizedGround b)).re := by
  rw [← energy_sub_energy_eq_shiftedForm, sub_pos]
  exact strictAnti_ccmRestrictedWeilGroundEnergy hab

/-- **RH iff the flow stays strictly positive.** -/
theorem riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture, 0 < ccmRestrictedWeilGroundEnergy a := by
  constructor
  · intro hRH a
    let b : SuzukiPositiveAperture := ⟨a.1 + 1, by linarith [a.2]⟩
    have hab : a < b := by change a.1 < a.1 + 1; linarith
    exact lt_of_le_of_lt (ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH b)
      (strictAnti_ccmRestrictedWeilGroundEnergy hab)
  · intro h
    exact riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg.mpr fun a => (h a).le

/-- **The flow crosses zero at most once.** Either RH holds, or the contact aperture is the unique
zero of the flow, with positive energy before it and negative energy after it. -/
theorem riemannHypothesis_or_unique_groundEnergyCrossing :
    RiemannHypothesis ∨ ∃ astar : SuzukiPositiveAperture,
      ccmRestrictedWeilGroundEnergy astar = 0 ∧
      (∀ a : SuzukiPositiveAperture, a < astar → 0 < ccmRestrictedWeilGroundEnergy a) ∧
      (∀ a : SuzukiPositiveAperture, astar < a → ccmRestrictedWeilGroundEnergy a < 0) ∧
      (∀ a : SuzukiPositiveAperture, ccmRestrictedWeilGroundEnergy a = 0 → a = astar) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  right
  refine ⟨⟨zetaContactAperture, zetaContactAperture_pos hRH⟩,
    ccmRestrictedWeilGroundEnergy_contact_eq_zero hRH, fun a ha => ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · rw [← ccmRestrictedWeilGroundEnergy_contact_eq_zero hRH]
    exact strictAnti_ccmRestrictedWeilGroundEnergy ha
  · rw [← ccmRestrictedWeilGroundEnergy_contact_eq_zero hRH]
    exact strictAnti_ccmRestrictedWeilGroundEnergy ha
  · exact strictAnti_ccmRestrictedWeilGroundEnergy.injective
      (ha.trans (ccmRestrictedWeilGroundEnergy_contact_eq_zero hRH).symm)

/-- **The aperture flow never stalls.** No ground state is non-radiating, the flow is strictly
decreasing, RH is strict positivity of the flow, and the flow crosses zero at most once. -/
theorem apertureFlow_neverStalls :
    (∀ {a b : SuzukiPositiveAperture} (hab : a.1 < b.1),
      ∃ v : CCMArchimedeanFormDomain b, shellFlux literalFamily hab.le v ≠ 0) ∧
    StrictAnti ccmRestrictedWeilGroundEnergy ∧
    (RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture, 0 < ccmRestrictedWeilGroundEnergy a) ∧
    (RiemannHypothesis ∨ ∃ astar : SuzukiPositiveAperture,
      ccmRestrictedWeilGroundEnergy astar = 0 ∧
      (∀ a : SuzukiPositiveAperture, a < astar → 0 < ccmRestrictedWeilGroundEnergy a) ∧
      (∀ a : SuzukiPositiveAperture, astar < a → ccmRestrictedWeilGroundEnergy a < 0) ∧
      (∀ a : SuzukiPositiveAperture, ccmRestrictedWeilGroundEnergy a = 0 → a = astar)) :=
  ⟨fun hab => exists_shellFlux_ne_zero hab, strictAnti_ccmRestrictedWeilGroundEnergy,
    riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos,
    riemannHypothesis_or_unique_groundEnergyCrossing⟩

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
