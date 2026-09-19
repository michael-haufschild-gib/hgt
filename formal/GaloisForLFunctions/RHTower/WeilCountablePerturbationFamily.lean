import GaloisForLFunctions.RHTower.WeilFinitePerturbationFamily

/-!
# The restricted Weil operator with countably many prime weights changed

For scales `x n > 1` and weights `w n` with summable budget `∑ |w n| · 2/√(x n)` and summable
logarithmic moment, the series of inserted blocks converges in operator norm and defines an
aperture-compatible family of self-adjoint remainders.  The family's ground energy exceeds the
literal one by at most the budget, so it is unbounded below if the Riemann hypothesis fails, and
its Rayleigh floor on the modulated wide bump is the literal zero side minus the series of the
visible block terms.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilDeletion

/-! ## Operator norm of the inserted block -/

theorem norm_ccmScaleTransportOperator_apply_le (a : SuzukiPositiveAperture) {x : ℝ} (hx : 0 < x)
    (f : suzukiApertureHilbert a) :
    ‖ccmScaleTransportOperator a x f‖ ≤ (2 / Real.sqrt x) * ‖f‖ := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  set g := ccmScaleTransportOperator a x f with hg
  have hinner := inner_ccmScaleTransportOperator a x f g
  have hsq : ‖g‖ ^ 2 = ‖inner ℂ g g‖ := by
    have e : inner ℂ g g = ((‖g‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K g
    rw [e, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hb : ∀ h : ℝ, ‖inner ℂ (logTranslationCLM h f.1) g.1‖ ≤ ‖f‖ * ‖g‖ := by
    intro h
    calc ‖inner ℂ (logTranslationCLM h f.1) g.1‖
        ≤ ‖logTranslationCLM h f.1‖ * ‖g.1‖ := norm_inner_le_norm _ _
      _ = ‖f‖ * ‖g‖ := by rw [norm_logTranslationCLM_apply, Submodule.norm_coe, Submodule.norm_coe]
  have h1 : ‖g‖ * ‖g‖ ≤ ((2 / Real.sqrt x) * ‖f‖) * ‖g‖ := by
    rw [← sq, hsq, hinner, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc (1 / Real.sqrt x) * ‖inner ℂ (logTranslationCLM (Real.log x) f.1) g.1 +
          inner ℂ (logTranslationCLM (-Real.log x) f.1) g.1‖
        ≤ (1 / Real.sqrt x) * (‖f‖ * ‖g‖ + ‖f‖ * ‖g‖) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add (hb _) (hb _))
      _ = ((2 / Real.sqrt x) * ‖f‖) * ‖g‖ := by ring
  rcases eq_or_lt_of_le (norm_nonneg g) with h0 | h0
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_right h1 h0

theorem norm_ccmInsertedBlock_le (a : SuzukiPositiveAperture) {x : ℝ} (hx : 0 < x) (w : ℝ) :
    ‖ccmInsertedBlock a x w‖ ≤ |w| * (2 / Real.sqrt x) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
  unfold ccmInsertedBlock
  split_ifs with hvis
  · show ‖(w : ℂ) • ccmScaleTransportOperator a x f‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_ccmScaleTransportOperator_apply_le a hx f) (abs_nonneg w)
  · have h0 : (0 : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a) f = 0 := rfl
    rw [h0, norm_zero]
    positivity

/-! ## Countable perturbations -/

/-- Countably many changes of prime weights with summable budget and logarithmic moment. -/
structure CountablePrimePerturbation where
  x : ℕ → ℝ
  w : ℕ → ℝ
  one_lt : ∀ n, 1 < x n
  budget_summable : Summable fun n => |w n| * (2 / Real.sqrt (x n))
  logMoment_summable : Summable fun n => |w n| * (2 / Real.sqrt (x n)) * Real.log (x n)

theorem summable_ccmInsertedBlock (a : SuzukiPositiveAperture) (P : CountablePrimePerturbation) :
    Summable fun n => ccmInsertedBlock a (P.x n) (P.w n) := by
  have h : ∀ n, ‖ccmInsertedBlock a (P.x n) (P.w n)‖ ≤ |P.w n| * (2 / Real.sqrt (P.x n)) :=
    fun n => norm_ccmInsertedBlock_le a (by linarith [P.one_lt n]) _
  exact @Summable.of_norm_bounded ℕ _ ContinuousLinearMap.toSeminormedAddCommGroup _
    (fun n => ccmInsertedBlock a (P.x n) (P.w n)) _ P.budget_summable h

/-- The series of inserted blocks. -/
def ccmCountableBlock (a : SuzukiPositiveAperture) (P : CountablePrimePerturbation) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑' n, ccmInsertedBlock a (P.x n) (P.w n)

theorem adjoint_tsum_eq {a : SuzukiPositiveAperture}
    {B : ℕ → (suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)} (h : Summable B) :
    ContinuousLinearMap.adjoint (∑' n, B n) = ∑' n, ContinuousLinearMap.adjoint (B n) :=
  (h.hasSum.map (ContinuousLinearMap.adjoint (E := suzukiApertureHilbert a)
    (F := suzukiApertureHilbert a)).toLinearEquiv.toAddMonoidHom
    (ContinuousLinearMap.adjoint (E := suzukiApertureHilbert a)
      (F := suzukiApertureHilbert a)).continuous).tsum_eq.symm

theorem ccmCountableBlock_isSelfAdjoint (a : SuzukiPositiveAperture)
    (P : CountablePrimePerturbation) : IsSelfAdjoint (ccmCountableBlock a P) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold ccmCountableBlock
  rw [adjoint_tsum_eq (summable_ccmInsertedBlock a P)]
  refine tsum_congr fun n => ?_
  have := ccmInsertedBlock_isSelfAdjoint a (P.x n) (P.w n)
  rwa [ContinuousLinearMap.isSelfAdjoint_iff'] at this

theorem ccmCountableBlock_apply (a : SuzukiPositiveAperture) (P : CountablePrimePerturbation)
    (f : suzukiApertureHilbert a) :
    ccmCountableBlock a P f = ∑' n, ccmInsertedBlock a (P.x n) (P.w n) f :=
  ((summable_ccmInsertedBlock a P).hasSum.mapL
    (ContinuousLinearMap.apply ℂ (suzukiApertureHilbert a) f)).tsum_eq.symm

theorem summable_ccmInsertedBlock_apply (a : SuzukiPositiveAperture)
    (P : CountablePrimePerturbation) (f : suzukiApertureHilbert a) :
    Summable fun n => ccmInsertedBlock a (P.x n) (P.w n) f :=
  ((summable_ccmInsertedBlock a P).hasSum.mapL
    (ContinuousLinearMap.apply ℂ (suzukiApertureHilbert a) f)).summable

theorem re_inner_ccmCountableBlock (a : SuzukiPositiveAperture) (P : CountablePrimePerturbation)
    (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmCountableBlock a P f) f).re =
      ∑' n, (inner ℂ (ccmInsertedBlock a (P.x n) (P.w n) f) f).re := by
  rw [ccmCountableBlock_apply]
  set S := ∑' n, ccmInsertedBlock a (P.x n) (P.w n) f with hS
  have e : inner ℂ S f = (starRingEnd ℂ) (inner ℂ f S) := (inner_conj_symm S f).symm
  rw [e, Complex.conj_re]
  have hs := (summable_ccmInsertedBlock_apply a P f).hasSum.mapL (innerSL ℂ f)
  have h2 : (inner ℂ f S).re = ∑' n, (inner ℂ f (ccmInsertedBlock a (P.x n) (P.w n) f)).re :=
    (hs.mapL Complex.reCLM).tsum_eq.symm
  rw [h2]
  refine tsum_congr fun n => ?_
  have e' : inner ℂ (ccmInsertedBlock a (P.x n) (P.w n) f) f =
      (starRingEnd ℂ) (inner ℂ f (ccmInsertedBlock a (P.x n) (P.w n) f)) :=
    (inner_conj_symm _ f).symm
  rw [e', Complex.conj_re]

/-- The bounded remainder with the countable block removed from the prime side. -/
def ccmCountableRemainder (a : SuzukiPositiveAperture) (P : CountablePrimePerturbation) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmRestrictedWeilBoundedRemainder a - ccmCountableBlock a P

theorem ccmCountableRemainder_isSelfAdjoint (a : SuzukiPositiveAperture)
    (P : CountablePrimePerturbation) : IsSelfAdjoint (ccmCountableRemainder a P) := by
  unfold ccmCountableRemainder
  have h1 := ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a
  have h2 := ccmCountableBlock_isSelfAdjoint a P
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h1 h2 ⊢
  rw [ContinuousLinearMap.adjoint.map_sub, h1, h2]

/-- The countably perturbed remainders as an aperture-compatible family. -/
def countableFamily (P : CountablePrimePerturbation) : CCMRemainderFamily where
  B a := ccmCountableRemainder a P
  selfAdjoint a := ccmCountableRemainder_isSelfAdjoint a P
  compat := by
    intro a b hab u v hvu
    unfold ccmCountableRemainder
    rw [sub_apply, sub_apply, inner_sub_left, inner_sub_left, Complex.sub_re, Complex.sub_re,
      literal_diagonal_eq_of_val_eq hab hvu, re_inner_ccmCountableBlock,
      re_inner_ccmCountableBlock]
    congr 1
    exact tsum_congr fun n => inserted_diagonal_eq_of_val_eq _ _ hab hvu

theorem countableFamily_Q_eq (P : CountablePrimePerturbation) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (countableFamily P).Q a u = ccmRestrictedWeilSourceQuadratic a u -
      ∑' n, (inner ℂ (ccmInsertedBlock a (P.x n) (P.w n) (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  rw [CCMRemainderFamily.Q_eq_form_re]
  show (inner ℂ u u + inner ℂ (ccmCountableRemainder a P (ccmArchimedeanFormToAperture a u))
    (ccmArchimedeanFormToAperture a u)).re = _
  unfold ccmCountableRemainder
  rw [sub_apply, inner_sub_left, ← add_sub_assoc, Complex.sub_re, re_inner_ccmCountableBlock]
  congr 1
  exact ccmRestrictedWeilForm_self_re_eq_source a u

/-- The Rayleigh floor of the countable family. -/
theorem countableFamily_energy_mul_le (P : CountablePrimePerturbation) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (countableFamily P).energy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u -
        ∑' n, (inner ℂ (ccmInsertedBlock a (P.x n) (P.w n) (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
  have := (countableFamily P).energy_mul_formNorm_sq_le a u
  rwa [countableFamily_Q_eq] at this

/-- The total budget of the countable block. -/
def countableBudget (P : CountablePrimePerturbation) : ℝ :=
  ∑' n, |P.w n| * (2 / Real.sqrt (P.x n))

theorem countableBudget_nonneg (P : CountablePrimePerturbation) : 0 ≤ countableBudget P :=
  tsum_nonneg fun n => by positivity

theorem summable_re_inner_insertedBlock (a : SuzukiPositiveAperture)
    (P : CountablePrimePerturbation) (f : suzukiApertureHilbert a) :
    Summable fun n => (inner ℂ (ccmInsertedBlock a (P.x n) (P.w n) f) f).re :=
  Summable.of_norm_bounded (P.budget_summable.mul_right (‖f‖ ^ 2)) fun n => by
    rw [Real.norm_eq_abs]
    exact abs_re_inner_insertedBlock_le a _ _ (by linarith [P.one_lt n]) f

theorem countableFamily_Q_le (P : CountablePrimePerturbation) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (countableFamily P).Q a u ≤
      literalFamily.Q a u + countableBudget P * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [countableFamily_Q_eq, literalFamily_Q_eq]
  set f := ccmArchimedeanFormToAperture a u with hf
  have hs := summable_re_inner_insertedBlock a P f
  have hb := P.budget_summable.mul_right (‖f‖ ^ 2)
  have hle : ∑' n, -(inner ℂ (ccmInsertedBlock a (P.x n) (P.w n) f) f).re ≤
      ∑' n, |P.w n| * (2 / Real.sqrt (P.x n)) * ‖f‖ ^ 2 := by
    refine Summable.tsum_le_tsum (fun n => ?_) hs.neg hb
    have h1 := abs_re_inner_insertedBlock_le a (P.x n) (P.w n) (by linarith [P.one_lt n]) f
    have h2 := neg_abs_le (inner ℂ (ccmInsertedBlock a (P.x n) (P.w n) f) f).re
    linarith
  rw [tsum_neg] at hle
  have hmul : ∑' n, |P.w n| * (2 / Real.sqrt (P.x n)) * ‖f‖ ^ 2 =
      countableBudget P * ‖f‖ ^ 2 := by
    unfold countableBudget
    exact P.budget_summable.tsum_mul_right _
  rw [hmul] at hle
  linarith

theorem countableFamily_energy_le (P : CountablePrimePerturbation) (a : SuzukiPositiveAperture) :
    (countableFamily P).energy a ≤ ccmRestrictedWeilGroundEnergy a + countableBudget P := by
  rw [← literalFamily_energy]
  exact CCMRemainderFamily.energy_le_energy_add_of_Q_le literalFamily (countableFamily P) a
    (countableFamily_Q_le P a)

theorem exists_countableFamily_energy_neg_of_not_riemannHypothesis (P : CountablePrimePerturbation)
    (hRH : ¬ RiemannHypothesis) :
    ∃ a : SuzukiPositiveAperture, (countableFamily P).energy a < 0 := by
  obtain ⟨a, ha⟩ := exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis hRH
    (countableBudget_nonneg P)
  exact ⟨a, by linarith [countableFamily_energy_le P a]⟩

/-! ## The block terms on the modulated wide bump -/

/-- The block pairing on the modulated bump, visible or not. -/
theorem re_inner_insertedBlock_modulatedBump' {L : ℝ} (hL : 1 ≤ L) (ζ x w : ℝ) :
    (inner ℂ (ccmInsertedBlock (wideBumpAperture L hL) x w
      (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL ζ).toCCMFormVector))
      (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL ζ).toCCMFormVector)).re =
      if x ≤ Real.exp (2 * (wideBumpAperture L hL).1) then
        w * (1 / Real.sqrt x) * (2 * Real.cos (ζ * Real.log x) * bumpOverlap L (Real.log x))
      else 0 := by
  split_ifs with hvis
  · exact re_inner_insertedBlock_modulatedBump hL ζ w hvis
  · rw [ccmInsertedBlock_of_invisible _ w hvis]
    simp

end RHTower.WeilDeletion

end
