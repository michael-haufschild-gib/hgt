import GaloisForLFunctions.RHTower.DeningerMeyerHasseHilbertDensity
import GaloisForLFunctions.RHTower.DeningerMeyerCausalReflectionCovariance

/-! # Bounded full-jet reflection and complementary-index operators -/

noncomputable section
open Complex Set

namespace RHTower

def deningerHasseJetReverse : Equiv.Perm DeningerArithmeticJetCoordinate where
  toFun q := ⟨q.1, q.2.rev⟩
  invFun q := ⟨q.1, q.2.rev⟩
  left_inv q := by cases q; simp
  right_inv q := by cases q; simp

@[simp] theorem deningerHasseJetReverse_apply (q : DeningerArithmeticJetCoordinate) :
    deningerHasseJetReverse q = ⟨q.1, q.2.rev⟩ := rfl

def deningerHasseJetReflect : Equiv.Perm DeningerArithmeticJetCoordinate :=
  Equiv.sigmaCongr xiZeroReflectEquiv
    (fun rho => finCongr (xiSupportMultiplicity_reflect rho).symm)

@[simp] theorem deningerHasseJetReflect_apply (q : DeningerArithmeticJetCoordinate) :
    deningerHasseJetReflect q = ⟨xiZeroReflectEquiv q.1,
      ⟨q.2.val, by rw [xiSupportMultiplicity_reflect]; exact q.2.isLt⟩⟩ := rfl

@[simp] theorem deningerHasseJetReflect_sq (q : DeningerArithmeticJetCoordinate) :
    deningerHasseJetReflect (deningerHasseJetReflect q) = q := by
  apply Sigma.ext (xiZeroReflectEquiv.apply_symm_apply q.1)
  apply (Fin.heq_ext_iff (by simp only [deningerHasseJetReflect_apply,
    xiSupportMultiplicity_reflect])).mpr
  rfl

@[simp] theorem deningerHasseJetReverse_sq (q : DeningerArithmeticJetCoordinate) :
    deningerHasseJetReverse (deningerHasseJetReverse q) = q := by
  cases q
  simp

theorem deningerHasseJetReverse_reflect (q : DeningerArithmeticJetCoordinate) :
    deningerHasseJetReverse (deningerHasseJetReflect q) =
      deningerHasseJetReflect (deningerHasseJetReverse q) := by
  simp only [deningerHasseJetReverse_apply, deningerHasseJetReflect_apply]
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply Fin.ext
  simp only [Fin.val_rev, xiSupportMultiplicity_reflect]

def deningerHasseHilbertReindex (e : Equiv.Perm DeningerArithmeticJetCoordinate) :
    DeningerArithmeticJetHilbert →ₗ[ℂ] DeningerArithmeticJetHilbert where
  toFun x := ⟨fun q => x (e q), memℓp_gen
    (e.summable_iff.mpr ((lp.memℓp x).summable (by norm_num)))⟩
  map_add' _ _ := lp.ext rfl
  map_smul' _ _ := lp.ext rfl

@[simp] theorem deningerHasseHilbertReindex_apply
    (e : Equiv.Perm DeningerArithmeticJetCoordinate) (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) : deningerHasseHilbertReindex e x q = x (e q) := rfl

theorem deningerHasseHilbertReindex_norm
    (e : Equiv.Perm DeningerArithmeticJetCoordinate) (x : DeningerArithmeticJetHilbert) :
    ‖deningerHasseHilbertReindex e x‖ = ‖x‖ := by
  have h (y : DeningerArithmeticJetHilbert) : ‖y‖ ^ 2 = ∑' q, ‖y q‖ ^ (2 : ℕ) := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) y
  have he : ‖deningerHasseHilbertReindex e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [h, h]
    exact e.tsum_eq (fun q => ‖x q‖ ^ (2 : ℕ))
  nlinarith [norm_nonneg x, norm_nonneg (deningerHasseHilbertReindex e x)]

/-- The original Paugam reflection, including every derivative parity. -/
def deningerHasseHilbertReflectLM :
    DeningerArithmeticJetHilbert →ₗ[ℂ] DeningerArithmeticJetHilbert where
  toFun x := ⟨fun q => (-1 : ℂ) ^ q.2.val * x (deningerHasseJetReflect q), by
    apply (lp.memℓp (deningerHasseHilbertReindex deningerHasseJetReflect x)).mono'
    intro q
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      deningerHasseHilbertReindex_apply]
    exact le_rfl⟩
  map_add' x y := by apply lp.ext; funext q; exact mul_add _ _ _
  map_smul' c x := by apply lp.ext; funext q; exact mul_left_comm _ _ _

@[simp] theorem deningerHasseHilbertReflectLM_apply (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerHasseHilbertReflectLM x q =
      (-1 : ℂ) ^ q.2.val * x (deningerHasseJetReflect q) := rfl

theorem deningerHasseHilbertReflectLM_norm_le (x : DeningerArithmeticJetHilbert) :
    ‖deningerHasseHilbertReflectLM x‖ ≤ ‖x‖ := by
  rw [← deningerHasseHilbertReindex_norm deningerHasseJetReflect x]
  apply lp.norm_mono (by norm_num)
  intro q
  simp

def deningerHasseHilbertReflectCLM :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  deningerHasseHilbertReflectLM.mkContinuous 1 (fun x => by
    simpa using deningerHasseHilbertReflectLM_norm_le x)

theorem deningerHasseHilbertReflect_single (q : DeningerArithmeticJetCoordinate) (c : ℂ) :
    deningerHasseHilbertReflectCLM (lp.single 2 q c) =
      lp.single 2 (deningerHasseJetReflect q) ((-1 : ℂ)^q.2.val * c) := by
  classical
  apply lp.ext
  funext r
  change (-1 : ℂ)^r.2.val *
    (lp.single 2 q c : DeningerArithmeticJetHilbert) (deningerHasseJetReflect r) = _
  by_cases hr : r = deningerHasseJetReflect q
  · subst r
    rw [deningerHasseJetReflect_sq, lp.single_apply_self, lp.single_apply_self]
    rfl
  · have hh : deningerHasseJetReflect r ≠ q := by
      intro h
      apply hr
      rw [← h, deningerHasseJetReflect_sq]
    rw [lp.single_apply_ne (E := fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q c hh,
      lp.single_apply_ne (E := fun _ : DeningerArithmeticJetCoordinate => ℂ) 2
        (deningerHasseJetReflect q) ((-1 : ℂ)^q.2.val * c) hr, mul_zero]

theorem deningerMeyerHasseJet_J (u : DeningerMeyerStrongLogCohomology)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseJet (deningerMeyerStrongLogCohomologyJ u) q =
      (-1 : ℂ) ^ q.2.val * deningerMeyerHasseJet u (deningerHasseJetReflect q) := by
  simp only [deningerMeyerHasseJet, deningerMeyerXiSupportJetEvaluationLM_J,
    deningerHasseJetReflect_apply, mul_div_assoc]

/-- The bounded Hilbert reflection agrees with the literal source reflection. -/
theorem deningerMeyerHasseHilbert_J (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyJ u) =
      deningerHasseHilbertReflectCLM (deningerMeyerHasseHilbertLM u) := by
  apply lp.ext
  funext q
  exact deningerMeyerHasseJet_J u q

end RHTower
