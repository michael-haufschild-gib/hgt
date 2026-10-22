import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyVerticalGauge
import GaloisForLFunctions.HTGeometry.GomesVerticalShearForms

/-!
# Invariant sesquilinear forms on rational-adelic Haar-shear cohomology

This applies the representation-category obstruction in Gomes, arXiv:2607.24901,
to the corpus's actual rational-adelic prime relative complex. The existing Stokes
splitting intertwines its Haar shear with the universal residual vertical shear.
All invariant sesquilinear forms descend uniquely to residual cohomology; the retained
ordinary-prime class lies in both radicals. Even the real Haar subgroup excludes a
strictly positive form, while the action itself remains faithful.
-/

noncomputable section
open GaloisForLFunctions GaloisForLFunctions.RHTower
namespace RHTower
open GaloisForLFunctions.HTGeometry

private abbrev H1 (p : Nat.Primes) := (ccmRationalAdelicPrimeRelativeComplex p).H1
private abbrev Residual (p : Nat.Primes) := CCMRationalAdelicPrimeResidualQuotient p

/-- The actual Haar-shear action on rational-adelic relative cohomology. -/
def gomesAdelicHaarAction (p : Nat.Primes) (z : ℂ) : H1 p →ₗ[ℂ] H1 p :=
  (ccmRationalAdelicPrimeVerticalShearHom p (ccmRationalAdelicPrimeHaarShear_mem p z)).H1map

/-- The existing Stokes splitting identifies the actual cohomological Haar action with the
universal vertical shear on residual cohomology times the retained class line. -/
theorem gomesAdelicHaarAction_split (p : Nat.Primes) (z : ℂ) (x : H1 p) :
    ccmRationalAdelicPrimeRelativeH1Equiv p (gomesAdelicHaarAction p z x) =
      gomesVerticalShear (ccmRationalAdelicPrimeResidualHaar p) z
        (ccmRationalAdelicPrimeRelativeH1Equiv p x) := by
  induction x using Submodule.Quotient.induction_on with
  | H w =>
    refine Prod.ext rfl ?_
    change ((w : CCMRationalAdelicPrimeRelativeOne).2 +
        z * ccmRationalAdelicBruhatIntegral (w : CCMRationalAdelicPrimeRelativeOne).1) -
        ccmRationalAdelicPrimeOrbitStokesLM p (w : CCMRationalAdelicPrimeRelativeOne).1 =
      (w : CCMRationalAdelicPrimeRelativeOne).2 -
        ccmRationalAdelicPrimeOrbitStokesLM p (w : CCMRationalAdelicPrimeRelativeOne).1 +
        z * ccmRationalAdelicBruhatIntegral (w : CCMRationalAdelicPrimeRelativeOne).1
    ring

/-- Inverse splitting transports the universal shear back to the actual cohomology action. -/
theorem gomesAdelicHaarAction_unsplit (p : Nat.Primes) (z : ℂ) (x : Residual p × ℂ) :
    gomesAdelicHaarAction p z ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm x) =
      (ccmRationalAdelicPrimeRelativeH1Equiv p).symm
        (gomesVerticalShear (ccmRationalAdelicPrimeResidualHaar p) z x) := by
  apply (ccmRationalAdelicPrimeRelativeH1Equiv p).injective
  rw [gomesAdelicHaarAction_split,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

/-- Sesquilinear forms expressed in the actual residual/Stokes splitting. -/
def gomesAdelicSplitSesqForm (p : Nat.Primes)
    (B : H1 p →ₛₗ[starRingEnd ℂ] H1 p →ₗ[ℂ] ℂ) :
    (Residual p × ℂ) →ₛₗ[starRingEnd ℂ] (Residual p × ℂ) →ₗ[ℂ] ℂ :=
  (B.comp (ccmRationalAdelicPrimeRelativeH1Equiv p).symm.toLinearMap).compl₂
    (ccmRationalAdelicPrimeRelativeH1Equiv p).symm.toLinearMap

/-- Invariant-form transport is exact for the actual Haar action and its residual model. -/
theorem gomesAdelicHaarAction_sesq_transport (p : Nat.Primes)
    (B : H1 p →ₛₗ[starRingEnd ℂ] H1 p →ₗ[ℂ] ℂ) :
    (∀ z : ℂ, ∀ x y : H1 p, B (gomesAdelicHaarAction p z x)
      (gomesAdelicHaarAction p z y) = B x y) ↔
    (∀ z : ℂ, ∀ x y : Residual p × ℂ,
      gomesAdelicSplitSesqForm p B
        (gomesVerticalShear (ccmRationalAdelicPrimeResidualHaar p) z x)
        (gomesVerticalShear (ccmRationalAdelicPrimeResidualHaar p) z y) =
        gomesAdelicSplitSesqForm p B x y) := by
  constructor
  · intro h z x y
    change B ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
        (gomesVerticalShear (ccmRationalAdelicPrimeResidualHaar p) z x))
      ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
        (gomesVerticalShear (ccmRationalAdelicPrimeResidualHaar p) z y)) = _
    rw [← gomesAdelicHaarAction_unsplit,← gomesAdelicHaarAction_unsplit]
    exact h z _ _
  · intro h z x y
    have hc := h z (ccmRationalAdelicPrimeRelativeH1Equiv p x)
      (ccmRationalAdelicPrimeRelativeH1Equiv p y)
    change B ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
        (gomesVerticalShear (ccmRationalAdelicPrimeResidualHaar p) z
          (ccmRationalAdelicPrimeRelativeH1Equiv p x)))
      ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
        (gomesVerticalShear (ccmRationalAdelicPrimeResidualHaar p) z
          (ccmRationalAdelicPrimeRelativeH1Equiv p y))) = _ at hc
    rw [← gomesAdelicHaarAction_split,← gomesAdelicHaarAction_split] at hc
    simpa only [gomesAdelicSplitSesqForm,LinearMap.compl₂_apply,LinearMap.comp_apply,
      LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hc

/-- Every complex Haar-invariant sesquilinear form annihilates the retained class in both slots,
and this radical condition is sufficient. The statement is on actual relative cohomology. -/
theorem gomesAdelicHaarAction_invariant_forms (p : Nat.Primes)
    (B : H1 p →ₛₗ[starRingEnd ℂ] H1 p →ₗ[ℂ] ℂ) :
    (∀ z : ℂ, ∀ x y : H1 p, B (gomesAdelicHaarAction p z x)
      (gomesAdelicHaarAction p z y) = B x y) ↔
    ∀ x : H1 p, B (ccmRationalAdelicPrimeRelativeClass p) x = 0 ∧
      B x (ccmRationalAdelicPrimeRelativeClass p) = 0 := by
  have hm : (ccmRationalAdelicPrimeRelativeH1Equiv p).symm (0,1) =
      ccmRationalAdelicPrimeRelativeClass p := by
    apply (ccmRationalAdelicPrimeRelativeH1Equiv p).injective
    rw [LinearEquiv.apply_symm_apply,ccmRationalAdelicPrimeRelativeH1Equiv_class]
  rw [gomesAdelicHaarAction_sesq_transport,gomesVerticalShear_sesq_invariants,
    or_iff_right (ccmRationalAdelicPrimeResidualHaar_ne_zero p)]
  constructor
  · intro h x
    have hx := h (ccmRationalAdelicPrimeRelativeH1Equiv p x)
    change B ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm (0,1))
        ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
          (ccmRationalAdelicPrimeRelativeH1Equiv p x)) = 0 ∧
      B ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
          (ccmRationalAdelicPrimeRelativeH1Equiv p x))
        ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm (0,1)) = 0 at hx
    simpa only [hm,LinearEquiv.symm_apply_apply] using hx
  · intro h x
    change B ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm (0,1))
        ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm x) = 0 ∧
      B ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm x)
        ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm (0,1)) = 0
    rw [hm]
    exact h _

/-- The Haar action is faithful on actual relative cohomology for every ordinary prime. -/
theorem gomesAdelicHaarAction_faithful (p : Nat.Primes) (z w : ℂ) :
    gomesAdelicHaarAction p z = gomesAdelicHaarAction p w ↔ z = w := by
  constructor
  · intro h
    have hw := LinearMap.congr_fun h
      (Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p))
    simp only [gomesAdelicHaarAction,ccmRationalAdelicPrimeHaarShear_H1map_witness] at hw
    have hs := congrArg (ccmRationalAdelicPrimeRelativeH1StokesRegulator p) hw
    simp only [map_add,map_smul,ccmRationalAdelicPrimeRelativeH1StokesRegulator_class,
      smul_eq_mul,mul_one] at hs
    exact mul_right_cancel₀ (ccmRationalAdelicHaarWitness_integral_ne_zero p) (add_left_cancel hs)
  · rintro rfl
    rfl

/-- Even the real Haar-shear subgroup rules out every strictly positive sesquilinear form on
actual relative cohomology. No Hermitian assumption is needed for this obstruction. -/
theorem gomesAdelicHaarAction_no_positive_metric (p : Nat.Primes) :
    ¬ ∃ B : H1 p →ₛₗ[starRingEnd ℂ] H1 p →ₗ[ℂ] ℂ,
      (∀ x : H1 p, x ≠ 0 → 0 < (B x x).re) ∧
      (∀ t : ℝ, ∀ x y : H1 p, B (gomesAdelicHaarAction p (t : ℂ) x)
        (gomesAdelicHaarAction p (t : ℂ) y) = B x y) := by
  rintro ⟨B,hpos,hinv⟩
  let c := ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p)
  let e := c • ccmRationalAdelicPrimeRelativeClass p
  let w : H1 p := Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p)
  have he : e ≠ 0 := smul_ne_zero (ccmRationalAdelicHaarWitness_integral_ne_zero p)
    (ccmRationalAdelicPrimeRelativeClass_ne_zero p)
  have hl : ∀ t : ℝ, B (w + (t : ℂ) • e) (w + (t : ℂ) • e) = B w w := by
    intro t
    have ht := hinv t w w
    simpa only [gomesAdelicHaarAction,w,e,c,ccmRationalAdelicPrimeHaarShear_H1map_witness,
      smul_smul] using ht
  have hz := ((sesq_real_affine_line_constant_iff B e w).mp hl).1
  have hp := hpos e he
  rw [hz,Complex.zero_re] at hp
  exact lt_irrefl _ hp

/-- Pullback of a residual-cohomology sesquilinear form to actual relative cohomology. -/
def gomesAdelicResidualSesqPullback (p : Nat.Primes)
    (C : Residual p →ₛₗ[starRingEnd ℂ] Residual p →ₗ[ℂ] ℂ) :
    H1 p →ₛₗ[starRingEnd ℂ] H1 p →ₗ[ℂ] ℂ :=
  (C.comp ((LinearMap.fst ℂ (Residual p) ℂ).comp
    (ccmRationalAdelicPrimeRelativeH1Equiv p).toLinearMap)).compl₂
      ((LinearMap.fst ℂ (Residual p) ℂ).comp
        (ccmRationalAdelicPrimeRelativeH1Equiv p).toLinearMap)

/-- The concrete residual pullback agrees exactly with the universal quotient pullback under
the actual Stokes splitting. -/
theorem gomesAdelicResidualSesqPullback_split (p : Nat.Primes)
    (C : Residual p →ₛₗ[starRingEnd ℂ] Residual p →ₗ[ℂ] ℂ) :
    gomesAdelicSplitSesqForm p (gomesAdelicResidualSesqPullback p C) =
      gomesResidualSesqPullback C := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change C ((ccmRationalAdelicPrimeRelativeH1Equiv p)
      ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm x)).1
    ((ccmRationalAdelicPrimeRelativeH1Equiv p)
      ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm y)).1 = C x.1 y.1
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

/-- Expressing a sesquilinear form in the Stokes splitting loses no information. -/
theorem gomesAdelicSplitSesqForm_injective (p : Nat.Primes) :
    Function.Injective (gomesAdelicSplitSesqForm p) := by
  intro B C h
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hc := congrArg (fun F => F (ccmRationalAdelicPrimeRelativeH1Equiv p x)
    (ccmRationalAdelicPrimeRelativeH1Equiv p y)) h
  change B ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
      (ccmRationalAdelicPrimeRelativeH1Equiv p x))
    ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
      (ccmRationalAdelicPrimeRelativeH1Equiv p y)) =
      C ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
        (ccmRationalAdelicPrimeRelativeH1Equiv p x))
      ((ccmRationalAdelicPrimeRelativeH1Equiv p).symm
        (ccmRationalAdelicPrimeRelativeH1Equiv p y)) at hc
  simpa only [LinearEquiv.symm_apply_apply] using hc

/-- The positive survivor is exact and unique: invariant sesquilinear forms on actual adelic
cohomology are precisely pullbacks of arbitrary forms on the existing residual quotient. -/
theorem gomesAdelicHaarAction_unique_residual_form (p : Nat.Primes)
    (B : H1 p →ₛₗ[starRingEnd ℂ] H1 p →ₗ[ℂ] ℂ) :
    (∀ z : ℂ, ∀ x y : H1 p, B (gomesAdelicHaarAction p z x)
      (gomesAdelicHaarAction p z y) = B x y) ↔
      ∃! C : Residual p →ₛₗ[starRingEnd ℂ] Residual p →ₗ[ℂ] ℂ,
        B = gomesAdelicResidualSesqPullback p C := by
  rw [gomesAdelicHaarAction_sesq_transport,gomesVerticalShear_unique_residual_form,
    or_iff_right (ccmRationalAdelicPrimeResidualHaar_ne_zero p)]
  constructor
  · rintro ⟨C,hC,hunique⟩
    refine ⟨C,?_,?_⟩
    · apply gomesAdelicSplitSesqForm_injective p
      rw [gomesAdelicResidualSesqPullback_split]
      exact hC
    · intro D hD
      apply hunique D
      rw [hD,gomesAdelicResidualSesqPullback_split]
  · rintro ⟨C,hC,hunique⟩
    refine ⟨C,?_,?_⟩
    · rw [hC,gomesAdelicResidualSesqPullback_split]
    · intro D hD
      apply hunique D
      apply gomesAdelicSplitSesqForm_injective p
      rw [gomesAdelicResidualSesqPullback_split]
      exact hD

end RHTower
