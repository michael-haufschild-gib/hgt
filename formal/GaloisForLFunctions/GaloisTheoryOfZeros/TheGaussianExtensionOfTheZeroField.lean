import GaloisForLFunctions.GaloisTheoryOfZeros.TheFieldOfCompleteFibreTraces
import GaloisForLFunctions.HTGeometry.QuadraticRootConjugation
import GaloisForLFunctions.HTGeometry.QuadraticSemilinearInvolution
import GaloisForLFunctions.HTGeometry.QuadraticRepresentation
import GaloisForLFunctions.HTGeometry.AdjoinInsert
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Algebra.Ring.Int.Units

/-!
# Original zero coordinates and the Gaussian extension

Adjoining `i` to the complete centered zero field gives exactly the field of
all original zeros and `i`. It remains normal over the real source field.
Ordinary conjugation is central, and every zero orbit is finite.

Functional-equation reflection lifts uniquely precisely when `-1` is not a
square in the centered field. In that regime restriction and Gaussian sign
identify the full infinite Galois group with the centered group times `C₂`.
If `i` already belongs to the centered field, the extension collapses and no
functional-equation lift exists. These alternatives require no assumption
about the location or simplicity of the zeros.
-/

noncomputable section
set_option autoImplicit false
open Complex Polynomial Set RHTower
open scoped IntermediateField

namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Any field automorphism sends the Gaussian unit to one of its two roots. -/
private theorem gaussianUnit_image {E : Subfield ℂ} (hi : I ∈ E) (σ : E ≃+* E) :
    (σ ⟨I, hi⟩ : ℂ) = I ∨ (σ ⟨I, hi⟩ : ℂ) = -I := by
  have hs : (⟨I, hi⟩ : E)^2 = -1 := by
    apply Subtype.ext
    exact Complex.I_sq
  have hs' : (σ ⟨I, hi⟩ : ℂ)^2 = -1 := by
    have h := congrArg σ hs
    rw [map_pow, map_neg, map_one] at h
    exact_mod_cast h
  have hp : ((σ ⟨I, hi⟩ : ℂ)-I) * ((σ ⟨I, hi⟩ : ℂ)+I) = 0 := by
    calc
      _ = (σ ⟨I, hi⟩ : ℂ)^2 - I^2 := by ring
      _ = 0 := by rw [hs', I_sq, sub_self]
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- Absence of the Gaussian unit is exactly nonsquareness of minus one. -/
private theorem not_isSquare_neg_one_of_I_not_mem (E : Subfield ℂ) (hi : I ∉ E) :
    ¬ IsSquare (-1 : E) := by
  rintro ⟨a, ha⟩
  have hs : (a : ℂ)^2 = -1 := by
    have h := congrArg (fun z : E => (z : ℂ)) ha
    change (-1 : ℂ) = (a : ℂ)*(a : ℂ) at h
    exact (pow_two _).trans h.symm
  have hp : ((a : ℂ)-I) * ((a : ℂ)+I) = 0 := by
    calc
      _ = (a : ℂ)^2-I^2 := by ring
      _ = 0 := by rw [hs, I_sq, sub_self]
  rcases mul_eq_zero.mp hp with h | h
  · exact hi ((sub_eq_zero.mp h) ▸ a.property)
  · have he : (a : ℂ) = -I := eq_neg_of_add_eq_zero_left h
    have hn := E.neg_mem a.property
    exact hi (by simpa only [he, neg_neg] using hn)

/-- The Gaussian quadratic involution fixes the original field and reverses `i`. -/
private def gaussianQuadraticConjugation (E : Subfield ℂ) (hi : I ∉ E) :
    E⟮I⟯ ≃ₐ[E] E⟮I⟯ :=
  HTGeometry.quadraticRootConjugation
    (show I*I = algebraMap E ℂ (-1) by simp only [I_mul_I, map_neg, map_one])
    (not_isSquare_neg_one_of_I_not_mem E hi)

private theorem gaussianQuadraticConjugation_I (E : Subfield ℂ) (hi : I ∉ E) :
    gaussianQuadraticConjugation E hi ⟨I, IntermediateField.mem_adjoin_simple_self E I⟩ =
      -⟨I, IntermediateField.mem_adjoin_simple_self E I⟩ :=
  HTGeometry.quadraticRootConjugation_gen _ _

/-- Adjoining the missing Gaussian unit is a normal quadratic extension. -/
private theorem gaussianExtension_normal (E : Subfield ℂ) (hi : I ∉ E) :
    Normal E E⟮I⟯ := by
  have hbot : I ∉ (⊥ : IntermediateField E ℂ) := by
    intro h
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp h
    exact hi (ha ▸ a.property)
  have hr : I*I = algebraMap E ℂ (-1) := by
    simp only [I_mul_I, map_neg, map_one]
  letI : Algebra.IsQuadraticExtension E E⟮I⟯ :=
    { toFree := inferInstance
      finrank_eq_two' := HTGeometry.finrank_adjoin_eq_two hr hbot }
  infer_instance

/-- The complete zero field with the Gaussian unit, in the original zero coordinate. -/
def gaussianZeroExtension : IntermediateField fullFibreSourceField ℂ :=
  (fullFibreZeroExtension⟮I⟯).restrictScalars fullFibreSourceField

instance gaussianZeroExtension_algebra :
    Algebra fullFibreZeroExtension gaussianZeroExtension :=
  inferInstanceAs (Algebra fullFibreZeroExtension fullFibreZeroExtension⟮I⟯)

instance gaussianZeroExtension_sourceTower :
    IsScalarTower fullFibreSourceField fullFibreZeroExtension gaussianZeroExtension :=
  inferInstanceAs (IsScalarTower fullFibreSourceField fullFibreZeroExtension
    fullFibreZeroExtension⟮I⟯)

instance gaussianZeroExtension_complexTower :
    IsScalarTower fullFibreZeroExtension gaussianZeroExtension ℂ :=
  inferInstanceAs (IsScalarTower fullFibreZeroExtension fullFibreZeroExtension⟮I⟯ ℂ)

/-- The centered zeros and the Gaussian unit generate the full extension. -/
theorem gaussianZeroExtension_eq_adjoin :
    gaussianZeroExtension = IntermediateField.adjoin fullFibreSourceField
      (insert I (Set.range xiSpectralPoint)) :=
  HTGeometry.adjoin_insert_eq_restrictScalars _ _

/-- The centered zero field embeds into the Gaussian extension. -/
theorem zeroExtension_le_gaussian : fullFibreZeroExtension ≤ gaussianZeroExtension := by
  rw [gaussianZeroExtension, IntermediateField.restrictScalars_adjoin_eq_sup]
  exact le_sup_left

private theorem gaussianUnit_mem_extension : I ∈ gaussianZeroExtension :=
  IntermediateField.mem_adjoin_simple_self fullFibreZeroExtension I

/-- A centered zero embedded in the Gaussian extension. -/
def centeredZeroInGaussianExtension (q : XiZeroCopy) : gaussianZeroExtension :=
  ⟨xiSpectralPoint q, zeroExtension_le_gaussian (centeredZeroInFibreExtension q).property⟩

/-- The Gaussian unit in the full extension. -/
def gaussianUnit : gaussianZeroExtension := ⟨I, gaussianUnit_mem_extension⟩

/-- The original zero coordinate `ρ=1/2+iw`. -/
def originalZeroInGaussianExtension (q : XiZeroCopy) : gaussianZeroExtension :=
  1/2 + gaussianUnit * centeredZeroInGaussianExtension q

private theorem gaussianUnit_not_mem_sourceField : I ∉ fullFibreSourceField := by
  intro hi
  obtain ⟨x, hx⟩ := fullFibreSourceField_le_real hi
  have h := congrArg Complex.im hx
  norm_num at h

/-- Every source automorphism still preserves each centered ordinate fibre after adjoining `i`. -/
theorem gaussian_aut_preserves_centered_fibre
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension)
    (q : XiZeroCopy) :
    ∃ q' ∈ ordinateFibreCopies (xiSpectralPoint q).re,
      (σ (centeredZeroInGaussianExtension q) : ℂ) = xiSpectralPoint q' :=
  sourceFibrePolynomial_aut_image gaussianZeroExtension σ q
    (centeredZeroInGaussianExtension q).property

/-- Some zero has nonzero ordinate: a single finite fibre cannot exhaust the zero carrier. -/
private theorem exists_nonzero_ordinate : ∃ q : XiZeroCopy, (xiSpectralPoint q).re ≠ 0 := by
  by_contra h
  push Not at h
  apply range_xiSpectralPoint_infinite
  apply ((ordinateFibreCopies 0).finite_toSet.image xiSpectralPoint).subset
  rintro z ⟨q, rfl⟩
  exact ⟨q, (mem_ordinateFibreCopies 0 q).mpr (h q), rfl⟩

theorem originalZeroInGaussianExtension_coe (q : XiZeroCopy) :
    (originalZeroInGaussianExtension q : ℂ) = q.1 := by
  change 1/2 + I * xiSpectralPoint q = (q.1 : ℂ)
  rw [xiSpectralPoint, mul_left_comm, mul_neg, I_mul_I, neg_neg, mul_one]
  ring

private theorem conj_mem_gaussianZeroExtension (z : ℂ) (hz : z ∈ gaussianZeroExtension) :
    (starRingEnd ℂ) z ∈ gaussianZeroExtension := by
  have hstable : gaussianZeroExtension.toSubfield ≤
      gaussianZeroExtension.toSubfield.comap (starRingEnd ℂ) := by
    rw [gaussianZeroExtension_eq_adjoin, IntermediateField.adjoin_toSubfield]
    apply Subfield.closure_le.mpr
    rintro a (⟨k, rfl⟩ | ha)
    · change (starRingEnd ℂ) (k : ℂ) ∈ Subfield.closure
        (Set.range (algebraMap fullFibreSourceField ℂ) ∪ insert I (Set.range xiSpectralPoint))
      obtain ⟨x, hx⟩ := fullFibreSourceField_le_real k.property
      have hk : (starRingEnd ℂ) (k : ℂ) = (k : ℂ) := by rw [← hx]; simp
      rw [hk]
      exact Subfield.subset_closure (Or.inl ⟨k, rfl⟩)
    · rcases ha with rfl | ⟨q, rfl⟩
      · change (starRingEnd ℂ) I ∈ Subfield.closure
          (Set.range (algebraMap fullFibreSourceField ℂ) ∪ insert I (Set.range xiSpectralPoint))
        rw [Complex.conj_I]
        exact Subfield.neg_mem _ (Subfield.subset_closure (Or.inr (Or.inl rfl)))
      · change (starRingEnd ℂ) (xiSpectralPoint q) ∈ Subfield.closure
          (Set.range (algebraMap fullFibreSourceField ℂ) ∪ insert I (Set.range xiSpectralPoint))
        rw [← xiSpectralPoint_lineConj]
        exact Subfield.subset_closure (Or.inr (Or.inr ⟨_, rfl⟩))
  exact hstable hz

/-- Ordinary complex conjugation on the field containing all original zeros and `i`. -/
def gaussianZeroConjugation : gaussianZeroExtension ≃ₐ[fullFibreSourceField]
    gaussianZeroExtension where
  toFun z := ⟨(starRingEnd ℂ) z.1, conj_mem_gaussianZeroExtension z.1 z.2⟩
  invFun z := ⟨(starRingEnd ℂ) z.1, conj_mem_gaussianZeroExtension z.1 z.2⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; exact map_mul (starRingEnd ℂ) x.1 y.1
  map_add' x y := by apply Subtype.ext; exact map_add (starRingEnd ℂ) x.1 y.1
  commutes' k := by
    apply Subtype.ext
    change (starRingEnd ℂ) (k : ℂ) = (k : ℂ)
    obtain ⟨x, hx⟩ := fullFibreSourceField_le_real k.property
    rw [← hx]
    simp

private theorem conj_eq_ordinate_reflection_gaussian {z : ℂ} {t : ℝ} (ht : z.re = t) :
    (starRingEnd ℂ) z = 2*(t:ℂ)-z := by
  apply Complex.ext
  · change z.re = 2*t-0*0-z.re
    linarith only [ht]
  · simp

/-- Adjoining the Gaussian unit preserves normality over the real source field. -/
instance gaussianZeroExtension_normal : Normal fullFibreSourceField gaussianZeroExtension := by
  letI : Normal fullFibreSourceField fullFibreSourceField⟮I⟯ :=
    gaussianExtension_normal fullFibreSourceField gaussianUnit_not_mem_sourceField
  rw [gaussianZeroExtension, IntermediateField.restrictScalars_adjoin_eq_sup]
  infer_instance

private theorem gaussian_aut_unit
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) :
    σ gaussianUnit = gaussianUnit ∨ σ gaussianUnit = -gaussianUnit := by
  rcases gaussianUnit_image (E := gaussianZeroExtension.toSubfield)
    gaussianUnit_mem_extension σ.toRingEquiv with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- Ordinary conjugation is central on the entire original-coordinate zero field. -/
theorem gaussianZeroConjugation_central
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) :
    gaussianZeroConjugation.trans σ = σ.trans gaussianZeroConjugation := by
  have hI : gaussianZeroConjugation gaussianUnit = -gaussianUnit := by
    apply Subtype.ext
    exact Complex.conj_I
  have hunit : σ (gaussianZeroConjugation gaussianUnit) =
      gaussianZeroConjugation (σ gaussianUnit) := by
    rw [hI, map_neg]
    rcases gaussian_aut_unit σ with h | h
    · rw [h, hI]
    · rw [h, map_neg, hI]
  have hzero (q : XiZeroCopy) :
      σ (gaussianZeroConjugation (centeredZeroInGaussianExtension q)) =
        gaussianZeroConjugation (σ (centeredZeroInGaussianExtension q)) := by
    let t : fullFibreSourceField :=
      ⟨((xiSpectralPoint q).re : ℂ), ordinate_mem_fullFibreSourceField q⟩
    let a : gaussianZeroExtension := algebraMap fullFibreSourceField gaussianZeroExtension t
    have hqconj : gaussianZeroConjugation (centeredZeroInGaussianExtension q) =
        2*a-centeredZeroInGaussianExtension q := by
      apply Subtype.ext
      exact conj_eq_ordinate_reflection_gaussian rfl
    obtain ⟨q', hq', heq⟩ := gaussian_aut_preserves_centered_fibre σ q
    have hre : (σ (centeredZeroInGaussianExtension q) : ℂ).re = (xiSpectralPoint q).re := by
      rw [heq]
      exact (mem_ordinateFibreCopies _ q').mp hq'
    have hσconj : gaussianZeroConjugation (σ (centeredZeroInGaussianExtension q)) =
        2*a-σ (centeredZeroInGaussianExtension q) := by
      apply Subtype.ext
      exact conj_eq_ordinate_reflection_gaussian hre
    rw [hqconj, hσconj, map_sub, map_mul, map_ofNat, σ.commutes t]
  have heq := IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
    (S := gaussianZeroExtension) gaussianZeroExtension_eq_adjoin
    (φ₁ := (gaussianZeroConjugation.trans σ).toAlgHom)
    (φ₂ := (σ.trans gaussianZeroConjugation).toAlgHom)
    (by
      intro z hz
      rcases hz with rfl | ⟨q, rfl⟩
      · exact hunit
      · exact hzero q)
  apply AlgEquiv.ext
  intro z
  exact DFunLike.congr_fun heq z

/-- Any functional-equation lift reverses the Gaussian unit. -/
theorem gaussian_reflection_forces_flip
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension)
    (hρ : ∀ q, σ (originalZeroInGaussianExtension q) =
      1-originalZeroInGaussianExtension q) : σ gaussianUnit = -gaussianUnit := by
  rcases gaussian_aut_unit σ with hI | hI
  · obtain ⟨q, hq⟩ := exists_nonzero_ordinate
    have hr := congrArg (fun x : gaussianZeroExtension => (x : ℂ)) (hρ q)
    simp only [originalZeroInGaussianExtension, map_add, map_div₀, map_one,
      map_ofNat, map_mul, hI] at hr
    change 1/2 + I*(σ (centeredZeroInGaussianExtension q) : ℂ) =
      1-(1/2+I*xiSpectralPoint q) at hr
    have hs : (σ (centeredZeroInGaussianExtension q) : ℂ) = -xiSpectralPoint q := by
      have hp : I*((σ (centeredZeroInGaussianExtension q) : ℂ)+xiSpectralPoint q) = 0 := by
        linear_combination hr
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hp).resolve_left I_ne_zero)
    obtain ⟨q', hq', heq⟩ := gaussian_aut_preserves_centered_fibre σ q
    have hre := (mem_ordinateFibreCopies _ q').mp hq'
    have hneg := congrArg Complex.re (heq.symm.trans hs)
    simp only [Complex.neg_re] at hneg
    exact (hq (by linarith only [hre, hneg])).elim
  · exact hI

/-- Any functional-equation lift fixes every centered zero. -/
theorem gaussian_reflection_fixes_centered
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension)
    (hρ : ∀ q, σ (originalZeroInGaussianExtension q) =
      1-originalZeroInGaussianExtension q) (q : XiZeroCopy) :
    σ (centeredZeroInGaussianExtension q) = centeredZeroInGaussianExtension q := by
  have hI := gaussian_reflection_forces_flip σ hρ
  have hr := congrArg (fun x : gaussianZeroExtension => (x : ℂ)) (hρ q)
  simp only [originalZeroInGaussianExtension, map_add, map_div₀, map_one,
    map_ofNat, map_mul, hI] at hr
  change 1/2 + (-I)*(σ (centeredZeroInGaussianExtension q) : ℂ) =
    1-(1/2+I*xiSpectralPoint q) at hr
  apply Subtype.ext
  have hp : I*((σ (centeredZeroInGaussianExtension q) : ℂ)-xiSpectralPoint q) = 0 := by
    linear_combination -hr
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left I_ne_zero)

/-- Functional-equation reflection lifts exactly when the centered zero field omits `i`. -/
theorem functional_equation_lift_iff :
    (∃ σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension,
      ∀ q, σ (originalZeroInGaussianExtension q) = 1-originalZeroInGaussianExtension q) ↔
    I ∉ fullFibreZeroExtension := by
  constructor
  · rintro ⟨σ, hρ⟩ hi
    let ι := IntermediateField.inclusion zeroExtension_le_gaussian
    have heq : σ.toAlgHom.comp ι = ι :=
      IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
        (S := fullFibreZeroExtension) rfl
        (by rintro z ⟨q, rfl⟩; exact gaussian_reflection_fixes_centered σ hρ q)
    have hfixed : σ gaussianUnit = gaussianUnit :=
      DFunLike.congr_fun heq (⟨I, hi⟩ : fullFibreZeroExtension)
    have hflip := gaussian_reflection_forces_flip σ hρ
    have he : (I : ℂ) = -I := congrArg (fun x : gaussianZeroExtension => (x : ℂ))
      (hfixed.symm.trans hflip)
    have := congrArg Complex.im he
    norm_num at this
  · intro hi
    let e : fullFibreZeroExtension⟮I⟯ ≃ₐ[fullFibreZeroExtension]
        fullFibreZeroExtension⟮I⟯ :=
      gaussianQuadraticConjugation fullFibreZeroExtension.toSubfield hi
    let σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension :=
      e.restrictScalars fullFibreSourceField
    have hI : σ gaussianUnit = -gaussianUnit :=
      gaussianQuadraticConjugation_I fullFibreZeroExtension.toSubfield hi
    have hw (q : XiZeroCopy) : σ (centeredZeroInGaussianExtension q) =
        centeredZeroInGaussianExtension q := e.commutes (centeredZeroInFibreExtension q)
    refine ⟨σ, fun q => ?_⟩
    simp only [originalZeroInGaussianExtension, map_add, map_div₀, map_one,
      map_ofNat, map_mul, hI, hw]
    ring

/-- The Gaussian extension is precisely the field of all original zeros and `i`. -/
theorem gaussianZeroExtension_toSubfield :
    gaussianZeroExtension.toSubfield =
      Subfield.closure (insert I (Set.range fun q : XiZeroCopy => (q.1 : ℂ))) := by
  let E := Subfield.closure (insert I (Set.range fun q : XiZeroCopy => (q.1 : ℂ)))
  have hi : I ∈ E := Subfield.subset_closure (Or.inl rfl)
  have hw (q : XiZeroCopy) : xiSpectralPoint q ∈ E := by
    rw [xiSpectralPoint]
    exact E.mul_mem
      (E.sub_mem (Subfield.subset_closure (Or.inr ⟨q, rfl⟩))
        (E.div_mem E.one_mem (natCast_mem E 2))) (E.neg_mem hi)
  have hL : Subfield.closure (Set.range xiSpectralPoint) ≤ E := by
    apply Subfield.closure_le.mpr
    rintro z ⟨q, rfl⟩
    exact hw q
  apply le_antisymm
  · rw [gaussianZeroExtension_eq_adjoin, IntermediateField.adjoin_toSubfield]
    apply Subfield.closure_le.mpr
    rintro z (⟨k, rfl⟩ | hz)
    · exact hL (fullFibreSourceField_le_zeroClosure k.property)
    · rcases hz with rfl | ⟨q, rfl⟩
      · exact hi
      · exact hw q
  · apply Subfield.closure_le.mpr
    rintro z (rfl | ⟨q, rfl⟩)
    · exact gaussianUnit_mem_extension
    · change (q.1 : ℂ) ∈ gaussianZeroExtension.toSubfield
      rw [← originalZeroInGaussianExtension_coe q]
      exact (originalZeroInGaussianExtension q).property

/-- Original-coordinate zero orbits are finite in the entire Gaussian extension. -/
theorem gaussian_original_zero_orbit_finite (q : XiZeroCopy) :
    (Set.range fun σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension =>
      (σ (originalZeroInGaussianExtension q) : ℂ)).Finite := by
  let S : Set XiZeroCopy := ↑(ordinateFibreCopies (xiSpectralPoint q).re)
  have hS : S.Finite := (ordinateFibreCopies _).finite_toSet
  apply ((hS.image (fun q' => (1/2 : ℂ)+I*xiSpectralPoint q')).union
    (hS.image (fun q' => (1/2 : ℂ)-I*xiSpectralPoint q'))).subset
  rintro z ⟨σ, rfl⟩
  obtain ⟨q', hq', heq⟩ := gaussian_aut_preserves_centered_fibre σ q
  have hr : (σ (originalZeroInGaussianExtension q) : ℂ) =
      1/2+(σ gaussianUnit : ℂ)*(σ (centeredZeroInGaussianExtension q) : ℂ) := by
    simp only [originalZeroInGaussianExtension, map_add, map_div₀, map_one,
      map_ofNat, map_mul]
    rfl
  rcases gaussian_aut_unit σ with hI | hI
  · left
    refine ⟨q', hq', ?_⟩
    change 1/2+I*xiSpectralPoint q' = (σ (originalZeroInGaussianExtension q) : ℂ)
    rw [hr, hI, heq]
    rfl
  · right
    refine ⟨q', hq', ?_⟩
    change 1/2-I*xiSpectralPoint q' = (σ (originalZeroInGaussianExtension q) : ℂ)
    rw [hr, hI, heq]
    change 1/2-I*xiSpectralPoint q' = 1/2+(-I)*xiSpectralPoint q'
    ring

/-- Every element is a linear expression in the Gaussian unit over the centered zero field. -/
theorem gaussian_element_repr (z : gaussianZeroExtension) :
    ∃ a b : fullFibreZeroExtension, (z : ℂ) = (a : ℂ)+(b : ℂ)*I :=
  HTGeometry.exists_repr_of_mem_adjoin_sqrt
    (show I*I = algebraMap fullFibreZeroExtension ℂ (-1) by
      simp only [I_mul_I, map_neg, map_one]) z.property

/-- Gaussian expressions are unique when the centered field omits `i`. -/
theorem gaussian_element_repr_unique (hi : I ∉ fullFibreZeroExtension)
    (a b a' b' : fullFibreZeroExtension)
    (he : (a : ℂ)+(b : ℂ)*I = (a' : ℂ)+(b' : ℂ)*I) : a = a' ∧ b = b' := by
  have hb : b = b' := by
    by_contra hb
    have hbC : (b : ℂ)-(b' : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hb (Subtype.ext h))
    have hI : I = ((a' : ℂ)-(a : ℂ))/((b : ℂ)-(b' : ℂ)) := by
      apply (eq_div_iff hbC).mpr
      linear_combination he
    apply hi
    rw [hI]
    exact fullFibreZeroExtension.div_mem
      (fullFibreZeroExtension.sub_mem a'.property a.property)
      (fullFibreZeroExtension.sub_mem b.property b'.property)
  refine ⟨?_, hb⟩
  apply Subtype.ext
  rw [hb] at he
  exact add_right_cancel he

private theorem gaussianUnit_square_zeroField :
    I*I = algebraMap fullFibreZeroExtension ℂ (-1) := by
  simp only [I_mul_I, map_neg, map_one]

/-- Every source automorphism of the centered field lifts while fixing `i`, when `i` is absent. -/
private def gaussianBaseLift (hi : I ∉ fullFibreZeroExtension)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension := by
  let hr : I*I = algebraMap fullFibreZeroExtension ℂ (-1) := gaussianUnit_square_zeroField
  let hc : ¬ IsSquare (-1 : fullFibreZeroExtension) :=
    not_isSquare_neg_one_of_I_not_mem fullFibreZeroExtension.toSubfield hi
  let e : fullFibreZeroExtension⟮I⟯ ≃+* fullFibreZeroExtension⟮I⟯ :=
    HTGeometry.quadraticSemilinearEquiv
      (F := fullFibreZeroExtension) (L := ℂ) (c := -1) (r := I)
      hr hc σ.toRingEquiv (by simp)
  let τ : fullFibreZeroExtension⟮I⟯ ≃ₐ[fullFibreSourceField] fullFibreZeroExtension⟮I⟯ :=
    { toRingEquiv := e
      commutes' k := by
        change e (algebraMap fullFibreZeroExtension fullFibreZeroExtension⟮I⟯
          (algebraMap fullFibreSourceField fullFibreZeroExtension k)) =
          algebraMap fullFibreZeroExtension fullFibreZeroExtension⟮I⟯
            (algebraMap fullFibreSourceField fullFibreZeroExtension k)
        dsimp only [e]
        rw [HTGeometry.quadraticSemilinearEquiv_base]
        exact congrArg (algebraMap fullFibreZeroExtension fullFibreZeroExtension⟮I⟯)
          (σ.commutes k) }
  exact τ

private theorem gaussianBaseLift_base (hi : I ∉ fullFibreZeroExtension)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (a : fullFibreZeroExtension) :
    gaussianBaseLift hi σ (algebraMap fullFibreZeroExtension gaussianZeroExtension a) =
      algebraMap fullFibreZeroExtension gaussianZeroExtension (σ a) :=
  HTGeometry.quadraticSemilinearEquiv_base
    (F := fullFibreZeroExtension) (L := ℂ) gaussianUnit_square_zeroField
    (not_isSquare_neg_one_of_I_not_mem fullFibreZeroExtension.toSubfield hi)
    σ.toRingEquiv (by simp) a

private theorem gaussianBaseLift_unit (hi : I ∉ fullFibreZeroExtension)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    gaussianBaseLift hi σ gaussianUnit = gaussianUnit :=
  HTGeometry.quadraticSemilinearEquiv_gen
    (F := fullFibreZeroExtension) (L := ℂ) gaussianUnit_square_zeroField
    (not_isSquare_neg_one_of_I_not_mem fullFibreZeroExtension.toSubfield hi)
    σ.toRingEquiv (by simp)

private theorem gaussianUnit_ne_neg : gaussianUnit ≠ -gaussianUnit := by
  intro h
  have hC := congrArg (fun z : gaussianZeroExtension => (z : ℂ)) h
  have hI := congrArg Complex.im hC
  norm_num [gaussianUnit] at hI

/-- The action on the Gaussian unit records a two-element sign character. -/
private def gaussianSignValue
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) : ℤˣ := by
  classical
  exact if σ gaussianUnit = gaussianUnit then 1 else -1

private theorem gaussianSignValue_action
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) :
    σ gaussianUnit = ((gaussianSignValue σ : ℤ) : gaussianZeroExtension)*gaussianUnit := by
  classical
  unfold gaussianSignValue
  split_ifs with h
  · simpa only [Units.val_one, Int.cast_one, one_mul] using h
  · simpa only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
      using (gaussian_aut_unit σ).resolve_left h

private theorem gaussianSignValue_mul
    (σ τ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) :
    gaussianSignValue (σ*τ) = gaussianSignValue σ * gaussianSignValue τ := by
  classical
  have hneg : -gaussianUnit ≠ gaussianUnit := Ne.symm gaussianUnit_ne_neg
  rcases gaussian_aut_unit σ with hσ | hσ <;>
    rcases gaussian_aut_unit τ with hτ | hτ <;>
    simp [gaussianSignValue, AlgEquiv.mul_apply, hσ, hτ, map_neg, hneg]

/-- Restriction and the Gaussian sign are the two coordinates of the full Galois action. -/
def gaussianActionCoordinates :
    (gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) →*
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) × ℤˣ :=
  (AlgEquiv.restrictNormalHom fullFibreZeroExtension).prod
    { toFun := gaussianSignValue
      map_one' := by simp [gaussianSignValue]
      map_mul' := gaussianSignValue_mul }

/-- The second coordinate is exactly the automorphism's sign on the Gaussian unit. -/
theorem gaussianActionCoordinates_unit
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) :
    σ gaussianUnit = (((gaussianActionCoordinates σ).2 : ℤ) : gaussianZeroExtension)*gaussianUnit :=
  gaussianSignValue_action σ

private theorem gaussian_aut_ext
    (σ τ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension)
    (hbase : ∀ a : fullFibreZeroExtension,
      σ (algebraMap fullFibreZeroExtension gaussianZeroExtension a) =
      τ (algebraMap fullFibreZeroExtension gaussianZeroExtension a))
    (hI : σ gaussianUnit = τ gaussianUnit) : σ = τ := by
  have heq := IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
    (S := gaussianZeroExtension) gaussianZeroExtension_eq_adjoin
    (φ₁ := σ.toAlgHom) (φ₂ := τ.toAlgHom)
    (by
      intro z hz
      rcases hz with rfl | ⟨q, rfl⟩
      · exact hI
      · exact hbase (centeredZeroInFibreExtension q))
  exact AlgEquiv.ext (fun z => DFunLike.congr_fun heq z)

private theorem gaussianActionCoordinates_injective :
    Function.Injective gaussianActionCoordinates := by
  intro σ τ he
  have hbase := congrArg Prod.fst he
  have hsign := congrArg Prod.snd he
  apply gaussian_aut_ext σ τ
  · intro a
    rw [← AlgEquiv.restrictNormal_commutes σ fullFibreZeroExtension,
      ← AlgEquiv.restrictNormal_commutes τ fullFibreZeroExtension]
    exact congrArg (fun η : fullFibreZeroExtension ≃ₐ[fullFibreSourceField]
      fullFibreZeroExtension => algebraMap fullFibreZeroExtension gaussianZeroExtension (η a)) hbase
  · rw [gaussianSignValue_action σ, gaussianSignValue_action τ]
    exact congrArg (fun ε : ℤˣ => ((ε : ℤ) : gaussianZeroExtension)*gaussianUnit) hsign

private theorem gaussianUnit_ne_zero : gaussianUnit ≠ 0 := by
  intro h
  exact I_ne_zero (congrArg (fun z : gaussianZeroExtension => (z : ℂ)) h)

private theorem gaussian_coordinates_of_action
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension)
    (τ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) (ε : ℤˣ)
    (hbase : ∀ a : fullFibreZeroExtension,
      σ (algebraMap fullFibreZeroExtension gaussianZeroExtension a) =
      algebraMap fullFibreZeroExtension gaussianZeroExtension (τ a))
    (hI : σ gaussianUnit = ((ε : ℤ) : gaussianZeroExtension)*gaussianUnit) :
    gaussianActionCoordinates σ = (τ, ε) := by
  apply Prod.ext
  · apply AlgEquiv.ext
    intro a
    apply (algebraMap fullFibreZeroExtension gaussianZeroExtension).injective
    change algebraMap fullFibreZeroExtension gaussianZeroExtension
      (σ.restrictNormal fullFibreZeroExtension a) =
      algebraMap fullFibreZeroExtension gaussianZeroExtension (τ a)
    rw [AlgEquiv.restrictNormal_commutes]
    exact hbase a
  · change gaussianSignValue σ = ε
    apply Units.ext
    have hc := mul_right_cancel₀ gaussianUnit_ne_zero
      ((gaussianSignValue_action σ).symm.trans hI)
    exact_mod_cast hc

private def gaussianFlip (hi : I ∉ fullFibreZeroExtension) :
    gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension :=
  let e : fullFibreZeroExtension⟮I⟯ ≃ₐ[fullFibreZeroExtension] fullFibreZeroExtension⟮I⟯ :=
    gaussianQuadraticConjugation fullFibreZeroExtension.toSubfield hi
  e.restrictScalars fullFibreSourceField

private theorem gaussianFlip_base (hi : I ∉ fullFibreZeroExtension)
    (a : fullFibreZeroExtension) :
    gaussianFlip hi (algebraMap fullFibreZeroExtension gaussianZeroExtension a) =
      algebraMap fullFibreZeroExtension gaussianZeroExtension a :=
  (gaussianQuadraticConjugation fullFibreZeroExtension.toSubfield hi).commutes a

private theorem gaussianFlip_unit (hi : I ∉ fullFibreZeroExtension) :
    gaussianFlip hi gaussianUnit = -gaussianUnit :=
  gaussianQuadraticConjugation_I fullFibreZeroExtension.toSubfield hi

private theorem gaussianActionCoordinates_surjective (hi : I ∉ fullFibreZeroExtension) :
    Function.Surjective gaussianActionCoordinates := by
  rintro ⟨τ, ε⟩
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨gaussianBaseLift hi τ, gaussian_coordinates_of_action _ τ 1
      (gaussianBaseLift_base hi τ) ?_⟩
    simpa using gaussianBaseLift_unit hi τ
  · refine ⟨(gaussianFlip hi).trans (gaussianBaseLift hi τ),
      gaussian_coordinates_of_action _ τ (-1) ?_ ?_⟩
    · intro a
      rw [AlgEquiv.trans_apply, gaussianFlip_base, gaussianBaseLift_base]
    · simp only [AlgEquiv.trans_apply, gaussianFlip_unit, map_neg, gaussianBaseLift_unit,
        Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]

/-- If `i` is absent, the full infinite Galois group splits as the centered group times `C₂`. -/
def gaussianGaloisProduct (hi : I ∉ fullFibreZeroExtension) :
    (gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) ≃*
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) × ℤˣ :=
  MulEquiv.ofBijective gaussianActionCoordinates
    ⟨gaussianActionCoordinates_injective, gaussianActionCoordinates_surjective hi⟩

private theorem gaussianConjugation_coe (z : gaussianZeroExtension) :
    (gaussianZeroConjugation z : ℂ) = (starRingEnd ℂ) (z : ℂ) := rfl

private theorem centeredConjugation_coe (z : fullFibreZeroExtension) :
    (fullFibreZeroConjugation z : ℂ) = (starRingEnd ℂ) (z : ℂ) := rfl

private theorem centered_gaussian_algebraMap_coe (a : fullFibreZeroExtension) :
    (algebraMap fullFibreZeroExtension gaussianZeroExtension a : ℂ) = (a : ℂ) :=
  (IsScalarTower.algebraMap_apply fullFibreZeroExtension gaussianZeroExtension ℂ a).symm

private theorem gaussianConjugation_base (a : fullFibreZeroExtension) :
    gaussianZeroConjugation (algebraMap fullFibreZeroExtension gaussianZeroExtension a) =
      algebraMap fullFibreZeroExtension gaussianZeroExtension (fullFibreZeroConjugation a) := by
  apply Subtype.ext
  rw [gaussianConjugation_coe, centered_gaussian_algebraMap_coe,
    centered_gaussian_algebraMap_coe, centeredConjugation_coe]

private theorem gaussianConjugation_unit :
    gaussianZeroConjugation gaussianUnit =
      (((-1 : ℤˣ) : ℤ) : gaussianZeroExtension)*gaussianUnit := by
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
  apply Subtype.ext
  exact Complex.conj_I

/-- Ordinary conjugation has centered conjugation and negative Gaussian sign as coordinates. -/
theorem gaussian_conjugation_coordinates :
    gaussianActionCoordinates gaussianZeroConjugation = (fullFibreZeroConjugation, -1) :=
  gaussian_coordinates_of_action gaussianZeroConjugation fullFibreZeroConjugation (-1)
    gaussianConjugation_base gaussianConjugation_unit

/-- Independent centered and Gaussian actions exist precisely when `i` is absent. -/
theorem gaussianActionCoordinates_surjective_iff :
    Function.Surjective gaussianActionCoordinates ↔ I ∉ fullFibreZeroExtension := by
  constructor
  · intro h hi
    obtain ⟨σ, hσ⟩ := h (1, -1)
    have hb := congrArg Prod.fst hσ
    have hs := congrArg Prod.snd hσ
    have hfixed : σ gaussianUnit = gaussianUnit := by
      have h := AlgEquiv.restrictNormal_commutes σ fullFibreZeroExtension
        (⟨I, hi⟩ : fullFibreZeroExtension)
      change algebraMap fullFibreZeroExtension gaussianZeroExtension
        ((gaussianActionCoordinates σ).1 ⟨I, hi⟩) = σ gaussianUnit at h
      rw [hb] at h
      exact h.symm
    have hflip := gaussianSignValue_action σ
    change σ gaussianUnit = (((gaussianActionCoordinates σ).2 : ℤ) :
      gaussianZeroExtension)*gaussianUnit at hflip
    rw [hs] at hflip
    have hbad : gaussianUnit = -gaussianUnit := by simpa [hfixed] using hflip
    exact gaussianUnit_ne_neg hbad
  · exact gaussianActionCoordinates_surjective

/-- The Gaussian extension collapses exactly when the centered field already contains `i`. -/
theorem gaussianZeroExtension_eq_centered_iff :
    gaussianZeroExtension = fullFibreZeroExtension ↔ I ∈ fullFibreZeroExtension := by
  constructor
  · intro h
    rw [← h]
    exact gaussianUnit_mem_extension
  · intro hi
    apply le_antisymm _ zeroExtension_le_gaussian
    rw [gaussianZeroExtension_eq_adjoin, IntermediateField.adjoin_le_iff]
    rintro z (rfl | ⟨q, rfl⟩)
    · exact hi
    · exact (centeredZeroInFibreExtension q).property

/-- The two Gaussian-extension regimes form an unconditional classification. -/
theorem gaussian_extension_dichotomy :
    (I ∈ fullFibreZeroExtension ∧ gaussianZeroExtension = fullFibreZeroExtension) ∨
    (I ∉ fullFibreZeroExtension ∧ Nonempty
      ((gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) ≃*
        (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) × ℤˣ)) := by
  classical
  by_cases hi : I ∈ fullFibreZeroExtension
  · exact Or.inl ⟨hi, gaussianZeroExtension_eq_centered_iff.mpr hi⟩
  · exact Or.inr ⟨hi, ⟨gaussianGaloisProduct hi⟩⟩

/-- A functional-equation lift, when it exists, is unique on the entire Gaussian field. -/
theorem functional_equation_lift_unique
    (σ τ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension)
    (hσ : ∀ q, σ (originalZeroInGaussianExtension q) = 1-originalZeroInGaussianExtension q)
    (hτ : ∀ q, τ (originalZeroInGaussianExtension q) = 1-originalZeroInGaussianExtension q) :
    σ = τ := by
  have heq := IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
    (S := gaussianZeroExtension) gaussianZeroExtension_eq_adjoin
    (φ₁ := σ.toAlgHom) (φ₂ := τ.toAlgHom)
    (by
      intro z hz
      rcases hz with rfl | ⟨q, rfl⟩
      · exact (gaussian_reflection_forces_flip σ hσ).trans
          (gaussian_reflection_forces_flip τ hτ).symm
      · exact (gaussian_reflection_fixes_centered σ hσ q).trans
          (gaussian_reflection_fixes_centered τ hτ q).symm)
  exact AlgEquiv.ext (fun z => DFunLike.congr_fun heq z)

/-- The functional-equation obstruction is the square class of minus one in the entire centered field. -/
theorem functional_equation_lift_iff_nonsquare :
    (∃ σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension,
      ∀ q, σ (originalZeroInGaussianExtension q) = 1-originalZeroInGaussianExtension q) ↔
    ¬ IsSquare (-1 : fullFibreZeroExtension) := by
  rw [functional_equation_lift_iff]
  constructor
  · exact not_isSquare_neg_one_of_I_not_mem fullFibreZeroExtension.toSubfield
  · intro hn hi
    apply hn
    refine ⟨⟨I, hi⟩, ?_⟩
    apply Subtype.ext
    exact I_mul_I.symm

/-- Every source automorphism permutes the entire original zero support. -/
theorem gaussian_aut_preserves_original_zeros
    (σ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension)
    (q : XiZeroCopy) :
    ∃ q' : XiZeroCopy, (σ (originalZeroInGaussianExtension q) : ℂ) = (q'.1 : ℂ) := by
  obtain ⟨q', _, heq⟩ := gaussian_aut_preserves_centered_fibre σ q
  have hr : (σ (originalZeroInGaussianExtension q) : ℂ) =
      1/2+(σ gaussianUnit : ℂ)*(σ (centeredZeroInGaussianExtension q) : ℂ) := by
    simp only [originalZeroInGaussianExtension, map_add, map_div₀, map_one,
      map_ofNat, map_mul]
    rfl
  rcases gaussian_aut_unit σ with hI | hI
  · refine ⟨q', ?_⟩
    rw [← originalZeroInGaussianExtension_coe q', hr, hI, heq]
    rfl
  · refine ⟨xiZeroCopyReflectEquiv q', ?_⟩
    rw [← originalZeroInGaussianExtension_coe (xiZeroCopyReflectEquiv q'), hr, hI, heq]
    change 1/2+(-I)*xiSpectralPoint q' = 1/2+I*xiSpectralPoint (xiZeroCopyReflectEquiv q')
    rw [xiSpectralPoint_reflect]
    ring

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussianZeroExtension_normal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussianZeroConjugation_central
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.functional_equation_lift_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussianZeroExtension_toSubfield
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussian_original_zero_orbit_finite
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussianGaloisProduct
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussian_conjugation_coordinates
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussianActionCoordinates_surjective_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussian_extension_dichotomy
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.functional_equation_lift_unique
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.functional_equation_lift_iff_nonsquare
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussian_aut_preserves_original_zeros
