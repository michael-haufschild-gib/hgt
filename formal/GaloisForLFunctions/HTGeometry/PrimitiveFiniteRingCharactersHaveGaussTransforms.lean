import GaloisForLFunctions.HTGeometry.FiniteRingUnitsLiftThroughQuotients
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.GaussSum

/-!
# Primitive Gauss transforms over finite commutative rings

Surjectivity on units identifies quotient-character descent with triviality
on the corresponding congruence kernel. A primitive character therefore
detects a unit stabilizing each nonunit, forcing its Gauss coefficient to
vanish. Unit shifts give the full inverse-character transform. Additive
orthogonality then gives the reciprocal Gauss product and its exact norm.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.FiniteRing

variable {R S T C : Type*} [CommRing R] [CommRing S] [CommRing T]
  [CommMonoidWithZero C]

/-- Pull back a unit character, extending it by zero on source nonunits. -/
def inflateChar (f : R →+* S) (χ : MulChar S C) : MulChar R C :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (Units.map f.toMonoidHom))

theorem inflateChar_unit (f : R →+* S) (χ : MulChar S C) (u : Rˣ) :
    inflateChar f χ (u : R) = χ (f (u : R)) := by
  rw [inflateChar, MulChar.ofUnitHom_coe]
  rfl

theorem inflateChar_toUnitHom (f : R →+* S) (χ : MulChar S C) :
    (inflateChar f χ).toUnitHom = χ.toUnitHom.comp (Units.map f.toMonoidHom) := by
  ext u
  exact inflateChar_unit f χ u

theorem inflateChar_injective [Finite R] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (inflateChar (C := C) f) := by
  intro χ ψ h
  apply MulChar.ext
  intro u
  obtain ⟨v, hv⟩ := units_map_surjective f hf u
  have h' := DFunLike.congr_fun h (v : R)
  have hv' : f (v : R) = (u : S) := congrArg Units.val hv
  simpa only [inflateChar_unit, hv'] using h'

theorem inflateChar_id (χ : MulChar R C) : inflateChar (RingHom.id R) χ = χ := by
  ext u
  exact inflateChar_unit _ _ u

theorem inflateChar_comp (f : R →+* S) (g : S →+* T) (χ : MulChar T C) :
    inflateChar f (inflateChar g χ) = inflateChar (g.comp f) χ := by
  ext u
  rw [inflateChar_unit, inflateChar_unit]
  exact inflateChar_unit g χ (Units.map f.toMonoidHom u)

/-- Descent along a surjective finite-ring quotient is exactly triviality on its unit kernel. -/
theorem exists_inflateChar_eq_iff [Finite R] (f : R →+* S)
    (hf : Function.Surjective f) (χ : MulChar R C) :
    (∃ χ' : MulChar S C, inflateChar f χ' = χ) ↔
      (Units.map f.toMonoidHom).ker ≤ χ.toUnitHom.ker := by
  constructor
  · rintro ⟨χ', rfl⟩ u hu
    rw [MonoidHom.mem_ker, inflateChar_toUnitHom, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp hu, map_one]
  · intro h
    let E := MonoidHom.liftOfSurjective _ (units_map_surjective f hf) ⟨χ.toUnitHom, h⟩
    have hE : E.comp (Units.map f.toMonoidHom) = χ.toUnitHom :=
      MonoidHom.liftOfRightInverse_comp ..
    refine ⟨MulChar.ofUnitHom E, MulChar.equivToUnitHom.injective ?_⟩
    change (inflateChar f (MulChar.ofUnitHom E)).toUnitHom = χ.toUnitHom
    rw [inflateChar_toUnitHom]
    have hunit : (MulChar.ofUnitHom E).toUnitHom = E :=
      MulChar.equivToUnitHom.apply_symm_apply E
    rw [hunit, hE]

/-- A multiplicative character descends through an ideal when its unit character does. -/
def FactorsThrough (χ : MulChar R C) (J : Ideal R) : Prop :=
  ∃ χ' : MulChar (R ⧸ J) C, inflateChar (Ideal.Quotient.mk J) χ' = χ

theorem factorsThrough_iff [Finite R] (χ : MulChar R C) (J : Ideal R) :
    FactorsThrough χ J ↔
      ∀ u : Rˣ, (u : R) - 1 ∈ J → χ (u : R) = 1 := by
  rw [FactorsThrough, exists_inflateChar_eq_iff _ Ideal.Quotient.mk_surjective]
  constructor
  · intro h u hu
    have hq : Units.map (Ideal.Quotient.mk J).toMonoidHom u = 1 := by
      apply Units.ext
      change Ideal.Quotient.mk J (u : R) = 1
      rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
      exact hu
    exact congrArg Units.val (h (MonoidHom.mem_ker.mpr hq))
  · intro h u hu
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    apply h
    have hq := congrArg Units.val (MonoidHom.mem_ker.mp hu)
    change Ideal.Quotient.mk J (u : R) = 1 at hq
    rwa [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq] at hq

/-- A primitive character descends through no nonzero quotient ideal. -/
def IsPrimitive (χ : MulChar R C) : Prop :=
  ∀ J : Ideal R, FactorsThrough χ J → J = ⊥

theorem isPrimitive_iff [Finite R] (χ : MulChar R C) :
    IsPrimitive χ ↔ ∀ J : Ideal R, J ≠ ⊥ →
      ∃ u : Rˣ, (u : R) - 1 ∈ J ∧ χ (u : R) ≠ 1 := by
  simp only [IsPrimitive, factorsThrough_iff]
  constructor
  · intro h J hJ
    by_contra! hc
    exact hJ (h J hc)
  · intro h J hJ
    by_contra hne
    obtain ⟨u, hu, hχ⟩ := h J hne
    exact hχ (hJ u hu)

/-- A nonunit has a stabilizing unit detected by every primitive character. -/
theorem exists_unit_stabilizer [Finite R] {χ : MulChar R C} (hχ : IsPrimitive χ)
    {a : R} (ha : ¬IsUnit a) :
    ∃ u : Rˣ, (u : R) * a = a ∧ χ (u : R) ≠ 1 := by
  let J := (Submodule.span R ({a} : Set R)).annihilator
  have hJ : J ≠ ⊥ := by
    simp only [isUnit_iff_mem_nonZeroDivisors_of_finite,
      mem_nonZeroDivisors_iff_right, not_forall] at ha
    obtain ⟨x, hxa, hx⟩ := ha
    have hxJ : x ∈ J :=
      (Submodule.mem_annihilator_span_singleton a x).mpr hxa
    intro hbot
    rw [hbot] at hxJ
    exact hx (show x = 0 from hxJ)
  obtain ⟨u, hu, hχu⟩ := (isPrimitive_iff χ).mp hχ J hJ
  have hua := (Submodule.mem_annihilator_span_singleton a ((u : R) - 1)).mp hu
  change ((u : R) - 1) * a = 0 at hua
  rw [sub_mul, one_mul, sub_eq_zero] at hua
  exact ⟨u, hua, hχu⟩

/-- Primitive multiplicative characters have zero Gauss coefficients at nonunit shifts. -/
theorem gaussSum_nonunit_eq_zero [Fintype R] {χ : MulChar R ℂ} (hχ : IsPrimitive χ)
    (ψ : AddChar R ℂ) {a : R} (ha : ¬IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by
  obtain ⟨u, hu, hχu⟩ := exists_unit_stabilizer hχ ha
  have hs : (ψ.mulShift a).mulShift (u : R) = ψ.mulShift a := by
    rw [AddChar.mulShift_mulShift, mul_comm a, hu]
  have h := gaussSum_mulShift χ (ψ.mulShift a) u
  rw [hs] at h
  exact eq_zero_of_mul_eq_self_left hχu h

/-- The full primitive Gauss transform, valid for units and nonunits alike. -/
theorem gaussSum_mulShift_eq_of_isPrimitive [Fintype R] {χ : MulChar R ℂ}
    (hχ : IsPrimitive χ) (ψ : AddChar R ℂ) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    exact gaussSum_mulShift_eq χ ψ u
  · rw [gaussSum_nonunit_eq_zero hχ ψ ha, (χ⁻¹).map_nonunit ha, zero_mul]

/-- Additive orthogonality evaluates the inverse Fourier transform at one. -/
theorem sum_gaussSum_mul_inverse_eq_card [Fintype R] (χ : MulChar R ℂ)
    {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) :
    ∑ a : R, gaussSum χ (ψ.mulShift a) * ψ⁻¹ a = Fintype.card R := by
  calc
    ∑ a : R, gaussSum χ (ψ.mulShift a) * ψ⁻¹ a =
        ∑ b : R, χ b * ∑ a : R, ψ (a * (b - 1)) := by
      simp only [gaussSum, AddChar.mulShift_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, AddChar.inv_apply, ← ψ.map_add_eq_mul]
      congr 2
      ring
    _ = ∑ b : R, χ b * (if b - 1 = 0 then (Fintype.card R : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [AddChar.sum_mulShift _ hψ]
      split_ifs <;> simp only [Nat.cast_zero]
    _ = Fintype.card R := by simp [sub_eq_zero]

/-- Primitive multiplicative and additive characters have reciprocal Gauss product `#R`. -/
theorem gaussSum_mul_inverse_eq_card [Fintype R] {χ : MulChar R ℂ}
    (hχ : IsPrimitive χ) {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R := by
  calc
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ =
        ∑ a : R, (χ⁻¹ a * gaussSum χ ψ) * ψ⁻¹ a := by
      change gaussSum χ ψ * (∑ a : R, χ⁻¹ a * ψ⁻¹ a) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ a : R, gaussSum χ (ψ.mulShift a) * ψ⁻¹ a := by
      simp_rw [gaussSum_mulShift_eq_of_isPrimitive hχ]
    _ = Fintype.card R := sum_gaussSum_mul_inverse_eq_card χ hψ

/-- The squared absolute value of a primitive finite-ring Gauss sum is the ring's cardinality. -/
theorem norm_gaussSum_sq [Fintype R] {χ : MulChar R ℂ} (hχ : IsPrimitive χ)
    {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = Fintype.card R := by
  have h := gaussSum_mul_inverse_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hr := congrArg Complex.re h
  rw [← Complex.normSq_eq_norm_sq]
  simpa only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    mul_neg, sub_neg_eq_add, Complex.natCast_re, Complex.normSq_apply, pow_two] using hr

end GaloisForLFunctions.FiniteRing
