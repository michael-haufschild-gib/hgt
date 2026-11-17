import GaloisForLFunctions.GaloisTheoryOfZeros.TheSignedPermutationsOfTheZeroFibres

/-!
# Fixed choices of conjugate roots

The product action of a signed permutation acts on one choice from every
conjugate pair. For an involution, a fixed choice exists exactly when each
fixed pair has positive sign. Thus every fixed-point-free involution exposes
a negative sign on a fixed coordinate. This is the involution case of the
product-action mechanism in Ding et al., arXiv:2611.21555, Theorem 3.1.
-/

noncomputable section
namespace GaloisForLFunctions.GaloisTheoryOfZeros.FibreSignedPerm
variable {α : Type*}

/-- Product action on a simultaneous choice of one root from every pair. -/
def choicePerm (a : FibreSignedPerm α) : Equiv.Perm (α → ℤˣ) where
  toFun f i := a.sign i * f (a.perm⁻¹ i)
  invFun f i := (a.sign (a.perm i))⁻¹ * f (a.perm i)
  left_inv f := by
    funext i
    change (a.sign (a.perm i))⁻¹ *
      (a.sign (a.perm i) * f (a.perm.symm (a.perm i))) = f i
    simp only [Equiv.symm_apply_apply, inv_mul_cancel_left]
  right_inv f := by
    funext i
    change a.sign i * ((a.sign (a.perm (a.perm.symm i)))⁻¹ *
      f (a.perm (a.perm.symm i))) = f i
    simp only [Equiv.apply_symm_apply, mul_inv_cancel_left]

/-- The product action respects the existing signed-permutation group law. -/
def choiceAction : FibreSignedPerm α →* Equiv.Perm (α → ℤˣ) where
  toFun := choicePerm
  map_one' := by
    apply Equiv.ext
    intro f
    funext i
    change 1 * f i = f i
    exact one_mul _
  map_mul' a b := by
    apply Equiv.ext
    intro f
    funext i
    change (a.sign i * b.sign (a.perm⁻¹ i)) *
        f ((a.perm * b.perm)⁻¹ i) =
      a.sign i * (b.sign (a.perm⁻¹ i) * f (b.perm⁻¹ (a.perm⁻¹ i)))
    rw [mul_inv_rev]
    exact mul_assoc _ _ _

/-- A pure change of the chosen root in each pair. -/
def choiceGauge (f : α → ℤˣ) : FibreSignedPerm α := ⟨1, f⟩

/-- The pair permutation with no sign changes. -/
def unsigned (σ : Equiv.Perm α) : FibreSignedPerm α := ⟨σ, fun _ => 1⟩

/-- A fixed choice trivializes all signs by conjugation inside the base group. -/
theorem fixed_choice_iff_gauge (a : FibreSignedPerm α) (f : α → ℤˣ) :
    choiceAction a f = f ↔ (choiceGauge f)⁻¹ * a * choiceGauge f = unsigned a.perm := by
  constructor
  · intro h
    apply FibreSignedPerm.ext
    · simp [choiceGauge, unsigned]
    · funext i
      have hi := congrFun h i
      change a.sign i * f (a.perm⁻¹ i) = f i at hi
      change (f i)⁻¹ * a.sign i * f (a.perm⁻¹ i) = 1
      rw [mul_assoc, hi, inv_mul_cancel]
  · intro h
    funext i
    have hi := congrArg (fun a : FibreSignedPerm α => a.sign i) h
    change (f i)⁻¹ * a.sign i * f (a.perm⁻¹ i) = 1 at hi
    change a.sign i * f (a.perm⁻¹ i) = f i
    have he := congrArg (fun z : ℤˣ => f i * z) hi
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using he

private theorem sign_square (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

private theorem involution_perm (a : FibreSignedPerm α) (ha : a * a = 1) :
    a.perm⁻¹ = a.perm := by
  apply inv_eq_of_mul_eq_one_left
  exact congrArg FibreSignedPerm.perm ha

private theorem involution_perm_apply (a : FibreSignedPerm α) (ha : a * a = 1) (i : α) :
    a.perm (a.perm i) = i := by
  have h := congrArg (fun a : FibreSignedPerm α => a.perm i) ha
  exact h

private theorem involution_sign (a : FibreSignedPerm α) (ha : a * a = 1) (i : α) :
    a.sign (a.perm i) = a.sign i := by
  have h := congrArg (fun a : FibreSignedPerm α => a.sign i) ha
  change a.sign i * a.sign (a.perm⁻¹ i) = 1 at h
  rw [involution_perm a ha] at h
  exact mul_left_cancel (h.trans (sign_square (a.sign i)).symm)

/-- A signed involution admits a simultaneous root choice precisely when fixed pair labels have positive signs. -/
theorem involution_has_fixed_choice_iff [LinearOrder α] (a : FibreSignedPerm α)
    (ha : a * a = 1) :
    (∃ f, choiceAction a f = f) ↔ ∀ i, a.perm i = i → a.sign i = 1 := by
  constructor
  · rintro ⟨f, hf⟩ i hi
    have h := congrFun hf i
    change a.sign i * f (a.perm⁻¹ i) = f i at h
    rw [involution_perm a ha, hi] at h
    exact mul_right_cancel (h.trans (one_mul (f i)).symm)
  · intro h
    let f : α → ℤˣ := fun i => if a.perm i < i then a.sign i else 1
    refine ⟨f, funext fun i => ?_⟩
    change a.sign i * f (a.perm⁻¹ i) = f i
    rw [involution_perm a ha]
    change a.sign i * (if a.perm (a.perm i) < a.perm i then a.sign (a.perm i) else 1) =
      if a.perm i < i then a.sign i else 1
    rw [involution_perm_apply a ha, involution_sign a ha]
    rcases lt_trichotomy (a.perm i) i with hi | hi | hi
    · simp only [hi, not_lt.mpr hi.le, if_false, if_true, mul_one]
    · simp only [hi, lt_self_iff_false, if_false, h i hi, mul_one]
    · simp only [hi, not_lt.mpr hi.le, if_false, if_true, sign_square]

/-- The obstruction is sharp: a negative fixed coordinate is equivalent to having no fixed root choice. -/
theorem involution_fixedPointFree_iff [LinearOrder α] (a : FibreSignedPerm α)
    (ha : a * a = 1) :
    (∀ f, choiceAction a f ≠ f) ↔ ∃ i, a.perm i = i ∧ a.sign i = -1 := by
  classical
  rw [← not_exists, involution_has_fixed_choice_iff a ha]
  push Not
  constructor
  · rintro ⟨i, hi, hs⟩
    refine ⟨i, hi, ?_⟩
    exact (Int.units_eq_one_or (a.sign i)).resolve_left hs
  · rintro ⟨i, hi, hs⟩
    exact ⟨i, hi, by rw [hs]; decide⟩

/-- Finite zero-pair labels need no chosen order for the fixed-choice classification. -/
theorem finite_involution_has_fixed_choice_iff [Finite α] (a : FibreSignedPerm α)
    (ha : a * a = 1) :
    (∃ f, choiceAction a f = f) ↔ ∀ i, a.perm i = i → a.sign i = 1 := by
  letI := Fintype.ofFinite α
  letI : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  exact involution_has_fixed_choice_iff a ha

/-- A fixed-point-free involution on finite root choices exposes a negative fixed pair. -/
theorem finite_involution_fixedPointFree_iff [Finite α] (a : FibreSignedPerm α)
    (ha : a * a = 1) :
    (∀ f, choiceAction a f ≠ f) ↔ ∃ i, a.perm i = i ∧ a.sign i = -1 := by
  letI := Fintype.ofFinite α
  letI : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  exact involution_fixedPointFree_iff a ha

#print axioms finite_involution_has_fixed_choice_iff
#print axioms finite_involution_fixedPointFree_iff

#print axioms fixed_choice_iff_gauge
#print axioms involution_has_fixed_choice_iff
#print axioms involution_fixedPointFree_iff
end GaloisForLFunctions.GaloisTheoryOfZeros.FibreSignedPerm
