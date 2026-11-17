import GaloisForLFunctions.GaloisTheoryOfZeros.Actions.SignedChoiceInvolutions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Stabilizers classify simultaneous root choices

A signed action admits a common root choice precisely when every label
stabilizer has positive sign. Transport from orbit representatives then
identifies all common choices with independent signs on the label orbits.
-/

noncomputable section
open Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros.FibreSignedPerm
variable {α H : Type*} [Group H] (ρ : H →* FibreSignedPerm α)

/-- The sign acquired while transporting a root from its source label. -/
def transportSign (g : H) (i : α) : ℤˣ := (ρ g).sign ((ρ g).perm i)

private theorem perm_mul_at (g h : H) (i : α) :
    (ρ (g * h)).perm i = (ρ g).perm ((ρ h).perm i) := by rw [map_mul]; rfl

private theorem perm_one_at (i : α) : (ρ 1).perm i = i := by rw [map_one]; rfl

/-- Forward signs satisfy the cocycle law along successive transports. -/
theorem transportSign_mul (g h : H) (i : α) :
    transportSign ρ (g * h) i = transportSign ρ g ((ρ h).perm i) * transportSign ρ h i := by
  unfold transportSign
  rw [map_mul, mul_sign, mul_perm]
  change (ρ g).sign ((ρ g).perm ((ρ h).perm i)) *
    (ρ h).sign ((ρ g).perm.symm ((ρ g).perm ((ρ h).perm i))) = _
  rw [Equiv.symm_apply_apply]

/-- Every label stabilizer preserves each root in its two-point fibre. -/
def PositiveStabilizers : Prop :=
  ∀ (g : H) (i : α), (ρ g).perm i = i → (ρ g).sign i = 1

/-- Under positive stabilizers, the transported sign depends only on source and destination. -/
theorem transportSign_eq_of_image_eq (hb : PositiveStabilizers ρ)
    (g h : H) (i : α) (he : (ρ g).perm i = (ρ h).perm i) :
    transportSign ρ g i = transportSign ρ h i := by
  have hf : (ρ (h⁻¹ * g)).perm i = i := by
    rw [perm_mul_at, he, map_inv, inv_perm]
    exact (ρ h).perm.symm_apply_apply i
  have hs : transportSign ρ (h⁻¹ * g) i = 1 := by
    unfold transportSign
    rw [hf]
    exact hb _ _ hf
  have hc := transportSign_mul ρ h (h⁻¹ * g) i
  rw [mul_inv_cancel_left, hf, hs, mul_one] at hc
  exact hc

/-- Orbit equivalence for the underlying permutation of pair labels. -/
def labelOrbitSetoid : Setoid α where
  r i j := ∃ g : H, (ρ g).perm i = j
  iseqv := ⟨fun i => ⟨1, perm_one_at ρ i⟩,
    fun {i j} ⟨g, hg⟩ => ⟨g⁻¹, by
      rw [map_inv, inv_perm, ← hg]
      exact (ρ g).perm.symm_apply_apply i⟩,
    fun {i j k} ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by rw [perm_mul_at, hg, hh]⟩⟩

/-- Label orbits, allowing arbitrary groups and infinitely many pair labels. -/
abbrev LabelOrbits := Quotient (labelOrbitSetoid ρ)

private def labelClass (i : α) : LabelOrbits ρ := Quotient.mk _ i

private theorem labelClass_perm (g : H) (i : α) :
    labelClass ρ ((ρ g).perm i) = labelClass ρ i :=
  (Quotient.sound (s := labelOrbitSetoid ρ) ⟨g, rfl⟩).symm

private def orbitTransport (i : α) : H :=
  Classical.choose (Quotient.exact (Quotient.out_eq (labelClass ρ i)))

private theorem orbitTransport_spec (i : α) :
    (ρ (orbitTransport ρ i)).perm (labelClass ρ i).out = i :=
  Classical.choose_spec (Quotient.exact (Quotient.out_eq (labelClass ρ i)))

/-- Canonical root choice obtained by transport from arbitrary orbit representatives. -/
def orbitChoice (i : α) : ℤˣ :=
  transportSign ρ (orbitTransport ρ i) (labelClass ρ i).out

private theorem orbitChoice_covariant (hb : PositiveStabilizers ρ) (g : H) (i : α) :
    orbitChoice ρ ((ρ g).perm i) = transportSign ρ g i * orbitChoice ρ i := by
  have he : (ρ (orbitTransport ρ ((ρ g).perm i))).perm (labelClass ρ i).out =
      (ρ (g * orbitTransport ρ i)).perm (labelClass ρ i).out := by
    rw [perm_mul_at, orbitTransport_spec]
    have h := orbitTransport_spec ρ ((ρ g).perm i)
    rwa [labelClass_perm] at h
  have hs := transportSign_eq_of_image_eq ρ hb
    (orbitTransport ρ ((ρ g).perm i)) (g * orbitTransport ρ i) (labelClass ρ i).out he
  unfold orbitChoice
  rw [labelClass_perm, hs, transportSign_mul, orbitTransport_spec]

private theorem fixed_iff_covariant (f : α → ℤˣ) :
    (∀ g : H, choiceAction (ρ g) f = f) ↔
    ∀ (g : H) (i : α), f ((ρ g).perm i) = transportSign ρ g i * f i := by
  constructor
  · intro hf g i
    have h := congrFun (hf g) ((ρ g).perm i)
    change (ρ g).sign ((ρ g).perm i) * f ((ρ g).perm.symm ((ρ g).perm i)) = _ at h
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  · intro hf g
    funext i
    have h := hf g ((ρ g).perm.symm i)
    unfold transportSign at h
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

/-- A common root choice exists exactly when all stabilizer signs vanish. -/
theorem common_fixed_choice_iff :
    (∃ f : α → ℤˣ, ∀ g : H, choiceAction (ρ g) f = f) ↔ PositiveStabilizers ρ := by
  constructor
  · rintro ⟨f, hf⟩ g i hi
    have h := (fixed_iff_covariant ρ f).mp hf g i
    unfold transportSign at h
    rw [hi] at h
    exact (mul_right_cancel ((one_mul (f i)).trans h)).symm
  · intro hb
    exact ⟨orbitChoice ρ, (fixed_iff_covariant ρ _).mpr (orbitChoice_covariant ρ hb)⟩

/-- The full space of simultaneous choices of roots fixed by the signed action. -/
abbrev FixedChoices := {f : α → ℤˣ // ∀ g : H, choiceAction (ρ g) f = f}

private theorem fixed_ratio_invariant (hb : PositiveStabilizers ρ) (f : FixedChoices ρ)
    (g : H) (i : α) :
    f.val ((ρ g).perm i) / orbitChoice ρ ((ρ g).perm i) = f.val i / orbitChoice ρ i := by
  rw [(fixed_iff_covariant ρ f.val).mp f.property, orbitChoice_covariant ρ hb]
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (f.val i * (orbitChoice ρ i)⁻¹) *
        (transportSign ρ g i * (transportSign ρ g i)⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel, mul_one]

/-- Common root choices form a torsor for independent signs on label orbits. -/
def fixedChoicesEquiv (hb : PositiveStabilizers ρ) :
    FixedChoices ρ ≃ (LabelOrbits ρ → ℤˣ) where
  toFun f := Quotient.lift (fun i => f.val i / orbitChoice ρ i) (by
    rintro i j ⟨g, rfl⟩
    exact (fixed_ratio_invariant ρ hb f g i).symm)
  invFun a := ⟨fun i => orbitChoice ρ i * a (labelClass ρ i), by
    apply (fixed_iff_covariant ρ _).mpr
    intro g i
    rw [orbitChoice_covariant ρ hb, labelClass_perm]
    exact mul_assoc _ _ _⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    change orbitChoice ρ i * (f.val i / orbitChoice ρ i) = f.val i
    rw [div_eq_mul_inv]
    calc
      _ = f.val i * (orbitChoice ρ i * (orbitChoice ρ i)⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel, mul_one]
  right_inv a := by
    funext o
    induction o using Quotient.inductionOn with
    | h i =>
      change orbitChoice ρ i * a (labelClass ρ i) / orbitChoice ρ i = a (labelClass ρ i)
      rw [div_eq_mul_inv]
      calc
        _ = a (labelClass ρ i) * (orbitChoice ρ i * (orbitChoice ρ i)⁻¹) := by ac_rfl
        _ = _ := by rw [mul_inv_cancel, mul_one]

/-- Stabilizer positivity is also exactly simultaneous conjugacy to an unsigned action. -/
theorem simultaneously_unsigned_iff :
    (∃ f : α → ℤˣ, ∀ g : H,
      (choiceGauge f)⁻¹ * ρ g * choiceGauge f = unsigned (ρ g).perm) ↔
      PositiveStabilizers ρ := by
  simpa only [← fixed_choice_iff_gauge] using common_fixed_choice_iff ρ

/-- A finite signed action has either no common choices or two choices per label orbit. -/
theorem card_fixedChoices [Finite α] :
    Nat.card (FixedChoices ρ) =
      if PositiveStabilizers ρ then 2 ^ Nat.card (LabelOrbits ρ) else 0 := by
  classical
  by_cases hb : PositiveStabilizers ρ
  · rw [if_pos hb, Nat.card_congr (fixedChoicesEquiv ρ hb), Nat.card_fun,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  · rw [if_neg hb]
    letI : IsEmpty (FixedChoices ρ) := ⟨fun f =>
      hb ((common_fixed_choice_iff ρ).mp ⟨f.val, f.property⟩)⟩
    exact Finite.card_eq_zero_iff.mpr inferInstance

#print axioms card_fixedChoices
#print axioms common_fixed_choice_iff
#print axioms fixedChoicesEquiv
#print axioms simultaneously_unsigned_iff
end GaloisForLFunctions.GaloisTheoryOfZeros.FibreSignedPerm
