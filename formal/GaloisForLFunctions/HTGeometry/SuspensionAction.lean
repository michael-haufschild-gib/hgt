import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Suspensions of a group action

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §6.

For a group `Q` acting on a set `S` and a homomorphism `ι : Q → R` into a commutative group, the
suspension `S ×_Q R` is the quotient of `S × R` by `(s , u) q = (q • s , ι (q)^{-1} u)`.  The group
`R` acts on it through the second factor, and the isotropy group of a class `[s , u]` is the image
under `ι` of the isotropy group of `s`.
-/

namespace HTGeometry

variable {Q S R : Type*} [Group Q] [MulAction Q S] [CommGroup R]

/-- The suspension relation. -/
def SuspensionRel (ι : Q →* R) (a b : S × R) : Prop :=
  ∃ q : Q, q • a.1 = b.1 ∧ (ι q)⁻¹ * a.2 = b.2

theorem suspensionRel_refl (ι : Q →* R) (a : S × R) : SuspensionRel ι a a :=
  ⟨1, one_smul _ _, by rw [map_one, inv_one, one_mul]⟩

theorem suspensionRel_symm {ι : Q →* R} {a b : S × R} (h : SuspensionRel ι a b) :
    SuspensionRel ι b a := by
  obtain ⟨q, h1, h2⟩ := h
  refine ⟨q⁻¹, ?_, ?_⟩
  · rw [← h1, ← mul_smul, inv_mul_cancel, one_smul]
  · rw [← h2, map_inv, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

theorem suspensionRel_trans {ι : Q →* R} {a b c : S × R} (hab : SuspensionRel ι a b)
    (hbc : SuspensionRel ι b c) : SuspensionRel ι a c := by
  obtain ⟨q, h1, h2⟩ := hab
  obtain ⟨r, h3, h4⟩ := hbc
  refine ⟨r * q, ?_, ?_⟩
  · rw [mul_smul, h1, h3]
  · rw [← h4, ← h2, map_mul, mul_inv, mul_assoc]

/-- The setoid defining the suspension. -/
def suspensionSetoid (ι : Q →* R) : Setoid (S × R) where
  r := SuspensionRel ι
  iseqv := ⟨suspensionRel_refl ι, suspensionRel_symm, suspensionRel_trans⟩

/-- **Deninger, §6.**  The suspension `S ×_Q R`. -/
def Suspension (ι : Q →* R) (S : Type*) [MulAction Q S] : Type _ :=
  Quotient (suspensionSetoid (S := S) ι)

/-- The class of a pair in the suspension. -/
def suspensionMk (ι : Q →* R) (s : S) (u : R) : Suspension ι S :=
  Quotient.mk _ (s, u)

theorem suspensionMk_eq_iff (ι : Q →* R) (s t : S) (u v : R) :
    suspensionMk ι s u = suspensionMk ι t v ↔ ∃ q : Q, q • s = t ∧ (ι q)⁻¹ * u = v :=
  Quotient.eq (r := suspensionSetoid ι)

theorem suspensionMk_surjective (ι : Q →* R) (z : Suspension ι S) :
    ∃ (s : S) (u : R), suspensionMk ι s u = z := by
  obtain ⟨⟨s, u⟩, rfl⟩ := Quotient.exists_rep z
  exact ⟨s, u, rfl⟩

/-- **Deninger, §6.**  The `R`-action on the suspension, through the second factor. -/
def suspensionSMul (ι : Q →* R) (v : R) : Suspension ι S → Suspension ι S :=
  Quotient.map (fun a : S × R => (a.1, a.2 * v)) (by
    rintro ⟨s, u⟩ ⟨t, w⟩ ⟨q, h1, h2⟩
    refine ⟨q, h1, ?_⟩
    show (ι q)⁻¹ * (u * v) = w * v
    rw [← mul_assoc]
    exact congrArg (· * v) h2)

@[simp] theorem suspensionSMul_mk (ι : Q →* R) (v : R) (s : S) (u : R) :
    suspensionSMul ι v (suspensionMk ι s u) = suspensionMk ι s (u * v) := rfl

theorem suspensionSMul_one (ι : Q →* R) (z : Suspension ι S) : suspensionSMul ι 1 z = z := by
  obtain ⟨s, u, rfl⟩ := suspensionMk_surjective ι z
  rw [suspensionSMul_mk, mul_one]

theorem suspensionSMul_mul (ι : Q →* R) (v w : R) (z : Suspension ι S) :
    suspensionSMul ι v (suspensionSMul ι w z) = suspensionSMul ι (w * v) z := by
  obtain ⟨s, u, rfl⟩ := suspensionMk_surjective ι z
  rw [suspensionSMul_mk, suspensionSMul_mk, suspensionSMul_mk, mul_assoc]

/-- **Deninger, Theorem 6.1.**  The isotropy group of a class in the suspension is the image under
`ι` of the isotropy group of the underlying point. -/
theorem suspension_isotropy (ι : Q →* R) (s : S) (u v : R) :
    suspensionSMul ι v (suspensionMk ι s u) = suspensionMk ι s u
      ↔ ∃ q : Q, q • s = s ∧ ι q = v := by
  rw [suspensionSMul_mk, suspensionMk_eq_iff]
  constructor
  · rintro ⟨q, h1, h2⟩
    refine ⟨q, h1, ?_⟩
    have h2' : (ι q)⁻¹ * (u * v) = u := h2
    rw [← mul_assoc, mul_comm ((ι q)⁻¹) u, mul_assoc] at h2'
    have h3 : (ι q)⁻¹ * v = 1 := mul_left_cancel (a := u) (by rw [mul_one]; exact h2')
    exact inv_mul_eq_one.1 h3
  · rintro ⟨q, h1, h2⟩
    refine ⟨q, h1, ?_⟩
    show (ι q)⁻¹ * (u * v) = u
    rw [h2, ← mul_assoc, mul_comm v⁻¹ u, mul_assoc, inv_mul_cancel, mul_one]

/-- **Deninger, Theorem 6.1, the remark.**  A point with trivial isotropy in `Q` has trivial
isotropy in `R` after suspension. -/
theorem suspension_isotropy_trivial (ι : Q →* R) (s : S) (u v : R)
    (h : ∀ q : Q, q • s = s → q = 1)
    (hv : suspensionSMul ι v (suspensionMk ι s u) = suspensionMk ι s u) : v = 1 := by
  obtain ⟨q, h1, h2⟩ := (suspension_isotropy ι s u v).1 hv
  rw [← h2, h q h1, map_one]

/-- **Deninger, Theorem 6.1.**  The isotropy group of a class in the suspension is the image of
the isotropy group of the underlying point, as a subgroup of `R`. -/
theorem suspension_isotropy_eq_map (ι : Q →* R) (s : S) (u : R) :
    {v : R | suspensionSMul ι v (suspensionMk ι s u) = suspensionMk ι s u}
      = ι '' {q : Q | q • s = s} := by
  ext v
  rw [Set.mem_setOf_eq, suspension_isotropy]
  constructor
  · rintro ⟨q, h1, h2⟩
    exact ⟨q, h1, h2⟩
  · rintro ⟨q, h1, h2⟩
    exact ⟨q, h1, h2⟩

end HTGeometry
