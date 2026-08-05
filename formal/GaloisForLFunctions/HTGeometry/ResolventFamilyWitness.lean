import GaloisForLFunctions.HTGeometry.ResolventFamilyJet
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic.NoncommRing

/-!
# The shift resolvent of an algebra element realizes the resolvent identity

The jet theory of a resolvent family runs on the first resolvent identity alone.  Here that
identity is established for the family it is named after: the shift resolvent
`u ↦ (a - u · 1)⁻¹` of an element of a normed algebra, on any set of shifts inside its resolvent
set.  The proof is the classical two-sided insertion
`R_u - R_v = R_u ((a - v) - (a - u)) R_v`, whose middle factor is the scalar `u - v`.

Over a complete algebra the resolvent set is open, so the continuity, derivative and jet laws apply
with no hypothesis at all; and it contains every shift of modulus larger than `‖a‖`, so the theory
is never vacuous and its values are never zero.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Nat

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-! ## The trivial family -/

/-- The zero family satisfies the resolvent identity on every set of shifts. -/
theorem isResolventFamilyOn_zero (s : Set ℝ) :
    IsResolventFamilyOn (fun _ : ℝ => (0 : A)) s := by
  intro u _ v _
  simp

/-! ## The shift resolvent -/

/-- The shift resolvent `(a - u · 1)⁻¹` of an algebra element. -/
noncomputable def shiftResolvent (a : A) (u : ℝ) : A :=
  Ring.inverse (a - algebraMap ℝ A u)

theorem isUnit_sub_algebraMap_of_mem_resolventSet {a : A} {u : ℝ}
    (hu : u ∈ resolventSet ℝ a) : IsUnit (a - algebraMap ℝ A u) := by
  simpa [neg_sub] using (spectrum.mem_resolventSet_iff.mp hu).neg

theorem shiftResolvent_mul_cancel {a : A} {u : ℝ} (hu : u ∈ resolventSet ℝ a) :
    shiftResolvent a u * (a - algebraMap ℝ A u) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_sub_algebraMap_of_mem_resolventSet hu)

theorem mul_shiftResolvent_cancel {a : A} {u : ℝ} (hu : u ∈ resolventSet ℝ a) :
    (a - algebraMap ℝ A u) * shiftResolvent a u = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_sub_algebraMap_of_mem_resolventSet hu)

/-- The two shifted denominators differ by the scalar shift. -/
theorem sub_algebraMap_sub_sub_algebraMap (a : A) (u v : ℝ) :
    (a - algebraMap ℝ A v) - (a - algebraMap ℝ A u) = (u - v) • (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_smul]
  abel

/-- **The first resolvent identity.**  The shift resolvent of an algebra element satisfies the
resolvent identity on every set of shifts inside the resolvent set. -/
theorem isResolventFamilyOn_shiftResolvent (a : A) {s : Set ℝ} (hs : s ⊆ resolventSet ℝ a) :
    IsResolventFamilyOn (shiftResolvent a) s := by
  intro u hu v hv
  have h1 := shiftResolvent_mul_cancel (hs hu)
  have h2 := mul_shiftResolvent_cancel (hs hv)
  calc shiftResolvent a u - shiftResolvent a v
      = shiftResolvent a u * ((a - algebraMap ℝ A v) * shiftResolvent a v) -
          shiftResolvent a u * (a - algebraMap ℝ A u) * shiftResolvent a v := by
        rw [h1, h2, mul_one, one_mul]
    _ = shiftResolvent a u *
          ((a - algebraMap ℝ A v) - (a - algebraMap ℝ A u)) * shiftResolvent a v := by
        noncomm_ring
    _ = shiftResolvent a u * ((u - v) • (1 : A)) * shiftResolvent a v := by
        rw [sub_algebraMap_sub_sub_algebraMap]
    _ = (u - v) • (shiftResolvent a u * shiftResolvent a v) := by
        rw [mul_smul_comm, mul_one, smul_mul_assoc]

/-- The whole resolvent set carries the identity. -/
theorem isResolventFamilyOn_shiftResolvent_resolventSet (a : A) :
    IsResolventFamilyOn (shiftResolvent a) (resolventSet ℝ a) :=
  isResolventFamilyOn_shiftResolvent a (subset_refl _)

/-! ## The jet laws, with no hypothesis -/

variable [CompleteSpace A]

/-- The shift resolvent is continuous on the resolvent set. -/
theorem continuousAt_shiftResolvent (a : A) {v : ℝ} (hv : v ∈ resolventSet ℝ a) :
    ContinuousAt (shiftResolvent a) v :=
  (isResolventFamilyOn_shiftResolvent_resolventSet a).continuousAt
    (spectrum.isOpen_resolventSet a) hv

/-- **The derivative of the shift resolvent is its square.** -/
theorem hasDerivAt_shiftResolvent (a : A) {v : ℝ} (hv : v ∈ resolventSet ℝ a) :
    HasDerivAt (shiftResolvent a) (shiftResolvent a v * shiftResolvent a v) v :=
  (isResolventFamilyOn_shiftResolvent_resolventSet a).hasDerivAt
    (spectrum.isOpen_resolventSet a) hv

/-- **Every shift jet of the shift resolvent.**  The `n`-th normalized jet `n! Rⁿ⁺¹`
differentiates to the next one. -/
theorem hasDerivAt_shiftResolvent_jet (a : A) {v : ℝ} (hv : v ∈ resolventSet ℝ a) (n : ℕ) :
    HasDerivAt (fun u => ((n ! : ℝ)) • shiftResolvent a u ^ (n + 1))
      (((n + 1)! : ℝ) • shiftResolvent a v ^ (n + 2)) v :=
  (isResolventFamilyOn_shiftResolvent_resolventSet a).hasDerivAt_jet
    (spectrum.isOpen_resolventSet a) hv n

/-- The shift jets of the shift resolvent form a derivative chain. -/
theorem hasDerivAt_resolventShiftJet_shiftResolvent (a : A) {v : ℝ}
    (hv : v ∈ resolventSet ℝ a) (n : ℕ) :
    HasDerivAt (resolventShiftJet (shiftResolvent a) n)
      (resolventShiftJet (shiftResolvent a) (n + 1) v) v :=
  hasDerivAt_resolventShiftJet (isResolventFamilyOn_shiftResolvent_resolventSet a)
    (spectrum.isOpen_resolventSet a) hv n

/-! ## The theory is not vacuous -/

variable [NormOneClass A]

/-- Every shift of modulus larger than the norm lies in the resolvent set. -/
theorem mem_resolventSet_of_norm_lt_abs (a : A) {u : ℝ} (hu : ‖a‖ < |u|) :
    u ∈ resolventSet ℝ a := by
  by_contra hcon
  have hmem : u ∈ spectrum ℝ a := hcon
  have hle := spectrum.norm_le_norm_of_mem hmem
  rw [Real.norm_eq_abs] at hle
  linarith

/-- The resolvent set of an algebra element is nonempty. -/
theorem resolventSet_real_nonempty (a : A) : (resolventSet ℝ a).Nonempty := by
  refine ⟨‖a‖ + 1, mem_resolventSet_of_norm_lt_abs a ?_⟩
  rw [abs_of_nonneg (by positivity)]
  linarith

omit [CompleteSpace A] [NormOneClass A] in
/-- On the resolvent set the shift resolvent is a unit, hence never zero. -/
theorem shiftResolvent_ne_zero [Nontrivial A] (a : A) {u : ℝ} (hu : u ∈ resolventSet ℝ a) :
    shiftResolvent a u ≠ 0 := by
  intro hzero
  have h := shiftResolvent_mul_cancel hu
  rw [hzero, zero_mul] at h
  exact zero_ne_one h

/-- **A nonzero resolvent family exists over every nontrivial Banach algebra.**  So the shift-jet
theory is realized, and not by the zero family. -/
theorem exists_isResolventFamilyOn_ne_zero [Nontrivial A] (a : A) :
    ∃ (S : ℝ → A) (s : Set ℝ) (v : ℝ), IsOpen s ∧ v ∈ s ∧ S v ≠ 0 ∧
      IsResolventFamilyOn S s := by
  obtain ⟨v, hv⟩ := resolventSet_real_nonempty a
  exact ⟨shiftResolvent a, resolventSet ℝ a, v, spectrum.isOpen_resolventSet a, hv,
    shiftResolvent_ne_zero a hv, isResolventFamilyOn_shiftResolvent_resolventSet a⟩

end GaloisForLFunctions.HTGeometry
