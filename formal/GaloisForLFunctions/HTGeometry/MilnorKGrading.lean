import GaloisForLFunctions.HTGeometry.MilnorKGradedRing

/-!
# Torsion in Milnor `K`-theory above degree one

A symbol of length `2 + k` is the product of its first two entries with the remaining `k`, so an
integer annihilating the degree-two factor annihilates the whole class.  Since the classes of
symbols generate, every graded piece in degree at least two is torsion as soon as degree two is.

* `torsionAddSubgroup` : the torsion subgroup of an additive commutative group.
* `milnorKDeg_mem_torsion_of_two` : **degree `2 + k` is torsion once degree two is.**
-/

namespace GaloisForLFunctions.HTGeometry

/-- The torsion subgroup of an additive commutative group. -/
def torsionAddSubgroup (A : Type*) [AddCommGroup A] : AddSubgroup A where
  carrier := {x | ∃ n : ℤ, n ≠ 0 ∧ n • x = 0}
  zero_mem' := ⟨1, one_ne_zero, smul_zero 1⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have h1 : (n * m) • x = m • (n • x) := by rw [mul_comm, mul_smul]
    have h2 : (n * m) • y = n • (m • y) := by rw [mul_smul]
    rw [smul_add, h1, h2, hx, hy, smul_zero, smul_zero, add_zero]
  neg_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [smul_neg, hx, neg_zero]⟩

theorem mem_torsionAddSubgroup_iff {A : Type*} [AddCommGroup A] {x : A} :
    x ∈ torsionAddSubgroup A ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x = 0 := Iff.rfl

section MilnorTorsion

variable (F : Type*) [Field F]

/-- A symbol splits along a concatenation of its underlying list. -/
theorem milnorClassDeg_split (k : ℕ) (s : MilnorSymbolDeg F (2 + k))
    (s₁ : MilnorSymbolDeg F 2) (s₂ : MilnorSymbolDeg F k) (h : s.val = s₁.val ++ s₂.val) :
    milnorClassDeg F (2 + k) s
      = milnorMul F 2 k (milnorClassDeg F 2 s₁) (milnorClassDeg F k s₂) := by
  rw [milnorMul_class]
  exact congrArg _ (Subtype.ext h)

/-- **Degree at least two is torsion as soon as degree two is.** -/
theorem milnorKDeg_mem_torsion_of_two
    (h2 : ∀ x : MilnorKDeg F 2, x ∈ torsionAddSubgroup (MilnorKDeg F 2))
    (k : ℕ) (x : MilnorKDeg F (2 + k)) : x ∈ torsionAddSubgroup (MilnorKDeg F (2 + k)) := by
  have hgen : ∀ s : MilnorSymbolDeg F (2 + k),
      milnorClassDeg F (2 + k) s ∈ torsionAddSubgroup (MilnorKDeg F (2 + k)) := by
    intro s
    obtain ⟨s₁, s₂, hsplit⟩ : ∃ (s₁ : MilnorSymbolDeg F 2) (s₂ : MilnorSymbolDeg F k),
        s.val = s₁.val ++ s₂.val := by
      refine ⟨⟨s.val.take 2, ?_⟩, ⟨s.val.drop 2, ?_⟩, ?_⟩
      · rw [List.length_take, s.property]
        omega
      · rw [List.length_drop, s.property]
        omega
      · exact (List.take_append_drop 2 s.val).symm
    obtain ⟨n, hn, hnz⟩ := h2 (milnorClassDeg F 2 s₁)
    refine ⟨n, hn, ?_⟩
    rw [milnorClassDeg_split F k s s₁ s₂ hsplit]
    have hstep : n • milnorMul F 2 k (milnorClassDeg F 2 s₁) (milnorClassDeg F k s₂)
        = milnorMul F 2 k (n • milnorClassDeg F 2 s₁) (milnorClassDeg F k s₂) := by
      rw [map_zsmul]
      rfl
    rw [hstep, hnz, map_zero, AddMonoidHom.zero_apply]
  refine QuotientAddGroup.induction_on x fun w => ?_
  induction w using FreeAbelianGroup.induction_on with
  | zero => exact (torsionAddSubgroup _).zero_mem
  | of s => exact hgen s
  | neg s ih =>
      have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F (2 + k))
          (-FreeAbelianGroup.of s))
          = -(QuotientAddGroup.mk (s := milnorRelSubgroupDeg F (2 + k))
            (FreeAbelianGroup.of s)) := rfl
      rw [hmk]
      exact (torsionAddSubgroup _).neg_mem (hgen s)
  | add u v hu hv =>
      have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F (2 + k)) (u + v))
          = QuotientAddGroup.mk (s := milnorRelSubgroupDeg F (2 + k)) u
            + QuotientAddGroup.mk (s := milnorRelSubgroupDeg F (2 + k)) v := rfl
      rw [hmk]
      exact (torsionAddSubgroup _).add_mem hu hv

end MilnorTorsion

end GaloisForLFunctions.HTGeometry
