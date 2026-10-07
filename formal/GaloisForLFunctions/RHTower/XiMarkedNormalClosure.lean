import GaloisForLFunctions.RHTower.XiMarkedFiniteMonodromy

open GaloisForLFunctions.HTGeometry

namespace RHTower.XiMarkedMonodromy

instance diagonalWindingSubgroup_normal (A : Finset ℝ) :
    (diagonalWindingSubgroup A).Normal where
  conj_mem := by
    rintro q ⟨k, hk⟩ g
    refine ⟨k, fun a => ?_⟩
    change zeroWinding (g a * q a * (g a)⁻¹) = k
    rw [zeroWinding.map_mul, zeroWinding.map_mul, map_inv, hk]
    simp [mul_comm]

/-- Any normal subgroup containing actual Xi monodromy contains every diagonal-winding tuple. -/
theorem diagonal_le_normal_of_range_le (A : Finset ℝ) (N : Subgroup (JointGroup A))
    [N.Normal] (hN : (jointMap A).range ≤ N) : diagonalWindingSubgroup A ≤ N := by
  classical
  have hsingle (a : A) (q : TargetGroup) (hq : zeroWinding q = 1) : Pi.mulSingle a q ∈ N := by
    obtain ⟨g, hg⟩ := exists_common_conjugate_packet A a (fun _ : Unit => q) (fun _ => hq)
    let e : TargetGroup →* JointGroup A := MonoidHom.mulSingle (fun _ : A => TargetGroup) a
    have hmem : e (g * q * g⁻¹) ∈ N := hN (hg ())
    have hconj := (inferInstance : N.Normal).conj_mem _ hmem (e g)⁻¹
    change e q ∈ N
    simpa only [map_mul, map_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hconj
  have hproduct (q : JointGroup A) (hq : ∀ a, zeroWinding (q a) = 1) : q ∈ N :=
    Subgroup.pi_mem_of_mulSingle_mem q fun a => hsingle a (q a) (hq a)
  rintro q ⟨k, hk⟩
  obtain ⟨p, hp⟩ := xi_winding_surjective A k
  let u := jointMap A p
  have hu (a : A) : zeroWinding (u a) = k := (zeroWinding_jointMap A p a).trans hp
  have hker : ∀ a : A, zeroWinding ((q * u⁻¹) a) = 1 := by
    intro a
    change zeroWinding (q a * (u a)⁻¹) = 1
    rw [map_mul, map_inv, hk, hu, mul_inv_cancel]
  have huN : u ∈ N := hN ⟨p, rfl⟩
  have hmul := N.mul_mem (hproduct (q * u⁻¹) hker) huN
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul

/-- The exact discrete normal closure; no identification of the nonnormal image is asserted. -/
theorem jointMap_normalClosure_eq_diagonal (A : Finset ℝ) :
    Subgroup.normalClosure ((jointMap A).range : Set (JointGroup A)) =
      diagonalWindingSubgroup A := by
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (jointMap_range_le_diagonal A)
  · exact diagonal_le_normal_of_range_le A _ Subgroup.le_normalClosure

end RHTower.XiMarkedMonodromy
