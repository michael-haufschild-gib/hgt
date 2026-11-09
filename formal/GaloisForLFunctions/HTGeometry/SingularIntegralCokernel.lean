import GaloisForLFunctions.HTGeometry.IsogenyLattice

/-!
# Singular integral cokernels

A singular endomorphism of an integral lattice has a nonzero integral
functional annihilating its range. Multiples of a vector detected by that
functional remain distinct in the cokernel. Thus the determinant cardinality
formula extends to every endomorphism, with cardinal zero precisely for an
infinite cokernel.
-/

noncomputable section
namespace LinearMap
variable {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]

/-- A singular lattice endomorphism has an infinite cokernel. -/
theorem infinite_quotient_range_of_det_eq_zero (f : L →ₗ[ℤ] L) (hf : f.det = 0) :
    Infinite (L ⧸ f.range) := by
  have hd : f.dualMap.det = 0 := by rw [det_dualMap, hf]
  obtain ⟨l, hl, hl0⟩ := (Submodule.ne_bot_iff _).mp (det_eq_zero_iff_ker_ne_bot.mp hd)
  have hx : ∃ x : L, l x ≠ 0 := by
    by_contra h
    apply hl0
    ext x
    exact not_not.mp (fun hx => h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hx
  have hk : f.range ≤ l.ker := by
    rintro y ⟨z, rfl⟩
    have he := congrArg (fun g : Module.Dual ℤ L => g z) (mem_ker.mp hl)
    exact he
  let q := f.range.liftQ l hk
  apply Infinite.of_injective (fun a : ℤ => (Submodule.Quotient.mk (a • x) : L ⧸ f.range))
  intro a b hab
  have he := congrArg q hab
  change l (a • x) = l (b • x) at he
  simp only [map_smul, smul_eq_mul] at he
  exact mul_right_cancel₀ hx he

/-- The absolute determinant counts every integral cokernel, including singular ones. -/
theorem card_quotient_range_eq_natAbs_det_all (f : L →ₗ[ℤ] L) :
    Nat.card (L ⧸ f.range) = f.det.natAbs := by
  by_cases hf : f.det = 0
  · letI := infinite_quotient_range_of_det_eq_zero f hf
    rw [Nat.card_eq_zero_of_infinite, hf, Int.natAbs_zero]
  · exact card_quotient_range_eq_natAbs_det (injective_of_det_ne_zero hf)

#print axioms infinite_quotient_range_of_det_eq_zero
#print axioms card_quotient_range_eq_natAbs_det_all
end LinearMap
