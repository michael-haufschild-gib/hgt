import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplementaryExteriorCoordinate

/-! Pairing complementary exterior degrees by a nonzero top coefficient
detects every nonzero form. -/

noncomputable section

namespace GlobalTheory.PD

/-- A top coefficient separates complementary degrees by multiplication. -/
theorem wedge_pairing_sep {K V : Type} [Field K] [AddCommGroup V] [Module K V] {p q : ℕ}
    (b : Module.Basis (Fin (p + q)) K V) (τ : ExteriorAlgebra K V →ₗ[K] K)
    (hτ : τ (ExteriorAlgebra.ιMulti K (p + q) b) ≠ 0) (y : ExteriorAlgebra K V)
    (hy : y ∈ ⋀[K]^q V) (h : ∀ a ∈ ⋀[K]^p V, τ (a * y) = 0) : y = 0 := by
  let Y : ⋀[K]^q V := ⟨y, hy⟩
  let B := b.exteriorPower q
  suffices hY : B.repr Y = 0 by
    exact congrArg Subtype.val (B.repr.injective (hY.trans (map_zero B.repr).symm))
  ext J
  change B.repr Y J = 0
  obtain ⟨I, ε, hI⟩ := exists_complementary_exterior_coordinate b Y J
  have hu : ExteriorAlgebra.ιMulti_family K p b I ∈ ⋀[K]^p V := by
    simpa only [exteriorPower.ιMulti_family, ExteriorAlgebra.ιMulti_family,
      exteriorPower.ιMulti_apply_coe] using (exteriorPower.ιMulti_family K p b I).property
  have hz := h _ hu
  change τ (ExteriorAlgebra.ιMulti_family K p b I * (Y : ExteriorAlgebra K V)) = 0 at hz
  rw [hI, map_zsmul, map_smul, smul_eq_mul] at hz
  have hc := congrArg (fun u : K => (ε : ℤ) • u) hz
  simp only [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, smul_zero] at hc
  exact (mul_eq_zero.mp hc).resolve_right hτ

end GlobalTheory.PD
