import GaloisForLFunctions.HTGeometry.AffineExponentialProjectionClassification
import GaloisForLFunctions.HTGeometry.ConductorNearbyCycleSpecialization

/-!
# Saturation of character-relation lattices

An integral relation lattice is saturated exactly when its quotient character group has no
nonzero element killed by a positive integer.  This is the lattice-theoretic bridge used when
connectedness of a diagonalizable projection is converted into absence of finite character
quotients.
-/

namespace GaloisForLFunctions.HTGeometry
namespace CharacterLatticeSaturation

noncomputable section

/-- Integral saturation of an additive subgroup is equivalent to positive-integer torsion
freeness of the quotient group. -/
theorem integerSaturated_toIntSubmodule_iff_quotient_nsmul_eq_zero
    {M : Type*} [AddCommGroup M] (L : AddSubgroup M) :
    IntegerSaturated L.toIntSubmodule ↔
      ∀ (n : ℕ) (q : M ⧸ L), 0 < n → n • q = 0 → q = 0 := by
  constructor
  · intro hsat n q hn hnq
    obtain ⟨m, rfl⟩ := QuotientAddGroup.mk'_surjective L q
    rw [← map_nsmul] at hnq
    change (↑(n • m) : M ⧸ L) = 0 at hnq
    change (↑m : M ⧸ L) = 0
    apply (QuotientAddGroup.eq_zero_iff m).mpr
    exact hsat n m hn ((QuotientAddGroup.eq_zero_iff (n • m)).mp hnq)
  · intro htor n m hn hnm
    have hnq : n • QuotientAddGroup.mk' L m = 0 := by
      rw [← map_nsmul]
      change (↑(n • m) : M ⧸ L) = 0
      apply (QuotientAddGroup.eq_zero_iff (n • m)).mpr
      exact hnm
    have hq := htor n (QuotientAddGroup.mk' L m) hn hnq
    change (↑m : M ⧸ L) = 0 at hq
    exact (QuotientAddGroup.eq_zero_iff m).mp hq

open AffineExponentialGroup
open AffineExponentialProjectionClassification

/-- Exact saturation criterion for the character-relation lattice of the torus projection of a
mixed affine-exponential subgroup. -/
theorem torusRelationLattice_integerSaturated_iff_quotient_nsmul_eq_zero
    (k : Type*) [Field k] {n : ℕ}
    (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k] :
    IntegerSaturated (torusRelationLattice k I).toIntSubmodule ↔
      ∀ (d : ℕ) (q : (Fin n →₀ ℤ) ⧸ torusRelationLattice k I),
        0 < d → d • q = 0 → q = 0 :=
  integerSaturated_toIntSubmodule_iff_quotient_nsmul_eq_zero
    (torusRelationLattice k I)

end
end CharacterLatticeSaturation
end GaloisForLFunctions.HTGeometry
