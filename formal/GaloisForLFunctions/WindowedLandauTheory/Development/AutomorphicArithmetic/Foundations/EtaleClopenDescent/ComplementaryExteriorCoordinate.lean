import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Determinant

/-! A complementary basis wedge extracts one exterior coordinate, up to
the sign of the permutation assembling the two ordered wedges. -/

noncomputable section

namespace GlobalTheory.PD

/-- Wedge with the ordered complement of a basis index to extract just
that coordinate in the top degree. -/
theorem exists_complementary_exterior_coordinate {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] {p q : ℕ} (b : Module.Basis (Fin (p + q)) R V)
    (y : ⋀[R]^q V) (J : Set.powersetCard (Fin (p + q)) q) :
    ∃ I : Set.powersetCard (Fin (p + q)) p, ∃ ε : ℤˣ,
      ExteriorAlgebra.ιMulti_family R p b I * (y : ExteriorAlgebra R V) =
        (ε : ℤ) • ((b.exteriorPower q).repr y J • ExteriorAlgebra.ιMulti R (p + q) b) := by
  classical
  have hcard : (J.valᶜ : Finset (Fin (p + q))).card = p := by
    rw [Finset.card_compl, Fintype.card_fin, show J.val.card = q from J.property]
    omega
  let I : Set.powersetCard (Fin (p + q)) p := ⟨J.valᶜ, hcard⟩
  have hdisj : Disjoint I.val J.val := disjoint_compl_left
  let B := b.exteriorPower q
  have hrepr : (y : ExteriorAlgebra R V) =
      ∑ L, B.repr y L • ExteriorAlgebra.ιMulti_family R q b L := by
    conv_lhs => rw [← B.sum_repr y]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [Submodule.coe_smul]
    simp only [B, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      ExteriorAlgebra.ιMulti_family, exteriorPower.ιMulti_apply_coe]
  refine ⟨I, ?_⟩
  rw [hrepr, Finset.mul_sum, Finset.sum_eq_single J]
  · rw [mul_smul_comm, ExteriorAlgebra.ιMulti_family_mul_of_disjoint _ _ _ _ hdisj]
    let U := Set.powersetCard.disjUnion hdisj
    let e := Set.powersetCard.ofFinEmbEquiv.symm U
    let σ : Equiv.Perm (Fin (p + q)) :=
      Equiv.ofBijective e ⟨e.injective, Finite.injective_iff_surjective.mp e.injective⟩
    have htop : ExteriorAlgebra.ιMulti_family R (p + q) b U =
        (σ.sign : ℤ) • ExteriorAlgebra.ιMulti R (p + q) b := by
      change ExteriorAlgebra.ιMulti R (p + q) (b ∘ σ) = _
      rw [AlternatingMap.map_perm, Units.smul_def]
    refine ⟨(Set.powersetCard.permOfDisjoint hdisj).sign * σ.sign, ?_⟩
    change B.repr y J • ((Set.powersetCard.permOfDisjoint hdisj).sign •
      ExteriorAlgebra.ιMulti_family R (p + q) b U) = _
    rw [htop, Units.smul_def, smul_smul, Units.val_mul, smul_comm (B.repr y J)]
  · intro L _ hL
    rw [mul_smul_comm, ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint, smul_zero]
    intro hd
    have hsub : L.val ⊆ J.val := by
      intro j hj
      by_contra hj'
      exact Finset.disjoint_left.mp hd (Finset.mem_compl.mpr hj') hj
    exact hL (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (J.property.trans L.property.symm).le))
  · intro hJ
    exact (hJ (Finset.mem_univ J)).elim

end GlobalTheory.PD
