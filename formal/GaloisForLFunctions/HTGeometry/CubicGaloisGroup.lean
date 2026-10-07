import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic

/-!
# The Galois group of an irreducible cubic with nonsquare discriminant

The discriminant square root in the splitting field forces a quadratic
subextension. Cubic irreducibility forces a factor of three in the Galois
group order, while its faithful action on three roots bounds the order by
six. Thus the action is the full symmetric group and the splitting degree
is six.
-/

open Polynomial
namespace GaloisForLFunctions.HTGeometry

/-- A nonsquare cubic discriminant forces a quadratic subextension of the splitting field. -/
theorem two_dvd_cubic_splittingField_finrank {K : Type*} [Field K]
    (P : Cubic K) (ha : P.a ≠ 0) (hns : ¬ IsSquare P.discr) :
    2 ∣ Module.finrank K P.toPoly.SplittingField := by
  let L := P.toPoly.SplittingField
  obtain ⟨x, y, z, hroots⟩ :=
    (Cubic.splits_iff_roots_eq_three ha).mp (SplittingField.splits P.toPoly)
  let r : L := algebraMap K L P.a * algebraMap K L P.a * (x - y) * (x - z) * (y - z)
  have hr : algebraMap K L P.discr = r ^ 2 :=
    Cubic.discr_eq_prod_three_roots ha hroots
  let q : K[X] := X ^ 2 - C P.discr
  have hq : Irreducible q := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · simp [q]
    · intro t ht
      have ht' : t ^ 2 - P.discr = 0 := by simpa [q, IsRoot] using ht
      apply hns
      exact ⟨t, by rw [← pow_two]; exact (sub_eq_zero.mp ht').symm⟩
  have hqs : (q.map (algebraMap K L)).Splits := by
    have he : q.map (algebraMap K L) = (X - C r) * (X - C (-r)) := by
      simp only [q, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, hr, map_pow, map_neg]
      ring
    rw [he]
    exact (Splits.X_sub_C r).mul (Splits.X_sub_C (-r))
  simpa only [q, natDegree_X_pow_sub_C] using hq.natDegree_dvd_finrank hqs

/-- An irreducible cubic with nonsquare discriminant has a six-element Galois group. -/
theorem cubic_galois_card_eq_six {K : Type*} [Field K] [CharZero K]
    (P : Cubic K) (ha : P.a ≠ 0) (hirr : Irreducible P.toPoly)
    (hns : ¬ IsSquare P.discr) : Nat.card P.toPoly.Gal = 6 := by
  classical
  let p := P.toPoly
  let L := p.SplittingField
  letI : Fact ((p.map (algebraMap K L)).Splits) := ⟨SplittingField.splits p⟩
  have hdeg : p.natDegree = 3 := Cubic.natDegree_of_a_ne_zero ha
  have htwo : 2 ∣ Nat.card p.Gal := by
    rw [Gal.card_of_separable hirr.separable]
    exact two_dvd_cubic_splittingField_finrank P ha hns
  have hthree : 3 ∣ Nat.card p.Gal := by
    have h := Gal.prime_degree_dvd_card hirr (by rw [hdeg]; norm_num)
    simpa only [Cubic.natDegree_of_a_ne_zero ha] using h
  have hsix : 6 ∣ Nat.card p.Gal :=
    (by norm_num : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  have hroots : Fintype.card (p.rootSet L) = 3 := by
    rw [card_rootSet_eq_natDegree hirr.separable (SplittingField.splits p), hdeg]
  have hperm : Nat.card (Equiv.Perm (p.rootSet L)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, hroots]
    norm_num
  have hu := Nat.card_le_card_of_injective (Gal.galActionHom p L)
    (Gal.galActionHom_injective p L)
  rw [hperm] at hu
  exact hu.antisymm (Nat.le_of_dvd Nat.card_pos hsix)

/-- The full permutation action on the three roots of an irreducible nonsquare cubic. -/
noncomputable def cubicGaloisEquivPermThree {K : Type*} [Field K] [CharZero K]
    (P : Cubic K) (ha : P.a ≠ 0) (hirr : Irreducible P.toPoly)
    (hns : ¬ IsSquare P.discr) : P.toPoly.Gal ≃* Equiv.Perm (Fin 3) := by
  classical
  let p := P.toPoly
  let L := p.SplittingField
  letI : Fact ((p.map (algebraMap K L)).Splits) := ⟨SplittingField.splits p⟩
  have hroots : Fintype.card (p.rootSet L) = 3 := by
    rw [card_rootSet_eq_natDegree hirr.separable (SplittingField.splits p)]
    exact Cubic.natDegree_of_a_ne_zero ha
  have hbij : Function.Bijective (Gal.galActionHom p L) := by
    apply (Gal.galActionHom_injective p L).bijective_of_nat_card_le
    rw [Nat.card_perm, Nat.card_eq_fintype_card, hroots,
      cubic_galois_card_eq_six P ha hirr hns]
    norm_num
  exact (MulEquiv.ofBijective (Gal.galActionHom p L) hbij).trans
    (Fintype.equivFinOfCardEq hroots).permCongrHom

/-- The splitting extension of an irreducible nonsquare cubic has degree six. -/
theorem cubic_splittingField_finrank_eq_six {K : Type*} [Field K] [CharZero K]
    (P : Cubic K) (ha : P.a ≠ 0) (hirr : Irreducible P.toPoly)
    (hns : ¬ IsSquare P.discr) : Module.finrank K P.toPoly.SplittingField = 6 := by
  rw [← Gal.card_of_separable hirr.separable]
  exact cubic_galois_card_eq_six P ha hirr hns

end GaloisForLFunctions.HTGeometry
