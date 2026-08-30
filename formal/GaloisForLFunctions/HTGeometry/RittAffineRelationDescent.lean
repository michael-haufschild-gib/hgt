import GaloisForLFunctions.HTGeometry.RittAffineSliceResidue

/-!
# An affine relation descends over an affinely moved generator

The jet tower moves its coordinates affinely, `σ t = a·t + b`, above jet order one.  An affine
relation

`ν · σ W = W + β`,  `W` a coprime fraction in `t` over the coefficient field,

is the eigen-inhomogeneous slice with eigenvalue `ν⁻¹` and *zero* linear inhomogeneity coefficient,
so the residue classification leaves only two possibilities for the top-degree identity: the residue
is `0`, or it is the constant `ν⁻¹·β`.  Dividing back through, the descended relation is

`(ν · a^s) · φ(u) = u + β`   or   `(ν · a^s) · φ(u) = u`,   `s = deg P − deg Q`,

for the leading coefficient `u ≠ 0` of the numerator.  So the *shape* of an affine relation survives
one level of the tower, with the scalar multiplied by a power of the coordinate's multiplier — and
the only alternative is that the relation degenerates to an eigen-relation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- **The affine descent step.** -/
theorem exists_affine_or_eigen_descent (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a b ν β : E} (ha : a ≠ 0) (hν : ν ≠ 0)
    (hσt : σ t = algebraMap E L a * t + algebraMap E L b)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : algebraMap E L ν * σ W = W + algebraMap E L β) :
    ∃ (u : E) (s : ℤ), u ≠ 0 ∧
      ((ν * a ^ s) * φ u = u + β ∨ (ν * a ^ s) * φ u = u) := by
  classical
  have hνL : algebraMap E L ν ≠ 0 := (map_ne_zero_iff _ (algebraMap E L).injective).mpr hν
  have hνinv : ν⁻¹ ≠ 0 := inv_ne_zero hν
  have hrel' : σ W = algebraMap E L ν⁻¹ * W
      + (algebraMap E L 0 * t + algebraMap E L (ν⁻¹ * β)) := by
    rw [map_zero, zero_mul, zero_add, map_mul, map_inv₀]
    field_simp
    linear_combination hrel
  obtain ⟨u, r, D, e, hu0, hr, hmain⟩ :=
    exists_eigen_relation_residue_of_affine_mem_adjoin σ φ hcomp ht ha hνinv hσt hW0 hW hrel'
  have haD : (a : E) ^ D ≠ 0 := pow_ne_zero _ ha
  have hae : (a : E) ^ e ≠ 0 := pow_ne_zero _ ha
  have hzpow : (a : E) ^ ((D : ℤ) - e) = a ^ D / a ^ e := by
    rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
  refine ⟨u, (D : ℤ) - e, hu0, ?_⟩
  have hzero : r = 0 → (ν * a ^ ((D : ℤ) - e)) * φ u = u := by
    intro hr0
    rw [hr0, add_zero] at hmain
    have hm2 : ν * (φ u * a ^ D) = a ^ e * u := by
      rw [hmain]
      field_simp
    rw [hzpow]
    field_simp
    linear_combination hm2
  rcases hr with hr | hr | hr
  · exact Or.inr (hzero hr)
  · exact Or.inr (hzero hr)
  · left
    rw [hr] at hmain
    have hm2 : ν * (φ u * a ^ D) = a ^ e * (u + β) := by
      rw [hmain]
      field_simp
    rw [hzpow]
    field_simp
    linear_combination hm2

end GaloisForLFunctions.HTGeometry
