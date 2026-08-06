import GaloisForLFunctions.HTGeometry.TransverseChannelLift

/-!
# Two points of one fibre make their product degenerate

Any two points of the same fibre satisfy an exact relation below the horizon: the difference of the
completed jets is the product of the two jets against the difference of the completed reciprocals.
Since the first difference has degree below the first depth and the second below the second, this
exhibits a nonzero element of the kernel of the convolution pairing at the *product* of the two
jets.

So the products of pairs of distinct fibre points are confined to the degeneracy locus of that
pairing — the same square convolution system whose nonsingularity makes a transverse channel
uniquely liftable.  In particular no two distinct points of a fibre have a product congruent to a
jet with a nonsingular pairing.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## The exact relation -/

section Relation

variable {R : Type*} [CommRing R]

/-- **The product relation between two compatible pairs.**  The identity behind it is that the
difference of the jets, corrected by the product against the difference of the reciprocals, is a
combination of the two compatibility defects. -/
theorem product_relation_identity (U V A A' B B' : R[X]) :
    (A - A') - ((A + U) * (A' + U)) * (B' - B)
      = (A' + U) * ((A + U) * (B + V) - 1) - (A + U) * ((A' + U) * (B' + V) - 1) := by
  ring

/-- **Two compatible pairs of one observation satisfy the product relation below the horizon.** -/
theorem dvd_product_relation {L : ℕ} {U V A A' B B' : R[X]}
    (h : (X : R[X]) ^ L ∣ ((A + U) * (B + V) - 1))
    (h' : (X : R[X]) ^ L ∣ ((A' + U) * (B' + V) - 1)) :
    (X : R[X]) ^ L ∣ ((A - A') - ((A + U) * (A' + U)) * (B' - B)) := by
  rw [product_relation_identity U V A A' B B']
  exact dvd_sub (Dvd.dvd.mul_left h _) (Dvd.dvd.mul_left h' _)

end Relation

/-! ## The degeneracy at the product -/

section Degenerate

variable {K : Type*} [Field K] {m n : ℕ}

/-- **Two distinct fibre points produce a nonzero kernel vector of the pairing at their product.**
The kernel vector is the pair of differences: the jets differ below the first depth, the reciprocals
below the second, and the jet difference is nonzero because a fibre point is determined by its
jet. -/
theorem exists_kernel_of_fibre_ne (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (p q : criticalFibre K m n U V) (hpq : p ≠ q) :
    ∃ α β : K[X], α ≠ 0 ∧ α.degree < (m : ℕ) ∧ β.degree < (n : ℕ) ∧
      (X : K[X]) ^ (m + n) ∣ (α - ((p.1.1 + U) * (q.1.1 + U)) * β) := by
  refine ⟨p.1.1 - q.1.1, q.1.2 - p.1.2, ?_, ?_, ?_, ?_⟩
  · intro h0
    exact hpq (criticalFibre_fst_injective hm hn hU0 hV0 (sub_eq_zero.1 h0))
  · exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt p.2.1 q.2.1)
  · exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt q.2.2.1 p.2.2.1)
  · exact dvd_product_relation
      ((dvd_criticalLowProduct_sub_one_iff_mul_sub_one hU hV _ _).1 p.2.2.2)
      ((dvd_criticalLowProduct_sub_one_iff_mul_sub_one hU hV _ _).1 q.2.2.2)

/-- **The convolution pairing at the product of two distinct fibre points is singular.**  This is
the same pairing whose injectivity makes a transverse channel uniquely liftable, so a fibre with two
points forbids that product from being a nonsingular longitudinal jet. -/
theorem not_injective_transverseDifferential_of_fibre_ne (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (p q : criticalFibre K m n U V) (hpq : p ≠ q) :
    ¬ Function.Injective
      (transverseDifferential ((p.1.1 + U) * (q.1.1 + U)) m n (m + n)) := by
  obtain ⟨α, β, hα0, hα, hβ, hdvd⟩ := exists_kernel_of_fibre_ne hm hn hU hV hU0 hV0 p q hpq
  intro hinj
  have hker : transverseDifferential ((p.1.1 + U) * (q.1.1 + U)) m n (m + n)
      (⟨α, mem_degreeLT.2 hα⟩, ⟨β, mem_degreeLT.2 hβ⟩) = 0 :=
    transverseDifferential_eq_zero_iff.2 hdvd
  have hzero : ((⟨α, mem_degreeLT.2 hα⟩ : degreeLT K m), (⟨β, mem_degreeLT.2 hβ⟩ : degreeLT K n))
      = 0 := hinj (by rw [hker, map_zero])
  exact hα0 (congrArg Subtype.val (congrArg Prod.fst hzero))

/-- **No two distinct points of a fibre have the unipotent jet as their product.**  The unipotent
jet has a nonsingular convolution pairing. -/
theorem product_ne_one_add_X_pow_of_fibre_ne (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (p q : criticalFibre K m n U V) (hpq : p ≠ q) :
    (p.1.1 + U) * (q.1.1 + U) ≠ 1 + X ^ m := by
  intro hprod
  refine not_injective_transverseDifferential_of_fibre_ne hm hn hU hV hU0 hV0 p q hpq ?_
  rw [hprod]
  exact injective_transverseDifferential hm

end Degenerate

end GaloisForLFunctions.HTGeometry
