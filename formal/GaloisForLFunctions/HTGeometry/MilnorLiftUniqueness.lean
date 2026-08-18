import GaloisForLFunctions.HTGeometry.MilnorGradedSurjectivity

/-!
# The lift of a residue class below the degree of the place is unique

At the place of an irreducible `π` of degree `d`, every residue class is the residue of a polynomial
of degree below `d`, and that polynomial is **unique**: two such polynomials with the same residue
differ by a multiple of `π` of degree below `deg π`, hence are equal.

This is what makes Milnor's section well defined without any choice: the reduction map from the
nonzero polynomials of degree below `d` to the residue field is a bijection onto the units.

* `polyUnit_degree_lt_unique` : **uniqueness of the lift.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- **Uniqueness of the lift below the degree of the place.** -/
theorem polyUnit_degree_lt_unique {π p q : Polynomial F} (hπ : Irreducible π)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hpd : p.natDegree < π.natDegree) (hqd : q.natDegree < π.natDegree)
    (h : (polyResidueData hπ).residueUnit (polyUnit hp)
      = (polyResidueData hπ).residueUnit (polyUnit hq)) : p = q := by
  classical
  have hpm : p ∉ Ideal.span {π} := notMem_span_of_natDegree_lt hp hpd
  have hqm : q ∉ Ideal.span {π} := notMem_span_of_natDegree_lt hq hqd
  rw [polyResidueData_residueUnit_eq hπ hp hpm, polyResidueData_residueUnit_eq hπ hq hqm] at h
  have hval := congrArg Units.val h
  have hmk : Ideal.Quotient.mk (polyPlace hπ).asIdeal p
      = Ideal.Quotient.mk (polyPlace hπ).asIdeal q := by
    rw [← residueFieldAtPlaceEquiv_residueUnit (RatFunc F) (polyPlace hπ) hp hpm,
      ← residueFieldAtPlaceEquiv_residueUnit (RatFunc F) (polyPlace hπ) hq hqm]
    exact congrArg _ hval
  have hmem : (p - q) ∈ (polyPlace hπ).asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hmk, sub_self]
  rw [polyPlace_asIdeal] at hmem
  have hdvd : π ∣ (p - q) := (Ideal.mem_span_singleton).1 hmem
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.2 hne
  have hge : π.natDegree ≤ (p - q).natDegree := natDegree_le_of_dvd hdvd hsub
  have hle : (p - q).natDegree ≤ max p.natDegree q.natDegree := natDegree_sub_le p q
  omega

/-- **The residue of a polynomial unit, read in `F[X]/(π)`.**  This turns every residue computation
at a polynomial place into a computation in the quotient ring, where sums and products are
transparent. -/
theorem residueFieldEquiv_polyUnit {π : Polynomial F} (hπ : Irreducible π) {p : Polynomial F}
    (hp : p ≠ 0) (hpm : p ∉ Ideal.span {π}) :
    residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ)
        (((polyResidueData hπ).residueUnit (polyUnit hp) :
          (IsLocalRing.ResidueField
            (((polyPlace hπ).valuation (RatFunc F)).valuationSubring))ˣ) :
          IsLocalRing.ResidueField (((polyPlace hπ).valuation (RatFunc F)).valuationSubring))
      = Ideal.Quotient.mk (polyPlace hπ).asIdeal p := by
  rw [polyResidueData_residueUnit_eq hπ hp hpm]
  exact residueFieldAtPlaceEquiv_residueUnit (RatFunc F) (polyPlace hπ) hp hpm

/-- Two polynomial units with the same residue differ by a multiple of `π`. -/
theorem dvd_sub_of_residueUnit_eq {π : Polynomial F} (hπ : Irreducible π) {p q : Polynomial F}
    (hp : p ≠ 0) (hq : q ≠ 0) (hpm : p ∉ Ideal.span {π}) (hqm : q ∉ Ideal.span {π})
    (h : (polyResidueData hπ).residueUnit (polyUnit hp)
      = (polyResidueData hπ).residueUnit (polyUnit hq)) : π ∣ (p - q) := by
  have hval := congrArg Units.val h
  have hmk : Ideal.Quotient.mk (polyPlace hπ).asIdeal p
      = Ideal.Quotient.mk (polyPlace hπ).asIdeal q := by
    rw [← residueFieldEquiv_polyUnit hπ hp hpm, ← residueFieldEquiv_polyUnit hπ hq hqm]
    exact congrArg _ hval
  have hmem : (p - q) ∈ (polyPlace hπ).asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hmk, sub_self]
  rw [polyPlace_asIdeal] at hmem
  exact (Ideal.mem_span_singleton).1 hmem

/-- **Lifts of `ȳ` and `1 − ȳ` add up to `1` modulo `π`.** -/
theorem dvd_add_sub_one_of_residueUnit {π : Polynomial F} (hπ : Irreducible π)
    {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpm : p ∉ Ideal.span {π}) (hqm : q ∉ Ideal.span {π})
    {y : (IsLocalRing.ResidueField
      (((polyPlace hπ).valuation (RatFunc F)).valuationSubring))ˣ}
    (hy : ((y : IsLocalRing.ResidueField
      (((polyPlace hπ).valuation (RatFunc F)).valuationSubring))) ≠ 1)
    (hpy : (polyResidueData hπ).residueUnit (polyUnit hp) = y)
    (hqy : (polyResidueData hπ).residueUnit (polyUnit hq) = oneSubUnit hy) :
    π ∣ (p + q - 1) := by
  have hmkp : Ideal.Quotient.mk (polyPlace hπ).asIdeal p
      = residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ) (y : _) := by
    rw [← residueFieldEquiv_polyUnit hπ hp hpm, hpy]
  have hmkq : Ideal.Quotient.mk (polyPlace hπ).asIdeal q
      = residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ) ((oneSubUnit hy : _) : _) := by
    rw [← residueFieldEquiv_polyUnit hπ hq hqm, hqy]
  have hsum : Ideal.Quotient.mk (polyPlace hπ).asIdeal (p + q - 1) = 0 := by
    rw [map_sub, map_add, hmkp, hmkq, map_one, ← map_add, oneSubUnit_val]
    have : (y : IsLocalRing.ResidueField
        (((polyPlace hπ).valuation (RatFunc F)).valuationSubring)) + (1 - (y : _)) = 1 := by
      ring
    rw [this, map_one, sub_self]
  have hmem : (p + q - 1) ∈ (polyPlace hπ).asIdeal := (Ideal.Quotient.eq_zero_iff_mem).1 hsum
  rw [polyPlace_asIdeal] at hmem
  exact (Ideal.mem_span_singleton).1 hmem

/-- **The product of two lifts agrees modulo `π` with the lift of the product.** -/
theorem dvd_mul_sub_of_residueUnit {π : Polynomial F} (hπ : Irreducible π)
    {p q r : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hpm : p ∉ Ideal.span {π}) (hqm : q ∉ Ideal.span {π}) (hrm : r ∉ Ideal.span {π})
    (h : (polyResidueData hπ).residueUnit (polyUnit hp)
        * (polyResidueData hπ).residueUnit (polyUnit hq)
      = (polyResidueData hπ).residueUnit (polyUnit hr)) :
    π ∣ (p * q - r) := by
  have hval := congrArg Units.val h
  rw [Units.val_mul] at hval
  have hmk : Ideal.Quotient.mk (polyPlace hπ).asIdeal (p * q - r) = 0 := by
    rw [map_sub, map_mul, ← residueFieldEquiv_polyUnit hπ hp hpm,
      ← residueFieldEquiv_polyUnit hπ hq hqm, ← residueFieldEquiv_polyUnit hπ hr hrm,
      ← map_mul, hval, sub_self]
  have hmem : (p * q - r) ∈ (polyPlace hπ).asIdeal := (Ideal.Quotient.eq_zero_iff_mem).1 hmk
  rw [polyPlace_asIdeal] at hmem
  exact (Ideal.mem_span_singleton).1 hmem

end GaloisForLFunctions.HTGeometry
