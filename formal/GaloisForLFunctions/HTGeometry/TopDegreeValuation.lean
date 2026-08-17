import GaloisForLFunctions.HTGeometry.CascadeChainRule
import Mathlib.RingTheory.Valuation.Basic

/-!
# The degree in one coordinate is a valuation

The peel compares entries of a determinant by their degree in the newest coordinate.  That degree
is not an ad hoc bookkeeping device: `TopDegLE m d` is exactly the condition `-d ≤ v` for the
additive valuation `v = topOrd m` of the coordinate field, the order at infinity in the coordinate
`m`.  Writing an element as a quotient of polynomials, `topOrd m` is the excess of the denominator's
`m`-degree over the numerator's, and it does not depend on the representative because `degreeOf` is
additive on products of nonzero polynomials.

Recording the valuation makes the degree layer transportable: an algebraic extension of the
coordinate field carries a degree layer exactly when the valuation extends to it.  The coordinate
derivations move along the valuation in the two ways the peel uses: the derivation at the coordinate
itself raises the order by one, and every other coordinate derivation does not lower it.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The numerator of the chosen representative. -/
noncomputable def secNum (f : CascadeField) : MvPolynomial ℕ ℂ :=
  (IsLocalization.sec (nonZeroDivisors (MvPolynomial ℕ ℂ)) f).1

/-- The denominator of the chosen representative. -/
noncomputable def secDen (f : CascadeField) : MvPolynomial ℕ ℂ :=
  ((IsLocalization.sec (nonZeroDivisors (MvPolynomial ℕ ℂ)) f).2 : MvPolynomial ℕ ℂ)

theorem topDegreeAlgebraMap_ne_zero_of_ne_zero {D : MvPolynomial ℕ ℂ} (hD : D ≠ 0) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField D ≠ 0 := by
  intro h
  exact hD (IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField (by simpa using h))

theorem secDen_ne_zero (f : CascadeField) : secDen f ≠ 0 := by
  have := (IsLocalization.sec (nonZeroDivisors (MvPolynomial ℕ ℂ)) f).2.2
  rwa [mem_nonZeroDivisors_iff_ne_zero] at this

theorem secSpec (f : CascadeField) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (secDen f) * f
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (secNum f) := by
  rw [mul_comm]
  exact IsLocalization.sec_spec _ f

theorem secNum_ne_zero {f : CascadeField} (hf : f ≠ 0) : secNum f ≠ 0 := by
  intro h
  have := secSpec f
  rw [h, map_zero] at this
  exact hf ((mul_eq_zero.mp this).resolve_left (topDegreeAlgebraMap_ne_zero_of_ne_zero (secDen_ne_zero f)))

/-- The order at infinity in the coordinate `m`, read off the chosen representative. -/
noncomputable def topOrdRep (m : ℕ) (f : CascadeField) : ℤ :=
  ((secDen f).degreeOf m : ℤ) - ((secNum f).degreeOf m : ℤ)

/-- The order does not depend on the representative. -/
theorem topOrdRep_eq {m : ℕ} {f : CascadeField} (hf : f ≠ 0) {N D : MvPolynomial ℕ ℂ}
    (hD : D ≠ 0)
    (h : algebraMap (MvPolynomial ℕ ℂ) CascadeField D * f
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField N) :
    topOrdRep m f = (D.degreeOf m : ℤ) - (N.degreeOf m : ℤ) := by
  have hD₀ := secDen_ne_zero f
  have hN₀ := secNum_ne_zero hf
  have hcross : N * secDen f = D * secNum f := by
    refine IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField ?_
    rw [map_mul, map_mul, ← h, ← secSpec f]
    ring
  have hN : N ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact hf ((mul_eq_zero.mp h).resolve_left (topDegreeAlgebraMap_ne_zero_of_ne_zero hD))
  have hdeg : (N * secDen f).degreeOf m = (D * secNum f).degreeOf m := by rw [hcross]
  rw [MvPolynomial.degreeOf_mul_eq hN hD₀, MvPolynomial.degreeOf_mul_eq hD hN₀] at hdeg
  rw [topOrdRep]
  omega

/-- The order at infinity in the coordinate `m`, as an element of `ℤ ∪ {∞}`. -/
noncomputable def topOrd (m : ℕ) (f : CascadeField) : WithTop ℤ :=
  if f = 0 then ⊤ else (topOrdRep m f : ℤ)

@[simp]
theorem topOrd_zero (m : ℕ) : topOrd m (0 : CascadeField) = ⊤ := if_pos rfl

theorem topOrd_of_ne_zero {m : ℕ} {f : CascadeField} (hf : f ≠ 0) :
    topOrd m f = (topOrdRep m f : ℤ) := if_neg hf

theorem topOrd_eq_top_iff {m : ℕ} {f : CascadeField} : topOrd m f = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    rw [topOrd_of_ne_zero hf] at h
    exact WithTop.coe_ne_top h
  · rintro rfl
    exact topOrd_zero m

/-- **The degree layer is the valuation.** -/
theorem topDegLE_iff_le_topOrd (m : ℕ) (d : ℤ) (f : CascadeField) :
    TopDegLE m d f ↔ ((-d : ℤ) : WithTop ℤ) ≤ topOrd m f := by
  constructor
  · rintro ⟨N, D, hD, hf, hdeg⟩
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [topOrd_zero]
      exact le_top
    · rw [topOrd_of_ne_zero hf0, topOrdRep_eq hf0 hD hf, WithTop.coe_le_coe]
      omega
  · intro h
    rcases eq_or_ne f 0 with rfl | hf0
    · exact topDegLE_zero m d
    · rw [topOrd_of_ne_zero hf0, WithTop.coe_le_coe] at h
      refine ⟨secNum f, secDen f, secDen_ne_zero f, secSpec f, ?_⟩
      rw [topOrdRep] at h
      omega

/-! ## The valuation axioms -/

@[simp]
theorem topOrd_one (m : ℕ) : topOrd m (1 : CascadeField) = (0 : ℤ) := by
  rw [topOrd_of_ne_zero (one_ne_zero (α := CascadeField)),
    topOrdRep_eq (m := m) (one_ne_zero (α := CascadeField)) (one_ne_zero (α := MvPolynomial ℕ ℂ))
      (by rw [map_one, mul_one])]
  simp

theorem topOrd_mul (m : ℕ) (f g : CascadeField) :
    topOrd m (f * g) = topOrd m f + topOrd m g := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hprod : algebraMap (MvPolynomial ℕ ℂ) CascadeField (secDen f * secDen g) * (f * g)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (secNum f * secNum g) := by
    rw [map_mul, map_mul, ← secSpec f, ← secSpec g]
    ring
  rw [topOrd_of_ne_zero hfg, topOrd_of_ne_zero hf, topOrd_of_ne_zero hg,
    topOrdRep_eq hfg (mul_ne_zero (secDen_ne_zero f) (secDen_ne_zero g)) hprod,
    MvPolynomial.degreeOf_mul_eq (secDen_ne_zero f) (secDen_ne_zero g),
    MvPolynomial.degreeOf_mul_eq (secNum_ne_zero hf) (secNum_ne_zero hg), topOrdRep, topOrdRep,
    ← WithTop.coe_add]
  congr 1
  push_cast
  ring

theorem topOrd_add (m : ℕ) (f g : CascadeField) :
    min (topOrd m f) (topOrd m g) ≤ topOrd m (f + g) := by
  rcases eq_or_ne (min (topOrd m f) (topOrd m g)) ⊤ with h | h
  · have ha : topOrd m f = ⊤ := top_le_iff.mp (h ▸ min_le_left (topOrd m f) (topOrd m g))
    have hb : topOrd m g = ⊤ := top_le_iff.mp (h ▸ min_le_right (topOrd m f) (topOrd m g))
    have hsum : topOrd m (f + g) = ⊤ := by
      rw [topOrd_eq_top_iff.mp ha, topOrd_eq_top_iff.mp hb, add_zero, topOrd_zero]
    rw [hsum]
    exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
    have hf : TopDegLE m (-n) f := (topDegLE_iff_le_topOrd m (-n) f).mpr (by
      rw [neg_neg, hn]
      exact min_le_left _ _)
    have hg : TopDegLE m (-n) g := (topDegLE_iff_le_topOrd m (-n) g).mpr (by
      rw [neg_neg, hn]
      exact min_le_right _ _)
    have hsum := (topDegLE_iff_le_topOrd m (-n) (f + g)).mp (hf.add hg)
    rw [neg_neg] at hsum
    rw [← hn]
    exact hsum

/-- **The order at infinity in one coordinate, as an additive valuation.** -/
noncomputable def topOrdValuation (m : ℕ) : AddValuation CascadeField (WithTop ℤ) :=
  AddValuation.of (topOrd m) (topOrd_zero m) (topOrd_one m) (topOrd_add m) (topOrd_mul m)

@[simp]
theorem topOrdValuation_apply (m : ℕ) (f : CascadeField) : topOrdValuation m f = topOrd m f := rfl

/-! ## Values on the generators -/

theorem topOrd_algebraMap (m : ℕ) {N : MvPolynomial ℕ ℂ} (hN : N ≠ 0) :
    topOrd m (algebraMap (MvPolynomial ℕ ℂ) CascadeField N) = (-(N.degreeOf m : ℤ) : ℤ) := by
  have h1 : algebraMap (MvPolynomial ℕ ℂ) CascadeField 1
      * algebraMap (MvPolynomial ℕ ℂ) CascadeField N
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField N := by
    rw [map_one, one_mul]
  have hone : (1 : MvPolynomial ℕ ℂ).degreeOf m = 0 := by
    rw [show (1 : MvPolynomial ℕ ℂ) = MvPolynomial.C 1 from MvPolynomial.C_1.symm,
      MvPolynomial.degreeOf_C]
  rw [topOrd_of_ne_zero (topDegreeAlgebraMap_ne_zero_of_ne_zero hN),
    topOrdRep_eq (topDegreeAlgebraMap_ne_zero_of_ne_zero hN) (one_ne_zero (α := MvPolynomial ℕ ℂ)) h1,
    hone]
  norm_num

@[simp]
theorem topOrd_fx (m : ℕ) : topOrd m (fx m) = (-1 : ℤ) := by
  rw [fx, topOrd_algebraMap m (MvPolynomial.X_ne_zero m), MvPolynomial.degreeOf_X]
  norm_num

/-! ## How the coordinate derivations move the valuation -/

/-- **Differentiating at the coordinate itself raises the order by one.** -/
theorem topOrd_fpderiv_top (m : ℕ) (f : CascadeField) :
    topOrd m f + 1 ≤ topOrd m (fpderiv m f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, topOrd_zero, top_add]
  have hf' : TopDegLE m (-(topOrdRep m f)) f := (topDegLE_iff_le_topOrd m _ f).mpr (by
    rw [neg_neg, topOrd_of_ne_zero hf])
  have hd := (topDegLE_iff_le_topOrd m (-(topOrdRep m f) - 1) (fpderiv m f)).mp hf'.fpderiv_top
  rw [show -(-(topOrdRep m f) - 1) = topOrdRep m f + 1 by ring] at hd
  rw [topOrd_of_ne_zero hf, ← WithTop.coe_one, ← WithTop.coe_add]
  exact hd

/-- **Differentiating at another coordinate does not lower the order.** -/
theorem topOrd_fpderiv_of_ne {m l : ℕ} (h : l ≠ m) (f : CascadeField) :
    topOrd m f ≤ topOrd m (fpderiv l f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, topOrd_zero]
  have hf' : TopDegLE m (-(topOrdRep m f)) f := (topDegLE_iff_le_topOrd m _ f).mpr (by
    rw [neg_neg, topOrd_of_ne_zero hf])
  have hd := (topDegLE_iff_le_topOrd m (-(topOrdRep m f)) (fpderiv l f)).mp
    (TopDegLE.fpderiv_of_ne h hf')
  rw [neg_neg] at hd
  rw [topOrd_of_ne_zero hf]
  exact hd

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

theorem topOrd_neg_one (m : ℕ) : topOrd m (-1 : CascadeField) = ((0 : ℤ) : WithTop ℤ) := by
  have hne : (-1 : MvPolynomial ℕ ℂ) ≠ 0 := by
    simp
  have hmap : (-1 : CascadeField) = algebraMap (MvPolynomial ℕ ℂ) CascadeField (-1) := by
    rw [map_neg, map_one]
  have hone : (1 : MvPolynomial ℕ ℂ).degreeOf m = 0 := by
    rw [show (1 : MvPolynomial ℕ ℂ) = MvPolynomial.C 1 from MvPolynomial.C_1.symm,
      MvPolynomial.degreeOf_C]
  rw [hmap, topOrd_algebraMap m hne, MvPolynomial.degreeOf_neg, hone]
  norm_num

@[simp]
theorem topOrd_neg (m : ℕ) (f : CascadeField) : topOrd m (-f) = topOrd m f := by
  rw [show -f = (-1 : CascadeField) * f by ring, topOrd_mul, topOrd_neg_one]
  norm_num

theorem topOrd_inv (m : ℕ) {f : CascadeField} (hf : f ≠ 0) :
    topOrd m f + topOrd m f⁻¹ = ((0 : ℤ) : WithTop ℤ) := by
  rw [← topOrd_mul, mul_inv_cancel₀ hf, topOrd_one]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

theorem fx_ne_zero (m : ℕ) : fx m ≠ 0 :=
  topDegreeAlgebraMap_ne_zero_of_ne_zero (MvPolynomial.X_ne_zero m)

end GaloisForLFunctions.HTGeometry
