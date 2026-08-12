import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierConstruction

/-!
# The denominator row of the constructed carrier family

Three properties of the row `[c, d] = [B, −D]` of the classical analytic Nevanlinna carrier family
follow directly from the determinant identity and the leaf at infinity.

* the two entries have no common zero, since a common zero would make `A D − B C` vanish;
* `B` has a real zero, because the leaf at infinity is a probability measure carried by the zero
  set of `B`, and an empty carrier would give it total mass zero;
* `B` has a regular point, because it cannot vanish off the real axis.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The denominator row has no common zero.**  A common zero of `B` and `D` would force
`A D − B C = 0`, contradicting the determinant identity. -/
theorem nevInf_no_common_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (z : ℂ) :
    ¬ (nevBinf s z = 0 ∧ nevDinf s z = 0) := by
  rintro ⟨hB, hD⟩
  have hdet := (nevanlinna_entire_unimodular h h0b).2.2.2.2 z
  rw [hB, hD] at hdet
  have : (0 : ℂ) = 1 := by linear_combination hdet
  exact one_ne_zero this.symm

/-- **The zero set of `B` is nonempty.**  The leaf at infinity is a probability measure whose
complement of the zero set of `B` is null, so that zero set carries mass one. -/
theorem exists_nevBrealInf_eq_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) : ∃ x : ℝ, nevBrealInf s x = 0 := by
  by_contra hno
  have hcar := nevLeaf_infinity_carried h h0b h0
  have hset : (nevMatrixDataInf h h0b).infinityDenominatorFiber = (∅ : Set ℝ) := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    exact hno ⟨x, hx⟩
  rw [hset, Set.compl_empty] at hcar
  have huniv : (nevLeaf h h0b h0 ∞ : Measure ℝ) Set.univ = 1 :=
    (nevLeaf h h0b h0 ∞).2.measure_univ
  rw [hcar] at huniv
  exact zero_ne_one huniv

/-- **`B` has a zero.** -/
theorem exists_nevBinf_eq_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) : ∃ z : ℂ, nevBinf s z = 0 := by
  obtain ⟨x, hx⟩ := exists_nevBrealInf_eq_zero h h0b h0
  exact ⟨(x : ℂ), by rw [nevBinf_ofReal, hx]; simp⟩

/-- **`B` has a regular point**, namely `i`. -/
theorem nevBinf_I_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    nevBinf s Complex.I ≠ 0 :=
  nevBinf_ne_zero h h0b h0 (by simp)

/-! ## The same three facts in the carrier convention -/

/-- The denominator row of the constructed carrier family has no common zero. -/
theorem analyticNevCarrierFamily_noCommonZero (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (z : ℂ) :
    ¬ ((analyticNevCarrierFamily h h0b h0).c z = 0 ∧
        (analyticNevCarrierFamily h h0b h0).d z = 0) := by
  rintro ⟨hc, hd⟩
  refine nevInf_no_common_zero h h0b z ⟨hc, ?_⟩
  have : -nevDinf s z = 0 := hd
  linear_combination -this

/-- The `c` entry of the constructed carrier family has a zero. -/
theorem analyticNevCarrierFamily_exists_zero (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    ∃ z : ℂ, (analyticNevCarrierFamily h h0b h0).c z = 0 :=
  exists_nevBinf_eq_zero h h0b h0

/-- The `c` entry of the constructed carrier family has a regular point. -/
theorem analyticNevCarrierFamily_regular (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (analyticNevCarrierFamily h h0b h0).c Complex.I ≠ 0 :=
  nevBinf_I_ne_zero h h0b h0

/-- The projective parameter of the constructed carrier family is `D/B`. -/
theorem analyticNevCarrierFamily_quotient (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (z : ℂ) :
    (analyticNevCarrierFamily h h0b h0).quotient z = nevDinf s z / nevBinf s z := by
  show -(-nevDinf s z) / nevBinf s z = _
  rw [neg_neg]

end HTGeometry
