import GaloisForLFunctions.SignedArithmeticCorrespondences.GluingIntegerGraphsAtTheirQuotientEndpoints
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

/-!
# The projection formula for a dilated graph and a contracted endpoint

Multiplying a lower conductor by d is adjoint to moving each upper endpoint
to its integer quotient by d. The raw height and the boundary-corrected finite
part both obey exact projection. The discarded residue is an explicit product
of a lower degree with an upper boundary moment.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset ArithmeticCastelnuovoSeveri _root_.RHTower

/-- Place the lower multiplicity at i on the graph of conductor di. -/
def dilateLower (d : ℕ+) (u : ℕ → ℤ) (i : ℕ) : ℤ :=
  if (d:ℕ) ∣ i then u (i/d) else 0

/-- Move each upper jump to its Euclidean quotient and glue the multiplicities there. -/
def contractEndpoints (d : ℕ+) (N : ℕ) (b : ℕ → ℤ) (q : ℕ) : ℤ :=
  ∑ j ∈ Icc 1 N, if j/d=q then b j else 0

private theorem dilation_sum (d : ℕ+) (X : ℕ) (u : ℕ → ℤ) (F : ℕ → ℝ) :
    ∑ i ∈ Icc 1 ((d:ℕ)*X), (dilateLower d u i:ℝ)*F i =
      ∑ i ∈ Icc 1 X, (u i:ℝ)*F ((d:ℕ)*i) := by
  have he (i : ℕ) : (dilateLower d u i:ℝ)*F i =
      if (d:ℕ) ∣ i then (u (i/d):ℝ)*F i else 0 := by
    by_cases h : (d:ℕ) ∣ i <;> simp [dilateLower,h]
  simp only [he,← sum_filter,Sieve.sum_filter_dvd_eq_sum_scaled d.pos,Nat.mul_div_cancel_left _ d.pos]

private theorem contraction_sum (d : ℕ+) (N : ℕ) (b : ℕ → ℤ) (F : ℕ → ℝ) (h0 : F 0=0) :
    ∑ q ∈ Icc 1 N, (contractEndpoints d N b q:ℝ)*F q =
      ∑ j ∈ Icc 1 N, (b j:ℝ)*F (j/d) := by
  simp only [contractEndpoints,Int.cast_sum,sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have he (q : ℕ) :
      (((if j/d=q then b j else 0 : ℤ):ℝ) * F q) =
        if j/d=q then (b j:ℝ)*F (j/d) else 0 := by
    by_cases h : j/d=q
    · subst q; simp
    · simp [h]
  simp only [he]
  rcases Nat.eq_zero_or_pos (j/d) with h | h
  · simp [h,h0]
  · have hm := mem_Icc.mpr ⟨h,(Nat.div_le_self j d).trans (mem_Icc.mp hj).2⟩
    simp [hm]

private theorem project_quotient_test (d : ℕ+) (X N : ℕ) (u b : ℕ → ℤ) (F : ℕ → ℝ)
    (hF : F 0=0) :
    ∑ i ∈ Icc 1 ((d:ℕ)*X), ∑ j ∈ Icc 1 N, (dilateLower d u i:ℝ)*b j*F (j/i) =
      ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i:ℝ)*contractEndpoints d N b j*F (j/i) := by
  simp only [mul_assoc,← mul_sum]
  rw [dilation_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [contraction_sum d N b (fun q => F (q/i)) (by simpa using hF)]
  simp only [Nat.div_div_eq_div_mul]

/-- Exact adjunction for the actual signed orders of the integral graphs. -/
theorem project_graph_height (d : ℕ+) (X N : ℕ) (u b : ℕ → ℤ) :
    signedDivisorHeight 1 ((d:ℕ)*X) N (dilateLower d u) (upperDivisor N b) =
      signedDivisorHeight 1 X N u (upperDivisor N (contractEndpoints d N b)) := by
  rw [height_eq_quotient,height_eq_quotient]
  exact project_quotient_test d X N u b chebyshevPsi (by simp [chebyshevPsi])

/-- Every positive quotient retains its full signed coefficient under projection. -/
theorem project_quotient_coefficient (d : ℕ+) (X N : ℕ) (u b : ℕ → ℤ) {k : ℕ} (hk : 0<k) :
    quotientCoefficient ((d:ℕ)*X) N (dilateLower d u) b k =
      quotientCoefficient X N u (contractEndpoints d N b) k := by
  have h := project_quotient_test d X N u b (fun q => if q=k then 1 else 0) (by simp [hk.ne'])
  simpa only [quotientCoefficient,mul_ite,mul_one,mul_zero] using h

/-- Projection preserves the finite part, including integer cuts below d. -/
theorem project_finite_part (d : ℕ+) (X N : ℕ) (u b : ℕ → ℤ) :
    signedDivisorHeight 1 ((d:ℕ)*X) N (dilateLower d u) (upperDivisor N b) -
      poleProduct ((d:ℕ)*X) N (dilateLower d u) b + fractionalBoundary ((d:ℕ)*X) N (dilateLower d u) b =
    signedDivisorHeight 1 X N u (upperDivisor N (contractEndpoints d N b)) -
      poleProduct X N u (contractEndpoints d N b) + fractionalBoundary X N u (contractEndpoints d N b) := by
  simp only [mixed_height_finite_part]
  refine sum_congr rfl fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [psiRemainder,chebyshevPsi]
  · rw [project_quotient_coefficient d X N u b hk]

/-- The separate pole terms differ by the exact first moment of the discarded residues. -/
theorem project_opposite_degrees (d : ℕ+) (X N : ℕ) (u b : ℕ → ℤ) :
    poleProduct ((d:ℕ)*X) N (dilateLower d u) b - poleProduct X N u (contractEndpoints d N b) =
      (∑ i ∈ Icc 1 X, (u i:ℝ)/i) *
        ∑ j ∈ Icc 1 N, (b j:ℝ)*((j:ℝ)/(d:ℕ)-(j/d:ℕ)) := by
  have hl : (∑ i ∈ Icc 1 ((d:ℕ)*X), (dilateLower d u i:ℝ)/i) =
      (∑ i ∈ Icc 1 X, (u i:ℝ)/i) / (d:ℕ) := by
    simp only [div_eq_mul_inv]
    rw [dilation_sum,sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.cast_mul,mul_inv_rev]
    ring
  rw [poleProduct,poleProduct,hl,contraction_sum d N b (fun j => (j:ℝ)) (by simp)]
  rw [div_mul_eq_mul_div, mul_div_assoc, ← mul_sub, Finset.sum_div, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun j _ => by ring

#print axioms project_graph_height
#print axioms project_finite_part
#print axioms project_opposite_degrees

end GaloisForLFunctions.SignedArithmeticCorrespondences
