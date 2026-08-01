import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.TraceNorm

/-!
# Schatten relocation by a double commutator

If `Q` is Hilbert--Schmidt and `B` is bounded, the second commutator

`[Q,[Q,B]] = Q²B - 2QBQ + BQ²`

is Schatten-1.  When both inputs are self-adjoint it is self-adjoint.  On a marked eigenbasis of
`Q`, every matrix edge of `B` is multiplied by `(q_i-q_j)²`; consequently every nonzero triangle
holonomy survives whenever the three skeleton coordinates are distinct.

For Route K this supplies a canonical trace-ideal relocation mechanism tied to the reciprocal
Riemann--von Mangoldt skeleton, rather than an arbitrary diagonal gauge.  The theorem does not
assert that the completed physical-endpoint boundary kernel defines the required bounded `B`, nor
does it assert the centered-Xi determinant identity.
-/

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Second commutator written as a bounded operator polynomial. -/
def schattenDoubleCommutator
    (Q B : H →L[ℂ] H) : H →L[ℂ] H :=
  (Q ∘L Q) ∘L B -
    (2 : ℂ) • ((Q ∘L B) ∘L Q) +
      (B ∘L Q) ∘L Q

/-- The double commutator is itself Hilbert--Schmidt whenever the skeleton is
Hilbert--Schmidt. -/
theorem schattenDoubleCommutator_isHilbertSchmidt
    {Q B : H →L[ℂ] H} (hQ : Q.IsHilbertSchmidt) :
    (schattenDoubleCommutator Q B).IsHilbertSchmidt := by
  have hleft : ((Q ∘L Q) ∘L B).IsHilbertSchmidt :=
    (hQ.comp_left Q).comp_right B
  have hmiddle : ((Q ∘L B) ∘L Q).IsHilbertSchmidt :=
    (hQ.comp_right B).comp_right Q
  have hright : ((B ∘L Q) ∘L Q).IsHilbertSchmidt :=
    (hQ.comp_left B).comp_right Q
  rw [schattenDoubleCommutator]
  exact (hleft.sub (hmiddle.smul 2)).add hright

/-- A Hilbert--Schmidt skeleton makes the double commutator trace class against every bounded
operator. -/
theorem schattenDoubleCommutator_memSchattenClass_one
    {Q B : H →L[ℂ] H} (hQ : Q.IsHilbertSchmidt) :
    MemSchattenClass 1 (schattenDoubleCommutator Q B) := by
  have hQQ : MemSchattenClass 1 (Q ∘L Q) :=
    memSchattenClass_one_comp hQ hQ
  have hleft : MemSchattenClass 1 ((Q ∘L Q) ∘L B) :=
    memSchattenClass_one_comp_right hQQ B
  have hmiddle : MemSchattenClass 1 ((Q ∘L B) ∘L Q) :=
    memSchattenClass_one_comp (hQ.comp_right B) hQ
  have hright : MemSchattenClass 1 ((B ∘L Q) ∘L Q) :=
    memSchattenClass_one_comp (hQ.comp_left B) hQ
  have htwomiddle : MemSchattenClass 1
      ((2 : ℂ) • ((Q ∘L B) ∘L Q)) :=
    memSchattenClass_one_smul hmiddle 2
  have hnegmiddle : MemSchattenClass 1
      (-((2 : ℂ) • ((Q ∘L B) ∘L Q))) := by
    simpa only [neg_one_smul] using
      memSchattenClass_one_smul htwomiddle (-1 : ℂ)
  rw [schattenDoubleCommutator, sub_eq_add_neg]
  have hsum := memSchattenClass_one_add
    (hleft.isCompactOperator one_pos) (hnegmiddle.isCompactOperator one_pos)
    hleft hnegmiddle
  exact memSchattenClass_one_add
    (hsum.isCompactOperator one_pos)
    (hright.isCompactOperator one_pos)
    hsum hright

/-- Self-adjoint inputs produce a self-adjoint trace-ideal relocation. -/
theorem schattenDoubleCommutator_isSelfAdjoint
    {Q B : H →L[ℂ] H} (hQ : IsSelfAdjoint Q) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (schattenDoubleCommutator Q B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [schattenDoubleCommutator, map_add, map_sub,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint.map_smulₛₗ,
    hQ.adjoint_eq, hB.adjoint_eq, map_ofNat]
  simp only [← ContinuousLinearMap.comp_assoc]
  abel

/-- Exact edge incidence on any marked eigenbasis of the skeleton. -/
theorem inner_schattenDoubleCommutator_eigenvector
    {ι : Type*} {Q B : H →L[ℂ] H} (hQadj : IsSelfAdjoint Q)
    (basis : ι → H) (q : ι → ℝ)
    (hQ : ∀ i, Q (basis i) = (q i : ℂ) • basis i)
    (i j : ι) :
    inner ℂ (basis i) (schattenDoubleCommutator Q B (basis j)) =
      (((q i - q j) ^ 2 : ℝ) : ℂ) * inner ℂ (basis i) (B (basis j)) := by
  have hsym := hQadj.isSymmetric
  have hmove (x : H) :
      inner ℂ (basis i) (Q x) =
        (q i : ℂ) * inner ℂ (basis i) x := by
    calc
      inner ℂ (basis i) (Q x) = inner ℂ (Q (basis i)) x :=
        (hsym (basis i) x).symm
      _ = (q i : ℂ) * inner ℂ (basis i) x := by
        rw [hQ i, inner_smul_left]
        simp
  rw [schattenDoubleCommutator, add_apply, sub_apply, smul_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [inner_add_right, inner_sub_right, inner_smul_right]
  rw [hmove, hmove, hmove]
  simp only [hQ, map_smul, inner_smul_right]
  push_cast
  ring

/-- Every marked triangle holonomy is multiplied by the squared skeleton Vandermonde. -/
theorem schattenDoubleCommutator_triangleHolonomy
    {ι : Type*} {Q B : H →L[ℂ] H} (hQadj : IsSelfAdjoint Q)
    (basis : ι → H) (q : ι → ℝ)
    (hQ : ∀ i, Q (basis i) = (q i : ℂ) • basis i)
    (i j k : ι) :
    inner ℂ (basis i) (schattenDoubleCommutator Q B (basis j)) *
        inner ℂ (basis j) (schattenDoubleCommutator Q B (basis k)) *
          inner ℂ (basis k) (schattenDoubleCommutator Q B (basis i)) =
      (((q i - q j) ^ 2 * (q j - q k) ^ 2 * (q k - q i) ^ 2 : ℝ) : ℂ) *
        (inner ℂ (basis i) (B (basis j)) *
          inner ℂ (basis j) (B (basis k)) *
            inner ℂ (basis k) (B (basis i))) := by
  rw [inner_schattenDoubleCommutator_eigenvector hQadj basis q hQ,
    inner_schattenDoubleCommutator_eigenvector hQadj basis q hQ,
    inner_schattenDoubleCommutator_eigenvector hQadj basis q hQ]
  push_cast
  ring

/-- Distinct skeleton coordinates preserve every nonzero source triangle. -/
theorem schattenDoubleCommutator_triangleHolonomy_ne_zero
    {ι : Type*} {Q B : H →L[ℂ] H} (hQadj : IsSelfAdjoint Q)
    (basis : ι → H) (q : ι → ℝ)
    (hQ : ∀ i, Q (basis i) = (q i : ℂ) • basis i)
    {i j k : ι} (hij : q i ≠ q j) (hjk : q j ≠ q k) (hki : q k ≠ q i)
    (hijB : inner ℂ (basis i) (B (basis j)) ≠ 0)
    (hjkB : inner ℂ (basis j) (B (basis k)) ≠ 0)
    (hkiB : inner ℂ (basis k) (B (basis i)) ≠ 0) :
    inner ℂ (basis i) (schattenDoubleCommutator Q B (basis j)) *
        inner ℂ (basis j) (schattenDoubleCommutator Q B (basis k)) *
          inner ℂ (basis k) (schattenDoubleCommutator Q B (basis i)) ≠ 0 := by
  rw [schattenDoubleCommutator_triangleHolonomy hQadj basis q hQ]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hij))
        (pow_ne_zero 2 (sub_ne_zero.mpr hjk)))
        (pow_ne_zero 2 (sub_ne_zero.mpr hki)))
  · exact mul_ne_zero (mul_ne_zero hijB hjkB) hkiB

end

end RHTower
