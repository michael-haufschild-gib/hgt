import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCoprimeRowSum
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinLineInvariance
import GaloisForLFunctions.RHTower.EisensteinHoroballBound
import GaloisForLFunctions.RHTower.EisensteinMaassSelbergAlgebra

/-!
# The truncated Eisenstein line model as a truncated coprime-row sum

For `Re u > 1/2` the completed Eisenstein line model is the coprime-row (Poincaré) sum
`E_u(z) = A(u) · ½ Σ_{v} Im(γ_v z)^{½+u}` over `v ∈ gammaSet 1 1 0`, `γ_v = gammaSetMatrix v`.
On the fundamental domain `𝒟` and for `Y ≥ 1`, the horoball bound shows that only the two rows
`±(0, 1)` can move a point above height `Y`; hence the truncation `Λ^Y E_u = E_u − 1_{y>Y} c_u(y)`
is

`Λ^Y E_u(z) = A(u) · ½ Σ_v [Im(γ_v z) ≤ Y] Im(γ_v z)^{½+u} − B(u) · [y > Y] y^{½−u}`,

the identity that the unfolding step of the Maass–Selberg relation needs.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower RHTower.D4BMJointSource
open scoped MatrixGroups

namespace RHTower

noncomputable section

/-- The height of the image `γ_v z`. -/
def rowHeight (v : gammaSet 1 1 0) (z : ℍ) : ℝ := (gammaSetMatrix v • z).im

theorem rowHeight_pos (v : gammaSet 1 1 0) (z : ℍ) : 0 < rowHeight v z :=
  (gammaSetMatrix v • z).im_pos

theorem rowHeight_eq_div (v : gammaSet 1 1 0) (z : ℍ) :
    rowHeight v z = z.im / Complex.normSq (((v.1 0 : ℤ) : ℂ) * (z : ℂ) + ((v.1 1 : ℤ) : ℂ)) := by
  unfold rowHeight
  rw [ModularGroup.im_smul_eq_div_normSq, denom_SL2Z, gammaSetMatrix_apply_one_zero,
    gammaSetMatrix_apply_one_one]

/-- The horoball bound in row language. -/
theorem rowHeight_le_one_of_mem_fd {z : ℍ} (hz : z ∈ fd) {v : gammaSet 1 1 0} (hv : v.1 0 ≠ 0) :
    rowHeight v z ≤ 1 := by
  unfold rowHeight
  apply im_smul_le_one_of_mem_fd hz
  rw [gammaSetMatrix_apply_one_zero]
  exact hv

/-- The two rows `(0, 1)` and `(0, −1)`. -/
def rowPlus : gammaSet 1 1 0 :=
  ⟨![0, 1], (gammaSet_one_mem_iff 1 _).mpr (by simp)⟩

def rowMinus : gammaSet 1 1 0 :=
  ⟨![0, -1], (gammaSet_one_mem_iff 1 _).mpr (by simp)⟩

theorem rowPlus_ne_rowMinus : rowPlus ≠ rowMinus := by
  intro h
  have := congrArg (fun v : gammaSet 1 1 0 => v.1 1) h
  simp [rowPlus, rowMinus] at this

theorem first_zero_iff (v : gammaSet 1 1 0) : v.1 0 = 0 ↔ v = rowPlus ∨ v = rowMinus := by
  constructor
  · intro hv
    have hg : (v.1 0).gcd (v.1 1) = 1 := (gammaSet_one_mem_iff 1 v.1).mp v.2
    rw [hv, Int.gcd_zero_left] at hg
    rcases Int.natAbs_eq_iff.mp hg with h1 | h1
    · left
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [rowPlus] using hv
      · simpa [rowPlus] using h1
    · right
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [rowMinus] using hv
      · simpa [rowMinus] using h1
  · rintro (rfl | rfl) <;> rfl

theorem rowHeight_rowPlus (z : ℍ) : rowHeight rowPlus z = z.im := by
  rw [rowHeight_eq_div]
  simp [rowPlus]

theorem rowHeight_rowMinus (z : ℍ) : rowHeight rowMinus z = z.im := by
  rw [rowHeight_eq_div]
  simp [rowMinus]

/-! ## The row sum and the line model -/

/-- The row sum `Σ_v Im(γ_v z)^s`. -/
def rowSum (s : ℂ) (z : ℍ) : ℂ := ∑' v : gammaSet 1 1 0, (rowHeight v z : ℂ) ^ s

theorem summable_rowHeight_cpow {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    Summable (fun v : gammaSet 1 1 0 => (rowHeight v z : ℂ) ^ s) := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨s, hs⟩
  have h := summable_d4BMPoincareSeed ⟨z.re, z.im, z.im_pos⟩ P
  rw [← primitiveRowEquiv.summable_iff]
  refine h.congr fun p => ?_
  exact poincareSeed_eq_row_height z s p

/-- **The line model as the coprime-row sum** for `Re u > 1/2`. -/
theorem eisensteinLineModel_eq_rowSum {u : ℂ} (hu : 1 / 2 < u.re) (z : ℍ) :
    eisensteinLineModel u z = msA u * ((1 / 2 : ℂ) * rowSum (1 / 2 + u) z) := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨u + 1 / 2, by simp; linarith⟩
  have hP : P.s - 1 / 2 = u := by simp [P]
  let w : D4BMUpperHalfPlaneCoordinate := ⟨z.re, z.im, z.im_pos⟩
  have h1 := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg w P w.x
  unfold d4BMCompletedEisensteinHorizontalFunction at h1
  rw [horizontalCoordinate_self, hP] at h1
  unfold eisensteinLineModel
  change d4BMCompletedEisensteinCuspLeg .scalar u w.x w.y = _
  rw [← h1, d4BMCompletedEisensteinPoincareSeries, d4BMRawEisensteinPoincareSeries]
  unfold rowSum rowHeight
  rw [← primitiveRowEquiv.tsum_eq (fun v => ((gammaSetMatrix v • z).im : ℂ) ^ (1 / 2 + u))]
  have hs : (1 / 2 : ℂ) + u = P.s := by simp [P]; ring
  simp_rw [hs]
  simp_rw [← poincareSeed_eq_row_height]
  have hA : msA u = reflectedCompletedLambda (2 * P.s) := by
    unfold msA; congr 1; simp [P]; ring
  rw [hA]

/-! ## Truncation -/

/-- The truncated row sum `Σ_v [Im(γ_v z) ≤ Y] Im(γ_v z)^s`. -/
def truncatedRowSum (s : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  ∑' v : gammaSet 1 1 0, (if rowHeight v z ≤ Y then (rowHeight v z : ℂ) ^ s else 0)

/-- The truncated line model `Λ^Y E_u = E_u − 1_{y > Y} c_u(y)`. -/
def truncatedLineModel (u : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  eisensteinLineModel u z -
    (if Y < z.im then d4BMCompletedEisensteinCuspConstantPart .scalar u z.im else 0)

theorem summable_truncated_term {s : ℂ} (hs : 1 < s.re) (Y : ℝ) (z : ℍ) :
    Summable (fun v : gammaSet 1 1 0 =>
      if rowHeight v z ≤ Y then (rowHeight v z : ℂ) ^ s else 0) := by
  refine Summable.of_norm_bounded (summable_rowHeight_cpow hs z).norm fun v => ?_
  split_ifs <;> simp

theorem summable_above_term {s : ℂ} (hs : 1 < s.re) (Y : ℝ) (z : ℍ) :
    Summable (fun v : gammaSet 1 1 0 =>
      if Y < rowHeight v z then (rowHeight v z : ℂ) ^ s else 0) := by
  refine Summable.of_norm_bounded (summable_rowHeight_cpow hs z).norm fun v => ?_
  split_ifs <;> simp

/-- Only the two rows `±(0, 1)` move a point of `𝒟` above height `Y ≥ 1`. -/
theorem tsum_above_eq {z : ℍ} (hz : z ∈ fd) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ) :
    (∑' v : gammaSet 1 1 0, (if Y < rowHeight v z then (rowHeight v z : ℂ) ^ s else 0)) =
      2 * (if Y < z.im then (z.im : ℂ) ^ s else 0) := by
  classical
  rw [tsum_eq_sum (s := {rowPlus, rowMinus})]
  · rw [Finset.sum_pair rowPlus_ne_rowMinus, rowHeight_rowPlus, rowHeight_rowMinus]
    ring
  · intro v hv
    have hv0 : v.1 0 ≠ 0 := by
      intro h0
      rcases (first_zero_iff v).mp h0 with rfl | rfl
      · exact hv (Finset.mem_insert_self _ _)
      · exact hv (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have := rowHeight_le_one_of_mem_fd hz hv0
    rw [if_neg (by linarith)]

/-- **The truncated line model is the truncated row sum** on `𝒟`, for `Re u > 1/2`, `Y ≥ 1`. -/
theorem truncatedLineModel_eq_truncatedRowSum {u : ℂ} (hu : 1 / 2 < u.re) {z : ℍ} (hz : z ∈ fd)
    {Y : ℝ} (hY : 1 ≤ Y) :
    truncatedLineModel u Y z =
      msA u * ((1 / 2 : ℂ) * truncatedRowSum (1 / 2 + u) Y z) -
        msB u * (if Y < z.im then (z.im : ℂ) ^ (1 / 2 - u) else 0) := by
  have hs : 1 < (1 / 2 + u).re := by simp; linarith
  unfold truncatedLineModel
  rw [eisensteinLineModel_eq_rowSum hu, cuspConstantPart_eq_msAB]
  have hsplit : rowSum (1 / 2 + u) z =
      truncatedRowSum (1 / 2 + u) Y z +
        ∑' v : gammaSet 1 1 0,
          (if Y < rowHeight v z then (rowHeight v z : ℂ) ^ (1 / 2 + u) else 0) := by
    unfold rowSum truncatedRowSum
    rw [← (summable_truncated_term hs Y z).tsum_add (summable_above_term hs Y z)]
    refine tsum_congr fun v => ?_
    split_ifs with h1 h2 h2
    · exact absurd h2 (not_lt.mpr h1)
    · ring
    · ring
    · exact absurd (lt_of_not_ge h1) h2
  rw [hsplit, tsum_above_eq hz hY]
  split_ifs <;> ring

end

end RHTower
