import GaloisForLFunctions.HTGeometry.RankThreeHankelSchurBoundary

/-! # Strict six-dimensional signed Hankel assembly by parity -/
open Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A strict leading plane and strict determinant give positivity in every nonzero direction. -/
theorem hankelThreeQuadratic_pos {a b c d e x y z : ℝ}
    (ha : 0 < a) (hhead : 0 < a*c-b^2)
    (hdet : 0 < HilbertMetric.signedEvenHankelThreeDet a b c d e)
    (hxyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < hankelThreeQuadratic a b c d e x y z := by
  by_cases hz : z = 0
  · subst z
    exact hankelThreeQuadratic_head_pos ha hhead (by simpa using hxyz)
  · exact threeByThreeQuadratic_pos_of_minors ha hhead hdet hz

/-- The six-dimensional Hankel matrix of an even sequence, in its original index order. -/
def sixPointSignedHankel (m0 m1 m2 m3 m4 m5 : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![m0, 0, m1, 0, m2, 0;
     0, m1, 0, m2, 0, m3;
     m1, 0, m2, 0, m3, 0;
     0, m2, 0, m3, 0, m4;
     m2, 0, m3, 0, m4, 0;
     0, m3, 0, m4, 0, m5]

/-- Both strict parity blocks give the full strict six-dimensional section. -/
theorem sixPointSignedHankel_posDef {m0 m1 m2 m3 m4 m5 : ℝ}
    (h0 : 0 < m0) (h1 : 0 < m1)
    (h2 : 0 < m0*m2-m1^2) (h3 : 0 < m1*m3-m2^2)
    (h4 : 0 < HilbertMetric.signedEvenHankelThreeDet m0 m1 m2 m3 m4)
    (h5 : 0 < HilbertMetric.signedEvenHankelThreeDet m1 m2 m3 m4 m5) :
    (sixPointSignedHankel m0 m1 m2 m3 m4 m5).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sixPointSignedHankel]
  · intro v hv
    let E := hankelThreeQuadratic m0 m1 m2 m3 m4 (v 0) (v 2) (v 4)
    let O := hankelThreeQuadratic m1 m2 m3 m4 m5 (v 1) (v 3) (v 5)
    have hEp : (v 0 ≠ 0 ∨ v 2 ≠ 0 ∨ v 4 ≠ 0) → 0 < E :=
      fun h => hankelThreeQuadratic_pos h0 h2 h4 h
    have hOp : (v 1 ≠ 0 ∨ v 3 ≠ 0 ∨ v 5 ≠ 0) → 0 < O :=
      fun h => hankelThreeQuadratic_pos h1 h3 h5 h
    have hEn : 0 ≤ E := by
      by_cases h : v 0 ≠ 0 ∨ v 2 ≠ 0 ∨ v 4 ≠ 0
      · exact (hEp h).le
      · push Not at h
        simp [E, hankelThreeQuadratic, h.1, h.2.1, h.2.2]
    have hOn : 0 ≤ O := by
      by_cases h : v 1 ≠ 0 ∨ v 3 ≠ 0 ∨ v 5 ≠ 0
      · exact (hOp h).le
      · push Not at h
        simp [O, hankelThreeQuadratic, h.1, h.2.1, h.2.2]
    have hpos : 0 < E+O := by
      by_cases h : v 0 ≠ 0 ∨ v 2 ≠ 0 ∨ v 4 ≠ 0
      · exact add_pos_of_pos_of_nonneg (hEp h) hOn
      · have ho : v 1 ≠ 0 ∨ v 3 ≠ 0 ∨ v 5 ≠ 0 := by
          by_contra hn
          push Not at h hn
          apply hv
          funext i
          fin_cases i <;> simp [h.1, h.2.1, h.2.2, hn.1, hn.2.1, hn.2.2]
        exact add_pos_of_nonneg_of_pos hEn (hOp ho)
    have heq : star v ⬝ᵥ (sixPointSignedHankel m0 m1 m2 m3 m4 m5).mulVec v = E+O := by
      simp [sixPointSignedHankel, dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
        E, O, hankelThreeQuadratic]
      ring
    rw [heq]
    exact hpos

end
end GaloisForLFunctions.HTGeometry
