import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactScalarExpansion

/-!
# Fixed positive compact reserve for the corrected odd determinant

An exact decomposition into the checked cubic minorant and nonnegative
remainder proves the complete normalized compact-box inequality.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-- Exact decomposition on the normalized unit cube. -/
theorem oddCompactScalarDet_lower_decomposition {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactScalarDet u (17+3*t) w +
      1000000000*oddCompactScalarHead u (17+3*t) w*oddCompactLowerSource u (17+3*t) w =
      oddCompactCubicMinorant u t w + oddCompactRemainder u t w := by
  unfold oddCompactScalarDet oddCompactScalarHead oddCompactLowerSource
    oddCompactSourceZero oddCompactCubicMinorant oddCompactRemainder
    oddCompactScalarDetPart0 oddCompactScalarDetPart1 oddCompactScalarDetPart2 oddCompactScalarDetPart3 oddCompactScalarDetPart4 oddCompactScalarDetPart5 oddCompactScalarDetPart6 oddCompactScalarDetPart7 oddCompactScalarDetPart8 oddCompactScalarDetPart9 oddCompactScalarDetPart10 oddCompactScalarDetPart11 oddCompactScalarDetPart12 oddCompactScalarDetPart13 oddCompactScalarDetPart14 oddCompactScalarDetPart15 oddCompactScalarDetPart16 oddCompactScalarDetPart17 oddCompactScalarDetPart18 oddCompactScalarDetPart19 oddCompactScalarDetPart20 oddCompactScalarDetPart21 oddCompactScalarDetPart22 oddCompactScalarDetPart23 oddCompactScalarDetPart24 oddCompactScalarDetPart25 oddCompactScalarDetPart26 oddCompactScalarDetPart27 oddCompactScalarDetPart28 oddCompactScalarDetPart29 oddCompactScalarDetPart30 oddCompactScalarDetPart31 oddCompactScalarDetPart32 oddCompactScalarDetPart33
    oddCompactScalarHeadPart0 oddCompactScalarHeadPart1 oddCompactScalarHeadPart2 oddCompactScalarHeadPart3 oddCompactScalarHeadPart4 oddCompactScalarHeadPart5
    oddCompactRemainderPart0 oddCompactRemainderPart1 oddCompactRemainderPart2 oddCompactRemainderPart3 oddCompactRemainderPart4 oddCompactRemainderPart5 oddCompactRemainderPart6 oddCompactRemainderPart7 oddCompactRemainderPart8 oddCompactRemainderPart9 oddCompactRemainderPart10 oddCompactRemainderPart11 oddCompactRemainderPart12 oddCompactRemainderPart13 oddCompactRemainderPart14 oddCompactRemainderPart15 oddCompactRemainderPart16 oddCompactRemainderPart17 oddCompactRemainderPart18 oddCompactRemainderPart19 oddCompactRemainderPart20 oddCompactRemainderPart21 oddCompactRemainderPart22 oddCompactRemainderPart23 oddCompactRemainderPart24 oddCompactRemainderPart25 oddCompactRemainderPart26 oddCompactRemainderPart27 oddCompactRemainderPart28 oddCompactRemainderPart29 oddCompactRemainderPart30 oddCompactRemainderPart31 oddCompactRemainderPart32 oddCompactRemainderPart33 oddCompactRemainderPart34 oddCompactRemainderPart35 oddCompactRemainderPart36 oddCompactRemainderPart37 oddCompactRemainderPart38 oddCompactRemainderPart39 oddCompactRemainderPart40 oddCompactRemainderPart41 oddCompactRemainderPart42 oddCompactRemainderPart43 oddCompactRemainderPart44 oddCompactRemainderPart45 oddCompactRemainderPart46 oddCompactRemainderPart47 oddCompactRemainderPart48 oddCompactRemainderPart49 oddCompactRemainderPart50
  simp only [oddCompactUnitSlack_eq hu0 hu1 ht0 ht1 hw0 hw1]
  as_aux_lemma => ring

/-- Exact normalized determinant decomposition on the unit cube. -/
theorem oddCompactDet_lower_decomposition {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactDet u (17+3*t) w +
      1000000000*oddCompactHead u (17+3*t) w*oddCompactLowerSource u (17+3*t) w =
      oddCompactCubicMinorant u t w + oddCompactRemainder u t w := by
  rw [oddCompactDet_eq_scalarPolynomial, oddCompactHead_eq_scalarPolynomial]
  exact oddCompactScalarDet_lower_decomposition hu0 hu1 ht0 ht1 hw0 hw1

/-- Fixed arithmetic reserve throughout the complete compact modular box. -/
theorem oddCompactDet_corrected_lower {u a w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ha0 : 17 ≤ a) (ha1 : a ≤ 20)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    100000000000000 ≤ oddCompactDet u a w +
      1000000000*oddCompactHead u a w*oddCompactLowerSource u a w := by
  let t := (a-17)/3
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have ha : a = 17+3*t := by dsimp [t]; ring
  rw [ha, oddCompactDet_lower_decomposition hu0 hu1 ht0 ht1 hw0 hw1]
  exact (oddCompactCubicMinorant_lower hu0 hu1 ht0 ht1 hw0 hw1).trans
    (le_add_of_nonneg_right (oddCompactRemainder_nonneg hu0 ht0 hw0))

end
end HTGeometry
