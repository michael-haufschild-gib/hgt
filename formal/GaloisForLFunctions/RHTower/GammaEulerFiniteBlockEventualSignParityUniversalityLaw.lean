import GaloisForLFunctions.RHTower.GammaEulerTwoChannelAsymptotic

/-!
# Gamma--Euler finite-block eventual-sign parity universality

For every nonempty finite block of positive Euler scales, the far-tail sign of the iterated
Gamma--Euler difference is determined exactly by channel-count parity.  Odd blocks are eventually
positive and even blocks eventually negative; conversely, either eventual strict sign recovers
the corresponding parity.
-/

open Filter

namespace RHTower

noncomputable section

/-- Every nonempty odd block of positive Euler scales has an eventually positive Gamma tail. -/
theorem gammaEulerDifferenceList_eventually_pos
    {r : ℝ} (hr : 0 < r) {L : List ℝ}
    (hpos : ∀ h ∈ L, 0 < h) (hL : L ≠ []) (hlen : Odd L.length) :
    ∀ᶠ u in atTop,
      0 < gammaEulerDifferenceList r L
        (fun u => (Real.cosh (u / 2)) ^ (-r)) u := by
  have hPneg :
      (L.map
        (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod < 0 :=
    (gammaEulerEigenvalueList_prod_sign hr hpos).2 hlen
  have hCpos : 0 <
      -r * gammaEulerTailScale r *
        (L.map
          (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod := by
    have h1 : -r * gammaEulerTailScale r < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (gammaEulerTailScale_pos r)
    exact mul_pos_of_neg_of_neg h1 hPneg
  have hev :=
    (gammaEulerDifferenceList_asymptotic r hL).eventually
      (Ioi_mem_nhds hCpos)
  filter_upwards [hev] with u hu
  have hexp : 0 < Real.exp ((r / 2 + 1) * u) := Real.exp_pos _
  have hu' : 0 <
      Real.exp ((r / 2 + 1) * u) *
        gammaEulerDifferenceList r L
          (fun u => (Real.cosh (u / 2)) ^ (-r)) u :=
    Set.mem_Ioi.mp hu
  nlinarith

/-- **Gamma--Euler finite-block eventual-sign parity universality.**  For a nonempty positive-scale
block, eventual positivity is equivalent to odd length and eventual negativity to even length. -/
theorem gammaEulerDifferenceList_eventualSign_iff_parity
    {r : ℝ} (hr : 0 < r) {L : List ℝ}
    (hpos : ∀ h ∈ L, 0 < h) (hL : L ≠ []) :
    (Odd L.length ↔
        ∀ᶠ u in atTop,
          0 < gammaEulerDifferenceList r L
            (fun u => (Real.cosh (u / 2)) ^ (-r)) u) ∧
      (Even L.length ↔
        ∀ᶠ u in atTop,
          gammaEulerDifferenceList r L
            (fun u => (Real.cosh (u / 2)) ^ (-r)) u < 0) := by
  constructor
  · constructor
    · exact gammaEulerDifferenceList_eventually_pos hr hpos hL
    · intro hevpos
      by_contra hnotodd
      have heven : Even L.length := Nat.not_odd_iff_even.mp hnotodd
      have hevneg :=
        gammaEulerDifferenceList_eventually_neg hr hpos hL heven
      obtain ⟨u, huPos, huNeg⟩ := (hevpos.and hevneg).exists
      linarith
  · constructor
    · exact gammaEulerDifferenceList_eventually_neg hr hpos hL
    · intro hevneg
      by_contra hnoteven
      have hodd : Odd L.length := Nat.not_even_iff_odd.mp hnoteven
      have hevpos :=
        gammaEulerDifferenceList_eventually_pos hr hpos hL hodd
      obtain ⟨u, huPos, huNeg⟩ := (hevpos.and hevneg).exists
      linarith

end

end RHTower
