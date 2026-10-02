import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthSource

/-!
# Modular center polynomial for the growth sign

Exact even mass-jet polynomials through degree ten give a positive
curvature-weighted eighth-versus-sixth source numerator throughout
X >= 191/10, beta >= 200. The literal center factor curvature exceeds
this threshold. Source-jet identification is supplied separately.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section
def centerMassJet {K : Type*} [Field K] (X : K) : ℕ → K
  | 0 => 1
  | 2 => -1/2+X/8
  | 4 => 7/4-11/8*X-X^2/64
  | 6 => -139/8+889/32*X+95/128*X^2+51/512*X^3
  | 8 => 5473/16-14677/16*X-5397/128*X^2-3213/256*X^3+849/4096*X^4
  | 10 => -357721/32+5771821/128*X+797555/256*X^2+1562589/1024*X^3-445725/8192*X^4-26199/32768*X^5
  | _ => 0
def centerRawJet {K : Type*} [Field K] (X : K) (j : ℕ) : K :=
  (centerMassJet X (j+2)-centerMassJet X j/4)/2
def centerFourthNumerator {K : Type*} [Field K] (X : K) : K :=
  3*centerRawJet X 2^2-centerRawJet X 0*centerRawJet X 4
def centerSixthNumerator {K : Type*} [Field K] (X : K) : K :=
  -centerRawJet X 0^2*centerRawJet X 6+
    15*centerRawJet X 0*centerRawJet X 2*centerRawJet X 4-30*centerRawJet X 2^3
def centerEighthNumerator {K : Type*} [Field K] (X : K) : K :=
  -centerRawJet X 0^3*centerRawJet X 8+28*centerRawJet X 0^2*centerRawJet X 2*centerRawJet X 6+
    35*centerRawJet X 0^2*centerRawJet X 4^2-420*centerRawJet X 0*centerRawJet X 2^2*centerRawJet X 4+
    630*centerRawJet X 2^4

theorem centerFourthSixth_gap_shift_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < 4*centerFourthNumerator (191/10+y)*centerRawJet (191/10+y) 0^2-
      centerSixthNumerator (191/10+y)*centerRawJet (191/10+y) 0 := by
  unfold centerFourthNumerator centerSixthNumerator centerRawJet
  simp only [centerMassJet,Nat.reduceAdd]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem centerGrowth_modular_shift_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < centerEighthNumerator (191/10+y)-4*centerSixthNumerator (191/10+y)*centerRawJet (191/10+y) 0+
      200*(4*centerFourthNumerator (191/10+y)*centerRawJet (191/10+y) 0^2-
        centerSixthNumerator (191/10+y)*centerRawJet (191/10+y) 0) := by
  unfold centerEighthNumerator centerSixthNumerator centerFourthNumerator centerRawJet
  simp only [centerMassJet,Nat.reduceAdd]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity


theorem factorCurvature_ge_twoHundred {q : ℝ} (hq : 3/2 ≤ q) (hqu : q ≤ 5/3) :
    200 ≤ factorCurvature q := by
  have hq0 : 0 < q := by linarith
  have hq3 : 0 < q+3 := by linarith
  have ha : 2*(q+3/2)/(q+3) ≤ 2 := (div_le_iff₀ hq3).mpr (by linarith)
  have hb : 19 ≤ 10*(q+3/2)/q := (le_div_iff₀ hq0).mpr (by linarith)
  have hs : factorLogSlope q ≤ -13 := by unfold factorLogSlope; linarith
  have hsq : q^2 ≤ (5/3:ℝ)^2 := by nlinarith
  have hf : (27/5:ℝ) ≤ 15/q^2 := (le_div_iff₀ (sq_pos_of_pos hq0)).mpr (by nlinarith)
  have hg : 0 ≤ 3/(q+3)^2 := by positivity
  have hm := mul_le_mul (show (6:ℝ) ≤ 2*(q+3/2) by linarith)
    (show (27/5:ℝ) ≤ 3/(q+3)^2+15/q^2 by linarith) (by norm_num) (by linarith)
  unfold factorCurvature
  nlinarith [sq_nonneg (factorLogSlope q+13)]

theorem centerGrowth_modular_pos {X β : ℝ} (hX : 191/10 ≤ X) (hβ : 200 ≤ β) :
    0 < centerEighthNumerator X-(4+β)*centerSixthNumerator X*centerRawJet X 0+
      4*β*centerFourthNumerator X*centerRawJet X 0^2 := by
  have h1 := centerFourthSixth_gap_shift_pos (X-191/10) (by linarith)
  have h2 := centerGrowth_modular_shift_pos (X-191/10) (by linarith)
  rw [show (191/10:ℝ)+(X-191/10)=X by ring] at h1 h2
  have h3 := mul_nonneg (sub_nonneg.mpr hβ) h1.le
  nlinarith only [h2,h3]

end
end RHTower.ThetaCuspDefect
