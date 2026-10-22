import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleGapShape

/-!
# Exact first jets of the prime–Gamma pole matrix

The diagonal jet cancels its leading radius term against reciprocal Mangoldt
mass. The cross jet reads the pointwise Chebyshev deficit. Their sum gives
the exact arithmetic equation at every stationary even pole. No energy sign
is assumed or produced by these identities.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace RHTower

/-- Explicit first jet of the diagonal, retaining both arithmetic cumulatives and the boundary slope. -/
def ccmWeilPoleDiagonalSlope (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*Real.cosh s+
    (-1-2*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)))*Real.exp s+
    (1-2*s-2*Chebyshev.psi (Real.exp (2*a.1)))*Real.exp (-s)+
    8*Real.sinh s+8*s*Real.cosh s+ccmGammaPoleSelfBoundarySlope s

/-- Explicit first jet of the cross entry, with the complete finite arithmetic weight. -/
def ccmWeilPoleCrossSlope (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))+4*s+
    8*Real.sinh s*Real.cosh s-2*ccmWeilPrimeChamberWeight a+2*ccmGammaPoleBoundaryLog (2*s)

/-- The displayed diagonal jet is the derivative of the exact frozen source. -/
theorem hasDerivAt_ccmWeilPoleChamberDiagonal (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (ccmWeilPoleChamberDiagonal a) (ccmWeilPoleDiagonalSlope a s) s := by
  have hf := funext (ccmWeilPoleChamberDiagonal_eq_explicit a)
  rw [hf]
  have hm : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s := by
    simpa only [Pi.neg_apply,id_eq,mul_neg_one] using! (hasDerivAt_id s).neg.exp
  convert! (((((Real.hasDerivAt_sinh s).const_mul
    (2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi)))).add
    ((Real.hasDerivAt_exp s).const_mul (-1-2*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1))))).add
    (((((hasDerivAt_id s).const_mul 2).add_const 1).add_const
      (2*Chebyshev.psi (Real.exp (2*a.1)))).mul hm)).add
    (((hasDerivAt_id s).const_mul 8).mul (Real.hasDerivAt_sinh s))).add
    (hasDerivAt_ccmGammaPoleSelfBoundaryPrimitive hs) using 1
  unfold ccmWeilPoleDiagonalSlope
  simp only [id_eq]
  ring

/-- The displayed cross jet is the derivative of the exact frozen source. -/
theorem hasDerivAt_ccmWeilPoleChamberCross (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (ccmWeilPoleChamberCross a) (ccmWeilPoleCrossSlope a s) s := by
  have hf := funext (ccmWeilPoleChamberCross_eq_explicit a)
  rw [hf]
  convert! ((((((hasDerivAt_id s).const_mul 2).const_mul
    (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))).add
    (((hasDerivAt_id s).pow 2).const_mul 2)).add
    (((Real.hasDerivAt_sinh s).const_mul 2).pow 2)).add
    (hasDerivAt_ccmGammaPoleCrossBoundaryPrimitive hs)).sub
    ((hasDerivAt_const s (ccmPolarPrimeTent a)).add
      ((((hasDerivAt_id s).sub_const a.1).const_mul 2).mul_const (ccmWeilPrimeChamberWeight a))) using 1
  unfold ccmWeilPoleCrossSlope
  simp only [id_eq]
  ring

private theorem psi_sum (X : ℝ) :
    Chebyshev.psi X = ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hn).2⟩
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hsmall : n=0 ∨ n=1 := by omega
    rcases hsmall with rfl | rfl <;> simp

/-- The full cross-slope weight is exactly ordinary plus reciprocal Mangoldt mass. -/
theorem ccmWeilPrimeChamberWeight_eq_cumulatives (a : SuzukiPositiveAperture) :
    ccmWeilPrimeChamberWeight a = Chebyshev.psi (Real.exp (2*a.1))+
      ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)) := by
  rw [ccmWeilPrimeChamberWeight,ccmReciprocalMangoldtCumulative,psi_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The leading linear radius term cancels from the actual diagonal first jet. -/
theorem ccmWeilPoleDiagonalSlope_self_eq_error (a : SuzukiPositiveAperture) :
    ccmWeilPoleDiagonalSlope a a.1 =
      2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*Real.cosh a.1+
      (3-2*ccmReciprocalMangoldtError (2*a.1))*Real.exp a.1+
      (2*a.1-3-2*Chebyshev.psi (Real.exp (2*a.1)))*Real.exp (-a.1)+
      ccmGammaPoleSelfBoundarySlope a.1 := by
  unfold ccmWeilPoleDiagonalSlope ccmReciprocalMangoldtError
  rw [Real.sinh_eq,Real.cosh_eq]
  ring

/-- The actual cross slope is the pointwise Chebyshev deficit plus bounded arithmetic and Gamma terms. -/
theorem ccmWeilPoleCrossSlope_self_eq_error (a : SuzukiPositiveAperture) :
    ccmWeilPoleCrossSlope a a.1 = 2*((-Real.eulerMascheroniConstant-Real.log (2*Real.pi))+
      Real.exp (2*a.1)-Chebyshev.psi (Real.exp (2*a.1))-Real.exp (-(2*a.1))+
      ccmGammaPoleBoundaryLog (2*a.1)-ccmReciprocalMangoldtError (2*a.1)) := by
  unfold ccmWeilPoleCrossSlope
  rw [ccmWeilPrimeChamberWeight_eq_cumulatives]
  unfold ccmReciprocalMangoldtError
  rw [Real.sinh_eq,Real.cosh_eq]
  have he : Real.exp (2*a.1)=Real.exp a.1^(2 : ℕ) := by simpa using Real.exp_nat_mul a.1 2
  have hm : Real.exp (-(2*a.1))=Real.exp (-a.1)^(2 : ℕ) := by
    rw [show -(2*a.1)=2*(-a.1) by ring]
    simpa using Real.exp_nat_mul (-a.1) 2
  rw [he,hm]
  ring

/-- The complete even first jet is the sum of the two exact entry jets. -/
theorem hasDerivAt_ccmWeilEvenPoleChamber (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (ccmWeilEvenPoleChamber a)
      (2*(ccmWeilPoleDiagonalSlope a s+ccmWeilPoleCrossSlope a s)) s := by
  exact ((hasDerivAt_ccmWeilPoleChamberDiagonal a hs).add
    (hasDerivAt_ccmWeilPoleChamberCross a hs)).const_mul 2

/-- Exact pointwise prime-error equation at every stationary actual even pole. -/
theorem ccmWeilEvenPole_stationary_prime_error (a : SuzukiPositiveAperture)
    (hstat : deriv (ccmWeilEvenPoleChamber a) a.1 = 0) :
    Real.exp (2*a.1)-Chebyshev.psi (Real.exp (2*a.1)) =
      -ccmWeilPoleDiagonalSlope a a.1/2-
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))+Real.exp (-(2*a.1))-
      ccmGammaPoleBoundaryLog (2*a.1)+ccmReciprocalMangoldtError (2*a.1) := by
  rw [(hasDerivAt_ccmWeilEvenPoleChamber a a.2).deriv,
    ccmWeilPoleCrossSlope_self_eq_error] at hstat
  linarith

end RHTower
