import GaloisForLFunctions.RHTower.CCMRestrictedWeilOddIntegerEntryCriterion

/-!
# Exact arithmetic atoms of the moving Weil pole matrix

The frozen matrix is a smooth Gamma–polar term minus literal finite Mangoldt
atoms. Increasing the integer cutoff by one subtracts precisely the new atom.
Both atoms vanish at entry and vanish identically outside prime-power support.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

/-- Smooth Gamma and polar part of the moving positive-pole diagonal. -/
def ccmWeilPoleDiagonalSmooth (s : ℝ) : ℝ :=
  2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*Real.sinh s-Real.exp s+
    (2*s+1)*Real.exp (-s)+8*s*Real.sinh s+ccmGammaPoleSelfBoundaryPrimitive s

/-- Smooth Gamma and polar part of the moving opposite-pole entry. -/
def ccmWeilPoleCrossSmooth (s : ℝ) : ℝ :=
  (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*s)+2*s^(2 : ℕ)+
    (2*Real.sinh s)^(2 : ℕ)+ccmGammaPoleCrossBoundaryPrimitive s

/-- Literal Mangoldt diagonal atom before its subtraction from the Weil form. -/
def ccmWeilPolePrimeDiagonalAtom (n : ℕ) (s : ℝ) : ℝ :=
  2*ArithmeticFunction.vonMangoldt n*(Real.exp s/n-Real.exp (-s))

/-- Literal Mangoldt cross atom before its subtraction from the Weil form. -/
def ccmWeilPolePrimeCrossAtom (n : ℕ) (s : ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt n*(1+1/(n:ℝ))*(2*s-Real.log n)

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

/-- Exact frozen diagonal as its smooth source minus every visible arithmetic atom. -/
theorem ccmWeilPoleChamberDiagonal_eq_sum_atoms (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmWeilPoleChamberDiagonal a s = ccmWeilPoleDiagonalSmooth s-
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊, ccmWeilPolePrimeDiagonalAtom n s := by
  rw [ccmWeilPoleChamberDiagonal_eq_explicit]
  have hsum : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊, ccmWeilPolePrimeDiagonalAtom n s) =
      2*Real.exp s*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1))-
        2*Real.exp (-s)*Chebyshev.psi (Real.exp (2*a.1)) := by
    rw [ccmReciprocalMangoldtCumulative,psi_sum,Finset.mul_sum,Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    unfold ccmWeilPolePrimeDiagonalAtom
    ring
  rw [hsum]
  unfold ccmWeilPoleDiagonalSmooth
  ring

/-- Exact frozen cross entry as its smooth source minus the affine arithmetic atoms. -/
theorem ccmWeilPoleChamberCross_eq_sum_atoms (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmWeilPoleChamberCross a s = ccmWeilPoleCrossSmooth s-
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊, ccmWeilPolePrimeCrossAtom n s := by
  rw [ccmWeilPoleChamberCross_eq_explicit]
  have hsum : ccmPolarPrimeTent a+2*(s-a.1)*ccmWeilPrimeChamberWeight a =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊, ccmWeilPolePrimeCrossAtom n s := by
    unfold ccmPolarPrimeTent ccmWeilPrimeChamberWeight
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    unfold ccmWeilPolePrimeCrossAtom
    ring
  rw [hsum]
  rfl

/-- Both arithmetic atoms vanish identically when the integer is not a prime power. -/
theorem ccmWeilPolePrimeAtoms_zero_of_not_primePow {n : ℕ} (hn : ¬IsPrimePow n) (s : ℝ) :
    ccmWeilPolePrimeDiagonalAtom n s = 0 ∧ ccmWeilPolePrimeCrossAtom n s = 0 := by
  simp [ccmWeilPolePrimeDiagonalAtom,ccmWeilPolePrimeCrossAtom,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]

/-- Both actual arithmetic atoms vanish at their entry radius. -/
theorem ccmWeilPolePrimeAtoms_zero_at_entry (n : ℕ) (hn : 2 ≤ n) :
    ccmWeilPolePrimeDiagonalAtom n (ccmWeilIntegerEntry n hn).1 = 0 ∧
    ccmWeilPolePrimeCrossAtom n (ccmWeilIntegerEntry n hn).1 = 0 := by
  let b := ccmWeilIntegerEntry n hn
  have he : Real.exp b.1/n = Real.exp (-b.1) := by
    rw [← exp_two_mul_ccmWeilIntegerEntry n hn,← Real.exp_sub]
    congr 1
    dsimp [b]
    ring
  constructor
  · change 2*ArithmeticFunction.vonMangoldt n*(Real.exp b.1/n-Real.exp (-b.1)) = 0
    rw [he,sub_self,mul_zero]
  · unfold ccmWeilPolePrimeCrossAtom ccmWeilIntegerEntry
    dsimp
    ring

/-- Crossing one integer cutoff subtracts exactly its diagonal prime atom. -/
theorem ccmWeilPoleChamberDiagonal_succ_cutoff (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊ = ⌊Real.exp (2*a.1)⌋₊+1) (s : ℝ) :
    ccmWeilPoleChamberDiagonal b s-ccmWeilPoleChamberDiagonal a s =
      -ccmWeilPolePrimeDiagonalAtom (⌊Real.exp (2*a.1)⌋₊+1) s := by
  have hn : 2 ≤ ⌊Real.exp (2*a.1)⌋₊+1 := by
    have : 1 ≤ ⌊Real.exp (2*a.1)⌋₊ := Nat.le_floor (by
      simpa using Real.one_le_exp_iff.mpr (by linarith [a.2] : 0 ≤ 2*a.1))
    omega
  rw [ccmWeilPoleChamberDiagonal_eq_sum_atoms,ccmWeilPoleChamberDiagonal_eq_sum_atoms,
    hf,Finset.sum_Icc_succ_top hn]
  ring

/-- Crossing one integer cutoff subtracts exactly its cross prime atom. -/
theorem ccmWeilPoleChamberCross_succ_cutoff (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊ = ⌊Real.exp (2*a.1)⌋₊+1) (s : ℝ) :
    ccmWeilPoleChamberCross b s-ccmWeilPoleChamberCross a s =
      -ccmWeilPolePrimeCrossAtom (⌊Real.exp (2*a.1)⌋₊+1) s := by
  have hn : 2 ≤ ⌊Real.exp (2*a.1)⌋₊+1 := by
    have : 1 ≤ ⌊Real.exp (2*a.1)⌋₊ := Nat.le_floor (by
      simpa using Real.one_le_exp_iff.mpr (by linarith [a.2] : 0 ≤ 2*a.1))
    omega
  rw [ccmWeilPoleChamberCross_eq_sum_atoms,ccmWeilPoleChamberCross_eq_sum_atoms,
    hf,Finset.sum_Icc_succ_top hn]
  ring

end RHTower
