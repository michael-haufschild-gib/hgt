import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolePrimeChamber

/-!
# Exact Weil pole handoff at the next integer entry

Both entries of the actual two-pole matrix equal their incoming frozen-cutoff
values at the next integer boundary. The new diagonal atom and its cross tent
vanish exactly there, although the underlying prime cumulatives jump.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

/-- The frozen diagonal with its prime cumulatives displayed explicitly. -/
theorem ccmWeilPoleChamberDiagonal_eq_explicit (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmWeilPoleChamberDiagonal a s =
      2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*Real.sinh s +
      (-1-2*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)))*Real.exp s +
      (2*s+1+2*Chebyshev.psi (Real.exp (2*a.1)))*Real.exp (-s) +
      8*s*Real.sinh s+ccmGammaPoleSelfBoundaryPrimitive s := by
  change 2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*Real.sinh s +
    (-1-2*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)))*Real.exp s +
    (2*s+(1+2*Chebyshev.psi (Real.exp (2*a.1))))*Real.exp (-s)+
    8*s*Real.sinh s+ccmGammaPoleSelfBoundaryPrimitive s = _
  ring

/-- The frozen cross entry retains the exact affine continuation of the prime tent. -/
theorem ccmWeilPoleChamberCross_eq_explicit (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmWeilPoleChamberCross a s =
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*s)+2*s^(2 : ℕ)+
      (2*Real.sinh s)^(2 : ℕ)+ccmGammaPoleCrossBoundaryPrimitive s-
      (ccmPolarPrimeTent a+2*(s-a.1)*ccmWeilPrimeChamberWeight a) := by
  change (2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))-
    2*ccmWeilPrimeChamberWeight a)*s+2*s^(2 : ℕ)+4*Real.sinh s^(2 : ℕ)+
    (2*a.1*ccmWeilPrimeChamberWeight a-ccmPolarPrimeTent a)+_ = _
  ring

private theorem next_ge_two (a : SuzukiPositiveAperture) :
    2 ≤ ⌊Real.exp (2*a.1)⌋₊+1 := by
  have h : 1 ≤ ⌊Real.exp (2*a.1)⌋₊ := Nat.le_floor (by
    simpa using (Real.one_le_exp_iff.mpr (by linarith [a.2] : 0 ≤ 2*a.1)))
  omega

private theorem entry_log (a b : SuzukiPositiveAperture)
    (hb : Real.exp (2*b.1) = (⌊Real.exp (2*a.1)⌋₊+1:ℕ)) :
    Real.log (⌊Real.exp (2*a.1)⌋₊+1:ℕ) = 2*b.1 := by
  rw [← hb,Real.log_exp]

private theorem entry_M (a b : SuzukiPositiveAperture)
    (hb : Real.exp (2*b.1) = (⌊Real.exp (2*a.1)⌋₊+1:ℕ)) :
    ccmReciprocalMangoldtCumulative (Real.exp (2*b.1)) =
      ccmReciprocalMangoldtCumulative (Real.exp (2*a.1))+
      ArithmeticFunction.vonMangoldt (⌊Real.exp (2*a.1)⌋₊+1)/(⌊Real.exp (2*a.1)⌋₊+1:ℕ) := by
  unfold ccmReciprocalMangoldtCumulative
  rw [hb,Nat.floor_natCast,Finset.sum_Icc_succ_top (next_ge_two a)]

private theorem entry_psi (a b : SuzukiPositiveAperture)
    (hb : Real.exp (2*b.1) = (⌊Real.exp (2*a.1)⌋₊+1:ℕ)) :
    Chebyshev.psi (Real.exp (2*b.1)) = Chebyshev.psi (Real.exp (2*a.1))+
      ArithmeticFunction.vonMangoldt (⌊Real.exp (2*a.1)⌋₊+1) := by
  rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.psi_eq_sum_Icc,hb,Nat.floor_natCast,
    Finset.sum_Icc_succ_top (Nat.zero_le _)]

private theorem entry_tent (a b : SuzukiPositiveAperture)
    (hb : Real.exp (2*b.1) = (⌊Real.exp (2*a.1)⌋₊+1:ℕ)) :
    ccmPolarPrimeTent b = ccmPolarPrimeTent a+2*(b.1-a.1)*ccmWeilPrimeChamberWeight a := by
  unfold ccmPolarPrimeTent ccmWeilPrimeChamberWeight
  rw [hb,Nat.floor_natCast,Finset.sum_Icc_succ_top (next_ge_two a),entry_log a b hb,
    sub_self,mul_zero,add_zero,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The actual diagonal at the next integer entry equals the incoming chamber value:
the newly entering atom has exactly zero diagonal energy. -/
theorem ccmWeilPoleDiagonal_eq_chamber_at_next_entry (a b : SuzukiPositiveAperture)
    (hb : Real.exp (2*b.1) = (⌊Real.exp (2*a.1)⌋₊+1:ℕ)) :
    ccmWeilPoleDiagonal b = ccmWeilPoleChamberDiagonal a b.1 := by
  rw [ccmWeilPoleDiagonal_eq,ccmGammaPoleSelfBoundaryMass_eq_primitive,
    ccmWeilPoleChamberDiagonal_eq_explicit,entry_M a b hb,entry_psi a b hb]
  have he : Real.exp b.1 / (⌊Real.exp (2*a.1)⌋₊+1:ℕ) = Real.exp (-b.1) := by
    rw [← hb,← Real.exp_sub]
    congr 1
    ring
  have hcancel := congrArg (fun x : ℝ => x *
    ArithmeticFunction.vonMangoldt (⌊Real.exp (2*a.1)⌋₊+1)) he
  simp only [div_eq_mul_inv] at hcancel ⊢
  nlinarith [hcancel]

/-- The actual cross entry at the next integer entry equals the incoming chamber value:
the newly entering prime tent vanishes at its endpoint. -/
theorem ccmWeilPoleCross_eq_chamber_at_next_entry (a b : SuzukiPositiveAperture)
    (hb : Real.exp (2*b.1) = (⌊Real.exp (2*a.1)⌋₊+1:ℕ)) :
    ccmWeilPoleCross b = ccmWeilPoleChamberCross a b.1 := by
  rw [ccmWeilPoleCross_eq,ccmGammaPoleCrossBoundaryMass_eq_primitive,
    ccmWeilPoleChamberCross_eq_explicit,entry_tent a b hb]

/-- Exact odd-source handoff across the next integer cutoff boundary. -/
theorem ccmWeilOddPole_eq_chamber_at_next_entry (a b : SuzukiPositiveAperture)
    (hb : Real.exp (2*b.1) = (⌊Real.exp (2*a.1)⌋₊+1:ℕ)) :
    ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1)) =
      ccmWeilOddPoleChamber a b.1 := by
  rw [ccmWeilPoleCompression_parity_energy b (Or.inr rfl),
    ccmWeilPoleDiagonal_eq_chamber_at_next_entry a b hb,
    ccmWeilPoleCross_eq_chamber_at_next_entry a b hb]
  unfold ccmWeilOddPoleChamber
  ring

end RHTower
