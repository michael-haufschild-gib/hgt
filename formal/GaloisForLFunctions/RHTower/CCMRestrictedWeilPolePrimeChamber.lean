import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleBoundaryDifferential
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleCompression

/-!
# Exact moving pole equations inside a prime cutoff chamber

Freezing the integer cutoff freezes both prime cumulatives and makes the exact
prime tent affine in aperture. The resulting expressions equal the actual full
Weil pole matrix at every aperture with that cutoff. The diagonal satisfies an
inhomogeneous second-order equation, and the cross entry has a universal second
derivative. The moving odd pole inherits the exact coupled differential law.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

private def bulkA (α β δ s : ℝ) : ℝ :=
  α*Real.sinh s+β*Real.exp s+(2*s+δ)*Real.exp (-s)+8*s*Real.sinh s

private def slopeA (α β δ s : ℝ) : ℝ :=
  α*Real.cosh s+β*Real.exp s+(2-(2*s+δ))*Real.exp (-s)+8*Real.sinh s+8*s*Real.cosh s

private theorem bulkA_deriv (α β δ s : ℝ) :
    HasDerivAt (bulkA α β δ) (slopeA α β δ s) s := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-s)) s := by
    simpa only [Pi.neg_apply,id_eq,mul_neg_one] using! (hasDerivAt_id s).neg.exp
  convert! ((((Real.hasDerivAt_sinh s).const_mul α).add
    ((Real.hasDerivAt_exp s).const_mul β)).add
    ((((hasDerivAt_id s).const_mul 2).add_const δ).mul he)).add
    (((hasDerivAt_id s).const_mul 8).mul (Real.hasDerivAt_sinh s)) using 1
  unfold slopeA
  simp only [id_eq]
  ring

private theorem slopeA_deriv (α β δ s : ℝ) :
    HasDerivAt (slopeA α β δ)
      (bulkA α β δ s-4*Real.exp (-s)+16*Real.cosh s) s := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-s)) s := by
    simpa only [Pi.neg_apply,id_eq,mul_neg_one] using! (hasDerivAt_id s).neg.exp
  convert! (((((Real.hasDerivAt_cosh s).const_mul α).add
    ((Real.hasDerivAt_exp s).const_mul β)).add
    (((((hasDerivAt_id s).const_mul 2).add_const δ).const_sub 2).mul he)).add
    ((Real.hasDerivAt_sinh s).const_mul 8)).add
    (((hasDerivAt_id s).const_mul 8).mul (Real.hasDerivAt_cosh s)) using 1
  unfold bulkA
  simp only [id_eq]
  ring

private def bulkC (α β s : ℝ) : ℝ := α*s+2*s^(2 : ℕ)+4*Real.sinh s^(2 : ℕ)+β
private def slopeC (α s : ℝ) : ℝ := α+4*s+8*Real.sinh s*Real.cosh s

private theorem bulkC_deriv (α β s : ℝ) :
    HasDerivAt (bulkC α β) (slopeC α s) s := by
  convert! (((((hasDerivAt_id s).const_mul α).add
    (((hasDerivAt_id s).pow 2).const_mul 2)).add
    (((Real.hasDerivAt_sinh s).pow 2).const_mul 4)).add_const β) using 1
  unfold slopeC
  simp only [id_eq]
  ring

private theorem slopeC_deriv (α s : ℝ) :
    HasDerivAt (slopeC α) (8*Real.cosh (2*s)+4) s := by
  convert! (((hasDerivAt_const s α).add ((hasDerivAt_id s).const_mul 4)).add
    (((Real.hasDerivAt_sinh s).const_mul 8).mul (Real.hasDerivAt_cosh s))) using 1
  rw [Real.cosh_two_mul]
  ring

/-- Exact derivative weight of the finite prime tent in a fixed cutoff chamber. -/
def ccmWeilPrimeChamberWeight (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ArithmeticFunction.vonMangoldt n*(1+1/(n:ℝ))

private def diagonalAlpha : ℝ := 2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))
private def diagonalBeta (a : SuzukiPositiveAperture) : ℝ :=
  -1-2*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1))
private def diagonalDelta (a : SuzukiPositiveAperture) : ℝ :=
  1+2*Chebyshev.psi (Real.exp (2*a.1))
private def crossAlpha (a : SuzukiPositiveAperture) : ℝ := diagonalAlpha-2*ccmWeilPrimeChamberWeight a
private def crossBeta (a : SuzukiPositiveAperture) : ℝ :=
  2*a.1*ccmWeilPrimeChamberWeight a-ccmPolarPrimeTent a

/-- The exact diagonal expression with prime cumulatives frozen at one actual aperture. -/
def ccmWeilPoleChamberDiagonal (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  bulkA diagonalAlpha (diagonalBeta a) (diagonalDelta a) s+ccmGammaPoleSelfBoundaryPrimitive s

/-- The exact cross expression in the same prime cutoff chamber. -/
def ccmWeilPoleChamberCross (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  bulkC (crossAlpha a) (crossBeta a) s+ccmGammaPoleCrossBoundaryPrimitive s

/-- The literal odd energy continued within one fixed prime cutoff chamber. -/
def ccmWeilOddPoleChamber (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  2*(ccmWeilPoleChamberDiagonal a s-ccmWeilPoleChamberCross a s)

private theorem tent_chamber (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) :
    ccmPolarPrimeTent b=ccmPolarPrimeTent a+2*(b.1-a.1)*ccmWeilPrimeChamberWeight a := by
  unfold ccmPolarPrimeTent ccmWeilPrimeChamberWeight
  rw [hf,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The chamber diagonal equals the actual full Weil diagonal at every matching cutoff. -/
theorem ccmWeilPoleDiagonal_eq_chamber_of_floor_eq (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) :
    ccmWeilPoleDiagonal b=ccmWeilPoleChamberDiagonal a b.1 := by
  have hM : ccmReciprocalMangoldtCumulative (Real.exp (2*b.1))=
      ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)) := by
    unfold ccmReciprocalMangoldtCumulative
    rw [hf]
  have hpsi : Chebyshev.psi (Real.exp (2*b.1))=Chebyshev.psi (Real.exp (2*a.1)) := by
    rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.psi_eq_sum_Icc,hf]
  rw [ccmWeilPoleDiagonal_eq,ccmGammaPoleSelfBoundaryMass_eq_primitive,hM,hpsi]
  unfold ccmWeilPoleChamberDiagonal bulkA diagonalAlpha diagonalBeta diagonalDelta
  ring

/-- The chamber cross entry equals the actual full Weil cross entry at every matching cutoff. -/
theorem ccmWeilPoleCross_eq_chamber_of_floor_eq (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) :
    ccmWeilPoleCross b=ccmWeilPoleChamberCross a b.1 := by
  rw [ccmWeilPoleCross_eq,ccmGammaPoleCrossBoundaryMass_eq_primitive,tent_chamber a b hf]
  unfold ccmWeilPoleChamberCross bulkC crossAlpha crossBeta diagonalAlpha
  ring

/-- Exact actual-source identification throughout each fixed prime cutoff chamber. -/
theorem ccmWeilOddPole_eq_chamber_of_floor_eq (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) :
    ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1))=ccmWeilOddPoleChamber a b.1 := by
  rw [ccmWeilPoleCompression_parity_energy b (Or.inr rfl),
    ccmWeilPoleDiagonal_eq_chamber_of_floor_eq a b hf,ccmWeilPoleCross_eq_chamber_of_floor_eq a b hf]
  unfold ccmWeilOddPoleChamber
  ring

private def diagonalSlope (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  slopeA diagonalAlpha (diagonalBeta a) (diagonalDelta a) s+ccmGammaPoleSelfBoundarySlope s
private def crossSlope (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  slopeC (crossAlpha a) s+2*ccmGammaPoleBoundaryLog (2*s)

private theorem diagonal_deriv (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    HasDerivAt (ccmWeilPoleChamberDiagonal a) (diagonalSlope a s) s := by
  exact (bulkA_deriv _ _ _ _).add (hasDerivAt_ccmGammaPoleSelfBoundaryPrimitive hs)

private theorem cross_deriv (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    HasDerivAt (ccmWeilPoleChamberCross a) (crossSlope a s) s := by
  exact (bulkC_deriv _ _ _).add (hasDerivAt_ccmGammaPoleCrossBoundaryPrimitive hs)

private theorem diagonalSlope_deriv (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    HasDerivAt (diagonalSlope a)
      (ccmWeilPoleChamberDiagonal a s+16*Real.cosh s-4*Real.exp (-s)-
        4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1)) s := by
  convert! (slopeA_deriv diagonalAlpha (diagonalBeta a) (diagonalDelta a) s).add
    (hasDerivAt_ccmGammaPoleSelfBoundarySlope hs) using 1
  unfold ccmWeilPoleChamberDiagonal
  ring

private theorem crossSlope_deriv (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    HasDerivAt (crossSlope a) (8*Real.cosh (2*s)+4-4/(Real.exp (2*s)-1)) s := by
  have hL : HasDerivAt (fun y => 2*ccmGammaPoleBoundaryLog (2*y))
      (-4/(Real.exp (2*s)-1)) s := by
    convert! ((hasDerivAt_ccmGammaPoleBoundaryLog (by linarith : 0<2*s)).comp s
      ((hasDerivAt_id s).const_mul 2)).const_mul 2 using 1
    ring
  convert! (slopeC_deriv (crossAlpha a) s).add hL using 1
  ring

/-- Differentiability of the actual diagonal expression within every prime cutoff chamber. -/
theorem differentiableAt_ccmWeilPoleChamberDiagonal (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    DifferentiableAt ℝ (ccmWeilPoleChamberDiagonal a) s := (diagonal_deriv a hs).differentiableAt

/-- Differentiability of the actual cross expression within every prime cutoff chamber. -/
theorem differentiableAt_ccmWeilPoleChamberCross (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    DifferentiableAt ℝ (ccmWeilPoleChamberCross a) s := (cross_deriv a hs).differentiableAt

/-- All frozen prime cumulatives disappear from the shifted diagonal differential law. -/
theorem deriv_deriv_ccmWeilPoleChamberDiagonal_sub (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    deriv (deriv (ccmWeilPoleChamberDiagonal a)) s-ccmWeilPoleChamberDiagonal a s =
      16*Real.cosh s-4*Real.exp (-s)-4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1) := by
  have he : deriv (ccmWeilPoleChamberDiagonal a) =ᶠ[𝓝 s] diagonalSlope a := by
    filter_upwards [eventually_gt_nhds hs] with y hy
    exact (diagonal_deriv a hy).deriv
  rw [((diagonalSlope_deriv a hs).congr_of_eventuallyEq he).deriv]
  ring

/-- The actual cross entry has a universal second derivative inside every prime chamber. -/
theorem deriv_deriv_ccmWeilPoleChamberCross (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    deriv (deriv (ccmWeilPoleChamberCross a)) s=8*Real.cosh (2*s)+4-4/(Real.exp (2*s)-1) := by
  have he : deriv (ccmWeilPoleChamberCross a) =ᶠ[𝓝 s] crossSlope a := by
    filter_upwards [eventually_gt_nhds hs] with y hy
    exact (cross_deriv a hy).deriv
  exact ((crossSlope_deriv a hs).congr_of_eventuallyEq he).deriv

/-- The moving odd pole is differentiable within each prime cutoff chamber. -/
theorem differentiableAt_ccmWeilOddPoleChamber (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    DifferentiableAt ℝ (ccmWeilOddPoleChamber a) s :=
  ((diagonal_deriv a hs).sub (cross_deriv a hs)).const_mul 2 |>.differentiableAt

/-- Exact shifted odd differential law; its prime dependence survives through the full cross entry. -/
theorem deriv_deriv_ccmWeilOddPoleChamber_sub (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0<s) :
    deriv (deriv (ccmWeilOddPoleChamber a)) s-ccmWeilOddPoleChamber a s =
      2*(16*Real.cosh s-4*Real.exp (-s)-
        4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1)-
        (8*Real.cosh (2*s)+4-4/(Real.exp (2*s)-1))+ccmWeilPoleChamberCross a s) := by
  have he : deriv (ccmWeilOddPoleChamber a) =ᶠ[𝓝 s]
      (fun y => 2*(diagonalSlope a y-crossSlope a y)) := by
    filter_upwards [eventually_gt_nhds hs] with y hy
    exact (((diagonal_deriv a hy).sub (cross_deriv a hy)).const_mul 2).deriv
  have hd := ((diagonalSlope_deriv a hs).sub (crossSlope_deriv a hs)).const_mul 2
  rw [(hd.congr_of_eventuallyEq he).deriv]
  unfold ccmWeilOddPoleChamber
  ring

end RHTower
