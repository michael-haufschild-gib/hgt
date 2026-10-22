import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedGreenContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalRadialModeMatching

/-! Exact finite resolvent assembly, retaining every angular gap and its collision locus. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Difference between an original principal eigenvalue and the actual physical target eigenvalue. -/
def physicalAngularGap (q r : XiZeroCopy) (i : Fin 3) : ℂ :=
  principalExponent q i*(principalExponent q i-1)+(1/4+physicalRadialFrequency r^(2 : ℕ))

def physicalAngularGapProduct (q r : XiZeroCopy) : ℂ := ∏ i : Fin 3, physicalAngularGap q r i

def physicalAngularGapCofactor (q r : XiZeroCopy) (i : Fin 3) : ℂ :=
  ∏ j ∈ (Finset.univ : Finset (Fin 3)).erase i, physicalAngularGap q r j

/-- Cofactor cancellation is an exact identity, including zero angular gaps. -/
theorem physicalAngularGapCofactor_mul (q r : XiZeroCopy) (i : Fin 3) :
    physicalAngularGapCofactor q r i*physicalAngularGap q r i = physicalAngularGapProduct q r := by
  simpa only [physicalAngularGapCofactor,physicalAngularGapProduct,mul_comm] using
    Finset.mul_prod_erase Finset.univ (physicalAngularGap q r) (Finset.mem_univ i)

/-- The complete source determines all coefficients of the denominator-cleared response. -/
def physicalResolventAssembly (q r : XiZeroCopy) (U : ℂ → ℝ → ℂ) (V : Fin 3 → ℝ → ℂ) (t : ℝ) : ℂ :=
  physicalAngularGapProduct q r*U (scalarResidualPeriod q (physicalAngularParameter r)) t+
    ∑ i : Fin 3, (physicalAngularGapCofactor q r i*scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q i))*
      (V i t-U (principalAmplitude q i) t)

def clearedPhysicalGreen (q r : XiZeroCopy) (branch : Bool) (w a : ℂ) : ℝ → ℂ :=
  physicalResolventAssembly q r
    (fun J => continuedReducedGreen w (physicalRadialFrequency r) (physicalRate q branch) a J)
    (continuedPrincipalDifference q branch w a)

def clearedPhysicalGreenFirst (q r : XiZeroCopy) (branch : Bool) (w a : ℂ) : ℝ → ℂ :=
  physicalResolventAssembly q r
    (fun J => continuedReducedGreenFirst w (physicalRadialFrequency r) (physicalRate q branch) a J)
    (continuedPrincipalDifferenceFirst q branch w a)

def clearedPhysicalGreenSecond (q r : XiZeroCopy) (branch : Bool) (w a : ℂ) : ℝ → ℂ :=
  physicalResolventAssembly q r
    (fun J => continuedReducedGreenSecond w (physicalRadialFrequency r) (physicalRate q branch) a J)
    (continuedPrincipalDifferenceSecond q branch w a)

/-- Actual radial differentiation preserves every coefficient and all three subtracted channels. -/
theorem clearedPhysicalGreen_hasDerivAt (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    HasDerivAt (clearedPhysicalGreen q r branch w a) (clearedPhysicalGreenFirst q r branch w a t) t ∧
    HasDerivAt (clearedPhysicalGreenFirst q r branch w a) (clearedPhysicalGreenSecond q r branch w a t) t := by
  have hU (J : ℂ) := continuedReducedGreen_hasDerivAt w (physicalRadialFrequency r) (physicalRate q branch) a J hw hwr t ht
  have hV (i : Fin 3) := continuedPrincipalDifference_hasDerivAt q branch w a hw hwr i t ht
  constructor
  · exact ((hU _).1.const_mul _).add (HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      (((hV i).1).sub (hU _).1).const_mul _))
  · exact ((hU _).2.const_mul _).add (HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      (((hV i).2).sub (hU _).2).const_mul _))

/-- The cleared finite assembly is meromorphic without assuming any angular gaps are nonzero. -/
theorem clearedPhysicalGreen_meromorphicAt (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    MeromorphicAt (fun v => clearedPhysicalGreen q r branch v a t) w := by
  have hconst (c : ℂ) : MeromorphicAt (fun _ : ℂ => c) w := analyticAt_const.meromorphicAt
  have hU (J : ℂ) := continuedReducedGreen_meromorphicAt w (physicalRadialFrequency r) (physicalRate q branch) a J hw hwr t ht
  have hV (i : Fin 3) := continuedPrincipalDifference_meromorphicAt q branch w a hw hwr i t ht
  exact ((hconst _).mul (hU _)).add (MeromorphicAt.fun_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun i _ => (hconst _).mul ((hV i).sub (hU _))))

end
end RHTower.D4BMJointSource
