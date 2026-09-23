import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamMetricEinstein

/-! Identification and cancellation of the complete original mixed Einstein source. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMMetricReconstruction D4BMGlobalAngularResponse D4BMQuadraticMixedSource
noncomputable section

/-- The full original mixed source, expressed through its actual quadratic covectors. -/
def literalMixedSource (q : XiZeroCopy) (branch : Bool) (r B : ℂ) (z : Point) : Matrix (Fin 4) (Fin 4) ℂ :=
  let s := physicalRate q branch
  let J := fullSquareCovector q
  let K := fullGradientCovector q branch
  let T0 := B^(2 : ℕ)*(timeSquare s r*J 0 z+timeGradient s r*K 0 z)
  let T1 := B^(2 : ℕ)*(timeSquare s r*J 1 z+timeGradient s r*K 1 z)
  let R0 := B^(2 : ℕ)*(radialSquare s r*J 0 z+radialGradient s r*K 0 z)
  let R1 := B^(2 : ℕ)*(radialSquare s r*J 1 z+radialGradient s r*K 1 z)
  !![0,0,T0,T1; 0,0,R0,R1; T0,R0,0,0; T1,R1,0,0]

/-- Every component is exactly the retained original quadratic Einstein source tensor. -/
theorem literalMixedSource_eq (q : XiZeroCopy) (branch : Bool) (r B : ℂ) (z : Point) :
    literalMixedSource q branch r B z =
      tensor (physicalRate q branch) r (z 1) B (scalar (center q) z)
        (coordDeriv 0 (scalar (center q)) z) (coordDeriv 1 (scalar (center q)) z)
        (coordDeriv 0 (coordDeriv 0 (scalar (center q))) z)
        (coordDeriv 0 (coordDeriv 1 (scalar (center q))) z) := by
  have hj := fullSquareCovector_source q z
  have hj0 := congrArg Prod.fst hj
  have hj1 := congrArg Prod.snd hj
  dsimp only at hj0 hj1
  norm_num [literalMixedSource,tensor,hj0,hj1,fullGradientCovector]

private theorem radius_nonzero (p : D4BMBackground.ExteriorPoint) :
    (p.val 1 : ℂ) ≠ 0 ∧ (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
  constructor
  · exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  · exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)

/-- Both master factors cancel the complete mixed source tensor, including its temporal components. -/
theorem streamMetricTensor_forced (q : XiZeroCopy) (branch : Bool) (p : D4BMBackground.ExteriorPoint)
    (B : ℂ) (i j : Fin 4) :
    let s := physicalRate q branch
    let z := angularPoint p.val
    streamMetricTensor (2*s) (p.val 1) (B^(2 : ℕ)) false (fullAngularCovector q branch) z i j-
      (s*(s-1)/4)*streamMetricTensor (2*s) (p.val 1) (B^(2 : ℕ)) true (fullSquareCovector q) z i j =
      -literalMixedSource q branch (p.val 1) B z i j := by
  let s := physicalRate q branch
  let z := angularPoint p.val
  let r := (p.val 1 : ℂ)
  let c := s*(s-1)/4
  let A := fullAngularCovector q branch
  let J := fullSquareCovector q
  let K := fullGradientCovector q branch
  have hr : r ≠ 0 := (radius_nonzero p).1
  have hf : r^(2 : ℕ)-1 ≠ 0 := (radius_nonzero p).2
  have ht (k : Fin 2) :
      -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*streamMasterFirst (2*s) r (B^(2 : ℕ)) false A k z-
        c*(-(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*streamMasterFirst (2*s) r (B^(2 : ℕ)) true J k z) =
      -(B^(2 : ℕ)*(timeSquare s r*J k z+timeGradient s r*K k z)) := by
    calc
      _ = -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*(streamMasterFirst (2*s) r (B^(2 : ℕ)) false A k z-
          c*streamMasterFirst (2*s) r (B^(2 : ℕ)) true J k z) := by ring
      _ = -(r^(2 : ℕ)-1)/r^(2 : ℕ)*currentFirst s r B (J k z) (K k z) := by
        rw [forced_stream_masterFirst q branch p B k]
        ring
      _ = _ := by
        rw [← temporal_current s r B (J k z) (K k z) hr hf]
        field_simp [hr,hf]
  have hv (k : Fin 2) :
      -(2*s)/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*streamMaster (2*s) r (B^(2 : ℕ)) false A k z-
        c*(-(2*s)/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*streamMaster (2*s) r (B^(2 : ℕ)) true J k z) =
      -(B^(2 : ℕ)*(radialSquare s r*J k z+radialGradient s r*K k z)) := by
    calc
      _ = -(2*s)/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*(streamMaster (2*s) r (B^(2 : ℕ)) false A k z-
          c*streamMaster (2*s) r (B^(2 : ℕ)) true J k z) := by ring
      _ = -((2*s)*current s r B (J k z) (K k z))/(r^(2 : ℕ)*(r^(2 : ℕ)-1)) := by
        rw [forced_stream_master q branch p B k]
        field_simp [hr,hf]
        ring
      _ = _ := by
        rw [← radial_current s r B (J k z) (K k z) hr hf]
        field_simp [hr,hf]
  change streamMetricTensor (2*s) r (B^(2 : ℕ)) false A z i j-
    c*streamMetricTensor (2*s) r (B^(2 : ℕ)) true J z i j = -literalMixedSource q branch r B z i j
  fin_cases i <;> fin_cases j
  all_goals first | exact ht 0 | exact ht 1 | exact hv 0 | exact hv 1 |
    simp [streamMetricTensor,literalMixedSource]

end
end RHTower.D4BMModularCore
