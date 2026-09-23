import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMForcedMetricCompact

/-! Exact horizon and boundary values and conformally rescaled boundary limit. -/

open GaloisForLFunctions.HTGeometry Filter Topology
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMIngoingCoordinates
noncomputable section

/-- Exact unrescaled metric boundary value, retaining the exact du-angular entries. -/
def forcedBoundaryMetric (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) (z : Point) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let s := physicalRate q branch
  let E := a^(2 : ℕ)*Complex.exp ((2*s)*(v:ℂ))
  let U := fun k => E*(-2*s*fullAngularCovector q branch k z)
  !![0,0,0,0; 0,0,U 0,U 1; 0,U 0,0,0; 0,U 1,0,0]

/-- Exact horizon value of the complete reconstructed metric. -/
def forcedHorizonMetric (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) (z : Point) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let s := physicalRate q branch
  let c := s*(s-1)/4
  let E := a^(2 : ℕ)*Complex.exp ((2*s)*((v:ℂ)+Complex.log 2))
  let T := fun k => E*(2*s*(fullAngularCovector q branch k z-c*fullSquareCovector q k z))
  let U := fun k => E*(-s*fullAngularCovector q branch k z+c*(s+2)*fullSquareCovector q k z)
  !![0,0,T 0,T 1; 0,0,U 0,U 1; T 0,U 0,0,0; T 1,U 1,0,0]

/-- The full reconstructed boundary value is explicit in the actual global angular response. -/
theorem compactForcedMetric_boundary_value (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) : compactForcedMetric q branch a v 0 z = forcedBoundaryMetric q branch a v z := by
  simp [compactForcedMetric,forcedBoundaryMetric,compactEnvelope]

/-- The full horizon value retains both the response and the original squared-source covector. -/
theorem compactForcedMetric_horizon_value (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) : compactForcedMetric q branch a v 1 z = forcedHorizonMetric q branch a v z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactForcedMetric,forcedHorizonMetric,compactEnvelope]
  all_goals ring_nf

/-- The actual inverse-radius metric has this finite horizon limit. -/
theorem compactForcedMetric_horizon (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (i j : Fin 4) :
    Tendsto (fun u => compactForcedMetric q branch a v u z i j) (𝓝 1)
      (𝓝 (forcedHorizonMetric q branch a v z i j)) := by
  have h := (compactForcedMetric_smooth q branch a v 1 z
    (by norm_num [Complex.mem_slitPlane_iff]) 0 i j).continuousAt.tendsto
  simpa only [compactForcedMetric_horizon_value] using h

/-- Its unrescaled boundary limit retains the radial-angular component. -/
theorem compactForcedMetric_boundary (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (i j : Fin 4) :
    Tendsto (fun u => compactForcedMetric q branch a v u z i j) (𝓝 0)
      (𝓝 (forcedBoundaryMetric q branch a v z i j)) := by
  have h := (compactForcedMetric_smooth q branch a v 0 z
    (by norm_num [Complex.mem_slitPlane_iff]) 0 i j).continuousAt.tendsto
  simpa only [compactForcedMetric_boundary_value] using h

/-- The complete conformally rescaled perturbation vanishes at the boundary after actual metric reconstruction. -/
theorem compactForcedMetric_conformal_boundary (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (i j : Fin 4) :
    Tendsto (fun u : ℂ => u^(2 : ℕ)*compactForcedMetric q branch a v u z i j) (𝓝 0) (𝓝 0) := by
  simpa using ((continuousAt_id (x := (0 : ℂ))).pow 2).tendsto.mul
    (compactForcedMetric_boundary q branch a v z i j)

end
end RHTower.D4BMModularCore
