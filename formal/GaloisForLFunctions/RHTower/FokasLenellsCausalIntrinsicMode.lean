import GaloisForLFunctions.RHTower.FokasLenellsCausalIntrinsicFrequency
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyTransport
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencySupport

/-! Actual eigenmodes, frequency means, projections and scalar amplitudes indexed
by intrinsic complex unit rates. Exact chart independence follows from the scalar
homeomorphism and the canonical underlying-chain transport. -/
open Complex Set Filter Topology
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized bounded derivative eigenchain at an intrinsic unit rate. -/
def causalIntrinsicFrequencyMode (z : causalUnitFrequency) : causalFrequencySpace 0 :=
  causalFrequencyMode 0 (causalUnitFrequencyCoordinate 0 z)

/-- The actual finite frequency mean indexed by its intrinsic scalar rate. -/
def causalIntrinsicFrequencyMean (z : causalUnitFrequency) (N : ℕ) :
    causalBoundedChain →L[ℂ] causalBoundedChain :=
  causalBoundedFrequencyMean 0 (causalUnitFrequencyCoordinate 0 z) N

/-- The actual completed rank-one frequency projection at an intrinsic unit rate. -/
def causalIntrinsicFrequencyProjection (z : causalUnitFrequency) :
    causalFrequencySpace 0 →L[ℂ] causalFrequencySpace 0 :=
  causalFrequencyProjection 0 (causalUnitFrequencyCoordinate 0 z)

/-- Canonical scalar amplitude indexed by the actual complex unit rate. -/
def causalIntrinsicFrequencyCoefficient (z : causalUnitFrequency) :
    causalFrequencySpace 0 →L[ℂ] ℂ :=
  causalFrequencyCoefficient 0 (causalUnitFrequencyCoordinate 0 z)

private theorem coordinate_eq_iff (z w : causalUnitFrequency) :
    causalUnitFrequencyCoordinate 0 z = causalUnitFrequencyCoordinate 0 w ↔ z = w := by
  constructor
  · intro h
    have he := congrArg (causalUnitFrequencyRate 0) h
    simpa only [causalUnitFrequencyRate_coordinate] using he
  · intro h
    exact congrArg (causalUnitFrequencyCoordinate 0) h

private theorem coordinate_chart (b : ℝ) (z : causalUnitFrequency) :
    causalUnitFrequencyCoordinate b z =
      Real.exp (b - 0) * causalUnitFrequencyCoordinate 0 z := by
  have h := causalUnitFrequencyHomeomorph_relabel 0 b (causalUnitFrequencyCoordinate 0 z)
  change causalUnitFrequencyCoordinate b
    (causalUnitFrequencyRate 0 (causalUnitFrequencyCoordinate 0 z)) = _ at h
  simpa only [causalUnitFrequencyRate_coordinate] using h

/-- The intrinsic actual mode has unit bounded-chain norm. -/
theorem norm_causalIntrinsicFrequencyMode (z : causalUnitFrequency) :
    ‖causalIntrinsicFrequencyMode z‖ = 1 :=
  norm_causalBoundedUnitEigenchain 0 (causalUnitFrequencyCoordinate 0 z)

/-- Its intrinsic label is exactly the eigenvalue of the actual bounded derivative shift. -/
theorem causalBoundedChainShift_intrinsicFrequencyMode (z : causalUnitFrequency) :
    causalBoundedChainShift (causalIntrinsicFrequencyMode z).val =
      z.val • (causalIntrinsicFrequencyMode z).val := by
  have hr : (causalUnitBoundaryRate 0 (causalUnitFrequencyCoordinate 0 z)).val = z.val :=
    congrArg (fun w : causalUnitFrequency => w.val) (causalUnitFrequencyRate_coordinate 0 z)
  exact (causalBoundedChainShift_unitEigenchain 0 (causalUnitFrequencyCoordinate 0 z)).trans
    (congrArg (fun t : ℂ => t • (causalIntrinsicFrequencyMode z).val) hr)

/-- Intrinsically indexed actual means converge strongly on the complete frequency space. -/
theorem causalIntrinsicFrequencyProjection_tendsto (z : causalUnitFrequency)
    (u : causalFrequencySpace 0) :
    Tendsto (fun N : ℕ => causalIntrinsicFrequencyMean z N u.val) atTop
      (𝓝 (causalIntrinsicFrequencyProjection z u).val) :=
  causalFrequencyProjection_tendsto 0 (causalUnitFrequencyCoordinate 0 z) u

/-- The intrinsic projection has exactly the actual one-dimensional mode line as range. -/
theorem causalIntrinsicFrequencyProjection_range (z : causalUnitFrequency) :
    LinearMap.range (causalIntrinsicFrequencyProjection z).toLinearMap =
      Submodule.span ℂ {causalIntrinsicFrequencyMode z} :=
  causalFrequencyProjection_range 0 (causalUnitFrequencyCoordinate 0 z)

/-- Equality of intrinsic rates determines the complete rank-one projection algebra. -/
theorem causalIntrinsicFrequencyProjection_comp (z w : causalUnitFrequency) :
    (causalIntrinsicFrequencyProjection z).comp (causalIntrinsicFrequencyProjection w) =
      if z = w then causalIntrinsicFrequencyProjection z else 0 := by
  simpa only [causalIntrinsicFrequencyProjection, coordinate_eq_iff] using!
    causalFrequencyProjection_comp 0 (causalUnitFrequencyCoordinate 0 z)
      (causalUnitFrequencyCoordinate 0 w)

/-- Actual modes have Kronecker amplitudes indexed directly by their complex rates. -/
theorem causalIntrinsicFrequencyCoefficient_mode (z w : causalUnitFrequency) :
    causalIntrinsicFrequencyCoefficient z (causalIntrinsicFrequencyMode w) =
      if z = w then 1 else 0 := by
  simpa only [causalIntrinsicFrequencyCoefficient, causalIntrinsicFrequencyMode,
    coordinate_eq_iff] using!
    causalFrequencyCoefficient_mode 0 (causalUnitFrequencyCoordinate 0 z)
      (causalUnitFrequencyCoordinate 0 w)

/-- The intrinsic amplitude reconstructs exactly its own actual projected component. -/
theorem causalIntrinsicFrequencyCoefficient_smul_mode (z : causalUnitFrequency)
    (u : causalFrequencySpace 0) :
    causalIntrinsicFrequencyCoefficient z u • causalIntrinsicFrequencyMode z =
      causalIntrinsicFrequencyProjection z u :=
  causalFrequencyCoefficient_smul_mode 0 (causalUnitFrequencyCoordinate 0 z) u

/-- Intrinsic scalar extraction has sharp operator norm one. -/
theorem norm_causalIntrinsicFrequencyCoefficient (z : causalUnitFrequency) :
    ‖causalIntrinsicFrequencyCoefficient z‖ = 1 :=
  norm_causalFrequencyCoefficient 0 (causalUnitFrequencyCoordinate 0 z)

/-- Every actual closed-span vector has nonzero amplitudes at only countably many intrinsic rates. -/
theorem causalIntrinsicFrequencyCoefficient_countable_support (u : causalFrequencySpace 0) :
    (Function.support (fun z : causalUnitFrequency => causalIntrinsicFrequencyCoefficient z u)).Countable := by
  have hc := (causalFrequencyCoefficient_countable_support 0 u).image (causalUnitFrequencyRate 0)
  have hs : Function.support (fun z : causalUnitFrequency => causalIntrinsicFrequencyCoefficient z u) ⊆
      causalUnitFrequencyRate 0 '' Function.support (fun ω : ℝ => causalFrequencyCoefficient 0 ω u) := by
    intro z hz
    exact ⟨causalUnitFrequencyCoordinate 0 z, hz, causalUnitFrequencyRate_coordinate 0 z⟩
  exact Set.Countable.mono hs hc

/-- Every damping-chart presentation gives the same actual intrinsic mean operator. -/
theorem causalIntrinsicFrequencyMean_chart (b : ℝ) (z : causalUnitFrequency) (N : ℕ) :
    causalBoundedFrequencyMean b (causalUnitFrequencyCoordinate b z) N =
      causalIntrinsicFrequencyMean z N := by
  exact (congrArg (fun ω : ℝ => causalBoundedFrequencyMean b ω N) (coordinate_chart b z)).trans
    (causalBoundedFrequencyMean_rescale 0 b (causalUnitFrequencyCoordinate 0 z) N)

/-- The actual extracted component is intrinsic under canonical transport into every chart. -/
theorem causalIntrinsicFrequencyProjection_chart (b : ℝ) (z : causalUnitFrequency)
    (u : causalFrequencySpace 0) :
    causalFrequencyProjection b (causalUnitFrequencyCoordinate b z)
      (causalFrequencySpaceTransport 0 b u) =
        causalFrequencySpaceTransport 0 b (causalIntrinsicFrequencyProjection z u) := by
  exact (congrArg (fun ω : ℝ => causalFrequencyProjection b ω
    (causalFrequencySpaceTransport 0 b u)) (coordinate_chart b z)).trans
      (causalFrequencyProjection_transport 0 b (causalUnitFrequencyCoordinate 0 z) u)

/-- The scalar amplitude of an intrinsic rate is independent of the damping-chart presentation. -/
theorem causalIntrinsicFrequencyCoefficient_chart (b : ℝ) (z : causalUnitFrequency)
    (u : causalFrequencySpace 0) :
    causalFrequencyCoefficient b (causalUnitFrequencyCoordinate b z)
      (causalFrequencySpaceTransport 0 b u) = causalIntrinsicFrequencyCoefficient z u := by
  exact (congrArg (fun ω : ℝ => causalFrequencyCoefficient b ω
    (causalFrequencySpaceTransport 0 b u)) (coordinate_chart b z)).trans
      (causalFrequencyCoefficient_transport 0 b (causalUnitFrequencyCoordinate 0 z) u)

end
end RHTower.FokasLenells
