import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMasterCurrent

/-! Actual differentiation of the literal squared theta cusp and its gradient energy. -/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMHorizon
noncomputable section

/-- The literal scalar eigenvalue has the original shifted physical value on both branches. -/
theorem scalar_physical_equation (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (scalar (center q)) z =
      (physicalRate q branch+1)*(physicalRate q branch+2)*scalar (center q) z := by
  rw [scalarLaplacian_eq _ z hz]
  change hyperbolicLaplacian (scalar (center q)) z = _
  have he := scalarCusp_hyperbolicLaplacian (center q) z hz
  change hyperbolicLaplacian (scalar (center q)) z = (center q^2-1/4)*scalar (center q) z at he
  rw [he]
  cases branch <;> dsimp [physicalRate,D4BMGlobalAngularResponse.center] <;> ring

/-- The original scalar half-square potential. -/
def fullSquarePotential (q : XiZeroCopy) (z : Point) : ℂ :=
  (1/2 : ℂ)*(scalar (center q) z*scalar (center q) z)

/-- The complete hyperbolic gradient energy of the literal scalar. -/
def fullGradientEnergy (q : XiZeroCopy) (z : Point) : ℂ :=
  (z 1 : ℂ)^2*(coordDeriv 0 (scalar (center q)) z^2+coordDeriv 1 (scalar (center q)) z^2)

private theorem scalar_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (n : ℕ) :
    ContDiffAt ℝ n (scalar (center q)) z := cuspLeg_contDiffAt .scalar (center q) n z hz

/-- Every finite jet of the original half-square potential exists. -/
theorem fullSquarePotential_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (n : ℕ) :
    ContDiffAt ℝ n (fullSquarePotential q) z :=
  contDiffAt_const.mul ((scalar_smooth q z hz n).mul (scalar_smooth q z hz n))

private theorem square_jet (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    ofField (fullSquarePotential q) z = (constant (1/2)).mul
      ((ofField (scalar (center q)) z).mul (ofField (scalar (center q)) z)) := by
  have hs : ContDiffAt ℝ 2 (scalar (center q)) z := by simpa using scalar_smooth q z hz 2
  unfold fullSquarePotential
  rw [ofField_mul contDiffAt_const (hs.mul hs),ofField_constant,ofField_mul hs hs]

private theorem square_first (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (j : Fin 2) :
    coordDeriv j (fullSquarePotential q) z = scalar (center q) z*coordDeriv j (scalar (center q)) z := by
  have h := congrArg (fun a => a.first j) (square_jet q z hz)
  simp only [ofField,ScalarTwoJet.mul,constant] at h
  linear_combination h

private theorem square_second (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (i j : Fin 2) :
    coordDeriv i (coordDeriv j (fullSquarePotential q)) z =
      coordDeriv i (scalar (center q)) z*coordDeriv j (scalar (center q)) z +
        scalar (center q) z*coordDeriv i (coordDeriv j (scalar (center q))) z := by
  have h := congrArg (fun a => a.second i j) (square_jet q z hz)
  simp only [ofField,ScalarTwoJet.mul,constant] at h
  linear_combination h

/-- The retained source covector is the actual coexact derivative of the half-square. -/
theorem fullSquarePotential_coexact (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (k : Fin 2) :
    coexact (fullSquarePotential q) k z = fullSquareCovector q k z := by
  fin_cases k <;> simp [coexact,fullSquareCovector,square_first q z hz]

/-- The squared scalar equation retains its complete gradient-energy forcing. -/
theorem fullSquarePotential_laplacian (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (fullSquarePotential q) z =
      2*(physicalRate q branch+1)*(physicalRate q branch+2)*fullSquarePotential q z+
        fullGradientEnergy q z := by
  have he := scalar_physical_equation q branch z hz
  rw [scalarLaplacian_eq _ z hz] at he ⊢
  rw [square_second q z hz,square_second q z hz]
  dsimp [fullSquarePotential,fullGradientEnergy]
  linear_combination scalar (center q) z*he

private theorem gradient_first (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (i : Fin 2) :
    coordDeriv i (fullGradientEnergy q) z =
      (if i = 1 then 2*(z 1 : ℂ) else 0)*
        (coordDeriv 0 (scalar (center q)) z^2+coordDeriv 1 (scalar (center q)) z^2)+
      (z 1 : ℂ)^2*(2*coordDeriv 0 (scalar (center q)) z*
          coordDeriv i (coordDeriv 0 (scalar (center q))) z+
        2*coordDeriv 1 (scalar (center q)) z*
          coordDeriv i (coordDeriv 1 (scalar (center q))) z) := by
  have hs : ContDiffAt ℝ 2 (scalar (center q)) z := by simpa using scalar_smooth q z hz 2
  have h0 := (coordDeriv_hasFDerivAt hs 0).differentiableAt.hasFDerivAt
  have h1 := (coordDeriv_hasFDerivAt hs 1).differentiableAt.hasFDerivAt
  have hY := Complex.ofRealCLM.hasFDerivAt.comp z
    ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)
  have hd := (hY.pow 2).mul ((h0.pow 2).add (h1.pow 2))
  change HasFDerivAt (fullGradientEnergy q) _ z at hd
  change fderiv ℝ (fullGradientEnergy q) z (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp [coordDeriv,smul_eq_mul] <;> ring

/-- The actual derivative of the complete gradient energy equals the original source K. -/
theorem fullGradientEnergy_coexact (q : XiZeroCopy) (branch : Bool) (z : Point)
    (hz : 0 < z 1) (k : Fin 2) :
    coexact (fullGradientEnergy q) k z = 2*fullGradientCovector q branch k z := by
  have he := scalar_physical_equation q branch z hz
  rw [scalarLaplacian_eq _ z hz] at he
  have hs : ContDiffAt ℝ 2 (scalar (center q)) z := by simpa using scalar_smooth q z hz 2
  have hc := coordDeriv_commute hs 1 0
  fin_cases k
  · change coordDeriv 1 (fullGradientEnergy q) z = 2*fullGradientCovector q branch 0 z
    rw [gradient_first q z hz, hc]
    norm_num [fullGradientCovector,D4BMQuadraticMixedSource.gradientCovector]
    linear_combination 2*coordDeriv 1 (scalar (center q)) z*he
  · change -coordDeriv 0 (fullGradientEnergy q) z = 2*fullGradientCovector q branch 1 z
    rw [gradient_first q z hz]
    norm_num [fullGradientCovector,D4BMQuadraticMixedSource.gradientCovector]
    ring

end
end RHTower.D4BMModularCore
