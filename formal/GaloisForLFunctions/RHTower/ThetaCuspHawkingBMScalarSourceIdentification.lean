import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularTwoCuspDecay
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarScalarQuadraticSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamSourceHarmonic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarLinearEinsteinEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticConservation

/-!
# Literal scalar source identification

The original physical scalar perturbation's second Taylor coefficient is identified in all
sixteen metric slots. The angular fields are the complete literal square, its actual Laplacian
and coordinate derivatives, and the trace-free Hessians of the square and the constructed
shift-two inverse. The scalar-gradient tensor is eliminated by the proved modular tensor identity.
Every lower Ricci slot is evaluated through the original connection tables. The factor one half
is matched to the nonlinear Einstein source's actual second amplitude derivative.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet
open scoped ContDiff
namespace RHTower.D4BMScalarSourceIdentification
open D4BMHorizon D4BMAngularTwo D4BMAngularTwoTensor D4BMModularCore D4BMScalarStream
open D4BMScalarLinearEquation
noncomputable section
set_option autoImplicit false

/-- Exact replacement of an affine harmonic coefficient by its angular differential action. -/
def affineRead (c : ℂ → ℂ) (F LF : ℂ) : ℂ := c 0*F+(c 1-c 0)*LF

/-- The scalar source's trace-free radial multiplier. -/
def tensorCoefficient (s r : ℂ) : ℂ := s^2*((s+1)^2-4*r^2)/(8*r^4)

/-- The original harmonic trace-free coefficient separates into the source and its shift-two inverse. -/
theorem ssSourceTF_factor (s r μ : ℂ) (hr : r ≠ 0) (hμ : 2-μ ≠ 0) :
    ssSourceTF s r μ = tensorCoefficient s r*(1+(s+1)*(s+2)/(2-μ)) := by
  unfold ssSourceTF tensorCoefficient
  field_simp
  ring

/-- All original source slots, before substituting the actual angular differential fields. -/
def sourceMatrix (s r y B F LF Fx Fy J0 J1 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let TT := affineRead (ssSourceTT s r) F LF
  let TR := ssSourceTR s r 0*F
  let RR := affineRead (ssSourceRR s r) F LF
  let tx := ssSourceT s r 0*Fx
  let ty := ssSourceT s r 0*Fy
  let rx := ssSourceR s r 0*Fx
  let ry := ssSourceR s r 0*Fy
  let L := affineRead (ssSourceL s r) F LF/y^2
  let A := tensorCoefficient s r*J0
  let C := tensorCoefficient s r*J1
  B^2 • !![TT,TR,tx,ty;TR,RR,rx,ry;tx,rx,L+A,C;ty,ry,C,L-A]

private def algebraSource (s r y B S Sx Sy Sxx Sxy : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  sourceMatrix s r y B (S^2) (2*(s+1)*(s+2)*S^2+2*y^2*(Sx^2+Sy^2))
    (2*S*Sx) (2*S*Sy)
    ((Sx^2-Sy^2)/2+2*S*Sxx-2*S*Sy/y-(s+1)*(s+2)*S^2/y^2)
    (Sx*Sy+2*S*Sxy+2*S*Sx/y)

private theorem algebra_source_0_0 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 0 0 := by
  rw [scalarJet_quadratic_einstein_0_0 hr hy hf]
  change _ = B^2*(affineRead (ssSourceTT s r) (S^2) (2*(s+1)*(s+2)*S^2+2*y^2*(Sx^2+Sy^2)))
  unfold affineRead ssSourceTT
  field_simp
  ring

private theorem algebra_source_0_1 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 0 1 := by
  rw [scalarJet_quadratic_einstein_0_1 hr hy hf]
  change _ = B^2*(ssSourceTR s r 0*(S^2))
  unfold ssSourceTR
  field_simp
  ring

private theorem algebra_source_0_2 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 0 2 := by
  rw [scalarJet_quadratic_einstein_0_2 hr hy hf]
  change _ = B^2*(ssSourceT s r 0*(2*S*Sx))
  unfold ssSourceT
  field_simp
  ring

private theorem algebra_source_0_3 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 0 3 := by
  rw [scalarJet_quadratic_einstein_0_3 hr hy hf]
  change _ = B^2*(ssSourceT s r 0*(2*S*Sy))
  unfold ssSourceT
  field_simp
  ring

private theorem algebra_source_1_1 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 1 1 := by
  rw [scalarJet_quadratic_einstein_1_1 hr hy hf]
  change _ = B^2*(affineRead (ssSourceRR s r) (S^2) (2*(s+1)*(s+2)*S^2+2*y^2*(Sx^2+Sy^2)))
  unfold affineRead ssSourceRR
  field_simp
  ring

private theorem algebra_source_1_2 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 1 2 := by
  rw [scalarJet_quadratic_einstein_1_2 hr hy hf]
  change _ = B^2*(ssSourceR s r 0*(2*S*Sx))
  unfold ssSourceR
  field_simp
  ring

private theorem algebra_source_1_3 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 1 3 := by
  rw [scalarJet_quadratic_einstein_1_3 hr hy hf]
  change _ = B^2*(ssSourceR s r 0*(2*S*Sy))
  unfold ssSourceR
  field_simp
  ring

private theorem algebra_source_2_2 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 2 2 := by
  rw [scalarJet_quadratic_einstein_2_2 hr hy hf]
  change _ = B^2*(affineRead (ssSourceL s r) (S^2) (2*(s+1)*(s+2)*S^2+2*y^2*(Sx^2+Sy^2))/y^2+tensorCoefficient s r*((Sx^2-Sy^2)/2+2*S*Sxx-2*S*Sy/y-(s+1)*(s+2)*S^2/y^2))
  unfold affineRead ssSourceL tensorCoefficient
  field_simp
  ring

private theorem algebra_source_2_3 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 2 3 := by
  rw [scalarJet_quadratic_einstein_2_3 hr hy hf]
  change _ = B^2*(tensorCoefficient s r*(Sx*Sy+2*S*Sxy+2*S*Sx/y))
  unfold tensorCoefficient
  field_simp
  ring

private theorem algebra_source_3_3 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3/2 =
      algebraSource s r y B S Sx Sy Sxx Sxy 3 3 := by
  rw [scalarJet_quadratic_einstein_3_3 hr hy hf]
  change _ = B^2*(affineRead (ssSourceL s r) (S^2) (2*(s+1)*(s+2)*S^2+2*y^2*(Sx^2+Sy^2))/y^2-tensorCoefficient s r*((Sx^2-Sy^2)/2+2*S*Sxx-2*S*Sy/y-(s+1)*(s+2)*S^2/y^2))
  unfold affineRead ssSourceL tensorCoefficient
  field_simp
  ring

private theorem quadratic_ricci_symm_0_1 {s r y B S Sx Sy Sxx Sxy : ℂ} (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 =
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [scalarJet_quadratic_ricci_0_1 hr hy hf]
  simp only [Quadratic.ricci, Fin.sum_univ_four]
  simp only [hd.quadratic_curvature_eq, Fin.sum_univ_four, Fin.isValue, Fin.reduceEq,
    if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

private theorem quadratic_ricci_symm_0_2 {s r y B S Sx Sy Sxx Sxy : ℂ} (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 =
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Quadratic.ricci, Fin.sum_univ_four]
  simp only [hd.quadratic_curvature_eq, Fin.sum_univ_four, Fin.isValue, Fin.reduceEq,
    if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

private theorem quadratic_ricci_symm_0_3 {s r y B S Sx Sy Sxx Sxy : ℂ} (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 =
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Quadratic.ricci, Fin.sum_univ_four]
  simp only [hd.quadratic_curvature_eq, Fin.sum_univ_four, Fin.isValue, Fin.reduceEq,
    if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

private theorem quadratic_ricci_symm_1_2 {s r y B S Sx Sy Sxx Sxy : ℂ} (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 =
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [scalarJet_quadratic_ricci_1_2 hr hy hf]
  simp only [Quadratic.ricci, Fin.sum_univ_four]
  simp only [hd.quadratic_curvature_eq, Fin.sum_univ_four, Fin.isValue, Fin.reduceEq,
    if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

private theorem quadratic_ricci_symm_1_3 {s r y B S Sx Sy Sxx Sxy : ℂ} (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 =
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [scalarJet_quadratic_ricci_1_3 hr hy hf]
  simp only [Quadratic.ricci, Fin.sum_univ_four]
  simp only [hd.quadratic_curvature_eq, Fin.sum_univ_four, Fin.isValue, Fin.reduceEq,
    if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

private theorem quadratic_ricci_symm_2_3 {s r y B S Sx Sy Sxx Sxy : ℂ} (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 =
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Quadratic.ricci, Fin.sum_univ_four]
  simp only [hd.quadratic_curvature_eq, Fin.sum_univ_four, Fin.isValue, Fin.reduceEq,
    if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

/-- Symmetry is derived from every original Ricci slot, including the six lower slots. -/
theorem quadratic_einstein_symm (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) (i j : Fin 4) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) i j =
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) j i := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf]
  have hm : (D4BMBackground.jet r y).metric i j = (D4BMBackground.jet r y).metric j i := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [hm]
  congr 1
  fin_cases i <;> fin_cases j
  · rfl
  · exact quadratic_ricci_symm_0_1 hr hy hf
  · exact quadratic_ricci_symm_0_2 hr hy hf
  · exact quadratic_ricci_symm_0_3 hr hy hf
  · exact (quadratic_ricci_symm_0_1 hr hy hf).symm
  · rfl
  · exact quadratic_ricci_symm_1_2 hr hy hf
  · exact quadratic_ricci_symm_1_3 hr hy hf
  · exact (quadratic_ricci_symm_0_2 hr hy hf).symm
  · exact (quadratic_ricci_symm_1_2 hr hy hf).symm
  · rfl
  · exact quadratic_ricci_symm_2_3 hr hy hf
  · exact (quadratic_ricci_symm_0_3 hr hy hf).symm
  · exact (quadratic_ricci_symm_1_3 hr hy hf).symm
  · exact (quadratic_ricci_symm_2_3 hr hy hf).symm
  · rfl

private theorem algebra_source (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    (fun i j => Quadratic.einstein (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) i j/2) =
      algebraSource s r y B S Sx Sy Sxx Sxy := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact algebra_source_0_0 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact algebra_source_0_1 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact algebra_source_0_2 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact algebra_source_0_3 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact (congrArg (fun z : ℂ => z/2)
      (quadratic_einstein_symm s r y B S Sx Sy Sxx Sxy hr hy hf 1 0)).trans
        (algebra_source_0_1 s r y B S Sx Sy Sxx Sxy hr hy hf)
  · exact algebra_source_1_1 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact algebra_source_1_2 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact algebra_source_1_3 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact (congrArg (fun z : ℂ => z/2)
      (quadratic_einstein_symm s r y B S Sx Sy Sxx Sxy hr hy hf 2 0)).trans
        (algebra_source_0_2 s r y B S Sx Sy Sxx Sxy hr hy hf)
  · exact (congrArg (fun z : ℂ => z/2)
      (quadratic_einstein_symm s r y B S Sx Sy Sxx Sxy hr hy hf 2 1)).trans
        (algebra_source_1_2 s r y B S Sx Sy Sxx Sxy hr hy hf)
  · exact algebra_source_2_2 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact algebra_source_2_3 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact (congrArg (fun z : ℂ => z/2)
      (quadratic_einstein_symm s r y B S Sx Sy Sxx Sxy hr hy hf 3 0)).trans
        (algebra_source_0_3 s r y B S Sx Sy Sxx Sxy hr hy hf)
  · exact (congrArg (fun z : ℂ => z/2)
      (quadratic_einstein_symm s r y B S Sx Sy Sxx Sxy hr hy hf 3 1)).trans
        (algebra_source_1_3 s r y B S Sx Sy Sxx Sxy hr hy hf)
  · exact (congrArg (fun z : ℂ => z/2)
      (quadratic_einstein_symm s r y B S Sx Sy Sxx Sxy hr hy hf 3 2)).trans
        (algebra_source_2_3 s r y B S Sx Sy Sxx Sxy hr hy hf)
  · exact algebra_source_3_3 s r y B S Sx Sy Sxx Sxy hr hy hf

/-- The complete literal squared source. -/
def squareSource (q : XiZeroCopy) (z : Point) : ℂ := source q z^2

/-- Both physical branches have the original angular eigenvalue. -/
theorem eigenvalue_physicalRate (q : XiZeroCopy) (branch : Bool) :
    eigenvalue q = (physicalRate q branch+1)*(physicalRate q branch+2) := by
  cases branch <;> dsimp [eigenvalue,D4BMLiteralCusp.scalarQ,
    physicalRate,D4BMGlobalAngularResponse.center] <;> ring

private theorem square_jet (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    ofField (squareSource q) z = (ofField (source q) z).mul (ofField (source q) z) := by
  have hs : ContDiffAt ℝ 2 (source q) z := D4BMLiteralCusp.scalar_contDiffAt _ 2 z hz
  have he : squareSource q = (fun z => source q z*source q z) := funext fun z => pow_two _
  rw [he]
  exact ofField_mul hs hs

/-- The squared source's actual first coordinate derivative. -/
theorem squareSource_first (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (i : Fin 2) :
    coordDeriv i (squareSource q) z = 2*source q z*coordDeriv i (source q) z := by
  have h := congrArg (fun a => a.first i) (square_jet q z hz)
  simp only [ofField,ScalarTwoJet.mul] at h
  linear_combination h

/-- The squared source's actual ordered second coordinate derivative. -/
theorem squareSource_second (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (i j : Fin 2) :
    coordDeriv i (coordDeriv j (squareSource q)) z =
      2*coordDeriv i (source q) z*coordDeriv j (source q) z+
      2*source q z*coordDeriv i (coordDeriv j (source q)) z := by
  have h := congrArg (fun a => a.second i j) (square_jet q z hz)
  simp only [ofField,ScalarTwoJet.mul] at h
  linear_combination h

/-- The full square is not assumed harmonic: its Laplacian retains gradient energy. -/
theorem squareSource_laplacian (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (squareSource q) z =
      2*(physicalRate q branch+1)*(physicalRate q branch+2)*source q z^2+
      2*(z 1:ℂ)^2*(coordDeriv 0 (source q) z^2+coordDeriv 1 (source q) z^2) := by
  have he := scalar_physical_equation q branch z hz
  change scalarLaplacian (source q) z = (physicalRate q branch+1)*(physicalRate q branch+2)*source q z at he
  rw [scalarLaplacian_eq _ z hz] at he ⊢
  rw [squareSource_second q z hz,squareSource_second q z hz]
  linear_combination 2*source q z*he

private theorem hessian_00 (F : Field) (z : Point) (hz : 0 < z 1) :
    hessianTensor F z 0 0 =
      (coordDeriv 0 (coordDeriv 0 F) z-coordDeriv 1 (coordDeriv 1 F) z)/2-
      coordDeriv 1 F z/(z 1:ℂ) := by
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  simp only [hessianTensor,covariant_eq _ z hz,scalarLaplacian_eq _ z hz]
  simp [covariantFormula,D4BMHorizon.metric]
  field_simp
  ring

private theorem hessian_01 (F : Field) (z : Point) (hz : 0 < z 1) :
    hessianTensor F z 0 1 = coordDeriv 0 (coordDeriv 1 F) z+
      coordDeriv 0 F z/(z 1:ℂ) := by
  simp [hessianTensor,covariant_eq _ z hz,covariantFormula,D4BMHorizon.metric,div_eq_mul_inv,mul_comm]

private theorem gradient_00 (F : Field) (z : Point) (hz : 0 < z 1) :
    gradientTensor F z 0 0 = (coordDeriv 0 F z^2-coordDeriv 1 F z^2)/2 := by
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  simp only [gradientTensor,metric_inverse z hz]
  simp [D4BMHorizon.metric,Fin.sum_univ_two]
  field_simp
  ring

private theorem gradient_01 (F : Field) (z : Point) :
    gradientTensor F z 0 1 = coordDeriv 0 F z*coordDeriv 1 F z := by
  simp [gradientTensor,D4BMHorizon.metric]

/-- Actual diagonal tensor source; the constructed inverse removes the original gradient tensor. -/
theorem squareSource_tensor_00 (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    hessianTensor (squareSource q) z 0 0+eigenvalue q*hessianTensor (coordinateResponse q) z 0 0 =
      (coordDeriv 0 (source q) z^2-coordDeriv 1 (source q) z^2)/2+
      2*source q z*coordDeriv 0 (coordDeriv 0 (source q)) z-
      2*source q z*coordDeriv 1 (source q) z/(z 1:ℂ)-
      (physicalRate q branch+1)*(physicalRate q branch+2)*source q z^2/(z 1:ℂ)^2 := by
  have hzero := congrArg (fun T => T 0 0) (D4BMAngularTwoCuspDecay.actual_tensor_zero q z hz)
  change gradientTensor (source q) z 0 0+eigenvalue q*hessianTensor (coordinateResponse q) z 0 0 = 0 at hzero
  rw [gradient_00 _ z hz] at hzero
  rw [hessian_00 _ z hz,squareSource_second q z hz,squareSource_second q z hz,squareSource_first q z hz]
  have he := scalar_physical_equation q branch z hz
  change scalarLaplacian (source q) z = (physicalRate q branch+1)*(physicalRate q branch+2)*source q z at he
  rw [scalarLaplacian_eq _ z hz] at he
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  field_simp
  linear_combination 2*(z 1:ℂ)^2*hzero-2*source q z*he

/-- Actual off-diagonal tensor source, including its connection contribution. -/
theorem squareSource_tensor_01 (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    hessianTensor (squareSource q) z 0 1+eigenvalue q*hessianTensor (coordinateResponse q) z 0 1 =
      coordDeriv 0 (source q) z*coordDeriv 1 (source q) z+
      2*source q z*coordDeriv 0 (coordDeriv 1 (source q)) z+
      2*source q z*coordDeriv 0 (source q) z/(z 1:ℂ) := by
  have hzero := congrArg (fun T => T 0 1) (D4BMAngularTwoCuspDecay.actual_tensor_zero q z hz)
  change gradientTensor (source q) z 0 1+eigenvalue q*hessianTensor (coordinateResponse q) z 0 1 = 0 at hzero
  rw [gradient_01] at hzero
  rw [hessian_01 _ z hz,squareSource_second q z hz,squareSource_first q z hz]
  linear_combination hzero

/-- The actual nonseparated scalar source, with both angular tensors and full square Laplacian. -/
def literalSourceTensor (q : XiZeroCopy) (branch : Bool) (r B : ℂ) (z : Point) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  sourceMatrix (physicalRate q branch) r (z 1) B (squareSource q z)
    (scalarLaplacian (squareSource q) z)
    (coordDeriv 0 (squareSource q) z) (coordDeriv 1 (squareSource q) z)
    (hessianTensor (squareSource q) z 0 0+eigenvalue q*hessianTensor (coordinateResponse q) z 0 0)
    (hessianTensor (squareSource q) z 0 1+eigenvalue q*hessianTensor (coordinateResponse q) z 0 1)

/-- Every original scalar-jet source component equals its constructed angular differential action. -/
theorem literal_scalarJet_source (q : XiZeroCopy) (branch : Bool) (r B : ℂ)
    (z : Point) (hz : 0 < z 1) (hr : r ≠ 0) (hf : r^2-1 ≠ 0) :
    (fun i j => Quadratic.einstein (D4BMBackground.jet r (z 1))
      (scalarJet (physicalRate q branch) r (z 1) B (source q z)
        (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z)
        (coordDeriv 0 (coordDeriv 0 (source q)) z)
        (coordDeriv 0 (coordDeriv 1 (source q)) z)) i j/2) =
      literalSourceTensor q branch r B z := by
  rw [algebra_source _ _ _ _ _ _ _ _ _ hr (Complex.ofReal_ne_zero.mpr hz.ne') hf]
  simp only [literalSourceTensor,squareSource_laplacian q branch z hz,
    squareSource_first q z hz,squareSource_tensor_00 q branch z hz,squareSource_tensor_01 q z hz]
  rfl

private theorem ofField_congr_germ {f g : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (h : f =ᶠ[nhds x] g) : ofField f x = ofField g x := by
  have hD : fderiv ℝ f =ᶠ[nhds x] fderiv ℝ g := h.fderiv
  have hd (k : Fin 4) : coordDeriv k f =ᶠ[nhds x] coordDeriv k g := by
    filter_upwards [hD] with y hy
    exact congrArg (fun L => L (Pi.single k 1)) hy
  ext i j
  · exact h.self_of_nhds
  · change fderiv ℝ f x (Pi.single i 1) = fderiv ℝ g x (Pi.single i 1)
    rw [h.fderiv_eq]
  · change fderiv ℝ (coordDeriv j f) x (Pi.single i 1) =
      fderiv ℝ (coordDeriv j g) x (Pi.single i 1)
    rw [(hd j).fderiv_eq]

private def assemble (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) :
    CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k,
    fun k l i j => (J i j).second k l⟩

/-- The original physical scalar perturbation has the actual jet used in the source formula. -/
theorem physical_scalar_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    D4BMMetricReconstruction.ofMetricField (D4BMLiteralCusp.physicalPerturbation q branch a 0) p.val =
    D4BMMetricReconstruction.ofMetricField
      (D4BMFundamentalScalarMetric.field (physicalRate q branch) a (source q)) p.val := by
  have hparam : D4BMLiteralCusp.scalarQ (D4BMGlobalAngularResponse.center q) =
      D4BMFundamentalScalarMetric.harmonicParameter (physicalRate q branch) := by
    have he := eigenvalue_physicalRate q branch
    unfold eigenvalue at he
    unfold D4BMFundamentalScalarMetric.harmonicParameter
    linear_combination -he
  change assemble _ = assemble _
  congr 1
  funext i j
  apply ofField_congr_germ
  have hO : IsOpen {x : Fin 4 → ℝ | 1 < x 1 ∧ 0 < x 3} :=
    (isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt continuous_const (continuous_apply 3))
  filter_upwards [hO.mem_nhds p.property] with x hx
  change D4BMFundamentalMetric.perturbation (Complex.I*physicalRate q branch)
    (D4BMLiteralCusp.scalarQ (D4BMGlobalAngularResponse.center q)) a 0
    (source q) (D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q)) x i j = _
  rw [hparam]
  exact congrArg (fun M => M i j) (D4BMFundamentalScalarMetric.reconstruction_eq
    (physicalRate q branch) a (source q) _ ⟨x,hx⟩)

/-- Unconditional identification of all sixteen original physical scalar-source components. -/
theorem physical_scalar_source (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    D4BMQuadraticConservation.physicalQuadraticSource q branch a 0 p.val =
      literalSourceTensor q branch (p.val 1)
        (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) a p.val)
        (D4BMMetricReconstruction.angularPoint p.val) := by
  have hr : (p.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1:ℂ)^2-1 ≠ 0 := by
    have h : (p.val 1)^2-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have hdet : (D4BMBackground.actualJet p).metric.det ≠ 0 := D4BMBackground.exterior_metric_det_ne_zero p
  have hj := field_jet (physicalRate q branch) a (source q) p
    (D4BMLiteralCusp.scalar_contDiffAt _ 2 _ p.property.2)
    (scalar_physical_equation q branch _ p.property.2)
  funext i j
  change (1/2:ℂ)*ComplexCoordinateMetricTwoJet.secondVariation
    (ComplexCoordinateMetricTwoJet.toSpace (D4BMBackground.actualJet p)) i j
    (ComplexCoordinateMetricTwoJet.toSpace (D4BMMetricReconstruction.ofMetricField
      (D4BMLiteralCusp.physicalPerturbation q branch a 0) p.val))
    (ComplexCoordinateMetricTwoJet.toSpace (D4BMMetricReconstruction.ofMetricField
      (D4BMLiteralCusp.physicalPerturbation q branch a 0) p.val)) = _
  rw [← Quadratic.einstein_eq_secondVariation _ _ hdet i j,physical_scalar_jet,hj,D4BMBackground.actualJet_eq]
  have he := congrArg (fun T => T i j) (literal_scalarJet_source q branch (p.val 1)
    (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) a p.val)
    (D4BMMetricReconstruction.angularPoint p.val) p.property.2 hr hf)
  have hycoord : D4BMMetricReconstruction.angularPoint p.val 1 = p.val 3 := rfl
  rw [hycoord] at he
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using he

/-- The literal source formula is the second Taylor coefficient of the original nonlinear metric source. -/
theorem physical_scalar_source_coefficient (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    iteratedDeriv 2 (D4BMActualMetricSource.source p
      (D4BMLiteralCusp.physicalPerturbation q branch a 0) i j) 0/2 =
      literalSourceTensor q branch (p.val 1)
        (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) a p.val)
        (D4BMMetricReconstruction.angularPoint p.val) i j := by
  rw [← D4BMQuadraticConservation.physicalQuadraticSource_eq p q branch a 0 i j,
    physical_scalar_source]

end
end RHTower.D4BMScalarSourceIdentification
