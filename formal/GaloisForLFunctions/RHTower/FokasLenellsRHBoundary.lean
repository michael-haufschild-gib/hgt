import GaloisForLFunctions.HTGeometry.FokasLenellsSquareIntegrableData
import GaloisForLFunctions.RHTower.FokasLenellsDirectResolvent

/-!
# The actual regularized Fokas–Lenells RH boundary problem

Every entry of the regularized jump perturbation belongs to L², so its rows
supply the specific inhomogeneous data for the constructed Cauchy inverse.
The signed Fourier cutoff has square equal to its negative. Consequently
the lower correction lies in the negative Hardy range and the corresponding
upper correction lies in the complementary range.

For each identity row, this file constructs the unique L² Hardy boundary
pair satisfying the actual regularized jump (3.31)–(3.35) of
arXiv:2607.19649v1 almost everywhere. The pointwise jump and the affine L²
equation are proved equivalent. All potentials are explicitly normalized
Schwartz data, and all positions and prescribed times are covered.
Analytic extension away from the contour, weighted Sobolev estimates, and
nonlinear PDE reconstruction remain separate steps.
-/

open MeasureTheory Complex Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Each entry of the actual jump perturbation, represented on the corpus's L² carrier. -/
def directJumpEntry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) : SoninL2 :=
  (globalSmall_regularJump_sub_one_memLp q t x i j).toLp
    (fun z => (regularJump (globalSmallScatteringPotential q) t x z-(1 : Matrix (Fin 2) (Fin 2) ℂ)) i j)

theorem directJumpEntry_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    (directJumpEntry q t x i j : ℝ → ℂ) =ᵐ[volume]
      (fun z => (regularJump (globalSmallScatteringPotential q) t x z-(1 : Matrix (Fin 2) (Fin 2) ℂ)) i j) :=
  (globalSmall_regularJump_sub_one_memLp q t x i j).coeFn_toLp

def directJumpRow (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  (directJumpEntry q t x i 0,directJumpEntry q t x i 1)

theorem directJumpRow_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    (fun z => (((directJumpRow q t x i).1 : ℝ → ℂ) z,((directJumpRow q t x i).2 : ℝ → ℂ) z)) =ᵐ[volume]
      (fun z => ((regularJump (globalSmallScatteringPotential q) t x z-1) i 0,
        (regularJump (globalSmallScatteringPotential q) t x z-1) i 1)) := by
  filter_upwards [directJumpEntry_ae q t x i 0,directJumpEntry_ae q t x i 1] with z h0 h1
  exact Prod.ext h0 h1

/-- The signed Cauchy operator squares to its negative, as required by the Plemelj projection convention. -/
theorem negativeCauchy_square (u : SoninL2) : negativeCauchy (negativeCauchy u) = -negativeCauchy u := by
  have hi := DFunLike.congr_fun (indicatorCutoff_idempotent (Set.Iio 0) measurableSet_Iio)
    (fourierUnitary.symm u)
  simp only [mul_apply_eq_comp] at hi
  change -fourierUnitary (indicatorCutoff (Set.Iio 0) measurableSet_Iio
    (fourierUnitary.symm (-fourierUnitary (indicatorCutoff (Set.Iio 0) measurableSet_Iio (fourierUnitary.symm u))))) =
    -(-fourierUnitary (indicatorCutoff (Set.Iio 0) measurableSet_Iio (fourierUnitary.symm u)))
  simp only [map_neg, fourierUnitary.symm_apply_apply, hi, neg_neg]

def boundaryCauchy : Boundary →L[ℂ] Boundary := negativeCauchy.prodMap negativeCauchy

theorem boundaryCauchy_square (u : Boundary) : boundaryCauchy (boundaryCauchy u) = -boundaryCauchy u :=
  Prod.ext (negativeCauchy_square u.1) (negativeCauchy_square u.2)

theorem boundaryCauchy_bound (u : Boundary) : ‖boundaryCauchy u‖ ≤ ‖u‖ := by
  exact max_le_max (negativeCauchy_bound u.1) (negativeCauchy_bound u.2)

/-- The inhomogeneous term is the Cauchy projection of the actual row of `R`, not arbitrary supplied data. -/
def directRHForcing (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  boundaryCauchy (directJumpRow q t x i)

def directLowerCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directSolution q t x (directRHForcing q t x i)

/-- The normalized lower boundary solves the actual regularized RH integral equation. -/
theorem directLowerCorrection_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    directLowerCorrection q t x i =
      boundaryCauchy (directJumpRow q t x i+directJumpPerturbation q t x (directLowerCorrection q t x i)) := by
  rw [map_add]
  exact (sub_eq_iff_eq_add).mp (directSolution_equation q t x (directRHForcing q t x i))

theorem directLowerCorrection_existsUnique (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ∃! u : Boundary, u = boundaryCauchy (directJumpRow q t x i+directJumpPerturbation q t x u) := by
  refine ⟨directLowerCorrection q t x i,directLowerCorrection_equation q t x i,?_⟩
  intro u hu
  have he : u-directCauchyOperator q t x u = directRHForcing q t x i := by
    rw [map_add] at hu
    exact sub_eq_iff_eq_add.mpr hu
  exact (directSolution_existsUnique q t x (directRHForcing q t x i)).unique he
    (directSolution_equation q t x (directRHForcing q t x i))

theorem directLowerCorrection_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directLowerCorrection q t x i‖ ≤ (9/5 : ℝ)*‖directJumpRow q t x i‖ := by
  exact (directSolution_bound q t x (directRHForcing q t x i)).trans
    (mul_le_mul_of_nonneg_left (boundaryCauchy_bound _) (by positivity))

/-- The constructed lower correction lies in the negative Hardy range. -/
theorem directLowerCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directLowerCorrection q t x i) = -directLowerCorrection q t x i := by
  have he := directLowerCorrection_equation q t x i
  calc
    _ = boundaryCauchy (boundaryCauchy (directJumpRow q t x i+
      directJumpPerturbation q t x (directLowerCorrection q t x i))) := congrArg boundaryCauchy he
    _ = -boundaryCauchy (directJumpRow q t x i+directJumpPerturbation q t x (directLowerCorrection q t x i)) :=
      boundaryCauchy_square _
    _ = _ := congrArg Neg.neg he.symm

/-- Adding the exact jump increment gives the upper correction, still an L² vector. -/
def directUpperCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directLowerCorrection q t x i+(directJumpRow q t x i+
    directJumpPerturbation q t x (directLowerCorrection q t x i))

/-- The upper correction belongs to the complementary Hardy range. -/
theorem directUpperCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directUpperCorrection q t x i) = 0 := by
  rw [directUpperCorrection, map_add, directLowerCorrection_hardy,
    ← directLowerCorrection_equation, neg_add_cancel]

/-- The boundary pair is uniquely determined by its Hardy conditions and the exact L² jump equation. -/
theorem directBoundaryPair_existsUnique (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ∃! uv : Boundary × Boundary,
      boundaryCauchy uv.1 = -uv.1 ∧ boundaryCauchy uv.2 = 0 ∧
      uv.2 = uv.1+(directJumpRow q t x i+directJumpPerturbation q t x uv.1) := by
  refine ⟨(directLowerCorrection q t x i,directUpperCorrection q t x i),
    ⟨directLowerCorrection_hardy q t x i,directUpperCorrection_hardy q t x i,rfl⟩,?_⟩
  intro uv huv
  have hfix : uv.1 = boundaryCauchy (directJumpRow q t x i+directJumpPerturbation q t x uv.1) := by
    have he := congrArg boundaryCauchy huv.2.2
    rw [map_add, huv.1, huv.2.1, neg_add_eq_sub] at he
    exact (sub_eq_zero.mp he.symm).symm
  have hu := (directLowerCorrection_existsUnique q t x i).unique hfix (directLowerCorrection_equation q t x i)
  apply Prod.ext hu
  simpa only [hu, directUpperCorrection] using huv.2.2

/-- Evaluation of an L² row is additive almost everywhere. -/
def boundaryRowValue (u : Boundary) (z : ℝ) : SpectralVector := ((u.1 : ℝ → ℂ) z,(u.2 : ℝ → ℂ) z)

theorem boundaryRowValue_add_ae (u v : Boundary) :
    boundaryRowValue (u+v) =ᵐ[volume] (fun z => boundaryRowValue u z+boundaryRowValue v z) := by
  filter_upwards [Lp.coeFn_add u.1 v.1,Lp.coeFn_add u.2 v.2] with z h0 h1
  exact Prod.ext h0 h1

/-- A normalized row differs from its L² correction by the corresponding identity row. -/
def normalizedBoundaryRow (i : Fin 2) (u : Boundary) (z : ℝ) : SpectralVector :=
  ((1 : Matrix (Fin 2) (Fin 2) ℂ) i 0,(1 : Matrix (Fin 2) (Fin 2) ℂ) i 1)+boundaryRowValue u z

/-- Almost-everywhere equality of normalized rows is exactly equality of their L² corrections. -/
theorem normalizedBoundaryRow_injective_ae (i : Fin 2) (u v : Boundary) :
    normalizedBoundaryRow i u =ᵐ[volume] normalizedBoundaryRow i v ↔ u = v := by
  constructor
  · intro he
    have hv : boundaryRowValue u =ᵐ[volume] boundaryRowValue v := by
      filter_upwards [he] with z hz
      exact add_left_cancel hz
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [hv] with z hz
      exact congrArg Prod.fst hz
    · apply Lp.ext
      filter_upwards [hv] with z hz
      exact congrArg Prod.snd hz
  · intro he
    rw [he]

/-- Adding the exact L² jump increment is right multiplication by the actual regularized jump almost everywhere. -/
theorem normalizedBoundaryRow_jump_increment (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (u : Boundary) :
    normalizedBoundaryRow i (u+(directJumpRow q t x i+directJumpPerturbation q t x u)) =ᵐ[volume]
      (fun z => matrixVector (regularJump (globalSmallScatteringPotential q) t x z).transpose
        (normalizedBoundaryRow i u z)) := by
  let r := directJumpRow q t x i
  let j := directJumpPerturbation q t x u
  filter_upwards [boundaryRowValue_add_ae u (r+j),boundaryRowValue_add_ae r j,
    directJumpRow_ae q t x i,directJumpPerturbation_ae q t x u] with z h1 h2 hr hj
  change boundaryRowValue r z = _ at hr
  change boundaryRowValue j z = _ at hj
  change ((1 : Matrix (Fin 2) (Fin 2) ℂ) i 0,(1 : Matrix (Fin 2) (Fin 2) ℂ) i 1)+
      boundaryRowValue (u+(r+j)) z =
    matrixVector (regularJump (globalSmallScatteringPotential q) t x z).transpose
      (((1 : Matrix (Fin 2) (Fin 2) ℂ) i 0,(1 : Matrix (Fin 2) (Fin 2) ℂ) i 1)+boundaryRowValue u z)
  rw [h1,h2,hr,hj]
  fin_cases i <;> apply Prod.ext <;>
    simp [boundaryRowValue, directSymbol, regularJump, jump, matrixVector,
      Matrix.mulVec, Matrix.one_apply, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring

/-- The pointwise RH jump and the L² affine equation are equivalent, not merely compatible. -/
theorem normalizedBoundaryRow_jump_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (u v : Boundary) :
    (normalizedBoundaryRow i v =ᵐ[volume]
      (fun z => matrixVector (regularJump (globalSmallScatteringPotential q) t x z).transpose
        (normalizedBoundaryRow i u z))) ↔
      v = u+(directJumpRow q t x i+directJumpPerturbation q t x u) := by
  have hj := normalizedBoundaryRow_jump_increment q t x i u
  constructor
  · intro he
    exact (normalizedBoundaryRow_injective_ae i _ _).mp (he.trans hj.symm)
  · intro he
    rw [he]
    exact hj

/-- The identity row plus the constructed lower or upper L² correction. -/
def directBoundaryRow (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (z : ℝ) : SpectralVector :=
  normalizedBoundaryRow i (if upper then directUpperCorrection q t x i else directLowerCorrection q t x i) z

/-- The constructed Hardy boundary pair obeys the paper's actual regularized jump almost everywhere. -/
theorem directBoundaryRow_jump (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    directBoundaryRow q t x i true =ᵐ[volume]
      (fun z => matrixVector (regularJump (globalSmallScatteringPotential q) t x z).transpose
        (directBoundaryRow q t x i false z)) :=
  normalizedBoundaryRow_jump_increment q t x i (directLowerCorrection q t x i)

/-- A unique L² Hardy boundary pair solves each row of the actual regularized Riemann–Hilbert jump. -/
theorem directHardyRHBoundary_existsUnique (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ∃! uv : Boundary × Boundary,
      boundaryCauchy uv.1 = -uv.1 ∧ boundaryCauchy uv.2 = 0 ∧
      normalizedBoundaryRow i uv.2 =ᵐ[volume]
        (fun z => matrixVector (regularJump (globalSmallScatteringPotential q) t x z).transpose
          (normalizedBoundaryRow i uv.1 z)) := by
  simpa only [normalizedBoundaryRow_jump_iff] using directBoundaryPair_existsUnique q t x i

end
end RHTower.FokasLenells
