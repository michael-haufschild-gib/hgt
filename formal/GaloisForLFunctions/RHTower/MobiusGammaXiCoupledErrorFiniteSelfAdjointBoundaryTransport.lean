import GaloisForLFunctions.RHTower.MobiusGammaXiCoupledErrorSingularGraphGlobalWall
import GaloisForLFunctions.RHTower.BaezDuarteDetectorIndependence
import GaloisForLFunctions.HTGeometry.CompoundOperatorOrder
import GaloisForLFunctions.HTGeometry.FiniteMatrixSpectralDensityDecay

/-!
# G-CE finite self-adjoint realization and source boundary transport

The literal Suzuki--Weil Friedrichs operator, its form Hilbert space, and its deficiency indices
are already formalized elsewhere in the corpus. This module closes the different source-defined
finite-head problem exposed by the coupled-error wall.

For each Hardy Cauchy head it constructs the canonical minimum-energy positive completion. The
completion is a finite positive self-adjoint operator, not an arbitrary positive cap: its scalar
corner is exactly the Schur-complement capacity of the actual Gamma--Xi source response.

The heads are canonical grids `i/(N+1)` containing both wall origin and collapsing node
`1/(N+1)`. Two-node saturation and global singular graph wall squeeze target capacity to exact
graph energy `4+|d|^(2 : ℕ)`. Fixed-head source convergence is then upgraded by one strictly cofinal
diagonal selection. Along that same schedule:

* source finite self-adjoint operators converge in operator norm to singular target heads;
* complete moving boundary column converges in `ell^(1 : ℕ)`, hence at every moving node;
* actual minimum completion budgets converge to `4+|d|^(2 : ℕ)`.

Thus boundary transport preserves singular Gamma--Xi debt instead of erasing it through an
uncontrolled completion. No RH assumption or abstract source-convergence premise is used.
-/

open Complex Filter Set Topology Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace RHTower


def finiteHardyBoundaryColumn {n : ℕ} (b : Fin n → ℂ) : Matrix (Fin n) Unit ℂ :=
  fun i _ => star (b i)

def finiteHardyMinimumCompletion {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (_hK : K.PosDef)
    (b : Fin n → ℂ) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ := by
  letI : Invertible K := _hK.isUnit.invertible
  let B := finiteHardyBoundaryColumn b
  exact Matrix.fromBlocks K B Bᴴ (Bᴴ * K⁻¹ * B)

def finiteHardyMinimumCapacity {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (_hK : K.PosDef)
    (b : Fin n → ℂ) : Matrix Unit Unit ℂ := by
  letI : Invertible K := _hK.isUnit.invertible
  let B := finiteHardyBoundaryColumn b
  exact Bᴴ * K⁻¹ * B

theorem finiteHardyMinimumCapacity_pos {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (hK : K.PosDef)
    (b : Fin n → ℂ) : (finiteHardyMinimumCapacity K hK b).PosSemidef := by
  letI : Invertible K := hK.isUnit.invertible
  let B := finiteHardyBoundaryColumn b
  change (Bᴴ * K⁻¹ * B).PosSemidef
  exact hK.inv.posSemidef.conjTranspose_mul_mul_same B

def finiteHardyMinimumBudget {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (hK : K.PosDef)
    (b : Fin n → ℂ) : ℝ := (finiteHardyMinimumCapacity K hK b () ()).re

theorem finiteHardyMinimumCapacity_entry_eq_budget {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K.PosDef) (b : Fin n → ℂ) :
    finiteHardyMinimumCapacity K hK b () () = (finiteHardyMinimumBudget K hK b : ℂ) := by
  have hherm := (finiteHardyMinimumCapacity_pos K hK b).isHermitian
  have hdiag := congrFun (congrFun hherm.eq ()) ()
  simp only [Matrix.conjTranspose_apply] at hdiag
  apply Complex.ext
  · rfl
  · have him : (finiteHardyMinimumCapacity K hK b () ()).im = 0 := by
      have := congrArg Complex.im hdiag
      have h : -(finiteHardyMinimumCapacity K hK b () ()).im =
          (finiteHardyMinimumCapacity K hK b () ()).im := by simpa using this
      linarith
    simp [finiteHardyMinimumBudget, him]

theorem continuous_finiteHardyMinimumCompletion {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K.PosDef) : Continuous (finiteHardyMinimumCompletion K hK) := by
  unfold finiteHardyMinimumCompletion finiteHardyBoundaryColumn
  fun_prop

theorem tendsto_finiteHardyMinimumCompletion {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K.PosDef) {α : Type*} {l : Filter α} {b : α → Fin n → ℂ} {b0 : Fin n → ℂ}
    (hb : ∀ i, Tendsto (fun a => b a i) l (𝓝 (b0 i))) :
    Tendsto (fun a => finiteHardyMinimumCompletion K hK (b a)) l (𝓝 (finiteHardyMinimumCompletion K hK b0)) := by
  apply (continuous_finiteHardyMinimumCompletion K hK).continuousAt.tendsto.comp
  rw [tendsto_pi_nhds]
  exact hb

theorem finiteHardyMinimumBudget_le_of_block_pos {n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℂ) (hK : K.PosDef)
    (b : Fin n → ℂ) (q : ℝ)
    (hpos : (Matrix.fromBlocks K (finiteHardyBoundaryColumn b)
      (finiteHardyBoundaryColumn b)ᴴ (Matrix.of fun _ _ : Unit => (q : ℂ))).PosSemidef) :
    finiteHardyMinimumBudget K hK b ≤ q := by
  letI : Invertible K := hK.isUnit.invertible
  let B := finiteHardyBoundaryColumn b
  have hschur := (Matrix.PosDef.fromBlocks₁₁ B
    (Matrix.of fun _ _ : Unit => (q : ℂ)) hK).mp hpos
  have hquad := hschur.dotProduct_mulVec_nonneg (fun _ : Unit => (1 : ℂ))
  rw [RCLike.le_iff_re_im] at hquad
  have hre := hquad.1
  simp only [dotProduct, Matrix.mulVec, Finset.univ_unique,
    Finset.sum_singleton, Pi.star_apply, star_one, one_mul] at hre
  have hcap := finiteHardyMinimumCapacity_entry_eq_budget K hK b
  change finiteHardyMinimumCapacity K hK b () () = (finiteHardyMinimumBudget K hK b : ℂ) at hcap
  change (Bᴴ * K⁻¹ * B) () () = (finiteHardyMinimumBudget K hK b : ℂ) at hcap
  have hre' : 0 ≤ ((q : ℂ) - (Bᴴ * K⁻¹ * B) () ()).re := by
    simpa using hre
  rw [hcap] at hre'
  norm_num at hre'
  exact hre'

theorem finiteHardyMinimumCompletion_pos {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (hK : K.PosDef)
    (b : Fin n → ℂ) : (finiteHardyMinimumCompletion K hK b).PosSemidef := by
  letI : Invertible K := hK.isUnit.invertible
  let B := finiteHardyBoundaryColumn b
  change (Matrix.fromBlocks K B Bᴴ (Bᴴ * K⁻¹ * B)).PosSemidef
  rw [Matrix.PosDef.fromBlocks₁₁ B (Bᴴ * K⁻¹ * B) hK]
  simpa using (Matrix.PosSemidef.zero :
    (0 : Matrix Unit Unit ℂ).PosSemidef)

def mobiusGammaXiCoupledErrorHeadNodes (N : ℕ) (i : Fin (N + 2)) : ℂ :=
  (((i : ℕ) : ℝ) / (N + 1 : ℝ) : ℝ)

theorem mobiusGammaXiCoupledErrorHeadNodes_re (N : ℕ) (i : Fin (N + 2)) : 0 ≤ (mobiusGammaXiCoupledErrorHeadNodes N i).re := by
  simp only [mobiusGammaXiCoupledErrorHeadNodes, ofReal_re]
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem mobiusGammaXiCoupledErrorHeadNodes_inj (N : ℕ) : Function.Injective (mobiusGammaXiCoupledErrorHeadNodes N) := by
  intro i j hij
  have hreal := congrArg Complex.re hij
  simp only [mobiusGammaXiCoupledErrorHeadNodes, ofReal_re] at hreal
  have hden : (N + 1 : ℝ) ≠ 0 := by positivity
  have hcast : (i : ℝ) = (j : ℝ) := by
    exact (div_left_inj' hden).mp hreal
  exact Fin.ext (by exact_mod_cast hcast)

def mobiusGammaXiCoupledErrorHeadGram (N : ℕ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ :=
  fun i j => mobiusCriticalUniversalHardyKernel (mobiusGammaXiCoupledErrorHeadNodes N i) (mobiusGammaXiCoupledErrorHeadNodes N j)

theorem mobiusGammaXiCoupledErrorHeadGram_posDef (N : ℕ) : (mobiusGammaXiCoupledErrorHeadGram N).PosDef := by
  let w : Fin (N + 2) → ℂ := fun i => mobiusGammaXiCoupledErrorHeadNodes N i + 1 / 2
  have hw : ∀ i, 0 < (w i).re := by
    intro i
    have hi := mobiusGammaXiCoupledErrorHeadNodes_re N i
    dsimp [w]
    norm_num
    linarith
  have hinj : Function.Injective w := by
    intro i j hij
    apply mobiusGammaXiCoupledErrorHeadNodes_inj N
    dsimp [w] at hij
    exact add_right_cancel hij
  have h := rightHalfPlaneHardyCauchyGram_posDef w hw hinj
  convert h using 1
  ext i j
  simp [mobiusGammaXiCoupledErrorHeadGram, rightHalfPlaneHardyCauchyGram, w, mobiusGammaXiCoupledErrorHeadNodes,
    mobiusCriticalUniversalHardyKernel]
  ring

def mobiusGammaXiCoupledErrorSingularResponse (N : ℕ) (i : Fin (N + 2)) : ℂ :=
  mobiusCriticalUniversalFisherScore (mobiusGammaXiCoupledErrorHeadNodes N i) +
    mobiusGammaXiCoupledErrorCriticalCoefficient *
      mobiusCriticalUniversalHardyMassProfile (mobiusGammaXiCoupledErrorHeadNodes N i)

def mobiusGammaXiCoupledErrorSourceResponse (j N : ℕ) (i : Fin (N + 2)) : ℂ :=
  mobiusCriticalUniversalFisherScore (mobiusGammaXiCoupledErrorHeadNodes N i) +
    mobiusGammaXiClockNormalizedTrueComplementDefect
      (soninMobiusCriticalSigmaSequence j)
      (((i : ℕ) : ℝ) / (N + 1 : ℝ))
      (soninMobiusCriticalSigmaSequence_gt_one j)

theorem tendsto_mobiusGammaXiCoupledErrorSourceResponse (N : ℕ) (i : Fin (N + 2)) :
    Tendsto (fun j => mobiusGammaXiCoupledErrorSourceResponse j N i) atTop
      (𝓝 (mobiusGammaXiCoupledErrorSingularResponse N i)) := by
  have hu : 0 ≤ (((i : ℕ) : ℝ) / (N + 1 : ℝ)) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have h := tendsto_mobiusGammaXiClockNormalizedComplementDefect hu
  have hconst : Tendsto
      (fun _ : ℕ => mobiusCriticalUniversalFisherScore (mobiusGammaXiCoupledErrorHeadNodes N i))
      atTop (𝓝 (mobiusCriticalUniversalFisherScore (mobiusGammaXiCoupledErrorHeadNodes N i))) :=
    tendsto_const_nhds
  have hadd := hconst.add h
  simpa [mobiusGammaXiCoupledErrorSourceResponse, mobiusGammaXiCoupledErrorSingularResponse, mobiusGammaXiCoupledErrorHeadNodes,
    mobiusGammaXiCoupledErrorCriticalCoefficient, mul_comm] using hadd

def mobiusGammaXiCoupledErrorSourceCompletion (j N : ℕ) :
    Matrix (Fin (N + 2) ⊕ Unit) (Fin (N + 2) ⊕ Unit) ℂ :=
  finiteHardyMinimumCompletion (mobiusGammaXiCoupledErrorHeadGram N) (mobiusGammaXiCoupledErrorHeadGram_posDef N) (mobiusGammaXiCoupledErrorSourceResponse j N)

def mobiusGammaXiCoupledErrorSingularCompletion (N : ℕ) :
    Matrix (Fin (N + 2) ⊕ Unit) (Fin (N + 2) ⊕ Unit) ℂ :=
  finiteHardyMinimumCompletion (mobiusGammaXiCoupledErrorHeadGram N) (mobiusGammaXiCoupledErrorHeadGram_posDef N) (mobiusGammaXiCoupledErrorSingularResponse N)

def mobiusGammaXiCoupledErrorSourceOperator (j N : ℕ) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (mobiusGammaXiCoupledErrorSourceCompletion j N)

def mobiusGammaXiCoupledErrorSingularOperator (N : ℕ) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (mobiusGammaXiCoupledErrorSingularCompletion N)

theorem mobiusGammaXiCoupledErrorSourceCompletion_pos (j N : ℕ) :
    (mobiusGammaXiCoupledErrorSourceCompletion j N).PosSemidef :=
  finiteHardyMinimumCompletion_pos _ _ _

theorem mobiusGammaXiCoupledErrorSourceOperator_selfAdjoint (j N : ℕ) :
    IsSelfAdjoint (mobiusGammaXiCoupledErrorSourceOperator j N) :=
  GaloisForLFunctions.HTGeometry.isSelfAdjoint_toEuclideanCLM
    (mobiusGammaXiCoupledErrorSourceCompletion_pos j N).isHermitian

theorem tendsto_mobiusGammaXiCoupledErrorSourceCompletion (N : ℕ) :
    Tendsto (fun j => mobiusGammaXiCoupledErrorSourceCompletion j N) atTop
      (𝓝 (mobiusGammaXiCoupledErrorSingularCompletion N)) := by
  exact tendsto_finiteHardyMinimumCompletion _ _ (tendsto_mobiusGammaXiCoupledErrorSourceResponse N)

theorem tendsto_mobiusGammaXiCoupledErrorSourceOperator_norm (N : ℕ) :
    Tendsto (fun j => ‖mobiusGammaXiCoupledErrorSourceOperator j N - mobiusGammaXiCoupledErrorSingularOperator N‖) atTop (𝓝 0) := by
  have hmat := (tendsto_mobiusGammaXiCoupledErrorSourceCompletion N).sub_const (mobiusGammaXiCoupledErrorSingularCompletion N)
  have hnorm := hmat.norm
  simpa only [sub_self, norm_zero, Matrix.cstar_norm_def, map_sub,
    mobiusGammaXiCoupledErrorSourceOperator, mobiusGammaXiCoupledErrorSingularOperator] using hnorm

def mobiusGammaXiCoupledErrorSourceBudget (j N : ℕ) : ℝ :=
  finiteHardyMinimumBudget (mobiusGammaXiCoupledErrorHeadGram N) (mobiusGammaXiCoupledErrorHeadGram_posDef N) (mobiusGammaXiCoupledErrorSourceResponse j N)

def mobiusGammaXiCoupledErrorSingularBudget (N : ℕ) : ℝ :=
  finiteHardyMinimumBudget (mobiusGammaXiCoupledErrorHeadGram N) (mobiusGammaXiCoupledErrorHeadGram_posDef N) (mobiusGammaXiCoupledErrorSingularResponse N)

theorem continuous_finiteHardyMinimumBudget {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K.PosDef) : Continuous (finiteHardyMinimumBudget K hK) := by
  unfold finiteHardyMinimumBudget finiteHardyMinimumCapacity finiteHardyBoundaryColumn
  fun_prop

theorem tendsto_mobiusGammaXiCoupledErrorSourceBudget (N : ℕ) :
    Tendsto (fun j => mobiusGammaXiCoupledErrorSourceBudget j N) atTop (𝓝 (mobiusGammaXiCoupledErrorSingularBudget N)) := by
  apply (continuous_finiteHardyMinimumBudget _ _).continuousAt.tendsto.comp
  rw [tendsto_pi_nhds]
  exact tendsto_mobiusGammaXiCoupledErrorSourceResponse N

theorem mobiusGammaXiCoupledErrorSingularCompletion_eq_wall (N : ℕ) :
    mobiusGammaXiCoupledErrorSingularCompletion N =
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
        (mobiusGammaXiCoupledErrorHeadNodes N) mobiusGammaXiCoupledErrorCriticalCoefficient
        (mobiusGammaXiCoupledErrorSingularBudget N) := by
  ext a b
  rcases a with i | z <;> rcases b with j | w
  · simp [mobiusGammaXiCoupledErrorSingularCompletion, finiteHardyMinimumCompletion, mobiusGammaXiCoupledErrorHeadGram,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram]
  · simp [mobiusGammaXiCoupledErrorSingularCompletion, finiteHardyMinimumCompletion, finiteHardyBoundaryColumn,
      mobiusGammaXiCoupledErrorSingularResponse,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram]
  · simp [mobiusGammaXiCoupledErrorSingularCompletion, finiteHardyMinimumCompletion, finiteHardyBoundaryColumn,
      mobiusGammaXiCoupledErrorSingularResponse,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram]
  · cases z
    cases w
    simpa [mobiusGammaXiCoupledErrorSingularCompletion, finiteHardyMinimumCompletion, finiteHardyMinimumCapacity,
      mobiusGammaXiCoupledErrorSingularBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram] using
        (finiteHardyMinimumCapacity_entry_eq_budget (mobiusGammaXiCoupledErrorHeadGram N) (mobiusGammaXiCoupledErrorHeadGram_posDef N)
          (mobiusGammaXiCoupledErrorSingularResponse N))

theorem mobiusGammaXiCoupledErrorSingularBudget_le_graphBudget (N : ℕ) :
    mobiusGammaXiCoupledErrorSingularBudget N ≤ 4 + mobiusGammaXiCoupledErrorSingularGraphDebt := by
  have hpos := mobiusGammaXiCoupledErrorSingularGraphWall_posSemidef
    (mobiusGammaXiCoupledErrorHeadNodes N) (mobiusGammaXiCoupledErrorHeadNodes_re N)
  apply finiteHardyMinimumBudget_le_of_block_pos (mobiusGammaXiCoupledErrorHeadGram N) (mobiusGammaXiCoupledErrorHeadGram_posDef N)
      (mobiusGammaXiCoupledErrorSingularResponse N) _
  convert hpos using 1
  ext a b
  rcases a with i | z <;> rcases b with j | w <;>
    simp [mobiusGammaXiCoupledErrorSingularGraphWall,
      mobiusGammaXiCoupledErrorWallWithBudget,
      mobiusGammaXiCoupledErrorSingularGraphDebt,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram,
      mobiusGammaXiCoupledErrorHeadGram, finiteHardyBoundaryColumn, mobiusGammaXiCoupledErrorSingularResponse]

def mobiusGammaXiCoupledErrorFirstTwoEmbedding (N : ℕ) :
    Fin 2 ⊕ Unit → Fin (N + 2) ⊕ Unit
  | Sum.inl i => Sum.inl (Fin.castLE (by omega) i)
  | Sum.inr _ => Sum.inr ()

theorem mobiusGammaXiCoupledErrorHeadNodes_firstTwo (N : ℕ) (i : Fin 2) :
    mobiusGammaXiCoupledErrorHeadNodes N (Fin.castLE (by omega) i) =
      mobiusCriticalHardySaturationNodes
        (mobiusCriticalHardySaturationScale N) i := by
  fin_cases i <;>
    simp [mobiusGammaXiCoupledErrorHeadNodes, mobiusCriticalHardySaturationNodes,
      mobiusCriticalHardySaturationScale]

theorem mobiusGammaXiCoupledErrorSingularWall_firstTwo (N : ℕ) :
    (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
      (mobiusGammaXiCoupledErrorHeadNodes N) mobiusGammaXiCoupledErrorCriticalCoefficient
      (mobiusGammaXiCoupledErrorSingularBudget N)).submatrix
        (mobiusGammaXiCoupledErrorFirstTwoEmbedding N) (mobiusGammaXiCoupledErrorFirstTwoEmbedding N) =
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
        (mobiusCriticalHardySaturationNodes
          (mobiusCriticalHardySaturationScale N))
        mobiusGammaXiCoupledErrorCriticalCoefficient (mobiusGammaXiCoupledErrorSingularBudget N) := by
  ext a b
  rcases a with i | z <;> rcases b with j | w
  · simp [Matrix.submatrix_apply, mobiusGammaXiCoupledErrorFirstTwoEmbedding,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram,
      mobiusGammaXiCoupledErrorHeadNodes_firstTwo]
  · cases w
    simp [Matrix.submatrix_apply, mobiusGammaXiCoupledErrorFirstTwoEmbedding,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram,
      mobiusGammaXiCoupledErrorHeadNodes_firstTwo]
  · cases z
    simp [Matrix.submatrix_apply, mobiusGammaXiCoupledErrorFirstTwoEmbedding,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram,
      mobiusGammaXiCoupledErrorHeadNodes_firstTwo]
  · cases z
    cases w
    rfl

theorem mobiusGammaXiCoupledErrorSingularBudget_lower (N : ℕ) :
    4 + mobiusGammaXiCoupledErrorSingularGraphDebt -
        8 * mobiusCriticalHardySaturationScale N ^ (2 : ℕ) *
          (2 * mobiusCriticalHardySaturationScale N + 3) /
          ((1 + mobiusCriticalHardySaturationScale N) ^ (2 : ℕ) *
            (1 + 2 * mobiusCriticalHardySaturationScale N)) ≤
      mobiusGammaXiCoupledErrorSingularBudget N := by
  have hpos : (mobiusGammaXiCoupledErrorSingularCompletion N).PosSemidef :=
    finiteHardyMinimumCompletion_pos _ _ _
  rw [mobiusGammaXiCoupledErrorSingularCompletion_eq_wall N] at hpos
  have hsub := hpos.submatrix (mobiusGammaXiCoupledErrorFirstTwoEmbedding N)
  rw [mobiusGammaXiCoupledErrorSingularWall_firstTwo N] at hsub
  have hquad := hsub.dotProduct_mulVec_nonneg
    (mobiusCriticalHardyMassSaturationCoefficients
      (mobiusCriticalHardySaturationScale N)
      mobiusGammaXiCoupledErrorCriticalCoefficient)
  rw [mobiusCriticalHardyMassSaturation_budget_quadratic_eq
    (mobiusCriticalHardySaturationScale_pos N)] at hquad
  have hc : (0 : ℂ) ≤
      ((8 * mobiusCriticalHardySaturationScale N ^ (2 : ℕ) *
            (2 * mobiusCriticalHardySaturationScale N + 3) /
            ((1 + mobiusCriticalHardySaturationScale N) ^ (2 : ℕ) *
              (1 + 2 * mobiusCriticalHardySaturationScale N)) +
          mobiusGammaXiCoupledErrorSingularBudget N - 4 -
          Complex.normSq mobiusGammaXiCoupledErrorCriticalCoefficient : ℝ) : ℂ) := by
    convert hquad using 1
    all_goals push_cast
    all_goals ring
  rw [RCLike.le_iff_re_im] at hc
  have hre := hc.1
  change 0 ≤
    8 * mobiusCriticalHardySaturationScale N ^ (2 : ℕ) *
          (2 * mobiusCriticalHardySaturationScale N + 3) /
          ((1 + mobiusCriticalHardySaturationScale N) ^ (2 : ℕ) *
            (1 + 2 * mobiusCriticalHardySaturationScale N)) +
      mobiusGammaXiCoupledErrorSingularBudget N - 4 -
        Complex.normSq mobiusGammaXiCoupledErrorCriticalCoefficient at hre
  unfold mobiusGammaXiCoupledErrorSingularGraphDebt
  linarith

def mobiusGammaXiCoupledErrorSaturationResidual (N : ℕ) : ℝ :=
  8 * mobiusCriticalHardySaturationScale N ^ (2 : ℕ) *
      (2 * mobiusCriticalHardySaturationScale N + 3) /
    ((1 + mobiusCriticalHardySaturationScale N) ^ (2 : ℕ) *
      (1 + 2 * mobiusCriticalHardySaturationScale N))

theorem tendsto_mobiusGammaXiCoupledErrorSaturationResidual :
    Tendsto mobiusGammaXiCoupledErrorSaturationResidual atTop (𝓝 0) := by
  let r : ℝ → ℝ := fun t =>
    8 * t ^ (2 : ℕ) * (2 * t + 3) / ((1 + t) ^ (2 : ℕ) * (1 + 2 * t))
  have hr : ContinuousAt r 0 := by
    have hn : ContinuousAt (fun t : ℝ => 8 * t ^ (2 : ℕ) * (2 * t + 3)) 0 := by
      fun_prop
    have hd : ContinuousAt (fun t : ℝ => (1 + t) ^ (2 : ℕ) * (1 + 2 * t)) 0 := by
      fun_prop
    exact hn.div hd (by norm_num)
  have hscale : Tendsto mobiusCriticalHardySaturationScale atTop (𝓝 0) :=
    tendsto_mobiusCriticalHardySaturationScale.mono_right inf_le_left
  have hcomp : Tendsto (r ∘ mobiusCriticalHardySaturationScale) atTop (𝓝 (r 0)) :=
    hr.tendsto.comp hscale
  have hr0 : r 0 = 0 := by norm_num [r]
  rw [hr0] at hcomp
  change Tendsto (fun N =>
    8 * mobiusCriticalHardySaturationScale N ^ (2 : ℕ) *
        (2 * mobiusCriticalHardySaturationScale N + 3) /
      ((1 + mobiusCriticalHardySaturationScale N) ^ (2 : ℕ) *
        (1 + 2 * mobiusCriticalHardySaturationScale N))) atTop (𝓝 0)
  simpa [Function.comp_def, r] using hcomp

theorem tendsto_mobiusGammaXiCoupledErrorSingularBudget_graphBudget :
    Tendsto mobiusGammaXiCoupledErrorSingularBudget atTop
      (𝓝 (4 + mobiusGammaXiCoupledErrorSingularGraphDebt)) := by
  let G := 4 + mobiusGammaXiCoupledErrorSingularGraphDebt
  have hnonneg : ∀ N, 0 ≤ G - mobiusGammaXiCoupledErrorSingularBudget N := by
    intro N
    exact sub_nonneg.mpr (mobiusGammaXiCoupledErrorSingularBudget_le_graphBudget N)
  have hle : ∀ N, G - mobiusGammaXiCoupledErrorSingularBudget N ≤ mobiusGammaXiCoupledErrorSaturationResidual N := by
    intro N
    have h := mobiusGammaXiCoupledErrorSingularBudget_lower N
    change G - mobiusGammaXiCoupledErrorSaturationResidual N ≤ mobiusGammaXiCoupledErrorSingularBudget N at h
    linarith
  have hgap : Tendsto (fun N => G - mobiusGammaXiCoupledErrorSingularBudget N) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hle) tendsto_mobiusGammaXiCoupledErrorSaturationResidual
  have hconst : Tendsto (fun _ : ℕ => G) atTop (𝓝 G) := tendsto_const_nhds
  have hback := hconst.sub hgap
  simpa [G] using hback

theorem mobiusGammaXiCoupledErrorSingularCompletion_pos (N : ℕ) :
    (mobiusGammaXiCoupledErrorSingularCompletion N).PosSemidef :=
  finiteHardyMinimumCompletion_pos _ _ _

theorem mobiusGammaXiCoupledErrorSingularOperator_selfAdjoint (N : ℕ) :
    IsSelfAdjoint (mobiusGammaXiCoupledErrorSingularOperator N) :=
  GaloisForLFunctions.HTGeometry.isSelfAdjoint_toEuclideanCLM
    (mobiusGammaXiCoupledErrorSingularCompletion_pos N).isHermitian

def mobiusGammaXiCoupledErrorBoundaryColumnError (j N : ℕ) : ℝ :=
  ∑ i : Fin (N + 2), ‖mobiusGammaXiCoupledErrorSourceResponse j N i - mobiusGammaXiCoupledErrorSingularResponse N i‖

theorem mobiusGammaXiCoupledErrorBoundaryColumnError_nonneg (j N : ℕ) :
    0 ≤ mobiusGammaXiCoupledErrorBoundaryColumnError j N :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem tendsto_mobiusGammaXiCoupledErrorBoundaryColumnError (N : ℕ) :
    Tendsto (fun j => mobiusGammaXiCoupledErrorBoundaryColumnError j N) atTop (𝓝 0) := by
  have hzero : (0 : ℝ) = ∑ _i : Fin (N + 2), (0 : ℝ) := by simp
  rw [hzero]
  apply tendsto_finsetSum
  intro i _hi
  have hsub := (tendsto_mobiusGammaXiCoupledErrorSourceResponse N i).sub_const
    (mobiusGammaXiCoupledErrorSingularResponse N i)
  simpa using hsub.norm

def mobiusGammaXiCoupledErrorBoundaryTransportError (j N : ℕ) : ℝ :=
  ‖mobiusGammaXiCoupledErrorSourceOperator j N - mobiusGammaXiCoupledErrorSingularOperator N‖ +
    |mobiusGammaXiCoupledErrorSourceBudget j N - mobiusGammaXiCoupledErrorSingularBudget N| +
    mobiusGammaXiCoupledErrorBoundaryColumnError j N

theorem mobiusGammaXiCoupledErrorBoundaryTransportError_nonneg (j N : ℕ) :
    0 ≤ mobiusGammaXiCoupledErrorBoundaryTransportError j N := by
  exact add_nonneg
    (add_nonneg (norm_nonneg _) (abs_nonneg _))
    (mobiusGammaXiCoupledErrorBoundaryColumnError_nonneg j N)

theorem tendsto_mobiusGammaXiCoupledErrorBoundaryTransportError (N : ℕ) :
    Tendsto (fun j => mobiusGammaXiCoupledErrorBoundaryTransportError j N) atTop (𝓝 0) := by
  have hbudgetSub :=
    (tendsto_mobiusGammaXiCoupledErrorSourceBudget N).sub_const (mobiusGammaXiCoupledErrorSingularBudget N)
  have hbudgetAbs : Tendsto
      (fun j => |mobiusGammaXiCoupledErrorSourceBudget j N - mobiusGammaXiCoupledErrorSingularBudget N|)
      atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hbudgetSub.norm
  have h := (tendsto_mobiusGammaXiCoupledErrorSourceOperator_norm N).add hbudgetAbs
  have h' := h.add (tendsto_mobiusGammaXiCoupledErrorBoundaryColumnError N)
  simpa [mobiusGammaXiCoupledErrorBoundaryTransportError] using h'

theorem exists_mobiusGammaXiCoupledErrorBoundaryTransportDepth :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun N => mobiusGammaXiCoupledErrorBoundaryTransportError (depth N) N)
        atTop (𝓝 0) := by
  have hthreshold : ∀ N : ℕ, ∃ M : ℕ, ∀ j : ℕ, M ≤ j →
      mobiusGammaXiCoupledErrorBoundaryTransportError j N ≤
        mobiusCriticalHardySaturationScale N := by
    intro N
    have hpos := mobiusCriticalHardySaturationScale_pos N
    have hball := (tendsto_mobiusGammaXiCoupledErrorBoundaryTransportError N).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hpos)
    obtain ⟨M, hM⟩ := eventually_atTop.1 hball
    refine ⟨M, fun j hj => ?_⟩
    have hjball := hM j hj
    have hjlt : |mobiusGammaXiCoupledErrorBoundaryTransportError j N| <
        mobiusCriticalHardySaturationScale N := by
      simpa [Real.dist_eq] using hjball
    calc
      mobiusGammaXiCoupledErrorBoundaryTransportError j N
          ≤ |mobiusGammaXiCoupledErrorBoundaryTransportError j N| := le_abs_self _
      _ ≤ mobiusCriticalHardySaturationScale N := hjlt.le
  choose threshold hthresholdBound using hthreshold
  let depth : ℕ → ℕ :=
    fun N => N + ∑ k ∈ Finset.range (N + 1), threshold k
  have hdepthThreshold (N : ℕ) : threshold N ≤ depth N := by
    simp only [depth, Finset.sum_range_succ]
    omega
  have hdepthMono : StrictMono depth := by
    apply strictMono_nat_of_lt_succ
    intro N
    simp only [depth, Finset.sum_range_succ]
    omega
  refine ⟨depth, hdepthMono, ?_⟩
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N =>
      mobiusGammaXiCoupledErrorBoundaryTransportError_nonneg (depth N) N)
    (Filter.Eventually.of_forall fun N =>
      hthresholdBound N (depth N) (hdepthThreshold N))
    (tendsto_mobiusCriticalHardySaturationScale.mono_right inf_le_left)

/-- **Source-native finite self-adjoint boundary transport.** One strictly cofinal source-depth
schedule simultaneously preserves positivity/self-adjointness, transports complete moving Hardy
boundary columns and finite operators, and converges to exact singular graph energy. -/
theorem exists_mobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      (∀ N, (mobiusGammaXiCoupledErrorSourceCompletion (depth N) N).PosSemidef ∧
        IsSelfAdjoint (mobiusGammaXiCoupledErrorSourceOperator (depth N) N)) ∧
      (∀ N, (mobiusGammaXiCoupledErrorSingularCompletion N).PosSemidef ∧
        IsSelfAdjoint (mobiusGammaXiCoupledErrorSingularOperator N)) ∧
      Tendsto (fun N =>
        ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N -
          mobiusGammaXiCoupledErrorSingularOperator N‖)
        atTop (𝓝 0) ∧
      Tendsto (fun N => mobiusGammaXiCoupledErrorBoundaryColumnError (depth N) N)
        atTop (𝓝 0) ∧
      (∀ i : (N : ℕ) → Fin (N + 2),
        Tendsto (fun N =>
          ‖mobiusGammaXiCoupledErrorSourceResponse (depth N) N (i N) -
            mobiusGammaXiCoupledErrorSingularResponse N (i N)‖) atTop (𝓝 0)) ∧
      Tendsto (fun N => mobiusGammaXiCoupledErrorSourceBudget (depth N) N) atTop
        (𝓝 (4 + mobiusGammaXiCoupledErrorSingularGraphDebt)) := by
  obtain ⟨depth, hdepth, herror⟩ := exists_mobiusGammaXiCoupledErrorBoundaryTransportDepth
  have hopBound : ∀ N,
      ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N - mobiusGammaXiCoupledErrorSingularOperator N‖ ≤
        mobiusGammaXiCoupledErrorBoundaryTransportError (depth N) N := by
    intro N
    unfold mobiusGammaXiCoupledErrorBoundaryTransportError
    calc
      ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N - mobiusGammaXiCoupledErrorSingularOperator N‖ ≤
          ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N - mobiusGammaXiCoupledErrorSingularOperator N‖ +
            |mobiusGammaXiCoupledErrorSourceBudget (depth N) N - mobiusGammaXiCoupledErrorSingularBudget N| :=
        le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right
        (mobiusGammaXiCoupledErrorBoundaryColumnError_nonneg (depth N) N)
  have hop : Tendsto (fun N =>
      ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N - mobiusGammaXiCoupledErrorSingularOperator N‖)
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall hopBound) herror
  have hcolumnBound : ∀ N, mobiusGammaXiCoupledErrorBoundaryColumnError (depth N) N ≤
      mobiusGammaXiCoupledErrorBoundaryTransportError (depth N) N := by
    intro N
    unfold mobiusGammaXiCoupledErrorBoundaryTransportError
    exact le_add_of_nonneg_left
      (add_nonneg (norm_nonneg _) (abs_nonneg _))
  have hcolumn : Tendsto (fun N => mobiusGammaXiCoupledErrorBoundaryColumnError (depth N) N)
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun N =>
        mobiusGammaXiCoupledErrorBoundaryColumnError_nonneg (depth N) N)
      (Filter.Eventually.of_forall hcolumnBound) herror
  have hpoint (i : (N : ℕ) → Fin (N + 2)) : Tendsto (fun N =>
      ‖mobiusGammaXiCoupledErrorSourceResponse (depth N) N (i N) -
        mobiusGammaXiCoupledErrorSingularResponse N (i N)‖) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun N => ?_)
      hcolumn
    unfold mobiusGammaXiCoupledErrorBoundaryColumnError
    exact Finset.single_le_sum
      (fun (j : Fin (N + 2)) _ =>
        norm_nonneg (mobiusGammaXiCoupledErrorSourceResponse (depth N) N j -
          mobiusGammaXiCoupledErrorSingularResponse N j))
      (Finset.mem_univ (i N))
  have hbudgetAbsBound : ∀ N,
      |mobiusGammaXiCoupledErrorSourceBudget (depth N) N - mobiusGammaXiCoupledErrorSingularBudget N| ≤
        mobiusGammaXiCoupledErrorBoundaryTransportError (depth N) N := by
    intro N
    unfold mobiusGammaXiCoupledErrorBoundaryTransportError
    calc
      |mobiusGammaXiCoupledErrorSourceBudget (depth N) N - mobiusGammaXiCoupledErrorSingularBudget N| ≤
          ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N - mobiusGammaXiCoupledErrorSingularOperator N‖ +
            |mobiusGammaXiCoupledErrorSourceBudget (depth N) N - mobiusGammaXiCoupledErrorSingularBudget N| :=
        le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right
        (mobiusGammaXiCoupledErrorBoundaryColumnError_nonneg (depth N) N)
  have hbudgetAbs : Tendsto (fun N =>
      |mobiusGammaXiCoupledErrorSourceBudget (depth N) N - mobiusGammaXiCoupledErrorSingularBudget N|)
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hbudgetAbsBound) herror
  have hbudgetSub : Tendsto (fun N =>
      mobiusGammaXiCoupledErrorSourceBudget (depth N) N - mobiusGammaXiCoupledErrorSingularBudget N)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using hbudgetAbs
  have hbudget := hbudgetSub.add tendsto_mobiusGammaXiCoupledErrorSingularBudget_graphBudget
  refine ⟨depth, hdepth, fun N =>
    ⟨mobiusGammaXiCoupledErrorSourceCompletion_pos (depth N) N,
      mobiusGammaXiCoupledErrorSourceOperator_selfAdjoint (depth N) N⟩,
    fun N => ⟨mobiusGammaXiCoupledErrorSingularCompletion_pos N,
      mobiusGammaXiCoupledErrorSingularOperator_selfAdjoint N⟩,
    hop, hcolumn, hpoint, ?_⟩
  simpa using hbudget

end RHTower
