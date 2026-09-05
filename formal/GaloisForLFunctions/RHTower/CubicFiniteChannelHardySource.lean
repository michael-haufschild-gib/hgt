import GaloisForLFunctions.RHTower.CubicTwoChannelHardySource
import GaloisForLFunctions.RHTower.CCMArchimedeanPhaseTraceFormula
import GaloisForLFunctions.HTGeometry.PencilTracePolynomial
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-channel Hardy transport of literal cubic source charge

Matrix multiplication, adjoints, and ordinary nuclear traces are transported on
finite orthogonal Hilbert sums. The scalar CCM cocycle is extended to constant
plus Schwartz symbols, retaining the full matrix first-jet pairing. A flat
orthogonal source triple therefore produces genuine rounded projections with
combined cubic trace i/(4*pi) times its literal local source current.

This is the standard analytic bridge needed by the circulant source construction.
It asserts neither an arithmetic contour identification nor an independent source
budget/conservation law. No RH, prescribed index, or trace-value premise is used.
-/

open MeasureTheory ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower

section FiniteBlocks
variable {n H : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev CubicFiniteChannel (n H : Type*) := PiLp 2 (fun _ : n => H)

def cubicChannelIn (i : n) : H →L[ℂ] CubicFiniteChannel n H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : n => H) i

def cubicChannelOut (i : n) : CubicFiniteChannel n H →L[ℂ] H :=
  PiLp.proj 2 (fun _ : n => H) i

omit [Fintype n] in
@[simp] theorem cubicChannelIn_apply (i j : n) (x : H) :
    (cubicChannelIn i x) j = if j = i then x else 0 := by
  simp [cubicChannelIn, ContinuousLinearMap.comp_apply]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem cubicChannelOut_apply (i : n) (x : CubicFiniteChannel n H) :
    cubicChannelOut i x = x i := rfl

omit [Fintype n] in
@[simp] theorem cubicChannelOut_in (i j : n) :
    (cubicChannelOut i : CubicFiniteChannel n H →L[ℂ] H) ∘L cubicChannelIn j =
      if i = j then 1 else 0 := by
  ext x
  by_cases h : i = j <;> simp [h, ContinuousLinearMap.comp_apply]

def cubicFiniteBlock (M : Matrix n n (H →L[ℂ] H)) :
    CubicFiniteChannel n H →L[ℂ] CubicFiniteChannel n H :=
  ∑ i, ∑ j, cubicChannelIn i ∘L M i j ∘L cubicChannelOut j

@[simp] theorem cubicFiniteBlock_apply (M : Matrix n n (H →L[ℂ] H))
    (x : CubicFiniteChannel n H) (i : n) :
    (cubicFiniteBlock M x) i = ∑ j, M i j (x j) := by
  simp [cubicFiniteBlock, ContinuousLinearMap.comp_apply, Finset.sum_ite_irrel]

theorem cubicFiniteBlock_mul (M N : Matrix n n (H →L[ℂ] H)) :
    cubicFiniteBlock (M*N) = cubicFiniteBlock M * cubicFiniteBlock N := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  simp only [mul_apply_eq_comp, cubicFiniteBlock_apply, Matrix.mul_apply,
    sum_apply, map_sum]
  exact Finset.sum_comm

theorem cubicFiniteBlock_add (M N : Matrix n n (H →L[ℂ] H)) :
    cubicFiniteBlock (M+N) = cubicFiniteBlock M + cubicFiniteBlock N := by
  ext x i
  simp [Matrix.add_apply, Finset.sum_add_distrib]

theorem cubicFiniteBlock_one :
    cubicFiniteBlock (1 : Matrix n n (H →L[ℂ] H)) = 1 := by
  ext x i
  simp only [cubicFiniteBlock_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem cubicFiniteBlock_zero :
    cubicFiniteBlock (0 : Matrix n n (H →L[ℂ] H)) = 0 := by
  ext x i
  simp

def cubicFiniteBlockHom : Matrix n n (H →L[ℂ] H) →+*
    (CubicFiniteChannel n H →L[ℂ] CubicFiniteChannel n H) where
  toFun := cubicFiniteBlock
  map_one' := cubicFiniteBlock_one
  map_mul' := cubicFiniteBlock_mul
  map_zero' := cubicFiniteBlock_zero
  map_add' := cubicFiniteBlock_add

variable [CompleteSpace H]

theorem cubicChannelIn_adjoint (i : n) :
    adjoint (cubicChannelIn i : H →L[ℂ] CubicFiniteChannel n H) = cubicChannelOut i := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, cubicChannelOut_apply, cubicChannelIn_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem cubicFiniteBlock_adjoint (M : Matrix n n (H →L[ℂ] H)) :
    adjoint (cubicFiniteBlock M) = cubicFiniteBlock (fun i j => adjoint (M j i)) := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, cubicFiniteBlock_apply, sum_inner, inner_sum,
    adjoint_inner_left]
  exact Finset.sum_comm

omit [CompleteSpace H] in
theorem cubicFiniteBlock_corner_nuclear (i j : n) (T : H →L[ℂ] H)
    (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (cubicChannelIn i ∘L T ∘L cubicChannelOut j) := by
  rw [← memRectSchattenClass_iff_memSchattenClass, memRectSchattenClass_one_iff]
  exact summable_rectApproxNumber_comp_left
    (summable_rectApproxNumber_comp_right
      ((memRectSchattenClass_one_iff T).mp hT) (cubicChannelOut j)) (cubicChannelIn i)

omit [CompleteSpace H] in
theorem cubicFiniteBlock_nuclear (M : Matrix n n (H →L[ℂ] H))
    (hM : ∀ i j, MemSchattenClass 1 (M i j)) :
    MemSchattenClass 1 (cubicFiniteBlock M) := by
  apply memSchattenClass_one_finsetSum
  intro i _
  apply memSchattenClass_one_finsetSum
  intro j _
  exact cubicFiniteBlock_corner_nuclear i j _ (hM i j)

end FiniteBlocks

section RectangularTrace
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Rectangular trace transport with an explicit trace-class middle factor. -/
theorem cubic_nuclear_rectangular_trace (A : H →L[ℂ] K) (B : K →L[ℂ] H)
    (T : H →L[ℂ] H) (hT : MemSchattenClass 1 T) :
    opTrace (A ∘L T ∘L B) = opTrace (T ∘L (B ∘L A)) := by
  obtain ⟨S, U, hS, hU, hfac⟩ := hT.one_isTraceClass
  rw [hfac]
  calc
    opTrace (A ∘L (S ∘L U) ∘L B) =
        opTrace ((A ∘L S) ∘L (U ∘L B)) := by congr 1
    _ = opTrace ((U ∘L B) ∘L (A ∘L S)) :=
      ContinuousLinearMap.opTrace_comp_comm (hS.comp_left A) (hU.comp_right B)
    _ = opTrace ((U ∘L (B ∘L A)) ∘L S) := by congr 1
    _ = opTrace (S ∘L (U ∘L (B ∘L A))) :=
      ContinuousLinearMap.opTrace_comp_comm (hU.comp_right (B ∘L A)) hS
    _ = opTrace ((S ∘L U) ∘L (B ∘L A)) := by congr 1
end RectangularTrace

section FiniteTrace
variable {n H : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cubicFiniteBlock_corner_trace (i j : n) (T : H →L[ℂ] H)
    (hT : MemSchattenClass 1 T) :
    opTrace (cubicChannelIn i ∘L T ∘L cubicChannelOut j) =
      if i = j then opTrace T else 0 := by
  rw [cubic_nuclear_rectangular_trace _ _ _ hT, cubicChannelOut_in]
  by_cases h : i = j <;> simp [h, Ne.symm, opTrace]

theorem cubicFiniteBlock_trace (M : Matrix n n (H →L[ℂ] H))
    (hM : ∀ i j, MemSchattenClass 1 (M i j)) :
    opTrace (cubicFiniteBlock M) = ∑ i, opTrace (M i i) := by
  unfold cubicFiniteBlock
  rw [opTrace_finsetSum _ _ (fun i _ => memSchattenClass_one_finsetSum _ _
    (fun j _ => cubicFiniteBlock_corner_nuclear i j _ (hM i j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [opTrace_finsetSum _ _ (fun j _ => cubicFiniteBlock_corner_nuclear i j _ (hM i j))]
  simp only [cubicFiniteBlock_corner_trace _ _ _ (hM _ _)]
  simp

end FiniteTrace

section FiniteSymbols
variable {n : Type*} [Fintype n] [DecidableEq n]

def cubicFiniteMatrixMultiplier : Matrix n n CubicSymbols →+*
    (CubicFiniteChannel n SoninL2 →L[ℂ] CubicFiniteChannel n SoninL2) :=
  cubicFiniteBlockHom.comp cubicSymbolMultiplierHom.mapMatrix

theorem cubicFiniteMatrixMultiplier_adjoint (M : Matrix n n CubicSymbols) :
    adjoint (cubicFiniteMatrixMultiplier M) =
      cubicFiniteMatrixMultiplier M.conjTranspose := by
  change adjoint (cubicFiniteBlock (M.map cubicSymbolMultiplier)) =
    cubicFiniteBlock (M.conjTranspose.map cubicSymbolMultiplier)
  rw [cubicFiniteBlock_adjoint]
  congr 1
  apply Matrix.ext
  intro i j
  exact cubicSymbolMultiplier_adjoint (M j i)

def cubicFiniteHardyCutoff :
    CubicFiniteChannel n SoninL2 →L[ℂ] CubicFiniteChannel n SoninL2 :=
  cubicFiniteBlock (Matrix.diagonal fun _ : n => ccmHardyProjection)

theorem cubicFiniteHardyCutoff_idempotent :
    IsIdempotentElem (cubicFiniteHardyCutoff (n := n)) := by
  unfold cubicFiniteHardyCutoff IsIdempotentElem
  rw [← cubicFiniteBlock_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  exact ccmHardyProjection_idempotent

theorem cubicFiniteHardyCutoff_selfAdjoint :
    IsSelfAdjoint (cubicFiniteHardyCutoff (n := n)) := by
  have h : adjoint ccmHardyProjection = ccmHardyProjection :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ccmHardyProjection_symmetric
  change adjoint (cubicFiniteBlock (Matrix.diagonal fun _ : n => ccmHardyProjection)) =
    cubicFiniteBlock (Matrix.diagonal fun _ : n => ccmHardyProjection)
  rw [cubicFiniteBlock_adjoint]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij, Ne.symm, h]

theorem cubicFiniteMatrix_boundary (M : Matrix n n CubicSymbols) :
    cubicFiniteHardyCutoff * cubicFiniteMatrixMultiplier M -
      cubicFiniteMatrixMultiplier M * cubicFiniteHardyCutoff =
        cubicFiniteBlock (M.map cubicHardyBoundary) := by
  change cubicFiniteBlock _ * cubicFiniteBlock (M.map cubicSymbolMultiplier) -
    cubicFiniteBlock (M.map cubicSymbolMultiplier) * cubicFiniteBlock _ = _
  rw [← cubicFiniteBlock_mul, ← cubicFiniteBlock_mul]
  change cubicFiniteBlockHom _ - cubicFiniteBlockHom _ = cubicFiniteBlockHom _
  rw [← map_sub]
  congr 1
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, cubicHardyBoundary]

/-- Finite-channel boundary pairing retains every off-diagonal source coefficient. -/
theorem cubicFiniteMatrix_boundary_trace (M N : Matrix n n CubicSymbols)
    (hN : ∀ i j, MemSchattenClass 1 (cubicHardyBoundary (N i j))) :
    opTrace (cubicFiniteMatrixMultiplier M *
      (cubicFiniteHardyCutoff * cubicFiniteMatrixMultiplier N -
        cubicFiniteMatrixMultiplier N * cubicFiniteHardyCutoff)) =
      ∑ i, ∑ j, opTrace (cubicSymbolMultiplier (M i j) * cubicHardyBoundary (N j i)) := by
  rw [cubicFiniteMatrix_boundary]
  change opTrace (cubicFiniteBlock (M.map cubicSymbolMultiplier) * cubicFiniteBlock _) = _
  rw [← cubicFiniteBlock_mul]
  have hn (i j k : n) :
      MemSchattenClass 1 (cubicSymbolMultiplier (M i k) * cubicHardyBoundary (N k j)) :=
    memSchattenClass_one_comp_left (hN k j) _
  have hall (i j : n) : MemSchattenClass 1
      ((M.map cubicSymbolMultiplier * N.map cubicHardyBoundary) i j) := by
    apply memSchattenClass_one_finsetSum
    intro k _
    exact hn i j k
  rw [cubicFiniteBlock_trace _ hall]
  apply Finset.sum_congr rfl
  intro i _
  exact opTrace_finsetSum _ _ (fun j _ => hn i i j)

end FiniteSymbols

/-- Unitization of a Schwartz source; its constant is retained in the multiplier. -/
def cubicConstSchwartzSymbol (c : ℂ) (f : SchwartzMap ℝ ℂ) : CubicSymbols :=
  c • 1 + f.toBoundedContinuousFunction

@[simp] theorem cubicConstSchwartzSymbol_apply (c : ℂ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    cubicConstSchwartzSymbol c f t = c + f t := by
  simp [cubicConstSchwartzSymbol]

theorem cubicConstSchwartzSymbol_hasDerivAt (c : ℂ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt (cubicConstSchwartzSymbol c f : ℝ → ℂ) (deriv (f : ℝ → ℂ) t) t := by
  have heq : (cubicConstSchwartzSymbol c f : ℝ → ℂ) = fun x => c + f x :=
    funext (cubicConstSchwartzSymbol_apply c f)
  rw [heq]
  convert (f.hasDerivAt t).const_add c using 1

theorem cubicConstSchwartzSymbol_deriv (c : ℂ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    deriv (cubicConstSchwartzSymbol c f : ℝ → ℂ) t = deriv (f : ℝ → ℂ) t :=
  (cubicConstSchwartzSymbol_hasDerivAt c f t).deriv

theorem cubicConstSchwartzSymbol_boundary (c : ℂ) (f : SchwartzMap ℝ ℂ) :
    cubicHardyBoundary (cubicConstSchwartzSymbol c f) =
      (1 / 2 : ℂ) • ccmQuantizedDifferential f := by
  simp [cubicConstSchwartzSymbol, cubicHardyBoundary_add, cubicHardyBoundary_smul,
    cubicHardyBoundary_one, cubicHardyBoundary_schwartz]

theorem cubicConstSchwartzSymbol_boundary_nuclear (c : ℂ) (f : SchwartzMap ℝ ℂ) :
    MemSchattenClass 1 (cubicHardyBoundary (cubicConstSchwartzSymbol c f)) := by
  rw [cubicConstSchwartzSymbol_boundary]
  exact memSchattenClass_one_smul (ccmQuantizedDifferential_memSchattenClass_one f) _

theorem cubicConstSchwartzSymbol_boundary_trace (c d : ℂ) (f g : SchwartzMap ℝ ℂ) :
    opTrace (cubicSymbolMultiplier (cubicConstSchwartzSymbol c f) *
      cubicHardyBoundary (cubicConstSchwartzSymbol d g)) =
        (Complex.I / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, f t * deriv (g : ℝ → ℂ) t := by
  rw [cubicConstSchwartzSymbol_boundary]
  have hg := ccmQuantizedDifferential_memSchattenClass_one g
  have hfg : MemSchattenClass 1 (ccmSchwartzMultiplier f * ccmQuantizedDifferential g) :=
    memSchattenClass_one_comp_left hg (ccmSchwartzMultiplier f)
  simp only [cubicConstSchwartzSymbol, cubicSymbolMultiplier_add, cubicSymbolMultiplier_smul,
    cubicSymbolMultiplier_one, cubicSymbolMultiplier_schwartz, add_mul,
    mul_smul_comm, smul_mul_assoc, one_mul, opTrace_smul]
  rw [opTrace_add_of_memSchattenClass_one (memSchattenClass_one_smul hg c) hfg,
    opTrace_smul, opTrace_ccmQuantizedDifferential_eq_zero,
    opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_local]
  ring

theorem cubicConstSchwartzSymbol_pairing_integrable
    (a : CubicSymbols) (d : ℂ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => a t * deriv (cubicConstSchwartzSymbol d g : ℝ → ℂ) t) := by
  simp only [cubicConstSchwartzSymbol_deriv]
  have hg : Integrable (deriv (g : ℝ → ℂ)) := by
    exact (SchwartzMap.derivCLM ℂ ℂ g).integrable
  exact hg.bdd_mul a.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall a.norm_coe_le_norm)

/-- Constants are present in the source but their closed-boundary derivative term integrates out. -/
theorem cubicConstSchwartzSymbol_full_boundary_trace
    (c d : ℂ) (f g : SchwartzMap ℝ ℂ) :
    opTrace (cubicSymbolMultiplier (cubicConstSchwartzSymbol c f) *
      cubicHardyBoundary (cubicConstSchwartzSymbol d g)) =
        (Complex.I / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ, cubicConstSchwartzSymbol c f t *
            deriv (cubicConstSchwartzSymbol d g : ℝ → ℂ) t := by
  rw [cubicConstSchwartzSymbol_boundary_trace]
  congr 1
  simp only [cubicConstSchwartzSymbol_deriv, cubicConstSchwartzSymbol_apply, add_mul]
  have hg : Integrable (deriv (g : ℝ → ℂ)) := by
    exact (SchwartzMap.derivCLM ℂ ℂ g).integrable
  have hfg : Integrable (fun t : ℝ => f t * deriv (g : ℝ → ℂ) t) :=
    hg.bdd_mul f.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall f.toBoundedContinuousFunction.norm_coe_le_norm)
  rw [integral_add (hg.const_mul c) hfg, integral_const_mul,
    integral_deriv_schwartz_eq_zero, mul_zero, zero_add]

section FiniteCocycle
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix-valued CCM cocycle, with exact Hardy normalization and all channel coefficients. -/
theorem cubicFiniteMatrix_constSchwartz_boundary_trace
    (C D : Matrix n n ℂ) (F G : Matrix n n (SchwartzMap ℝ ℂ)) :
    opTrace (cubicFiniteMatrixMultiplier (fun i j => cubicConstSchwartzSymbol (C i j) (F i j)) *
      (cubicFiniteHardyCutoff *
          cubicFiniteMatrixMultiplier (fun i j => cubicConstSchwartzSymbol (D i j) (G i j)) -
        cubicFiniteMatrixMultiplier (fun i j => cubicConstSchwartzSymbol (D i j) (G i j)) *
          cubicFiniteHardyCutoff)) =
      (Complex.I / (2 * (Real.pi : ℂ))) *
        ∑ i, ∑ j, ∫ t : ℝ, F i j t * deriv (G j i : ℝ → ℂ) t := by
  rw [cubicFiniteMatrix_boundary_trace _ _
    (fun i j => cubicConstSchwartzSymbol_boundary_nuclear _ _)]
  simp only [cubicConstSchwartzSymbol_boundary_trace, Finset.mul_sum]

end FiniteCocycle

/-- Exact analytic admission, not a positivity or arithmetic-budget assumption. -/
def CubicSchwartzAdmissible (a : CubicSymbols) : Prop :=
  ∃ c : ℂ, ∃ f : SchwartzMap ℝ ℂ, a = cubicConstSchwartzSymbol c f

theorem cubicSchwartzAdmissible_zero : CubicSchwartzAdmissible 0 := by
  refine ⟨0, 0, ?_⟩
  ext t
  simp

theorem CubicSchwartzAdmissible.add {a b : CubicSymbols}
    (ha : CubicSchwartzAdmissible a) (hb : CubicSchwartzAdmissible b) :
    CubicSchwartzAdmissible (a+b) := by
  obtain ⟨c,f,rfl⟩ := ha
  obtain ⟨d,g,rfl⟩ := hb
  refine ⟨c+d,f+g,?_⟩
  ext t
  simp only [BoundedContinuousFunction.add_apply, cubicConstSchwartzSymbol_apply, _root_.add_apply]
  ring

theorem CubicSchwartzAdmissible.neg {a : CubicSymbols}
    (ha : CubicSchwartzAdmissible a) : CubicSchwartzAdmissible (-a) := by
  obtain ⟨c,f,rfl⟩ := ha
  refine ⟨-c,-f,?_⟩
  ext t
  simp [add_comm]

theorem CubicSchwartzAdmissible.sub {a b : CubicSymbols}
    (ha : CubicSchwartzAdmissible a) (hb : CubicSchwartzAdmissible b) :
    CubicSchwartzAdmissible (a-b) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

theorem CubicSchwartzAdmissible.mul {a b : CubicSymbols}
    (ha : CubicSchwartzAdmissible a) (hb : CubicSchwartzAdmissible b) :
    CubicSchwartzAdmissible (a*b) := by
  obtain ⟨c,f,rfl⟩ := ha
  obtain ⟨d,g,rfl⟩ := hb
  refine ⟨c*d, c • g + d • f + SchwartzMap.smulLeftCLM ℂ (f : ℝ → ℂ) g, ?_⟩
  ext t
  simp [SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth, smul_eq_mul]
  ring

theorem cubicSchwartzAdmissible_finsetSum {ι : Type*} (s : Finset ι)
    (a : ι → CubicSymbols) (ha : ∀ i ∈ s, CubicSchwartzAdmissible (a i)) :
    CubicSchwartzAdmissible (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using cubicSchwartzAdmissible_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (ha i (Finset.mem_insert_self i s)).add
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))

section AdmissibleMatrices
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem cubicSchwartzAdmissible_matrix_mul (M N : Matrix n n CubicSymbols)
    (hM : ∀ i j, CubicSchwartzAdmissible (M i j))
    (hN : ∀ i j, CubicSchwartzAdmissible (N i j)) :
    ∀ i j, CubicSchwartzAdmissible ((M*N) i j) := by
  intro i j
  exact cubicSchwartzAdmissible_finsetSum _ _ (fun k _ => (hM i k).mul (hN k j))

theorem cubicFiniteMatrix_admissible_boundary_nuclear (M : Matrix n n CubicSymbols)
    (hM : ∀ i j, CubicSchwartzAdmissible (M i j)) :
    MemSchattenClass 1 (cubicFiniteHardyCutoff * cubicFiniteMatrixMultiplier M -
      cubicFiniteMatrixMultiplier M * cubicFiniteHardyCutoff) := by
  rw [cubicFiniteMatrix_boundary]
  apply cubicFiniteBlock_nuclear
  intro i j
  obtain ⟨c,f,h⟩ := hM i j
  change MemSchattenClass 1 (cubicHardyBoundary (M i j))
  rw [h]
  exact cubicConstSchwartzSymbol_boundary_nuclear c f

def cubicFiniteSymbolValue (M : Matrix n n CubicSymbols) (t : ℝ) : Matrix n n ℂ :=
  fun i j => M i j t

def cubicFiniteSymbolJet (M : Matrix n n CubicSymbols) (t : ℝ) : Matrix n n ℂ :=
  fun i j => deriv (M i j : ℝ → ℂ) t

def cubicFiniteSourceCurrent (A B C : Matrix n n CubicSymbols) : Matrix n n CubicSymbols :=
  (A*B-B*A)+(B*C-C*B)+(C*A-A*C)

/-- The ordinary finite-channel trace is the literal matrix first-jet pairing. -/
theorem cubicFiniteMatrix_admissible_boundary_trace (M N : Matrix n n CubicSymbols)
    (hM : ∀ i j, CubicSchwartzAdmissible (M i j))
    (hN : ∀ i j, CubicSchwartzAdmissible (N i j)) :
    opTrace (cubicFiniteMatrixMultiplier M *
      (cubicFiniteHardyCutoff * cubicFiniteMatrixMultiplier N -
        cubicFiniteMatrixMultiplier N * cubicFiniteHardyCutoff)) =
      (Complex.I / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ, Matrix.trace (cubicFiniteSymbolValue M t * cubicFiniteSymbolJet N t) := by
  have hint (i j : n) : Integrable
      (fun t : ℝ => M i j t * deriv (N j i : ℝ → ℂ) t) := by
    obtain ⟨d,g,h⟩ := hN j i
    rw [h]
    exact cubicConstSchwartzSymbol_pairing_integrable _ _ _
  have htrace (i j : n) :
      opTrace (cubicSymbolMultiplier (M i j) * cubicHardyBoundary (N j i)) =
        (Complex.I / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ, M i j t * deriv (N j i : ℝ → ℂ) t := by
    obtain ⟨c,f,hf⟩ := hM i j
    obtain ⟨d,g,hg⟩ := hN j i
    rw [hf,hg]
    exact cubicConstSchwartzSymbol_full_boundary_trace _ _ _ _
  rw [cubicFiniteMatrix_boundary_trace _ _ (fun i j => by
    obtain ⟨d,g,h⟩ := hN i j
    rw [h]
    exact cubicConstSchwartzSymbol_boundary_nuclear _ _)]
  simp only [htrace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    cubicFiniteSymbolValue, cubicFiniteSymbolJet]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hint i j))]
  simp only [integral_finsetSum Finset.univ (fun j _ => hint _ j), Finset.mul_sum]

/-- Lift a finite source triple, preserving the complete local charge through projection rounding.
Only algebraic orthogonal projection identities, source flatness, and Schwartz admission are used.
No index, zero count, trace value, positivity, or conservation premise appears. -/
theorem exists_rounded_finiteSource_cubic_with_local_charge
    (A B C : Matrix n n CubicSymbols)
    (hA : A*A=A) (hB : B*B=B) (hC : C*C=C)
    (hAs : A.conjTranspose=A) (hBs : B.conjTranspose=B) (hCs : C.conjTranspose=C)
    (hAa : ∀ i j, CubicSchwartzAdmissible (A i j))
    (hBa : ∀ i j, CubicSchwartzAdmissible (B i j))
    (hCa : ∀ i j, CubicSchwartzAdmissible (C i j))
    (hflat : (A+B+C) * cubicFiniteSourceCurrent A B C =
      cubicFiniteSourceCurrent A B C * (A+B+C)) :
    ∃ P Q R : CubicFiniteChannel n SoninL2 →L[ℂ] CubicFiniteChannel n SoninL2,
      IsSelfAdjoint P ∧ IsSelfAdjoint Q ∧ IsSelfAdjoint R ∧
      IsIdempotentElem P ∧ IsIdempotentElem Q ∧ IsIdempotentElem R ∧
      MemSchattenClass 1 (P-cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier A*cubicFiniteHardyCutoff) ∧
      MemSchattenClass 1 (Q-cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier B*cubicFiniteHardyCutoff) ∧
      MemSchattenClass 1 (R-cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier C*cubicFiniteHardyCutoff) ∧
      MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) ∧
      opTrace (formationAnchoredCubicAssociator R Q P) =
        (Complex.I / (4 * (Real.pi : ℂ))) *
          ∫ t : ℝ, Matrix.trace (cubicFiniteSymbolValue (A+B+C) t *
            cubicFiniteSymbolJet (cubicFiniteSourceCurrent A B C) t) := by
  let L := cubicFiniteMatrixMultiplier (n := n)
  have hid (M : Matrix n n CubicSymbols) (hM : M*M=M) : IsIdempotentElem (L M) := by
    change L M * L M = L M
    rw [← map_mul, hM]
  have hsa (M : Matrix n n CubicSymbols) (hM : M.conjTranspose=M) : IsSelfAdjoint (L M) := by
    change adjoint (cubicFiniteMatrixMultiplier M) = cubicFiniteMatrixMultiplier M
    rw [cubicFiniteMatrixMultiplier_adjoint, hM]
  have hsum : L (A+B+C) = cubicAggregate (L A) (L B) (L C) := by
    simp [cubicAggregate]
  have hcur : L (cubicFiniteSourceCurrent A B C) = cubicCyclicCurrent (L A) (L B) (L C) := by
    simp [cubicFiniteSourceCurrent, cubicCyclicCurrent]
  have hfl : cubicAggregate (L A) (L B) (L C) * cubicCyclicCurrent (L A) (L B) (L C) =
      cubicCyclicCurrent (L A) (L B) (L C) * cubicAggregate (L A) (L B) (L C) := by
    rw [← hsum, ← hcur, ← map_mul, ← map_mul, hflat]
  obtain ⟨P,Q,R,hPs,hQs,hRs,hPi,hQi,hRi,hP,hQ,hR,hN,htr⟩ :=
    exists_rounded_cubic_with_boundary_trace cubicFiniteHardyCutoff (L A) (L B) (L C)
      cubicFiniteHardyCutoff_idempotent cubicFiniteHardyCutoff_selfAdjoint
      (hid A hA) (hid B hB) (hid C hC) (hsa A hAs) (hsa B hBs) (hsa C hCs)
      (cubicFiniteMatrix_admissible_boundary_nuclear A hAa)
      (cubicFiniteMatrix_admissible_boundary_nuclear B hBa)
      (cubicFiniteMatrix_admissible_boundary_nuclear C hCa) hfl
  refine ⟨P,Q,R,hPs,hQs,hRs,hPi,hQi,hRi,hP,hQ,hR,hN,?_⟩
  have hsumA (i j : n) : CubicSchwartzAdmissible ((A+B+C) i j) :=
    ((hAa i j).add (hBa i j)).add (hCa i j)
  have hcurA (i j : n) : CubicSchwartzAdmissible (cubicFiniteSourceCurrent A B C i j) :=
    (((cubicSchwartzAdmissible_matrix_mul A B hAa hBa i j).sub
      (cubicSchwartzAdmissible_matrix_mul B A hBa hAa i j)).add
      ((cubicSchwartzAdmissible_matrix_mul B C hBa hCa i j).sub
      (cubicSchwartzAdmissible_matrix_mul C B hCa hBa i j))).add
      ((cubicSchwartzAdmissible_matrix_mul C A hCa hAa i j).sub
      (cubicSchwartzAdmissible_matrix_mul A C hAa hCa i j))
  rw [← hsum, ← hcur] at htr
  rw [cubicFiniteMatrix_admissible_boundary_trace _ _ hsumA hcurA] at htr
  linear_combination (1/2 : ℂ) * htr

end AdmissibleMatrices
end RHTower

