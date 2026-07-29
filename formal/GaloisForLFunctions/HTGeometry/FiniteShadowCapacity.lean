import GaloisForLFunctions.HTGeometry.DifferentialIndependentLinearForms
import Mathlib.Tactic

/-!
# Finite shadows disperse differential orbit capacity

Suppose an observable is a finite linear superposition of differentially independent source
coefficients, and a structural action only changes the constant coefficient row.  Then a packet of
observations is differentially independent exactly when its coefficient rows are linearly
independent.  In particular, `N + 1` observations mixed from only `N` sources can never be
differentially free, while an invertible `N x N` observation packet realizes rank `N`.

This is the algebraic core of the compact-shadow capacity theorem.  For a meromorphic family on a
compact Abelian fibre, relative rationality supplies a finite source-coefficient presentation for
each individual observable.  Different observables may use arbitrarily large finite palettes, but
no one finite palette supports an infinite free orbit.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Matrix GaloisForLFunctions

noncomputable section

/-- Multiplication by a nonvanishing germ in divided-jet coordinates.  If `a r` is the `r`th
divided jet of the multiplier, the product jet of order `i` is the lower-triangular convolution
with coefficients `a (i-j)`. -/
def truncatedJetMultiplicationMatrix
    {R : Type*} [Zero R] (a : ℕ → R) (N : ℕ) :
    Matrix (Fin N) (Fin N) R :=
  fun i j => if (j : ℕ) ≤ (i : ℕ) then a ((i : ℕ) - (j : ℕ)) else 0

/-- Multiplication by a germ preserves the order filtration on every finite jet algebra. -/
theorem truncatedJetMultiplicationMatrix_lowerTriangular
    {R : Type*} [Zero R] (a : ℕ → R) (N : ℕ) :
    (truncatedJetMultiplicationMatrix a N).BlockTriangular
      (fun i : Fin N => OrderDual.toDual i) := by
  intro i j hij
  have hlt : (i : ℕ) < (j : ℕ) := OrderDual.toDual_lt_toDual.mp hij
  simp [truncatedJetMultiplicationMatrix, Nat.not_le_of_gt hlt]

/-- Every diagonal entry of finite jet multiplication is the value of the multiplier. -/
@[simp]
theorem truncatedJetMultiplicationMatrix_diag
    {R : Type*} [Zero R] (a : ℕ → R) (N : ℕ) (i : Fin N) :
    truncatedJetMultiplicationMatrix a N i i = a 0 := by
  simp [truncatedJetMultiplicationMatrix]

/-- The determinant of multiplication on `N` divided jets is the `N`th power of the multiplier's
value. -/
theorem truncatedJetMultiplicationMatrix_det
    {R : Type*} [CommRing R] (a : ℕ → R) (N : ℕ) :
    (truncatedJetMultiplicationMatrix a N).det = (a 0) ^ N := by
  rw [Matrix.det_of_lowerTriangular _
    (truncatedJetMultiplicationMatrix_lowerTriangular a N)]
  simp

/-- **Finite-jet unit law.**  Multiplication by a germ nonzero at the packet point is invertible
on every finite truncated jet algebra.  This is the exact algebraic step used when a Poincare-series
damping factor multiplies the already interpolated subgroup packet. -/
theorem truncatedJetMultiplicationMatrix_det_ne_zero
    {R : Type*} [Field R] (a : ℕ → R) (N : ℕ) (ha : a 0 ≠ 0) :
    (truncatedJetMultiplicationMatrix a N).det ≠ 0 := by
  rw [truncatedJetMultiplicationMatrix_det]
  exact pow_ne_zero N ha

/-- **Local Artin unit law.**  In any finite or multivariate truncated local algebra,
multiplication by the class of a nonvanishing germ is bijective as soon as that class is a unit.
This is the coordinate-free version of the preceding triangular determinant theorem. -/
theorem truncatedLocalAlgebra_mul_bijective_of_isUnit
    {A : Type*} [Monoid A] (u : A) (hu : IsUnit u) :
    Function.Bijective (u * ·) := by
  exact IsUnit.isUnit_iff_mulLeft_bijective.mp hu

/-- Differentiating a matrix observation applies the same matrix to every jet order when the
actual matrix entries, rather than the whole coefficient field, are differential constants. -/
theorem differentialJet_matrixLinearForms_of_coefficients_constant
    {C K m n : Type*} [CommRing C] [CommRing K] [Algebra C K]
    [Differential K] [Fintype n]
    (M : Matrix m n C)
    (hMconst : ∀ i j, (algebraMap C K (M i j))′ = 0)
    (x : n → K) (i : m) (r : ℕ) :
    differentialJet r (matrixLinearForms M x i) =
      matrixLinearForms M (fun j => differentialJet r (x j)) i := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [differentialJet_succ, ih]
      simp only [matrixLinearForms, map_sum, Derivation.leibniz, hMconst,
        smul_eq_mul, mul_zero, add_zero]

/-- Full-row-rank recombination preserves differential independence when the entries of this
matrix are differential constants.  No constancy assumption is imposed on unrelated elements of
the coefficient field. -/
theorem differentialIndependent_matrixLinearForms_of_linearIndependent_rows_of_coefficients_constant
    {C K m n : Type*} [Field C] [CommRing K] [Algebra C K]
    [Differential K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n C)
    (hMconst : ∀ i j, (algebraMap C K (M i j))′ = 0)
    (hM : LinearIndependent C M.row)
    (x : n → K) (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (matrixLinearForms M x) := by
  obtain ⟨N, hMN⟩ := exists_matrix_rightInverse_of_linearIndependent_rows M hM
  unfold DifferentialIndependent at hx ⊢
  have h := algebraicIndependent_jetwiseMatrixLinearForms_of_mul_eq_one M N hMN
    (fun p : n × ℕ => differentialJet p.2 (x p.1)) hx
  have heq :
      (fun p : m × ℕ => differentialJet p.2 (matrixLinearForms M x p.1)) =
        jetwiseMatrixLinearForms M
          (fun p : n × ℕ => differentialJet p.2 (x p.1)) := by
    funext p
    exact differentialJet_matrixLinearForms_of_coefficients_constant
      M hMconst x p.1 p.2
  rw [heq]
  exact h

/-- **Exact finite-shadow rank criterion.**  If the source coordinates are differentially
independent and the observation-matrix entries are differential constants, then its linear forms
are differentially independent exactly when the matrix rows are linearly independent.

The reverse implication is important: differential freedom of the observations forces full row
rank in the finite coefficient shadow; a nonlinear differential relation cannot hide a linear
coefficient collision. -/
theorem differentialIndependent_matrixLinearForms_iff_rowIndependent
    {C K m n : Type*} [Field C] [CommRing K] [Algebra C K]
    [Differential K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n C)
    (hMconst : ∀ i j, (algebraMap C K (M i j))′ = 0)
    (x : n → K) (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (matrixLinearForms M x) ↔
      LinearIndependent C M.row := by
  constructor
  · intro hout
    have houtLinear : LinearIndependent C (matrixLinearForms M x) :=
      hout.algebraicIndependent.linearIndependent
    let L : (n → C) →ₗ[C] K := Fintype.linearCombination C x
    have hcomp : (L ∘ M.row) = matrixLinearForms M x := by
      funext i
      simp [L, matrixLinearForms, Fintype.linearCombination_apply, Algebra.smul_def]
    apply LinearIndependent.of_comp L
    simpa only [hcomp] using houtLinear
  · intro hrows
    exact differentialIndependent_matrixLinearForms_of_linearIndependent_rows_of_coefficients_constant
      M hMconst hrows x hx

/-- **Finite-shadow nonconcentration.**  `N + 1` observations assembled from `N`
differentially independent source coefficients cannot themselves be differentially independent.
This is the formal no-go behind finite cyclic capacity of a compact-trapped meromorphic
observable. -/
theorem finiteShadow_moreObservablesThanSources_not_differentialIndependent
    {C K : Type*} [Field C] [CommRing K] [Algebra C K]
    [Differential K] (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin n) C)
    (hMconst : ∀ i j, (algebraMap C K (M i j))′ = 0)
    (x : Fin n → K)
    (hx : DifferentialIndependent C x) :
    ¬ DifferentialIndependent C (matrixLinearForms M x) := by
  intro hout
  have hrows : LinearIndependent C M.row :=
    (differentialIndependent_matrixLinearForms_iff_rowIndependent
      M hMconst x hx).mp hout
  have hrank : M.rank = n + 1 := by
    simpa using hrows.rank_matrix
  have hle : M.rank ≤ n := by
    simpa using M.rank_le_card_width
  omega

/-- **Exact finite-capacity realization.**  An invertible square observation matrix transfers all
`N` differentially independent source directions to `N` observations.  Together with the preceding
no-go, this is the finite attained side of the unbounded-but-unattained capacity law. -/
theorem finiteShadow_fullRank_realizes_capacity
    {C K : Type*} [Field C] [CommRing K] [Algebra C K]
    [Differential K] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C) (hdet : M.det ≠ 0)
    (hMconst : ∀ i j, (algebraMap C K (M i j))′ = 0)
    (x : Fin n → K) (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (matrixLinearForms M x) := by
  apply differentialIndependent_matrixLinearForms_of_linearIndependent_rows_of_coefficients_constant
    M hMconst _ x hx
  exact Matrix.linearIndependent_rows_of_det_ne_zero hdet

/-- **Active-quotient faithfulness.**  Let a torsion-free structural lattice carry a completely
differentially free orbit.  If every nonzero cyclic orbit lying in the kernel of a quotient has
finite-shadow capacity, then the lattice map to that quotient is injective.

This is the exact formal passage from compact-kernel finite capacity to the active-quotient law:
any nonzero kernel element would generate an injectively indexed cyclic subfamily of the full free
orbit, contradicting compact-shadow nonconcentration. -/
theorem activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not
    {F K L Q : Type*} [CommRing F] [Nontrivial F] [CommRing K]
    [Algebra F K] [Differential K] [AddCommGroup L] [AddCommGroup Q]
    (orbit : L → K) (horbit : DifferentialIndependent F orbit)
    (q : L →+ Q)
    (hcyclic : ∀ k : L, k ≠ 0 → Function.Injective (fun n : ℤ => n • k))
    (hcompact : ∀ k : L, q k = 0 → k ≠ 0 →
      ¬ DifferentialIndependent F (fun n : ℤ => orbit (n • k))) :
    Function.Injective q := by
  intro a b hab
  let k : L := a - b
  have hkq : q k = 0 := by
    simp [k, hab]
  by_contra habne
  have hkne : k ≠ 0 := by
    simpa only [k, sub_ne_zero] using habne
  have hsub : DifferentialIndependent F (fun n : ℤ => orbit (n • k)) := by
    simpa only [Function.comp_def] using
      horbit.comp (fun n : ℤ => n • k) (hcyclic k hkne)
  exact hcompact k hkq hkne hsub

/-- **Exact active-palette dimension classification.**  If every full HT realization extracts an
active quasi-Abelian palette in the same dimension and every active palette realizes a full HT
system in the same dimension, then their least realization dimensions coincide.

The two analytic directions are explicit hypotheses: compact-kernel nonconcentration supplies
`extract`, while all-order packet interpolation on the active quotient supplies `realize`. -/
theorem activeQuasiAbelianDimension_eq_hypertranscendenceDimension
    (FullHTRealizable ActivePaletteRealizable : ℕ → Prop)
    (htDim aqaDim : ℕ)
    (hfull : FullHTRealizable htDim)
    (hactive : ActivePaletteRealizable aqaDim)
    (extract : ∀ d, FullHTRealizable d → ActivePaletteRealizable d)
    (realize : ∀ d, ActivePaletteRealizable d → FullHTRealizable d)
    (hhtLeast : ∀ d, FullHTRealizable d → htDim ≤ d)
    (haqaLeast : ∀ d, ActivePaletteRealizable d → aqaDim ≤ d) :
    htDim = aqaDim := by
  apply Nat.le_antisymm
  · exact hhtLeast aqaDim (realize aqaDim hactive)
  · exact haqaLeast htDim (extract htDim hfull)

end

end GaloisForLFunctions.HTGeometry
