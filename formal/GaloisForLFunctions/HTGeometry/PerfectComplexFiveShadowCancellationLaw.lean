import GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationMatrixRay
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.DualNumberErasure
import GaloisForLFunctions.HTGeometry.LoopGaugeApplications

/-!
# Perfect-complex five-shadow cancellation

The two equivariant exact sequences in each degree give additive and multiplicative shadow data:
`Cⁱ = Zⁱ + Bⁱ⁺¹`, `Zⁱ = Bⁱ + Hⁱ` and their determinant analogues.  This file proves the generic
bounded telescoping laws once, then packages the Euler/K₀, all power-supertrace, all
power-superdeterminant, and positive modulus readings.  Boundary terms cancel between adjacent
degrees without any parity or dimension restriction.

The unitary recurrence theorem is inherited from the corpus's arbitrary finite unitary matrix
theorem.  Explicit countermodels record polarity loss, extension-data loss, cost rescaling, and
flat nontrivial holonomy.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset
open scoped BigOperators

noncomputable section

/-- Alternating additive reading of degrees `0,...,N`. -/
def perfectAlternatingSum {A : Type*} [AddCommGroup A] (N : ℕ) (f : ℕ → A) : A :=
  ∑ i ∈ range (N + 1), ((-1 : ℤ) ^ i) • f i

theorem perfectAlternatingBoundarySum_eq_zero {A : Type*} [AddCommGroup A]
    (N : ℕ) (B : ℕ → A) (hzero : B 0 = 0) (hend : B (N + 1) = 0) :
    perfectAlternatingSum N B + perfectAlternatingSum N (fun i => B (i + 1)) = 0 := by
  rw [perfectAlternatingSum, perfectAlternatingSum, sum_range_succ', sum_range_succ]
  rw [hzero, hend]
  simp only [smul_zero, add_zero, ← sum_add_distrib]
  apply sum_eq_zero
  intro i hi
  rw [pow_succ]
  simp

/-- Additive invariant values supplied by the two exact sequences
`0→Zⁱ→Cⁱ→Bⁱ⁺¹→0` and `0→Bⁱ→Zⁱ→Hⁱ→0`. -/
structure PerfectAdditiveExactShadow (A : Type*) [AddCommGroup A] (N : ℕ) where
  term : ℕ → A
  cocycle : ℕ → A
  boundary : ℕ → A
  cohomology : ℕ → A
  boundary_zero : boundary 0 = 0
  boundary_top : boundary (N + 1) = 0
  term_exact : ∀ i, term i = cocycle i + boundary (i + 1)
  cocycle_exact : ∀ i, cocycle i = boundary i + cohomology i

namespace PerfectAdditiveExactShadow

/-- Every additive exact-sequence invariant of a bounded perfect complex factors through
cohomology after taking the alternating reading. -/
theorem alternating_term_eq_cohomology {A : Type*} [AddCommGroup A] {N : ℕ}
    (S : PerfectAdditiveExactShadow A N) :
    perfectAlternatingSum N S.term = perfectAlternatingSum N S.cohomology := by
  have hterm : perfectAlternatingSum N S.term =
      perfectAlternatingSum N S.cocycle +
        perfectAlternatingSum N (fun i => S.boundary (i + 1)) := by
    unfold perfectAlternatingSum
    simp_rw [S.term_exact, smul_add]
    exact sum_add_distrib
  have hcycle : perfectAlternatingSum N S.cocycle =
      perfectAlternatingSum N S.boundary +
        perfectAlternatingSum N S.cohomology := by
    unfold perfectAlternatingSum
    simp_rw [S.cocycle_exact, smul_add]
    exact sum_add_distrib
  rw [hterm, hcycle]
  have hcancel := perfectAlternatingBoundarySum_eq_zero N S.boundary
    S.boundary_zero S.boundary_top
  calc
    perfectAlternatingSum N S.boundary + perfectAlternatingSum N S.cohomology +
        perfectAlternatingSum N (fun i => S.boundary (i + 1)) =
      perfectAlternatingSum N S.cohomology +
        (perfectAlternatingSum N S.boundary +
          perfectAlternatingSum N (fun i => S.boundary (i + 1))) := by abel
    _ = perfectAlternatingSum N S.cohomology := by rw [hcancel, add_zero]

end PerfectAdditiveExactShadow

/-- Alternating multiplicative reading, using inverses in odd degree. -/
def perfectAlternatingProduct {G : Type*} [CommGroup G] (N : ℕ) (f : ℕ → G) : G :=
  ∏ i ∈ range (N + 1), f i ^ ((-1 : ℤ) ^ i)

theorem perfectAlternatingBoundaryProduct_eq_one {G : Type*} [CommGroup G]
    (N : ℕ) (B : ℕ → G) (hzero : B 0 = 1) (hend : B (N + 1) = 1) :
    perfectAlternatingProduct N B *
      perfectAlternatingProduct N (fun i => B (i + 1)) = 1 := by
  rw [perfectAlternatingProduct, perfectAlternatingProduct,
    prod_range_succ', prod_range_succ]
  rw [hzero, hend]
  simp only [one_zpow, mul_one, ← prod_mul_distrib]
  apply prod_eq_one
  intro i hi
  rw [pow_succ]
  simp [zpow_neg]

/-- Multiplicative invariant values supplied by the same two exact sequences. -/
structure PerfectMultiplicativeExactShadow (G : Type*) [CommGroup G] (N : ℕ) where
  term : ℕ → G
  cocycle : ℕ → G
  boundary : ℕ → G
  cohomology : ℕ → G
  boundary_zero : boundary 0 = 1
  boundary_top : boundary (N + 1) = 1
  term_exact : ∀ i, term i = cocycle i * boundary (i + 1)
  cocycle_exact : ∀ i, cocycle i = boundary i * cohomology i

namespace PerfectMultiplicativeExactShadow

/-- Every multiplicative exact-sequence invariant factors through cohomology after taking the
alternating product. -/
theorem alternating_term_eq_cohomology {G : Type*} [CommGroup G] {N : ℕ}
    (S : PerfectMultiplicativeExactShadow G N) :
    perfectAlternatingProduct N S.term = perfectAlternatingProduct N S.cohomology := by
  have hterm : perfectAlternatingProduct N S.term =
      perfectAlternatingProduct N S.cocycle *
        perfectAlternatingProduct N (fun i => S.boundary (i + 1)) := by
    unfold perfectAlternatingProduct
    simp_rw [S.term_exact, mul_zpow]
    exact prod_mul_distrib
  have hcycle : perfectAlternatingProduct N S.cocycle =
      perfectAlternatingProduct N S.boundary *
        perfectAlternatingProduct N S.cohomology := by
    unfold perfectAlternatingProduct
    simp_rw [S.cocycle_exact, mul_zpow]
    exact prod_mul_distrib
  rw [hterm, hcycle]
  have hcancel := perfectAlternatingBoundaryProduct_eq_one N S.boundary
    S.boundary_zero S.boundary_top
  calc
    perfectAlternatingProduct N S.boundary *
          perfectAlternatingProduct N S.cohomology *
        perfectAlternatingProduct N (fun i => S.boundary (i + 1)) =
      perfectAlternatingProduct N S.cohomology *
        (perfectAlternatingProduct N S.boundary *
          perfectAlternatingProduct N (fun i => S.boundary (i + 1))) := by ac_rfl
    _ = perfectAlternatingProduct N S.cohomology := by rw [hcancel, mul_one]

end PerfectMultiplicativeExactShadow

/-- Exact bounded-perfect input for all five readings.  The integer shadow is `K₀(k) ≅ ℤ` for a
field; complex additive shadows are traces of every power; unit-valued multiplicative shadows are
the nonzero determinants of every automorphism power. -/
structure PerfectComplexFiveShadowData (N : ℕ) where
  euler : PerfectAdditiveExactShadow ℤ N
  tracePower : ℕ → PerfectAdditiveExactShadow ℂ N
  determinantPower : ℕ → PerfectMultiplicativeExactShadow ℂˣ N

/-- Positive scalar reading `|u|²`. -/
def perfectPositiveModulus (u : ℂˣ) : ℝ := ‖(u : ℂ)‖ ^ 2

/-- Five-shadow cancellation: Euler/K₀, all power supertraces, all power superdeterminants, and
their positive squared moduli factor through cohomology simultaneously. -/
theorem perfectComplex_fiveShadow_cancellation {N : ℕ}
    (C : PerfectComplexFiveShadowData N) :
    perfectAlternatingSum N C.euler.term =
        perfectAlternatingSum N C.euler.cohomology ∧
      (∀ n, perfectAlternatingSum N (C.tracePower n).term =
        perfectAlternatingSum N (C.tracePower n).cohomology) ∧
      (∀ n, perfectAlternatingProduct N (C.determinantPower n).term =
        perfectAlternatingProduct N (C.determinantPower n).cohomology) ∧
      (∀ n, perfectPositiveModulus
          (perfectAlternatingProduct N (C.determinantPower n).term) =
        perfectPositiveModulus
          (perfectAlternatingProduct N (C.determinantPower n).cohomology)) := by
  refine ⟨C.euler.alternating_term_eq_cohomology,
    fun n => (C.tracePower n).alternating_term_eq_cohomology,
    fun n => (C.determinantPower n).alternating_term_eq_cohomology, ?_⟩
  intro n
  rw [(C.determinantPower n).alternating_term_eq_cohomology]

theorem perfectAlternatingProduct_norm_eq_one (N : ℕ) (f : ℕ → ℂˣ)
    (hf : ∀ i, ‖(f i : ℂ)‖ = 1) :
    ‖((perfectAlternatingProduct N f : ℂˣ) : ℂ)‖ = 1 := by
  simp [perfectAlternatingProduct, hf]

/-- A unitary determinant shadow has identically unit positive modulus. -/
theorem perfectUnitary_positiveModulus_eq_one (N : ℕ) (f : ℕ → ℂˣ)
    (hf : ∀ i, ‖(f i : ℂ)‖ = 1) :
    perfectPositiveModulus (perfectAlternatingProduct N f) = 1 := by
  rw [perfectPositiveModulus, perfectAlternatingProduct_norm_eq_one N f hf]
  norm_num

/-- Arbitrary finite-dimensional unitary powers lie in a compact group and recur to identity at
unbounded natural times. -/
theorem finiteUnitary_powers_have_compact_recurrence
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    IsCompact (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) ∧
      MapClusterPt 1 Filter.atTop (fun k : ℕ => U ^ k) :=
  ⟨isCompact_matrixUnitaryGroup, matrixUnitary_pow_recurrent U⟩

/-- Positive square/modulus data do not determine polarity. -/
theorem positiveShadow_loses_polarity :
    (1 : ℂ) ^ 2 = (-1 : ℂ) ^ 2 ∧
      Complex.normSq (1 : ℂ) = Complex.normSq (-1 : ℂ) ∧
      (1 : ℂ) ≠ -1 := by
  norm_num [Complex.normSq_apply]

/-- Same two-dimensional vector-space shadow, but distinct dual-number extension laws. -/
theorem dualNumber_extensionData_not_determined_by_scalarShadows
    (K : Type) [Field K] :
    (_root_.HTGeometry.ConstraintRelativity.zeroLaw K (K × K)).frame ≠
        (_root_.HTGeometry.ConstraintRelativity.jordanLaw K).frame ∧
      Nonempty (_root_.HTGeometry.ConstraintRelativity.trivialExtension K ≃ K) ∧
      (∀ (W : Type) [AddCommGroup W] [Module K W] (F : Submodule K W),
        ∃ C : Submodule K W, IsCompl F C) := by
  have h :=
    _root_.HTGeometry.ConstraintRelativity.static_conservativity_not_deformation_conservativity K
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- Two positive actions on the same motive and automorphism data differ by a genuine scale. -/
def perfectCost (z : ℂ) : ℝ := Complex.normSq z

def doubledPerfectCost (z : ℂ) : ℝ := 2 * perfectCost z

theorem same_motive_does_not_determine_cost :
    (∀ z, doubledPerfectCost z = 2 * perfectCost z) ∧
      perfectCost 1 ≠ doubledPerfectCost 1 := by
  constructor
  · intro z
    rfl
  · norm_num [perfectCost, doubledPerfectCost, Complex.normSq_apply]

/-- Zero local curvature does not determine global triviality. -/
theorem flat_not_globally_trivial :
    (0 : Module.End ℝ ℝ) = 0 ∧
      _root_.HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection.circleSignHolonomy
        (Multiplicative.ofAdd 1) ≠ 1 :=
  LoopGaugeApplications.flatWilsonLoop_can_survive_zero_curvature

end

end GaloisForLFunctions.HTGeometry
