import GaloisForLFunctions.RHTower.CCMRectangularAutocorrelation
import GaloisForLFunctions.RHTower.SuzukiWallFieldAntidiagonalGramLift
import GaloisForLFunctions.RHTower.SuzukiCausalDepthRectangularCaratheodoryGrowth

/-!
# Suzuki rectangular wall-Gram gate

The exact sharp rectangular prime-power cell is the diagonal of a genuine positive wall kernel.
Multiply the observer-free critical wall Gram by the sharp two-edge autocorrelation at its
prime-power log lag.  This produces simultaneously:

* exact compact causal support;
* the von Mangoldt rectangular prime cell on the diagonal;
* the full delayed prime phase on the functional-equation anti-diagonal;
* positive semidefiniteness on every finite height packet.

This also proves a representation no-go.  The Gamma-boundary-paired causal-depth observer
rectangle has strictly positive real part even beyond the sharp wall, whereas the gated wall Gram
is exactly zero there.  Hence that fused observer response cannot be the literal sharp trace cell;
the observer-free quadratic wall source is the correct local arithmetic object.

No RH premise, estimate, numerical computation, infinite prime sum, or endpoint realization is
used.  Global compensation of the negative prime sign by Robin--Gamma--holonomy terms remains
open.
-/

open Complex Set
open scoped ComplexConjugate ComplexOrder

namespace RHTower

noncomputable section

/-! ## Nonnegative sharp gate and local prime cell -/

/-- The four-tent sharp autocorrelation is nonnegative without restrictions on its real
parameters. -/
theorem rectangularTwoEdgeAutocorrelation_nonneg_unconditional (L a h : ℝ) :
    0 ≤ rectangularTwoEdgeAutocorrelation L a h := by
  rw [rectangularTwoEdgeAutocorrelation_eq_four_tents]
  positivity

/-- Sharp rectangular autocorrelation evaluated at one prime-power log lag. -/
def suzukiRectangularWallGramGate
    (L a : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  rectangularTwoEdgeAutocorrelation L a
    (Real.log (xiGammaEulerValuationNat (p, e) : ℝ))

/-- One exact nonnegative von Mangoldt cell in the sharp rectangular prime sum. -/
def suzukiRectangularPrimePowerWallCell
    (L a : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  suzukiRectangularWallGramGate L a p e *
    (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
      Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ))

theorem suzukiRectangularWallGramGate_nonneg
    (L a : ℝ) (p : Nat.Primes) (e : ℕ) :
    0 ≤ suzukiRectangularWallGramGate L a p e := by
  exact rectangularTwoEdgeAutocorrelation_nonneg_unconditional L a _

theorem suzukiRectangularPrimePowerWallCell_nonneg
    (L a : ℝ) (p : Nat.Primes) (e : ℕ) :
    0 ≤ suzukiRectangularPrimePowerWallCell L a p e := by
  exact mul_nonneg (suzukiRectangularWallGramGate_nonneg L a p e)
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))

/-! ## Gated Hermitian wall kernel -/

/-- Sharp autocorrelation-gated observer-free critical wall Gram. -/
def suzukiRectangularWallGramKernel
    (L a t u : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (suzukiRectangularWallGramGate L a p e : ℂ) *
    suzukiCriticalWallFieldGramKernel t u p e

/-- Real sharp gating preserves exact Hermitian height-swap symmetry. -/
theorem star_suzukiRectangularWallGramKernel_swap
    (L a t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    star (suzukiRectangularWallGramKernel L a u t p e) =
      suzukiRectangularWallGramKernel L a t u p e := by
  simp [suzukiRectangularWallGramKernel,
    star_suzukiCriticalWallFieldGramKernel_swap]

/-- The gated wall kernel is the sharp prime cell times the half-log difference character. -/
theorem suzukiRectangularWallGramKernel_eq_differenceCharacter
    (L a t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiRectangularWallGramKernel L a t u p e =
      (suzukiRectangularWallGramGate L a p e : ℂ) *
        (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
        suzukiOscillatoryKernel ((t - u : ℝ) : ℂ)
          (suzukiPrimePowerEntryWallAperture p e) := by
  rw [suzukiRectangularWallGramKernel,
    suzukiCriticalWallFieldGramKernel_eq_differenceCharacter]
  ring

/-- **Exact sharp trace cell.**  Kernel diagonal is literally one nonnegative von Mangoldt
summand in the sharp rectangular prime autocorrelation sum. -/
theorem suzukiRectangularWallGramKernel_diagonal_eq_primeCell
    (L a t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiRectangularWallGramKernel L a t t p e =
      (suzukiRectangularPrimePowerWallCell L a p e : ℂ) := by
  rw [suzukiRectangularWallGramKernel,
    suzukiCriticalWallFieldGramKernel_diagonal]
  simp only [suzukiRectangularPrimePowerWallCell]
  push_cast
  rfl

/-- Functional-equation reflection retains the full delayed prime phase inside the same sharp
positive carrier. -/
theorem suzukiRectangularWallGramKernel_antidiagonal
    (L a t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiRectangularWallGramKernel L a t (-t) p e =
      (suzukiRectangularWallGramGate L a p e : ℂ) *
        ((ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
            Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
          suzukiOscillatoryKernel (t : ℂ)
            (Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) := by
  rw [suzukiRectangularWallGramKernel,
    suzukiCriticalWallFieldGramKernel_antidiagonal]

/-! ## Finite-packet positivity and sharp support -/

/-- Finite height matrix of one sharp gated prime-power wall block. -/
def suzukiRectangularWallGramMatrix {N : ℕ}
    (L a : ℝ) (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  suzukiRectangularWallGramGate L a p e •
    suzukiCriticalWallFieldGramMatrix height p e

/-- Matrix entries are exactly the gated two-height kernel. -/
theorem suzukiRectangularWallGramMatrix_apply {N : ℕ}
    (L a : ℝ) (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ)
    (i j : Fin N) :
    suzukiRectangularWallGramMatrix L a height p e i j =
      suzukiRectangularWallGramKernel L a (height i) (height j) p e := by
  simp only [suzukiRectangularWallGramMatrix, Matrix.smul_apply,
    Complex.real_smul, suzukiRectangularWallGramKernel,
    suzukiCriticalWallFieldGramMatrix]

/-- **Finite-packet PSD.**  Every finite height section of the exact sharp prime-power block is
positive semidefinite. -/
theorem suzukiRectangularWallGramMatrix_posSemidef {N : ℕ}
    (L a : ℝ) (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) :
    (suzukiRectangularWallGramMatrix L a height p e).PosSemidef := by
  exact (suzukiCriticalWallFieldGramMatrix_posSemidef height p e).smul
    (suzukiRectangularWallGramGate_nonneg L a p e)

/-- Beyond the exact rectangular causal wall the complete prime-power block vanishes, including
all heights and phases. -/
theorem suzukiRectangularWallGramKernel_eq_zero_of_two_mul_a_lt
    {L a : ℝ} (p : Nat.Primes) (e : ℕ) (hL : 0 ≤ L) (ha : L ≤ a)
    (hh : 2 * a < Real.log (xiGammaEulerValuationNat (p, e) : ℝ))
    (t u : ℝ) :
    suzukiRectangularWallGramKernel L a t u p e = 0 := by
  rw [suzukiRectangularWallGramKernel, suzukiRectangularWallGramGate,
    rectangularTwoEdgeAutocorrelation_eq_zero_of_two_mul_a_lt hL ha hh]
  norm_num

/-! ## Exact representation no-go and positive survivor -/

/-- **Direct S64 trace-cell no-go.**  Outside sharp prime support, the source-selected fused
observer rectangle still has strictly positive real part while the correct sharp wall cell is
zero.  Thus the fused response cannot be the literal arithmetic trace block. -/
theorem xiGammaBoundary_fusedRectangle_ne_suzukiRectangularWallGramKernel_diagonal
    {h a L : ℝ} (hh : 0 < h) (ha : 0 < a) (hL : 0 < L) (hLa : L ≤ a)
    (t : ℝ) (p : Nat.Primes) (hout : 2 * a < Real.log (p : ℝ)) :
    xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, 0) *
        (suzukiCriticalApertureDepthFusedAtom h (a + L) t p -
          suzukiCriticalApertureDepthFusedAtom h a t p) ≠
      suzukiRectangularWallGramKernel L a t t p 0 := by
  have hpos :=
    re_xiGammaEulerHeightBoundaryFeature_mul_fusedAtom_rectangle_pos hh ha hL t p
  have hzero : suzukiRectangularWallGramKernel L a t t p 0 = 0 := by
    apply suzukiRectangularWallGramKernel_eq_zero_of_two_mul_a_lt p 0 hL.le hLa
    simpa [xiGammaEulerValuationNat] using hout
  intro heq
  rw [hzero] at heq
  have hre := congrArg Complex.re heq
  simp only [Complex.zero_re] at hre
  linarith

end

/-! ## Local positivity is not global positivity

The full formula subtracts twice this block.  A positive semidefinite block entering with a negative
coefficient can destroy positivity outright, so finite-packet positive semidefiniteness of the wall
Gram carries no consequence for the assembled formula.  This is the hostile audit's "global sign not
smuggled", as a theorem. -/

open Matrix in
/-- **Subtracting a positive block can break positivity.**  There are positive semidefinite `S` and
`G` with `S - 2 G` not positive semidefinite, so local positive semidefiniteness never implies
positivity of a formula that subtracts it. -/
theorem exists_posSemidef_sub_two_smul_not_posSemidef :
    ∃ S G : Matrix (Fin 1) (Fin 1) ℝ,
      S.PosSemidef ∧ G.PosSemidef ∧ ¬ (S - (2 : ℝ) • G).PosSemidef := by
  refine ⟨0, 1, Matrix.PosSemidef.zero, Matrix.PosSemidef.one, ?_⟩
  intro hM
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2 (![1] : Fin 1 → ℝ)
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.one_apply] at h

end RHTower
