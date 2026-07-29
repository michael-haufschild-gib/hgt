import GaloisForLFunctions.HTGeometry.TateClockUnilateralShiftDefect
import GaloisForLFunctions.RHTower.PrimeStokesWoldCalderonSuspension
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Common interval character for Tate, Kummer, Wold, and Gamma boundaries

The finite unilateral Tate-clock boundary has one equivariant interval character.  Its augmentation
is the Kummer multiplicity, its modular evaluation is the Wold/BV boundary mass, and its
multiplicative characteristic telescopes to an endpoint determinant ratio.  For two commuting
prime directions, the two ordered edge paths differ by the boundary of one canonical square.

These are the dependency-closed finite algebraic comparison laws.  They do not construct the
source-natural infinite-prime completion, prove strictness of that completion, or prove RH.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Equivariant character of the positively oriented interval with vertices `0, ..., m - 1`. -/
def tateIntervalCharacter {R : Type*} [CommSemiring R]
    (u : R) (m : ℕ) : R :=
  ∑ k ∈ Finset.range m, u ^ k

/-- Concatenating two oriented intervals shifts the character of the second interval by the
length of the first. -/
theorem tateIntervalCharacter_add {R : Type*} [CommSemiring R]
    (u : R) (m n : ℕ) :
    tateIntervalCharacter u (m + n) =
      tateIntervalCharacter u m + u ^ m * tateIntervalCharacter u n := by
  unfold tateIntervalCharacter
  rw [Finset.sum_range_add]
  simp only [pow_add]
  rw [Finset.mul_sum]

/-- The Euler boundary of the interval character is the endpoint difference `1 - u^m`. -/
theorem one_sub_mul_tateIntervalCharacter {R : Type*} [CommRing R]
    (u : R) (m : ℕ) :
    (1 - u) * tateIntervalCharacter u m = 1 - u ^ m := by
  induction m with
  | zero => simp [tateIntervalCharacter]
  | succ m ih =>
      have hsucc :
          tateIntervalCharacter u (m + 1) =
            tateIntervalCharacter u m + u ^ m := by
        rw [tateIntervalCharacter, Finset.sum_range_succ]
        rfl
      rw [hsucc, mul_add, ih, pow_succ]
      ring

/-- Augmentation at the trivial character recovers the integral interval length. -/
theorem tateIntervalCharacter_one {R : Type*} [CommSemiring R] (m : ℕ) :
    tateIntervalCharacter (1 : R) m = m := by
  simp [tateIntervalCharacter]

/-- Finitely supported Tate-clock vector carrying one unit at every vertex of the interval. -/
def tateClockIndUnitInterval (R : Type*) [CommSemiring R]
    (m : ℕ) : ℕ →₀ R :=
  ∑ k ∈ Finset.range m, Finsupp.single k 1

/-- Tate-clock pairing is additive in its finitely supported interval input. -/
theorem tateClockPairing_add
    {R : Type*} [CommSemiring R] (a b : ℕ →₀ R) (p : ℕ → R) :
    tateClockPairing (a + b) p =
      tateClockPairing a p + tateClockPairing b p := by
  simp only [tateClockPairing]
  apply Finsupp.sum_add_index
  · intro n hn
    simp
  · intro n hn x y
    exact add_mul x y (p n)

/-- Evaluating the unit Tate interval against the character `k ↦ u^k` gives its equivariant
interval character. -/
theorem tateClockPairing_unitInterval_eq_character
    {R : Type*} [CommSemiring R] (u : R) (m : ℕ) :
    tateClockPairing (tateClockIndUnitInterval R m) (fun k => u ^ k) =
      tateIntervalCharacter u m := by
  classical
  unfold tateClockIndUnitInterval tateIntervalCharacter
  induction m with
  | zero => simp [tateClockPairing]
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, tateClockPairing_add, ih]
      simp [tateClockPairing]

/-- The trivial Tate-clock character is exactly the Kummer/localization multiplicity. -/
theorem tateClockPairing_unitInterval_one_eq_natCast
    {R : Type*} [CommSemiring R] (m : ℕ) :
    tateClockPairing (tateClockIndUnitInterval R m) (fun _ => 1) = m := by
  rw [show (fun _ : ℕ => (1 : R)) = fun k => (1 : R) ^ k by funext k; simp]
  rw [tateClockPairing_unitInterval_eq_character, tateIntervalCharacter_one]

/-- Linear observation of the first `m` Tate-clock coordinates. -/
def tateClockIndBoundaryCoordinateMap (K : Type*) [Field K] (m : ℕ) :
    (ℕ →₀ K) →ₗ[K] (Fin m → K) where
  toFun a i := a i
  map_add' a b := by
    ext i
    simp
  map_smul' c a := by
    ext i
    simp

/-- Every finite interval coordinate vector lifts to a finitely supported Tate-clock vector. -/
theorem tateClockIndBoundaryCoordinateMap_surjective
    (K : Type*) [Field K] (m : ℕ) :
    Function.Surjective (tateClockIndBoundaryCoordinateMap K m) := by
  intro f
  classical
  let a : ℕ →₀ K :=
    Finsupp.onFinset (Finset.range m)
      (fun n => if hn : n < m then f ⟨n, hn⟩ else 0)
      (by
        intro n hn
        by_cases hnm : n < m
        · exact Finset.mem_range.mpr hnm
        · simp [hnm] at hn)
  refine ⟨a, ?_⟩
  ext i
  simp [tateClockIndBoundaryCoordinateMap, a, i.isLt]

/-- The kernel of finite interval observation is exactly the one-sided tail. -/
theorem tateClockIndBoundaryCoordinateMap_ker
    (K : Type*) [Field K] (m : ℕ) :
    LinearMap.ker (tateClockIndBoundaryCoordinateMap K m) =
      tateClockIndTailSubmodule K m := by
  ext a
  constructor
  · intro ha n hn
    have hfun : tateClockIndBoundaryCoordinateMap K m a = 0 :=
      LinearMap.mem_ker.mp ha
    have hi := congrFun hfun ⟨n, hn⟩
    simpa [tateClockIndBoundaryCoordinateMap] using hi
  · intro ha
    apply LinearMap.mem_ker.mpr
    funext i
    exact ha i i.isLt

/-- **Typed local interval realization.**  The positive Tate clock modulo its `m`th tail is
canonically the `m`-vertex interval representation.  This retains the extension arrows that the
nonequivariant rank and split associated graded forget. -/
noncomputable def tateClockIndTailQuotientEquiv
    (K : Type*) [Field K] (m : ℕ) :
    ((ℕ →₀ K) ⧸ tateClockIndTailSubmodule K m) ≃ₗ[K] (Fin m → K) := by
  rw [← tateClockIndBoundaryCoordinateMap_ker K m]
  exact (tateClockIndBoundaryCoordinateMap K m).quotKerEquivOfSurjective
    (tateClockIndBoundaryCoordinateMap_surjective K m)

/-- Standard basis vector in the finite interval representation. -/
def tateClockFinIntervalBasis
    (K : Type*) [Field K] {m : ℕ} (k : Fin m) : Fin m → K :=
  fun i => if i = k then 1 else 0

/-- Away from the top vertex, the Tate forward shift is exactly the next interval arrow. -/
theorem tateClockIndBoundaryCoordinateMap_forward_single
    (K : Type*) [Field K] {m k : ℕ} (hk : k + 1 < m) :
    tateClockIndBoundaryCoordinateMap K m
        (tateClockIndForward (Finsupp.single k (1 : K))) =
      tateClockFinIntervalBasis K ⟨k + 1, hk⟩ := by
  ext i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      simp [tateClockIndBoundaryCoordinateMap, tateClockFinIntervalBasis]
  | succ i =>
      simp [tateClockIndBoundaryCoordinateMap, tateClockFinIntervalBasis, Fin.ext_iff,
        Finsupp.single_apply, eq_comm]

/-- The top interval vertex shifts into the discarded tail, hence becomes zero in the quotient. -/
theorem tateClockIndBoundaryCoordinateMap_forward_last
    (K : Type*) [Field K] (m : ℕ) :
    tateClockIndBoundaryCoordinateMap K (m + 1)
        (tateClockIndForward (Finsupp.single m (1 : K))) = 0 := by
  ext i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      simp [tateClockIndBoundaryCoordinateMap]
  | succ i =>
      have him : i ≠ m := by omega
      simp [tateClockIndBoundaryCoordinateMap, him]

/-- Multiplicative characteristic obtained by assigning the adjacent ratio
`φ(k) * φ(k + 1)⁻¹` to interval layer `k`. -/
def tateIntervalDeterminant {G : Type*} [CommGroup G]
    (φ : ℕ → G) (m : ℕ) : G :=
  ∏ k ∈ Finset.range m, φ k * (φ (k + 1))⁻¹

/-- The multiplicative interval characteristic telescopes to the ratio of its two endpoint
values.  Taking `φ(k) = Φ(p⁻ᵏ t)` is the nested Gamma determinant formula. -/
theorem tateIntervalDeterminant_eq_boundary_ratio
    {G : Type*} [CommGroup G] (φ : ℕ → G) (m : ℕ) :
    tateIntervalDeterminant φ m = φ 0 * (φ m)⁻¹ := by
  induction m with
  | zero => simp [tateIntervalDeterminant]
  | succ m ih =>
      rw [tateIntervalDeterminant, Finset.prod_range_succ]
      rw [show (∏ k ∈ Finset.range m, φ k * (φ (k + 1))⁻¹) =
          tateIntervalDeterminant φ m by rfl, ih]
      group

/-- Boundary of a two-prime edge chain in the cubical interval model. -/
def primeIntervalEdgeBoundary {R : Type*} [CommRing R]
    (g h : R) (edge : R × R) : R :=
  (1 - g) * edge.1 + (1 - h) * edge.2

/-- Ordered path which traverses the `g` edge and then the translated `h` edge. -/
def primeIntervalPathGH {R : Type*} [CommRing R]
    (g _h : R) : R × R :=
  (1, g)

/-- Ordered path which traverses the `h` edge and then the translated `g` edge. -/
def primeIntervalPathHG {R : Type*} [CommRing R]
    (_g h : R) : R × R :=
  (h, 1)

/-- Cubical boundary of a two-prime square with coefficient `c`. -/
def primeIntervalSquareBoundary {R : Type*} [CommRing R]
    (g h c : R) : R × R :=
  ((1 - h) * c, -((1 - g) * c))

/-- The `g`-then-`h` path has total boundary `1 - gh`. -/
theorem primeIntervalEdgeBoundary_pathGH {R : Type*} [CommRing R]
    (g h : R) :
    primeIntervalEdgeBoundary g h (primeIntervalPathGH g h) = 1 - g * h := by
  simp [primeIntervalEdgeBoundary, primeIntervalPathGH]
  ring

/-- The `h`-then-`g` path has the same total boundary `1 - gh`. -/
theorem primeIntervalEdgeBoundary_pathHG {R : Type*} [CommRing R]
    (g h : R) :
    primeIntervalEdgeBoundary g h (primeIntervalPathHG g h) = 1 - g * h := by
  simp [primeIntervalEdgeBoundary, primeIntervalPathHG]
  ring

/-- The cubical edge boundary annihilates every two-prime square boundary. -/
theorem primeIntervalEdgeBoundary_squareBoundary {R : Type*} [CommRing R]
    (g h c : R) :
    primeIntervalEdgeBoundary g h (primeIntervalSquareBoundary g h c) = 0 := by
  simp [primeIntervalEdgeBoundary, primeIntervalSquareBoundary]
  ring

/-- Prime-order discrepancy is exactly the boundary of the canonical square, rather than an
uncontrolled choice of ordering. -/
theorem primeIntervalPaths_sub_eq_squareBoundary {R : Type*} [CommRing R]
    (g h : R) :
    primeIntervalPathGH g h - primeIntervalPathHG g h =
      primeIntervalSquareBoundary g h 1 := by
  ext <;> simp [primeIntervalPathGH, primeIntervalPathHG, primeIntervalSquareBoundary]

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Wold cells are the modular evaluation of the same Tate interval character. -/
theorem unitExponentialWoldCells_eq_intervalCharacter
    {q : ℝ} (hq : 0 < q) (m : ℕ) :
    ∑ k ∈ Finset.range m, unitExponentialWoldCellMass (Real.log q) k =
      (1 - q⁻¹) * tateIntervalCharacter q⁻¹ m := by
  rw [tateIntervalCharacter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [unitExponentialWoldCellMass_log hq]

/-- The Wold/BV modular evaluation of an interval is its endpoint Euler defect
`1 - (q⁻¹)^m`. -/
theorem unitExponentialWoldCells_eq_intervalBoundary
    {q : ℝ} (hq : 0 < q) (m : ℕ) :
    ∑ k ∈ Finset.range m, unitExponentialWoldCellMass (Real.log q) k =
      1 - (q⁻¹) ^ m := by
  rw [unitExponentialWoldCells_eq_intervalCharacter hq]
  exact one_sub_mul_tateIntervalCharacter q⁻¹ m

end RHTower
