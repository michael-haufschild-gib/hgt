import GaloisForLFunctions.HTGeometry.TateClockUnilateralShiftDefect
import GaloisForLFunctions.HTGeometry.NodalChargeCharacterRealization
import GaloisForLFunctions.RHTower.PrimeStokesWoldCalderonSuspension
import GaloisForLFunctions.RHTower.SigmaDivisorJet
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
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
    ((ℕ →₀ K) ⧸ tateClockIndTailSubmodule K m) ≃ₗ[K] (Fin m → K) :=
  (Submodule.quotEquivOfEq
      (tateClockIndTailSubmodule K m)
      (LinearMap.ker (tateClockIndBoundaryCoordinateMap K m))
      (tateClockIndBoundaryCoordinateMap_ker K m).symm).trans
    ((tateClockIndBoundaryCoordinateMap K m).quotKerEquivOfSurjective
      (tateClockIndBoundaryCoordinateMap_surjective K m))

/-- The typed Tate-tail equivalence is induced by finite boundary coordinates. -/
theorem tateClockIndTailQuotientEquiv_mk
    (K : Type*) [Field K] (m : ℕ) (a : ℕ →₀ K) :
    tateClockIndTailQuotientEquiv K m (Submodule.Quotient.mk a) =
      tateClockIndBoundaryCoordinateMap K m a := by
  simp [tateClockIndTailQuotientEquiv, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Standard basis vector in the finite interval representation. -/
def tateClockFinIntervalBasis
    (K : Type*) [Field K] {m : ℕ} (k : Fin m) : Fin m → K :=
  fun i => if i = k then 1 else 0

/-- Linear observation of the first `m` coefficients of a polynomial local divisor model. -/
def localDivisorJetBoundaryCoordinateMap (K : Type*) [Field K] (m : ℕ) :
    Polynomial K →ₗ[K] (Fin m → K) where
  toFun P i := P.coeff i
  map_add' P Q := by
    ext i
    simp
  map_smul' c P := by
    ext i
    simp

/-- Every finite local divisor-jet coordinate vector has a polynomial representative. -/
theorem localDivisorJetBoundaryCoordinateMap_surjective
    (K : Type*) [Field K] (m : ℕ) :
    Function.Surjective (localDivisorJetBoundaryCoordinateMap K m) := by
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
  let P : Polynomial K :=
    Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff a)
  refine ⟨P, ?_⟩
  ext i
  simp [localDivisorJetBoundaryCoordinateMap, P, a, i.isLt]

/-- The kernel of finite coefficient observation is the scalar restriction of `(X^m)`. -/
theorem localDivisorJetBoundaryCoordinateMap_ker
    (K : Type*) [Field K] (m : ℕ) :
    LinearMap.ker (localDivisorJetBoundaryCoordinateMap K m) =
      (RHTower.jetIdeal K m).restrictScalars K := by
  ext P
  constructor
  · intro hP
    change P ∈ RHTower.jetIdeal K m
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (RHTower.jetClass_eq_zero_iff_coeff_lt_eq_zero K m).mpr
    intro j hj
    have hfun : localDivisorJetBoundaryCoordinateMap K m P = 0 :=
      LinearMap.mem_ker.mp hP
    have hi := congrFun hfun ⟨j, hj⟩
    simpa [localDivisorJetBoundaryCoordinateMap] using hi
  · intro hP
    apply LinearMap.mem_ker.mpr
    funext i
    have hzero : RHTower.jetClass K m P = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hP
    exact (RHTower.jetClass_eq_zero_iff_coeff_lt_eq_zero K m).mp hzero i i.isLt

/-- Restriction of scalars identifies an ideal-quotient representative with the same
submodule-quotient representative. -/
theorem restrictScalarsEquiv_symm_jetIdeal_mk
    (K : Type*) [Field K] (m : ℕ) (P : Polynomial K) :
    (Submodule.Quotient.restrictScalarsEquiv K (RHTower.jetIdeal K m)).symm
        (Ideal.Quotient.mk (RHTower.jetIdeal K m) P) =
      Submodule.Quotient.mk P := by
  rfl

/-- **Kummer-to-interval comparison.**  The actual local divisor-jet algebra
`K[X]/(X^m)`, after forgetting multiplication, is canonically the same `m`-vertex interval
representation as the Tate tail quotient. -/
noncomputable def localDivisorJetEquivFiniteInterval
    (K : Type*) [Field K] (m : ℕ) :
    RHTower.LocalDivisorJet K m ≃ₗ[K] (Fin m → K) :=
  let restrictEquiv : RHTower.LocalDivisorJet K m ≃ₗ[K]
      ((Polynomial K) ⧸ (RHTower.jetIdeal K m).restrictScalars K) :=
    (Submodule.Quotient.restrictScalarsEquiv K (RHTower.jetIdeal K m)).symm
  let kernelEquiv :
      ((Polynomial K) ⧸ (RHTower.jetIdeal K m).restrictScalars K) ≃ₗ[K]
        (Fin m → K) :=
    (Submodule.quotEquivOfEq
        ((RHTower.jetIdeal K m).restrictScalars K)
        (LinearMap.ker (localDivisorJetBoundaryCoordinateMap K m))
        (localDivisorJetBoundaryCoordinateMap_ker K m).symm).trans
      ((localDivisorJetBoundaryCoordinateMap K m).quotKerEquivOfSurjective
        (localDivisorJetBoundaryCoordinateMap_surjective K m))
  restrictEquiv.trans kernelEquiv

/-- The Kummer-to-interval comparison is induced by the coefficients below multiplicity `m`. -/
theorem localDivisorJetEquivFiniteInterval_jetClass
    (K : Type*) [Field K] (m : ℕ) (P : Polynomial K) :
    localDivisorJetEquivFiniteInterval K m (RHTower.jetClass K m P) =
      localDivisorJetBoundaryCoordinateMap K m P := by
  simp [localDivisorJetEquivFiniteInterval, RHTower.jetClass,
    restrictScalarsEquiv_symm_jetIdeal_mk, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- A local Kummer monomial `X^k`, for `k < m`, is the `k`th interval vertex. -/
theorem localDivisorJetBoundaryCoordinateMap_X_pow
    (K : Type*) [Field K] {m : ℕ} (k : Fin m) :
    localDivisorJetBoundaryCoordinateMap K m
        ((Polynomial.X : Polynomial K) ^ k.1) =
      tateClockFinIntervalBasis K k := by
  ext i
  simp [localDivisorJetBoundaryCoordinateMap, tateClockFinIntervalBasis,
    Polynomial.coeff_X_pow, Fin.ext_iff]

/-- Canonical typed comparison between a local Kummer divisor jet and the Tate-clock tail
quotient.  Both sides retain the interval extension arrows erased by rank. -/
noncomputable def localDivisorJetEquivTateClockTailQuotient
    (K : Type*) [Field K] (m : ℕ) :
    RHTower.LocalDivisorJet K m ≃ₗ[K]
      ((ℕ →₀ K) ⧸ tateClockIndTailSubmodule K m) :=
  (localDivisorJetEquivFiniteInterval K m).trans
    (tateClockIndTailQuotientEquiv K m).symm

/-- Under the typed Kummer-to-Tate comparison, the monomial `X^k` is the clock point mass at
the same interval vertex. -/
theorem localDivisorJetEquivTateClockTailQuotient_jetClass_X_pow
    (K : Type*) [Field K] {m : ℕ} (k : Fin m) :
    localDivisorJetEquivTateClockTailQuotient K m
        (RHTower.jetClass K m ((Polynomial.X : Polynomial K) ^ k.1)) =
      Submodule.Quotient.mk (Finsupp.single k.1 (1 : K)) := by
  apply (tateClockIndTailQuotientEquiv K m).injective
  change
    tateClockIndTailQuotientEquiv K m
        ((tateClockIndTailQuotientEquiv K m).symm
          (localDivisorJetEquivFiniteInterval K m
            (RHTower.jetClass K m ((Polynomial.X : Polynomial K) ^ k.1)))) =
      tateClockIndTailQuotientEquiv K m
        (Submodule.Quotient.mk (Finsupp.single k.1 (1 : K)))
  rw [LinearEquiv.apply_symm_apply,
    localDivisorJetEquivFiniteInterval_jetClass,
    localDivisorJetBoundaryCoordinateMap_X_pow,
    tateClockIndTailQuotientEquiv_mk]
  ext i
  simp [tateClockIndBoundaryCoordinateMap, tateClockFinIntervalBasis,
    Finsupp.single_apply, Fin.ext_iff, eq_comm]

/-- Nilpotent forward arrow on the `(m+1)`-vertex interval representation. -/
def tateClockFinIntervalForward (K : Type*) [Field K] (m : ℕ) :
    (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) → K) where
  toFun f := Fin.cases 0 (fun i => f i.castSucc)
  map_add' f g := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  map_smul' c f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

/-- Evaluation of the finite forward arrow at the top vertex. -/
theorem tateClockFinIntervalForward_last
    (K : Type*) [Field K] (m : ℕ) (f : Fin (m + 2) → K) :
    tateClockFinIntervalForward K (m + 1) f (Fin.last (m + 1)) =
      f (Fin.last m).castSucc := by
  rw [← Fin.succ_last]
  rfl

/-- Cofinal inclusion which appends a zero top coordinate to a finite interval. -/
def tateClockFinIntervalInclusion
    (K : Type*) [Field K] (m : ℕ) :
    (Fin m → K) →ₗ[K] (Fin (m + 1) → K) where
  toFun f i := if hi : i.1 < m then f ⟨i.1, hi⟩ else 0
  map_add' f g := by
    funext i
    by_cases hi : i.1 < m
    · simp [hi]
    · simp [hi]
  map_smul' c f := by
    funext i
    by_cases hi : i.1 < m
    · simp [hi]
    · simp [hi]

/-- Rank-one top boundary created when the forward arrow exits a finite interval stage. -/
def tateClockFinIntervalTopBoundary
    (K : Type*) [Field K] (m : ℕ) :
    (Fin (m + 1) → K) →ₗ[K] (Fin (m + 2) → K) where
  toFun f i :=
    if i = Fin.last (m + 1) then f (Fin.last m) else 0
  map_add' f g := by
    funext i
    by_cases hi : i = Fin.last (m + 1)
    · simp [hi]
    · simp [hi]
  map_smul' c f := by
    funext i
    by_cases hi : i = Fin.last (m + 1)
    · simp [hi]
    · simp [hi]

/-- The outgoing top vertex of one stage is the new top vertex of the next stage. -/
theorem tateClockFinIntervalTopBoundary_basis_last
    (K : Type*) [Field K] (m : ℕ) :
    tateClockFinIntervalTopBoundary K m
        (tateClockFinIntervalBasis K (Fin.last m)) =
      tateClockFinIntervalBasis K (Fin.last (m + 1)) := by
  funext i
  simp [tateClockFinIntervalTopBoundary, tateClockFinIntervalBasis, Fin.ext_iff]

/-- The cofinal top-boundary class is nonzero at every finite stage. -/
theorem tateClockFinIntervalTopBoundary_basis_last_ne_zero
    (K : Type*) [Field K] (m : ℕ) :
    tateClockFinIntervalTopBoundary K m
        (tateClockFinIntervalBasis K (Fin.last m)) ≠ 0 := by
  rw [tateClockFinIntervalTopBoundary_basis_last]
  intro h
  have hlast := congrFun h (Fin.last (m + 1))
  have hlast' : (1 : K) = 0 := by
    simpa only [tateClockFinIntervalBasis, if_pos, Pi.zero_apply] using hlast
  exact one_ne_zero hlast'

/-- **Cofinal Bockstein generator.**  Finite nilpotent forward arrows do not form a morphism of
the interval direct system.  Their naturality defect is exactly the rank-one top boundary. -/
theorem tateClockFinIntervalForward_inclusion_defect
    (K : Type*) [Field K] (m : ℕ) (f : Fin (m + 1) → K) :
    tateClockFinIntervalForward K (m + 1)
        (tateClockFinIntervalInclusion K (m + 1) f) =
      tateClockFinIntervalInclusion K (m + 1)
          (tateClockFinIntervalForward K m f) +
        tateClockFinIntervalTopBoundary K m f := by
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      simp [tateClockFinIntervalForward, tateClockFinIntervalInclusion,
        tateClockFinIntervalTopBoundary]
  | succ i =>
      by_cases him : i < m
      · have himle : i ≤ m := by omega
        have hine : i ≠ m := by omega
        simp [tateClockFinIntervalForward, tateClockFinIntervalInclusion,
          tateClockFinIntervalTopBoundary, him, himle, hine, Fin.ext_iff]
      · have hieq : i = m := by omega
        subst i
        have htop :
            (⟨m + 1, hi⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
          apply Fin.ext
          rfl
        rw [htop, tateClockFinIntervalForward_last]
        simp [tateClockFinIntervalForward, tateClockFinIntervalInclusion,
          tateClockFinIntervalTopBoundary, Fin.ext_iff]
        congr 1

/-- Multiplication by the local parameter `X` is the nilpotent forward interval arrow. -/
theorem localDivisorJetBoundaryCoordinateMap_X_mul_intertwines
    (K : Type*) [Field K] (m : ℕ) (P : Polynomial K) :
    localDivisorJetBoundaryCoordinateMap K (m + 1)
        ((Polynomial.X : Polynomial K) * P) =
      tateClockFinIntervalForward K m
        (localDivisorJetBoundaryCoordinateMap K (m + 1) P) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [localDivisorJetBoundaryCoordinateMap, tateClockFinIntervalForward]
  · simp [localDivisorJetBoundaryCoordinateMap, tateClockFinIntervalForward,
      Polynomial.coeff_X_mul]

/-- The unilateral Tate-clock shift is the same nilpotent forward interval arrow. -/
theorem tateClockIndBoundaryCoordinateMap_forward_intertwines
    (K : Type*) [Field K] (m : ℕ) (a : ℕ →₀ K) :
    tateClockIndBoundaryCoordinateMap K (m + 1)
        (tateClockIndForward a) =
      tateClockFinIntervalForward K m
        (tateClockIndBoundaryCoordinateMap K (m + 1) a) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [tateClockIndBoundaryCoordinateMap, tateClockFinIntervalForward]
  · simp [tateClockIndBoundaryCoordinateMap, tateClockFinIntervalForward]

/-- The Kummer comparison intertwines multiplication by `X` with the common forward interval
arrow for every local polynomial, not only on basis vectors. -/
theorem localDivisorJetEquivFiniteInterval_X_mul_intertwines
    (K : Type*) [Field K] (m : ℕ) (P : Polynomial K) :
    localDivisorJetEquivFiniteInterval K (m + 1)
        (RHTower.jetClass K (m + 1) ((Polynomial.X : Polynomial K) * P)) =
      tateClockFinIntervalForward K m
        (localDivisorJetEquivFiniteInterval K (m + 1)
          (RHTower.jetClass K (m + 1) P)) := by
  rw [localDivisorJetEquivFiniteInterval_jetClass,
    localDivisorJetEquivFiniteInterval_jetClass,
    localDivisorJetBoundaryCoordinateMap_X_mul_intertwines]

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

/-- Analytic realization of the `m`-vertex interval by the nonnegative nodal charge modes
`ℓ₀, ..., ℓₘ₋₁` on the face selected by period `ω`. -/
def nodalIntervalSynthesis (ω : ℂ) (m : ℕ) :
    (Fin m → ℂ) →ₗ[ℂ] (ℂ → ℂ) :=
  Fintype.linearCombination ℂ
    (fun k : Fin m => nodalChargeMode ω (k.1 : ℤ))

/-- The finite nonnegative nodal charge packet is linearly independent on every nonzero
period face. -/
theorem nodalIntervalModes_linearIndependent
    (ω : ℂ) (hω : ω ≠ 0) (m : ℕ) :
    LinearIndependent ℂ
      (fun k : Fin m => nodalChargeMode ω (k.1 : ℤ)) := by
  apply nodalChargeModes_linearIndependent ω hω
  intro i j hij
  apply Fin.ext
  exact Int.ofNat_inj.mp hij

/-- No interval coordinate is lost by the analytic nodal receiver. -/
theorem nodalIntervalSynthesis_injective
    (ω : ℂ) (hω : ω ≠ 0) (m : ℕ) :
    Function.Injective (nodalIntervalSynthesis ω m) := by
  rw [nodalIntervalSynthesis,
    ← Finsupp.linearCombination_eq_fintype_linearCombination]
  exact
    ((linearIndependent_iff_injective_finsuppLinearCombination.mp
      (nodalIntervalModes_linearIndependent ω hω m)).comp
        (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin m)).symm.injective)

/-- The standard interval basis is the corresponding `Pi.single`. -/
theorem tateClockFinIntervalBasis_eq_piSingle
    {m : ℕ} (k : Fin m) :
    tateClockFinIntervalBasis ℂ k = Pi.single k 1 := by
  funext i
  simp [tateClockFinIntervalBasis, Pi.single_apply]

/-- The `k`th interval vertex is realized by the analytic nodal mode of charge `k`. -/
theorem nodalIntervalSynthesis_basis
    (ω : ℂ) {m : ℕ} (k : Fin m) :
    nodalIntervalSynthesis ω m (tateClockFinIntervalBasis ℂ k) =
      nodalChargeMode ω (k.1 : ℤ) := by
  rw [tateClockFinIntervalBasis_eq_piSingle,
    nodalIntervalSynthesis, Fintype.linearCombination_apply_single]
  simp

/-- The nonzero cofinal top boundary is realized analytically as the first charge mode outside
the smaller interval stage. -/
theorem nodalIntervalSynthesis_topBoundary_basis_last
    (ω : ℂ) (m : ℕ) :
    nodalIntervalSynthesis ω (m + 2)
        (tateClockFinIntervalTopBoundary ℂ m
          (tateClockFinIntervalBasis ℂ (Fin.last m))) =
      nodalChargeMode ω ((m + 1 : ℕ) : ℤ) := by
  rw [tateClockFinIntervalTopBoundary_basis_last,
    nodalIntervalSynthesis_basis]
  rfl

/-- Every analytically synthesized interval vector is killed by the selected face operator
`T_ω - 1`. -/
theorem nodalIntervalSynthesis_periodic
    (ω : ℂ) (hω : ω ≠ 0) (m : ℕ) (f : Fin m → ℂ) :
    Function.Periodic (nodalIntervalSynthesis ω m f) ω := by
  intro z
  rw [nodalIntervalSynthesis, Fintype.linearCombination_apply]
  change
    (∑ i, f i • nodalChargeMode ω (i.1 : ℤ)) (z + ω) =
      (∑ i, f i • nodalChargeMode ω (i.1 : ℤ)) z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [nodalChargeMode_periodic ω hω (i.1 : ℤ) z]

/-- **Typed Kummer-to-analytic comparison.**  The complete local divisor jet maps into the
analytic nodal receiver by sending `X^k` to charge mode `ℓ_k`. -/
def localDivisorJetNodalIntervalRealization
    (ω : ℂ) (m : ℕ) :
    RHTower.LocalDivisorJet ℂ m →ₗ[ℂ] (ℂ → ℂ) :=
  (nodalIntervalSynthesis ω m).comp
    (localDivisorJetEquivFiniteInterval ℂ m).toLinearMap

/-- The analytic nodal receiver retains every local divisor-jet class on a nonzero period
face. -/
theorem localDivisorJetNodalIntervalRealization_injective
    (ω : ℂ) (hω : ω ≠ 0) (m : ℕ) :
    Function.Injective (localDivisorJetNodalIntervalRealization ω m) :=
  (nodalIntervalSynthesis_injective ω hω m).comp
    (localDivisorJetEquivFiniteInterval ℂ m).injective

/-- A Kummer monomial `X^k` is exactly the analytic nodal mode of the same charge. -/
theorem localDivisorJetNodalIntervalRealization_X_pow
    (ω : ℂ) {m : ℕ} (k : Fin m) :
    localDivisorJetNodalIntervalRealization ω m
        (RHTower.jetClass ℂ m ((Polynomial.X : Polynomial ℂ) ^ k.1)) =
      nodalChargeMode ω (k.1 : ℤ) := by
  rw [localDivisorJetNodalIntervalRealization, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, localDivisorJetEquivFiniteInterval_jetClass,
    localDivisorJetBoundaryCoordinateMap_X_pow,
    nodalIntervalSynthesis_basis]

/-- Every local divisor jet is realized inside the kernel of the selected Barnes face
translation `T_ω - 1`. -/
theorem localDivisorJetNodalIntervalRealization_periodic
    (ω : ℂ) (hω : ω ≠ 0) (m : ℕ) (x : RHTower.LocalDivisorJet ℂ m) :
    Function.Periodic
      (localDivisorJetNodalIntervalRealization ω m x) ω := by
  exact nodalIntervalSynthesis_periodic ω hω m
    (localDivisorJetEquivFiniteInterval ℂ m x)

/-- Multiplication by the charge-one mode advances every nonnegative nodal charge by one. -/
theorem nodalChargeMode_one_mul_nat
    (ω z : ℂ) (k : ℕ) :
    nodalChargeMode ω 1 z * nodalChargeMode ω (k : ℤ) z =
      nodalChargeMode ω ((k + 1 : ℕ) : ℤ) z := by
  rw [nodalChargeMode, nodalChargeMode, nodalChargeMode,
    physicalExponentialMode, physicalExponentialMode, physicalExponentialMode,
    ← Complex.exp_add]
  congr 1
  simp [nodalChargeFrequency]
  ring

/-- **Exact finite leakage law.**  Multiplying an `m+1`-mode analytic packet by the
charge-one mode agrees with the truncated forward shift plus exactly the first excluded charge
mode.  Thus finite nilpotence is caused by discarding a canonical boundary class, not by
vanishing of the analytic mode. -/
theorem nodalIntervalSynthesis_forward_leakage
    (ω : ℂ) (m : ℕ) (f : Fin (m + 1) → ℂ) (z : ℂ) :
    nodalChargeMode ω 1 z * nodalIntervalSynthesis ω (m + 1) f z =
      nodalIntervalSynthesis ω (m + 1) (tateClockFinIntervalForward ℂ m f) z +
        f (Fin.last m) * nodalChargeMode ω ((m + 1 : ℕ) : ℤ) z := by
  simp only [nodalIntervalSynthesis, Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  calc
    nodalChargeMode ω 1 z *
          ∑ i : Fin (m + 1), f i * nodalChargeMode ω (i.1 : ℤ) z =
        ∑ i : Fin (m + 1),
          f i * (nodalChargeMode ω 1 z * nodalChargeMode ω (i.1 : ℤ) z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ i : Fin (m + 1),
          f i * nodalChargeMode ω ((i.1 + 1 : ℕ) : ℤ) z := by
            apply Finset.sum_congr rfl
            intro i _
            rw [nodalChargeMode_one_mul_nat]
    _ = (∑ i : Fin m,
          f i.castSucc * nodalChargeMode ω ((i.1 + 1 : ℕ) : ℤ) z) +
          f (Fin.last m) * nodalChargeMode ω ((m + 1 : ℕ) : ℤ) z := by
            rw [Fin.sum_univ_castSucc]
            rfl
    _ = (∑ i : Fin (m + 1),
          tateClockFinIntervalForward ℂ m f i *
            nodalChargeMode ω (i.1 : ℤ) z) +
          f (Fin.last m) * nodalChargeMode ω ((m + 1 : ℕ) : ℤ) z := by
            rw [Fin.sum_univ_succ]
            simp [tateClockFinIntervalForward]

/-- **Kummer leakage is the next analytic charge.**  Multiplication by `X` in the truncated
local divisor algebra differs from multiplication by the analytic charge-one mode by the top
coefficient times the first mode excluded from the jet. -/
theorem localDivisorJetNodalIntervalRealization_X_mul_leakage
    (ω : ℂ) (m : ℕ) (P : Polynomial ℂ) (z : ℂ) :
    nodalChargeMode ω 1 z *
        localDivisorJetNodalIntervalRealization ω (m + 1)
          (RHTower.jetClass ℂ (m + 1) P) z =
      localDivisorJetNodalIntervalRealization ω (m + 1)
          (RHTower.jetClass ℂ (m + 1)
            ((Polynomial.X : Polynomial ℂ) * P)) z +
        P.coeff m * nodalChargeMode ω ((m + 1 : ℕ) : ℤ) z := by
  change
    nodalChargeMode ω 1 z *
        nodalIntervalSynthesis ω (m + 1)
          (localDivisorJetBoundaryCoordinateMap ℂ (m + 1) P) z =
      nodalIntervalSynthesis ω (m + 1)
          (localDivisorJetBoundaryCoordinateMap ℂ (m + 1)
            ((Polynomial.X : Polynomial ℂ) * P)) z +
        P.coeff m * nodalChargeMode ω ((m + 1 : ℕ) : ℤ) z
  rw [localDivisorJetBoundaryCoordinateMap_X_mul_intertwines]
  exact nodalIntervalSynthesis_forward_leakage ω m
    (localDivisorJetBoundaryCoordinateMap ℂ (m + 1) P) z

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
