import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPageTransition
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Fintype.Powerset

/-!
# Critical projective-horizon multiplicity

At the finite-jet Page resolution `N=m+n-1`, the scalar raw/reciprocal observation map is
generically finite.  Its compactified fiber is the intersection of `m+n` divisors of bidegree
`(1,1)` in `P^m × P^n`, so its intersection number is `choose (m+n) m`.

This file verifies the two exact algebraic cores used by that paper theorem:

* the top Chow coefficient of `(H₁+H₂)^(m+n)` is the binomial coefficient;
* truncated convolution cannot acquire a projective solution at infinity when the first prescribed
  tail coefficient is nonzero.  The latter follows from the multiplicativity of polynomial
  trailing degree and is formalized as an explicit surviving coefficient below order `m+n`.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- The decomposable tensor attached to two projective low-jet parameter vectors. Its projective
image is the Segre variety underlying the critical horizon compactification. -/
def criticalHorizonSegreTensor {K : Type*} [CommSemiring K] {I J : Type*}
    (a : I → K) (b : J → K) : Matrix I J K := fun i j => a i * b j

/-- Every `2×2` minor of the critical outer tensor vanishes: it is a rank-one tensor. -/
theorem criticalHorizonSegreTensor_twoByTwoMinor_eq_zero
    {K : Type*} [CommRing K] {I J : Type*}
    (a : I → K) (b : J → K) (i i' : I) (j j' : J) :
    criticalHorizonSegreTensor a b i j * criticalHorizonSegreTensor a b i' j' -
      criticalHorizonSegreTensor a b i j' * criticalHorizonSegreTensor a b i' j = 0 := by
  simp only [criticalHorizonSegreTensor]
  ring

/-- Linear pairing with an ambient tensor. -/
def criticalHorizonMatrixPairing {K : Type*} [CommSemiring K] {I J : Type*}
    [Fintype I] [Fintype J] (c : Matrix I J K) : Matrix I J K →ₗ[K] K where
  toFun M := ∑ i, ∑ j, c i j * M i j
  map_add' M N := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r M := by simp [mul_left_comm, Finset.mul_sum]

/-- Bilinear compatibility constraint on the two projective parameter vectors. -/
def criticalHorizonBilinearConstraint {K : Type*} [CommSemiring K] {I J : Type*}
    [Fintype I] [Fintype J] (c : Matrix I J K) (a : I → K) (b : J → K) : K :=
  ∑ i, ∑ j, c i j * a i * b j

/-- Every critical bilinear compatibility equation is the restriction of a linear hyperplane to
the Segre rank-one locus. -/
theorem criticalHorizonBilinearConstraint_eq_matrixPairing_segreTensor
    {K : Type*} [CommSemiring K] {I J : Type*}
    [Fintype I] [Fintype J] (c : Matrix I J K) (a : I → K) (b : J → K) :
    criticalHorizonBilinearConstraint c a b =
      criticalHorizonMatrixPairing c (criticalHorizonSegreTensor a b) := by
  simp [criticalHorizonBilinearConstraint, criticalHorizonMatrixPairing,
    criticalHorizonSegreTensor, mul_assoc]

/-- If the first factor has degree below `m` and the second has a nonzero `n`th coefficient, their
product has a nonzero coefficient strictly below `m+n`.  This is the left-boundary exclusion in
the biprojective compactification of a critical reciprocal-jet fiber. -/
theorem exists_low_mul_coeff_ne_zero {K : Type*} [Field K]
    {p q : K[X]} {m n : ℕ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpdeg : p.natDegree < m) (hqn : q.coeff n ≠ 0) :
    ∃ k < m + n, (p * q).coeff k ≠ 0 := by
  let k := p.natTrailingDegree + q.natTrailingDegree
  refine ⟨k, ?_, ?_⟩
  · have hpbound := p.natTrailingDegree_le_natDegree
    have hqbound := q.natTrailingDegree_le_of_ne_zero hqn
    omega
  · dsimp [k]
    rw [coeff_mul_natTrailingDegree_add_natTrailingDegree]
    exact mul_ne_zero
      (trailingCoeff_nonzero_iff_nonzero.mpr hp)
      (trailingCoeff_nonzero_iff_nonzero.mpr hq)

/-- A low-degree nonzero factor and a factor with a marked nonzero `n`th coefficient cannot have
zero truncated product through order `m+n-1`.  The marked coefficient supplies the nonzeroness of
the second factor. -/
theorem not_all_low_mul_coeff_zero_of_coeff_ne_zero {K : Type*} [Field K]
    {p q : K[X]} {m n : ℕ} (hp : p ≠ 0)
    (hpdeg : p.natDegree < m) (hqn : q.coeff n ≠ 0) :
    ¬ ∀ k < m + n, (p * q).coeff k = 0 := by
  have hq : q ≠ 0 := by
    intro hq
    exact hqn (by simp [hq])
  intro hzero
  obtain ⟨k, hk, hne⟩ := exists_low_mul_coeff_ne_zero hp hq hpdeg hqn
  exact hne (hzero k hk)

/-- Compatibility form with the formerly explicit, now redundant, second-factor premise. -/
theorem not_all_low_mul_coeff_zero {K : Type*} [Field K]
    {p q : K[X]} {m n : ℕ} (hp : p ≠ 0) (_hq : q ≠ 0)
    (hpdeg : p.natDegree < m) (hqn : q.coeff n ≠ 0) :
    ¬ ∀ k < m + n, (p * q).coeff k = 0 :=
  not_all_low_mul_coeff_zero_of_coeff_ne_zero hp hpdeg hqn

/-- If both factors have complementary low-degree bounds, their product already survives below the
critical truncation.  This excludes the corner where both projective homogenizing coordinates
vanish. -/
theorem exists_low_mul_coeff_ne_zero_of_natDegree_lt {K : Type*} [Field K]
    {p q : K[X]} {m n : ℕ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpdeg : p.natDegree < m) (hqdeg : q.natDegree < n) :
    ∃ k < m + n, (p * q).coeff k ≠ 0 := by
  let k := p.natTrailingDegree + q.natTrailingDegree
  refine ⟨k, ?_, ?_⟩
  · have hpbound := p.natTrailingDegree_le_natDegree
    have hqbound := q.natTrailingDegree_le_natDegree
    omega
  · dsimp [k]
    rw [coeff_mul_natTrailingDegree_add_natTrailingDegree]
    exact mul_ne_zero
      (trailingCoeff_nonzero_iff_nonzero.mpr hp)
      (trailingCoeff_nonzero_iff_nonzero.mpr hq)

/-- The critical raw/reciprocal horizon intersection number. -/
def criticalHorizonMultiplicity (m n : ℕ) : ℕ := (m + n).choose m

/-- The top bidegree coefficient of `m+n` `(1,1)` divisors is the critical horizon multiplicity. -/
theorem criticalHorizonMultiplicity_eq_chowCoefficient (m n : ℕ) :
    ((X + 1) ^ (m + n) : ℤ[X]).coeff m = criticalHorizonMultiplicity m n := by
  simp [criticalHorizonMultiplicity, Polynomial.coeff_X_add_one_pow]

/-- Every critical horizon multiplicity is positive. -/
theorem criticalHorizonMultiplicity_pos (m n : ℕ) :
    0 < criticalHorizonMultiplicity m n := by
  simp [criticalHorizonMultiplicity, Nat.choose_pos]

/-- Exchanging the two horizon depths does not change the critical multiplicity. -/
theorem criticalHorizonMultiplicity_comm (m n : ℕ) :
    criticalHorizonMultiplicity m n = criticalHorizonMultiplicity n m := by
  simpa [criticalHorizonMultiplicity, Nat.add_comm] using
    (Nat.choose_symm_add (a := m) (b := n))

/-- Schubert cells of `Gr(m,m+n)`, indexed combinatorially by the `m`-subsets of an
`(m+n)`-element set. -/
abbrev criticalHorizonSchubertCell (m n : ℕ) :=
  {s : Finset (Fin (m + n)) // s.card = m}

/-- The critical horizon multiplicity is exactly the number of Schubert-cell indices. -/
theorem card_criticalHorizonSchubertCell (m n : ℕ) :
    Fintype.card (criticalHorizonSchubertCell m n) =
      criticalHorizonMultiplicity m n := by
  simp [criticalHorizonMultiplicity]

/-- Every genuinely two-sided critical horizon has at least six states.  Thus, once full symmetric
monodromy is known, all such generic reconstruction problems lie beyond the radical-solvable
degrees. -/
theorem criticalHorizonMultiplicity_ge_six {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    6 ≤ criticalHorizonMultiplicity m n := by
  rw [criticalHorizonMultiplicity]
  calc
    6 = Nat.choose 4 2 := by decide
    _ ≤ Nat.choose (m + 2) 2 := Nat.choose_le_choose 2 (by omega)
    _ = Nat.choose (m + 2) m := (Nat.choose_symm_add (a := m) (b := 2)).symm
    _ ≤ Nat.choose (m + n) m := Nat.choose_le_choose m (by omega)

end GaloisForLFunctions.HTGeometry
