import Mathlib.Combinatorics.Colex
import Mathlib.Tactic

/-!
# Explicit two-local isolation of every Boolean spectral edge

For a distinguished Boolean degree of freedom and an arbitrary environment
configuration `z₀`, this file constructs an explicit diagonal star
Hamiltonian whose only repeated energy is the pair obtained by flipping the
distinguished degree of freedom above `z₀`.

The construction replaces generic finite-hyperplane avoidance by a binary
separation formula.  The environment disagreement pattern is encoded as an
integer `c < 2^m`.  One distinguished layer has energy `c`; the other has
energy `2^m c`.  Their positive ranges are disjoint, while both vanish at
exactly the selected environment.  An explicit affine-plus-bilinear
decomposition proves that the energy uses only onsite and distinguished-star
two-body terms.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Boolean values as integer occupation variables. -/
def boolOccupation (b : Bool) : ℤ :=
  if b then 1 else 0

/-- Coordinates on which `z` differs from a fixed Boolean environment `z₀`,
stored as natural-number positions. -/
def boolDisagreementSupport {m : ℕ}
    (z₀ z : Fin m → Bool) : Finset ℕ :=
  (Finset.univ.filter fun i : Fin m => z i ≠ z₀ i).map Fin.valEmbedding

@[simp] theorem finVal_mem_boolDisagreementSupport {m : ℕ}
    (z₀ z : Fin m → Bool) (i : Fin m) :
    i.1 ∈ boolDisagreementSupport z₀ z ↔ z i ≠ z₀ i := by
  rw [boolDisagreementSupport]
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨j, hj, hval⟩
    have hji : j = i := Fin.ext hval
    simpa [hji] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- Binary code of the environment's disagreement pattern. -/
def starIsingBinaryCode {m : ℕ}
    (z₀ z : Fin m → Bool) : ℕ :=
  ∑ k ∈ boolDisagreementSupport z₀ z, 2 ^ k

theorem starIsingBinaryCode_eq_sum {m : ℕ}
    (z₀ z : Fin m → Bool) :
    starIsingBinaryCode z₀ z =
      ∑ i : Fin m, if z i ≠ z₀ i then 2 ^ (i : ℕ) else 0 := by
  classical
  simp [starIsingBinaryCode, boolDisagreementSupport]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : z i = z₀ i <;> simp [h]

private theorem bool_eq_of_ne_iff_ne
    (a b c : Bool) (h : (a ≠ c ↔ b ≠ c)) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem boolDisagreementSupport_injective {m : ℕ}
    (z₀ : Fin m → Bool) :
    Function.Injective (boolDisagreementSupport z₀) := by
  intro z w h
  funext i
  apply bool_eq_of_ne_iff_ne (z i) (w i) (z₀ i)
  rw [← finVal_mem_boolDisagreementSupport,
    h, finVal_mem_boolDisagreementSupport]

theorem starIsingBinaryCode_injective {m : ℕ}
    (z₀ : Fin m → Bool) :
    Function.Injective (starIsingBinaryCode z₀) := by
  intro z w h
  apply boolDisagreementSupport_injective z₀
  apply Finset.geomSum_injective (n := 2) (by omega)
  exact h

@[simp] theorem starIsingBinaryCode_self {m : ℕ}
    (z₀ : Fin m → Bool) :
    starIsingBinaryCode z₀ z₀ = 0 := by
  simp [starIsingBinaryCode, boolDisagreementSupport]

@[simp] theorem starIsingBinaryCode_eq_zero_iff {m : ℕ}
    (z₀ z : Fin m → Bool) :
    starIsingBinaryCode z₀ z = 0 ↔ z = z₀ := by
  constructor
  · intro h
    apply starIsingBinaryCode_injective z₀
    simpa using h
  · rintro rfl
    simp

theorem boolDisagreementSupport_subset_range {m : ℕ}
    (z₀ z : Fin m → Bool) :
    boolDisagreementSupport z₀ z ⊆ Finset.range m := by
  intro k hk
  simp only [boolDisagreementSupport, Finset.mem_map] at hk
  obtain ⟨i, _hi, rfl⟩ := hk
  exact Finset.mem_range.mpr i.2

/-- The binary disagreement code lies in the expected `m`-bit range. -/
theorem starIsingBinaryCode_lt_two_pow {m : ℕ}
    (z₀ z : Fin m → Bool) :
    starIsingBinaryCode z₀ z < 2 ^ m := by
  have hle :
      starIsingBinaryCode z₀ z ≤
        ∑ k ∈ Finset.range m, 2 ^ k :=
    Finset.sum_le_sum_of_subset
      (boolDisagreementSupport_subset_range z₀ z)
  have hsum :
      (∑ k ∈ Finset.range m, 2 ^ k) = 2 ^ m - 1 := by
    simpa using Nat.geomSum_eq (m := 2) (by omega) m
  rw [hsum] at hle
  have hpow : 0 < 2 ^ m := Nat.two_pow_pos m
  omega

/-- Selected-edge star energy.  The two Boolean layers have disjoint positive
ranges `[1,2^m)` and `2^m * ℕ_{>0}` and meet only at the selected
environment `z₀`. -/
def twoLocalIsolatedEdgeEnergy {m : ℕ}
    (z₀ : Fin m → Bool) (x : Bool × (Fin m → Bool)) : ℕ :=
  if x.1 then
    2 ^ m * starIsingBinaryCode z₀ x.2
  else
    starIsingBinaryCode z₀ x.2

private theorem starIsingBinaryCode_eq_scaled_iff {m : ℕ}
    (z₀ z w : Fin m → Bool) :
    starIsingBinaryCode z₀ z =
        2 ^ m * starIsingBinaryCode z₀ w ↔
      z = z₀ ∧ w = z₀ := by
  constructor
  · intro h
    by_cases hw : starIsingBinaryCode z₀ w = 0
    · have hz : starIsingBinaryCode z₀ z = 0 := by simp [h, hw]
      exact ⟨(starIsingBinaryCode_eq_zero_iff z₀ z).mp hz,
        (starIsingBinaryCode_eq_zero_iff z₀ w).mp hw⟩
    · have hwpos : 0 < starIsingBinaryCode z₀ w :=
        Nat.pos_of_ne_zero hw
      have hscale :
          2 ^ m ≤ 2 ^ m * starIsingBinaryCode z₀ w := by
        simpa using Nat.mul_le_mul_left (2 ^ m)
          (Nat.succ_le_iff.mpr hwpos)
      have hbound := starIsingBinaryCode_lt_two_pow z₀ z
      omega
  · rintro ⟨rfl, rfl⟩
    simp

/-- Exact spectral classification: equality occurs only for the same Boolean
state or for the selected flip pair above `z₀`. -/
theorem twoLocalIsolatedEdgeEnergy_eq_iff {m : ℕ}
    (z₀ : Fin m → Bool) (x y : Bool × (Fin m → Bool)) :
    twoLocalIsolatedEdgeEnergy z₀ x =
        twoLocalIsolatedEdgeEnergy z₀ y ↔
      x = y ∨ (x.2 = z₀ ∧ y.2 = z₀) := by
  rcases x with ⟨sx, z⟩
  rcases y with ⟨sy, w⟩
  cases sx <;> cases sy
  · simp only [twoLocalIsolatedEdgeEnergy, Bool.false_eq_true,
      ↓reduceIte, Prod.mk.injEq, true_and]
    constructor
    · intro h
      exact Or.inl (starIsingBinaryCode_injective z₀ h)
    · rintro (h | ⟨hz, hw⟩)
      · exact congrArg (starIsingBinaryCode z₀) h
      · subst z
        subst w
        rfl
  · simp only [twoLocalIsolatedEdgeEnergy, ↓reduceIte,
      Prod.mk.injEq, Bool.false_eq_true, false_and, false_or]
    exact starIsingBinaryCode_eq_scaled_iff z₀ z w
  · simp only [twoLocalIsolatedEdgeEnergy, ↓reduceIte,
      Prod.mk.injEq, Bool.true_eq_false, false_and, false_or]
    constructor
    · intro h
      have hh :=
        (starIsingBinaryCode_eq_scaled_iff z₀ w z).mp h.symm
      exact ⟨hh.2, hh.1⟩
    · rintro ⟨hz, hw⟩
      exact
        ((starIsingBinaryCode_eq_scaled_iff z₀ w z).mpr
          ⟨hw, hz⟩).symm
  · simp only [twoLocalIsolatedEdgeEnergy, ↓reduceIte,
      Prod.mk.injEq, true_and]
    constructor
    · intro h
      left
      exact starIsingBinaryCode_injective z₀
        (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos m) h)
    · rintro (h | ⟨hz, hw⟩)
      · exact congrArg (fun u => 2 ^ m * starIsingBinaryCode z₀ u) h
      · subst z
        subst w
        rfl

/-- Diagonal Boolean energy has distinguished-star two-local form: a
constant, one distinguished onsite term, environment onsite terms, and
distinguished--environment pair terms. -/
def IsDistinguishedStarTwoLocal {m : ℕ}
    (energy : Bool × (Fin m → Bool) → ℤ) : Prop :=
  ∃ (constant distinguished : ℤ)
      (onsite pair : Fin m → ℤ),
    ∀ x,
      energy x =
        constant +
          distinguished * boolOccupation x.1 +
          ∑ i, onsite i * boolOccupation (x.2 i) +
          ∑ i, pair i * boolOccupation x.1 *
            boolOccupation (x.2 i)

private def starIsingCodeConstant {m : ℕ}
    (z₀ : Fin m → Bool) : ℤ :=
  ∑ i : Fin m, if z₀ i then (2 : ℤ) ^ (i : ℕ) else 0

private def starIsingCodeOnsite {m : ℕ}
    (z₀ : Fin m → Bool) (i : Fin m) : ℤ :=
  if z₀ i then -((2 : ℤ) ^ (i : ℕ)) else (2 : ℤ) ^ (i : ℕ)

private theorem intCast_starIsingBinaryCode_eq_affine {m : ℕ}
    (z₀ z : Fin m → Bool) :
    (starIsingBinaryCode z₀ z : ℤ) =
      starIsingCodeConstant z₀ +
        ∑ i, starIsingCodeOnsite z₀ i * boolOccupation (z i) := by
  rw [starIsingBinaryCode_eq_sum]
  push_cast
  unfold starIsingCodeConstant starIsingCodeOnsite boolOccupation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  cases hzi : z₀ i <;> cases hz : z i <;> simp []

/-- The isolated-edge spectrum is realized by an explicit two-local
distinguished-star Hamiltonian. -/
theorem twoLocalIsolatedEdgeEnergy_isDistinguishedStarTwoLocal {m : ℕ}
    (z₀ : Fin m → Bool) :
    IsDistinguishedStarTwoLocal
      (fun x => (twoLocalIsolatedEdgeEnergy z₀ x : ℤ)) := by
  let B : ℤ := (2 : ℤ) ^ m
  let c : ℤ := starIsingCodeConstant z₀
  let b : Fin m → ℤ := starIsingCodeOnsite z₀
  refine ⟨c, (B - 1) * c, b, fun i => (B - 1) * b i, ?_⟩
  rintro ⟨s, z⟩
  have hcode := intCast_starIsingBinaryCode_eq_affine z₀ z
  let S : ℤ := ∑ i, b i * boolOccupation (z i)
  have hcode' :
      (starIsingBinaryCode z₀ z : ℤ) = c + S := by
    simpa [c, b, S] using hcode
  have hpair :
      (∑ i, (B - 1) * b i * boolOccupation (z i)) =
        (B - 1) * S := by
    simp only [S, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  cases s
  · simp only [twoLocalIsolatedEdgeEnergy, 
      boolOccupation]
    simpa [S, boolOccupation] using hcode'
  · simp only [twoLocalIsolatedEdgeEnergy, ↓reduceIte,
      boolOccupation, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      mul_one]
    change
      B * (starIsingBinaryCode z₀ z : ℤ) =
        c + (B - 1) * c + S +
          ∑ i, (B - 1) * b i * boolOccupation (z i)
    rw [hcode', hpair]
    ring

/-! ## Symmetric refinement and explicit branch divisor -/

/-- Sharper symmetric isolated-edge energy.  The two layers carry `+c` and
`-c`; their ranges meet only at the selected zero code. -/
def twoLocalSymmetricIsolatedEdgeEnergy {m : ℕ}
    (z₀ : Fin m → Bool) (x : Bool × (Fin m → Bool)) : ℤ :=
  if x.1 then
    -(starIsingBinaryCode z₀ x.2 : ℤ)
  else
    (starIsingBinaryCode z₀ x.2 : ℤ)

private theorem intCast_starIsingBinaryCode_eq_neg_iff {m : ℕ}
    (z₀ z w : Fin m → Bool) :
    (starIsingBinaryCode z₀ z : ℤ) =
        -(starIsingBinaryCode z₀ w : ℤ) ↔
      z = z₀ ∧ w = z₀ := by
  constructor
  · intro h
    have hz : starIsingBinaryCode z₀ z = 0 := by
      exact_mod_cast (show (starIsingBinaryCode z₀ z : ℤ) = 0 by omega)
    have hw : starIsingBinaryCode z₀ w = 0 := by
      exact_mod_cast (show (starIsingBinaryCode z₀ w : ℤ) = 0 by omega)
    exact ⟨(starIsingBinaryCode_eq_zero_iff z₀ z).mp hz,
      (starIsingBinaryCode_eq_zero_iff z₀ w).mp hw⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- Exact classification for the symmetric two-local star energy. -/
theorem twoLocalSymmetricIsolatedEdgeEnergy_eq_iff {m : ℕ}
    (z₀ : Fin m → Bool) (x y : Bool × (Fin m → Bool)) :
    twoLocalSymmetricIsolatedEdgeEnergy z₀ x =
        twoLocalSymmetricIsolatedEdgeEnergy z₀ y ↔
      x = y ∨ (x.2 = z₀ ∧ y.2 = z₀) := by
  rcases x with ⟨sx, z⟩
  rcases y with ⟨sy, w⟩
  cases sx <;> cases sy
  · simp only [twoLocalSymmetricIsolatedEdgeEnergy, 
      Prod.mk.injEq, true_and]
    constructor
    · intro h
      exact Or.inl (starIsingBinaryCode_injective z₀
        (Int.ofNat_inj.mp h))
    · rintro (h | ⟨hz, hw⟩)
      · exact congrArg (fun u => (starIsingBinaryCode z₀ u : ℤ)) h
      · subst z
        subst w
        rfl
  · simp only [twoLocalSymmetricIsolatedEdgeEnergy, ↓reduceIte,
      Prod.mk.injEq, Bool.false_eq_true, false_and, false_or]
    exact intCast_starIsingBinaryCode_eq_neg_iff z₀ z w
  · simp only [twoLocalSymmetricIsolatedEdgeEnergy, ↓reduceIte,
      Prod.mk.injEq, Bool.true_eq_false, false_and, false_or]
    constructor
    · intro h
      have hh := (intCast_starIsingBinaryCode_eq_neg_iff z₀ w z).mp
        h.symm
      exact ⟨hh.2, hh.1⟩
    · rintro ⟨hz, hw⟩
      subst z
      subst w
      simp
  · simp only [twoLocalSymmetricIsolatedEdgeEnergy, ↓reduceIte,
      Prod.mk.injEq, true_and, neg_inj]
    constructor
    · intro h
      exact Or.inl (starIsingBinaryCode_injective z₀
        (Int.ofNat_inj.mp h))
    · rintro (h | ⟨hz, hw⟩)
      · exact congrArg
          (fun u => (starIsingBinaryCode z₀ u : ℤ)) h
      · subst z
        subst w
        rfl

/-- The symmetric isolated-edge spectrum is still explicitly two-local. -/
theorem twoLocalSymmetricIsolatedEdgeEnergy_isDistinguishedStarTwoLocal
    {m : ℕ} (z₀ : Fin m → Bool) :
    IsDistinguishedStarTwoLocal
      (twoLocalSymmetricIsolatedEdgeEnergy z₀) := by
  let c : ℤ := starIsingCodeConstant z₀
  let b : Fin m → ℤ := starIsingCodeOnsite z₀
  refine ⟨c, -2 * c, b, fun i => -2 * b i, ?_⟩
  rintro ⟨s, z⟩
  have hcode := intCast_starIsingBinaryCode_eq_affine z₀ z
  let S : ℤ := ∑ i, b i * boolOccupation (z i)
  have hcode' :
      (starIsingBinaryCode z₀ z : ℤ) = c + S := by
    simpa [c, b, S] using hcode
  have hpair :
      (∑ i, -2 * b i * boolOccupation (z i)) = -2 * S := by
    simp only [S, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hS_bool :
      (∑ i, b i * if z i = true then 1 else 0) = S := by
    simp [S, boolOccupation]
  have hpair_bool :
      (∑ i, -2 * b i * if z i = true then 1 else 0) =
        -2 * S := by
    simpa [boolOccupation] using hpair
  cases s
  · simp only [twoLocalSymmetricIsolatedEdgeEnergy, 
      boolOccupation]
    simpa [S, boolOccupation] using hcode'
  · simp only [twoLocalSymmetricIsolatedEdgeEnergy, ↓reduceIte,
      boolOccupation, mul_one]
    rw [hcode', hS_bool, hpair_bool]
    ring

/-- Quadratic radicand of the distinguished two-level block after adding
unit transverse coupling and complex longitudinal parameter `w`. -/
def twoLocalEdgeBranchRadicand {m : ℕ}
    (z₀ z : Fin m → Bool) (w : ℂ) : ℂ :=
  ((starIsingBinaryCode z₀ z : ℂ) + w) ^ (2 : ℕ) + 1

/-- The `λI-H` matrix for the two-level block with diagonal field
`c+w` and unit transverse coupling. -/
def twoLocalEdgeCharacteristicMatrix {m : ℕ}
    (z₀ z : Fin m → Bool) (w lam : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![lam - ((starIsingBinaryCode z₀ z : ℂ) + w), -1;
      -1, lam + ((starIsingBinaryCode z₀ z : ℂ) + w)]

/-- Exact characteristic factor of every two-level environment block. -/
theorem det_twoLocalEdgeCharacteristicMatrix {m : ℕ}
    (z₀ z : Fin m → Bool) (w lam : ℂ) :
    (twoLocalEdgeCharacteristicMatrix z₀ z w lam).det =
      lam ^ (2 : ℕ) - twoLocalEdgeBranchRadicand z₀ z w := by
  simp [twoLocalEdgeCharacteristicMatrix, Matrix.det_fin_two,
    twoLocalEdgeBranchRadicand]
  ring

/-- The chosen environment is exactly the block whose radicand vanishes at
`w = i`. -/
theorem twoLocalEdgeBranchRadicand_I_eq_zero_iff {m : ℕ}
    (z₀ z : Fin m → Bool) :
    twoLocalEdgeBranchRadicand z₀ z Complex.I = 0 ↔ z = z₀ := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    norm_num [twoLocalEdgeBranchRadicand, pow_two,
      Complex.mul_re] at hre
    exact hre
  · rintro rfl
    norm_num [twoLocalEdgeBranchRadicand, pow_two, Complex.ext_iff]

/-- The selected branch zero is simple: the derivative of
`(c+w)^(2 : ℕ)+1` with respect to `w` is nonzero at `c=0,w=i`. -/
theorem twoLocalEdgeBranchDerivative_I_ne_zero {m : ℕ}
    (z₀ : Fin m → Bool) :
    2 * ((starIsingBinaryCode z₀ z₀ : ℂ) + Complex.I) ≠ 0 := by
  simp

/-- Polynomial form of the quadratic branch radicand. -/
noncomputable def twoLocalEdgeBranchPolynomial {m : ℕ}
    (z₀ z : Fin m → Bool) : Polynomial ℂ :=
  (Polynomial.X +
      Polynomial.C (starIsingBinaryCode z₀ z : ℂ)) ^ (2 : ℕ) +
    Polynomial.C 1

theorem twoLocalEdgeBranchPolynomial_eval {m : ℕ}
    (z₀ z : Fin m → Bool) (w : ℂ) :
    (twoLocalEdgeBranchPolynomial z₀ z).eval w =
      twoLocalEdgeBranchRadicand z₀ z w := by
  simp [twoLocalEdgeBranchPolynomial, twoLocalEdgeBranchRadicand,
    add_comm]

/-- At `w=i`, precisely the selected block polynomial has a root. -/
theorem twoLocalEdgeBranchPolynomial_isRoot_I_iff {m : ℕ}
    (z₀ z : Fin m → Bool) :
    (twoLocalEdgeBranchPolynomial z₀ z).IsRoot Complex.I ↔ z = z₀ := by
  rw [Polynomial.IsRoot, twoLocalEdgeBranchPolynomial_eval,
    twoLocalEdgeBranchRadicand_I_eq_zero_iff]

/-- The selected root has nonzero polynomial derivative, so its discriminant
branch is simple. -/
theorem twoLocalEdgeBranchPolynomial_selected_simple {m : ℕ}
    (z₀ : Fin m → Bool) :
    (twoLocalEdgeBranchPolynomial z₀ z₀).IsRoot Complex.I ∧
      (twoLocalEdgeBranchPolynomial z₀ z₀).derivative.eval Complex.I ≠ 0 := by
  constructor
  · exact (twoLocalEdgeBranchPolynomial_isRoot_I_iff z₀ z₀).mpr rfl
  · simp [twoLocalEdgeBranchPolynomial,
      ]

end GaloisForLFunctions.HTGeometry
