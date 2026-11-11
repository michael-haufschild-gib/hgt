import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The ring of the cube roots of two is not abelian and has its Hodge index

A number ring that is not abelian, with the theorems of the programme stated on it. The field is
the splitting field `L` of `X³ − 2` over `ℚ` (`CubeRootsOfTwo`).

* `X³ − 2` is irreducible (`2` is not a cube in `ℚ`: a rational root of a monic integer
  polynomial is an integer), of prime degree, with one real root and three complex roots. So
  its Galois group is the full symmetric group on the three roots
  (`galActionHom_cubeMinusTwo_bijective`), and two transpositions do not commute
  (`exists_not_commute_cubeRootsOfTwo`): `L/ℚ` is not abelian.
* The theorems on the square of a number ring hold for every number field, hence on `L`:
  the ideals of `L`, counted by norms on the comb of the integers, pair with the zeros of the
  Dedekind zeta function of `L` (`tendsto_ringForm_cubeRootsOfTwo`), and Weil's form of `L` has
  exactly as many negative squares as the completed Dedekind zeta function has distinct zeros to
  the right of the critical line (`exists_le_negIndex_cubeRootsOfTwo_iff`,
  `forall_negIndex_cubeRootsOfTwo_eq_zero_iff`).

The index law of the irreducible character of degree two, whose `L`-function is the Hecke
`L`-function of the cubic character of `2` over `ℚ(√−3)`, is
`TheDegreeTwoCharacterOfTheCubeRootsOfTwoHasItsHodgeIndex`.
-/

open Polynomial Filter Topology

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions HTGeometry

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-! ### `X³ − 2` has the symmetric group -/

/-- The polynomial `X³ − 2` over `ℚ`. -/
def cubeMinusTwo : ℚ[X] := X ^ 3 - C 2

/-- `2` is not a cube in `ℚ`. -/
theorem cube_ne_two (b : ℚ) : b ^ 3 ≠ 2 := by
  intro h
  have hmonic : (X ^ 3 - C 2 : ℤ[X]).Monic := monic_X_pow_sub_C 2 (by norm_num)
  have hroot : aeval b (X ^ 3 - C 2 : ℤ[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, h]
    simp
  obtain ⟨n, hn⟩ := isInteger_of_is_root_of_monic hmonic hroot
  rw [eq_intCast] at hn
  have hn3 : n ^ 3 = 2 := by
    have h' : ((n ^ 3 : ℤ) : ℚ) = ((2 : ℤ) : ℚ) := by
      push_cast
      rw [hn, h]
    exact_mod_cast h'
  have hmono := (Odd.strictMono_pow (R := ℤ) (by decide : Odd 3)).monotone
  rcases le_or_gt n 1 with h1 | h1
  · have h2 : n ^ 3 ≤ 1 ^ 3 := hmono h1
    omega
  · have h2 : (2 : ℤ) ^ 3 ≤ n ^ 3 := hmono (by omega : (2 : ℤ) ≤ n)
    omega

theorem irreducible_cubeMinusTwo : Irreducible cubeMinusTwo :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three cube_ne_two

theorem natDegree_cubeMinusTwo : cubeMinusTwo.natDegree = 3 :=
  natDegree_X_pow_sub_C

theorem mem_rootSet_cubeMinusTwo (x : ℝ) : x ∈ cubeMinusTwo.rootSet ℝ ↔ x ^ 3 = 2 := by
  rw [mem_rootSet_of_ne irreducible_cubeMinusTwo.ne_zero]
  simp [cubeMinusTwo, sub_eq_zero]

/-- Three complex roots. -/
theorem card_rootSet_complex_cubeMinusTwo : Fintype.card (cubeMinusTwo.rootSet ℂ) = 3 := by
  rw [card_rootSet_eq_natDegree irreducible_cubeMinusTwo.separable (IsAlgClosed.splits _),
    natDegree_cubeMinusTwo]

/-- One real root: the cube is strictly increasing. -/
theorem card_rootSet_real_cubeMinusTwo : Fintype.card (cubeMinusTwo.rootSet ℝ) = 1 := by
  rw [Fintype.card_eq_one_iff]
  have hroot : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨⟨(2 : ℝ) ^ (1 / 3 : ℝ), (mem_rootSet_cubeMinusTwo _).mpr hroot⟩, fun y => ?_⟩
  have hy := (mem_rootSet_cubeMinusTwo y.1).mp y.2
  exact Subtype.ext
    ((Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective (hy.trans hroot.symm))

/-- **The Galois group of `X³ − 2` is the symmetric group on its three roots.** -/
theorem galActionHom_cubeMinusTwo_bijective :
    Function.Bijective (Gal.galActionHom cubeMinusTwo ℂ) :=
  Gal.galActionHom_bijective_of_prime_degree irreducible_cubeMinusTwo
    (by rw [natDegree_cubeMinusTwo]; exact Nat.prime_three)
    (by rw [card_rootSet_complex_cubeMinusTwo, card_rootSet_real_cubeMinusTwo])

/-- Two automorphisms of the splitting field that do not commute: two transpositions of the
roots. -/
theorem exists_not_commute_gal_cubeMinusTwo : ∃ σ τ : cubeMinusTwo.Gal, σ * τ ≠ τ * σ := by
  have hcard : 2 < Fintype.card (cubeMinusTwo.rootSet ℂ) := by
    rw [card_rootSet_complex_cubeMinusTwo]
    norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcard
  obtain ⟨σ, hσ⟩ := galActionHom_cubeMinusTwo_bijective.2 (Equiv.swap a b)
  obtain ⟨τ, hτ⟩ := galActionHom_cubeMinusTwo_bijective.2 (Equiv.swap b c)
  refine ⟨σ, τ, fun h => ?_⟩
  have h' := congrArg (fun g => Gal.galActionHom cubeMinusTwo ℂ g a) h
  simp only [map_mul, hσ, hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac,
    Equiv.swap_apply_left] at h'
  exact hbc h'

/-! ### The ring -/

/-- The splitting field of `X³ − 2` over `ℚ`: the field of the cube roots of two. -/
abbrev CubeRootsOfTwo : Type := cubeMinusTwo.SplittingField

instance : NumberField CubeRootsOfTwo where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ CubeRootsOfTwo).injective
  to_finiteDimensional := inferInstance

/-- **The field of the cube roots of two is not abelian over `ℚ`.** -/
theorem exists_not_commute_cubeRootsOfTwo :
    ∃ σ τ : CubeRootsOfTwo ≃ₐ[ℚ] CubeRootsOfTwo, σ * τ ≠ τ * σ :=
  exists_not_commute_gal_cubeMinusTwo

/-- **The ideals of the ring of the cube roots of two are degree points**: counted by norms on
the comb of the integers they pair, at finite scale, with the zeros of its Dedekind zeta
function. -/
theorem tendsto_ringForm_cubeRootsOfTwo {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K₀ : ℕ} (hK : 1 ≤ K₀)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K₀ ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ringForm CubeRootsOfTwo f (3 * K₀) N +
        2 * weightedContact (idealContact CubeRootsOfTwo) f (3 * K₀) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        dedekindZeroSum CubeRootsOfTwo f)) :=
  tendsto_ringForm_add_idealContact CubeRootsOfTwo hf hfc hK hsupp

/-- **The Hodge index of a ring that is not abelian.** Weil's form of the ring of the cube roots
of two has `n` negative squares on some family of `n` tests iff its completed Dedekind zeta
function has at least `n` distinct zeros to the right of the critical line. -/
theorem exists_le_negIndex_cubeRootsOfTwo_iff (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex
          (ArithmeticCastelnuovoSeveri.zeroGram (dedekindZeros CubeRootsOfTwo) f)) ↔
      (n : ℕ∞) ≤
        (ArithmeticCastelnuovoSeveri.rightZeros (dedekindZeros CubeRootsOfTwo)).encard :=
  exists_le_negIndex_dedekindGram_iff CubeRootsOfTwo n

/-- Castelnuovo and Severi on the square of the ring of the cube roots of two: no negative
square on any family of tests iff every zero of its completed Dedekind zeta function is on the
critical line. -/
theorem forall_negIndex_cubeRootsOfTwo_eq_zero_iff :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) →
        hermNegIndex
          (ArithmeticCastelnuovoSeveri.zeroGram (dedekindZeros CubeRootsOfTwo) f) = 0) ↔
      ∀ ρ : ℂ, heckeXi (trivialModulus CubeRootsOfTwo) 1 ρ = 0 → ρ.re = 1 / 2 :=
  forall_negIndex_dedekindGram_eq_zero_iff CubeRootsOfTwo

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
