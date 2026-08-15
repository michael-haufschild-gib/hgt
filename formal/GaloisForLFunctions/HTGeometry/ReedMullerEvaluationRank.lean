import GaloisForLFunctions.HTGeometry.BooleanConjunctionParity

/-!
# Full rank of low-degree multilinear evaluation at few Boolean points

The evaluation matrix of the multilinear monomials of degree at most `m` at fewer than `2^(m+1)`
distinct Boolean points has full row rank over `ZMod 2`: a nonzero left kernel vector would be a
dual Reed–Muller codeword of weight below the minimum distance.  Transposing, the evaluation map
from coefficient vectors to value vectors is surjective.
-/

open Finset Matrix Module

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multilinear monomials of degree at most `m`, indexed by their support. -/
abbrev MonLe (ι : Type*) [DecidableEq ι] (m : ℕ) := {S : Finset ι // S.card ≤ m}

/-- The evaluation matrix of the degree-at-most-`m` multilinear monomials at a family of Boolean
points. -/
def evalMatrix (R : Type*) [CommRing R] (m : ℕ) {k : ℕ} (x : Fin k → (ι → Bool)) :
    Matrix (Fin k) (MonLe ι m) R :=
  fun j S => if ∀ i ∈ S.1, x j i = true then 1 else 0

theorem zmodTwo_eq_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

/-- The left action of a coefficient vector on the evaluation matrix reads off the parity of the
conjunction fibre it selects. -/
theorem vecMul_evalMatrix_apply {k : ℕ} (m : ℕ) (x : Fin k → (ι → Bool))
    (lam : Fin k → ZMod 2) (S : MonLe ι m) :
    (lam ᵥ* evalMatrix (ZMod 2) m x) S =
      ((Finset.univ.filter fun j => lam j = 1 ∧ ∀ i ∈ S.1, x j i = true).card : ZMod 2) := by
  classical
  show (∑ j, lam j * evalMatrix (ZMod 2) m x j S) = _
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases zmodTwo_eq_zero_or_one (lam j) with h0 | h1
  · rw [h0, zero_mul, if_neg]
    rintro ⟨hc, -⟩
    exact absurd hc (by decide)
  · rw [h1, one_mul, evalMatrix]
    by_cases hS : ∀ i ∈ S.1, x j i = true
    · rw [if_pos hS, if_pos ⟨rfl, hS⟩]
    · rw [if_neg hS, if_neg]
      rintro ⟨-, hc⟩
      exact hS hc

/-- **No nonzero left kernel vector.**  Fewer than `2^(m+1)` distinct Boolean points admit no
nonzero dual relation among their degree-at-most-`m` monomial evaluations. -/
theorem vecMul_evalMatrix_eq_zero_imp {k m : ℕ} (hk : k < 2 ^ (m + 1))
    (x : Fin k → (ι → Bool)) (hx : Function.Injective x)
    (lam : Fin k → ZMod 2) (hlam : lam ᵥ* evalMatrix (ZMod 2) m x = 0) : lam = 0 := by
  classical
  by_contra hne
  obtain ⟨j₀, hj₀⟩ : ∃ j, lam j ≠ 0 := by
    by_contra hcon
    exact hne (funext fun j => not_not.mp fun h => hcon ⟨j, h⟩)
  set J : Finset (Fin k) := Finset.univ.filter fun j => lam j = 1 with hJ
  have hj₀J : j₀ ∈ J := by
    rw [hJ, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (zmodTwo_eq_zero_or_one (lam j₀)).resolve_left hj₀⟩
  set T : Finset (ι → Bool) := J.image x with hT
  have hTne : T.Nonempty := ⟨x j₀, Finset.mem_image_of_mem x hj₀J⟩
  have hTcard : T.card < 2 ^ (m + 1) := by
    refine lt_of_le_of_lt (le_trans Finset.card_image_le ?_) hk
    exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_fin k))
  obtain ⟨S, hScard, hSodd⟩ := exists_odd_conjunctionFiber hTne hTcard
  have hfiber : conjunctionFiber S T =
      (Finset.univ.filter fun j => lam j = 1 ∧ ∀ i ∈ S, x j i = true).image x := by
    ext y
    rw [mem_conjunctionFiber, hT, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨⟨j, hjJ, rfl⟩, hy⟩
      rw [hJ, Finset.mem_filter] at hjJ
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjJ.2, hy⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rw [Finset.mem_filter] at hj
      exact ⟨⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2.1⟩, rfl⟩, hj.2.2⟩
  have hcard : (conjunctionFiber S T).card =
      (Finset.univ.filter fun j => lam j = 1 ∧ ∀ i ∈ S, x j i = true).card := by
    rw [hfiber]
    exact Finset.card_image_of_injective _ hx
  have hzero : (lam ᵥ* evalMatrix (ZMod 2) m x) ⟨S, hScard⟩ = 0 := by
    rw [hlam]
    rfl
  rw [vecMul_evalMatrix_apply, ZMod.natCast_eq_zero_iff_even] at hzero
  exact hSodd (hcard ▸ hzero)

/-- **Surjectivity of low-degree multilinear evaluation over `ZMod 2`.** -/
theorem surjective_mulVec_evalMatrix {k m : ℕ} (hk : k < 2 ^ (m + 1))
    (x : Fin k → (ι → Bool)) (hx : Function.Injective x) :
    Function.Surjective fun c : MonLe ι m → ZMod 2 => (evalMatrix (ZMod 2) m x) *ᵥ c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Matrix (Fin k) (MonLe ι m) (ZMod 2) := evalMatrix (ZMod 2) m x with hA
  have hinj : Function.Injective (Aᵀ.mulVecLin) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro lam hlam
    have h1 : Aᵀ *ᵥ lam = 0 := by
      rw [← Matrix.mulVecLin_apply]
      exact hlam
    rw [Matrix.mulVec_transpose] at h1
    exact vecMul_evalMatrix_eq_zero_imp hk x hx lam h1
  have hrankT : Aᵀ.rank = k := by
    have hdef : Aᵀ.rank = finrank (ZMod 2) (LinearMap.range Aᵀ.mulVecLin) := rfl
    rw [hdef, LinearMap.finrank_range_of_inj hinj]
    simp
  have hrank : A.rank = k := by
    rw [← Matrix.rank_transpose A]
    exact hrankT
  have htop : LinearMap.range A.mulVecLin = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have hdef : A.rank = finrank (ZMod 2) (LinearMap.range A.mulVecLin) := rfl
    rw [← hdef, hrank]
    simp
  intro w
  obtain ⟨c, hc⟩ := LinearMap.range_eq_top.mp htop w
  exact ⟨c, hc⟩

end GaloisForLFunctions.HTGeometry
