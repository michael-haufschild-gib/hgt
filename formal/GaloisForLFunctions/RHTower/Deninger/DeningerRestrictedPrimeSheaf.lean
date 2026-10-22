import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The restricted prime sum: gluing, flasqueness, and finite valuation support

Three elementary facts carry the restricted-sum sheaf on the arithmetic base.

Gluing over a finite cover: a nonnegative weight family which is summable on each member of a
finite cover of the index set is summable, because it is dominated by the finite sum of the
indicator families.  Quasi-compactness of a cofinite affine open is exactly what reduces an
arbitrary cover to a finite one, so the weighted summability conditions are local.

Flasqueness: deleting coordinates preserves summability, and extension by zero is a right inverse
which does not change the weighted sums — so every restriction is onto and norm preserving.

Finiteness of the valuation support: a nonzero rational has nonzero valuation at only finitely many
primes, so its residue family has finite support and both weighted norms are finite sums.

* `deningerWeighted_summable_of_finiteCover` : the gluing estimate.
* `deningerWeighted_summable_restrict`, `deningerZeroExtension_tsum` : flasqueness.
* `deningerPadicValRat_support_finite` : the residue family has finite support.
-/

namespace RHTower

open scoped Topology

section FiniteCover

variable {ι κ : Type*}

/-- **The gluing estimate.**  A nonnegative weight family summable on each member of a finite cover
is summable: it is dominated by the finite sum of the indicator families.  This is the estimate
that makes the weighted summability conditions local on quasi-compact opens. -/
theorem deningerWeighted_summable_of_finiteCover [DecidableEq ι] (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (s : Finset κ) (T : κ → Set ι) (hcover : ∀ i : ι, ∃ k ∈ s, i ∈ T k)
    (hsum : ∀ k ∈ s, Summable fun i : T k => g i) : Summable g := by
  classical
  have hind : ∀ k ∈ s, Summable ((T k).indicator g) := fun k hk =>
    summable_subtype_iff_indicator.mp (hsum k hk)
  have hbig : Summable fun i => ∑ k ∈ s, (T k).indicator g i := summable_sum hind
  refine Summable.of_nonneg_of_le hg (fun i => ?_) hbig
  obtain ⟨k, hk, hik⟩ := hcover i
  have hle : g i = (T k).indicator g i := (Set.indicator_of_mem hik g).symm
  rw [hle]
  refine Finset.single_le_sum (f := fun k => (T k).indicator g i) (fun k _ => ?_) hk
  exact Set.indicator_nonneg (fun j _ => hg j) i

end FiniteCover

section Flasque

variable {ι : Type*} {g : ι → ℝ}

/-- **Deleting coordinates preserves summability.** -/
theorem deningerWeighted_summable_restrict {T T' : Set ι} (hsub : T' ⊆ T)
    (h : Summable fun i : T => g i) : Summable fun i : T' => g i := by
  have hinj : Function.Injective (fun x : T' => (⟨(x : ι), hsub x.2⟩ : T)) := by
    intro a b hab
    have hval : (a : ι) = (b : ι) := congrArg (fun z : T => (z : ι)) hab
    exact Subtype.ext hval
  exact h.comp_injective hinj

/-- **Extension by zero preserves the weighted sums.**  So the coordinate deletion has a norm-one
right inverse and every restriction is surjective: the restricted-sum prescription is flasque. -/
theorem deningerZeroExtension_tsum (T T' : Set ι) (hsub : T' ⊆ T)
    (_h : Summable fun i : T' => g i) :
    ∑' i : T, (T'.indicator g) i = ∑' i : T', g i := by
  classical
  have hT' : ∑' i : ι, (T'.indicator g) i = ∑' i : T', g i :=
    (tsum_subtype T' g).symm
  have hTT : ∑' i : T, (T'.indicator g) i = ∑' i : ι, (T'.indicator g) i := by
    refine tsum_subtype_eq_of_support_subset ?_
    intro i hi
    have hmem : i ∈ T' := by
      by_contra hcon
      exact hi (Set.indicator_of_notMem hcon g)
    exact hsub hmem
  rw [hTT, hT']

end Flasque

section ValuationSupport

/-- **The residue family has finite support.**  A nonzero rational has nonzero `p`-adic valuation
at only finitely many primes, so the weighted `ℓ¹` and `ℓ²` norms of its residue family are finite
sums. -/
theorem deningerPadicValRat_support_finite {x : ℚ} (hx : x ≠ 0) :
    {p : ℕ | p.Prime ∧ padicValRat p x ≠ 0}.Finite := by
  classical
  have hnum : x.num.natAbs ≠ 0 := by
    intro hcon
    rw [Int.natAbs_eq_zero] at hcon
    exact hx (Rat.zero_iff_num_zero.mpr hcon)
  have hden : x.den ≠ 0 := x.den_nz
  refine Set.Finite.subset
    (Set.Finite.union (x.num.natAbs.factorization.support.finite_toSet)
      (x.den.factorization.support.finite_toSet)) ?_
  intro p hp
  obtain ⟨hprime, hne⟩ := hp
  by_contra hcon
  refine hne ?_
  have hnum0 : padicValNat p x.num.natAbs = 0 := by
    have hns : p ∉ x.num.natAbs.factorization.support := fun h => hcon (Or.inl h)
    have := Finsupp.notMem_support_iff.mp hns
    rwa [Nat.factorization_def _ hprime] at this
  have hden0 : padicValNat p x.den = 0 := by
    have hns : p ∉ x.den.factorization.support := fun h => hcon (Or.inr h)
    have := Finsupp.notMem_support_iff.mp hns
    rwa [Nat.factorization_def _ hprime] at this
  show padicValRat p x = 0
  rw [padicValRat, padicValInt, hnum0, hden0]
  norm_num

end ValuationSupport

end RHTower
