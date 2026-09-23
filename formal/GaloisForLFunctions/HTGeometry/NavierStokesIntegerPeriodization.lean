import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-!
# Integer periodization without nonlinear cross terms

Corollary 10.6 of the supplied Navier--Stokes paper embeds a compactly supported
Euclidean solution into the torus.  After rescaling its support into
`(-1/2, 1/2)^d`, distinct integer translates are disjoint.  Consequently the
periodization is pointwise a sum with at most one nonzero term, so zero-preserving
nonlinear operations commute with it exactly.

This file isolates that mechanism for arbitrary coordinate dimension and arbitrary
additive codomains.  The unary and binary forms cover local nonlinearities and the
paper's quadratic convection term; scalar multiplication is included as a direct
corollary.  Periodicity itself does not need the support assumption.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesIntegerPeriodization

open Function Set

noncomputable section

variable {d E F G : Type*}

/-- Integer translation of a point in a real coordinate space. -/
def integerShift (x : d → ℝ) (k : d → ℤ) : d → ℝ :=
  x + fun i ↦ (k i : ℝ)

/-- Open unit cube centered at the origin. -/
def openFundamentalCube : Set (d → ℝ) :=
  {x | ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2}

/-- A function vanishes outside the open centered unit cube. -/
def SupportedInOpenFundamentalCube [Zero E] (f : (d → ℝ) → E) : Prop :=
  Function.support f ⊆ openFundamentalCube

/-- Integer periodization, expressed as a finite-support sum. -/
def integerPeriodization [AddCommMonoid E] (f : (d → ℝ) → E) (x : d → ℝ) : E :=
  ∑ᶠ k : d → ℤ, f (integerShift x k)

theorem integerShift_add (x : d → ℝ) (k l : d → ℤ) :
    integerShift (integerShift x k) l = integerShift x (k + l) := by
  ext i
  simp [integerShift, add_assoc]

/-- Two active integer translates of cube-supported data have the same index. -/
theorem integerShift_active_unique [Zero E] {f : (d → ℝ) → E}
    (hf : SupportedInOpenFundamentalCube f) (x : d → ℝ) {k l : d → ℤ}
    (hk : f (integerShift x k) ≠ 0) (hl : f (integerShift x l) ≠ 0) :
    k = l := by
  funext i
  have hkcube := hf hk
  have hlcube := hf hl
  have hki : -(1 / 2 : ℝ) < x i + (k i : ℝ) ∧ x i + (k i : ℝ) < 1 / 2 := by
    simpa [openFundamentalCube, integerShift] using hkcube i
  have hli : -(1 / 2 : ℝ) < x i + (l i : ℝ) ∧ x i + (l i : ℝ) < 1 / 2 := by
    simpa [openFundamentalCube, integerShift] using hlcube i
  have hupper : ((k i - l i : ℤ) : ℝ) < 1 := by
    norm_num only [Int.cast_sub]
    linarith [hki.2, hli.1]
  have hlower : (-1 : ℝ) < ((k i - l i : ℤ) : ℝ) := by
    norm_num only [Int.cast_sub]
    linarith [hki.1, hli.2]
  have hupperZ : k i - l i < 1 := by exact_mod_cast hupper
  have hlowerZ : -1 < k i - l i := by exact_mod_cast hlower
  omega

/-- The translate family has at most one active summand at every point. -/
theorem integerShift_support_subsingleton [Zero E] {f : (d → ℝ) → E}
    (hf : SupportedInOpenFundamentalCube f) (x : d → ℝ) :
    (Function.support fun k : d → ℤ ↦ f (integerShift x k)).Subsingleton := by
  intro k hk l hl
  exact integerShift_active_unique hf x hk hl

/-- In particular, the pointwise translate family has finite support. -/
theorem integerShift_hasFiniteSupport [Zero E] {f : (d → ℝ) → E}
    (hf : SupportedInOpenFundamentalCube f) (x : d → ℝ) :
    HasFiniteSupport fun k : d → ℤ ↦ f (integerShift x k) :=
  (integerShift_support_subsingleton hf x).finite

/-- Distinct translated supports are disjoint. -/
theorem disjoint_integerShift_support [Zero E] {f : (d → ℝ) → E}
    (hf : SupportedInOpenFundamentalCube f) {k l : d → ℤ} (hkl : k ≠ l) :
    Disjoint (Function.support fun x ↦ f (integerShift x k))
      (Function.support fun x ↦ f (integerShift x l)) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  exact hkl (integerShift_active_unique hf x hxk hxl)

/-- At a point with an active translate, periodization selects exactly that translate. -/
theorem integerPeriodization_eq_single [AddCommMonoid E] {f : (d → ℝ) → E}
    (hf : SupportedInOpenFundamentalCube f) (x : d → ℝ) {k : d → ℤ}
    (hk : f (integerShift x k) ≠ 0) :
    integerPeriodization f x = f (integerShift x k) := by
  apply finsum_eq_single
  intro l hl
  by_contra hactive
  exact hl (integerShift_active_unique hf x hactive hk)

/-- A zero-preserving nonlinear map commutes with a sum having at most one active summand. -/
theorem finsum_apply_of_subsingleton_support [AddCommMonoid E] [AddCommMonoid F]
    (Q : E → F) (hQ : Q 0 = 0) (a : d → E)
    (ha : ∀ i j, a i ≠ 0 → a j ≠ 0 → i = j) :
    (∑ᶠ i, Q (a i)) = Q (∑ᶠ i, a i) := by
  classical
  by_cases hactive : ∃ i, a i ≠ 0
  · obtain ⟨i, hi⟩ := hactive
    have hzero : ∀ j, j ≠ i → a j = 0 := by
      intro j hji
      by_contra hj
      exact hji (ha j i hj hi)
    rw [finsum_eq_single a i hzero,
      finsum_eq_single (fun j ↦ Q (a j)) i]
    intro j hji
    rw [hzero j hji, hQ]
  · have hzero : ∀ i, a i = 0 := by
      intro i
      exact not_ne_iff.mp fun hi ↦ hactive ⟨i, hi⟩
    simp [hzero, hQ]

/-- A zero-at-the-origin binary operation commutes with two jointly one-active sums. -/
theorem finsum_apply₂_of_subsingleton_joint
    [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G]
    (Q : E → F → G) (hQ : Q 0 0 = 0) (a : d → E) (b : d → F)
    (hab : ∀ i j, (a i ≠ 0 ∨ b i ≠ 0) → (a j ≠ 0 ∨ b j ≠ 0) → i = j) :
    (∑ᶠ i, Q (a i) (b i)) = Q (∑ᶠ i, a i) (∑ᶠ i, b i) := by
  classical
  by_cases hactive : ∃ i, a i ≠ 0 ∨ b i ≠ 0
  · obtain ⟨i, hi⟩ := hactive
    have hazero : ∀ j, j ≠ i → a j = 0 := by
      intro j hji
      by_contra hj
      exact hji (hab j i (Or.inl hj) hi)
    have hbzero : ∀ j, j ≠ i → b j = 0 := by
      intro j hji
      by_contra hj
      exact hji (hab j i (Or.inr hj) hi)
    rw [finsum_eq_single a i hazero, finsum_eq_single b i hbzero,
      finsum_eq_single (fun j ↦ Q (a j) (b j)) i]
    intro j hji
    rw [hazero j hji, hbzero j hji, hQ]
  · have ha0 : ∀ i, a i = 0 := by
      intro i
      exact not_ne_iff.mp fun hi ↦ hactive ⟨i, Or.inl hi⟩
    have hb0 : ∀ i, b i = 0 := by
      intro i
      exact not_ne_iff.mp fun hi ↦ hactive ⟨i, Or.inr hi⟩
    simp [ha0, hb0, hQ]

/-- Exact nonlinear termwise periodization from Corollary 10.6. -/
theorem integerPeriodization_comp [AddCommMonoid E] [AddCommMonoid F]
    {f : (d → ℝ) → E} (hf : SupportedInOpenFundamentalCube f)
    (Q : E → F) (hQ : Q 0 = 0) (x : d → ℝ) :
    integerPeriodization (fun y ↦ Q (f y)) x = Q (integerPeriodization f x) := by
  apply finsum_apply_of_subsingleton_support Q hQ
  intro k l hk hl
  exact integerShift_active_unique hf x hk hl

/-- Exact binary nonlinear periodization for two fields supported in the same cube. -/
theorem integerPeriodization_apply₂ [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G]
    {f : (d → ℝ) → E} {g : (d → ℝ) → F}
    (hf : SupportedInOpenFundamentalCube f) (hg : SupportedInOpenFundamentalCube g)
    (Q : E → F → G) (hQ : Q 0 0 = 0) (x : d → ℝ) :
    integerPeriodization (fun y ↦ Q (f y) (g y)) x =
      Q (integerPeriodization f x) (integerPeriodization g x) := by
  apply finsum_apply₂_of_subsingleton_joint Q hQ
  intro k l hk hl
  let p : (d → ℝ) → E × F := fun y ↦ (f y, g y)
  have hp : SupportedInOpenFundamentalCube p := by
    intro y hy
    by_cases hyf : f y = 0
    · apply hg
      intro hyg
      exact hy (Prod.ext hyf hyg)
    · exact hf hyf
  have hpk : p (integerShift x k) ≠ 0 := by
    rcases hk with hk | hk
    · intro hpair
      exact hk (congrArg Prod.fst hpair)
    · intro hpair
      exact hk (congrArg Prod.snd hpair)
  have hpl : p (integerShift x l) ≠ 0 := by
    rcases hl with hl | hl
    · intro hpair
      exact hl (congrArg Prod.fst hpair)
    · intro hpair
      exact hl (congrArg Prod.snd hpair)
  exact integerShift_active_unique hp x hpk hpl

/-- Scalar products periodize termwise when both factors occupy the same open cell. -/
theorem integerPeriodization_mul {R : Type*} [Semiring R]
    {f g : (d → ℝ) → R} (hf : SupportedInOpenFundamentalCube f)
    (hg : SupportedInOpenFundamentalCube g) (x : d → ℝ) :
    integerPeriodization (fun y ↦ f y * g y) x =
      integerPeriodization f x * integerPeriodization g x := by
  exact integerPeriodization_apply₂ hf hg (fun a b ↦ a * b) (zero_mul 0) x

/-- Integer periodization is invariant under every integer translation. -/
theorem integerPeriodization_integerShift [AddCommMonoid E]
    (f : (d → ℝ) → E) (x : d → ℝ) (m : d → ℤ) :
    integerPeriodization f (integerShift x m) = integerPeriodization f x := by
  unfold integerPeriodization
  apply finsum_eq_of_bijective (fun k ↦ m + k)
  · constructor
    · intro a b h
      exact add_left_cancel h
    · intro y
      exact ⟨y - m, by simp⟩
  · intro k
    rw [integerShift_add]

end

end GaloisForLFunctions.HTGeometry.NavierStokesIntegerPeriodization
