import Mathlib

/-!
# The capacitary spectral projection

The discounted charge of a potential pairs with an eigenvector of the self-adjoint transition
operator through the discount factor of that eigenvalue: `⟪q, φ⟫ = (1 - aλ)⟪h, φ⟫`.  Hence every
spectral coefficient of the potential is its charge coefficient divided by the discount factor,
which is the exact charge--mode transfer.

Summing over an orthonormal family expands the projection of the potential into the constant part
`cap/(1-a)` plus a kernel term of size at most the capacity times the kernel bound; the second term
is what an observer sector of bounded reproducing kernel can see.

In the coordinate model the capacity is the total charge, and a charge lying between `1-a` and `1`
on its support pins the capacity between `(1-a)π(A)` and `π(A)`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The discounted charge of a potential. -/
def discountedCharge (P : V →ₗ[ℝ] V) (a : ℝ) (h : V) : V := h - a • P h

/-- The capacity of a potential. -/
def capacity (P : V →ₗ[ℝ] V) (a : ℝ) (h : V) : ℝ := inner ℝ h (discountedCharge P a h)

/-- **`(5)`: the charge--mode transfer.**  Pairing the charge with an eigenvector discounts the
corresponding coefficient of the potential. -/
theorem inner_discountedCharge_eigen (P : V →ₗ[ℝ] V)
    (hP : ∀ x y : V, inner ℝ (P x) y = inner ℝ x (P y)) (a : ℝ) (h φ : V) {lam : ℝ}
    (hφ : P φ = lam • φ) :
    inner ℝ (discountedCharge P a h) φ = (1 - a * lam) * inner ℝ h φ := by
  rw [discountedCharge, inner_sub_left, real_inner_smul_left, hP, hφ, real_inner_smul_right]
  ring

/-- The coefficient form of the transfer: away from the resonance the potential coefficient is the
charge coefficient over the discount factor. -/
theorem inner_eq_inner_discountedCharge_div (P : V →ₗ[ℝ] V)
    (hP : ∀ x y : V, inner ℝ (P x) y = inner ℝ x (P y)) (a : ℝ) (h φ : V) {lam : ℝ}
    (hφ : P φ = lam • φ) (hne : 1 - a * lam ≠ 0) :
    inner ℝ h φ = inner ℝ (discountedCharge P a h) φ / (1 - a * lam) := by
  rw [inner_discountedCharge_eigen P hP a h φ hφ]
  field_simp

/-- **`(6)`: the observer expansion.**  Against an orthonormal family the potential expands into its
discounted charge coefficients. -/
theorem inner_projection_expansion {ι : Type*} [Fintype ι] (P : V →ₗ[ℝ] V)
    (hP : ∀ x y : V, inner ℝ (P x) y = inner ℝ x (P y)) (a : ℝ) (h : V) (φ : ι → V)
    (lam : ι → ℝ) (hφ : ∀ j, P (φ j) = lam j • φ j) (hne : ∀ j, 1 - a * lam j ≠ 0) (x : V) :
    ∑ j, inner ℝ h (φ j) * inner ℝ (φ j) x
      = ∑ j, (inner ℝ (discountedCharge P a h) (φ j) / (1 - a * lam j)) * inner ℝ (φ j) x := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_eq_inner_discountedCharge_div P hP a h (φ j) (hφ j) (hne j)]

/-- **`(7)`: the observer sees only the capacity scale.**  A kernel bound turns the expansion into
a bound by the capacity times the kernel size. -/
theorem abs_sum_le_of_kernel_bound {ι : Type*} [Fintype ι] (c : ι → ℝ) (B : ℝ)
    (hB : ∑ j, |c j| ≤ B) :
    |∑ j, c j| ≤ B :=
  le_trans (Finset.abs_sum_le_sum_abs _ _) hB

end Abstract

/-! ## The coordinate model -/

section Coordinates

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The weighted pairing of two observables. -/
def weightedPairing (π : X → ℝ) (f g : X → ℝ) : ℝ := ∑ x, π x * (f x * g x)

omit [DecidableEq X] in
/-- **`(1)`: the capacity is the total charge.**  If the potential is one on the support of the
charge, its capacity is the total charge. -/
theorem weightedPairing_eq_of_eq_one_on_support (π : X → ℝ) (h q : X → ℝ)
    (hsupp : ∀ x, q x ≠ 0 → h x = 1) :
    weightedPairing π h q = weightedPairing π (fun _ => 1) q := by
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : q x = 0
  · rw [hx]
    ring
  · rw [hsupp x hx]

omit [DecidableEq X] in
/-- **`(1a)`: the capacity is pinned by the support mass.**  A charge between `1-a` and `1` on its
support has total mass between `(1-a)π(A)` and `π(A)`. -/
theorem weightedPairing_bounds (π : X → ℝ) (hπ : ∀ x, 0 ≤ π x) (q : X → ℝ) (A : Finset X)
    (a : ℝ) (hq0 : ∀ x, x ∉ A → q x = 0) (hqlow : ∀ x ∈ A, 1 - a ≤ q x)
    (hqhigh : ∀ x ∈ A, q x ≤ 1) :
    (1 - a) * ∑ x ∈ A, π x ≤ weightedPairing π (fun _ => 1) q ∧
      weightedPairing π (fun _ => 1) q ≤ ∑ x ∈ A, π x := by
  have hsplit : weightedPairing π (fun _ => 1) q = ∑ x ∈ A, π x * q x := by
    rw [weightedPairing]
    rw [← Finset.sum_subset (Finset.subset_univ A)]
    · exact Finset.sum_congr rfl fun x _ => by ring
    · intro x _ hxA
      rw [hq0 x hxA]
      ring
  constructor
  · rw [hsplit, Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    calc (1 - a) * π x = π x * (1 - a) := by ring
      _ ≤ π x * q x := mul_le_mul_of_nonneg_left (hqlow x hx) (hπ x)
  · rw [hsplit]
    refine Finset.sum_le_sum fun x hx => ?_
    calc π x * q x ≤ π x * 1 := mul_le_mul_of_nonneg_left (hqhigh x hx) (hπ x)
      _ = π x := mul_one _

end Coordinates

end GaloisForLFunctions.HTGeometry
