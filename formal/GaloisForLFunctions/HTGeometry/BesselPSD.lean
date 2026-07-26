import Mathlib

/-!
# Bessel's inequality for a positive semi-definite sesquilinear form

For a form that is additive and `ℂ`-homogeneous in its first slot, conjugate-symmetric, and positive
semi-definite on the diagonal, an orthonormal family satisfies Bessel's inequality
`∑ᵢ ‖B u (e i)‖² ≤ Re (B u u)`.  Definiteness is not needed, so the statement applies to forms
obtained as limits of positive forms — in particular to the logarithmic prime form
`⟨u,v⟩ = lim (loglog x)⁻¹ ∑_{p ≤ x} u(p) conj(v(p)) / p`.

In that setting the family `e_τ(p) = p^{2iτ}` is orthonormal, because
`∑_p p^{-1-2iθ} = log ζ(1+2iθ) + O(1)` is bounded for `θ ≠ 0` while the `θ = 0` sum is
`loglog x + O(1)`.  Bessel then bounds the sum of squares of the coefficient correlations at distinct
frequencies by the total energy.

Distinct from `GaloisForLFunctions.RHTower.TraceNorm.sum_inner_sq_le_of_orthonormal_with_zeros`,
which is Bessel in a genuine `InnerProductSpace ℂ H` (hence for a definite form).  The form used here
is only positive **semi**-definite and is given as a bare function, which is required for limits of
positive forms such as the logarithmic prime form.
-/

namespace HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Bessel's inequality for a positive semi-definite sesquilinear form.** -/
theorem bessel_of_orthonormal (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (c : ℂ) (x y : V), B (c • x) y = c * B x y)
    (hconj : ∀ x y, B y x = (starRingEnd ℂ) (B x y))
    (hpsd : ∀ x, 0 ≤ (B x x).re)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V) (u : V)
    (horth : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, ‖B u (e i)‖ ^ 2 ≤ (B u u).re := by
  classical
  set c : ι → ℂ := fun i => B u (e i) with hc
  set w : V := ∑ i, c i • e i with hw
  -- additivity in the second slot, from conjugate symmetry
  have hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z := by
    intro x y z
    have h1 : B x (y + z) = (starRingEnd ℂ) (B (y + z) x) := hconj (y + z) x
    rw [h1, hadd₁, map_add, ← hconj, ← hconj]
  have hsum₁ : ∀ (f : ι → ℂ) (g : ι → V) (z : V),
      B (∑ i, f i • g i) z = ∑ i, f i * B (g i) z := by
    intro f g z
    induction (Finset.univ : Finset ι) using Finset.induction with
    | empty => simp [show B 0 z = 0 from by
        have := hsmul₁ 0 z z; simpa using this]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd₁, hsmul₁, ih]
  have hsum₂ : ∀ (f : ι → ℂ) (g : ι → V) (z : V),
      B z (∑ i, f i • g i) = ∑ i, (starRingEnd ℂ) (f i) * B z (g i) := by
    intro f g z
    have h1 : B z (∑ i, f i • g i) = (starRingEnd ℂ) (B (∑ i, f i • g i) z) :=
      hconj (∑ i, f i • g i) z
    rw [h1, hsum₁, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, ← hconj]
  -- expand the four terms
  have hBwu : B w u = ∑ i, c i * (starRingEnd ℂ) (c i) := by
    rw [hw, hsum₁]
    exact Finset.sum_congr rfl fun i _ => by rw [hconj]
  have hBuw : B u w = ∑ i, (starRingEnd ℂ) (c i) * c i := by
    rw [hw, hsum₂]
  have hBww : B w w = ∑ i, c i * (starRingEnd ℂ) (c i) := by
    rw [hw]
    rw [hsum₁ c e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum₂ c e]
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single i]
    · rw [horth i i]; simp
    · intro j _ hj
      rw [horth i j]
      simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hvv : B (u - w) (u - w) = B u u - ∑ i, c i * (starRingEnd ℂ) (c i) := by
    have hsub : ∀ x y z : V, B (x - y) z = B x z - B y z := by
      intro x y z
      have h : B ((x - y) + y) z = B (x - y) z + B y z := hadd₁ _ _ _
      simp only [sub_add_cancel] at h
      linear_combination -h
    have hsub₂ : ∀ x y z : V, B x (y - z) = B x y - B x z := by
      intro x y z
      have h1 : B x (y - z) = (starRingEnd ℂ) (B (y - z) x) := hconj (y - z) x
      rw [h1, hsub, map_sub, ← hconj, ← hconj]
    rw [hsub, hsub₂, hsub₂, hBwu, hBuw, hBww]
    have : ∀ i, (starRingEnd ℂ) (c i) * c i = c i * (starRingEnd ℂ) (c i) := fun i => by ring
    simp only [this]
    ring
  have hnn : 0 ≤ (B (u - w) (u - w)).re := hpsd _
  rw [hvv] at hnn
  have hre : (∑ i, c i * (starRingEnd ℂ) (c i)).re = ∑ i, ‖c i‖ ^ 2 := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Complex.sub_re, hre] at hnn
  linarith

end HTGeometry
