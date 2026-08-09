import GaloisForLFunctions.HTGeometry.SliceRootCount

/-!
# The monic polynomial of the roots of a slice

The product of the linear factors at the roots of a slice is a monic polynomial in the
distinguished variable whose coefficients are, up to sign, the elementary symmetric functions of
the root multiset.  Those are holomorphic in the remaining variables and the degree is locally
constant, so the whole polynomial is holomorphic in the parameters — it is the Weierstrass
polynomial of the slice.

* `HTGeometry.differentiableOn_multisetLinearProd_sliceRoots`.
-/

open Complex Metric Polynomial
open scoped Real Topology

namespace HTGeometry

variable {n : ℕ}

/-- **The monic polynomial of the roots is holomorphic in the parameters.** -/
theorem differentiableOn_multisetLinearProd_sliceRoots {f : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} {V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f U) {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (hVconn : IsPreconnected V)
    {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) (z : ℂ) :
    DifferentiableOn ℂ (fun y => multisetLinearProd (sliceRoots f t y) z) V := by
  classical
  set k : ℕ := Multiset.card (sliceRoots f t y₀) with hk
  have hcard : ∀ y ∈ V, Multiset.card (sliceRoots f t y) = k := fun y hy =>
    card_sliceRoots_const_of_isPreconnected hU hV hf ht hdisc hnez hadm hVconn hy hy₀
  have hdiff : DifferentiableOn ℂ (fun y : Fin n → ℂ =>
      ∑ j ∈ Finset.range (k + 1),
        (-1) ^ (k - j) * (sliceRoots f t y).esymm (k - j) * z ^ j) V := by
    have hterm : ∀ j ∈ Finset.range (k + 1), DifferentiableOn ℂ (fun y : Fin n → ℂ =>
        (-1) ^ (k - j) * (sliceRoots f t y).esymm (k - j) * z ^ j) V := by
      intro j _
      exact (((differentiableOn_esymm_sliceRoots hU hV hf ht hdisc hnez hadm (k - j)).const_mul
        ((-1 : ℂ) ^ (k - j))).mul (differentiableOn_const (z ^ j)))
    have hsum := DifferentiableOn.sum (u := Finset.range (k + 1))
      (A := fun j (y : Fin n → ℂ) => (-1) ^ (k - j) * (sliceRoots f t y).esymm (k - j) * z ^ j)
      hterm
    have hfun : (∑ j ∈ Finset.range (k + 1),
        fun y : Fin n → ℂ => (-1) ^ (k - j) * (sliceRoots f t y).esymm (k - j) * z ^ j)
        = fun y : Fin n → ℂ => ∑ j ∈ Finset.range (k + 1),
            (-1) ^ (k - j) * (sliceRoots f t y).esymm (k - j) * z ^ j := by
      funext y
      rw [Finset.sum_apply]
    rw [hfun] at hsum
    exact hsum
  refine hdiff.congr fun y hy => ?_
  rw [multisetLinearProd_eq_sum, hcard y hy]

end HTGeometry
