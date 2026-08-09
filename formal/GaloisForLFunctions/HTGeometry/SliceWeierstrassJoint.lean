import GaloisForLFunctions.HTGeometry.SliceWeierstrassFactorization

/-!
# The Weierstrass polynomial as a function of all the variables

Assembled from the slices, the monic polynomial of the roots is a function of all the variables at
once.  It is holomorphic there: expanded in the elementary symmetric functions it is a polynomial
in the distinguished variable, of locally constant degree, whose coefficients are holomorphic in
the remaining variables.

* `HTGeometry.tailLin`, `HTGeometry.sliceWeierstrass`;
* `HTGeometry.differentiableOn_sliceWeierstrass`;
* `HTGeometry.sliceWeierstrass_ne_zero_of_norm_eq`.
-/

open Complex Metric
open scoped Real Topology

namespace HTGeometry

variable {n : ℕ}

/-- Dropping the first coordinate, as a continuous linear map. -/
noncomputable def tailLin : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp]
theorem tailLin_apply (w : Fin (n + 1) → ℂ) : tailLin w = Fin.tail w := rfl

/-- The monic polynomial of the roots of a slice, as a function of all the variables. -/
noncomputable def sliceWeierstrass (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (w : Fin (n + 1) → ℂ) : ℂ :=
  multisetLinearProd (sliceRoots f t (Fin.tail w)) (w 0)

@[simp]
theorem sliceWeierstrass_cons (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (y : Fin n → ℂ) (z : ℂ) :
    sliceWeierstrass f t (Fin.cons z y) = multisetLinearProd (sliceRoots f t y) z := by
  rw [sliceWeierstrass, Fin.tail_cons, Fin.cons_zero]

/-- It does not vanish on the circle, the roots being strictly inside. -/
theorem sliceWeierstrass_ne_zero_of_norm_eq {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y) {ζ : ℂ} (hζ : ‖ζ‖ = t) :
    sliceWeierstrass f t (Fin.cons ζ y) ≠ 0 := by
  rw [sliceWeierstrass_cons]
  exact multisetLinearProd_ne_zero (sliceRoots_norm_lt ht hy) hζ

/-- **The Weierstrass polynomial is holomorphic in all the variables.** -/
theorem differentiableOn_sliceWeierstrass {f : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} {V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f U) {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (hVconn : IsPreconnected V)
    {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) :
    DifferentiableOn ℂ (sliceWeierstrass f t) {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} := by
  classical
  set W : Set (Fin (n + 1) → ℂ) := {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} with hW
  set k : ℕ := Multiset.card (sliceRoots f t y₀) with hk
  have hcard : ∀ y ∈ V, Multiset.card (sliceRoots f t y) = k := fun y hy =>
    card_sliceRoots_const_of_isPreconnected hU hV hf ht hdisc hnez hadm hVconn hy hy₀
  have htail : DifferentiableOn ℂ (fun w : Fin (n + 1) → ℂ => Fin.tail w) W :=
    ((tailLin : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ)).differentiable).differentiableOn
  have hmaps : Set.MapsTo (fun w : Fin (n + 1) → ℂ => Fin.tail w) W V := fun w hw => hw
  have hproj : DifferentiableOn ℂ (fun w : Fin (n + 1) → ℂ => w 0) W :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
      (0 : Fin (n + 1))).differentiable).differentiableOn
  have hterm : ∀ j ∈ Finset.range (k + 1), DifferentiableOn ℂ (fun w : Fin (n + 1) → ℂ =>
      (-1) ^ (k - j) * (sliceRoots f t (Fin.tail w)).esymm (k - j) * (w 0) ^ j) W := by
    intro j _
    have hesymm : DifferentiableOn ℂ (fun w : Fin (n + 1) → ℂ =>
        (sliceRoots f t (Fin.tail w)).esymm (k - j)) W :=
      (differentiableOn_esymm_sliceRoots hU hV hf ht hdisc hnez hadm (k - j)).comp htail hmaps
    exact (hesymm.const_mul ((-1 : ℂ) ^ (k - j))).mul (hproj.pow j)
  have hsum := DifferentiableOn.sum (u := Finset.range (k + 1))
    (A := fun j (w : Fin (n + 1) → ℂ) =>
      (-1) ^ (k - j) * (sliceRoots f t (Fin.tail w)).esymm (k - j) * (w 0) ^ j) hterm
  have hfun : (∑ j ∈ Finset.range (k + 1),
      fun w : Fin (n + 1) → ℂ =>
        (-1) ^ (k - j) * (sliceRoots f t (Fin.tail w)).esymm (k - j) * (w 0) ^ j)
      = fun w : Fin (n + 1) → ℂ => ∑ j ∈ Finset.range (k + 1),
          (-1) ^ (k - j) * (sliceRoots f t (Fin.tail w)).esymm (k - j) * (w 0) ^ j := by
    funext w
    rw [Finset.sum_apply]
  rw [hfun] at hsum
  refine hsum.congr fun w hw => ?_
  rw [sliceWeierstrass, multisetLinearProd_eq_sum, hcard (Fin.tail w) hw]

end HTGeometry
