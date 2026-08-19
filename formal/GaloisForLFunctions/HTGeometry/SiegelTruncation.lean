import GaloisForLFunctions.HTGeometry.SiegelTopRow

/-!
# Truncating Jacobi data

The leading `k × k` part of a Jacobi datum is again a Jacobi datum, its form is the leading block of
the original form, and it inherits both Siegel bounds — the diagonal bound because it constrains
consecutive indices, all of which survive truncation, and the unipotent bound entrywise.

This is the structure the descending induction of Siegel's finiteness runs on: having bounded the
top row, one restricts to the leading block and repeats.

* `JacobiData.trunc` : the leading sub-datum.
* `JacobiData.trunc_form` : **its form is the leading block.**
* `JacobiData.trunc_isSiegel`, `trunc_sizeReduced` : the bounds are inherited.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The leading `k × k` sub-datum. -/
def JacobiData.trunc (J : JacobiData n) {k : ℕ} (hk : k ≤ n) : JacobiData k where
  U := leadingBlock hk J.U
  d := fun m => J.d (Fin.castLE hk m)
  pos := fun _ => J.pos _
  upper := fun i j hji => leadingBlock_upper hk J.upper i j hji
  unit := fun i => leadingBlock_unit hk J.unit i

@[simp]
theorem JacobiData.trunc_d (J : JacobiData n) {k : ℕ} (hk : k ≤ n) (m : Fin k) :
    (J.trunc hk).d m = J.d (Fin.castLE hk m) := rfl

@[simp]
theorem JacobiData.trunc_U (J : JacobiData n) {k : ℕ} (hk : k ≤ n) (i j : Fin k) :
    (J.trunc hk).U i j = J.U (Fin.castLE hk i) (Fin.castLE hk j) := rfl

/-- **The form of the truncation is the leading block of the form.** -/
theorem JacobiData.trunc_form (J : JacobiData n) {k : ℕ} (hk : k ≤ n) :
    (J.trunc hk).form = leadingBlock hk J.form :=
  (leadingBlock_congr hk J.upper J.d).symm

/-- The Siegel bounds are inherited by the truncation. -/
theorem JacobiData.trunc_isSiegel (J : JacobiData n) {k : ℕ} (hk : k ≤ n) {t u : ℝ}
    (hS : J.IsSiegel t u) : (J.trunc hk).IsSiegel t u := by
  refine ⟨fun i j hij => ?_, fun i j => hS.2 _ _⟩
  exact hS.1 (Fin.castLE hk i) (Fin.castLE hk j) (by simpa using hij)

/-- Size reduction is inherited by the truncation. -/
theorem JacobiData.trunc_sizeReduced (J : JacobiData n) {k : ℕ} (hk : k ≤ n)
    (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2) (a b : Fin k) (hab : a < b) :
    |(J.trunc hk).U a b| ≤ 1 / 2 :=
  hred _ _ (by simpa using hab)

end GaloisForLFunctions.HTGeometry
