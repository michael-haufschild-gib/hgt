import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninCutoffTraceFormula

/-!
# The archimedean carrier is indefinite

The archimedean Weil distribution is a trace (RHTower CCM):
`−W_∞(g★ ⋆ g) = Tr(ϑ(g) A ϑ(g)†)`, `A = 1 − P − P̂`, with `P` the time cutoff and `P̂` the band
cutoff on the even carrier. A trace of a positive operator would be a positivity statement that holds
by structure; this file shows what the middle operator of two projections is.

* **Two-projection identities** (`twoProjection_sq_add_sq`, `twoProjection_anticomm`): for
  self-adjoint idempotents `P, Q`, `A = 1 − P − Q` satisfies `A² + (P − Q)² = 1` and
  `A(P − Q) = −(P − Q)A`. On the generic part (where `P − Q` is injective) `P − Q` exchanges the
  positive and negative spectral subspaces of `A`: its spectrum is symmetric.
* **Negative on each range** (`re_inner_twoProjection_of_fixed_left`,
  `re_inner_twoProjection_of_fixed_right`): `Re⟨Av, v⟩ = −‖Qv‖²` if `Pv = v`, and `−‖Pv‖²` if
  `Qv = v`.
* **Identity on the common kernel** (`twoProjection_apply_of_ker`): `Av = v` if `Pv = 0 = Qv`.
* **The archimedean carrier** (`archimedeanCarrier_negative_on_timeLimited`,
  `archimedeanCarrier_negative_on_bandLimited`): `1 − P₁ − P̂₁` is negative semidefinite on the
  whole time-limited space and on the whole band-limited space. The trace identity at `∞` is an
  identity with an indefinite middle operator: the archimedean place alone is not a positive
  carrier, and the pole terms of Weil's form must pay its negative part.
-/

noncomputable section

open ContinuousLinearMap
open scoped InnerProductSpace

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Two-projection identity.** `(1 − P − Q)² + (P − Q)² = 1` for idempotents. -/
theorem twoProjection_sq_add_sq {P Q : E →L[ℂ] E} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) :
    (1 - P - Q) * (1 - P - Q) + (P - Q) * (P - Q) = 1 := by
  have h1 : (1 - P - Q) * (1 - P - Q) = 1 - P - Q - P + P * P + P * Q - Q + Q * P + Q * Q := by
    noncomm_ring
  have h2 : (P - Q) * (P - Q) = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
  rw [h1, h2, hP.eq, hQ.eq]
  abel

omit [CompleteSpace E] in
/-- **Anticommutation.** `(1 − P − Q)(P − Q) = −(P − Q)(1 − P − Q)` for idempotents. -/
theorem twoProjection_anticomm {P Q : E →L[ℂ] E} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) :
    (1 - P - Q) * (P - Q) = -((P - Q) * (1 - P - Q)) := by
  have h1 : (1 - P - Q) * (P - Q) = P - Q - P * P + P * Q - Q * P + Q * Q := by noncomm_ring
  have h2 : (P - Q) * (1 - P - Q) = P - P * P - P * Q - Q + Q * P + Q * Q := by noncomm_ring
  rw [h1, h2, hP.eq, hQ.eq]
  abel

/-- For a self-adjoint idempotent, `Re⟨Pv, v⟩ = ‖Pv‖²`. -/
theorem inner_projection_self {P : E →L[ℂ] E} (hP : IsIdempotentElem P)
    (hPa : ContinuousLinearMap.adjoint P = P) (v : E) :
    RCLike.re ⟪P v, v⟫_ℂ = ‖P v‖ ^ 2 := by
  have hPP : P (P v) = P v := congrArg (fun T : E →L[ℂ] E => T v) hP.eq
  have h : ⟪P v, v⟫_ℂ = ⟪P v, P v⟫_ℂ := by
    calc ⟪P v, v⟫_ℂ = ⟪P (P v), v⟫_ℂ := by rw [hPP]
      _ = ⟪P v, (ContinuousLinearMap.adjoint P) v⟫_ℂ := (adjoint_inner_right P (P v) v).symm
      _ = ⟪P v, P v⟫_ℂ := by rw [hPa]
  rw [h, inner_self_eq_norm_sq]

/-- **Negative on the range of the first projection.** If `Pv = v`, `Re⟨(1 − P − Q)v, v⟩ = −‖Qv‖²`. -/
theorem re_inner_twoProjection_of_fixed_left {P Q : E →L[ℂ] E} (hQ : IsIdempotentElem Q)
    (hQa : ContinuousLinearMap.adjoint Q = Q) {v : E} (hv : P v = v) :
    RCLike.re ⟪(1 - P - Q) v, v⟫_ℂ = -‖Q v‖ ^ 2 := by
  have h : (1 - P - Q) v = -(Q v) := by
    simp only [sub_apply, one_apply_eq_self, hv, sub_self, zero_sub]
  rw [h, inner_neg_left, map_neg, inner_projection_self hQ hQa]

/-- **Negative on the range of the second projection.** If `Qv = v`, `Re⟨(1 − P − Q)v, v⟩ = −‖Pv‖²`. -/
theorem re_inner_twoProjection_of_fixed_right {P Q : E →L[ℂ] E} (hP : IsIdempotentElem P)
    (hPa : ContinuousLinearMap.adjoint P = P) {v : E} (hv : Q v = v) :
    RCLike.re ⟪(1 - P - Q) v, v⟫_ℂ = -‖P v‖ ^ 2 := by
  have h : (1 - P - Q) v = -(P v) := by
    simp only [sub_apply, one_apply_eq_self, hv]
    abel
  rw [h, inner_neg_left, map_neg, inner_projection_self hP hPa]

omit [CompleteSpace E] in
/-- **Identity on the common kernel.** -/
theorem twoProjection_apply_of_ker {P Q : E →L[ℂ] E} {v : E} (hP : P v = 0) (hQ : Q v = 0) :
    (1 - P - Q) v = v := by
  simp [sub_apply, hP, hQ]

open _root_.RHTower in
/-- **The archimedean carrier is negative on the time-limited space.** For every even vector
supported in the unit interval, `Re⟨(1 − P₁ − P̂₁)v, v⟩ = −‖P̂₁ v‖² ≤ 0`. -/
theorem archimedeanCarrier_negative_on_timeLimited {v : evenSubspace}
    (hv : evenIndicatorCutoff 1 v = v) :
    RCLike.re ⟪(1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) v, v⟫_ℂ =
      -‖evenFourierCutoff 1 v‖ ^ 2 :=
  re_inner_twoProjection_of_fixed_left evenFourierCutoff_one_mul_self (adjoint_evenFourierCutoff 1) hv

open _root_.RHTower in
/-- **The archimedean carrier is negative on the band-limited space.** -/
theorem archimedeanCarrier_negative_on_bandLimited {v : evenSubspace}
    (hv : evenFourierCutoff 1 v = v) :
    RCLike.re ⟪(1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) v, v⟫_ℂ =
      -‖evenIndicatorCutoff 1 v‖ ^ 2 :=
  re_inner_twoProjection_of_fixed_right (evenIndicatorCutoff_idempotent 1)
    (adjoint_evenIndicatorCutoff 1) hv

open _root_.RHTower in
/-- The middle operator of the archimedean trace identity satisfies the two-projection identities. -/
theorem archimedeanCarrier_twoProjection :
    (1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) * (1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) +
        (evenIndicatorCutoff 1 - evenFourierCutoff 1) * (evenIndicatorCutoff 1 - evenFourierCutoff 1) = 1 ∧
      (1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) * (evenIndicatorCutoff 1 - evenFourierCutoff 1) =
        -((evenIndicatorCutoff 1 - evenFourierCutoff 1) * (1 - evenIndicatorCutoff 1 - evenFourierCutoff 1)) :=
  ⟨twoProjection_sq_add_sq (evenIndicatorCutoff_idempotent 1) evenFourierCutoff_one_mul_self,
    twoProjection_anticomm (evenIndicatorCutoff_idempotent 1) evenFourierCutoff_one_mul_self⟩

end GaloisForLFunctions.ArithmeticDegenerationTheory
