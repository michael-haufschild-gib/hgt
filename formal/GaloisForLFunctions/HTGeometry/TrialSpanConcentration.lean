import GaloisForLFunctions.HTGeometry.TruncatedFixedVector
import GaloisForLFunctions.HTGeometry.OrthonormalTrialSpan

/-!
# Concentration on the span of a family of truncated fixed vectors

A variational lower bound for a compressed operator `T = P U P` needs a subspace on which `T`
loses little norm.  Two steps produce one.

First, a single vector fixed by the isometry `U` is moved by `T` only by twice its truncation
error:

```text
h − P U P h = (h − P h) + P U (h − P h),
```

because `U h = h` lets the middle term be rewritten as `U` applied to the truncation defect, and
both `P` and `U` are contractions on it.  So `‖h − T h‖ ≤ 2‖h − P h‖`, with no squares lost —
unlike the norm-squared form, which is the right tool only for a one-dimensional trial space.

Second, a defect bound valid on each member of an orthonormal family of size `m` aggregates to
the whole span at the cost of `√m`, by the Bessel–Chebyshev estimate.  Subtracting from the
identity converts that into the lower bound

```text
(1 − √m·η)² ‖f‖² ≤ ‖T f‖²        for every `f` in the span,
```

which is exactly the hypothesis shape a Courant–Fischer argument consumes.  Nothing here is
specific to the Fourier transform: any isometry with an orthonormal family of fixed vectors and
any orthogonal projection will do.
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A projection satisfying the Pythagorean identity is a contraction. -/
theorem norm_proj_le {P : H →L[ℂ] H}
    (hpyth : ∀ x : H, ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2) (x : H) :
    ‖P x‖ ≤ ‖x‖ := by
  have hp := hpyth x
  nlinarith [norm_nonneg (x - P x), norm_nonneg x, norm_nonneg (P x), sq_nonneg ‖x - P x‖]

/-- **A fixed vector is moved by the compressed operator only by twice its truncation error.**
The linear form of the estimate: no square is lost, so it survives aggregation over a family. -/
theorem norm_sub_proj_unitary_proj_le {U P : H →L[ℂ] H}
    (hU : ∀ x : H, ‖U x‖ = ‖x‖)
    (hpyth : ∀ x : H, ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2)
    {h : H} (hUh : U h = h) :
    ‖h - P (U (P h))‖ ≤ 2 * ‖h - P h‖ := by
  have hUsub : U (h - P h) = h - U (P h) := by
    rw [map_sub, hUh]
  have hsplit : h - P (U (P h)) = (h - P h) + P (U (h - P h)) := by
    rw [hUsub, map_sub]
    abel
  have hbound : ‖P (U (h - P h))‖ ≤ ‖h - P h‖ := by
    calc ‖P (U (h - P h))‖ ≤ ‖U (h - P h)‖ := norm_proj_le hpyth _
      _ = ‖h - P h‖ := hU _
  calc ‖h - P (U (P h))‖ = ‖(h - P h) + P (U (h - P h))‖ := by rw [hsplit]
    _ ≤ ‖h - P h‖ + ‖P (U (h - P h))‖ := norm_add_le _ _
    _ ≤ ‖h - P h‖ + ‖h - P h‖ := by linarith
    _ = 2 * ‖h - P h‖ := by ring

/-- **Concentration on the span.**  If an operator moves each member of an orthonormal family of
size `m` by at most `η`, then on the whole span it retains a fraction `(1 − √m·η)²` of the
squared norm. -/
theorem norm_sq_apply_ge_of_orthonormal_span {m : ℕ} {g : Fin m → H} (hg : Orthonormal ℂ g)
    (T : H →L[ℂ] H) {η : ℝ} (hη0 : 0 ≤ η) (hη : ∀ k, ‖g k - T (g k)‖ ≤ η)
    (hηm : Real.sqrt m * η ≤ 1)
    {f : H} (hf : f ∈ Submodule.span ℂ (Set.range g)) :
    (1 - Real.sqrt m * η) ^ 2 * ‖f‖ ^ 2 ≤ ‖T f‖ ^ 2 := by
  set R : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - T with hR
  have hRapply : ∀ x : H, R x = x - T x := fun x => by
    rw [hR, _root_.sub_apply, ContinuousLinearMap.id_apply]
  have hRk : ∀ k, ‖R (g k)‖ ≤ η := fun k => by rw [hRapply]; exact hη k
  have hagg := norm_sq_apply_le_of_orthonormal_span hg R hRk hf
  have hsqrt : ‖R f‖ ≤ Real.sqrt m * η * ‖f‖ := by
    have hnn : (0 : ℝ) ≤ Real.sqrt m * η * ‖f‖ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hη0) (norm_nonneg _)
    have hsq : ‖R f‖ ^ 2 ≤ (Real.sqrt m * η * ‖f‖) ^ 2 := by
      have hm : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
      calc ‖R f‖ ^ 2 ≤ (m * η ^ 2) * ‖f‖ ^ 2 := hagg
        _ = (Real.sqrt m * η * ‖f‖) ^ 2 := by rw [mul_pow, mul_pow, hm]
    nlinarith [hsq, norm_nonneg (R f), hnn]
  have hTf : (1 - Real.sqrt m * η) * ‖f‖ ≤ ‖T f‖ := by
    have hsub : T f = f - R f := by rw [hRapply]; abel
    have := norm_sub_norm_le f (R f)
    rw [hsub]
    calc (1 - Real.sqrt m * η) * ‖f‖ = ‖f‖ - Real.sqrt m * η * ‖f‖ := by ring
      _ ≤ ‖f‖ - ‖R f‖ := by linarith
      _ ≤ ‖f - R f‖ := this
  have hnn : (0 : ℝ) ≤ (1 - Real.sqrt m * η) * ‖f‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  calc (1 - Real.sqrt m * η) ^ 2 * ‖f‖ ^ 2 = ((1 - Real.sqrt m * η) * ‖f‖) ^ 2 := by ring
    _ ≤ ‖T f‖ ^ 2 := by nlinarith [hTf, hnn, norm_nonneg (T f)]

end ContinuousLinearMap
