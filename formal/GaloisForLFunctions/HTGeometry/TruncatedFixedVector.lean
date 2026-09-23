import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Truncating a Fourier-fixed vector loses only twice the truncation error

A prolate trial function is obtained by cutting a Fourier-invariant profile down to the aperture.
The resulting vector is no longer Fourier-invariant, but it is nearly so, and the deficit is
controlled by the mass removed by the cut alone.

Let `U` be an isometry fixing `h`, let `P` be an orthogonal projection — used only through the
Pythagorean identity `‖x‖² = ‖Px‖² + ‖x − Px‖²` — and set `τ = ‖h − Ph‖`, the mass the cut
removes.  Writing `Ph = h − (h − Ph)` and applying `U`,

```text
U(Ph) = h − U(h − Ph),
```

so the part of `U(Ph)` outside the range of `P` is at most `τ` from `h − Ph` and at most `τ`
again from the second term: `‖U(Ph) − P(U(Ph))‖ ≤ 2τ`.  Pythagoras and the isometry then give

```text
‖P U P h‖² ≥ ‖Ph‖² − 4τ².
```

Applied to the Gaussian, which is Fourier-fixed, and to the aperture cut, this converts the
Gaussian tail bound directly into a concentration estimate for the truncated Gaussian — the form
a Courant–Fischer trial space consumes.
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Pythagorean identity forces the complementary part to be a contraction. -/
theorem norm_sub_proj_le {P : H →L[ℂ] H}
    (hpyth : ∀ x : H, ‖x‖ ^ (2 : ℕ) = ‖P x‖ ^ (2 : ℕ) + ‖x - P x‖ ^ (2 : ℕ)) (x : H) :
    ‖x - P x‖ ≤ ‖x‖ := by
  have hp := hpyth x
  nlinarith [norm_nonneg (x - P x), norm_nonneg x, sq_nonneg ‖P x‖]

/-- **Truncation of a fixed vector.**  If the isometry `U` fixes `h` and `P` is an orthogonal
projection, then the truncated vector `Ph` retains its norm under `P U ·` up to four times the
squared truncation error. -/
theorem norm_sq_proj_unitary_proj_ge {U P : H →L[ℂ] H}
    (hU : ∀ x : H, ‖U x‖ = ‖x‖)
    (hpyth : ∀ x : H, ‖x‖ ^ (2 : ℕ) = ‖P x‖ ^ (2 : ℕ) + ‖x - P x‖ ^ (2 : ℕ))
    {h : H} (hUh : U h = h) :
    ‖P h‖ ^ (2 : ℕ) - 4 * ‖h - P h‖ ^ (2 : ℕ) ≤ ‖P (U (P h))‖ ^ (2 : ℕ) := by
  have hUf : U (P h) = h - U (h - P h) := by
    have hms : U (h - (h - P h)) = U h - U (h - P h) := map_sub U h (h - P h)
    rw [hUh, show h - (h - P h) = P h from by abel] at hms
    exact hms
  have hrw : U (P h) - P (U (P h))
      = (h - P h) - (U (h - P h) - P (U (h - P h))) := by
    rw [hUf, show P (h - U (h - P h)) = P h - P (U (h - P h)) from
      map_sub P h (U (h - P h))]
    abel
  have hτ1 : ‖U (h - P h) - P (U (h - P h))‖ ≤ ‖h - P h‖ := by
    calc ‖U (h - P h) - P (U (h - P h))‖ ≤ ‖U (h - P h)‖ := norm_sub_proj_le hpyth _
      _ = ‖h - P h‖ := hU _
  have hbound : ‖U (P h) - P (U (P h))‖ ≤ 2 * ‖h - P h‖ := by
    rw [hrw]
    calc ‖(h - P h) - (U (h - P h) - P (U (h - P h)))‖
        ≤ ‖h - P h‖ + ‖U (h - P h) - P (U (h - P h))‖ := norm_sub_le _ _
      _ ≤ ‖h - P h‖ + ‖h - P h‖ := by linarith [hτ1]
      _ = 2 * ‖h - P h‖ := by ring
  have hpy := hpyth (U (P h))
  have hnorm : ‖U (P h)‖ = ‖P h‖ := hU _
  rw [hnorm] at hpy
  nlinarith [hbound, norm_nonneg (U (P h) - P (U (P h))), norm_nonneg (h - P h)]


/-! ## Pythagoras from a star projection -/

/-- An idempotent symmetric operator splits every vector orthogonally, so the Pythagorean
identity the truncation estimate consumes is automatic for a star projection. -/
theorem norm_sq_eq_of_isIdempotent_symmetric {P : H →L[ℂ] H}
    (hPP : ∀ x : H, P (P x) = P x)
    (hsym : ∀ x y : H, inner ℂ (P x) y = inner ℂ x (P y)) (x : H) :
    ‖x‖ ^ (2 : ℕ) = ‖P x‖ ^ (2 : ℕ) + ‖x - P x‖ ^ (2 : ℕ) := by
  have horth : inner ℂ (P x) (x - P x) = 0 := by
    have e1 : inner ℂ (P x) x = inner ℂ x (P x) := hsym x x
    have e2 : inner ℂ (P x) (P x) = inner ℂ x (P x) := by
      rw [hsym x (P x), hPP]
    rw [inner_sub_right, e1, e2, sub_self]
  have hsplit : P x + (x - P x) = x := by abel
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (x - P x) horth
  rw [hsplit] at hpy
  calc ‖x‖ ^ (2 : ℕ) = ‖x‖ * ‖x‖ := by ring
    _ = ‖P x‖ * ‖P x‖ + ‖x - P x‖ * ‖x - P x‖ := hpy
    _ = ‖P x‖ ^ (2 : ℕ) + ‖x - P x‖ ^ (2 : ℕ) := by ring

/-- The truncation estimate for a star projection, with Pythagoras discharged. -/
theorem norm_sq_proj_unitary_proj_ge' {U P : H →L[ℂ] H}
    (hU : ∀ x : H, ‖U x‖ = ‖x‖)
    (hPP : ∀ x : H, P (P x) = P x)
    (hsym : ∀ x y : H, inner ℂ (P x) y = inner ℂ x (P y))
    {h : H} (hUh : U h = h) :
    ‖P h‖ ^ (2 : ℕ) - 4 * ‖h - P h‖ ^ (2 : ℕ) ≤ ‖P (U (P h))‖ ^ (2 : ℕ) :=
  norm_sq_proj_unitary_proj_ge hU (norm_sq_eq_of_isIdempotent_symmetric hPP hsym) hUh

/-! ## The concentration form consumed by a trial space -/

/-- **Truncation concentration.**  If the truncation error is at most `θ` times the norm of the
truncated vector, the truncated vector retains at least `1 − 4θ²` of its squared norm under
`P U ·` — exactly the form `evenProlateLeakageValue_le_of_form_trial` consumes, with
`ε = 4θ²`. -/
theorem norm_sq_proj_unitary_proj_ge_of_rel {U P : H →L[ℂ] H}
    (hU : ∀ x : H, ‖U x‖ = ‖x‖)
    (hPP : ∀ x : H, P (P x) = P x)
    (hsym : ∀ x y : H, inner ℂ (P x) y = inner ℂ x (P y))
    {h : H} (hUh : U h = h) {θ : ℝ} (hθ : ‖h - P h‖ ≤ θ * ‖P h‖) :
    (1 - 4 * θ ^ (2 : ℕ)) * ‖P h‖ ^ (2 : ℕ) ≤ ‖P (U (P h))‖ ^ (2 : ℕ) := by
  have hmain := norm_sq_proj_unitary_proj_ge' hU hPP hsym hUh
  have hsq : ‖h - P h‖ ^ (2 : ℕ) ≤ θ ^ (2 : ℕ) * ‖P h‖ ^ (2 : ℕ) := by
    have h1 : ‖h - P h‖ ^ (2 : ℕ) ≤ (θ * ‖P h‖) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hθ 2
    calc ‖h - P h‖ ^ (2 : ℕ) ≤ (θ * ‖P h‖) ^ (2 : ℕ) := h1
      _ = θ ^ (2 : ℕ) * ‖P h‖ ^ (2 : ℕ) := by ring
  nlinarith [hmain, hsq]

end ContinuousLinearMap
