/-
# The chordal (spherical) metric on `ℂ̂` — second brick of the Marty/Zalcman layer

The Marty normality criterion measures a family in the **chordal metric**
`χ(z,w) = ‖z - w‖ / (√(1+‖z‖²)·√(1+‖w‖²))` — the metric of the Riemann sphere `ℂ̂` realised on `ℂ`.
This file sets it up (non-negativity, symmetry, the squared form) and banks the **stereographic chordal
identity**: `χ` is exactly half the Euclidean chord between the stereographic images on the unit
sphere, `‖Φz - Φw‖² = 4·χ(z,w)²` with `Φz = (2x, 2y, ‖z‖²-1)/(1+‖z‖²)`.

That identity is the crux of the Marty equicontinuity bound `σf ≤ M ⟹ χ(fa,fb) ≤ M‖a-b‖`: realising
`χ` as a genuine sphere chord turns the bound into the Euclidean mean-value inequality
`‖Φ(fa) - Φ(fb)‖ ≤ (length of the lifted path) ≤ 2M‖a-b‖`, where the round-metric speed of `Φ∘f` is
`2·sphericalDeriv f`. The derivative/mean-value step is the next brick; the geometric content is here.

New file (Montel/Julia lane — spherical normality foundation). General lemmas; Mathlib only.
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open Complex

namespace Bottcher

/-- **Chordal (spherical) metric** on `ℂ`: `χ(z,w) = ‖z-w‖ / (√(1+‖z‖²)·√(1+‖w‖²))`, the Riemann-sphere
distance, in which Marty's normality criterion is stated. -/
noncomputable def chordalDist (z w : ℂ) : ℝ :=
  ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))

theorem chordalDist_nonneg (z w : ℂ) : 0 ≤ chordalDist z w := by
  unfold chordalDist; positivity

theorem chordalDist_comm (z w : ℂ) : chordalDist z w = chordalDist w z := by
  unfold chordalDist; rw [norm_sub_rev]; ring

theorem chordalDist_self (z : ℂ) : chordalDist z z = 0 := by
  unfold chordalDist; simp

/-- The squared chordal distance: `χ(z,w)² = ‖z-w‖² / ((1+‖z‖²)(1+‖w‖²))`. -/
theorem chordalDist_sq (z w : ℂ) :
    chordalDist z w ^ 2 = ‖z - w‖ ^ 2 / ((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) := by
  unfold chordalDist
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

/-- The chordal distance never exceeds the Euclidean distance (the denominator is `≥ 1`). -/
theorem chordalDist_le_norm (z w : ℂ) : chordalDist z w ≤ ‖z - w‖ := by
  unfold chordalDist
  apply div_le_self (norm_nonneg _)
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 + ‖z‖ ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 + ‖z‖ ^ 2),
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + ‖z‖ ^ 2 by positivity), sq_nonneg ‖z‖]
  have h2 : (1 : ℝ) ≤ Real.sqrt (1 + ‖w‖ ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 + ‖w‖ ^ 2),
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + ‖w‖ ^ 2 by positivity), sq_nonneg ‖w‖]
  nlinarith [h1, h2, Real.sqrt_nonneg (1 + ‖z‖ ^ 2), Real.sqrt_nonneg (1 + ‖w‖ ^ 2)]

/-- **Stereographic chordal identity** — the crux for Marty's estimate. With the stereographic
embedding `Φz = (2x, 2y, ‖z‖²-1)/(1+‖z‖²)` of `ℂ` onto the unit sphere (`z = x + iy`), the squared
Euclidean chord equals `4·χ(z,w)²`:
`‖Φz - Φw‖² = 4·((x-x')² + (y-y')²) / ((1+‖z‖²)(1+‖w‖²))`.
This realises the chordal metric as a genuine sphere chord, so the Marty equicontinuity bound becomes
the Euclidean mean-value inequality applied to the lifted path `Φ ∘ f`. -/
theorem chordal_stereo_identity (a b c d : ℝ) :
    (2 * a / (1 + a ^ 2 + b ^ 2) - 2 * c / (1 + c ^ 2 + d ^ 2)) ^ 2
      + (2 * b / (1 + a ^ 2 + b ^ 2) - 2 * d / (1 + c ^ 2 + d ^ 2)) ^ 2
      + ((a ^ 2 + b ^ 2 - 1) / (1 + a ^ 2 + b ^ 2) - (c ^ 2 + d ^ 2 - 1) / (1 + c ^ 2 + d ^ 2)) ^ 2
      = 4 * ((a - c) ^ 2 + (b - d) ^ 2) / ((1 + a ^ 2 + b ^ 2) * (1 + c ^ 2 + d ^ 2)) := by
  have h1 : (1 : ℝ) + a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have h2 : (1 : ℝ) + c ^ 2 + d ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Stereographic embedding** `ℂ → S² ⊂ ℝ³`, `z = x+iy ↦ (2x, 2y, ‖z‖²-1)/(1+‖z‖²)`. -/
noncomputable def stereo (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * z.re / (1 + ‖z‖ ^ 2), 2 * z.im / (1 + ‖z‖ ^ 2), (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)]

/-- **The chordal metric IS a Euclidean chord**: `‖Φz - Φw‖_{ℝ³} = 2·χ(z,w)`. This is the bridge
that makes the Marty equicontinuity bound a consequence of the Euclidean mean-value inequality —
`χ(f a, f b) = ½‖Φ(f a) - Φ(f b)‖ ≤ ½·(length of Φ∘f over [a,b])`. Proven by squaring, via the
stereographic chordal identity. -/
theorem norm_stereo_sub (z w : ℂ) : ‖stereo z - stereo w‖ = 2 * chordalDist z w := by
  have hnn : 0 ≤ 2 * chordalDist z w := by have := chordalDist_nonneg z w; linarith
  have hsq : ‖stereo z - stereo w‖ ^ 2 = (2 * chordalDist z w) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp only [stereo, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.isValue, Real.norm_eq_abs, sq_abs]
    rw [show (2 * chordalDist z w) ^ 2 = 4 * chordalDist z w ^ 2 by ring, chordalDist_sq]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    have h1 : (1 : ℝ) + (z.re * z.re + z.im * z.im) ≠ 0 :=
      (show (0 : ℝ) < 1 + (z.re * z.re + z.im * z.im) by
        nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]).ne'
    have h2 : (1 : ℝ) + (w.re * w.re + w.im * w.im) ≠ 0 :=
      (show (0 : ℝ) < 1 + (w.re * w.re + w.im * w.im) by
        nlinarith [mul_self_nonneg w.re, mul_self_nonneg w.im]).ne'
    field_simp
    ring
  rw [← Real.sqrt_sq (norm_nonneg (stereo z - stereo w)), hsq, Real.sqrt_sq hnn]

/-- **Conformality of stereographic projection** (the geometric core of the Marty derivative bound).
With `Φ(x,y) = (2x, 2y, x²+y²-1)/D`, `D = 1+x²+y²`, the Jacobian columns `J₁ = ∂ₓΦ`, `J₂ = ∂_yΦ` are
orthogonal and have equal norm `2/D`. Hence `DΦ` is a similarity with factor `2/(1+‖z‖²)`, so
`‖D(Φ∘f)‖ = ‖f'‖·2/(1+‖f‖²) = 2·sphericalDeriv f` — the round-metric speed feeding Marty's
equicontinuity `χ(fa,fb) ≤ M‖a-b‖`. Banked here as the real-algebra identities (`field_simp; ring`). -/
theorem stereo_conformal_identities (x y : ℝ) :
    let D := 1 + x ^ 2 + y ^ 2
    ((2 * (1 - x ^ 2 + y ^ 2) / D ^ 2) ^ 2 + (-4 * x * y / D ^ 2) ^ 2 + (4 * x / D ^ 2) ^ 2
        = (2 / D) ^ 2)
      ∧ ((-4 * x * y / D ^ 2) ^ 2 + (2 * (1 + x ^ 2 - y ^ 2) / D ^ 2) ^ 2 + (4 * y / D ^ 2) ^ 2
        = (2 / D) ^ 2)
      ∧ ((2 * (1 - x ^ 2 + y ^ 2) / D ^ 2) * (-4 * x * y / D ^ 2)
          + (-4 * x * y / D ^ 2) * (2 * (1 + x ^ 2 - y ^ 2) / D ^ 2)
          + (4 * x / D ^ 2) * (4 * y / D ^ 2) = 0) := by
  intro D
  have hD : D ≠ 0 := by simp only [D]; positivity
  refine ⟨?_, ?_, ?_⟩ <;> (field_simp [D]; ring)

/-- **Dynamic round-speed identity** — the path version of conformality, the analytic core of Marty's
estimate. For a path `t ↦ (u(t), v(t))` in `ℂ` with velocity `(u', v')`, the velocity of the lifted
path `t ↦ stereo(u,v)` has squared norm `(2/D)²·(u'² + v'²)` (`D = 1+u²+v²`). Hence the round speed of
`stereo ∘ f ∘ γ` is `(2/(1+‖f‖²))·‖(f∘γ)'‖ = 2·sphericalDeriv f·‖γ'‖`, the bound that the Euclidean
mean-value inequality integrates into `χ(fa,fb) ≤ M‖a-b‖`. (`Dp = D' = 2uu'+2vv'`; the three terms
are the component velocities `∂ₜ(2u/D), ∂ₜ(2v/D), ∂ₜ((u²+v²-1)/D)`.) -/
theorem stereo_speed_identity (u v u' v' : ℝ) :
    let D := 1 + u ^ 2 + v ^ 2
    let Dp := 2 * u * u' + 2 * v * v'
    ((2 * u' * D - 2 * u * Dp) / D ^ 2) ^ 2 + ((2 * v' * D - 2 * v * Dp) / D ^ 2) ^ 2
        + (Dp * 2 / D ^ 2) ^ 2
      = (2 / D) ^ 2 * (u' ^ 2 + v' ^ 2) := by
  intro D Dp
  have hD : D ≠ 0 := by simp only [D]; positivity
  field_simp [D, Dp]
  ring

/-- Norm of a 3-vector in `EuclideanSpace ℝ (Fin 3)`: `‖!₂[a,b,c]‖ = √(a²+b²+c²)`. -/
theorem norm_euclidean3 (a b c : ℝ) :
    ‖(!₂[a, b, c] : EuclideanSpace ℝ (Fin 3))‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, sq_abs]

/-- **Component-wise `HasDerivAt` into `EuclideanSpace (Fin 3)`** (analytic plumbing for the Marty
derivative). If the three coordinate functions have derivatives `d₀,d₁,d₂` at `t`, then the
`EuclideanSpace`-valued path `t ↦ !₂[g₀,g₁,g₂]` has derivative `!₂[d₀,d₁,d₂]`. (Transferred from the
plain `hasDerivAt_pi` through the `PiLp ≃L Pi` isometry — derivatives are norm-independent.) -/
theorem hasDerivAt_euclidean3 {g0 g1 g2 : ℝ → ℝ} {d0 d1 d2 t : ℝ}
    (h0 : HasDerivAt g0 d0 t) (h1 : HasDerivAt g1 d1 t) (h2 : HasDerivAt g2 d2 t) :
    HasDerivAt (fun s => (!₂[g0 s, g1 s, g2 s] : EuclideanSpace ℝ (Fin 3)))
      (!₂[d0, d1, d2] : EuclideanSpace ℝ (Fin 3)) t := by
  have hpi : HasDerivAt (fun s => (![g0 s, g1 s, g2 s] : Fin 3 → ℝ)) (![d0, d1, d2]) t := by
    rw [hasDerivAt_pi]
    intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi

end Bottcher
