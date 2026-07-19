import GaloisForLFunctions.RHTower.ConstrainedProlateEigenvectorAngle
import GaloisForLFunctions.HTGeometry.SignChoiceNormalizedDistance
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The constrained ground direction in metric form

The exact constrained eigenvector is pinned in its head plane by a single linear condition: it
pairs against the constraint vector `(ℓ₀, ℓ₁)` by exactly the negative of the infinite tail.  As
the tail collapses, the head becomes orthogonal to the constraint, and in a plane the directions
orthogonal to a fixed nonzero vector form a single line — spanned by `(−ℓ₁, ℓ₀)`.  So the head
direction converges to the two-mode seed direction.

Recording that convergence metrically rather than projectively costs only a choice of sign, since
`‖u ∓ w‖² = 2 ∓ 2⟪u,w⟫` for unit vectors.  The geometric input is the Lagrange identity

```text
(x₀ℓ₀ + x₁ℓ₁)² + (x₁ℓ₀ − x₀ℓ₁)² = (x₀² + x₁²)(ℓ₀² + ℓ₁²),
```

which says the squared components along `(ℓ₀, ℓ₁)` and along `(−ℓ₁, ℓ₀)` exhaust the squared
length: a vanishing relative component along the constraint is a full relative component along
the seed.
-/

open Filter GaloisForLFunctions
open scoped Real

noncomputable section

namespace RHTower

variable (d ℓ : ℕ → ℝ) (μ : ℝ)

/-! ## The head plane -/

/-- The head of the exact constrained eigenvector, as a vector of the plane. -/
def secularHead : EuclideanSpace ℝ (Fin 2) :=
  !₂[secularVector d ℓ μ 0, secularVector d ℓ μ 1]

/-- The constraint direction in the head plane. -/
def constraintNormal : EuclideanSpace ℝ (Fin 2) := !₂[ℓ 0, ℓ 1]

/-- The two-mode seed direction: the direction of the head plane orthogonal to the constraint. -/
def twoModeSeed : EuclideanSpace ℝ (Fin 2) := !₂[-(ℓ 1), ℓ 0]

/-- The squared length of a plane vector in coordinates. -/
theorem norm_sq_euclid (a b : ℝ) : ‖(!₂[a, b] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

/-- The inner product of two plane vectors in coordinates. -/
theorem inner_euclid (a b c e : ℝ) :
    inner ℝ (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, e] = a * c + b * e := by
  simp [EuclideanSpace.inner_eq_star_dotProduct]
  ring

theorem norm_sq_secularHead :
    ‖secularHead d ℓ μ‖ ^ 2 = secularVector d ℓ μ 0 ^ 2 + secularVector d ℓ μ 1 ^ 2 :=
  norm_sq_euclid _ _

theorem norm_sq_constraintNormal : ‖constraintNormal ℓ‖ ^ 2 = ℓ 0 ^ 2 + ℓ 1 ^ 2 :=
  norm_sq_euclid _ _

theorem norm_sq_twoModeSeed : ‖twoModeSeed ℓ‖ ^ 2 = ℓ 0 ^ 2 + ℓ 1 ^ 2 := by
  rw [twoModeSeed, norm_sq_euclid]
  ring

/-- The seed is orthogonal to the constraint. -/
theorem inner_constraintNormal_twoModeSeed : inner ℝ (constraintNormal ℓ) (twoModeSeed ℓ) = 0 := by
  rw [constraintNormal, twoModeSeed, inner_euclid]
  ring

/-- The component of the head along the constraint is the head–constraint pairing. -/
theorem inner_secularHead_constraintNormal :
    inner ℝ (secularHead d ℓ μ) (constraintNormal ℓ)
      = secularVector d ℓ μ 0 * ℓ 0 + secularVector d ℓ μ 1 * ℓ 1 :=
  inner_euclid _ _ _ _

/-- The component of the head along the seed. -/
theorem inner_secularHead_twoModeSeed :
    inner ℝ (secularHead d ℓ μ) (twoModeSeed ℓ)
      = -(secularVector d ℓ μ 0 * ℓ 1) + secularVector d ℓ μ 1 * ℓ 0 := by
  rw [secularHead, twoModeSeed, inner_euclid]
  ring

/-! ## The Lagrange identity -/

/-- **The two components exhaust the length.**  In the head plane the squared components along the
constraint and along the seed sum to the product of the squared lengths. -/
theorem inner_sq_add_inner_sq_secularHead :
    inner ℝ (secularHead d ℓ μ) (constraintNormal ℓ) ^ 2
        + inner ℝ (secularHead d ℓ μ) (twoModeSeed ℓ) ^ 2
      = ‖secularHead d ℓ μ‖ ^ 2 * ‖constraintNormal ℓ‖ ^ 2 := by
  rw [inner_secularHead_constraintNormal, inner_secularHead_twoModeSeed, norm_sq_secularHead,
    norm_sq_constraintNormal]
  ring

/-- The head is nonzero as soon as its first coordinate is. -/
theorem secularHead_ne_zero (h : secularVector d ℓ μ 0 ≠ 0) : secularHead d ℓ μ ≠ 0 := by
  intro hz
  have hn : ‖secularHead d ℓ μ‖ ^ 2 = 0 := by rw [hz]; simp
  rw [norm_sq_secularHead] at hn
  have h1 := sq_nonneg (secularVector d ℓ μ 1)
  have h0 : secularVector d ℓ μ 0 ^ 2 = 0 := by nlinarith [sq_nonneg (secularVector d ℓ μ 0)]
  exact h ((pow_eq_zero_iff two_ne_zero).mp h0)

/-- The constraint direction is nonzero as soon as its first coordinate is. -/
theorem constraintNormal_ne_zero (h : ℓ 0 ≠ 0) : constraintNormal ℓ ≠ 0 := by
  intro hz
  have hn : ‖constraintNormal ℓ‖ ^ 2 = 0 := by rw [hz]; simp
  rw [norm_sq_constraintNormal] at hn
  have h1 := sq_nonneg (ℓ 1)
  have h0 : ℓ 0 ^ 2 = 0 := by nlinarith [sq_nonneg (ℓ 0)]
  exact h ((pow_eq_zero_iff two_ne_zero).mp h0)

theorem twoModeSeed_ne_zero (h : ℓ 0 ≠ 0) : twoModeSeed ℓ ≠ 0 := by
  intro hz
  have hn : ‖twoModeSeed ℓ‖ ^ 2 = 0 := by rw [hz]; simp
  rw [norm_sq_twoModeSeed] at hn
  have h1 := sq_nonneg (ℓ 1)
  have h0 : ℓ 0 ^ 2 = 0 := by nlinarith [sq_nonneg (ℓ 0)]
  exact h ((pow_eq_zero_iff two_ne_zero).mp h0)

/-! ## Alignment -/

/-- **A vanishing constraint component is a full seed component.**  The normalized squared
alignment of the head with the seed is one minus the normalized squared head–constraint defect. -/
theorem align_eq_one_sub_defect (hx : secularVector d ℓ μ 0 ≠ 0) (hn : ℓ 0 ≠ 0) :
    inner ℝ (secularHead d ℓ μ) (twoModeSeed ℓ) ^ 2
        / (‖secularHead d ℓ μ‖ ^ 2 * ‖twoModeSeed ℓ‖ ^ 2)
      = 1 - inner ℝ (secularHead d ℓ μ) (constraintNormal ℓ) ^ 2
          / (‖secularHead d ℓ μ‖ ^ 2 * ‖constraintNormal ℓ‖ ^ 2) := by
  have hxn : ‖secularHead d ℓ μ‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (secularHead_ne_zero d ℓ μ hx))
  have hnn : ‖constraintNormal ℓ‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (constraintNormal_ne_zero ℓ hn))
  have hseed : ‖twoModeSeed ℓ‖ ^ 2 = ‖constraintNormal ℓ‖ ^ 2 := by
    rw [norm_sq_twoModeSeed, norm_sq_constraintNormal]
  have hlag := inner_sq_add_inner_sq_secularHead d ℓ μ
  have hNM : ‖secularHead d ℓ μ‖ ^ 2 * ‖constraintNormal ℓ‖ ^ 2 ≠ 0 := mul_ne_zero hxn hnn
  rw [hseed, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hNM]
  linarith [hlag]

/-! ## The metric form of the ground-direction convergence -/

/-- The head–constraint defect in coordinates is the normalized squared component along the
constraint. -/
theorem defect_eq_inner_sq_div :
    (ℓ 0 * secularVector d ℓ μ 0 + ℓ 1 * secularVector d ℓ μ 1) ^ 2
        / ((secularVector d ℓ μ 0 ^ 2 + secularVector d ℓ μ 1 ^ 2) * (ℓ 0 ^ 2 + ℓ 1 ^ 2))
      = inner ℝ (secularHead d ℓ μ) (constraintNormal ℓ) ^ 2
          / (‖secularHead d ℓ μ‖ ^ 2 * ‖constraintNormal ℓ‖ ^ 2) := by
  rw [inner_secularHead_constraintNormal, norm_sq_secularHead, norm_sq_constraintNormal]
  ring_nf

/-- **The exact constrained ground direction converges to the two-mode seed direction, in the
sign-optimized metric sense.**  This is the metric form of the projective statement: once the
head–constraint defect collapses, the normalized head is close to `±` the normalized seed.

The defect hypothesis is exactly the conclusion of `secularVector_head_seed_defect_tendsto_zero`,
so that theorem discharges it verbatim. -/
theorem tendsto_min_norm_secularHead_normalize_sub_twoModeSeed
    {D L : ℝ → ℕ → ℝ} {M : ℝ → ℝ}
    (hv0 : ∀ᶠ lam in atTop, secularVector (D lam) (L lam) (M lam) 0 ≠ 0)
    (hL0 : ∀ᶠ lam in atTop, L lam 0 ≠ 0)
    (hdefect : Tendsto (fun lam =>
      (L lam 0 * secularVector (D lam) (L lam) (M lam) 0
          + L lam 1 * secularVector (D lam) (L lam) (M lam) 1) ^ 2
        / ((secularVector (D lam) (L lam) (M lam) 0 ^ 2
              + secularVector (D lam) (L lam) (M lam) 1 ^ 2)
            * (L lam 0 ^ 2 + L lam 1 ^ 2))) atTop (nhds 0)) :
    Tendsto (fun lam => min
        (‖(‖secularHead (D lam) (L lam) (M lam)‖)⁻¹ • secularHead (D lam) (L lam) (M lam)
          - (‖twoModeSeed (L lam)‖)⁻¹ • twoModeSeed (L lam)‖ ^ 2)
        (‖(‖secularHead (D lam) (L lam) (M lam)‖)⁻¹ • secularHead (D lam) (L lam) (M lam)
          + (‖twoModeSeed (L lam)‖)⁻¹ • twoModeSeed (L lam)‖ ^ 2))
      atTop (nhds 0) := by
  refine tendsto_min_norm_sub_sq_normalize_of_inner_sq
    (hv0.mono fun lam h => secularHead_ne_zero _ _ _ h)
    (hL0.mono fun lam h => twoModeSeed_ne_zero _ h) ?_
  have halign : Tendsto (fun lam =>
      1 - (L lam 0 * secularVector (D lam) (L lam) (M lam) 0
            + L lam 1 * secularVector (D lam) (L lam) (M lam) 1) ^ 2
          / ((secularVector (D lam) (L lam) (M lam) 0 ^ 2
                + secularVector (D lam) (L lam) (M lam) 1 ^ 2)
              * (L lam 0 ^ 2 + L lam 1 ^ 2))) atTop (nhds (1 - 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds hdefect
  rw [sub_zero] at halign
  refine halign.congr' ?_
  filter_upwards [hv0, hL0] with lam h0 h1
  rw [defect_eq_inner_sq_div]
  exact (align_eq_one_sub_defect (D lam) (L lam) (M lam) h0 h1).symm

end RHTower

end
