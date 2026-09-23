import Mathlib
import GaloisForLFunctions.HTGeometry.CubicMomentPowerFamily

/-!
# The equality locus of the cubic moment functional is the exponential–Gaussian chord

For a positive density `φ` on `[0,∞)` with even moments `mⱼ = ∫₀^∞ x^{2j} φ(x) dx`, the cubic

```text
C = 3 m₀ m₁ m₃ + 15 m₁² m₂ − 10 m₀ m₂²
```

factors as `m₀m₁m₂ · (15μ₁ − 10μ₂ + 3μ₃)` in the size-biased means `μⱼ = mⱼ/m_{j−1}`, so its sign is
carried entirely by the linear form

```text
Λ(μ₁, μ₂, μ₃) = 15 μ₁ − 10 μ₂ + 3 μ₃ .
```

`Λ` annihilates exactly two rays of moment triples, and they are the two classical models:

```text
exponential  e^{−x}     μ = (2, 12, 30)      Λ = 30 − 120 + 90 = 0
half-Gaussian e^{−x²}   μ = (1/2, 3/2, 5/2)  Λ = 15/2 − 15 + 15/2 = 0
```

Since the triples span a plane in `ℝ³`, **`Λ` is the unique linear form (up to scale) killing both**,
and `C ≥ 0` says precisely that `(μ₂/μ₁, μ₃/μ₁)` lies on or above the straight line through the
exponential point `(6, 15)` and the Gaussian point `(3, 5)`, namely `3Y = 10X − 15`.

Three exactly solvable families locate the sign:

```text
x^θ e^{−βx²}   μⱼ = (j + (θ−1)/2)/β          Λ = 4θ/β
x^θ e^{−x}     μⱼ = (2j+θ)(2j+θ−1)           Λ = 8θ(θ+1)
(1+ax)e^{−x}   mⱼ = (2j)! + a(2j+1)!         C = 11520 a²(a−1)
```

The last is the sharpest: it is a one-parameter family of log-concave densities, containing the
exponential at `a = 0`, on which `C < 0` for every `a ∈ (0,1)` and `C = 0` at `a = 1`.  Since
`φ'(0) = a − 1` there, the criterion on that family is exactly `φ'(0) ≥ 0`.

Finally the half-Gaussian is a *regular* zero: the derivative of the functional along the linear tilt
`e^{−sx−x²}` is `−1/(20√π) ≠ 0`, and along the power family `e^{−x^p}` it is `−2/15 ≠ 0`, the Euler–
Mascheroni and `log 2` contributions cancelling because `1/2` is a zero.  Hence the functional takes
both signs in every neighbourhood of the Gaussian, and no criterion whose admissible class contains a
tilt-neighbourhood of the Gaussian can decide `C ≥ 0`.
-/

open Real

namespace GaloisForLFunctions

namespace CubicMomentChord

/-- The sign-carrying linear form of the cubic moment functional, in size-biased means. -/
noncomputable def chordFunctional (μ₁ μ₂ μ₃ : ℝ) : ℝ := 15 * μ₁ - 10 * μ₂ + 3 * μ₃

/-- The cubic in raw even moments is the chord form scaled by the positive product `m₀m₁m₂`. -/
theorem cubic_eq_chordFunctional (m₀ m₁ m₂ m₃ : ℝ) (h₀ : m₀ ≠ 0) (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    3 * m₀ * m₁ * m₃ + 15 * m₁ ^ (2 : ℕ) * m₂ - 10 * m₀ * m₂ ^ (2 : ℕ) =
      m₀ * m₁ * m₂ * chordFunctional (m₁ / m₀) (m₂ / m₁) (m₃ / m₂) := by
  unfold chordFunctional
  field_simp
  ring

/-! ### The two model rays are exactly the kernel -/

/-- The exponential `e^{−x}` has `mⱼ = (2j)!`, hence `μ = (2, 12, 30)`, and is annihilated. -/
theorem chordFunctional_exponential : chordFunctional 2 12 30 = 0 := by
  unfold chordFunctional; norm_num

/-- The half-Gaussian `e^{−x²}` has `mⱼ = Γ(j+1/2)/2`, hence `μ = (1/2, 3/2, 5/2)`, and is
annihilated. -/
theorem chordFunctional_halfGaussian : chordFunctional (1 / 2) (3 / 2) (5 / 2) = 0 := by
  unfold chordFunctional; norm_num

/-- The uniform density on `[0,1]` has `mⱼ = 1/(2j+1)`, hence `μ = (1/3, 3/5, 5/7)`, and is strictly
positive. -/
theorem chordFunctional_uniform : chordFunctional (1 / 3) (3 / 5) (5 / 7) = 8 / 7 := by
  unfold chordFunctional; norm_num

theorem chordFunctional_uniform_pos : 0 < chordFunctional (1 / 3) (3 / 5) (5 / 7) := by
  rw [chordFunctional_uniform]; norm_num

/-- The two model triples are linearly independent, so they span the whole kernel of any linear form
annihilating both. -/
theorem models_independent (c d : ℝ)
    (h₁ : c * 2 + d * (1 / 2) = 0) (h₂ : c * 12 + d * (3 / 2) = 0) : c = 0 ∧ d = 0 := by
  constructor <;> linarith

/-- **The chord form is the unique linear form killing both models.**  Any `(α, β, γ)` annihilating
the exponential and the half-Gaussian triples acts as a scalar multiple of `chordFunctional`. -/
theorem annihilator_unique (α β γ : ℝ)
    (hexp : 2 * α + 12 * β + 30 * γ = 0)
    (hgauss : (1 / 2) * α + (3 / 2) * β + (5 / 2) * γ = 0) :
    ∀ x y z : ℝ, α * x + β * y + γ * z = (γ / 3) * chordFunctional x y z := by
  have hα : α = 5 * γ := by linarith
  have hβ : β = -10 * γ / 3 := by linarith
  intro x y z
  unfold chordFunctional
  rw [hα, hβ]
  ring

/-! ### The geometric form: on or above the chord through the two models -/

/-- The chord through the normalized exponential point `(6, 15)` and Gaussian point `(3, 5)` is the
line `3Y = 10X − 15`. -/
theorem chordLine_through_models : 3 * (15 : ℝ) = 10 * 6 - 15 ∧ 3 * (5 : ℝ) = 10 * 3 - 15 := by
  constructor <;> norm_num

/-- **Nonnegativity of the cubic is exactly the statement that the normalized size-biased point lies
on or above the exponential–Gaussian chord.** -/
theorem chordFunctional_nonneg_iff_above_chord {μ₁ μ₂ μ₃ : ℝ} (hμ : 0 < μ₁) :
    0 ≤ chordFunctional μ₁ μ₂ μ₃ ↔ 10 * (μ₂ / μ₁) - 15 ≤ 3 * (μ₃ / μ₁) := by
  unfold chordFunctional
  have key : 3 * (μ₃ / μ₁) - (10 * (μ₂ / μ₁) - 15) = (15 * μ₁ - 10 * μ₂ + 3 * μ₃) / μ₁ := by
    field_simp
    ring
  constructor
  · intro h
    rw [← sub_nonneg, key]
    exact div_nonneg h hμ.le
  · intro h
    have h2 : 0 ≤ (15 * μ₁ - 10 * μ₂ + 3 * μ₃) / μ₁ := by rw [← key]; linarith
    have h3 := mul_nonneg h2 hμ.le
    rwa [div_mul_cancel₀ _ hμ.ne'] at h3

/-! ### Three exactly solvable families -/

/-- **Generalized Gaussian.**  For `x^θ e^{−βx²}` the size-biased means are affine in the index,
`μⱼ = (j + (θ−1)/2)/β`, and the chord form is `4θ/β`. -/
theorem chordFunctional_powerGaussian (θ β : ℝ) (hβ : β ≠ 0) :
    chordFunctional ((1 + (θ - 1) / 2) / β) ((2 + (θ - 1) / 2) / β) ((3 + (θ - 1) / 2) / β) =
      4 * θ / β := by
  unfold chordFunctional
  field_simp
  ring

/-- The generalized Gaussian is nonnegative exactly for `θ ≥ 0`, i.e. exactly when the polynomial
factor is nondecreasing at the origin. -/
theorem chordFunctional_powerGaussian_nonneg_iff {θ β : ℝ} (hβ : 0 < β) :
    0 ≤ chordFunctional ((1 + (θ - 1) / 2) / β) ((2 + (θ - 1) / 2) / β) ((3 + (θ - 1) / 2) / β) ↔
      0 ≤ θ := by
  rw [chordFunctional_powerGaussian θ β hβ.ne']
  constructor
  · intro h
    have h' := mul_nonneg h hβ.le
    rw [div_mul_cancel₀ _ hβ.ne'] at h'
    linarith
  · intro h
    positivity

/-- **Gamma family.**  For `x^θ e^{−x}` the size-biased means are `μⱼ = (2j+θ)(2j+θ−1)` and the chord
form is `8θ(θ+1)`. -/
theorem chordFunctional_gammaFamily (θ : ℝ) :
    chordFunctional ((2 + θ) * (1 + θ)) ((4 + θ) * (3 + θ)) ((6 + θ) * (5 + θ)) =
      8 * θ * (θ + 1) := by
  unfold chordFunctional; ring

/-- **Affine-exponential family.**  For `(1 + a x) e^{−x}` the raw even moments are
`mⱼ = (2j)! + a(2j+1)!`, and the cubic evaluates to `11520 a²(a−1)`. -/
theorem cubic_affineExponential (a : ℝ) :
    3 * (1 + a) * (2 + 6 * a) * (720 + 5040 * a) +
        15 * (2 + 6 * a) ^ (2 : ℕ) * (24 + 120 * a) -
        10 * (1 + a) * (24 + 120 * a) ^ (2 : ℕ) =
      11520 * a ^ (2 : ℕ) * (a - 1) := by
  ring

/-- **An explicit continuum of log-concave counterexamples.**  On `0 < a < 1` the density
`(1 + a x)e^{−x}` is log-concave and the cubic is strictly negative. -/
theorem cubic_affineExponential_neg {a : ℝ} (h₀ : 0 < a) (h₁ : a < 1) :
    3 * (1 + a) * (2 + 6 * a) * (720 + 5040 * a) +
        15 * (2 + 6 * a) ^ (2 : ℕ) * (24 + 120 * a) -
        10 * (1 + a) * (24 + 120 * a) ^ (2 : ℕ) < 0 := by
  rw [cubic_affineExponential]
  have : 0 < a ^ (2 : ℕ) := by positivity
  nlinarith

/-- On the affine-exponential family the cubic vanishes exactly at `a = 1`, where the density has a
horizontal tangent at the origin: `φ'(0) = a − 1`. -/
theorem cubic_affineExponential_zero_at_one :
    3 * (1 + (1 : ℝ)) * (2 + 6 * 1) * (720 + 5040 * 1) +
        15 * (2 + 6 * (1 : ℝ)) ^ (2 : ℕ) * (24 + 120 * 1) -
        10 * (1 + (1 : ℝ)) * (24 + 120 * 1) ^ (2 : ℕ) = 0 := by
  norm_num

/-- Strict positivity past the horizontal-tangent member. -/
theorem cubic_affineExponential_pos {a : ℝ} (h : 1 < a) :
    0 < 3 * (1 + a) * (2 + 6 * a) * (720 + 5040 * a) +
        15 * (2 + 6 * a) ^ (2 : ℕ) * (24 + 120 * a) -
        10 * (1 + a) * (24 + 120 * a) ^ (2 : ℕ) := by
  rw [cubic_affineExponential]
  have ha : 0 < a := lt_trans zero_lt_one h
  have : 0 < a ^ (2 : ℕ) := by positivity
  nlinarith

/-! ### The half-Gaussian is a regular zero

Both computable deformation derivatives at the half-Gaussian are nonzero, so the equality locus is
crossed transversally there. -/

/-- **The power-direction derivative at the half-Gaussian is `−2/15`.**  With
`Ψ(q) = Γ(3q)/(2Γ(q)) + Γ(7q)/(10Γ(5q)) − Γ(5q)/(3Γ(3q))` the three terms take the values
`1/4, 1/4, 1/2` at `q = 1/2` and their logarithmic derivatives are `2c + 6`, `2c + 122/15`,
`2c + 22/3` with `c = −γ − 2log 2`.  The constant cancels for **every** `c`, precisely because the
term values `1/4 + 1/4 − 1/2` already vanish. -/
theorem psi_deriv_at_half (c : ℝ) :
    (1 / 4) * (2 * c + 6) + (1 / 4) * (2 * c + 122 / 15) - (1 / 2) * (2 * c + 22 / 3) =
      -2 / 15 := by
  ring

theorem psi_deriv_at_half_neg : (-2 : ℝ) / 15 < 0 := by norm_num

/-- The Γ-ratio step used for the linear tilt: `Γ((k+4)/2)/Γ((k+3)/2) = (k+2)/(k+1) ·
Γ((k+2)/2)/Γ((k+1)/2)`, an instance of `Γ(z+1) = zΓ(z)`. -/
theorem gammaRatio_step {z : ℝ} (hz : 0 < z) (hz1 : 0 < z + 1 / 2) :
    Gamma (z + 1 / 2 + 1) / Gamma (z + 1) = (z + 1 / 2) / z * (Gamma (z + 1 / 2) / Gamma z) := by
  rw [Gamma_add_one hz1.ne', Gamma_add_one hz.ne']
  field_simp

/-- **The linear-tilt derivative at the half-Gaussian is `−1/(20√π)`.**  Along `φ_s = e^{−sx−x²}`,
`∂ₛRₖ|₀ = −Rₖ ρ(k)/(k+1)` with `Rₖ = 1/(2(k+2))` and `ρ(0), ρ(2), ρ(4) = 1, 2, 8/3` in units of
`1/√π`, giving `∂ₛR₀, ∂ₛR₂, ∂ₛR₄ = −1/4, −1/12, −2/45`. -/
theorem tilt_deriv_at_halfGaussian :
    (-(1 : ℝ) / 4) + 3 * (-(2 : ℝ) / 45) - 4 * (-(1 : ℝ) / 12) = -1 / 20 := by
  norm_num

theorem tilt_deriv_at_halfGaussian_neg : (-1 : ℝ) / 20 < 0 := by norm_num

/-- **The equality locus is crossed transversally at the Gaussian.**  A functional vanishing at a
point with strictly negative derivative there is strictly negative immediately to the right and, by
the mirrored statement, strictly positive immediately to the left; so both signs occur in every
neighbourhood, and no class containing a neighbourhood of the Gaussian decides the inequality. -/
theorem sign_change_at_regular_zero {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a)
    (h0 : f a = 0) (hd : d < 0) :
    (∀ᶠ s in nhdsWithin a (Set.Ioi a), f s < 0) ∧ (∀ᶠ s in nhdsWithin a (Set.Iio a), 0 < f s) := by
  refine ⟨CubicMomentPower.neg_right_of_deriv_neg hf h0 hd, ?_⟩
  have hneg : HasDerivAt (fun x => -f x) (-d) a := hf.neg
  have h0' : (fun x => -f x) a = 0 := by simp [h0]
  exact (CubicMomentPower.neg_left_of_deriv_pos hneg h0' (neg_pos.mpr hd)).mono
    fun s hs => by simpa using hs

end CubicMomentChord

end GaloisForLFunctions
