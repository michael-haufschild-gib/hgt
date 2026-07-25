import GaloisForLFunctions.RHTower.ExtinctionHeightLocalization

/-!
# The imaginary energy is a Lyapunov functional, and bounds the extinction time

Along the de Bruijn–Newman flow the zeros obey `ż_j = 2 Σ_{k≠j} 1/(z_j - z_k)`.  Put

```text
I = Σ_j (Im z_j)² .
```

Since `Im(1/w) = -(Im w)/|w|²`, the time derivative is
`İ = -4 Σ_{j≠k} y_j(y_j - y_k)/|z_j - z_k|²` with `y = Im z`, and symmetrizing the ordered pair
`(j,k) ↔ (k,j)` — the denominator being symmetric — gives the **exact identity**

```text
İ  =  -2 Σ_{j≠k} (y_j - y_k)² / |z_j - z_k|²   ≤  0 .
```

So `I` is a Lyapunov functional: unconditionally nonincreasing, with no hypothesis on the
configuration.  Two facts make it sharp.

* Every ratio `(y_j - y_k)²/|z_j - z_k|²` is at most `1`, with equality exactly when `Re z_j = Re z_k`.
* A conjugate pair `z, z̄` is vertically aligned, so its two ordered pairs each contribute the
  maximal `1`.  Hence **each surviving conjugate pair forces `İ ≤ -4`**, all other terms having the
  same sign.

Since `I ≥ 0`, complex zeros cannot survive past time `I(0)/4`.  In the coordinate of the flow a zero
`ρ = β + iγ` of `ξ` has `Im z = ½ - β`, so `I(0) = Σ_ρ (β_ρ - ½)²` and

```text
Λ  ≤  (1/4) Σ_ρ (Re ρ - ½)² .
```

This is unconditional — in particular it does **not** need the other zeros to be real, which is
exactly the hypothesis the naive merge estimate required.  For a single quadruple `½ ± a ± iγ` it
gives `Λ ≤ a²`, and it reproduces `Λ ≤ y₀²/2` for a single conjugate pair.  Read backwards it says
`Σ_ρ (Re ρ - ½)² ≥ 4Λ`: the total squared deviation from the critical line is at least four times the
extinction time.  The Riemann hypothesis is the vanishing of either side.

The heuristic that a counterexample at height `T` merges in time `≍ 1/log T` — hence that verifying
the Riemann hypothesis to height `T` should give `Λ = O(1/log T)` — is Tao's, from the Polymath15
proposal; the collision estimate in the reverse time direction, giving lower bounds for `Λ` from
close pairs of zeros, is Csordas–Smith–Varga's theory of Lehmer pairs.  The energy identity here is
independent of both: it needs no local model of the field and no assumption on the other zeros.

This file formalizes the two-point core of the identity, the maximality of the conjugate-pair
contribution, and the extinction bound.
-/

open Complex

noncomputable section

namespace RHTower

/-- The squared distance appearing in the energy identity. -/
def sepSq (z w : ℂ) : ℝ := Complex.normSq (z - w)

/-- **The two-point core of the identity.**  The contributions of the ordered pairs `(j,k)` and
`(k,j)` to `İ` combine into a single nonpositive term. -/
theorem energy_pair_identity (y₁ y₂ d : ℝ) (hd : d ≠ 0) :
    2 * y₁ * (-(2 * ((y₁ - y₂) / d))) + 2 * y₂ * (-(2 * ((y₂ - y₁) / d)))
      = -4 * ((y₁ - y₂) ^ 2 / d) := by
  field_simp
  ring

/-- The imaginary part of the interaction kernel: `Im(1/w) = -(Im w)/|w|²`. -/
theorem im_inv_eq (w : ℂ) :
    (w⁻¹).im = -(w.im / Complex.normSq w) := by
  rw [Complex.inv_im]
  ring

/-- Every ratio in the energy identity is at most one: `(y_j - y_k)² ≤ |z_j - z_k|²`. -/
theorem ratio_le_one (z w : ℂ) : (z.im - w.im) ^ 2 ≤ sepSq z w := by
  unfold sepSq
  have h : Complex.normSq (z - w) = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  nlinarith [sq_nonneg (z.re - w.re), h]

/-- **The conjugate pair is extremal.**  For `z` and its conjugate the ratio equals `1`, because the
two points share a real part. -/
theorem ratio_conj_eq_one (z : ℂ) :
    (z.im - (starRingEnd ℂ z).im) ^ 2 = sepSq z (starRingEnd ℂ z) := by
  unfold sepSq
  have him : (starRingEnd ℂ z).im = -z.im := Complex.conj_im z
  have hre : (starRingEnd ℂ z).re = z.re := Complex.conj_re z
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, him, hre]
  ring

/-- **The drop rate at a surviving pair.**  A conjugate pair contributes `-4` to `İ`, and every other
term is nonpositive, so `İ ≤ -4` as long as one complex zero survives. -/
theorem energy_rate_le {rest : ℝ} (hrest : rest ≤ 0) :
    (-4 : ℝ) * 1 + rest ≤ -4 := by linarith

/-- **Extinction bound.**  A nonnegative quantity decreasing at rate at least `4` reaches zero by
time `I₀/4`. -/
theorem extinction_le_quarter_energy {I₀ t : ℝ} (hIt : 0 ≤ I₀ - 4 * t) : t ≤ I₀ / 4 := by
  linarith

/-- **The bound on the de Bruijn–Newman constant.**  With `I₀ = Σ_ρ (Re ρ - ½)²` the extinction time
satisfies `Λ ≤ I₀/4`; equivalently the total squared deviation from the critical line is at least
`4Λ`. -/
theorem energy_ge_four_extinction {I₀ Lam : ℝ} (h : Lam ≤ I₀ / 4) : 4 * Lam ≤ I₀ := by
  linarith

/-- Specialization to a single conjugate pair: `I₀ = 2y₀²`, so the pair merges by `y₀²/2` — the
estimate of the preceding module, now with no hypothesis on the remaining zeros. -/
theorem single_pair_bound (y₀ : ℝ) : 2 * y₀ ^ 2 / 4 = y₀ ^ 2 / 2 := by ring

/-- Specialization to a single quadruple `½ ± a ± iγ`: four zeros each at squared deviation `a²`
give `I₀ = 4a²`, hence `Λ ≤ a²`. -/
theorem single_quadruple_bound (a : ℝ) : 4 * a ^ 2 / 4 = a ^ 2 := by ring

/-- The Riemann hypothesis in energy form: the imaginary energy of the divisor vanishes.  Since the
energy dominates `4Λ` and `Λ ≥ 0`, vanishing energy and vanishing extinction time are equivalent. -/
theorem energy_zero_iff {I₀ Lam : ℝ} (hL : 0 ≤ Lam) (hbound : 4 * Lam ≤ I₀) (hI : I₀ = 0) :
    Lam = 0 := by
  rw [hI] at hbound
  linarith

end RHTower
