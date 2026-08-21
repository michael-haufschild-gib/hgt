# Suzuki v2: formalization of the unlabeled propositions

**Status:** in progress — Section 8.2 (the inverse Neumann Laplacian) closed in Lean; remaining
sections under audit
**Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
arXiv:2606.09096v2, 17 August 2026 (source file `screwzelf_9.tex`, 3823 lines).

## Scope

The eleven *labeled* v2 results (5 theorems, 2 corollaries, 3 lemmas, 1 proposition) already have
exact Lean landings; see `suzuki-v2-literature-parity-and-cofinal-correction.md`.  This card covers
the **unlabeled but fully provable propositions**: the displayed identities of Sections 2, 3, 4, 5,
7 and 8 that the paper states and proves but does not number as theorems.

## Audit of the unlabeled content

### Section 2 (Preliminaries)

| Item | Corpus status |
|---|---|
| `P_a` is the genuine orthogonal projection onto `L²₀(-a,a)` | owned: `suzukiApertureZeroMeanProjection` |
| Origin expansion (2.2) of the screw function `g` | owned: `SuzukiOriginLogarithmicRemainder`, `suzukiApertureScrewExpansion` |
| (2.4) singular logarithmic integration by parts | owned: `suzuki_equation_two_four` |
| (2.5) arithmetic four-block form of `Q_{B_a}` | owned: `suzuki_equation_two_five` |
| (2.6) `L_a(v) = (2π)^{-1}∫(log|z| + C₀)|v̂|²` | owned: `suzukiFinitePartEnergy_eq_logFourier_add_eulerMass` |
| (2.9)–(2.11) distributional `-g''` kernel identities | owned: `SuzukiScrewDistributionalAtoms`, `SuzukiScrewOperatorEquationTwoFive` |

### Section 8 (from distribution kernels to continuous kernels)

| Item | Status |
|---|---|
| §8.1 `Q_{G̃}(u) = Q_G(u)` on `L²₀` (all centering ranks vanish) | owned: `suzukiScrewIntervalForm_eq_raw_of_zeroMean` |
| §8.2 inverse Neumann Laplacian, kernel `N(x,y)`, identity (8.2) | **closed here** |
| §8.4 Bombieri Problem 1 = eigenvalue problem for `G_a` on `L²₀` | reduces to §8.1 + the `H¹`-norm identification `‖v‖_{H¹} = ‖Dv‖_{L²}` |
| §8.5 (8.4) generalized eigenvalue problem `G_a u = λ K_a u` | **closed here** (`suzuki_equation_804`) |

## Section 8.2 closed: the inverse Neumann Laplacian

Two new Lean modules.

### `GaloisForLFunctions/HTGeometry/TriangularIntervalFubini.lean`

Reusable exchange lemma with no continuity, boundedness or compact-support hypothesis:

`∫_p^q F(x) (∫_x^q G) dx = ∫_p^q (∫_p^t F) G(t) dt`   (`intervalIntegral_triangle_swap`)

Both sides are the integral of `F(x)G(t)` over the triangle `p < x < t ≤ q`; the proof runs through
the corpus's product-majorant Fubini theorem `integral_swap_of_dominated_prod`.

### `GaloisForLFunctions/RHTower/SuzukiInverseNeumannLaplacian.lean`

Kernels:

* `suzukiPrefixGramKernel a x y = a - max x y`;
* `suzukiNeumannGreenKernel a x y = (x² + y²)/(4a) - |x - y|/2 + a/6`.

Mechanism.  The two kernels differ by the **separable** expression `φ(x) + φ(y)` with
`φ(t) = t²/(4a) + t/2 - 5a/12` (`suzukiNeumannGreenKernel_sub_prefixGramKernel`, needing no
hypothesis on `a` at all).  A separable perturbation contributes `φ(x)·∫u + (∫φu)·∫ū` to the
quadratic form, so it is invisible on mean-zero data.  On the prefix Gram side, one triangular
exchange gives

`∫_{-a}^a (a - max(x,y)) u(y) dy = ∫_x^a v(t) dt`,  `v(x) = ∫_{-a}^x u`,

and a second exchange turns the resulting form into `∫ |v|²`.

Closed statements:

* `suzuki_equation_802` — `‖v‖²_{L²} = ⟨N u, u⟩` for mean-zero `u`;
* `suzuki_neumannGreen_form_eq_ofReal`, `suzuki_neumannGreen_form_nonneg` — the form is the real
  nonnegative `L²` mass, i.e. `(-Δ_N)^{-1}` is positive;
* `intervalIntegral_suzukiNeumannGreenKernel_right` — `∫_{-a}^a N(x,y) dy = 0`; the constant `a/6`
  is exactly what forces this;
* `intervalIntegral_suzukiNeumannGreenOperator_eq_zero` — the operator maps `L²₀` into `L²₀`,
  proved by two further triangular exchanges instead of a plane Fubini;
* `hasDerivAt_suzukiNeumannGreenOperator` — `(K_a u)'(x) = -v(x)` at interior points;
* `hasDerivAt_deriv_suzukiNeumannGreenOperator` — `(K_a u)'' = -u` wherever `u` is continuous;
* `tendsto_deriv_suzukiNeumannGreenOperator_left`/`_right` — the Neumann boundary condition
  `(K_a u)'(±a) = 0`, obtained from `v(-a) = 0` and `v(a) = ∫u = 0`;
* `suzukiPrefixPrimitive_hasDerivAt_and_vanishes`, `intervalIntegral_eq_zero_of_dirichlet` — the two
  halves of the bijectivity of `D : H_0^1(-a,a) → L²₀(-a,a)`;
* `suzuki_equation_804` — the generalized-eigenvalue Rayleigh quotient.

Hypotheses are only `0 < a`, interval integrability of `u` (implied by `u ∈ L²(-a,a)` on a bounded
interval) and, where the source requires it, `∫_{-a}^a u = 0` (i.e. `u ∈ L²₀`).  No positivity, no
regularity beyond integrability, no Riemann-hypothesis input.

## Verification

Both modules pass `lake env lean`; targeted `.olean` builds pass; `#print axioms` on every capstone
reports only `propext`, `Classical.choice`, `Quot.sound`.  Both are wired into their theorem-area
umbrellas (`HTGeometry.lean`, `RHTower.lean`).

## Remaining audit

Sections 3, 4, 5 and 7 still need an item-by-item comparison of their displayed identities against
the corpus.  Known candidates not yet checked: the Fourier-side form (2.7)–(2.8), the cut-off
estimates (3.3)–(3.4) inside the proof of Theorem 1.1, the scaling identities (4.1)–(4.6), the
parity decomposition (4.10), the small-aperture expansion (5.1), and the de Branges computations of
Section 7 (reproducing-kernel deficiency vectors, `K(∓i,∓i) = ξ(3/2)ξ'(3/2)/π`, the boundary-form
evaluation with `C_θ`, and the `θ = π` specialization).
