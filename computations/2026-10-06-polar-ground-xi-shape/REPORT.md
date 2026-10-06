# Shape of the restricted-Weil ground states against Ξ

**What was computed.** Even ground states of the restricted Weil form on `L²(−a, a)`, for
a = 0.5, 0.6, 0.7, 0.8. The form uses the same conventions and code as
`computations/weil-polar-ground-energy` (Legendre Galerkin, mpmath 50 digits, N = 40 and 48). The
quadrature is exact up to N = 48; N = 52 gave garbage and was discarded.

Two ground states per aperture:
- `G`: the ground state on the pole-vanishing subspace (the corpus's polar ground state, MUST-794);
- `H`: the ground state of the unconstrained form (Connes's minuscule eigenvector).

Diagnostics:
- the transforms `F(z) = ∫f(x)e^{−izx}dx`, written as `F/F(0) = 1 + Az² + Bz⁴ + …`;
- the log-Taylor coefficient `c₄ = B − A²/2`;
- the ratios `G/((1+4z²)G(0))` and `H/H(0)` against `Ξ/Ξ(0)` on `[0, 20]` and on `i[0, 0.48]`;
- the sign changes of `F(iy)` for `y ∈ (0, 3]`.

Script: `shape.py`. Data: `shape48.out` / `shape48.json`. N = 40 and N = 48 agree to 3–4 digits.

**Outcome.**

| a | polar `c₄ + 8` | full `c₄` | `δ_G·e^{2a}` | `δ_H·e^{2a}` |
|---|---|---|---|---|
| 0.5 | −1.631e-5 | −1.756e-5 | 0.0254 | 0.0226 |
| 0.6 | −1.785e-5 | −1.811e-5 | 0.0237 | 0.0219 |
| 0.7 | −1.828e-5 | −1.835e-5 | 0.0227 | 0.0216 |
| 0.8 | −1.844e-5 | −1.847e-5 | 0.0221 | 0.0212 |

Here `δ_G = (A_G − 4) − A_Ξ` and `δ_H = A_H − A_Ξ`, with `A_Ξ = −Σ_{γ>0} γ⁻² = −0.023105`. Ξ's own
`c₄ = −½Σγ⁻⁴ ≈ −1.85e-5`.

- The polar ground state is `(1 + 4z²) × (Ξ-shaped)`: `c₄(G) = −8 + c₄(Ξ)`. The −8 is exactly the
  polar pair `±i/2`, since `log(1+4z²) = 4z² − 8z⁴ + …`.
- `G` has no imaginary zero in `i(0, 3]` other than `±i/2`. `H` has none at all.
- Both `G/((1+4z²)G(0))` and `H/H(0)` approach `Ξ/Ξ(0)`. The z²-coefficient deficit decays like
  `e^{−2a}`, with prefactor near `1/(4π²) = 0.0253`. That is the predicted excess
  `Σ_{γ>T*}γ⁻² − Σ_{x>T*}x⁻² ≈ 1/(2πT*)` from zeros above the Nyquist height `T* = 2πe^{2a}`,
  where the ground state has zero density `a/π` instead of `log(t/2π)/2π`.

**Interpretation.**
- The polar ground transforms cannot converge to Ξ itself. This is a theorem (MUST-796,
  `CrossRootedPolarZeroXiStripObstruction`): cross-rooted zeros contribute `+z⁻⁴`, and the polar
  pair alone gives `Σz⁻⁴ ≥ 16`. So MUST-795's even-ground receiver was vacuous.
- The corrected target, `G/(z² + ¼) → cΞ` (`riemannHypothesis_of_evenGround_polarQuotient_strip_convergence`),
  is what the data show, at rate `~e^{−2a}` in the z² coefficient.
- Connes's eigenvector `H` needs no division.
- Converged Galerkin data exist only for a ≤ 0.8. Larger apertures need dps ≈ 4.3·a·e^{2a} and
  N ≈ 2πa·e^{2a} + 40.
- Earlier "excess real zeros at low height" lists for a ≥ 1.1
  (`weil-polar-ground-energy/spectral_zeros.json`, used by loop rows 490–491) come from
  unconverged Galerkin runs and are not evidence about the true ground states.
