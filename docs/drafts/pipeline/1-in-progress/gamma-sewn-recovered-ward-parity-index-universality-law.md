# Gamma-sewn recovered Ward parity-index universality law

Status: **Stage 3 — formalized in Lean**

## Discovery

Whole-corpus posting closure joined:

- `GammaSewnSynchronizedRecoveryContraction`: synchronized squarefree recovery is strictly
  contractive at every positive aperture, converges to Möbius parity, is first-jet flat relative
  to that parity, and preserves the anti-causal Xi Ward tangent; and
- `XiWardInfinitesimalDefectIndexQuantization`: the Julia-defect derivative is twice the real Ward
  response and its Euler-edge mass is quantized in `8π` packets.

No recovered defect-index theorem occurs in either module.

## Universal law

For positive prime weights `nu`, finite squarefree support `P`, and strict-right Ward parameter
`w`, put

`A_P,w(a) = recoveredAmplitude(nu,a,P) · antiCausalWardTransport(w,a)`

and define its signed Julia defect by

`D_P,w(a) = 2 Re A_P,w(a) - |A_P,w(a)|²`.

Although recovery is strictly contractive for every positive aperture when `P` is nonempty,

`D_P,w(a) / a → (-1)^|P| · 2 Re r(w)` as `a → 0+`.

On the Euler edge this is `(-1)^|P|` times the canonical infinitesimal Ward-defect density.
Therefore Möbius parity can reverse the signed infinitesimal index but cannot change its absolute
total charge:

`∫⁻ |recovered density| = Σ_(right-upper Xi pairs) 8π`.

## Dependency-closed paper proof

1. `gammaSewnSynchronizedSignedRecovery_preserves_antiCausalWardTangent` gives
   `A(a)/a → (-1)^|P| r(w)`.
2. Since `a → 0` and the quotient has a finite limit,
   `A(a) = (A(a)/a)·a → 0` along `a>0`.
3. Thus
   `|A(a)|²/a = Re((A(a)/a)·conj(A(a))) → 0`.
4. Taking real parts in step 1 gives
   `2 Re(A(a))/a → 2 Re((-1)^|P|r(w))`.
5. The parity factor is real, so the latter is
   `(-1)^|P|·2 Re r(w)`. Subtract step 3.
6. At `w=1/2+it`, use the definition of `xiWardInfinitesimalDefectDensity`.
7. Its nonnegativity follows from
   `re_continuedXiAntiCausalWardResponse_nonneg`.
8. Since `|(-1)^|P||=1`, absolute recovered density equals the original density pointwise.
9. Apply `lintegral_xiWardInfinitesimalDefectDensity`.
10. Finite-aperture strict contraction is
    `norm_gammaSewnSynchronizedSignedRecoveryAmplitude_lt_one`.

No RH hypothesis, numerical evidence, or source-identification assumption enters.

## Formal targets

- `gammaSewnRecoveredWardSignedDefect`
- `gammaSewnRecoveredWardSignedDefect_slope_zero_right`
- `gammaSewnRecoveredWardInfinitesimalDensity`
- `lintegral_abs_gammaSewnRecoveredWardInfinitesimalDensity`
- `gammaSewn_recoveredWardParityIndexUniversality`

## Novelty audit

Post-proof searches covered the exact phrase combinations `Julia defect + 8π + Ward response +
Möbius parity`, `infinitesimal Julia defect + index quantization`, `Riemann xi + Schur +
Julia-Carathéodory + defect measure`, and `squarefree recovery + Xi Ward`.  Results separated into
standard generalized Schur/Julia defect theory, ordinary Möbius-function literature, and ordinary
Riemann-Xi zero literature; none stated the recovered squarefree-parity slope together with
absolute `8π` packet invariance.  Representative adjacent sources:

- [Generalized Schur–Nevanlinna functions and their realizations](https://link.springer.com/article/10.1007/s00020-020-02600-w)
- [Boundary angular derivatives of generalized Schur functions](https://resolve.cambridge.org/core/services/aop-cambridge-core/content/view/A643DD29628AE0169506E776E126162F/S1446788712000432a.pdf/boundary_angular_derivatives_of_generalized_schur_functions.pdf)
- [Zeros of Jensen polynomials and asymptotics for the Riemann xi function](https://arxiv.org/abs/2007.13582)
- [Quadratic Uniformity of the Möbius Function](https://arxiv.org/abs/math/0606087)

No exact collision found in this scoped audit. **[NOVELTY UNVERIFIED]**

## Lean formalization

Formal source:
`formal/GaloisForLFunctions/RHTower/GammaSewnRecoveredWardParityIndexUniversalityLaw.lean`.

Verified with:

`lake env lean GaloisForLFunctions/RHTower/GammaSewnRecoveredWardParityIndexUniversalityLaw.lean`

Umbrella:
`formal/GaloisForLFunctions/RHTower.lean`.
