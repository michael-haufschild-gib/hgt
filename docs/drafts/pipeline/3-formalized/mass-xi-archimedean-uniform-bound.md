# Mass--Xi archimedean contour shift and uniform vertical bound

- **ID:** `mass-xi-archimedean-uniform-bound`
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE SURVIVOR
- **Date:** 2026-08-04
- **Parent:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`

## Exact statement

Fix `a>1/2`, `1/2<c<a`, and `sigma>0`.  Put

```text
g_tau(z) = exp(-tau sqrt(z^2+a^2)),
s(z)     = 1/2+i z,
p        = -i/2.
```

Then for every `tau=sigma+i u`,

```text
integral_R g_tau(x-i c) logDeriv(archFactor)(1/2+c+i x) dx
 = integral_R g_tau(x) logDeriv(archFactor)(1/2+i x) dx
   + 2 pi g_tau(-i/2).                                    (1)
```

Consequently the left side is uniformly bounded for `u in R`.  An explicit admissible bound is

```text
integral_R exp(-sigma sqrt(x^2+a^2))
  norm(logDeriv(archFactor)(1/2+i x)) dx
+ 2 pi exp(-sigma sqrt(a^2-1/4)).                          (2)
```

## Proof

The mass test is holomorphic on `|Im z|<a`.  On the closed strip `-c<=Im z<=0`, write

```text
archFactor(s(z)) = (z-p) H(z),
H(z) = (i/2) s(z) Gamma_R(s(z)).                           (3)
```

Here `Re s(z)>=1/2`, so `s(z)` and `Gamma_R(s(z))` are nonzero and analytic.  Thus `H` is analytic
and nonzero throughout a neighbourhood of every closed rectangle in this strip.  The local
weighted argument principle applied to `g_tau` and `(3)` gives

```text
rectIntegral [g_tau(z) logDeriv_z(archFactor o s)(z)]
 = 2 pi i g_tau(p).                                       (4)
```

The chain rule gives

```text
logDeriv_z(archFactor o s)(z)
 = i logDeriv_s(archFactor)(s(z)).                         (5)
```

For `z=+/-R+i y`, `-c<=y<=0`, the mass-strip estimate is

```text
norm(g_tau(z)) <= exp(|u|c) exp(-sigma R).                 (6)
```

The closed archimedean formula

```text
logDeriv archFactor(s)
 = 1/s + 1/(s-1) - (log pi)/2 + digamma(s/2)/2             (7)
```

and the uniform right-half-plane digamma estimate imply, for all sufficiently large `R`,

```text
norm(logDeriv archFactor(s(+/-R+i y))) <= C_c + R/2        (8)
```

uniformly in `y`.  Indeed `Re s` stays in `[1/2,1/2+c]`, the two rational terms are bounded using
`|Im s|=R`, and conjugation reduces negative height to the positive-height digamma estimate.
Equations `(6)`--`(8)` make both vertical edges tend to zero because every fixed polynomial is
absorbed by `exp(-sigma R)`.  Expanding `(4)`, using `(5)`, and taking `R->infinity` proves `(1)`.

On the real centered line, the principal mass root is the positive real number
`sqrt(x^2+a^2)`.  Hence

```text
norm(g_(sigma+i u)(x)) = exp(-sigma sqrt(x^2+a^2)),
norm(g_(sigma+i u)(p)) = exp(-sigma sqrt(a^2-1/4)),        (9)
```

independently of `u`.  The real-line integrand in `(2)` is integrable: the mass factor decays
exponentially and `(7)` has at most logarithmic growth.  Triangle inequality in `(1)` proves the
uniform bound.

## Hostile audit

- The shift crosses `s=1`, but its residue is retained exactly; dropping it would be false.
- The crossed mass frequency is real because `a>1/2`; no RH input occurs.
- No Xi zero is crossed: this is the archimedean factor alone.
- Absolute values are used only after landing on the centered real line, where complex time is
  unitary in the mass phase.
- This does not bound the prime term.  It proves that all RH-strength vertical growth in the exact
  mass source identity is carried by the von-Mangoldt channel.

## Novelty and corpus audit

The corpus contains the rectangular Gamma--polar cancellation law and general strip contour-shift
machinery, but no mass-carrier theorem `(1)` or uniform complex-time archimedean bound.  Standard
ingredients are the Gamma logarithmic derivative, digamma vertical growth, and residue theorem.
Novelty claim is limited to their exact mass--Xi assembly.

## Gates

- [x] exact statement frozen
- [x] dependency-closed paper proof
- [x] hostile pole/circularity audit
- [x] Lean formalization: `XiMassArchimedeanUniformBound.lean`
- [x] targeted build and axiom audit

## Lean certificate

The formal module proves, without hypotheses beyond `a>1/2`, `1/2<c<a`, and `sigma>0`:

- the local factorization at the crossed zero and finite residue law;
- a uniform vertical-strip digamma/logarithmic-derivative estimate;
- vanishing of both vertical edges;
- centered-line and bottom-line absolute integrability;
- exact real mass frequencies on the centered line and at `p=-i/2`;
- `integral_xiMassBottomArch_eq_centered_add_residue`;
- `norm_integral_xiMassBottomArchIntegrand_le_uniform`.

The stronger formal observation is exact modulus invariance on the centered line:
`norm_xiMassCenteredArchIntegrand_verticalTime_eq`.

Final verification:

- `lake build GaloisForLFunctions.RHTower.XiMassPrimeGradedOpenCore` succeeded, rebuilding this
  module in the dependency chain;
- `#print axioms` for the exact shift and uniform-bound capstones reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
