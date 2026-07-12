# Xi Taylor theta-tail core density current

- **ID:** `xi-taylor-theta-tail-core-density-current`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / DIRECT SOURCE PRODUCER
- **Scientific status:** `[OPEN CORE] [NOVELTY UNVERIFIED]`
- **Parent target:** `xi-taylor-oriented-finite-coefficient-sublinear-flux.md`
- **Statement:** Prove directly from the explicit finite theta-tail integral and the canonical
  density `rho=4T''` that the finite core `U_d` has sublinear upper oriented current on every
  anisotropic rational-mesh fibre.

## Exact target

For a source-selected odd super-accurate schedule `D`, prove

```text
for every sigma with 0 < Re sigma < 1/2 and every epsilon > 0,
eventually in n,

J_(U_(D(k_n)))(z_n)
  < epsilon (n+1) |P_(2D(k_n)+3)(z_n)|^2,

k_n = xiCTaylorAnisotropicScheduleStage sigma n,
z_n = xiCTaylorAnisotropicCenteredPoint sigma n.
```

This is `XiCTaylorThetaTailCoreCurrentSublinearUpper D` in Lean.

## Firewall

The proof may use only the explicit finite theta-tail coefficients, the finite sections, and exact
identities of the canonical density.  It may not use Xi divisor data, real-rootedness,
Hermite--Biehler or anti-Herglotz positivity, complete limiting-measure selection, or an
RH-equivalent continued-Cauchy sequence sign.

## Exact source coordinate

Let

```text
rho(x) = 4 T''(x),
S_d(z,x) = sum_(k=0)^d (-1)^k z^(2k)x^(2k+2)/(2k+2)!,
H_d(z,x) = 1-(z^2+1/4)S_d(z,x).
```

Then `rho>0`, `integral rho=1`, and

```text
U_d(z)  = (1/2) integral rho(x) H_d(z,x) dx,
U_d'(z) = (1/2) integral rho(x) partial_z H_d(z,x) dx.       (1)
```

Consequently

```text
J_(U_d)(z)
 = (1/4) integral integral rho(x)rho(y) K_d(z;x,y) dx dy,    (2)

K_d(z;x,y)
 = (1/2) Im(
     partial_z H_d(z,x) conjugate(H_d(z,y))
     + partial_z H_d(z,y) conjugate(H_d(z,x))).
```

Equations `(1)` and `(2)` are proved on paper and in Lean.  They expose the exact correlation that
must cancel the positive-current atoms; positivity of `rho` alone cannot do so.

## Candidate cancellation

The shifted section satisfies the exact static relation

```text
partial_x^2 S_d(z,x) = C_d(z,x),
```

where `C_d` is the ordinary truncated cosine section.  Since `rho=4T''`, two integrations by parts
in either source variable replace `H_d` by `-(z^2+1/4)C_d` plus explicit seam terms.  The fully
integrated representation returns the already indefinite cosine two-point kernel.  The live
possibility is therefore the asymmetric or mixed representation obtained by integrating one
source variable at a time: its seam term and mixed `H_d/C_d` kernel must be tested together rather
than signed separately.

## Gates

- [x] positive normalized density coordinate formalized
- [x] finite section derivative formalized
- [x] derivative integral identity formalized
- [x] exact symmetric two-point current identity formalized
- [x] positive-current atom shortcut excluded
- [ ] derive the exact one-variable integration-by-parts correlation identity
- [ ] prove or refute a favorable sign/cancellation for the mixed kernel plus seam
- [ ] obtain the eventual scaled core-current inequality on every anisotropic fibre
- [ ] complete paper proof and Lean theorem
