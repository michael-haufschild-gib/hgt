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

The exact one-variable identity, now proved in Lean, is

```text
integral rho(x) H_d(z,x) dx
 = 1 - 4(z^2+1/4) integral T(y) C_d(z,y)dy,                (3)

J_(U_d)(z)
 = (1/4) integral Im(rho(x) partial_z H_d(z,x))dx
   - integral integral rho(x)T(y)
       Im(partial_z H_d(z,x)
          conjugate((z^2+1/4)C_d(z,y)))dxdy.              (4)
```

The seam term in `(4)` is not disposable: the mixed term is a cross energy, not a square, and the
already proved Wigner--Eisenstein analysis shows that the corresponding ambient pair form is
indefinite.  Thus `(4)` is an exact coordinate but not yet a producer.

There is a second finite value relation, also proved in Lean,

```text
z^2 S_d(z,x) = 1-C_(d+1)(z,x),
z^2 H_d(z,x) = (z^2+1/4)C_(d+1)(z,x)-1/4.                (5)
```

Equation `(5)` exposes the completion boundary `|Im z|=1/2` without division at `z=0`.  The live
residue is a completion-compensated cosine correlation.  A proof must orient this distinguished
canonical average; positivity of every cosine atom or of the ambient coefficient form is neither
true nor required.

The canonical density has the further exact completed-source split

```text
rho(x)=T(x)+4 Phi(x),
Phi(x)=T''(x)-(1/4)T(x),                                  (6)
```

where `Phi` is the even theta-cusp source.  Unlike `rho=4T''` alone, `(6)` retains the modular
completion.  Substitution into `(4)` separates a universal raw-tail cross term from the completed
theta correlation.  The latter is the only live place for a canonical orientation law; the
Wigner--Eisenstein calculation shows it cannot be replaced by positivity of the ambient pair
kernel.

## Gates

- [x] positive normalized density coordinate formalized
- [x] finite section derivative formalized
- [x] derivative integral identity formalized
- [x] exact symmetric two-point current identity formalized
- [x] positive-current atom shortcut excluded
- [x] derive the exact one-variable integration-by-parts correlation identity
- [x] derive the completion-compensated finite cosine identity
- [x] expose the raw-tail plus completed-source density split
- [ ] prove or refute a favorable sign/cancellation for the mixed kernel plus seam
- [ ] obtain the eventual scaled core-current inequality on every anisotropic fibre
- [ ] complete paper proof and Lean theorem
