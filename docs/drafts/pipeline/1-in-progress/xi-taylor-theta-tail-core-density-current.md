# Xi Taylor theta-tail core density current

- **ID:** `xi-taylor-theta-tail-core-density-current`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / DIRECT SOURCE PRODUCER
- **Scientific status:** `[OPEN CORE] [NOVELTY UNVERIFIED]`
- **Parent target:** `xi-taylor-oriented-finite-coefficient-sublinear-flux.md`
- **Statement:** Prove anisotropic sublinear upper current for the raw theta-tail/seam mixed
  correlation `(4)`.  The completed-source channel is an exact feedback copy of the next Xi
  Taylor section and supplies no independent positive term.

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

## Non-circularity boundary

No method class is excluded.  Any input must nevertheless prove a sign or cancellation for `(4)`
rather than restating the target Taylor current, assuming an RH-equivalent sign, or routing the
unknown Taylor section through an identity and calling the returned copy an error term.

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

where `Phi` is the even theta-cusp source.  The completed part is not an independent correction.
The exact finite transform and core identities are

```text
2 integral Phi(x) C_d(z,x) dx = P_(2d+1)(z),

z^2 [2 integral Phi(x) H_d(z,x) dx]
 = (z^2+1/4)P_(2(d+1)+1)(z) - (1/4)P_1(0).               (7)
```

Thus substitution of `(6)` feeds the next canonical Taylor section directly back into the current.
Any attempted positive bound on the `Phi` term is circular.  The only unresolved producer is the
raw `T` cross correlation together with the seam in `(4)`.

The completion boundary gives a genuine non-circular value relation:

```text
U_d(i/2)=1/2,
J_(U_d)(i/2)=-(1/2) A_d(1/4)<0,                           (8)
```

where `A_d=thetaCuspTailEvenPolynomial d` has strictly positive coefficients.  Equation `(8)` is
proved in Lean.  It localizes every possible positive-current obstruction to the open strip
`0<Im z<1/2`; it does not control the interior by itself.

For every polynomial `P`, Lean also proves the exact value-coordinate identity

```text
d/dy |P(x+iy)|^2 = -2 J_P(x+iy).                           (9)
```

Hence the narrowed target is equivalently a sublinear lower bound for the vertical derivative of
the finite core modulus on the anisotropic fibres.  The boundary value `(8)` gives the favorable
derivative at `y=1/2`; the open problem is to prevent an interior reversal of `(9)` at linear mesh
scale.  Such a reversal is exactly what a nearby nonreal zero produces.

## Literature/value-relation audit

- The classical theta-kernel formulas give positivity and modular balance of `Phi`, the Mellin
  representation of `xi`, the Fourier/cosine representation of `Xi`, and the raw even-moment
  formula.  These relations are present in Lean.
- Romik's orthogonal-polynomial expansions give positive coefficient sequences and compact-uniform
  convergence in the Hermite, Meixner--Pollaczek, and continuous-Hahn bases.  Their finite partial
  sums are not the monomial Taylor cores `U_d`; the Meixner--Pollaczek Poisson flow does not preserve
  hyperbolicity.  No transfer theorem in that work supplies the sign of `(4)`.
- Hedenmalm's theta-source boundary-value problem gives an eigenvalue characterization and a
  conditional self-adjointness program.  It supplies no finite Taylor-section identity beyond the
  theta/Mellin relations already used here, and the required inner-product sign remains an input.
- The 2025 backward-parabolic-barrier preprint claiming to propagate Pick positivity from a
  de Bruijn real-zero slice cannot supply the sign.  Its collision bridge requires a uniform
  differential inequality up to a collision.  The exact heat-flow polynomial
  `E_t(z)=z^2+1-2t` is a counterexample: `E_1` has two real zeros, `E_0` has zeros `+-i`, and the
  zero speed and separation constants blow up at the collision `t=1/2`.  Continuity of a tube
  energy at that time does not imply it remains zero on the earlier side.
- The Wigner--Eisenstein/Bessel coordinate has a positive real Mellin signature but an indefinite
  ordered-pair kernel.  Positivity on a real Mellin line is not a positive power-mixture
  representation, because Mellin inversion uses a complex vertical line.  Hence it does not orient
  the distinguished raw mixed correlation.

## Gates

- [x] positive normalized density coordinate formalized
- [x] finite section derivative formalized
- [x] derivative integral identity formalized
- [x] exact symmetric two-point current identity formalized
- [x] positive-current atom shortcut excluded
- [x] derive the exact one-variable integration-by-parts correlation identity
- [x] derive the completion-compensated finite cosine identity
- [x] expose the raw-tail plus completed-source density split
- [x] prove the completed-source feedback identity and remove that circular channel
- [x] prove the exact negative upper-completion-boundary current
- [x] identify the current with the vertical derivative of the finite squared modulus
- [x] audit classical theta, orthogonal-polynomial, spectral, and Wigner value relations
- [ ] prove a favorable interior sign/cancellation for the raw mixed kernel plus seam
- [ ] obtain the eventual scaled core-current inequality on every anisotropic fibre
- [ ] complete paper proof and Lean theorem
