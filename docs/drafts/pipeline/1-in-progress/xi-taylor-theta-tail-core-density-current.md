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
 = (z^2+1/4)P_(2(d+1)+1)(z) - (1/4)P_1(0),

z^4 [2 integral Phi(x) partial_z H_d(z,x) dx]
 =z^2(z^2+1/4)P'_(2(d+1)+1)(z)
   +(z/2)(P_1(0)-P_(2(d+1)+1)(z)).                       (7)
```

Thus substitution of `(6)` feeds the next canonical Taylor section directly back into the current.
Any attempted positive bound on the `Phi` term is circular.  The only unresolved producer is the
raw `T` cross correlation together with the seam in `(4)`.

The central completion seam point gives a genuine non-circular value relation:

```text
U_d(i/2)=1/2,
J_(U_d)(i/2)=-(1/2) A_d(1/4)<0,                           (8)
```

where `A_d=thetaCuspTailEvenPolynomial d` has strictly positive coefficients.  Equation `(8)` is
proved in Lean.  It signs only the single point `z=i/2`: on the rest of the horizontal line
`Im z=1/2`, the factor `z^2+1/4` does not vanish.  Thus `(8)` supplies no boundary-line control and
does not localize the positive-current obstruction by itself.

For every polynomial `P`, Lean also proves the exact value-coordinate identity

```text
d/dy |P(x+iy)|^2 = -2 J_P(x+iy).                           (9)
```

The whole real boundary, unlike the isolated point `(8)`, has an exact value relation.  Since
`U_d` has real coefficients,

```text
J_(U_d)(x)=0,

J_(U_d)(x+iy)
 = integral_(0..y) [Re(U_d'' conjugate(U_d))-|U_d'|^2](x+it)dt.  (10)
```

Equation `(10)` is proved in Lean.  It is the genuine boundary-to-interior formula on every
anisotropic fibre.  In the density coordinate its integrand is

```text
Re(U_d'' conjugate(U_d))-|U_d'|^2
 = (1/4) integral integral rho(a)rho(b) L_d(z;a,b) da db,

L_d(z;a,b)
 = (1/2) Re(
     partial_z^2 H_d(z,a) conjugate(H_d(z,b))
     + partial_z^2 H_d(z,b) conjugate(H_d(z,a))
     - 2 partial_z H_d(z,a) conjugate(partial_z H_d(z,b))). (11)
```

Thus the narrowed target is an integrated upper bound for the canonical complex Laguerre defect
`(11)`, not pointwise positivity of `rho`.  In the raw-tail coordinate

```text
w=-z^2,
B_d(w)=1/2+(w-1/4)A_d(w),
U_d(z)=B_d(-z^2),

Re(U_d'' conjugate(U_d))-|U_d'|^2
 = -2 Re(B_d' conjugate(B_d))
   -4 Re(w B_d'' conjugate(B_d))
   -4 |z|^2 |B_d'|^2.                                   (12)
```

The last term in `(12)` is favorable.  The open producer is a cancellation estimate for the first
two raw moment terms after integrating over `0<=t<=Im z`; imposing their pointwise sign would be a
complex Laguerre/anti-Herglotz condition and would simply repackage the target.

## Critical-Laguerre scale coordinate

The mechanism of Haufschild's critical-Laguerre moment deformation yields one exact new coordinate.
Let

```text
L_d(u)=sum_(k=0)^d (-1)^k d^(falling k) u^(2k)/(d^k(2k)!),
G_d ~ Gamma(shape=d+1, rate=d).
```

Then, for `0<=k<=d`,

```text
E[G_d^(-k)]=d^k/d^(falling k),
```

and hence the ordinary truncated cosine has the exact positive scale average

```text
C_d(z,x)=E[L_d(zx/sqrt(G_d))].                            (13)
```

Thus the raw theta transform in `(3)` is a double positive average of rescaled critical-Laguerre
polynomials.  Equation `(13)` is proved on paper by a finite coefficient comparison.  It is not yet
a sign theorem: the inverse-gamma scale law is continuous, unbounded, and has no identity atom,
whereas Haufschild's sign-transfer theorem uses an atom of mass `p>1/2` at scale one.  Indeed generic
positive scale averaging has exactly the cross-current obstruction already exposed in `(4)`.
The loss is already exact at degree three: writing the ordinary section as

```text
Q_3(s)=1-s/2+s^2/24-s^3/720,  s=z^2,
Q_3'(s)=-(s^2-20s+120)/240<0  for every real s,
```

shows that `Q_3` has only one real root and hence its even lift has four nonreal zeros, despite
being the positive inverse-gamma average `(13)` of hyperbolic critical-Laguerre copies.

The live question suggested by `(13)` is narrower: combine the horizontal Laguerre energy identity

```text
partial_x (|L_d|^2+|L_d'|^2)=(x/d)|L_d'|^2
```

with the *specific product scale* `x/sqrt(G_d)` and the raw theta weight `T(x)` to bound the two
cross terms in `(12)`.  A proof must control the averaged cross current; hyperbolicity of each
Laguerre copy separately is insufficient.

The identity-atom part of the Theorem-M mechanism is in fact unavailable for *any* critical-
Laguerre representation of the raw moment section.  Normalize the raw moments to `mu_0=1`, write
`r_k=mu_(k+1)/mu_k`, and note that positivity of the tail measure makes `r_k` nondecreasing.  If

```text
sum_(k=0)^d (-1)^k mu_k z^(2k)/(2k)!
  = integral_[0,1] L_d(lambda v z) dnu(v),
```

then coefficient comparison gives

```text
M_k := integral v^(2k)dnu(v)
     = mu_k d^k/(lambda^(2k) d^(falling k)).              (14)
```

If `nu` has an identity atom of mass `p`, then `p<=M_d`.  Since `[0,1]` moments decrease,
`M_d<=M_(d-1)`, so the last ratio in `(14)` gives `d r_(d-1)/lambda^2<=1`.  For every `k<d`,

```text
M_(k+1)/M_k
 = d r_k/(lambda^2(d-k)) <= 1/(d-k).
```

Multiplication yields

```text
p <= M_d <= 1/d!.                                       (15)
```

Thus for every `d>=2` an identity atom of mass `p>1/2` is impossible, even if one allows an
alternative truncated Hausdorff representing measure instead of the natural inverse-gamma law.
Equations `(14)`--`(15)` are proved on paper.  Theorem M therefore supplies the Laguerre coordinate
and energy identity, but its coercive sign-copy step is rigorously retired for the raw theta
moments.  Any surviving use of `(13)` must estimate the averaged cross current directly.

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
- Schoenberg total positivity does not provide an independent source-side shortcut.  For the
  symmetric coordinate `Xi(s)=Xi_1(-s^2)`, a one-sided Pólya-frequency representation of
  `1/Xi_1` is equivalent to RH, while the Pólya-frequency condition on its Taylor coefficients is
  the restricted Laguerre--Pólya condition.  The totally positive Jacobi-theta example attached to
  the zero set `{-n^2}` is a different transform and does not orient the differentiated Riemann
  theta-tail correlation `(4)`.
- Csordas's positive-definite-kernel results connect theta-kernel concavity to generalized *real*
  Laguerre inequalities.  They control restrictions to the real axis, where `(10)` already starts
  from zero, but do not sign the complex defect on `x+it`, `t>0`; making that extension for every
  fibre is a Laguerre--Pólya/RH condition.
- Effective Jensen-polynomial hyperbolicity applies to fixed degree and sufficiently large
  coefficient shift.  The cores here are unshifted initial sections whose degree grows with the
  approximation stage.  The literature explicitly retains all degrees and all shifts in the RH
  equivalence, so the high-shift Hermite asymptotic does not bound `(12)`.
- Haufschild's critical-Laguerre theorem is genuinely family-specific: an explicit moment law with
  an identity atom of mass `sqrt(2/e)>1/2` transfers the alternating critical signs of a Kummer-ODE
  base polynomial.  Its conclusion does not apply to `U_d`, but its mechanism gives the exact
  inverse-gamma scale representation `(13)` and a concrete energy estimate to test.
- The existing theta-tail first-moment Bezoutian and critical-tilt cards already contain the
  relevant full-source correlation identity.  Their positive-entry kernel is not a positive
  operator: its quadratic form on exponential packets is the Xi Hermitian orientation diagonal,
  and nonnegativity on the required cofinal family is equivalent to RH.  Replacing the exponential
  by its finite Taylor packet produces the same finite cross-current rather than a new square.
  Consequently the Volterra contraction in those cards can close the present task only if it is
  constructed on the finite source packets independently; assuming its contractivity merely
  renames the desired sign.

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
- [x] prove the exact negative current at the central completion seam point
- [x] identify the current with the vertical derivative of the finite squared modulus
- [x] derive and formalize the real-boundary-to-interior complex Laguerre-defect identity
- [x] audit classical theta, orthogonal-polynomial, spectral, and Wigner value relations
- [ ] prove an integrated cancellation bound for the raw moment terms in `(12)`
- [ ] obtain the eventual scaled core-current inequality on every anisotropic fibre
- [ ] complete paper proof and Lean theorem
