# Burnol bilateral aperture-defect energy law

- **ID:** `burnol-bilateral-aperture-defect-energy-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[VALUE RELATION] [RH INTERFACE]`
- **Scientific status:** `[PROVED HERE] [NOT AN RH PROOF]`
- **Parents:** normalized Mellin dilation covariance; the projected evaluator transport in
  `burnol-prime-dilation-copoisson-quotient-law.md`; forward and inverse Sonin aperture covariance.
- **Statement:** The difference between the inverse- and forward-dilation cross-aperture defect
  energies is exactly the hyperbolic modulus defect of the Mellin character.  Hence equality of
  the two source defects detects the critical line, while a one-sided defect inequality on
  right-half Xi zeros is already sufficient for RH.

## Theorem

Let `H` be the ambient cosine-transform Hilbert space, `K_a` the Sonin carrier at aperture `a>0`,
and `P_a` its orthogonal projection.  Let `r>1`, let `U_r` be normalized dilation, and let
`Z^a_w in K_a` be the continuous completed-Mellin evaluation vector at `w`.  Put

```text
lambda_r(w)=r^(w-1/2).
```

Both `U_r` and `U_r^*=U_(1/r)` send `K_a` into `K_(a/r)`: in one direction the physical support
gap becomes `a/r`, and in the other direction the Fourier support gap becomes `a/r`.  The two
projected Riesz laws are therefore

```text
P_a U_r^* Z^(a/r)_w = conj(lambda_r(w)) Z^a_w,          (1)
P_a U_r   Z^(a/r)_w = conj(lambda_r(w)^(-1)) Z^a_w.     (2)
```

Define the ambient cross-aperture defects

```text
epsilon^+_(a,r,w)=(1-P_a)U_r^*Z^(a/r)_w,
epsilon^-_(a,r,w)=(1-P_a)U_r  Z^(a/r)_w.               (3)
```

Then

```text
||Z^(a/r)_w||^2
 =|lambda_r(w)|^2 ||Z^a_w||^2+||epsilon^+_(a,r,w)||^2, (4)

||Z^(a/r)_w||^2
 =|lambda_r(w)|^(-2)||Z^a_w||^2+||epsilon^-_(a,r,w)||^2. (5)
```

Consequently,

```text
||epsilon^-_(a,r,w)||^2-||epsilon^+_(a,r,w)||^2
 =(|lambda_r(w)|^2-|lambda_r(w)|^(-2))||Z^a_w||^2
 =(r^(2 Re(w)-1)-r^(1-2 Re(w)))||Z^a_w||^2.           (6)
```

Whenever `Z^a_w` is nonzero, `(6)` gives

```text
||epsilon^-_(a,r,w)||=||epsilon^+_(a,r,w)||
  iff |lambda_r(w)|=1
  iff Re(w)=1/2.                                       (7)
```

It also records the orientation, not merely the critical set:

```text
Re(w)>1/2 iff ||epsilon^-_(a,r,w)||>||epsilon^+_(a,r,w)||,
Re(w)<1/2 iff ||epsilon^-_(a,r,w)||<||epsilon^+_(a,r,w)||. (8)
```

## Finite projection-curvature form

The two scalar defects are evaluations of one source-defined self-adjoint finite holonomy.  Put

```text
Q_a=1-P_a,
H_(a,r)=U_r P_a U_r^*-U_r^* P_a U_r.                    (9)
```

For every ambient vector `z`, orthogonality and unitarity give

```text
||Q_a U_r z||^2-||Q_a U_r^* z||^2
 =Re <z,H_(a,r)z>.                                      (10)
```

Taking `z=Z^(a/r)_w` converts `(10)` exactly into `(6)`.  Thus the missing contraction is not an
unspecified comparison between two norms: it is nonpositivity of one explicit source projection
curvature on the zero-evaluation fibers.

Let `F` be the cosine Fourier involution.  Since `F U_r F=U_r^*` and `F` preserves `K_a`,

```text
F H_(a,r) F=-H_(a,r).                                   (11)
```

The completed Mellin functional equation sends the evaluator at `w` to the evaluator at
`1-conj(w)`.  Hence `(11)` exchanges the two FE--Schwarz fibers and reverses the defect energy.
This explains why ordinary reflection proves only the paired sign law: a same-fiber sign or
balance still needs an additional source value relation.

The existing Lean phase rotation is the infinitesimal version of this finite holonomy.  If
`U_(exp t)=exp(i t D)` in a self-adjoint generator convention, then

```text
d/dt|_(t=0) H_(a,exp t)
 =2i(DP_a-P_aD)
 =2 projectionPhaseRotation(P_a,D).                    (12)
```

So `SemilocalProjectionPhasePolarization.lean` already formalizes the local algebraic orientation
operator appearing in `(12)`.  What it proves is curvature conversion and compactness transfer,
not a sign on the Burnol zero-evaluation fibers.

The statements remain valid for every evaluation jet after replacing the scalar component by the
triangular character-jet block and the squared norm by its corresponding Gram defect.  The
zeroth-jet statement above is already the minimal RH interface.

## Proof

For `f in K_a`, normalized Mellin covariance gives

```text
M(U_r f)(w)=lambda_r(w)M(f)(w),
M(U_r^*f)(w)=lambda_r(w)^(-1)M(f)(w).
```

Riesz representation against vectors of `K_a` gives `(1)` and `(2)`.  It gives only the projected
laws: the full ambient adjoint vectors can have nonzero components orthogonal to `K_a`, precisely
the two vectors in `(3)`.

Because `P_a` is orthogonal, the two terms in each decomposition

```text
U_r^*Z^(a/r)_w=P_aU_r^*Z^(a/r)_w+epsilon^+_(a,r,w),
U_r  Z^(a/r)_w=P_aU_r  Z^(a/r)_w+epsilon^-_(a,r,w)
```

are orthogonal.  Apply Pythagoras, use `(1)`--`(2)`, and use unitarity of `U_r` to replace both
left-hand norms by `||Z^(a/r)_w||`.  This proves `(4)`--`(5)`.  Subtraction proves `(6)`.  Since

```text
|lambda_r(w)|=r^(Re(w)-1/2)
```

and `r>1`, the coefficient in `(6)` vanishes exactly on the critical line and has the sign of
`Re(w)-1/2`.  This proves `(7)`--`(8)`.

## RH consequence and the remaining producer

For the nontrivial Xi divisor, the completed Sonin evaluation functionals are nonzero.  Therefore,
for any fixed `a>0` and `r>1`, the theorem yields the exact criterion

```text
RH
 iff every Xi-zero evaluator has balanced bilateral aperture defects. (13)
```

More usefully, Schwarz reality and the functional equation pair every off-line zero with a zero in
the open right half of the critical strip.  Thus the strictly weaker-looking source inequality

```text
||epsilon^-_(a,r,rho)|| <= ||epsilon^+_(a,r,rho)||      (14)
```

for every actual Xi zero `rho` with `Re(rho)>=1/2` already implies RH: a right-half off-line zero
would make `(6)` strictly positive and contradict `(14)`.  This gives the top-down chain

```text
source-side bilateral defect contraction on right-half zero evaluators
 -> no right-half off-critical Xi zero
 -> no off-critical Xi zero by reflection
 -> RH.                                                (15)
```

The open part is not another character computation.  It is to derive `(14)`, or the equality in
`(13)`, from a source theorem about the actual Sonin projection and the two physical/Fourier support
losses.  Positive Hilbert-space geometry alone cannot choose the sign: `(6)` shows that its sign is
exactly the zero orientation.  A successful producer must exploit an additional value relation
specific to the canonical prime--Gamma source, such as a contraction, monotonicity, or reflection
identity that compares the two defects at the same divisor point.

The divisor can be removed from the hypothesis.  Burnol's theorem identifies the closed
zero-evaluator span in the extended Sonin space with the orthogonal complement of the closed
co-Poisson source subspace.  Therefore the source-defined operator order obtained by compressing
`H_(a,r)` to that co-Poisson quotient implies `(14)` simultaneously for every zero evaluator.  The
quotient is Fourier invariant and `H_(a,r)` is Fourier odd, so either semidefinite order is
equivalent to exact flatness and to vanishing of one parity-mixing block.  The complete reduction
is proved in
`burnol-copoisson-quotient-bilateral-order-rh-law.md`.

## Why this is not the Calkin-lift conjecture

The bilateral identity is a vector norm law and requires neither the co-Poisson/time-band operator
lift nor a prime-pair compactness theorem.  Conversely, it does not imply that either defect is
compact, lies in the time-band ideal, or has the correct phase-polarized Calkin principal part.
It is therefore an independent, shorter top-down interface:

```text
same-point source defect contraction -> RH,
```

whereas the operator route remains

```text
co-Poisson/time-band lift -> prime-charge coherence -> charge decay -> RH.
```

## Corpus interfaces

- `formal/GaloisForLFunctions/RHTower/SoninEulerCalkinPartialIsometry.lean` proves both normalized
  dilation and inverse-dilation aperture inclusions;
- `burnol-prime-dilation-copoisson-quotient-law.md` proves the projected evaluator transport and
  identifies the orthogonal defect omitted by the false full-vector argument;
- `burnol-copoisson-quotient-bilateral-order-rh-law.md` replaces the zero-indexed contraction by
  one source-pure operator order on the closed co-Poisson quotient;
- `../../1-in-progress/burnol-copoisson-prime-seam-calkin-lift.md` is the distinct operator-ideal
  route;
- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamCoherenceCollapse.lean` supplies a longer
  prime-charge consumer, but is not needed for `(15)`.

The formal corpus does not yet define Burnol's continuous evaluation vectors, so no Lean wrapper is
added.  The source-side dilation inclusions needed for their future formalization are already
present.

## Literature boundary

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Théor. Nombres Bordeaux 16 (2004), 65--94: continuous Sonin evaluation vectors and
  their zero-divisor systems.
- The norm identity `(6)` is the elementary orthogonal-decomposition consequence of Burnol's
  evaluator framework and normalized Mellin covariance.  No claim is made that the same-point
  contraction `(14)` appears in the literature or is already proved.

## Gates

- [x] forward normalized-dilation aperture inclusion
- [x] inverse normalized-dilation aperture inclusion
- [x] projected forward and inverse evaluator laws
- [x] exact bilateral Pythagorean identities
- [x] exact signed defect-energy law
- [x] finite projection-curvature and Fourier-odd reflection forms
- [x] identification with the existing infinitesimal phase-polarization operator
- [x] critical-line balance and one-sided RH consumer
- [ ] derive the same-point defect contraction from the canonical source
- [ ] formalize only after continuous Sonin evaluation vectors enter Lean
- [ ] compose an unconditional source proof of `(14)` with `(15)`
