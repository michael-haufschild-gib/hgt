# Hedenmalm's source inverse is a quantile-weighted universal Volterra boundary system

- **ID:** `hedenmalm-quantile-volterra-universal-boundary-defect`
- **Stage:** 2-fully-proven / needs external novelty and Lean audit
- **Type:** THEOREM / SOURCE-NORMAL OPERATOR CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `hedenmalm-theta-source-compressed-inverse-determinant.md`;
  `hedenmalm-supersymmetric-fredholm-range-divisor.md`;
  `../new_scientific_knowledge/hedenmalm-pair-weil-polarization-law.md`.

## Question

What remains of Hedenmalm's source-derived compact operator after the positive theta density is
put in its intrinsic probability coordinate?  Does its failure of self-adjointness remain an
infinite-dimensional bulk problem, or is it a boundary charge?

## Theorem

Let `k : R -> (0,infinity)` be continuous and integrable, put

```text
M = integral_R k(x) dx,
p(x) = M^(-1) integral_(-infinity)^x k(y) dy,
Q = p^(-1) : (0,1) -> R,
q(t) = Q'(t) = M/k(Q(t)).
```

Assume `p` is a `C^1` increasing bijection and that the closed derivative below is injective with
closed range `k^perp`, as proved for Hedenmalm's positive theta source.  On

```text
H_k = L2(R,k(x)^(-1) dx)
```

let `A` be the closed derivative from the Hedenmalm Fredholm theorem, let `P` be orthogonal
projection onto `k^perp`, and let

```text
B = A^(-1) P.
```

Define the pinned primitive on `L2(0,1)` by

```text
(C g)(t) = integral_0^t g(u) du - t integral_0^1 g(u) du.          (1)
```

Then the following statements hold.

1. The probability-integral transform

   ```text
   (U f)(t) = sqrt(M) f(Q(t))/k(Q(t))                              (2)
   ```

   is unitary from `H_k` onto `L2(0,1)`.

2. The complete source operator has the exact normal form

   ```text
   T := U B U^(-1) = i M_q C,                                     (3)
   ```

   where `M_q` is multiplication by the quantile speed `q`.  Thus all source dependence is one
   positive diagonal multiplier; the nonlocal primitive is universal.

3. Let

   ```text
   G = M_(1/q).                                                     (4)
   ```

   For the theta source, `G` is bounded, positive, injective, has dense nonclosed range, and is
   not bounded below.  It is therefore a canonical singular positive metric, not an ordinary
   equivalent Hilbert norm.  Its pullback is exactly ordinary Lebesgue `L2`:

   ```text
   <G U f,U f>_(L2(0,1)) = M^(-1) integral_R |f(x)|^2 dx.          (4a)
   ```

   Thus completion in this canonical metric is precisely the already-known ordinary-`L2`
   completion which loses the divisor fibres into continuous boundary spectrum.

4. The metric defect is source-independent and rank two:

   ```text
   T* G - G T = -i R_2,
   R_2 = C* + C,
   (R_2 g)(t)
     = (1-t) integral_0^1 g(u) du - integral_0^1 u g(u) du.        (5)
   ```

   Equivalently, `R_2` has kernel `1-t-u`.  Its range is
   `span{1,t}`, its kernel is the codimension-two moment space

   ```text
   integral g = integral t g = 0,                                 (6)
   ```

   and its two nonzero eigenvalues are `+1/sqrt(12)` and
   `-1/sqrt(12)`.  Hence its exact inertia is `(1,1)`.

5. Put

   ```text
   m(g) = integral_0^1 g(t) dt,
   c(g) = integral_0^1 (t-1/2) g(t) dt.
   ```

   The entire nonsymmetry is the hyperbolic boundary pairing

   ```text
   <R_2 g,g> = -2 Re(c(g) conjugate(m(g))).                         (7)
   ```

   With the convention that the Hilbert inner product is linear in its first argument, every
   nonzero eigenvector `T g = lambda g` obeys

   ```text
   2 Im(lambda) <Gg,g> = <R_2 g,g>.                                (8)
   ```

   Thus a nonreal spectral coordinate is neither a bulk defect nor a failure of positive source
   mass.  It is exactly a nonzero rank-two boundary flux.

6. The corresponding root mode and flux are explicit.  If `z != 0`, `lambda=-1/z`, and
   `Tg=lambda g`, then `m(g) != 0`.  With `h=Cg`, after scaling `m=m(g)` one has

   ```text
   h(t) = -m exp(-i z Q(t)) integral_0^t exp(i z Q(u)) du,
   g(t) =  i z m q(t) exp(-i z Q(t))
           integral_0^t exp(i z Q(u)) du.                            (9)
   ```

   The endpoint condition `h(1)=0` is exactly

   ```text
   integral_0^1 exp(i z Q(u)) du = M^(-1) Xi_C(z) = 0.              (10)
   ```

   In particular, every zero satisfies the ordered-correlation flux identity

   ```text
   Re integral_(0<u<t<1) exp(i z (Q(u)-Q(t))) du dt
     = -Im(z) integral_0^1 q(t)
         |integral_0^t exp(i z (Q(u)-Q(t))) du|^2 dt.                (11)
   ```

   The right side is strictly opposite in sign to `Im(z)`.  Formula `(11)` detects an off-axis
   zero without locating its height, but does not exclude it: an independent theta-source law
   forcing the left side nonnegative in the upper half-plane would be exactly the missing sign.

7. The boundary flux is exactly the already-known modular divisor charge, not a parallel
   detector.  Let `rho` be a nontrivial zero of multiplicity `m_rho`, put

   ```text
   z = -i (rho-1/2),
   Q_rho = Re Res_(s=rho) (-(s-1/2) Xi'(s)/Xi(s))
         = m_rho (1/2-Re(rho)).                                  (12)
   ```

   For every nonzero root mode `g` at `z`,

   ```text
   <R_2 g,g> / (2 <Gg,g>)
     = Im(-1/z)
     = Q_rho/(m_rho |z|^2),                                     (13)
   ```

   or equivalently

   ```text
   Q_rho
     = m_rho |z|^2 <R_2 g,g>/(2 <Gg,g>)
     = -m_rho |z|^2 Re(c(g) conjugate(m(g)))/<Gg,g>.             (14)
   ```

   Define the two boundary amplitudes

   ```text
   a_in(g)  = (m(g)-c(g))/sqrt(2),
   a_out(g) = (m(g)+c(g))/sqrt(2).                               (15)
   ```

   Then

   ```text
   <R_2 g,g> = |a_in(g)|^2-|a_out(g)|^2.                         (16)
   ```

   Thus the critical-line condition is exact equality of the incoming and outgoing boundary
   intensities.  The Hedenmalm Green defect, normalized Julia residue, shell-transfer entropy,
   and independent-quadrant Sonin Lyapunov exponent are four charts of the same charge.

For Hedenmalm's theta source, the preceding compressed-inverse theorem identifies the nonzero
eigenvalues as `lambda=-1/z` at the centered Xi zeros `z`.  Consequently RH is equivalent to
vanishing of `(7)` on every root space.  Equation `(8)` is a classification, not a proof of that
vanishing.

## Proof

Since `p'(x)=k(x)/M`, the quantile derivative is `q(t)=M/k(Q(t))` and
`dx=q(t)dt`.  Therefore

```text
integral_R |f(x)|^2/k(x) dx
  = M integral_0^1 |f(Q(t))/k(Q(t))|^2 dt,
```

which proves unitarity of `(2)`.

For `g=Uf`, one has `f(Q(t))=k(Q(t))g(t)/sqrt(M)`.  Changing variables in ordinary Lebesgue
integrals gives

```text
integral_(-infinity)^Q(t) f(y) dy = sqrt(M) integral_0^t g(u) du,
integral_R f(y) dy                 = sqrt(M) integral_0^1 g(u) du.
```

The explicit Hedenmalm inverse

```text
(Bf)(x)=i integral_(-infinity)^x
  (f(y)-M^(-1)(integral_R f)k(y)) dy
```

now gives `(3)` after applying `U` once more.

For the theta source, `k` is bounded, strictly positive, and tends to zero at both ends.  Hence
`1/q=k(Q)/M` is bounded and positive almost everywhere, but tends to zero at `t=0,1`.  This proves
positivity, injectivity, and failure of a lower bound for `G`; density of its range follows from
`ker G=0`, while a bounded injective self-adjoint multiplier with nonclosed-away-from-zero symbol
cannot have closed range.  Substituting `(2)`, `1/q=k(Q)/M`, and
`dt=k(x)dx/M` gives `(4a)` directly.

Fubini gives

```text
(C* g)(t)=integral_t^1 g(u) du - integral_0^1 u g(u) du.
```

Although `M_q` is unbounded at the endpoints, `(3)` is a bounded operator identity because its
left side is the bounded Hilbert--Schmidt operator `UBU^(-1)`.  The bounded cancellation

```text
GT  =  i M_(1/q) M_q C =  i C,
```

holds first pointwise on the natural dense core and then everywhere by continuity.  Taking the
adjoint of this bounded identity gives `T*G=-iC*`; no illegal reversal of an unbounded multiplier
is used.  Subtraction proves `(5)`.  Adding the displayed formulas for `C` and `C*` gives the kernel
`1-t-u`, the range and kernel statements, and `(7)`.

Write `e_0(t)=1` and `e_1(t)=sqrt(12)(t-1/2)`.  They are orthonormal and

```text
R_2 e_0 = -(1/sqrt(12)) e_1,
R_2 e_1 = -(1/sqrt(12)) e_0.
```

The matrix on their span is therefore

```text
[[0,-1/sqrt(12)],[-1/sqrt(12),0]],
```

which proves the eigenvalue and inertia claim.  Finally, evaluate `(5)` on an eigenvector.  The
left side is `(conjugate(lambda)-lambda)<Gg,g>` under the stated convention, yielding `(8)`.

For the root-mode formula, put `h=Cg`.  Then `h(0)=h(1)=0` and
`h'=g-m`.  The eigenvalue equation `i qh=-g/z` becomes

```text
h'(t)+i z Q'(t)h(t)=-m.
```

Multiplication by `exp(i z Q(t))` and integration from `0` to `t` gives the first formula in
`(9)`; the eigenvalue equation gives the second.  If `m=0`, uniqueness for this first-order
equation and `h(0)=0` would give `h=g=0`, so every eigenvector has `m != 0`.  The endpoint at one
gives `(10)`.  Moreover, `c(g)=-integral h`, while `(9)` gives

```text
<Gg,g> = |z|^2 |m|^2 integral_0^1 q(t)
  |integral_0^t exp(i z (Q(u)-Q(t))) du|^2 dt.
```

Substitution into `(7)`--`(8)`, together with
`Im(-1/z)=Im(z)/|z|^2`, proves `(11)`.

Finally,

```text
Im(z) = 1/2-Re(rho) = Q_rho/m_rho.
```

Combining this identity with `(8)` and `lambda=-1/z` proves `(13)`--`(14)`.  Expanding the two
squares in `(15)` gives `(16)`.

## What this changes

Hedenmalm's open positive realization is not an unspecified search for a bulk inner product.
There is a canonical source-derived singular positive metric already, and it removes the complete
quantile speed.  What remains is exactly one universal two-channel boundary current with one
positive and one negative direction.

This unifies several corpus observations.

- The Witten square is positive because it scalarizes before this boundary current is read.
- Reflection-folded Dirac and causal/anti-causal formulas retain two boundary channels because
  `R_2` has rank two.
- The universal rank-two tangent inertia `(1,1)` is the same boundary signature in a different
  chart.
- Divisor-supported Weil polarization is nonlocal because no multiplication metric can remove
  `(5)`; the best multiplication metric leaves the exact finite-rank obstruction.
- The dense-radical/ordinary-`L2` no-go is not a separate pathology: `(4a)` says it is exactly
  the completion selected by the canonical quantile metric.
- Positive completion debt is unavoidable: a rank-two defect of inertia `(1,1)` cannot be
  canceled by adding only a decoupled positive scalar channel.
- Stone universality is compatible with the law: isodivisorial sources change `q` and the root
  modes, but not the universal boundary form.  Divisor data alone cannot choose which source
  boundary traces should be neutral.
- The source-normal Stokes/Bockstein problem now has a literal Hedenmalm landing target: it must
  carry the ordinary-prime inverse/adjoint comparison to the two amplitudes `(15)` and prove
  equality of their norms before divisor specialization.  Merely pairing reflected zeros only
  swaps the channels and permits nonzero flux.

The theorem does not produce the missing neutralization.  It replaces the vague requirement
“construct a positive self-adjoint realization” with a literal source obligation:

> Construct, before zero specialization, a singular cross-source boundary law forcing every
> Xi root mode's quantile trace `(m,c)` into the null cone
> `Re(c conjugate(m))=0`, while retaining every conormal and its multiplicity.

That obligation is still RH-bearing by `(8)` and must not be renamed “purity,” “same-fibre
dagger,” or “conservativity.”

## Hostile audit

1. **Not RH.**  The defect has both signs.  Nothing here proves its quadratic value vanishes on
   theta root modes.
2. **Not an ordinary metric.**  `G` is not bounded below and its range is nonclosed.  Completion
   in the `G`-norm can lose precisely the boundary modes under discussion.
3. **No quotient proof.**  Quotienting by `span{1,t}` or restricting to `(6)` kills the defect but
   is invalid unless every root mode survives and the chosen space is invariant.  Neither is
   proved, and generic root modes do not satisfy `(6)`.
4. **No finite-rank repair.**  Adding an abstract two-dimensional Krein channel gives a formal
   conservative colligation but not a positive Hilbert realization.  Positivity of that repair is
   the missing sign again.
5. **No generic shape theorem.**  The normal form holds for every smooth positive density, including
   sources whose Fourier transforms have off-axis zeros.  Arithmetic must enter through the
   allowed root-mode boundary traces, not through `(3)`--`(5)` alone.
6. **No target-fed metric.**  `G` is constructed from `k` before reading a zero.  The null-cone
   condition on all root modes is not constructed and is stated only as the open successor.

## Corpus and literature audit

Targeted corpus searches for `quantile`, `CDF`, `Brownian bridge`, `weighted Volterra`, and the
kernel `1-t-u` found no existing statement of `(2)`--`(8)`.  Existing Hedenmalm cards construct
`B`, its Fredholm determinant, the Witten square, the reflection fold, and the Weil metric
classification, but do not put `B` in probability-integral coordinates or compute this universal
rank-two metric defect.

The external ingredients are classical separately: probability-integral/quantile transport,
the Volterra operator and its adjoint, finite-rank boundary forms, and Grushin/Evans reductions.
Targeted searches found no paper combining them into the source-normal form `(3)`, metric defect
`(5)`, and Xi spectral-flux law `(8)`.  External novelty remains unverified pending a broader
operator-theory and boundary-triple citation audit.

Primary adjacent sources:

- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494 (2026).
- F. Gesztesy, Y. Latushkin, and K. A. Makarov, *Evans functions, Jost functions, and Fredholm
  determinants*, Arch. Ration. Mech. Anal. 186 (2007), 361--421.
- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Theorie des Nombres de Bordeaux 16 (2004), 65--94.

## Lean status

Paper proof is dependency-closed.  Lean formalization is open.  A meaningful formalization must
include the change-of-variables unitary, the transformed operator identity `(3)`, the adjoint
calculation, and exact rank-two inertia.  Formalizing only the `2 x 2` matrix would not certify the
new source theorem.

## Gates

- [x] internal corpus and failed-route search
- [x] exact source-normal conjecture frozen before proof
- [x] dependency-closed paper proof
- [x] hostile audit
- [ ] broad external novelty audit
- [ ] Lean probability-integral transform and operator identity
- [ ] Lean exact metric-defect inertia
- [ ] source theorem forcing the theta root traces into the neutral cone
- [ ] RH
