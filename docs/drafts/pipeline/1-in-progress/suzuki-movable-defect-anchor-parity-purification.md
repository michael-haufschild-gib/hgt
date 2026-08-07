# Suzuki movable-defect anchor and parity purification

- **ID:** `suzuki-movable-defect-anchor-parity-purification`
- **Stage:** 2 — dependency-closed paper proof; analytic core formalized in Lean
- **Route:** G / surviving two-angle Livšic--Hermite--Biehler producer
- **Scientific status:** `[SOURCE ADVANCE; PRIORITY UNVERIFIED]`
- **Parent facts:** deficiency spaces may be based at any nonreal point; spectral projections of
  compact-resolvent self-adjoint operators; Hilbert-valued Taylor expansion.
- **Candidate new content:** their combination for Suzuki's exponential defect sources, proving
  that every finite aperture admits arbitrarily pure bottom parity after moving the defect anchor,
  and isolating uniform interior-anchor observability as the first genuine cofinal obstruction.

## 1. Why this is the source frontier

Suzuki fixes the deficiency points at `+i` and `-i`.  This produces the source equations

```text
(A_a-lambda)v_+=e^x,
(A_a-lambda)v_-=e^(-x).
```

The choice `1` is a normalization of the defect point, not arithmetic data.  For every `c>0`, the
same adjoint computation at `+ic` and `-ic` instead gives

```text
(A_a-lambda)v_(+,c)=e^(cx),
(A_a-lambda)v_(-,c)=e^(-cx).                              (1)
```

The minimal operator and its self-adjoint extensions have not changed.  Only bases of the two
one-dimensional deficiency spaces and the extension-angle labels have changed.  Repeating
Suzuki's boundary-form proof gives

```text
W_(a,c,theta)(z)
  =(z-ic) integral v_(+,c)(x)e^(izx) dx
   +e^(i theta)(z+ic) integral v_(-,c)(x)e^(izx) dx,      (2)
```

and every zero of every member of `(2)` is real.

Consequently, a failure of the fixed source `e^x` to see a suitably polarized bottom eigenspace is
not yet a source obstruction.  The first legitimate question is whether the whole intrinsic
exponential family `e^(cx)`, `c>0`, can do so in a way compatible with a cofinal, unscaled Xi
limit.

## 2. Finite-aperture parity-purification theorem

Fix an aperture `a>0`.  Let `A=A_a` be Suzuki's self-adjoint restricted-Weil operator on
`L^2(-a,a)`.  Let `lambda_0` be its lowest eigenvalue, `G=ker(A-lambda_0)`, and `P` the orthogonal
projection onto `G`.  Reflection is

```text
(Jf)(x)=f(-x).
```

Because `A` commutes with `J`, so does `P`.

### Theorem A — first visible moment purifies parity

There is a least integer

```text
m=min{n>=0 : P(x^n) != 0}.                                (3)
```

For `c>0`, put `u_c=P(e^(cx))`.  Then

```text
c^(-m) u_c  ->  P(x^m)/m!                                (4)
```

in `L^2(-a,a)` as `c downarrow 0`.  In particular, `u_c!=0` for all sufficiently small `c>0`, and

```text
<J u_c,u_c>/||u_c||^2  ->  (-1)^m.                        (5)
```

Hence for every `0<=k<1` there is `c>0` such that

```text
k < |<J P(e^(cx)),P(e^(cx))>| / ||P(e^(cx))||^2.          (6)
```

#### Proof

Polynomials are dense in `L^2(-a,a)`.  If `P(x^n)=0` for every `n`, then `P` vanishes on a dense
subspace and therefore `P=0`, contradicting `G!=0`.  Thus `(3)` exists.

On the bounded interval, the exponential series converges in `L^2` uniformly for `c` in compact
sets.  Applying the bounded map `P` term by term and using minimality of `m` gives

```text
P(e^(cx))=c^m P(x^m)/m!+o(c^m),
```

which is `(4)`.  Since `PJ=JP` and `J(x^m)=(-1)^m x^m`, the nonzero leading vector in `(4)` is a
reflection eigenvector of sign `(-1)^m`.  Continuity of the inner product and norm gives `(5)`,
then `(6)`.

### Corollary A.1 — pointwise bottom visibility is automatic

For every finite aperture, the ground space is seen by `e^(cx)` for all sufficiently small
positive `c`, except possibly isolated values before that tail.  No positivity-improving theorem,
ground-state simplicity, or prescribed ground parity is required.

### Corollary A.2 — even and odd bottoms are equally admissible projectively

The sign in `(5)` records parity of the first visible moment.  The surviving two-angle divisor is
unchanged by relabelling the extension circle.  Its invariant nondegeneration datum is therefore
the modulus in `(6)`, not a preassigned sign at the conventional anchor `c=1`.

This does not erase signed information after a source angle has been fixed.  It says that the
fixed sign used in the old `81/85` cone is not invariant under the defect-base and extension-angle
normalizations available before taking the two-angle projective quotient.

## 3. Ground-edge realization

Fix a `c>0` for which `u_c=P(e^(cx))!=0`, and write `delta=lambda_0-lambda>0`.  Let

```text
w_(c,lambda)=(A-lambda)^(-1)e^(cx).                       (7)
```

Compact resolvent gives a positive gap from `lambda_0` to the rest of the spectrum.  Spectral
decomposition yields

```text
w_(c,lambda)=delta^(-1)u_c+r_(c,lambda),                  (8)
```

where `r_(c,lambda)` remains bounded as `lambda up to lambda_0`.  In the energy inner product of
`T=A-lambda`, the even and odd energies therefore satisfy

```text
E_(c,lambda)=delta^(-1)||u_c^+||^2+O(1),
O_(c,lambda)=delta^(-1)||u_c^-||^2+O(1),                  (9)
```

where `u_c^+=(u_c+Ju_c)/2` and `u_c^-=(u_c-Ju_c)/2`.  Thus

```text
(E_(c,lambda)-O_(c,lambda))/(E_(c,lambda)+O_(c,lambda))
  -> <Ju_c,u_c>/||u_c||^2.                                (10)
```

Combining `(6)` and `(10)` proves the source-selection statement.

### Theorem B — movable-anchor finite selection

At every finite aperture and for every `0<=k<1`, there are `c>0` and an admissible shift
`lambda<lambda_a` such that the phase-invariant first Livšic defect of Suzuki's all-angle family
based at `±ic` is greater than `k`.

In particular, taking `k=77/85` discharges the finite-aperture modulus version of the previously
advertised Xi first-defect cone.  It does not discharge cofinal Xi identification.

## 4. One fixed anchor on every strict-parity cofinal sequence

The movable anchor need not drift with aperture.  Suppose `a_n->infinity` and the even and odd
sector floors are unequal at every `a_n`.  Then the full bottom eigenspace at `a_n` has one pure
reflection parity.  Choose a nonzero real bottom vector `phi_n` and define its bilateral Laplace
transform

```text
F_n(c)=<phi_n,e^(cX)>.                                    (11)
```

`F_n` is entire.  It is not identically zero, since otherwise `phi_n` is orthogonal to every
monomial and polynomial density gives `phi_n=0`.  Its real zero set `Z_n` is discrete and therefore
countable.  Pure parity gives `F_n(-c)=±F_n(c)`, so `Z_n` is symmetric.  The countable union
`{0} union union_n Z_n` cannot exhaust `R`.  Choose `r` outside it and put `c=|r|`.  Symmetry gives
`c notin Z_n` for every `n`.

Thus one fixed interior anchor `c>0` sees every selected bottom eigenspace.  Because each bottom
space is pure parity, its reflection polarization has modulus exactly one.  For any prescribed
`k_n<1`, choose `lambda_n<lambda_(a_n)` close enough to the floor that the ground-pole defect has
modulus greater than `k_n`.

### Theorem C — fixed-anchor cofinal selection

If strict even/odd floor separation occurs at cofinally many apertures, then there are

```text
c>0,
a_n -> infinity,
lambda_n < lambda_(a_n),
```

all selected from the finite Suzuki source, such that the corresponding phase-invariant first
defects tend to one.  No uniform lower bound on a Laplace overlap is needed: arbitrarily small
nonzero overlap is amplified by taking `lambda_n` sufficiently close to the attained floor.

## 5. Exact parity-locking dichotomy and actual remaining source theorem

Write

```text
d(a)=lambda_a^+ - lambda_a^-.                             (12)
```

There is an exhaustive logical dichotomy:

1. for every `A` there exists `a>A` with `d(a)!=0`; or
2. there exists `A` such that `d(a)=0` for every `a>A`.

Theorem C completely solves first-defect source selection in branch 1.  Therefore the only
remaining obstruction at this stage is the rigid statement

```text
SUZUKI-EVENTUAL-PARITY-FLOOR-LOCKING:
  lambda_a^+ = lambda_a^- for every sufficiently large a. (13)
```

Route G must now either disprove `(13)` from the literal prime--Gamma screw kernel, or analyze the
permanently two-parity ground bundle and construct a two-angle selector directly through it.

This is strictly sharper than the old bottom-reflection cone:

- no pointwise visibility assumption remains;
- no uniform observability estimate remains;
- one fixed interior defect anchor works on the whole selected cofinal sequence;
- no fixed even-ground assumption remains;
- no signed `81/85` requirement remains before extension-angle normalization;
- no torque, safe Hankel minor, or second-jet calculation is relevant until `(13)` is resolved.

## 6. Relation to source conservation and verticality

The admission--separation law in
`riemann-source-modular-superselection/main-universal.tex` prevents choosing `c_j` by inspecting a
target Xi value.  The fixed-anchor selector above is source-only: its excluded zero sets come from
literal finite-aperture ground vectors and exponential defect sources.

The maximally vertical boundary theorem in `source-horizon-riemann-divisor/main.tex` explains why
even a fixed-anchor nondegenerate scalar limit cannot by itself be advertised as a bounded
prime-normal synthesis.  Retaining complete prime-normal rank still forces a singular,
relation-valued, or topology-changing completion.  Theorem C supplies admission into the scalar
two-angle family; it does not supply separation of the complete arithmetic source.

## 7. Hostile audit

1. **Does this prove RH?** No.  It removes finite-aperture and cofinal fixed-anchor visibility as
   obstructions whenever parity floors are not eventually locked.  Eventual locking and
   Xi/de Branges identification remain.
2. **Is arbitrary defect-base choice classical?** Yes.  It is parent operator theory and not
   claimed novel.
3. **Is the Taylor argument classical?** Yes.  Hilbert-valued Taylor expansion and polynomial
   density are parent analysis.
4. **What may be new?** The exact Suzuki application: projected exponential defect sources purify
   any reflection-invariant ground eigenspace, while countable zero-divisor avoidance chooses one
   fixed defect anchor on every strict-parity cofinal sequence.  This reduces the selector problem
   to eventual parity-floor locking.
5. **Could tiny overlaps defeat ground selection?** No.  The floor is attained and the shift may
   approach it after the source-only overlap is known; the pole amplifies every nonzero overlap.
6. **Could one choose `c_j` from Xi?** That would violate source admission.  `(11)` is deliberately
   finite-source measurable.
7. **Does phase modulus lose the RH orientation?** It is used only for nondegeneration of the
   projective two-angle family.  Xi identification must later fix the target phase and orientation.

## 8. Literature audit

Suzuki's 2026 paper fixes deficiency points `±i` and does not state the movable-anchor
parity-purification theorem.  General Livšic theory treats characteristic functions modulo defect
bases and disk automorphisms; this supplies parent normalization theory, not `(3)`--`(12)` for the
restricted Weil operator.  Targeted searches for the combination “Livšic characteristic
function / movable deficiency point / exponential source / ground parity projection” found no
matching theorem.  Priority remains unverified pending specialist review.

Primary references:

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- A. Aleman, R. T. W. Martin, W. T. Ross, *On a theorem of Livsic*, arXiv:1209.4497.

## 9. Lean boundary

`SuzukiMovableDefectAnchor.lean` formalizes, without axioms or computation:

- phase-invariant defect angle;
- countable symmetric bad-anchor avoidance and existence of one fixed positive anchor;
- Hilbert-valued first-visible-moment reflection purification;
- convergence to pure parity when one scaled energy has a positive leading coefficient and the
  opposite energy is lower order;
- eventual crossing of every threshold below one;
- stability under a subsequent ground-pole approximation.

The repository does not yet define Suzuki's unbounded `A_a`, its spectral projection `P_a`, or
Bochner `L^2` exponential source as Lean objects.  Therefore `(3)`--`(4)` remain the exact next
operator-infrastructure connector, and the operator-level interior-window/boundary-escape
dichotomy remains on paper rather than being silently replaced by a finite-dimensional model.
