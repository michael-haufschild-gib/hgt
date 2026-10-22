# Suzuki homogeneous projective-resolvent Plücker lift

- **ID:** `suzuki-homogeneous-projective-resolvent-plucker-lift`
- **Stage:** 3 — formalized in Lean 4
- **Type:** FRONTIER REPRESENTATION THEOREM / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `suzuki-negative-projector-coherent-completion`
- **Failed producer:**
  `../../5-failed/suzuki-negative-projector-triangle-producer.md`
- **RH used:** no
- **Computation used:** no

## Exact problem

The previous affine-resolvent analysis treated the source response as a linear matrix element of
`(A-lambda)^(-1)`.  The actual Suzuki response is projective:

```text
q_lambda(z)=N_z(u_lambda)/D_z(u_lambda),
u_lambda=(A-lambda)^(-1)e,
```

after the Euler--Gamma and Neumann pieces are placed in one gauge.  Linear-resolvent negative
projectors therefore act on the wrong object.  The theorem below gives the exact representation
of two-shift projective motion.

## Theorem A: fixed Plücker blade of a resolvent chord `[PAPER-PROVED]`

Let `V` be a real or complex vector space, `A : V -> V`, and let `alpha != beta` lie in the
resolvent set.  Put

```text
u_alpha=(A-alpha)^(-1)e,
u_beta =(A-beta)^(-1)e,
v=(A-alpha)^(-1)(A-beta)^(-1)e.
```

Resolvents commute with `A`, so

```text
u_beta =A v-alpha v,
u_alpha=A v-beta v.                                   (1)
```

For linear boundary functionals `B,D`, define their projective minor

```text
[B,D](x,y)=B(x)D(y)-B(y)D(x).                         (2)
```

Substitution in `(2)` gives the exact chord law

```text
[B,D](u_beta,u_alpha)
  =(beta-alpha)[B,D](v,A v).                          (3)
```

Equivalently, in exterior notation,

```text
u_beta wedge u_alpha
  =(beta-alpha) v wedge A v.                          (4)
```

Thus the whole two-shift Euler--Gamma motion is the image of one fixed decomposable Plücker
blade filtered by the product resolvent.  It is not a sum of independent one-mode resolvent
defects.

### Proof

From `(1)`, write `x=B(v)`, `X=B(Av)`, `y=D(v)`, and `Y=D(Av)`.  Then the left side of `(3)` is

```text
(X-alpha*x)(Y-beta*y)-(X-beta*x)(Y-alpha*y)
=(beta-alpha)(xY-Xy),
```

which is the right side.  Formula `(4)` is the same alternating-bilinear identity before applying
`B wedge D`.  No positivity or spectral theorem is used.

## Theorem B: affine Neumann channel is the homogeneous coordinate `[PAPER-PROVED]`

Let the full numerator contain one affine comparison channel

```text
L(u_lambda)-lambda K(u_lambda).                       (5)
```

The resolvent equation `A u_lambda-lambda u_lambda=e` gives

```text
L(u_lambda)-lambda K(u_lambda)
  =(L-KA)(u_lambda)+K(e).                             (6)
```

Set `B=L-KA`, `c=K(e)`, and homogenize the resolvent state:

```text
U_lambda=(u_lambda,1) in V direct_sum F,
Btilde(u,s)=B(u)+c*s,
Dtilde(u,s)=D(u).                                     (7)
```

Then the full projective chord, including the affine channel, is

```text
[Btilde,Dtilde](U_beta,U_alpha)
 =(beta-alpha)
   { B(v)D(Av)-B(Av)D(v)-cD(v) }.                    (8)
```

In exterior notation this is the single homogeneous blade

```text
U_beta wedge U_alpha
 =(beta-alpha)(v,0) wedge (Av,1).                    (9)
```

The `V wedge V` component `v wedge Av` is Euler--Gamma projective curvature.  The
`V wedge F` component `v wedge 1` is the affine Neumann/projective-holonomy channel.  They are
not unrelated diagonal and off-diagonal corrections: they are forced components of one
decomposable blade.

### Proof

Equation `(6)` follows by applying `K` to the resolvent equation.  For `(8)`, expand

```text
(B(u_beta)+c)D(u_alpha)-(B(u_alpha)+c)D(u_beta).
```

The `B,D` part is `(3)`.  From `(1)`,
`D(u_alpha)-D(u_beta)=-(beta-alpha)D(v)`, giving the last term.  This proves `(8)` and its
coordinate-free form `(9)`.

## Theorem C: spectral-pair law and rank-one blindness `[PAPER-PROVED]`

On a two-mode diagonal spectral plane, write

```text
A(v_0,v_1)=(t_0 v_0,t_1 v_1),
B=(b_0,b_1), D=(d_0,d_1).
```

Then

```text
[B,D](v,Av)
 =(t_1-t_0)v_0v_1(b_0d_1-b_1d_0).                   (10)
```

Consequently:

1. Euler--Gamma shift motion lives on unordered spectral pairs, weighted by a spectral gap and a
   source Plücker minor.
2. Its sign depends on source orientation, not on `sign(t_j)`.
3. On any one-dimensional invariant spectral line, `v wedge Av=0`; the Euler--Gamma projective
   quotient is exactly shift-flat.  Only homogeneous coordinate `c`, hence the affine Neumann
   channel, can move a one-mode projective response.

For a finite diagonal model, expanding `(3)` gives

```text
N_beta D_alpha-N_alpha D_beta
 =(beta-alpha) sum_(i<j)
   (t_j-t_i)v_i v_j(b_i d_j-b_j d_i).                (11)
```

Here `v_i=e_i/((t_i-alpha)(t_i-beta))`.  When both shifts lie below the spectrum, all resolvent
denominators have fixed positive sign.  The remaining sign problem is exactly total orientation
of boundary Plücker minors.

**`(11)` is formal** as `suzukiDiagonalProjectiveChord_expansion`: the chord of a diagonal model is
the double sum of the spectral gap `t_j - t_i` against the source coefficients.  The module
previously carried only `(10)`, the two-mode case.
`suzukiDiagonalProjectiveChord_diagonal_eq_zero` records that every diagonal term vanishes, so the
chord sees genuine spectral pairs only — the rank-one blindness of Theorem C at the level of the
sum.

`suzukiDiagonalProjectiveChord_symmetrized` exhibits the displayed pairing: symmetrizing the
expansion couples the blade coordinate `(t_j - t_i) v_i v_j`, which involves only spectral data,
against the source's own minor `b_i d_j - b_j d_i`.  That is `(4)`'s "fixed blade" claim in
coordinates — the source enters only through its minors — and it needs no ordering of the index set,
so no choice of orientation is smuggled in.

### Proof

Expand both products in `(10)`; diagonal terms cancel and two cross terms combine.  Summing the
same identity over all two-coordinate restrictions gives `(11)`.  If `Av=t v`, alternation gives
`[B,D](v,Av)=t[B,D](v,v)=0`.

## Hostile audit

- **Not a hidden RH premise.** `A`, its resolvents, source vector, and boundary functionals are
  finite-aperture source data.  No Xi divisor or positivity is used.
- **Not the second resolvent identity renamed.** Ordinary identity gives `u_beta-u_alpha`.
  Equations `(3)` and `(8)` identify projective quotient motion and show exactly how affine
  comparison channel enters after homogenization.
- **Projector producer fails.** A negative one-mode spectral coordinate has nonzero linear
  negative-projector debt, while its Euler--Gamma projective chord is identically zero.  Hence
  `P_- W` cannot be the canonical completion of the actual quotient response.
- **Neumann term is retained.** It is the `-cD(v)` component of `(8)`, not discarded as a central
  affine gauge.
- **No positivity claimed.** A Plücker minor can have either sign.  The theorem relocates exact
  source obligation; it does not assume positive Grassmannian orientation.
- **External audit.** Current searches across resolvent identities, ratios of Cauchy transforms,
  boundary triples, compound resolvents, and Plücker/Grassmannian resolvent curves found the
  classical ingredients but no Suzuki prime--Gamma/Neumann homogeneous-blade statement.  No
  priority claim is made.

## New RH-bearing conjecture

### `SUZUKI-PLUCKER-CHRISTOFFEL-DARBOUX-WELD` `[CONJECTURE]`

For one recurrence-selected aperture and admissible shift pair, place physical reflected
Euler--Gamma triangle and exact Neumann comparison channel in the homogeneous gauge `(7)`.  Let
`B_z,D_z` be resulting source boundary functionals.  Prove, source-before-divisor, that the gauged
Pick polarization of

```text
(B_z wedge D_z)((v,0) wedge (Av,1))                  (12)
```

equals a positive Gram kernel plus the exact Xi-multiplier deficit.  Equivalently, prove the
boundary image of the filtered blade `(9)` lies in the required positive Plücker cone on every
finite upper-half-plane node packet.

`[OPEN CORE]` Derive a Christoffel--Darboux/Green identity for the actual prime--Gamma boundary
map `z |-> (B_z,D_z)` whose right side is a positive restricted-source Gram.  This is stronger and
more falsifiable than asking an unspecified triangle to equal a weighted negative projector: one
wrong two-mode Plücker orientation kills it.

If `(12)` holds, existing exact Loewner-gap theorem gives jump Pick positivity; existing pole
tomography then excludes every nonreal Xi zero and proves RH.

## Significance

The frontier changes representation:

```text
old:  linear resolvent Krein defect + external projector + Schur tax
new:  one homogeneous decomposable resolvent blade
      = Euler--Gamma pair curvature + Neumann homogeneous component.
```

This removes the false one-node negative-projector target and identifies exact source theorem as
a positive-Grassmannian Christoffel--Darboux identity on spectral pairs.

## Formal target

`(2)--(3)`, `(6)--(8)`, `(10)--(11)`, quotient cross-multiplication, rank-one blindness, and the
connector to Suzuki's existing projective Neumann numerator are formalized in
`RHTower/Suzuki/SuzukiProjectiveResolventPluckerLift.lean`:

```text
suzukiProjectiveResolventMinor                        (2)
suzukiProjectiveResolventMinor_swap
suzukiProjectiveResolventMinor_chord                  (3)
suzukiProjectiveResolventMinor_twoResolvents
suzukiProjectiveResponse_sub_eq_minor                 quotient cross-multiplication
suzukiShiftedAffineSourceNumerator                    (5)
suzukiShiftedAffineSourceNumerator_eq_homogeneous     (6)-(7)
suzukiHomogeneousProjectiveResolventChord             (8)
suzukiShiftedAffineSourceProjectiveChord_twoResolvents
suzukiProjectiveResolventMinor_eigenvector_eq_zero    rank-one blindness
suzukiTwoModeProjectiveResolventMinor_eq              (10)
suzukiTwoModeProjectiveResolventMinor_nonneg_iff_orientation
suzukiCenteredProjectiveShiftNumerator_eq_projectiveMinor   Neumann-numerator connector
suzukiDiagonalProjectiveChord_expansion               (11)
suzukiDiagonalProjectiveChord_diagonal_eq_zero
suzukiDiagonalProjectiveChord_symmetrized
```

The two exterior-notation statements `(4)` and `(9)` — the ones asserting that the chord is a
*single decomposable blade* rather than a family of minors — are formalized separately, because
they live in the exterior square rather than in a pair of boundary functionals:

```text
GaloisForLFunctions/HTGeometry/AlternatingChordLaw.lean
  altPair, altPair_add_left, altPair_add_right, altPair_smul_left, altPair_smul_right,
  altPair_self, altPair_swap, altPair_sub_left, altPair_sub_right
  altPair_chord        the chord law for an arbitrary 2-alternating map into any module
  exteriorPair_chord   its exterior-square instance

GaloisForLFunctions/RHTower/Suzuki/SuzukiProjectiveResolventBlade.lean
  suzukiResolventBlade_chord              (4): u_beta ∧ u_alpha = (beta-alpha) v ∧ A v
  suzukiHomogeneousState_eq               (A v - alpha v, 1) = (A v, 1) - alpha (v, 0)
  suzukiHomogeneousResolventBlade_chord   (9): the same law after homogenization, in V × F
```

`altPair_chord` is stated for an arbitrary `2`-alternating map into an arbitrary module, so `(3)`
and `(4)` are one theorem read through two different alternating maps — the pair of boundary
functionals and the exterior square — which is exactly the card's claim that the minors are
shadows of one blade.  Axiom audit of all nine declarations: `propext`, `Classical.choice`,
`Quot.sound` only.


## Log

- 2026-08-01 — `(11)` formalized (`suzukiDiagonalProjectiveChord_expansion`).  The module carried
  `(10)`, the two-mode identity, but not its summed form, which is the one the finite-model sign
  discussion actually uses — the same two-mode-versus-general-sum gap as the scalar-versus-operator
  pattern elsewhere in this folder.  `suzukiDiagonalProjectiveChord_diagonal_eq_zero` gives Theorem
  C's rank-one blindness at the level of the sum: the diagonal terms vanish identically, so only
  genuine spectral pairs contribute.  Two new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the blade/source factorization made explicit
  (`suzukiDiagonalProjectiveChord_symmetrized`).  Symmetrizing the `(11)` expansion pairs the blade
  coordinate `(t_j - t_i) v_i v_j` against the source minor `b_i d_j - b_j d_i`, which is `(4)`'s
  fixed-blade claim in coordinates.  Doing it by symmetrization rather than by summing over `i < j`
  avoids choosing an ordering of the index set, so no orientation is introduced by the formalization
  itself — which matters on a card whose open problem is precisely the total orientation of the
  source minors.  One new declaration, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
