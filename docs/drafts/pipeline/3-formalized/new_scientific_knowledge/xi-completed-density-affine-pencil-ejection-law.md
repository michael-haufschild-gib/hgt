# Xi completed-density affine-pencil ejection law

- **ID:** `xi-completed-density-affine-pencil-ejection-law`
- **Stage:** 3-formalized
- **Type:** `[PROVED] [ROUTE OBSTRUCTION] [POSITIVE SURVIVOR] [NO RH CLAIM]`
- **Scientific status:** `[NOVELTY UNVERIFIED]`
- **Modules:**
  `formal/GaloisForLFunctions/HTGeometry/AffineSimpleZeroMotion.lean`;
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityAffinePencilEjection.lean`.
- **Parent:**
  `xi-completed-density-transverse-pick-zero-free.md`.

## Exact motion law

For analytic `H,K`, a simple zero `H(z0)=0`, and the affine relation

```text
H(g(c))+c*K(g(c))=0,
```

the holomorphic implicit-function theorem gives a local analytic zero branch with

```text
g(0)=z0,
g'(0)=-K(z0)/H'(z0).                                  (1)
```

This is formalized generically as `HTGeometry.exists_affineSimpleZero_branch`.  Its positive
survivor is the real-tangent law: if `H'(z0)` and `K(z0)` are real, then `Im g'(0)=0`.  A viable
real-zero deformation need not vanish on the target divisor, but it must at least be tangent to
the real divisor.  Schwarz-real perturbations meet this first-order obligation; an arbitrary
complex source channel does not.

## Completed-density specialization

Put

```text
H0(z)=2*z^2*XiC(z),
K(z)=E(z),
H_tau=tau*E+(1-tau)*H0,
tau=c/(1+c).
```

At every positive real Xi zero `t`, source sine positivity gives

```text
E(t)=i*Im(E(t)),   Im(E(t))>0.                          (2)
```

If the simple Xi slope is negative, then `(1)` becomes

```text
g'(0)=-E(t)/(2*t^2*XiC'(t)),
Im(g'(0))>0.                                            (3)
```

The formal theorem does not stop at velocity.  It proves that for every sufficiently small
positive real `c`, the actual point `g(c)` lies in the open upper strip and satisfies

```text
H_(c/(1+c))(g(c))=0.                                   (4)
```

Thus the proposed upper-zero-free homotopy is locally impossible at every displayed
negative-slope simple zero.  The theorem is an unconditional implication from its explicit
zero-and-slope hypotheses; no zero datum is inserted as an axiom.

## Signed winding correction

The old winding package detected an arbitrary real incidence coefficient after a `pi` phase
advance.  That is insufficient for a convex pencil.  The corrected signed theorem proves that a
continuous positive-modulus polar path with a full `2*pi` phase advance hits the **positive** real
axis.  For the incidence

```text
iota(z)=-H0(z)/E(z),
```

a hit `iota(z)=c>0` gives `tau=c/(1+c) in (0,1)` and an actual affine-pencil zero.  The composed
capstone is

```text
exists_thetaCuspTailSecondDensityDeBrangesAffinePencil_zero_of_two_pi_incidence_advance.
```

## Paper-level odd-multiplicity extension

Simplicity is not structurally needed.  Suppose `t>0` is a downward sign-changing Xi zero of odd
order `m`, with

```text
H0(t+delta)=A*delta^m+O(delta^(m+1)),   A<0.
```

By `(2)`, `E(t)=i*b`, `b>0`.  Under `delta=c^(1/m)*w`, the normalized pencil converges uniformly
on compact `w`-sets to

```text
A*w^m+i*b.                                               (5)
```

Equation `(5)` has a root with argument `pi/(2*m)`, hence in the open upper half-plane.  Rouche's
theorem on a small disk around that root transfers it to an upper pencil zero for every
sufficiently small `c>0`.  Classical Hardy sign change supplies a downward odd-multiplicity
critical-line zero without computation: `XiC(0)>0`, while the first transition to a negative
Hardy-sign interval is downward.  Therefore the raw affine zero-free homotopy is unconditionally
false on paper.  Formalization of this odd-order Rouche upgrade remains open; Lean currently
contains the complete simple-zero case.

## Frontier consequence

Top-edge control cannot repair this homotopy: zero-freeness already fails locally at the bottom
divisor.  Any replacement must preserve Schwarz reality or satisfy the exact tangent condition
at the real Xi divisor.  The direct Connes wall returns to constructing a source-defined cofinal
family of entire all-real-zero functions converging locally uniformly to `XiC`; the concrete
Hedenmalm wall remains the modular-seam phase-current inequality `(40)` in
`hedenmalm-center-mixed-double-positivity-law.md`.

## Formal gates

- [x] generic analytic simple-zero branch and exact velocity;
- [x] Schwarz-real first-order tangent survivor;
- [x] signed `2*pi` positive-incidence connector;
- [x] exact completed-density branch and upper-strip ejection;
- [x] eventual zero-free homotopy negation under negative simple slope;
- [ ] formalize odd-multiplicity Rouche scaling and the classical Hardy sign-change supplier;
- [ ] construct a Schwarz-real source approximant that closes `ConnesXiGroundStateLimitWall`.
