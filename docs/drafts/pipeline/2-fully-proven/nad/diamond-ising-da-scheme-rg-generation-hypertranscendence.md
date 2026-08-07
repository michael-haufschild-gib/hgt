# Diamond-Ising exact beta has no finite algebraic-differential scheme

- **ID:** `diamond-ising-da-scheme-rg-generation-hypertranscendence`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / EXACT PHYSICAL RG BRIDGE
- **Scientific status:** `[PROVED HERE] [PARENT-DERIVED MATHEMATICS]`
  `[PHYSICAL HIERARCHICAL ISING MODEL] [NOVELTY NEEDS AUDIT] [NOT YET QFT]`
- **Scope:** general hypertranscendence in an interacting physical renormalization problem; no
  Riemann-hypothesis or distinguished-special-function input
- **Statement:** At the nontrivial thermal fixed point of the zero-field Ising model on the
  two-branch, two-bond diamond hierarchical lattice, the exact local Callan--Symanzik beta field
  is hypertranscendental in the physical transmissivity and in every locally invertible
  differentially algebraic coupling scheme.  Linearization is possible, but every linearizing
  coupling coordinate is itself hypertranscendental.

## The exact physical map

Put a zero-field Ising spin `s_v in {+1,-1}` at every vertex and give each bond the weight

```text
exp(K s_v s_w),              t = tanh K.                         (1)
```

One diamond replacement puts two equal bonds in series on each of two parallel branches.
Summing the internal spin on one branch gives an effective series coupling `K_s` with

```text
tanh K_s = t^2.                                                   (2)
```

The two branches are in parallel, so their couplings add.  The tangent addition law therefore
gives the exact one-step renormalization map

```text
R(t) = tanh(2 K_s) = 2 t^2 / (1+t^4).                            (3)
```

This is an exact decimation identity, not a perturbative beta-function approximation.
Hierarchical-lattice RG as a rational map on finite-dimensional projective coupling space is
parent theory; equation `(3)` is also obtained directly from that construction in the Ising
invariant line.

In projective Boltzmann weights, if `z_s=A(1+t)` and `z_d=A(1-t)`, the exact two-branch map is

```text
Z_s=(z_s^2+z_d^2)^2,                 Z_d=(2z_s z_d)^2,
t'=(Z_s-Z_d)/(Z_s+Z_d)=2t^2/(1+t^4).                             (3a)
```

Consequently the four poles `t^4=-1` used below are zeros of the one-block normalization
`Z_s+Z_d`.  Their backward tree is the block-normalization/Fisher divisor tower of the exact
hierarchical recursion, not an auxiliary complex-dynamics decoration.

## The thermodynamic critical fixed point

Let

```text
g(t) = t^3+t^2+t-1.                                               (4)
```

Since `g'(t)=3t^2+2t+1>0` on the real line, while

```text
g(1/2)=-1/8,              g(2/3)=11/27,                           (5)
```

there is a unique `c in (1/2,2/3)` with `g(c)=0`.  The factorization

```text
t^4-2t+1 = (t-1)(t^3+t^2+t-1)                                   (6)
```

shows that `R(c)=c`.  Moreover

```text
R'(t) = 4t(1-t^4)/(1+t^4)^2,
lambda := R'(c) = 2(1-c)/c > 1.                                  (7)
```

Thus `c` is the repelling RG fixed point separating the high- and low-temperature basins on the
physical interval.  Here “critical” is thermodynamic terminology; `c` is not a critical point of
the rational map.

## Exact flow and beta constraint

Let `Phi` be the normalized Poincare function at `c` and let `kappa` be its local inverse:

```text
Phi(0)=c,        Phi'(0)=1,        R(Phi(z))=Phi(lambda z),
kappa(c)=0,      kappa'(c)=1,      kappa(R(t))=lambda kappa(t).    (8)
```

For real flow time `s` near zero, define

```text
F_s(t) = Phi(lambda^s kappa(t)).                                  (9)
```

This is a local one-parameter RG flow with `F_1=R`.  Its canonical beta field is

```text
beta(t) = (d/ds)|_(s=0) F_s(t)
        = (log lambda) kappa(t)/kappa'(t).                         (10)
```

Differentiating the Schroeder constraint in `(8)` gives the static Julia constraint

```text
beta(R(t)) = R'(t) beta(t).                                       (11)
```

Equations `(9)`--`(11)` are established parent RG functional-conjugation theory.  The new work
below is the exact differential-algebraic obstruction for this physical `R` and its scheme-level
interpretation.

## The Poincare function is hypertranscendental

Translate the fixed point to zero:

```text
S(y)=R(y+c)-c,                sigma(z)=Phi(z)-c.                   (12)
```

Then `S(0)=0`, `S'(0)=lambda`, and `S(sigma(z))=sigma(lambda z)`.  Suppose for contradiction
that `sigma` is differentially algebraic over `C(z)`.  The Di Vizio--Fernandes form of Ritt's
theorem then supplies integers `r != 0`, `j`, and a nonzero rational function `A` such that

```text
(sigma'(z))^r = z^j A(sigma(z)).                                  (13)
```

Differentiate the Poincare equation and use `(13)` at `z` and `lambda z`.  Cancellation on a
nonempty germ gives the rational identity

```text
lambda^(r+j) A(S(y)) = S'(y)^r A(y).                              (14)
```

With `B(t)=A(t-c)`, this is

```text
lambda^(r+j) B(R(t)) = R'(t)^r B(t).                              (15)
```

For a point `a` of the Riemann sphere, write `b_a=ord_a(B)`.  The local behavior of `(3)` and
`(7)` now forces an infinite divisor.

1. At the superattracting fixed point `0`, `R` has local degree two and `ord_0(R')=1`.
   Taking orders in `(15)` gives `2b_0=r+b_0`, hence

   ```text
   b_0=r.                                                         (16)
   ```

2. At infinity, `R(t)` tends to `0` with local degree two and `R'(t)` has order three.
   Therefore `2b_0=3r+b_infinity`, so

   ```text
   b_infinity=-r.                                                 (17)
   ```

3. Let `p` be any root of `p^4=-1`.  It is a simple pole of `R`, and `R'` has a double pole
   there.  Equation `(15)` gives

   ```text
   b_infinity=-2r+b_p,             hence b_p=r.                   (18)
   ```

The critical points of `R` are `0`, infinity, and the four roots of `t^4=1`; their critical
values are exactly `0,1,-1`.  The backward orbit of `p` cannot meet this set, because the forward
orbits of `0,1,-1` stay in `{0,1}` whereas `p` is a root of `-1` and is neither `0` nor `+/-1`.
Consequently every point in the backward orbit of `p` has four distinct noncritical preimages.
At every such preimage, taking orders in `(15)` preserves the value `r`.  Thus `B` has order
`r != 0` at infinitely many points, impossible for a rational function.

The contradiction proves

```text
Phi is hypertranscendental over C(z).                             (19)
```

This direct divisor proof also verifies, without relying on a portrait label, that the physical
map lies outside every differentially algebraic case in Ritt's classification.

## The beta field is hypertranscendental

Locally invertible differentially algebraic germs are closed under compositional inversion.
Hence `Phi` is DA if and only if `kappa` is DA.  Equation `(10)` gives one direction immediately:

```text
kappa DA  =>  beta DA.                                           (20)
```

Conversely, if `beta` were DA, then

```text
kappa' = ((log lambda)/beta) kappa                               (21)
```

would make `kappa` DA over the differential field generated by `beta`; transitivity of
differential algebraicity would make `kappa` DA over `C(t)`.  This contradicts `(19)`.  Therefore

```text
beta is hypertranscendental over C(t).                            (22)
```

Notice what has and has not been proved.  The analytic flow `(9)` exists.  Hypertranscendence
does not mean “there is no flow”; it means that the exact flow generator has no finite
algebraic-differential description in the physical coupling.

## Scheme theorem: the complexity cannot be removed by a finite-AD chart

Let `u=h(t)` be a locally invertible DA coupling change near `c`, and write

```text
R_h = h o R o h^(-1).                                             (23)
```

The transported beta field satisfies

```text
beta_h(h(t)) = h'(t) beta(t).                                     (24)
```

DA germs are closed under composition, differentiation, division, and local inversion.  Thus
`beta_h` is DA if and only if `beta` is DA.  Combining this with `(22)` proves:

```text
Every locally invertible DA renormalization scheme has an HT beta field.     (25)
```

The restriction to DA schemes is load-bearing.  The analytic change `u=kappa(t)` makes the flow
linear and gives `du/ds=(log lambda)u`; but `(19)` says that this trivializing coordinate is HT.
Therefore arbitrary analytic reparametrization can move the HT out of the beta field, but it can
do so only by putting the same non-finite differential complexity into the coupling chart.

This suggests the source-categorical physical invariant:

```text
RG-generation HT = no finite algebraic-differential coupling atlas
                   contains a finite algebraic-differential exact beta field.             (26)
```

## Discriminator and route selection

Four reporters were tested against the same requirement: source-natural, non-Gaussian or
interacting, exact, and stable under a stated admissible coordinate class.

| Reporter | Exact parent input | Result of the attack |
|---|---|---|
| p-adic fourth-cumulant boundary cocycle | rigorous non-Gaussian field and shell sum | still open: the shell seed is analytic but not proved DA |
| Poincare/Koenigs scaling coordinate | exact rational RG map | HT, but it is a coordinate rather than a local physical generator |
| canonical beta field | exact rational RG map plus flow normalization | survives; HT in every DA coupling chart |
| hierarchical free-energy cocycle | additive RG cohomology | deferred: local-counterterm quotient and relative base are not yet intrinsic |

There is also an exact negative control.  Pure parallel doubling has

```text
P(t)=2t/(1+t^2),      kappa_P(t)=arctanh(t),
beta_P(t)=(log 2)(1-t^2)arctanh(t),                              (27)
```

so its beta field is DA.  The diamond decimation inserts the series operation `t -> t^2` before
parallel doubling.  The discrete step remains rational, but its critical/pole orbit forces the
continuous generator from DA to HT.  Thus “nonlinearity” alone is not the mechanism; the
discriminator is the global divisor dynamics created by genuine internal-spin decimation.

The divisor has a direct statistical-field meaning.  The valuation contradiction `(16)`--`(18)`
says that a finite algebraic-differential invariant would have to carry the same nonzero order on
every pullback of a complex block-normalization zero.  The proliferating Fisher divisor makes that
impossible.  Complex zeros by themselves are not sufficient--power, Chebyshev, trigonometric, and
elliptic DA cases have highly structured infinite divisors--so the load-bearing fact is the
nonexceptional branching portrait of this divisor tower.

The family theorem
`diamond-ising-family-rg-generation-hypertranscendence.md` now extends this result from `b=2` to
every `b`-branch, two-bond diamond lattice with `b>=2`.

## Physical meaning and present boundary

The result is exact and interacting: it comes from summing physical Ising spins in a hierarchical
lattice, not from inserting a known HT special function into an observable.  It provides the
first clean example in this program where

```text
finite rational discrete RG rule
+ exact analytic continuous interpolation
+ no finite algebraic-differential beta description in any DA scheme.        (28)
```

It is not yet a continuum QFT theorem.  The diamond Ising model is a classical hierarchical
statistical field system.  The next QFT-level obligation is to reproduce the same Ritt-divisor
obstruction on a finite-dimensional invariant coupling slice of a rigorous non-Gaussian field RG,
or to prove that the infinite-dimensional p-adic fixed-point RG induces such a slice on a compact
source sector.

## Anti-theatre and dual gate

The component facts are parent theory:

- the diamond hierarchical Ising decimation and rational RG representation;
- Poincare/Koenigs linearization and exact beta functional equations;
- Ritt's classification and the Di Vizio--Fernandes Galoisian criterion.

The proved contribution is their exact assembly in a physical interacting RG map, the explicit
infinite-divisor obstruction `(16)`--`(18)`, and the DA-scheme invariant formulation `(25)`--`(26)`.
Targeted searches for “hierarchical Ising differential transcendence,” “diamond Ising Poincare
Ritt,” “diamond hierarchical Schroeder beta,” and the exact map together with “beta function” did
not locate this conjunction.  That is negative evidence only; the novelty gate remains open until
formula-level review of the complex-dynamics and hierarchical-RG literature.

The significance gate is partially cleared: `(26)` is a mathematically sharp candidate for a new
physical HT invariant and `(28)` is an exact nontrivial model.  A Fields- or Nobel-level claim is
not warranted without a continuum QFT realization, observable consequences, and a universality
theorem across an intrinsic class of admissible physical schemes.

## Lean boundary

The external Ritt theorem and analytic Poincare existence are not presently in the Lean corpus.
Formalization should therefore target only unconditional exact algebra that carries the physical
map: the rational-function identity `(3)`, its derivative identity `(7)`, and the fixed-point
factorization `(6)`.  A theorem assuming the missing Ritt or analytic inputs would be wrapper
theatre.

That exact core is now formalized in
`../../3-formalized/diamond-ising-exact-rg-algebra.md`, through module
`GaloisForLFunctions.HTGeometry.DiamondIsingRG`.  The full beta-field HT statement remains
paper-level until the external analytic and Ritt theory can be proved unconditionally in Lean.

## Primary sources

- J. De Simoi and S. Marmi, *Potts models on hierarchical lattices and Renormalization Group
  dynamics*, <https://arxiv.org/abs/0708.0616>.
- J. De Simoi, *Potts models on hierarchical lattices and Renormalization Group dynamics II:
  examples and numerical results*, <https://arxiv.org/abs/0711.4610>.
- T. L. Curtright and C. K. Zachos, *Renormalization Group Functional Equations*,
  <https://arxiv.org/abs/1010.5174>.
- L. Di Vizio and G. Fernandes, *A Galoisian proof of Ritt theorem on the differential
  transcendence of Poincare functions*, <https://arxiv.org/abs/2102.08268>.
- M. Aschenbrenner and W. Bergweiler, *Julia's equation and differential transcendence*,
  <https://arxiv.org/abs/1307.6381>.
- F. Pakovich, *On algebraic dependencies between Poincare functions*,
  <https://arxiv.org/abs/2106.05770>.

## Gates

- [x] 0 -> 1 in-progress: exact physical map, source-pure reporter, and hard failure modes stated.
- [x] 1 -> 2 fully-proven: exact paper proof of RG map, repelling fixed point, Ritt obstruction,
  beta HT, and DA-scheme invariance.
- [ ] Novelty audit: formula-level search of hierarchical Ising complex dynamics, invariant
  differentials, and exact-RG beta literature.
- [x] Unconditional rational-function core formalized in HTGeometry, with targeted build and axiom
  audit; the analytic beta-field HT theorem remains external.
- [ ] 3 -> 4 publication-ready: continuum-QFT realization and scheme-universality theorem.
