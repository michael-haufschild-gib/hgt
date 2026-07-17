# Phase-holomorphic autonomous-ADE frequency rank

- **ID:** `phase-holomorphic-autonomous-ade-frequency-rank`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CROSS-OPERATOR TRANSDUCTION
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Novelty status:** no exact predecessor found in the targeted primary-source audit; do not claim
  novelty before independent expert proof and a broader literature review
- **Statement:** For a quasiperiodic function with a holomorphic phase observable, the rational
  frequency rank is at most its minimal autonomous algebraic-differential order. The equation may
  be implicit and singular.

## Setup

Let

```text
A_rho={z in (C*)^r: exp(-rho_j)<|z_j|<exp(rho_j) for every j}   (1)
```

be a polyannulus containing `T^r`. Let `omega_1,...,omega_r` be rationally independent real
numbers and let `F` be holomorphic on `A_rho`. On a sufficiently narrow horizontal strip put

```text
f(t)=F(exp(i omega_1 t),...,exp(i omega_r t)).                 (2)
```

Write the convergent Laurent expansion

```text
F(z)=sum_(m in Z^r) a_m z^m.                                  (3)
```

Let

```text
Lambda_F=span_Z {m:a_m!=0},
s=rank_Z Lambda_F.                                             (4)
```

Assume that `n` is the least order of a nonzero autonomous algebraic-differential equation for
`f`:

```text
P(f,f',...,f^(n))=0,   P in C[Y_0,...,Y_n].                   (5)
```

## The theorem

`[PAPER-PROVED]` Under `(1)`--`(5)`,

```text
rank_Q Gamma(f)=s<=n.                                         (6)
```

No equation solved for the highest derivative and no initial-value uniqueness are assumed.

## 1. Time differentiation is a torus derivation

Define

```text
delta=sum_(j=1)^r i omega_j z_j partial_(z_j),
F_k=delta^k F.                                                (7)
```

Then

```text
f^(k)(t)=F_k(exp(i omega t)).                                 (8)
```

Every polynomial identity among time jets extends to the whole polyannulus. Indeed, if

```text
P(f,...,f^(q))=0,                                            (9)
```

then `P(F_0,...,F_q)` vanishes on the dense real orbit in `T^r`, hence on the product torus. The
product torus is a uniqueness set for a polyannulus: hold `r-1` unit-circle variables fixed and
apply the one-variable identity theorem in the remaining annulus, then iterate through the
variables. Thus

```text
P(F_0,...,F_q)=0 on A_rho.                                  (10)
```

The converse follows by restriction to the orbit. Minimal autonomous order can therefore be read
from the phase functions `F_k`.

## 2. Minimal differential order is the all-jet transcendence degree

Put

```text
L=C(F_k:k>=0) subset M(A_rho).                               (11)
```

Minimality of `n` says that

```text
F_0,...,F_(n-1) are algebraically independent over C.        (12)
```

Choose an order-`n` relation of minimal positive degree in `Y_n`. Its separant does not vanish
identically:

```text
P_n(F_0,...,F_n)!=0,    P_n=partial P/partial Y_n.            (13)
```

Otherwise `P_n` would be a lower-degree order-`n` identity, contradicting the choice of `P`.
Applying `delta` to `(10)` gives

```text
sum_(j=0)^n P_j(F_0,...,F_n) F_(j+1)=0.                      (14)
```

Solving for the unique occurrence of `F_(n+1)` yields

```text
F_(n+1) in C(F_0,...,F_n).                                  (15)
```

The field on the right is now `delta`-stable: the derivative of each generator lies in it.
Induction puts every higher `F_k` in this field. Since `F_n` is algebraic over the independent
lower packet `(12)`,

```text
trdeg_C L=n.                                                 (16)
```

This is the algebraic transduction half of the theorem.

## 3. The all-jet fibre detects the active Laurent lattice

Define the multiplicative symmetry subgroup

```text
H={h in (C*)^r:h^m=1 for every m in Lambda_F}.               (17)
```

It is an algebraic subgroup of complex dimension `r-s`. Fix `x in T^r`. Suppose `y` is close to
`x` and

```text
F_k(y)=F_k(x) for every k>=0.                                (18)
```

The two holomorphic functions

```text
t |-> F(exp(i omega t)x),
t |-> F(exp(i omega t)y)                                    (19)
```

have identical Taylor series at zero. They agree on their common strip and hence for every real
`t`. Kronecker density gives

```text
F(ax)=F(ay) for every a in T^r.                              (20)
```

Put `h=y/x`. The holomorphic function `z |-> F(hz)-F(z)` on a smaller polyannulus vanishes on the
product torus, hence vanishes identically. Laurent uniqueness now gives

```text
a_m(h^m-1)=0 for every m,                                   (21)
```

so `h in H`. Conversely, `(17)` and `(3)` show that multiplication by every `h in H` fixes `F`
and all `F_k`. Therefore the common all-jet level-set germ at `x` is exactly

```text
xH,   of complex dimension r-s.                             (22)
```

## 4. Noetherianity turns the infinite observation into finite algebraic rank

In the local analytic ring at `x`, let

```text
I_x=(F_k-F_k(x):k>=0).                                      (23)
```

Noetherianity supplies finitely many indices `k_1,...,k_N` generating this ideal. Their common
level-set germ still has dimension `r-s` by `(22)`. The holomorphic fibre-dimension theorem then
shows that the map

```text
z |-> (F_(k_1)(z),...,F_(k_N)(z))                           (24)
```

has differential rank at least `s` at a nearby regular point. Some `s` coordinate functions in
`(24)` have independent differentials there. Their image contains a complex-open set, so those
`s` phase jets satisfy no nonzero polynomial relation. Hence

```text
trdeg_C L>=s.                                                (25)
```

Combining `(16)` and `(25)` gives `s<=n`.

Finally, rational independence of the `omega_j` makes

```text
m |-> m dot omega                                            (26)
```

injective on `Z^r`. The Bohr spectrum in `(2)` is exactly `{m dot omega:a_m!=0}`, so its generated
rational frequency rank is the lattice rank `s`. This completes `(6)`.

## Sharpness

Let `omega_1,...,omega_n` be rationally independent and `a_j!=0`. For

```text
F(z)=sum_(j=1)^n a_j z_j,
f(t)=sum_(j=1)^n a_j exp(i omega_j t),                       (27)
```

the active lattice has rank `n`, while

```text
prod_(j=1)^n (D-i omega_j) f=0                              (28)
```

has order `n`. The Vandermonde matrix recovers the `n` exponentials from the lower `n` jets, and
exponential-polynomial uniqueness makes those exponentials algebraically independent. No
lower-order autonomous equation exists. Equality is therefore attained in `(6)`.

## Hostile audit and surviving frontier

The theorem eliminates every standard transversely holomorphic quasiperiodic, toric, or pole-free
abelian-phase construction as a counterexample to the sharp frequency/order bound.

It does **not** silently promote time-strip holomorphy to phase holomorphy. If the rational basis is
Liouville, decay in `|m dot omega|` need not imply decay in `|m|`; a Bohr hull may be a protorus or
have only a transversely continuous observable. The surviving attacks are therefore:

1. a finite-rank protorus with non-finitely-generated character group;
2. a torus observable that is holomorphic along the dense time orbit but not transversely
   holomorphic;
3. a genuinely wild singular-chart hull.

No exact counterexample of these types was found.

## Hypertranscendence consequence

If a phase-holomorphic carrier has active lattice rank `s`, then every autonomous algebraic
differential equation has order at least `s`. In particular, no fixed order can annihilate a
sequence of such carriers whose active ranks tend to infinity. This is a quantitative
cross-operator transduction from Laurent support to differential complexity.

## Literature and novelty audit

1. G. C. O'Brien, *The frequencies of almost periodic solutions of almost periodic differential
   equations*, J. Austral. Math. Soc. **17** (1974), 332--344,
   <https://doi.org/10.1017/S1446788700017092>. O'Brien proves fewer than `p` frequencies for a
   regular autonomous system in `R^p`; this neither gives the complex half-dimensional bound nor
   handles singular implicit ADEs.

2. M. Abate, *Iteration theory, compactly divergent sequences and commuting holomorphic maps*,
   Ann. Scuola Norm. Sup. Pisa **18** (1991), 167--191,
   <https://www.numdam.org/item/ASNSP_1991_4_18_2_167_0.pdf>. Proposition 2.16 proves the adjacent
   toral-rank bound for relatively compact iterates on a taut Stein manifold by total reality. It
   does not state the Laurent-support/all-jet-stabilizer theorem above.

Targeted searches found no primary source for the exact statement `(6)`. Its proof is short and
uses standard ingredients, so the conservative status is `[NOVELTY UNVERIFIED]`, not a novelty
claim.

## Lean status

`[NOT LEAN-FORMALIZED]` The corpus already contains the unconditional separant step in
`formal/GaloisForLFunctions/HTGeometry/AutonomousSeparant.lean` and abstract differential-jet
fields in `formal/GaloisForLFunctions/HTGeometry/DifferentialIndependence.lean`. It does not yet
contain the analytic Laurent-symmetry fibre theorem, the local Noetherian finite-jet reduction, or
their exact assembly into `(6)`. A structure assuming `s<=n` or assuming the required finite jet
rank would be circular and is not counted as formalization.

No Lean build or numerical computation was used in this paper proof.

## Gates

- [x] exact theorem and hypotheses
- [x] singular implicit ADE allowed
- [x] dense-orbit identity extension proved
- [x] all-jet stabilizer identified
- [x] finite-jet reduction proved
- [x] equality family proved
- [x] transversely rough falsifier class isolated
- [x] targeted primary-source audit
- [ ] independent expert proof and broad novelty audit
- [ ] unconditional Lean formalization

## Log

- 2026-07-17 -- Proved during programme-2 sharp-frequency research. An initial overclaim of
  equality for every holomorphic phase was killed: holomorphic function fields may have
  transcendence degree greater than the phase dimension. The surviving theorem is the sharp and
  sufficient inequality `s<=n`; equality is retained only for the exponential-polynomial family.
