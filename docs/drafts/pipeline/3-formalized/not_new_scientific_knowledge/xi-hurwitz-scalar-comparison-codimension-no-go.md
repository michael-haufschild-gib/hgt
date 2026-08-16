# Xi--Hurwitz scalar comparison codimension no-go

- **ID:** `xi-hurwitz-scalar-comparison-codimension-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE LOCAL NO-GO
- **Scientific status:** `[PROVED ON PAPER] [PARENT LOCAL ANALYTIC GEOMETRY]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [SIGNIFICANT ROUTE CLASSIFICATION]`
- **Parent:**
  `../../3-formalized/not_new_scientific_knowledge/xi-source-circuit-fracture-rh.md`

## Theorem

Put

```text
q(s)=exp(-2 pi i s),
M(s)=q(1-s)-q(conj(s)).
```

Let `rho=1/2+i gamma` and let `A` be a nonzero holomorphic germ at `rho` with `A(rho)=0`.
There is no continuous complex-valued germ `h` at `rho` such that

```text
M(s)=h(s) A(s).                                           (1)
```

In particular, at every nontrivial critical-line Xi zero, take

```text
z_s=(s-1/2)(-i),
A(s)=4 z_s^2 XiC(z_s)
    =E(z_s)+E#(z_s).
```

Then no continuous scalar comparison carries the completed-density analytic defect to the
Hurwitz functional-equation--Schwarz seam, even locally and even if RH is assumed.

## Proof

Write `s=x+i y`.  Directly from the exponential definition,

```text
M(x+i y)=2 i exp(-2 pi y) sin(2 pi x).                    (2)
```

Hence `M` vanishes on the full critical line `x=1/2`, while its transverse derivative there is

```text
partial_x M(1/2+i y)=-4 pi i exp(-2 pi y) != 0.           (3)
```

Because `A` is a nonzero holomorphic germ, its zeros are isolated.  Choose points on the critical
line converging to `rho` at which `A` is nonzero.  Equation `(1)` and `M=0` force `h=0` at those
points, so continuity gives `h(rho)=0`.

Let `m>=1` be the order of the zero of `A` at `rho`.  Along the horizontal real parameter `t`,

```text
A(rho+t)=a t^m+o(t^m),       a!=0,
M(rho+t)=c t+o(t),           c!=0.                        (4)
```

If `m=1`, equation `(1)` forces `h(rho+t)` to tend to the nonzero number `c/a`.  If `m>1`, it
forces `|h(rho+t)|` to be unbounded.  Both contradict continuity and `h(rho)=0`.  This proves the
theorem.

For the Xi specialization, `z_rho` is nonzero at a nontrivial zero, the factor `4 z_s^2` is a
holomorphic unit there, and `XiC` is not identically zero.  Thus its analytic defect satisfies the
hypotheses. `QED`

## Meaning

The obstruction is geometric, not a missing formula:

```text
analytic Xi defect zero:  complex divisor, real codimension two;
Hurwitz seam zero:         real hypersurface, real codimension one.
```

A bounded line-to-line module map cannot reconcile these germs.  Any viable comparison must use
at least one of the following genuinely extra structures:

- an unbounded or distributional graph with a specified domain;
- a real conormal/Koszul resolution retaining the transverse direction;
- a nonlinear radical relation with multiplicity control;
- a higher-rank comparison in which the scalar matroid is only a shadow.

This does not prove that a rank-two construction exists.  It proves that unboundedness or
transverse resolution is load-bearing rather than decorative.

## Novelty gate

The proof uses only elementary local analytic geometry and the explicit exponential character.
No new-scientific-knowledge claim is justified.  Its significance is the exact elimination of the
scalar comparison category, including under RH; it prevents the source-fracture criterion from
being pursued through a quotient `M/A` disguised as a chain map.

## Gates

- [x] exact seam formula
- [x] first-order transverse vanishing
- [x] all analytic zero multiplicities treated
- [x] Xi completed-density specialization
- [x] positive replacement category identified
- [x] 2 -> 3 formalized: `RHTower/HurwitzScalarComparisonNoGo.lean`

## 2026-08-16 Lean closure

`RHTower/HurwitzScalarComparisonNoGo.lean` proves the card unconditionally.

`hurwitzQ s = exp(-2 pi i s)` and `hurwitzM s = q(1-s) - q(conj s)` are the card's `q` and `M`.

- `one_sub_eq_conj` and `hurwitzM_shift`: on the critical line `1 - rho = conj rho`, so
  `M(rho + w) = q(conj rho) (exp(2 pi i w) - exp(-2 pi i conj w))`.  This is the exact seam formula
  (2) in the form the proof uses, with no separate real/imaginary decomposition.
- `hurwitzM_vertical`: `M` vanishes identically along the critical line.
- `hurwitzM_horizontal` and `hasDerivAt_hurwitzM_horizontal`: along the real direction `M` is
  `q(conj rho)(exp(2 pi i t) - exp(-2 pi i t))` with slope `4 pi i q(conj rho) != 0` at the origin —
  the transverse derivative (3).
- `no_continuous_scalar_comparison`: for any nonzero holomorphic germ `A` with `A(rho) = 0` and any
  germ `h` continuous at `rho`, the factorization `M = h A` near `rho` is impossible.  The vertical
  direction forces `h(rho) = 0` (the isolated zeros of `A` come from
  `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`), and then the horizontal slope of `h A` is
  `0 * A'(rho) = 0`, contradicting the nonzero transverse slope.  Treating all zero orders at once
  through the slope removes the card's case split on the multiplicity `m`.
- `xiHurwitzGerm` is the completed-density germ `4 z_s^2 XiC(z_s)`, and
  `no_continuous_scalar_comparison_xi` is the Xi specialization at a critical-line zero.
  `xiHurwitzGerm_not_eventually_zero` supplies the nondegeneracy from `XiC_zero_ne` and the
  identity theorem.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
