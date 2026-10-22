# CCM meromorphic-cusp Laurent charge law

- **ID:** CCM-C38
- **Stage:** 3-formalized/needs-audit
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [CORPUS-NOVEL SCOPE EXTENSION]`
  `[ARBITRARY NORMED TARGET] [ALL FINITE LAURENT SINGULARITIES CLOSED]`
  `[NO BOUNDEDNESS] [NO COMPLETENESS] [NO EVENTUAL-HOLOMORPHY PREMISE]`
  `[CLASSICAL LOCAL CORE] [EXTERNAL NOVELTY OPEN] [NOT RH] [NOT WHOLE-CCM DEATH]`
- **Source:** `docs/handover/connes.md` §§77--79; C36--C38
- **Statement:** Positive finite first-order thermal density fixes the full meromorphic Laurent
  charge by `2 q n = 1`. Therefore a periodic meromorphic logarithmic cusp has period
  `h = 4π n`, and no `2π`-periodic meromorphic cusp can realize any positive finite density,
  including CCM's four-unit normalization.

## Goal

Decide the unbounded finite-order cusp survivor explicitly left by C37. Remove boundedness,
completeness, holomorphy at the cusp, finite-dimensionality, and finite-rank assumptions. Cover
every pole, removable germ, and finite Laurent principal part in one theorem.

## Exact universal theorem

Let `E` be any complex normed space, `q>0`, and `F : C -> E` be meromorphic at zero. Define

```text
Delta_(q,F)(t)
  = ||F(exp(-q t))||^2/(1-exp(-exp(-t))).                (C38.1)
```

If `Delta_(q,F)(t)->ell` for any finite `ell>0`, then there is an integer `n` such that

```text
ord_0^mero(F)=n,   n>0,   2 q n=1.                      (C38.2)
```

The theorem does not assume that the meromorphic order is finite or that `F` is nonzero.
Positive density excludes the locally-zero order `top` and then fixes the unique finite Laurent
charge. In particular `(C38.2)` excludes all poles (`n<0`) and all nonvanishing removable germs
(`n=0`) automatically.

For `h>0`, let `f : C -> E` be `h`-periodic and let `F_h` be its descended cusp germ under

```text
q_h(z)=exp(2π i z/h).                                   (C38.3)
```

No boundedness, completeness, or eventual-holomorphy condition on `f` is imposed. If only `F_h`
is meromorphic at zero and the central-ray density

```text
Lambda_f(t)=||f(it)||^2/(1-exp(-exp(-t)))               (C38.4)
```

tends to `ell>0`, then

```text
ord_0^mero(F_h)=n>0,   h=4π n.                          (C38.5)
```

Thus `h=2π` would force `1=2n` in the integers, impossible. This includes the exact CCM
specialization `ell=4`.

## Proof `[PROVED HERE]`

Every finite meromorphic germ has the punctured Laurent normal form

```text
F(z)=z^n G(z),   n in Z,   G analytic at 0,   G(0) != 0. (C38.6)
```

Along `z=exp(-q t)`, the norm factorization is exact:

```text
||F(exp(-q t))||
  = exp(-q n t) ||G(exp(-q t))||,                       (C38.7)
```

and the last norm tends to `||G(0)||>0`. The thermal denominator obeys

```text
exp(-t)/(1-exp(-exp(-t))) -> 1.                         (C38.8)
```

Consequently `(C38.1)` factors as

```text
Delta_(q,F)(t)
  = exp((1-2 q n)t) U(t),   U(t)->||G(0)||^2>0.         (C38.9)
```

A product in `(C38.9)` can tend to a finite positive value only when its exponential rate is
zero, proving `2 q n=1` and hence `n>0`. If the order were `top`, `F` would vanish on a punctured
neighborhood, making `(C38.1)` eventually zero and contradicting `ell>0`.

For the cusp connector, periodicity and the exact identity

```text
q_h(it)=exp(-(2π/h)t)                                  (C38.10)
```

identify `(C38.4)` with `(C38.1)` at `q=2π/h`. Substitution into `(C38.2)` gives `(C38.5)`.
All steps are formalized for arbitrary complex normed `E`.

## No-go closure and surviving frontier

C38 closes every fixed `2π`-periodic logarithmic cusp whose descended boundary germ is
meromorphic, including unbounded cusps with arbitrary finite pole order. Do not retry a finite
Laurent principal part, meromorphic operator-valued cusp, or finite-order singularity as the CCM
four-unit transport.

The positive survivor is an exact category boundary:

```text
positive four-unit one-loop transport
  ==> descended cusp is not meromorphic at zero.        (C38.11)
```

Hence a surviving cusp must have an essential/nonmeromorphic singularity, vary cofinally with
aperture so no fixed germ exists, carry non-scalar monodromy, or live only as a closed graph
relation invisible to ambient norm.

C38 is not RH and does not kill whole CCM. Exact unresolved theorem remains

```text
D_Xi = closure(P_- M_(-2 Xi'/Xi)),
limsup_(u->0+) ||Q_u D_Xi||_(S2,ext)^2 /
                (4(1-exp(-u))) <= 1,                   (C38.12)
```

equivalently source-normalized Evans nonvanishing. The next research attack must derive
`(C38.12)` from source-rigged Plücker/Tate capacity geometry or prove that every remaining
essential/graph-singular transport fails. Another finite Laurent cusp is a closed route.

Laurent normal form and exponential-rate comparison are classical ingredients. Corpus search
found C37's bounded analytic result and the scalar square-root meromorphic obstruction, but no
arbitrary-normed-target all-Laurent charge law or exact CCM cusp connector. External literature
novelty remains open and must not be advertised as settled.

## Formal declarations

Module `formal/GaloisForLFunctions/RHTower/CCM/CCMMeromorphicCuspBoundaryNoGo.lean`:

- `tendsto_ofReal_exp_neg_mul_nhdsNE_zero`;
- `normedAnalyticShiftMultiplier_eventually_factor_zpow`;
- `meromorphicOrderAt_ne_top_of_analyticRamifiedBoundaryDensity_pos`;
- `meromorphic_boundaryDensity_chargeLaw`;
- `meromorphic_logarithmicCusp_period_chargeLaw`;
- `not_tendsto_meromorphic_logarithmicCuspBoundaryDensity_pos_of_two_pi_periodic`;
- `ccmFourUnit_not_two_pi_periodic_meromorphic_logarithmicCuspBoundary`.

## Gates

- [x] prior-research search across `HTGeometry`, `RHTower`, `HilbertMetric`, formalized cards,
  paper cards, and failed routes
- [x] dependency-closed paper proof
- [x] direct Lean check for pure theorem and CCM connector
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint attribution audit: no C38 finding; repository-wide lint fails only on
  pre-existing umbrella-reachability findings in other dirty-tree modules
- [x] targeted final module build:
  `GaloisForLFunctions.RHTower.CCM.CCMMeromorphicCuspBoundaryNoGo`
- [ ] external novelty audit
- [ ] RH or whole-lane no-go

## Log

- 2026-07-23 — Proved vector-valued meromorphic charge-rate law, all-Laurent periodic-cusp
  quantization, `2π` exclusion, and exact CCM four-unit connector.
