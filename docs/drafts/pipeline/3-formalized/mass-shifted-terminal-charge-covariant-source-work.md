# Mass-shifted terminal-charge covariant source work

- **ID:** MS-TCCSW
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceWork.lean`
- **Novelty:** UNVERIFIED

## Statement `[PROVED HERE]` `[LEAN-PROVED]`

Let `H_k(y)` be canonical admission norm, `Phi_k(y)` its division-free odd-Gamma norm flux, and

`W_N(y) = H_N(y) Phi_(N+1)(y) - H_(N+1)(y) Phi_N(y)`.

Where the two solve determinants are admitted and `H_N(y) != 0`,

`d(H_(N+1)/H_N)/dy = W_N/H_N^2`.

In the physical positive chamber, literal adaptive mixed/completed terminal source charge in mass
coordinate is `T_N(y)=4(N+1)H_(N+1)(y)/H_N(y)`, hence

`T_N'(y)=4(N+1)W_N(y)/H_N(y)^2`.

At an occupied strict frontier `y=tau_(n+1)`, if newborn norm has first contact
`H_(n+2)(y+u)/u^d -> C_(n,d)>0`, then

`W_(n+1)(y+u)/u^(d-1) -> d H_(n+1)(y) C_(n,d)>0`

and literal source-charge derivative satisfies

`T_(n+1)'(y+u)/u^(d-1) -> 4(n+2)d C_(n,d)/H_(n+1)(y)>0`.

## Dependency-closed paper proof

1. Corpus raw-flow theorem gives `H_k'=Phi_k` from the admitted determinant at each degree.
2. Quotient rule gives the Wronskian law without a following positive extension.
3. Existing arithmetic accounting identifies literal terminal source charge with weighted adjacent
   norm ratio throughout each positive physical chamber.
4. Current head is analytic and nonzero at strict contact, so its effectivity has zero logarithmic
   residue: `u E_(n+1)(y+u)->0`.
5. Newborn integer holonomy gives `u E_(n+2)(y+u)->-d`; determinant contact gives
   `H_(n+2)(y+u)/u^d->C_(n,d)`.
6. On the positive right germ, derivative uniqueness rewrites both raw fluxes by effectivity.
   Factoring `W/u^(d-1)` produces
   `H_current * (H_new/u^d) * u(E_current-E_new)`, whose limit is `d H_current C`.
7. Divide only by the nonzero current head norm and multiply by `4(n+2)` to obtain the literal
   source-charge derivative residue.

No newborn charge is divided out. No next-frontier positivity, orientation map, reflection
aggregate, finite observer, fixed linear reporter, computation, representing measure, RH premise,
or added axiom occurs.

## Failed conjecture and positive salvage

The Fisher-payment conjecture `W_N^2/(H_N^2 H_(N+1)) <= C J_N` fails structurally. At simple
contact its left side is proportional to `1/u`, while current outgoing source capital stays finite.
The strongest survivor is exact order descent by division-free bilinear source work.

## Remaining wall

Local positive residue may shrink with degree and contact width. Current theorem supplies exact
producer and order descent, not a cofinal lower bound on integrated source-work pulse capital.
Needed next: source-native sum rule or rigidity law preventing cofinally many positive derivative
pulses from having summable total capital.

## Gates

- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Verification

- Direct `lake env lean` on module: PASS
- Umbrella wiring: DONE
- Targeted module build: PASS (`11835` jobs)
- Axiom audit: pending final audit
