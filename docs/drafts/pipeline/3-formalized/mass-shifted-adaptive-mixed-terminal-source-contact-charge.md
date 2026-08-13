# Mass-shifted adaptive mixed terminal source contact charge

- **ID:** mass-shifted-adaptive-mixed-terminal-source-contact-charge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4) / exact arithmetic source law / phase classification
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3,
  (9.3.826)--(9.3.828)
- **Statement:** Literal top adaptive mixed/completed `P^sharp` source aggregate splits into
  lower-degree connector capital, retained reserve, and one terminal newborn charge. In every
  positive right chamber this terminal charge is exactly weighted newborn admission norm ratio;
  every strict frontier lands in it with exact finite positive contact-order residue.

## Goal

Locate strict-frontier contact inside actual admission-sensitive arithmetic source aggregate,
without orientation map, fixed reporter, reflection aggregation, or quotient-wall singularity.

## Gates

- [x] 0 → 1 in-progress: conjecture C8 one-extra-block failure and terminal-channel survivor
- [x] 1 → 2 fully-proven: exact algebraic split, shallow norm-ratio identification, contact limit
- [x] 2 → 3 formalized: direct Lean, targeted module build, umbrella wiring, standard-axiom audit
- [ ] 3 → 4 publication-ready: external novelty audit remains

## Conjecture loop

1. **C8 — top source directly pays newborn logarithmic collapse. `FAILED`.** Degree `n+2`
   effectivity/source coercivity asks for positive `H_(n+4)`, while right germ of strict frontier
   `tau_(n+1)` supplies only positive `H_(n+3)`. This is exact admission/effectivity restriction,
   not observer loss.
2. **C9 — contact hides arbitrarily somewhere in all-degree reserve. `FALSIFIED`.** Split final
   `beta_(N+1)` from reserve and define residual channel from literal source action. Exact source
   accounting identifies that channel uniquely.
3. **C10 — leading norm-ratio identification also needs future positive extension. `FALSIFIED`.**
   Actual inverse-Hankel admission equals monic orthogonal admission using only leading solve block.
   Hence newborn edge is exact at singular frontier with no positive following extension.
4. **C11 — false-RH contacts might escape this channel at higher contact order. `FALSIFIED`.**
   Arbitrary first order `d` gives exact positive scaled terminal-charge residue; false RH forces
   these charges cofinally.

## Exact law

For top source action `J_N`, connector energy `E_N`, and retained reserve

```text
R_N^ret = R_N - 4(N+1) beta_(N+1),
T_N = 2 J_N - E_N - R_N^ret,
```

the accounting identity `2 J_N = E_N + R_N^ret + T_N` is unconditional. In every positive
source chamber,

```text
T_N = 4(N+1) beta_(N+1)
    = 4(N+1) h_(N+1) / h_N.
```

Let `y=tau_(n+1)`, and suppose newborn norm has first contact order `d` with coefficient `C>0`:

```text
h_(n+2)(y+u) / u^d -> C.
```

Since `h_(n+1)(y)>0`,

```text
T_(n+1)(sqrt(y+u)) / u^d -> 4(n+2) C / h_(n+1)(y) > 0.
```

Thus contact cannot hide in retained reserve or disappear under finite observation. It is exactly
newborn arithmetic source capital, formed before reflection.

## No-go closure

- **Exact killing mechanism:** terminal charge vanishes at contact rather than consuming fixed
  positive capital. To turn cofinally many contacts into contradiction, one needs normalized
  logarithmic terminal-charge work or uniform pulse capital.
- **Admission wall:** existing degree-`n+2` source-effectivity coercivity needs one block beyond
  strict-right admission. Reusing it would assume next frontier already passed.
- **Strongest positive survivor:** exact terminal channel, shallow edge identity, arbitrary-order
  positive residue, and cofinal false-RH phase equivalence.
- **Remaining theorem:** source-paid normalized terminal-charge action under `H_(n+3)` only, or a
  degree-proper lower bound on terminal-charge pulse capital. Fixed linear reporting remains
  irrelevant.

## Lean artifact

`formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedSourceTerminalContactCharge.lean`

Direct check and targeted module build pass. Axiom audit of decomposition, shallow edge, contact
limit, positivity, strict-frontier law, cofinal phase, and RH phase equivalence reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean`.

## Log

- 2026-08-13 — C8 failed at exact one-extra-block admission wall; C9--C11 survived, formalized,
  audited, and promoted to Stage 3.
