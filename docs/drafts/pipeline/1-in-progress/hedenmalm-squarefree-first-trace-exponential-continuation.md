# Hedenmalm squarefree first-trace exponential continuation

- **Label:** `P-G139`
- **Route:** P
- **Parents:** `P-G138`, `SquarefreeCarlemanLogExpansion`, `XiPrimeLogHigherValuationHalfPlane`
- **Stage:** 1-in-progress
- **Type:** theorem / current continuation / prime--Gamma source weld
- **Status:** `[PAPER-PROVED] [LEAN EXACT-LEAF GREEN] [UMBRELLA-WIRED] [NOT RH]`

## Universal-principle conjecture

P-G138 isolates complete divisor charge in first-trace anomaly, but its Euler-chamber description
`exp(P(s)-P(sigma))` and its strict-right divisor description remain two presentations.  Conjecture:
they are one canonical meromorphic continuation of the valuation-one prime trace.  Higher
valuations and Carleman determinant must cancel exactly, leaving no unidentified regular current.

Define

```text
E_1(s) = squarefreePartition(s) / D2(s).
```

On `Re(s)>1`, `E_1(s)=exp(P(s))`.  On `Re(s)>1/2`, away from pole and zeros, expected exact current
law is

```text
-dlog E_1(s)
  = infinitePrimeFlux(s) - xiPrimeLogHigherValuation(s).
```

Equivalently, Carleman current must satisfy throughout its full half-plane

```text
dlog D2(s)
  = 2 infinitePrimeFlux(2s) - xiPrimeLogHigherValuation(s).
```

## Heavy conjecture loop

### P-G139.A — higher-trace leakage

Test whether analytic continuation introduces an extra holomorphic current not visible in Euler
chamber.

**Falsifier target.**  Prove identity theorem forces exact Carleman/higher-valuation law on entire
connected half-plane `Re(s)>1/2`; no leakage survives.

**Result:** hidden-leakage conjecture falsified positively.  Identity theorem proves exact current
law throughout full connected Hilbert--Schmidt half-plane.

### P-G139.B — source anomaly is normalized `E_1` transport

Prove for every affine chart

```text
squarefreeFirstTraceAnomaly(sigma,epsilon,u)
  = E_1(sigma+u epsilon) / E_1(sigma).
```

This must be algebraic and valid before any zero-free assumption.

**Result:** proved for every affine chart, including zero base under Lean's totalized division.

### P-G139.C — exact continued current and residue

Away from zeros and pole, prove `-dlog E_1` equals existing meromorphic valuation-one continuation.
At every strict-right zeta zero of multiplicity `m`, prove punctured current residue is `-m`, while
P-G138 Fisher residue remains `2m`.

**Result:** proved.  Continued current is exactly `-dlog E_1` away from divisor and pole, and has
punctured residue `-m` at every strict-right zeta zero.

### P-G139.D — completed prime--Gamma decomposition

Prove exact source decomposition

```text
completedPrimeGammaFlux
  = (-dlog E_1) + xiPrimeLogHigherValuation - dlog archFactor.
```

Thus Route P anomaly and anti-Herglotz gate have same singular current; remaining obstruction is a
sign/passivity theorem, not an unidentified analytic-continuation term.

**Result:** proved coefficient-exactly.  Module also proves completed flux oddness under
functional-equation reflection and that right-source dissipativity of this exact decomposition
implies RH via existing left-half accretivity gate.

## Proved outcome

`HedenmalmSquarefreeFirstTraceExponentialContinuation.lean` proves

```text
E_1(s) = squarefreePartition(s)/D2(s),
E_1(s)=exp(P(s))                         on Re(s)>1,
dlog D2(s)=2 A(2s)-H_{≥2}(s)             on Re(s)>1/2,
-dlog E_1(s)=A(s)-H_{≥2}(s)              off divisor and pole,
completedPrimeGammaFlux
  = (A-H_{≥2}) + H_{≥2} - dlog archFactor.
```

Here `A` is infinite von Mangoldt flux and `H_{≥2}` is absolutely convergent higher-valuation
current.  Thus Carleman regularization and all higher prime valuations cancel exactly: entire
singular completed source is valuation-one first trace plus explicit Gamma correction.  Route P's
charge theorem and prime--Gamma passivity gate are two faces of one source current.

## Non-theatre gate

Card succeeds only if half-plane Carleman current identity, normalized anomaly identity, continued
logarithmic current, zero residue, and completed prime--Gamma decomposition are all exact in Lean.
An Euler-chamber restatement or transitive charge renaming does not count.

## Gates

- [x] 0 → 1: exact continuation conjecture and falsifier fixed
- [x] 1 → 2: full paper proof; hidden leakage falsified with exact positive survivor
- [x] 2 → 3: Lean direct-check, exact leaf build, forbidden-declaration scan, axiom audit, umbrella wiring
- [ ] 3 → 4: publication-ready extraction

## Honest boundary

Even exact current identification does not prove RH.  It removes possibility that Route P is stuck
because of a hidden regular continuation term.  After closure, sole live gate is unconditional
right-source passivity (equivalently reflected completed prime--Gamma accretivity) strong enough to
exclude positive first-trace residues.

## Log

- 2026-08-13 — opened after P-G138 localization and audit of existing prime-first-trace closure and
  completed prime--Gamma corpus.  Ordinary graph closure is already terminalized; exact analytic
  current weld is first surviving connector.
- 2026-08-13 — direct Lean check green.  Exact continuation/current weld proved; source
  right-dissipativity is now a sufficient RH producer stated before divisor extraction.
- 2026-08-13 — exact module build passes `12395/12395`; headline axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`; targeted forbidden-declaration scan is clean.
  Whole-corpus lint is currently red only on unrelated concurrently added modules missing umbrella
  imports; both P-G138 and P-G139 are reachable from `RHTower.lean`.
