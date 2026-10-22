# Hedenmalm--Sonin Weyl-defect quantization wall

- **Label:** `P-G136`
- **Route:** P
- **Parents:** `P-G135`, `XiReflectionSelfIntersectionCharge`, `HedenmalmThetaContinuousPrincipalRenormalizationNoGo`
- **Stage:** 1-in-progress
- **Type:** theorem (Lean) / quantitative no-go / singular positive survivor
- **Status:** `[PAPER-PROVED] [LEAN DIRECT GREEN] [NOT RH]`

## Conjecture tested

P-G135 identifies the source-fixed Weyl reciprocity defect

```text
D(a)=exp(-4 |a| (log p + log q)(n+1)).
```

Test whether a uniform near-unit lower bound on products of these raw defects can force the
strict two-unit Xi reflection-charge endpoint and hence RH.

## Heavy conjecture loop

### P-G136.A — raw cofinal Weyl defect controls divisor incidence

For a packet of `M` reflected incidences, use `D(a)^M` as a source budget.  Required result would
separate every positive integer `M` from zero by a packet-independent gap below one.

**Falsified.** For every `M>0` and every `epsilon>0`, Lean exhibits `a != 0` with

```text
1-epsilon < D(a)^M < 1.
```

Thus arbitrarily large discrete incidence is invisible to raw continuous defect when horizontal
displacement approaches the wall. No raw near-unit estimate can imply a strict two-unit charge
bound without an independent horizontal gap.

### P-G136.B — logarithmic tropicalization recovers the lost integer

Away from `a=0`, test the normalized negative logarithm

```text
V_M(a) = -log(D(a)^M) /
  (4 |a| (log p + log q)(n+1)).
```

**Proved.** Exact value is `M` away from wall. Completing it by zero at wall is discontinuous for
every `M>0`. Specializing to one tropical unit at every Xi support point, weighting by squared
analytic multiplicity, and summing over finite strip windows gives exactly

```text
xiWeylTropicalReflectionCharge(T,p,q,n)
  = xiReflectionSelfIntersectionCharge(T).
```

Identity is independent of retained prime pair and valuation depth: those continuous source scales
cancel only after singular division by horizontal displacement.

## Non-theatre gate

This card succeeds only if it proves both:

1. an arbitrary-charge near-unit counterexample excluding every raw-defect threshold strategy;
2. a coefficient-exact identity with the existing Xi reflection charge, exposing precisely which
   singular operation restores quantization.

A renamed `D(a)=1 iff a=0` theorem or another RH equivalence does not count.

## Gates

- [x] 0 → 1: source-pure question and falsifier fixed
- [x] 1 → 2: paper proof and no-go closure
- [ ] 2 → 3: Lean module, exact build, lint, axiom audit, umbrella wiring
- [ ] 3 → 4: publication-ready extraction

## No-go closure

- **Exact killing theorem/mechanism:** `D(a)^M -> 1` as `a -> 0` for every fixed positive integer
  `M`; more strongly, every punctured neighborhood contains strict off-wall defects in
  `(1-epsilon,1)`. Raw continuous defect has no positive charge quantum.
- **Strongest positive survivor:** normalized negative logarithm divided by exact horizontal source
  scale equals `M`; its Xi multiplicity-weighted window sum is exactly canonical reflection
  self-intersection charge.
- **New insight:** Route P's continuous Cartan/Weyl geometry and discrete collision endpoint are
  separated by a genuine quantization wall. Erasing distance requires a discontinuous operation at
  critical wall. A viable producer must generate this singularity intrinsically—e.g. a
  logarithmic residue/order current—or prove an independent zero-free horizontal gap. Continuous
  norm, Hodge, Green, or raw-defect budgets cannot do it.
- **Status:** paper proof dependency-closed; direct Lean check, exact leaf build, standard-axiom
  audit, and umbrella wiring green. Lint and final umbrella build pending.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/HedenmalmSoninWeylDefectQuantizationWall.lean`

Headline declarations:

- `exists_deningerCalderonWittGammaWeylPacketDefect_between`;
- `deningerCalderonWittGammaWeylTropicalPacketCharge_eq`;
- `not_continuousAt_deningerCalderonWittGammaWeylTropicalPacketCharge`;
- `xiWeylTropicalReflectionCharge_eq`.

## Honest boundary

P-G136 does not prove RH. It proves raw Weyl defects cannot control discrete charge and identifies
the exact singular tropicalization that recovers it. Current formula weights by known Xi analytic
order; source-derived creation of that singular order detector remains open.

## Log

- 2026-08-13 — opened after P-G135 collapsed singular Green and Sonin scalarization to one
  continuous Weyl defect; discrete reflection charge selected as next independent endpoint.
- 2026-08-13 — P-G136.A falsified for arbitrary positive packet charge; P-G136.B paper-proved and
  formalized. Direct `lake env lean` check green.
- 2026-08-13 — exact leaf build passed (`12969/12969`); headline declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import wired. Lint invocation exited 143 without
  diagnostics and remains pending final audit.
