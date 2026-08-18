# Source-horizontal Euler--Wold indefinite endpoint-annihilation firewall

- **ID:** `P-G210-IEA`
- **Stage:** 3-formalized
- **Type:** `[LEAN-PROVED] [NO-GO CLASSIFICATION] [POSITIVE SURVIVOR]`
- **Route:** Frankenstein P + Euler--Wold BV/Krein + bilateral prime-angle sewing
- **Statement:** Classify whether a source-budgeted order-indefinite block can cancel literal
  endpoint excess before scalar domination without destroying coefficient-faithful bilateral Xi
  admission.

## Goal

Previous module constructs a transverse reporter `T_N` with `0<T_N<P(c)` cofinally, while literal
endpoint response `R_N` satisfies `P(c)<R_N` cofinally.  Linear domination is therefore impossible.
This card tests remaining possibility: retain `R_N` as positive corner, cancel excess by negative
source leg before scalarization, then ask whether cancellation survives physical Xi admission.

## Frozen conjecture loop

### C0 -- unique signed counterleg

Put

```text
K_N = T_N - R_N,
S_N = diag(R_N,K_N).
```

Predictions:

1. `tr S_N=T_N` exactly;
2. among diagonal blocks with first corner `R_N` and trace `T_N`, second corner is uniquely `K_N`;
3. for every nonzero conormal, cofinally `R_N>0` and `K_N<0`, so cancellation is genuinely
   order-indefinite rather than disguised positive domination.

### C1 -- physical Krein rotation

Apply fundamental symmetry `J=diag(1,-1)`.  Prediction: C0 cancellation is not physical-order
stable:

```text
tr(J S_N)=2 R_N-T_N>P(c)
```

cofinally.  Thus `J` converts the negative counterleg to positive excess and amplifies, rather than
solves, primitive-budget overspend.

### C2 -- bilateral Hardy--Stokes reinterpretation

Scale both Hardy orientations for `lambda_p(rho)` by nonzero endpoint energy.  Predictions:

1. scaled sewing defects cancel identically before scalarization;
2. nonzero scalar multiplication preserves and reflects bilateral moderation;
3. both scaled orientations are moderate iff `Re rho=1/2`;
4. consequently every retained strict-right Xi copy has exact signed cancellation but cannot be
   admitted to the coefficient-faithful bilateral source topology.

## Hostile audit

- C0 is not an RH proof unless cancellation survives a physical source topology/order.  Trace zero
  or bounded trace alone is blind to positive corner.
- C1 explicitly tests this missing compatibility rather than assuming it.
- C2 forbids claiming that a scalar endpoint counterterm repairs off-line exponential Fourier
  growth: any nonzero scalar leaves moderation unchanged.
- Connes--Consani archimedean Sonin positivity and Connes--Consani--Moscovici semilocal stability
  provide compressed positive spaces, not this coefficient-faithful finite endpoint counterleg or
  a theorem placing both off-unitary Hardy halves in one moderate source topology.  Connes--Consani--
  Marcolli identify global trace-pairing positivity as RH-equivalent.  Therefore an unconditional
  physical positive descent cannot be imported from those results.

## Proof plan

1. Prove generic scalar-multiplication and sewing covariance lemmas for `bilateralModerate` and
   `bilateralSewing`.
2. Construct signed endpoint block and prove exact trace, uniqueness, eventual inertia, and
   physical-rotation overspend.
3. Attach literal endpoint scale to both Hardy halves.  Prove exact cancellation and sharp
   moderation criterion.
4. Specialize to actual Gamma--Julia Xi conormal coefficient and retain support-copy fidelity.
5. Formalize exact positive survivor/no-go; wire leaf into `RHTower.lean` without umbrella build.

## No-go closure

- **Exact killing mechanism:** The unique diagonal counterleg is `K_N=T_N-R_N`.  It is cofinally
  negative.  Fundamental-symmetry rotation changes signed trace `T_N` into `2R_N-T_N`, which
  cofinally exceeds primitive budget.  In prime-angle source topology, nonzero endpoint scaling
  preserves bilateral moderation exactly, so exact cancellation cannot admit an off-line Xi copy.
- **Strongest positive survivor:** Exact order-indefinite annihilation exists before scalarization:
  `tr diag(R_N,T_N-R_N)=T_N`, and endpoint-scaled Hardy--Stokes boundary defects cancel identically.
  Construction retains actual Gamma--Julia coefficient, both reflection orientations, and analytic
  multiplicity.
- **New insight:** Obstruction is not lack of signed cancellation.  It is incompatibility between
  signed cancellation and physical source admission.  Any further scalar/Krein endpoint correction
  is dead: next producer must alter bilateral source topology non-scalarly while retaining both
  orientations, or prove an independent full-source admission theorem.
- **Status:** Dependency-closed paper proof and unconditional Lean proof complete.

## Gates

- [x] 0 -> 1 in-progress: source-pure target, frozen conjectures, hostile audit
- [x] 1 -> 2 fully-proven: complete dependency-closed paper proof
- [x] 2 -> 3 formalized: exact Lean leaf green and axiom-audited
- [ ] 3 -> 4 publication-ready

## Log

- 2026-08-18 -- C0--C2 frozen after scalar reporter firewall; formal attack started.
- 2026-08-18 -- C0 proved: unique signed counterleg and eventual inertia.
- 2026-08-18 -- C1 falsified: physical `J`-rotation yields `2R-T` and strict overspend.
- 2026-08-18 -- C2 proved sharply: scaled sewing cancellation is exact, but both orientations are
  moderate iff divisor is critical; every actual strict-right Xi copy fails admission.

## Paper proof

Write `P=P(c)` for primitive source budget, `R_N` for literal endpoint response, and `T_N` for
transverse reporter.  Existing formal results give, for `c != 0`, cofinally

```text
0 < T_N < P < R_N.                                      (1)
```

If a diagonal block has first corner `R_N` and trace `T_N`, elementary cancellation forces its
second corner to be

```text
K_N = T_N-R_N.                                          (2)
```

Thus `K_N<0` by (1), and `S_N=diag(R_N,K_N)` is genuinely indefinite.  Equation (2) gives exact
signed annihilation `tr S_N=T_N`, so C0 succeeds and is unique within the literal diagonal
coefficient-faithful class.

Let `J=diag(1,-1)`.  Then

```text
tr(J S_N)=R_N-K_N=2R_N-T_N.
```

By (1), `2R_N-T_N>R_N>P`.  Hence positive physical rotation necessarily restores and amplifies
endpoint excess.  C1 is false, and signed trace cannot be advertised as physical domination.

For the bilateral test, put `g_N=8|c|^2 E_N`, with positive endpoint jet `E_N`, and
`lambda=lambda_p(rho)`.  Bilateral sewing is linear, so

```text
D_lambda(g_N h_+) + D_lambda(g_N h_-)
= g_N (D_lambda h_+ + D_lambda h_-)=0.                  (3)
```

When `c != 0` and `E_N>0`, `g_N != 0`.  Multiplication by a nonzero scalar preserves and reflects
polynomial two-sided growth.  Existing sharp Hardy sewing law therefore gives

```text
g_N h_+ and g_N h_- are both moderate
iff h_+ and h_- are both moderate
iff |lambda_p(rho)|=1
iff Re rho=1/2.                                         (4)
```

Every `XiRightZeroCopy` has `Re rho>1/2`, so (3) holds while (4) fails.  Actual Gamma--Julia
coefficient is constant across a support fibre; hence each scaled orientation is copy-independent
and summing it restores `xiSupportMultiplicity` exactly.  This proves C2 and the capstone.  No RH
premise, zeta nonvanishing premise, computation, or fitted divisor scalar is used. ∎

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldIndefiniteEndpointAnnihilation.lean`
- Capstone: `sourceHorizontalActualXiIndefiniteEndpointAnnihilation_capstone`.
- Unique counterleg: `sourceHorizontalEulerWoldEndpointCounterleg_unique`.
- Physical firewall:
  `eventually_sourceBudget_lt_sourceHorizontalEulerWoldPhysicalEndpointBlock_trace`.
- Bilateral selector:
  `sourceHorizontalEndpointScaledHardy_both_moderate_iff_re_eq_half`.
- Direct `lake env lean`: PASS.
- Exact leaf build: PASS (`13564/13564`).  Umbrella import wired; umbrella not built.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint: target clean and reachable; global lint reports only unrelated concurrently unwired
  modules.

## Verdict

`[LEAN-PROVED]`.  Remaining problem is classified, not converted into RH: nonlinear signed
endpoint-excess annihilation is available and multiplicity-faithful, but cannot survive ordinary
physical `J`-rotation or coefficient-faithful bilateral source admission off the critical line.
Therefore scalar/Krein endpoint-correction branch is retired.  Next admissible producer must be a
non-scalar source-topology descent admitting both Hardy orientations simultaneously; by (4), that
producer itself forces criticality.
