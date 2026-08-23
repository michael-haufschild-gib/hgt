# FCRJ corrected-response saturation law

- **ID:** `fcrj-corrected-response-saturation-law`
- **Stage:** `3-formalized`
- **Type:** `THEOREM (paper) [POSITIVE SURVIVOR] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` `(AC18)`--`(AC25)` and
  `high-grade-sieve-survivor-one-mode-reduction.md` `(HGS23)`--`(HGS29)`
- **Statement:** After the physical-cutoff gauge is joined, the corrected global response never
  exceeds the density baseline; its exact saturation deficit is the squared ordinary-prime
  aperture carrier.  Consequently the negative half of `AC25` is unconditional and only the
  reverse response inequality remains at RH strength.

## Goal

Close the false signed-Jordan/correlation formulation with a positive invariant theorem, and
state the surviving analytic frontier with the correct orientation.  This theorem does not prove
the required small upper bound; it proves that one side of the formerly absolute target is already
forced by Hilbert positivity.

## Exact setup

Write the density baseline and complete joined response in `(AC25)` as

```text
D_M=sum_h J_h S_z(h),

R_M=sum_(h,p,a) mu(a) nu_h(pa)/(pa)
      E_(r~w_(N_p,h))[mu(r) B_(pa,r,h)],

F_M=D_M-R_M.
```

Let

```text
E_M=E_(prog,M)+E_(quad,M),
P_M=X_M+Y_M.
```

Here `X_M,Y_M` are the low/high Hilbert amplitudes in `(HGS26)`.  The exact cutoff join
`(HGS23)`--`(HGS29)` gives

```text
F_M=||P_M||^2-E_M.                                      (RS1)
```

In the square-root support range, `P_M` is the ordinary-prime endpoint carrier.

## Theorem `[PROVED HERE]`

Define the quadrature-corrected response

```text
R_M^sharp=R_M-E_M.
```

Then

```text
D_M-R_M^sharp=D_M-R_M+E_M=||P_M||^2>=0,                 (RS2)

R_M^sharp<=D_M,                                         (RS3)

R_M^sharp=D_M  iff  P_M=0.                              (RS4)
```

Equivalently,

```text
R_M<=D_M+E_M,                                           (RS5)

R_M=D_M+E_M  iff  P_M=0.                                (RS6)
```

### Proof

Substitute `(RS1)` into the left side of `(RS2)`.  This gives `||P_M||^2` identically.
Nonnegativity gives `(RS3)` and `(RS5)`.  Equality holds exactly when the norm of `P_M` is zero,
which is equivalent to `P_M=0`.  No estimate, limiting argument, or sign separation is used. ∎

## Quantitative one-sided reduction

Suppose

```text
|E_(prog,M)|<=A_prog epsilon_M,
|E_(quad,M)|<=A_quad epsilon_M,
A_E=A_prog+A_quad.
```

Then the triangle inequality and `(RS1)` give unconditionally

```text
F_M>=-A_E epsilon_M,
R_M<=D_M+A_E epsilon_M.                                 (RS7)
```

More sharply, for any budget `B_M>=|E_M|`,

```text
|F_M|<=B_M  iff  F_M<=B_M  iff  R_M>=D_M-B_M.           (RS8)
```

The first equivalence uses the automatic lower bound `F_M>=-|E_M|`; the second is algebra.
Therefore the absolute `AC25` checkpoint has only one open half: the joined response must nearly
saturate its corrected density envelope from below.  In norm form,

```text
F_M<=A_+ epsilon_M
  implies ||P_M||^2<=(A_++A_E)epsilon_M,                 (RS9)

||P_M||^2<=A_P epsilon_M
  implies |F_M|<=(A_P+A_E)epsilon_M.                    (RS10)
```

Thus absolute `AC25`, its one-sided upper bound, and the ordinary-prime aperture-energy bound are
quantitatively equivalent up to the already-controlled error constants.

## Physical strictness upgrade

For the actual clipped ordinary-prime interval packet, the equality case in `(RS4)` never occurs
when an active prime exists.  Writing the carrier as a sum of centered initial intervals shows that
its endpoint jumps are signed sums of the weights `log(p)/p`.  Starts and ends are separately
injective, and a start/end collision cannot have equal prime weights by unique factorization.
The Brownian endpoint Gram is strictly positive definite, so

```text
P_M=0  iff  the active-prime packet is empty.
```

Consequently `R_M^sharp<D_M` at every nonempty finite aperture: RH can demand only asymptotic
near-saturation, never exact cancellation.  The full radical proof and sharp local mesh lower
bound are recorded in
`physical-prime-endpoint-radical-mesh-coercivity.md`.

## Sharpness and route boundary

The inequality cannot be improved source-freely.  The counterflow normal form

```text
X=(1/2)P+Z,
Y=(1/2)P-Z
```

allows the cross-correlation `<X,Y>=(1/4)||P||^2-||Z||^2` to have arbitrary negative size while
`X+Y=P` remains fixed.  Even perfect angular anticorrelation does not make `P` small without
amplitude matching.  Likewise, endpoint-odd branch modes and zero-sum crossing colors vanish,
but the uniform endpoint-even carrier remains coherent.

The surviving theorem must therefore prove the source-specific lower response inequality in
`(RS8)`, or equivalently the small upper bound on `||P_M||^2`.  Calling this a generic response
correlation theorem would hide that it is exactly the original RH-equivalent endpoint.

## Novelty and parent-theory audit

Corpus search found `(HGS29)` but no explicit corrected-response domination, equality
classification, negative-half closure, or one-sided reformulation of `AC25`.  These are useful new
statements inside this project because they correct the orientation of the live frontier.

They are nevertheless an immediate application of Hilbert norm nonnegativity and definiteness to
the already-proved identity `(HGS29)`.  Accordingly this card makes **no external scientific
novelty claim**.  Existing averaged prime-correlation, nilsequence, spectral-dispersion, and
large-sieve results audited on the parent card do not provide the remaining reverse inequality at
the required `M^(-1)` scale.

## Lean status

`RHTower.XiPhysicalPrimeCorrectedResponseSaturation` formalizes the source-linked finite theorem,
not an abstract order-arithmetic wrapper.  It defines the corrected and uncorrected physical
responses from the actual clipped ordinary-prime aperture carrier and proves `(RS1)`--`(RS10)`,
including exact saturation, strictness for every nonempty active packet, automatic lower deficit,
one-sided reformulation, and both quantitative budget transfers.  Its fusion energy is linked to
the literal squared Hilbert norm by `XiPhysicalPrimeLogApertureHilbertMetric` and strict positivity
by `XiPhysicalPrimeEndpointRadical`.

Direct source checking and targeted
`lake build GaloisForLFunctions.RHTower.XiPhysicalPrimeCorrectedResponseSaturation` pass.  Delta
axiom audits of the capstone declarations report only `propext`, `Classical.choice`, and
`Quot.sound`.  As stated in the module documentation, identifying an external analytic `AC25` sum
with this finite response remains a separate interface and is not assumed by these theorems.

## Gates

- [x] 0 -> 1: exact invariant quantities and source-pure statement identified
- [x] 1 -> 2: dependency-closed proof of `(RS2)`--`(RS10)`
- [x] hostile audit: correlation sign, parity, crossing-color, and PSD shortcuts rejected
- [x] novelty audit: corpus-absent frontier correction; parent Hilbert step is standard
- [x] 2 -> 3: source-linked finite Lean theorem, targeted leaf check, and axiom audit
- [ ] analytic Lean definitions connecting that finite theorem to `D_M,R_M,E_M`

## Log

- 2026-07-18 — extracted from the signed-Jordan and low/high-correlation no-gos; paper proof and
  hostile audit completed without numerical computation.
- 2026-08-23 — Audited existing source-linked module
  `XiPhysicalPrimeCorrectedResponseSaturation`: all `(RS1)`--`(RS10)` declarations pass direct
  source, targeted `.olean`, and delta axiom checks.  Moved card to stage 3.
