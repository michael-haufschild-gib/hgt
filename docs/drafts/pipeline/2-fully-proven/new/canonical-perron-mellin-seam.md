# Canonical Perron--Mellin seam and source-gauge invariance

- **ID:** canonical-perron-mellin-seam
- **Stage:** 2-fully-proven
- **Type:** THEOREM / INTERFACE DISCHARGE, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parent:** `perron-mellin-seam-residue.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CanonicalPerronMellinSeam.lean`

## Medalist lens

An additive decomposition in an `L2` vector space is not extra structure.  Once the carrier line

`t |-> F(-M+it)`

is in `L2`, the defect relative to a source trace `T_M(g)` is forced:

`Delta_M^can(F,g) = [F(-M+i·)] - T_M(g)`.                             (1)

Therefore `HasCrossLineMellinDefect` should not remain a hypothesis.  The substantive condition is
eventual square-integrability of the carrier's negative lines, already encoded by the existing
`HasPerronCarrierFlankL2Energy` interface.

The stronger invariant question is source gauge.  If two lower-supported Sonin sources are
subtracted from the same carrier, their `L2` defect representatives differ.  Do their asymptotic
Perron coordinates still recover the same arithmetic datum?

The answer is yes.  The coefficient coordinate belongs to the carrier, not to the selected source.

## Theorem A `[PROVED]`: the additive defect is unique

Fix `F`, `g`, `M`, and the normalized trace `T_M(g)`.  Suppose two `L2` classes `Delta_M` and
`Delta'_M` satisfy

`F(-M+it)=T_M(g)(t)+Delta_M(t)` almost everywhere,

`F(-M+it)=T_M(g)(t)+Delta'_M(t)` almost everywhere.

Then

`Delta_M=Delta'_M` as `L2` classes.                                  (2)

### Proof

On the intersection of the two full-measure sets, cancel the common trace pointwise.  Equality
almost everywhere is equality in `L2`.

Thus the additive seam is not a moduli problem.  Existence is exactly square-integrability of the
carrier line; uniqueness is automatic.

## Theorem B `[PROVED]`: canonical construction

If `t |-> F(-M+it)` belongs to `L2`, let `[F_M]` be its canonical `MemLp.toLp` class and define (1).
Then

`F(-M+it)=T_M(g)(t)+Delta_M^can(F,g)(t)` almost everywhere.           (3)

### Proof

The canonical `toLp` representative equals the original carrier line almost everywhere.  The
coercion of subtraction agrees almost everywhere with pointwise subtraction, so (3) is the vector
identity

`F_M = T_M + (F_M-T_M)`.

If the carrier lines are square-integrable eventually in `M`, (3) supplies
`HasEventuallyCrossLineMellinDefect` without any chosen data.

## Theorem C `[PROVED]`: flank energy discharges the seam Prop

Assume `F` is entire and

`HasPerronCarrierFlankL2Energy F B`.

Then the carrier line belongs to `L2` eventually in `M`.

### Proof

Differentiability makes each vertical trace continuous and hence strongly measurable.  The energy
interface supplies integrability of `|F(-M+it)|^2`.  The `p=2` characterization of `MemLp` gives the
claim.  Theorem B then constructs the eventual additive seam.

This eliminates the former defect/coherence Prop completely.

## Theorem D `[PROVED]`: canonical coefficient recovery

Let `q>0`, let `f` belong to the even Sonin carrier at cutoff `q`, and let `F` be entire.  Assume:

1. `F` agrees with an absolutely convergent Dirichlet series `sum a_n n^(-s)` on `Re(s)>=c>0`;
2. `F` has eventual negative-line `L2` energy;
3. `F` has finite Perron horizontal carrier mass.

For an admissible `(n,delta)` with

`q^(-1)<n-delta`,                                                     (4)

form the canonical defect relative to `logEvenUnitary(f)`.  Then

`perronMellinSeamCoefficient(Delta^can,M,n,delta) -> a_n`.            (5)

### Proof

Theorem C constructs the eventual defect interface.  The previously proved Perron--Mellin seam
theorem says that every eventual additive defect has normalized residue tending to `a_n` under
(4).  Apply it to the canonical defect.

No defect family, coherence law, or representative choice remains among the assumptions.

## Theorem E `[PROVED]`: source-gauge invariance

Let `f_1,f_2` be even Sonin sources at positive cutoffs `q_1,q_2`.  Under the common carrier
hypotheses of Theorem D, assume

`q_1^(-1)<n-delta`,

`q_2^(-1)<n-delta`.

Let `Delta_1^can` and `Delta_2^can` be the canonical defects obtained by subtracting the two source
traces from the same carrier line.  Then

`A_(M,n,delta)(Delta_1^can)-A_(M,n,delta)(Delta_2^can) -> 0`.         (6)

### Proof

Each coordinate converges to `a_n` by Theorem D, so their difference converges to zero.

Equation (6) is more than uniqueness at a fixed source: it says changing the source gauge changes
the defect representative but not the asymptotic arithmetic class.

## Candidate attack

- `[FAILED AS STRUCTURE]` Treat the additive defect as chosen data.  Theorems A--C show that it is
  unique and canonically constructed from the carrier line.
- `[BRIDGE]` `MemLp.toLp`, almost-everywhere subtraction, and `p=2` energy characterization are
  standard Hilbert-space infrastructure.
- `[FAILED AS NEXT STEP]` Connect the earlier chosen-defect Prop directly to an abstract `M+` seam.
  Without a map from analytic traces to the algebraic seam, this would only manufacture another
  implication interface.
- `[SURVIVES]` Canonical subtraction followed by Perron coordinate extraction.  It removes the fake
  choice and exposes source-gauge invariance (6).

## Completed-versus-raw carrier audit

The canonical theorem sharpens, rather than hides, the remaining RH-facing mismatch:

- `xi` has the archimedean completion that supplies vertical decay, but it is
  `archFactor * LSeries`, not a raw Dirichlet series on the Perron right edge;
- a raw eta-type Dirichlet carrier removes the pole and has the correct strip divisor, but its deep
  negative-line `L2` and horizontal-mass inputs are not established and are expected to spend the
  reflected Gamma growth.

Dividing by `archFactor` is not harmless: it returns the meromorphic zeta function and introduces a
pole charge at `s=1`.  Therefore the next object must incorporate the archimedean completion into
coefficient extraction rather than assume it away.

## Novelty and significance gates

- **NOVEL:** source-gauge invariance (6) is a new constraint on the project-native seam coordinates.
  The `L2` defects depend on the chosen Sonin source, while their asymptotic Perron class does not.
- **SIGNIFICANT:** the cross-line defect Prop is fully discharged through an existing carrier-energy
  interface.  The true remaining work is now isolated to the completed/raw Perron mismatch and the
  target's analytic mass, not an artificial decomposition choice.

## Scope and open core

- The theorem does not prove the target carrier has the required flank energy or horizontal mass.
- The theorem still consumes a raw right-half-plane Dirichlet expansion.  It does not yet extract
  coefficients directly from `xi=archFactor*zeta`.
- `[OPEN CORE]` Construct an archimedean-completed Perron coordinate whose right-edge value is an
  explicit arithmetic coefficient plus computable boundary/Gamma charge, while retaining the
  completed carrier's negative-line decay.
- The theorem does not prove RH.

## Gates

- [x] 0 -> 1: fake defect choice identified and canonical replacement defined.
- [x] 1 -> 2: uniqueness, canonical existence, Prop discharge, recovery, and source invariance proved.
- [x] 2 -> 3: theorem family formalized in Lean.
- [ ] 3 -> 4: requires the archimedean-completed coefficient extractor and target mass theorem.

