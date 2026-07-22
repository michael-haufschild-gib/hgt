# Suzuki continuum two-flank surplus pays the bicausal seam

- **ID:** `suzuki-continuum-two-flank-surplus-pays-bicausal-seam`
- **Stage:** 5 — failed/retired
- **Status:** `[FALSE INFERENCE] [POSITIVE SURVIVOR PAPER-PROVED]`
- **Killed claim:** The strict inequality
  `D(1/2,2)>2` by itself gives a positive capacity margin after splicing sharp future and past
  Mangoldt cells across a width-two turning seam.

## Exact killing theorem

For every interval-integrable profile `Phi`, every common displacement `h`, and every source
quadrature `Q`, mixed future/past target mass satisfies

```text
mixedTarget(Phi)=capacityOneTarget(Phi)+overlapSeam(Phi),

mixedTarget(Phi)-Q-overlapSeam(Phi)
 =capacityOneTarget(Phi)-Q.
```

Thus “one-sided slack pays overlap” is equivalent to the original quadrature domination.  In the
continuum model `Q=capacityOneTarget(Phi)`, transport slack equals seam mass exactly and leaves
zero net margin, regardless of total apex deficit.  The critical tilted-tent theorem
`D(1/2,2)>2` is correct but measures a different quantity.

## Strongest positive survivor

`SUZUKI-BICAUSAL-NO-FREE-SPLICE`: common-displacement bicausal transport has a complete
classification.  After duplicate capacity is removed, its sole residual is the original
continuous-minus-Mangoldt quadrature deficit.  Any surviving proof must control that arithmetic
displacement commutator through new restricted-Weil/Robin/Gamma structure, not continuum
two-flank geometry or overlap bookkeeping.

Paper proof:
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-bicausal-no-free-splice-classification.md`.

## New insight

First-order weighted Mangoldt weak convergence cannot create a positive splice margin: its
continuum limit is exactly critical.  Only arithmetic displacement fluctuations around the
continuum transport can decide the sign.  This removes the proposed `C72 > seam` shortcut and
prevents a false RH claim while leaving source-specific operator transport open.

## Status

Positive survivor is dependency-closed on paper and formalized in
`formal/GaloisForLFunctions/RHTower/SuzukiBicausalNoFreeSplice.lean`.  Targeted module and axiom
audits are recorded on its Stage 3 card.

## Stronger 2026-07-22 closure: capacity and flank surplus still do not suffice

The no-free-splice identity killed one fixed-displacement realization but left an objection:
perhaps a different block arrangement could use the unbounded right-flank surplus from S69.
`SUZUKI-CRITICAL-APEX-VACUUM-CAPACITY-NO-GO` now kills that scalar inference at information-class
level.

Lean constructs an explicit atomless source measure satisfying the sharp band

```text
t-2 <= source([0,t]) <= t
```

at every positive lag and agreeing with Lebesgue measure on the entire decreasing flank.  Its
rising-flank mass compression creates Suzuki sample-channel excess at least `H_a/128`, unbounded
with aperture.  The complete reflected-polar/Gamma reserve is uniformly bounded by
`16+rectangularGammaPolarUniformBound(2)`.  At a symbolic aperture the source therefore violates
completed-lag domination despite atomlessness, capacity band, and unbounded untouched flank
surplus.

This closes the scalar **capacity/flank-surplus** sublane, not Suzuki's entire screw-function
program.  Exact remaining discriminator must use actual-Mangoldt source structure not shared by
the countermodel—equivalently, an independently derived restricted-Weil/Robin commutator or Gram
identity.  Treating S69's apex-relative block surplus as free target capacity is retired.

Paper and Lean survivor:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-apex-vacuum-capacity-no-go.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCriticalApexVacuumCapacityNoGo.lean`;
- capstone axioms: only `propext`, `Classical.choice`, `Quot.sound`.
