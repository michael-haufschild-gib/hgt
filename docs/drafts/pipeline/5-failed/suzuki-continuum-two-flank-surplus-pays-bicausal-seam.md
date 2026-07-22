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
