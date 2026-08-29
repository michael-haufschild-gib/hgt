# Route-T unconditional positive-Borel terminal classification

- **ID:** `route-t-borel-terminal-unconditional-classification`
- **Stage:** 3-formalized
- **Route:** T / C5b
- **Status:** unconditional closed Lean equivalence; critical mesh energy removed

## Corpus-derived conjecture and RH chain

After the natural Wold inverse-Abel criterion was formalized, corpus search found the missing
ordered-to-natural mechanism already latent in two local facts:

1. residual decay at rate `c` forces consecutive prime-log gaps to decay at every `a<c`;
2. Wold cumulative mass is constant between consecutive primes.

This fixed the complete conjectural chain before proof work:

```text
terminal decay at every 0<y<1/2
  -> ordered Wold residual rate c
  -> prime-log gap rate a<c
  -> between-prime natural residual interpolation
  -> every strict natural Wold half-power rate
  -> zero-width Chebyshev spectrum by inverse Abel
  -> RH.
```

RH supplies terminal decay by the existing strict-half Wold estimate, so the chain is reversible.

## New between-prime theorem

For every natural cutoff `N>=2`, Lean constructs a consecutive-prime bracket

```text
p_k <= N < p_(k+1).
```

There is no prime in the open shell, hence Wold mass is constant there. After subtracting log
height and holonomy this gives the sharp inequality

```text
|R_nat(N)| <= |R_ord(k)| + (log p_(k+1) - log p_k).
```

Terminal decay at `c` gives the first term an exponential `p_k^(-c)` envelope. The corpus local
increment theorem gives the log-gap an envelope `p_k^(-a)` for every `a<c`. Bertrand's unit
log-cell bound converts `p_k^(-a)` uniformly to `N^(-a)`. Thus ordered terminal control loses
arbitrarily little exponent and supplies the exact natural criterion.

## Formal classifications

Lean proves without any premise:

```text
RH iff forall 0<y<1/2, |R_k| exp(y h_k) -> 0.
```

It also proves the literal finite-current form:

```text
RH iff forall x and 0<y<1/2,
  finiteRenormalizedCurrent_N(x,y) - finiteRawEdgeIntegral_N(x,y) -> 0.
```

This removes `Summable xiHeatCassiniPrimeGapCriticalEnergy` from both earlier equivalences.
Separate terminal removal across the strict sector is therefore unconditionally the full RH
burden. A surviving lateral-continuation proof must regularize terminal plus edge current jointly;
it cannot prove terminal decay first as an easier independent step.

## Novelty audit

Primary-literature searches through 2026-08-29 found recent RH criteria for classical weighted
Mertens error signs and correlations, notably Zhao (arXiv:2411.18903) and
Bhattacharya--Martin--Simpson (arXiv:2507.13504). No source found the prime-edge Wold residual,
the ordered-terminal/prime-gap/natural-cutoff interpolation, or this unconditional finite-Borel
landing classification. Classical prime and Chebyshev estimates are explicitly inputs; novelty
claimed is the exact Wold/Borel route composition and closed converse.

## Lean audit

- Module:
  `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalUnconditionalClassification.lean`
- Direct `lake env lean` elaboration: passed.
- Single targeted `lake build` audit: passed (`12538/12538`).
- Umbrella: wired into `GaloisForLFunctions.RHTower`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Formal lint: no banned declaration; only unrelated pre-existing umbrella reachability debt.
