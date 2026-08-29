# Route-T natural Wold residual RH classification

- **ID:** `route-t-wold-natural-rh-classification`
- **Stage:** 3-formalized
- **Route:** T / C5b
- **Status:** unconditional closed Lean equivalence; no mesh-energy premise

## Corpus-derived conjecture and full RH chain

Corpus research exposed an unclosed reverse direction. Existing modules already proved

```text
RH
  -> every strict half-power rate for the centered natural Wold residual.
```

The same search found the exact Wold/Mertens decomposition, positive Euler trace-tail bound,
finite summation-by-parts API, Stirling sandwich, prime-power correction, zero-width Chebyshev
spectrum, and its RH endpoint. This fixed the reverse chain before proof work began:

```text
all strict natural Wold residual rates
  -> same-rate centered weighted Mertens error
  -> inverse Abel: theta(N)-N = O_eps(N^(1/2+eps))
  -> real-step theta bound
  -> psi(x)-x = O_eps(x^(1/2+eps))
  -> ChebyshevErrorPowerSpectrum 0
  -> RH.
```

## New reverse Abel theorem

Lean first proves the exact finite identity

```text
theta(N) = N * mertensA(N) - sum_(k<N) mertensA(k).
```

If `|mertensA(N) - log N - K| <= B N^(-c)` for `0<c<1`, the constant `K` cancels under
inverse Abel summation and the finite prefix is absorbed uniformly, giving

```text
|theta(N)-N| <= C N^(1-c).
```

The Wold residual differs from the centered Mertens error by a nonnegative Euler correction
tail bounded by `O_eps(N^(-1/2+eps))`. Thus every strict Wold half-rate supplies the Mertens
hypothesis required above. Floor transport extends the natural bound to real `theta`; the
classical `|psi-theta| <= 2 sqrt(x) log x` estimate reaches the exact corpus source spectrum.

## Formal classification and consequence

The new closed theorem is

```text
RiemannHypothesis ↔ WoldNatResidualAllStrictHalfPowerRate.
```

Unlike the ordered-terminal classification, this equivalence has no critical mesh-energy,
prime-gap, zero-location, or asymptotic premise. Therefore proving every strict natural Wold
rate is not preliminary Route-T control: it closes RH itself. Remaining terminal-first work must
either bridge ordered-prime terminal decay to these natural-cutoff rates or retain terminal and
edge current jointly.

## Novelty audit

Primary-literature searches through 2026-08-29 found recent RH criteria involving mean signs or
correlations of classical weighted Mertens errors, including Zhao (arXiv:2411.18903) and
Bhattacharya--Martin--Simpson (arXiv:2507.13504). No source found the centered Wold primitive,
its positive Euler trace decomposition, this exact inverse-Abel classification, or the resulting
unconditional Wold-residual RH equivalence. Classical Mertens and Chebyshev ingredients are
identified as inputs; novelty claimed is their exact Route-T Wold composition and formal closure.

## Lean audit

- Module:
  `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualMertensInverseAbel.lean`
- Direct `lake env lean` elaboration: passed.
- Single targeted `lake build` audit: passed (`12537/12537`).
- Umbrella: wired into `GaloisForLFunctions.RHTower`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Formal lint: no banned declaration; only unrelated pre-existing umbrella reachability debt.
