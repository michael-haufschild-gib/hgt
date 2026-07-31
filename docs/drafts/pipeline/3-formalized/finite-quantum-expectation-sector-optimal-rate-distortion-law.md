# Optimal observable recurrence capacity–distortion law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteQuantumExpectationSectorOptimalRateDistortionLaw`
- **Claim class:** `[LEAN-PROVED] [CANDIDATE-NOVEL]`

## Result

For fixed phase resolution \(Q\) and target deviation \(\varepsilon\), define
\[
 {\cal C}_{\varepsilon}(Q)=
 \min_{G:B_G(Q)\le\varepsilon}
 \left(|V|-\#\pi_0(G)\right).
\]
Whenever the target is feasible, this minimum is attained and gives the
least graph-capacity exponent among all certified sector-graph
compressions.

Joint graph–resolution optimization defines
\[
 {\cal T}_{\varepsilon}=
 \min_{Q,G:B_G(Q)\le\varepsilon}
 (Q+1)^{|V|-\#\pi_0(G)}.
\]
Every \(\varepsilon>0\) is feasible: the complete graph has no omitted mass,
and sufficiently fine phase resolution makes its retained contribution
smaller than \(\varepsilon\).

For every positive target and every guard time, either the complete
expectation-record family never exits deviation \(\varepsilon\), or an exit
is followed strictly later by a return inside the same target with sampled
clock
\[
 1\le n\le{\cal T}_{\varepsilon}.
\]

## Formal declarations

- `finiteQuantumExpectationSectorGraphCapacity`
- `finiteQuantumExpectationSectorOptimalCapacity`
- `exists_finiteQuantumExpectationSector_optimalGraph`
- `finiteQuantumExpectationSector_optimal_neverExits_or_postExit_return`
- `finiteQuantumExpectationSectorOptimalCertifiedDeadline`
- `exists_finiteQuantumExpectationSector_optimalCertifiedPair`
- `finiteQuantumExpectationSector_optimalCertifiedDeadline_neverExits_or_postExit`
- `exists_finiteQuantumExpectationSector_feasiblePair`
- `finiteQuantumExpectationSector_positiveTarget_optimal_neverExits_or_postExit`

## Verification

Direct foreground compilation passed:

```text
lake env lean \
  GaloisForLFunctions/RHTower/FiniteQuantumExpectationSectorOptimalRateDistortionLaw.lean
```

Final umbrella build and axiom audit remain part of the paper audit.

## Boundary

\({\cal T}_{\varepsilon}\) is the least deadline certified by this
graph–Dirichlet construction. It is not asserted to equal the first actual
return time of every fixed arithmetic spectrum.
