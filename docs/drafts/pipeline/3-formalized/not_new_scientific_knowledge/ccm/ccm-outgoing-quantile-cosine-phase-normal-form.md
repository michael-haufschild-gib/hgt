# CCM outgoing-quantile cosine-phase normal form

- **ID:** ccm-outgoing-quantile-cosine-phase-normal-form
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `CCMActualHeadOutgoingQuantileTransportProducer.lean`
- **Statement:** Every exact outgoing quantile transport cell and finite block is one Fourier
  spectral average against an explicit even signed cosine-discrepancy symbol. Its zero-frequency
  value vanishes, its curvature is an exact node-vs-cell second-moment error, and cell position plus
  completed error classify two one-sided curvature chambers.

## Goal

Preserve phase orientation in the exact globally covering quantile decomposition. Existing
`CCMActualHeadQuantileGammaChiSquareProducer` controls the same cells after absolute values and
Cauchy--Schwarz; this card asks for the exact signed spectral carrier before that information loss.
It is a bridge theorem, not an RH proof.

## Gates

- [x] 0 → 1 in-progress: exact source identity and attack specified; corpus search found no existing
  quantile Fourier normal form
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake env lean`, targeted `.olean`, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and external novelty audit

## Theorem A — one cell `[PROVED HERE]`

Write `b_n = ccmOutgoingPrimeQuantileBoundary n`, `s_n = log n`, and
`g = fourierUnitary f`. Define

`Q_n(xi) = ∫_[b_n,b_(n+1)] exp(h/2)
  (cos(2*pi*h*xi) - cos(2*pi*s_n*xi)) dh`.

Then

`∫_[b_n,b_(n+1)] exp(h/2) (E_f(s_n)-E_f(h)) dh
  = 2 ∫_R Q_n(xi) |g(xi)|^2 dxi`.

## Theorem B — finite exact-coverage block `[PROVED HERE]`

For `Q_N = sum_(n<N) Q_n`,

`sum_(n<N) ∫cell_n exp(h/2) (E_f(log n)-E_f(h)) dh
  = 2 ∫_R Q_N(xi) |g(xi)|^2 dxi`.

Moreover `Q_N` is even and `Q_N(0)=0`. No sign is conjectured.

## Theorem C — curvature/moment law `[PROVED HERE]`

The second frequency derivative at zero of one cell is

`Q_n''(0) = 4*pi^2 * (w_n*(log n)^2 -
  ∫_[b_n,b_(n+1)] exp(h/2)*h^2 dh)`,

where `w_n = criticalMellinAtomWeight n`. Thus first surviving low-frequency datum is exact
second-moment quadrature error of representing each mass-quantile cell by arithmetic node `log n`.

## Theorem D — displacement and completed-error chambers `[PROVED HERE]`

The same moment error is

`∫_R rho_n(r) * ( -r * (2*log n + r) ) dr`,

where `rho_n` is the literal quantile displacement-cell density already used by the Γ--chi-square
producer. Consequently:

- if `log n ≤ b_n`, then `Q_n''(0) ≤ 0`;
- if `b_(n+1) ≤ log n`, then `0 ≤ Q_n''(0)`;
- for `n>0`, `b_(n+1) ≤ log n` is equivalent to
  `2*(1-exp(-log(n)/2)) ≤ criticalMellinCompletedError(log n)`.

Therefore completed-error excess is exactly a nonnegative low-frequency phase-curvature chamber,
not merely an endpoint scalar estimate. Node-straddling cells remain genuinely mixed.

## Paper proof

1. Existing Plancherel law gives
   `E_f(s)-E_f(h)=2∫(cos(2*pi*h*xi)-cos(2*pi*s*xi))|g(xi)|² dxi`.
2. On each compact quantile cell, the joint integrand is dominated by
   `4*exp(h/2)*|g(xi)|²`. Fubini gives Theorem A; finite summation gives Theorem B.
3. Evenness follows from cosine parity and `Q_n(0)=0` pointwise.
4. Twice differentiating under the compact integral yields Theorem C. Exact cell mass replaces
   `∫exp(h/2)` by `w_n`.
5. Substitute `h=log n+r`; the square difference becomes `-r*(2*log n+r)`, giving the literal
   displacement-density identity.
6. Quantile boundaries and `log n` are nonnegative. If the full cell is on one side of its node,
   the square difference has fixed sign. Specializing the existing terminal-boundary equivalence
   to `T=log n` proves the completed-error chamber.

## Hostile audit

- Local symmetric matched cells cannot replace these cells: corpus proves they may overlap or gap.
- `Q_n` need not have a fixed sign; the theorem must retain the signed cosine discrepancy.
- `n=0,1` are included. Any use of `log n` must respect existing zero atom weights rather than add
  positivity hypotheses.
- Finite-block sign cannot be inferred from `Q_N(0)=0`; support/Fourier uncertainty remains.

## Novelty audit

- Internal search for `outgoing quantile cosine phase Fourier transport displacement moment`
  found quantile transport and Γ--chi-square modules, but no exact Fourier phase symbol, curvature
  law, displacement-moment identity, or completed-error curvature chamber.
- External novelty is not claimed. Labels:
  `[BRIDGE] [INTERNAL NOVELTY] [PROVED HERE] [FORMALIZED] [NOT AN RH PROOF]`.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileCosinePhaseNormalForm`
- Main exact spectral theorems:
  `ccmActualHeadOutgoingQuantileCellTransport_eq_cosinePhaseProfile` and
  `ccmActualHeadOutgoingQuantileFiniteBlock_eq_cosinePhaseFiniteSymbol`.
- Curvature/displacement theorems:
  `ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero`,
  `ccmActualHeadOutgoingQuantileMomentError_eq_displacementMoment`, and the two cell-position sign
  theorems.
- Arithmetic chamber:
  `ccmOutgoingPrimeQuantileBoundary_succ_le_log_iff_completedError_ge_threshold` and
  `ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero_nonneg_of_completedError`.
- `lake env lean GaloisForLFunctions/RHTower/CCMActualHeadOutgoingQuantileCosinePhaseNormalForm.lean`
  passed.
- Target-only `lake build
  GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileCosinePhaseNormalForm` passed.
- Scratch `#print axioms` audit for all 25 theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden declaration scan is empty.
- Module is wired into `GaloisForLFunctions/RHTower.lean`; umbrella was deliberately not built.
- Repository lint confirms this module is reachable. Its global nonzero exit is due only to five
  unrelated pre-existing unreachable modules.

## Log

- 2026-08-21 — promoted directly to Stage 1 after source-purity and corpus-absence audit.
- 2026-08-21 — Theorems A--D proved on paper and formalized; promoted to Stage 3.
