
# RH ledger checkpoint
- Audited committed range: 9e1fa313ac9324d52e689058ad15a669dba4200c..8cbf5160ec0310b142d31e1287b7cef51b7fe6b0.
- Updated docs/reports/rh-current-frontier-map.md and docs/reports/rh-killed-routes.md from actual Lean declarations/proofs and umbrella imports. No Lean edits, builds, umbrella builds, commits.
- Classification: 30 live; 17 standalone candidates + PM/PW-B; BVI supporting PM/MC/CTF; 37 named dead mechanisms. No route/candidate addition/promotion/retirement. New scalar-power limitation is scoped obstruction, not death of WL/SRT.
- [L] means committed umbrella-reachable source, NOT freshly compiled. [S] uncommitted/non-umbrella source. Source research command ran with --no-refresh; partial indexed coverage; direct source/diff audit primary.

## Incorporated facts
- BVI/MC: actual μ (H=floor log₂Q) and Λ−1 (H=ceil(2Q)^α, 7/12<α<1) weighted averaged block squared norm=o(Q^-3); final rank-two-subtracted Type-II estimate WITH arbitrary-small leading large-sieve coefficient now present, under prime-support/horizon restrictions. Mass/cubic tails remain. Centred-prime relative16ε theorem imported. ShortWindowMeanSquareCarriesTheCrossScaleLoss and MoebiusCancelsInAlmostAllLinearShortWindows imported.
- MoebiusPowerWindowSaving (one α∈(0,1), fixed powerδ>0, allQ) iff Θ<1 imported. This is quasi-RH boundary, NOT a zero-free-strip proof or RH.
- BAG: RH iff strong recurrence on EVERY compact right-strip set (no connected-complement restriction). Prime span=common polynomial/exponential closure; cutoff-uniform exp-target density on disc unions. Runge on connected-complement compacts; universality for targets with neighborhood analytic log or nonvanishing analytic extension to simply connected neighborhood. Not full interior-only/continuous-boundary Voronin theorem. Finite-point joint nonzero targets.
- BAG: target Hurwitz distance; subthreshold power-saving rarity, superthreshold positive density, equality case not asserted. At possible zero orderm, d(r)≍r^m. Uniform positive Haar mass of approximating multiplicative-prime Dirichlet-head twists on all doubled-strip discs iff RH; below distance threshold explicit mass O((M+1)^(1−2σ)). Target-zero elimination remains open.
- RW: contact aperture under ¬RH; common sup of nonnegative μ and positive-window apertures, μ=0 at contact, ≥0 below, <0 above; do NOT call first zero (zero plateau not excluded). RH iff sets unbounded; real sSup is not infinity underRH.
- EWU: blind minimum=even POLAR ground energy only for2A<log2; full even window iff Markov≥0 on zero cosh moment AND ≥−2 on unit cosh moment. No arbitrary-aperture converse from blind sign.
- ACT: finite-window shifted variation vs full odd form; converse only off-origin. Markov energy adds8(profileMoment)^2; don't identify finite Markov/variation windows generally. All-aperture at fixed positive shift isRH.
- SRT shared: width dictionaries imported, no producer. WL/FU/MC/TT/HCF/SZ/TH/HF/RW/PA/PBM/BAG equivalences; logderiv sign/cosine-shiftLP are only consequences. HJ/SEC/CDC/BSH/IRK/W1C dictionary and depth measurements remain post-divisor diagnostics, no promotion.
- Fixed finite aperture admits λ≥Λ, λ≠Λ, not full-positive, whose functional equals ζ on every windowtest; lattice position/depth have exact Nyquist L/2 blindness/detection. Scalar powers of absolute integrated Chebyshev deficit multiply excess rate byk (inf=kΔ), do not lower normalized exponent.
- Shared toolbox[L]: GuthMaynard Prop7.1 cubic expansion/phase decay/localization/unbalancedtails; HeathBrown majorants/power/dilation/corollary/meanvalue (T≤N) imported.
- Shared toolbox[S]: lagL2/L4/smoothedmoments, Prop8.1 CONDITIONAL on cubic expansion/localization premise, affineFejer/divisorcount, unitblockPerron. Principal ChenGuptaLi reflected-modes chain (5modules) source only, q=1ζ not generalcharacters. Full large-values/bootstrap unresolved.

## Concurrent working tree at handoff (not our edits)
- V/ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis.lean: finite energy defs/telescope/doubling bound only; NO equivalence declaration despite title. hH≤Q removed in favor of log(2Q+H) endpoint term.
- R/ChenGuptaLiLemma62PrincipalGuthMaynardForm.lean: proof refactor/helper constants; same principal nonzero-mode lemma62 conclusion, not umbrella-imported.
- R/Sieve/HeathBrownPairSumUnitBlock.lean: proof corrections; same Perron pair-sum scope.
- R/Sieve/GuthMaynardAffineDivisorCount.lean: Lorentz reuse; highfrequency bound improved4πKM→2πKM; same auxiliary scope, no bootstrap closure.
- Untracked R/Sieve/GuthMaynardPropSevenTwoTruncation.lean (341lines): absolute summability and frequency-box truncation of allNonzeroCubicSum, errorC|W|³T^-A forK=floor(T^(1+η)/N), W⊂[0,T], N,T≥1. NOT smoothed Prop7.2 producer; recorded[S].
- Concurrent sources preserved. Future changes/commits need fresh diff; do not assume these drafts compiled.

## Verification
- git diff --check clean for both ledgers.
- 77 new/changed real evidence paths exist (exclude six X legend placeholders).
- Counts30/17/37 and route family table preserved.
- Stale claims that Möbius Type-II assembly or arbitrarycompact Bagchi criterion are absent removed; old imported[S] labels corrected.
- No history/date/work-package sections added. Checkpoint replaced in place.
