# RH frontier map cutoff — 2026-08-19

Authoritative docs:
- docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md
- docs/drafts/pipeline/1-in-progress/rh-route-literature-exchange-august-2026.md

Evidence cutoff: committed HEAD 9b12b2e3420769fa1d383fbff7cc84580413dd93 plus declaration-index review of current working-tree Lean modules through final status scan. Documentation-only pass; no Lean builds.

Current classification:
- 13 live: CCM-FU, C1, D2, E, G, L, O, P, Q, T, U, HC, SV2.
- 12 candidates: UEB, PSRC, SC, PPM, IRK, OPUC, HJ, BW, MSC, PCS, SEC, BPC.
- TSR remains pre-route.
- R, IW, AP terminal as independent producers.
- Main map 2025 lines, below 4000-line cap.

Major latest changes:
1. PSRC promoted as new candidate from RHTower/PrimeShiftResidueClosability.lean:
   - canonical continued prime-shift residue = -zeta multiplicity;
   - residue vanishes on dense finite Euler core in logarithmic Marcinkiewicz topology;
   - RH iff residue functional vanishes;
   - RH iff residue graph is closable;
   - off-line zero yields explicit Marcinkiewicz-null tail sequence with constant nonzero residue.
   Open core: independent literal-source closed-graph/closability estimate; current criterion exactly RH.
2. UEB already promoted:
   unit-Euler residue selects c=0 and translated Xi Bezoutian PSD iff selected value fibre lies on critical line. Open: source-produced PSD.
3. Route T GS tail fully closed:
   - MoebiusSmoothPolySaving composes all six schedule thresholds and proves unconditional all-frequency distance plus O((log z)^0.99) smooth Möbius saving for |t|<=z^2.
   - MoebiusSeriesPolySaving gives same saving for full Möbius Dirichlet series at sigma=1+1/log z.
   - SmoothAFEZetaChiLeftPowerBound closes fixed-left-line archimedean power envelope.
   Exact scientific open core: signed short Möbius-block cancellation preserving combined depth-invariant top-row/translation current. No schedule backlog remains.
4. Route E inherits unconditional analytic tail/saving but still lacks one fixed Ramaré-supported relation with interval Hall, unit load, co-moving flux, and Gibbs cost.
5. SuzukiTheoremOneOne closes literal Weil operator = Friedrichs extension of D†G_aD and dense form-core lift for O/SV2; ground sign/global target identification remain.
6. PrimeCharacterTailIndependence + PrimeOrientationCoronaRank rule out finite character palettes/finitary differential rank as global orientation selectors.

Other latest Lean is infrastructure, no route/candidate promotion:
- GammaProductRootLaw, SelbergCuspArchimedeanRoot, SelbergShiftRootLaw, SelbergRankOneSineFactor: exact Selberg cusp-spectrum shift-lattice radius law; half-rate/rank-one sine condition automatic. No horizontal zero selector.
- DirichletLZeroCount + DirichletLZeroDensityFamily: fixed-family O(r log r) Jensen count, not conductor uniform.
- QuadraticJacobiSum: exact finite-field complete cancellation and J(chi,chi)=-chi(-1), not incomplete/cofinal T/E cancellation.
- TransferFunction + CaratheodoryNevanlinnaPick: Schur/positive-real interpolation adapters, no source PSD.
- BurnsideTwoByTwo, DifferenceSemiInvariantSolution, TorsorSpecializationSeparation: abstract difference-Galois carrier/Riccati obstruction, no arithmetic occurrence or Xi reader.
- LSeriesRightLimit + LimsupPositiveFactor: normalization/root-growth utilities.

Audit:
- git diff --check clean.
- route heading parser confirms 13 live, 12 candidate.
- stale searches for eleven candidates, four-of-six, two eventual schedule facts, conditional tail, inverse-budget backlog returned none.
- no builds run, per documentation-only instruction.
