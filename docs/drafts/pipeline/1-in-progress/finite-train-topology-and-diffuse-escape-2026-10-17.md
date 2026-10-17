# Finite-train topology and diffuse packet escape

- **ID:** finite-train-topology-and-diffuse-escape-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; general signed correlations.
- **Status:** Dependency-closed paper proof complete; Lean formalization in progress; uncounted.
- **Paper:** `docs/reports/BiScaleUncertainty/FiniteTrainTopologyAndDiffuseEscape.md`
- **Guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).

## Question and proposed invariant

For a fixed actual compact smooth positive-mass seed with correlation radius D>0,
let G=copyTrain(f,c,S), Q=sum c_i²>0, and A_k=copyTrainLagCoefficient(c,k).
Define L(c)=max({0} union {|A_k|/Q : 1<=k<=m}). For S>2D, conjecture

    ||H_G-H_f||_infinity = L(c).

For sequences with S_n>=2D+2 tending to infinity, allow both packet count and
coefficients to vary. Conjecture: energies converge to E(f) regardless of those
choices, while compact correlation closure and uniform signed-grid trace decay
are each equivalent to L(c_n)->0. Unlike two-copy attenuation, many comparable
source packets may diffuse their normalized correlation coefficients.

## Paper mechanism to audit

The verified grouped correlation formula is sum_k A_k h_f(x-kS), with A_0=Q
and A_(-k)=A_k. Separation makes all correlation packets disjoint; each nonzero
packet reaches its coefficient at its center. Local normalized correlations agree
with H_f on |x|<=S/2 when S>2D. The existing local energy theorem then gives
|E(G)-E(f)|<=2 integral_(S/2,infinity) w, uniformly in count and coefficients.
The common ceiling E(f)+2 integral_(1,infinity) w permits the signed compactness
criterion. Necessity evaluates a maximizing packet at a center at least S_n.

The exponential symbol should give the exact normalized polar multiplier

    P(G)=B_c(S,1/2) B_c(S,-1/2) P(f)/Q.

For P(f)!=0 this would characterize polar continuity by convergence of the
symbol product divided by Q to one. Prove every integral identity on actual
sources; do not install an assumed analytic interface.

## Concrete sharpness candidate

Use equal coefficients at integer indices 1,3,9,...,3^(q-1), zero elsewhere.
Their positive differences are distinct: if b>d, then
3^b-3^a >= 2*3^(b-1) >= 2*3^d > 3^d-3^c; equality of two differences therefore
forces equal larger indices and then equal smaller indices. Hence Q=q and every
active positive coefficient is one, predicting L=1/q for q>=2.
Let q and S both grow. A nonnegative smooth seed with positive polar moment
should then yield global correlation and energy convergence while polar moments
diverge, with no dominant source coefficient. Audit the quantitative divergence
and the full variable-count quantifiers before declaring a paper theorem.
No exact infinite-grid blindness is asserted.

## Corpus evidence and gates

- Initial AND search returned no match; OR fallback returned the actual grouped
  lag algebra and existing compactness criterion. Logs:
  `/tmp/finite-train-topology-frontier.txt`,
  `/tmp/finite-train-topology-frontier-broad.txt`, `/tmp/diffuse-train-frontier.txt`.
- Directly inspected `FiniteTrainActiveLags.lean` and the statement/proof entry of
  `normalizedArchEnergy_abs_sub_le_of_local`. Existing expansion, local energy
  stability, and source moment multipliers are inputs, not new contributions.
- [x] Finish focused corpus search and dependency-closed paper proof.
- [x] Audit actual growing-count sharpness witness and positive classification.
- [ ] Formalize exact survivor and unconditional witnesses in BiScaleUncertainty.
- [ ] Direct leaf, axiom, umbrella/API and lint checks; count the connected result once.

## Novelty boundary

Critical sqrt(n)-rescaled polar-copy sample defects and error-sensitive tail
energy estimates already belong to package 1. A normalized restatement of those
facts is not a new contribution. This candidate instead addresses arbitrary
packet counts, grouped interference, and diffuse escape of actual sources.

## Execution plan

1. Audit grouped-packet and tail-integral APIs; finish the complete paper proof.
2. Formalize the peak invariant, exact norm and variable-count topology criteria.
3. Construct and audit the diffuse smooth witness and polar divergence.
4. Check each leaf directly, audit every public declaration, wire umbrella/API,
   run formal lint and update the knowledge ledger. `update_plan` is unavailable.

## Stronger exact domain and current evidence

The paper covers arbitrary distinct integer sites, with old copyTrain as the
special case t_i=i. It proves the peak norm, count-independent energy convergence,
compactness/trace classification, exact polar multiplier, and an explicit equal-weight
powers-of-three producer whose polar moment diverges despite correlation and energy
convergence. Formalizing actual finite data first in `FiniteIntegerTrainPackets.lean`.

Deep search `/tmp/finite-train-topology-deep.json` returned partial source-only
candidates, pending coverage, no applicable replacement identities, and no proof ideas
or ingredient sets. Existing source algebra was checked directly.

Latest user Trap 10 is applied: explicit producers with unconditional bounds are
endpoints; no assumed Chebyshev receiver or pre-floor counterterm subtraction.
The updated read-only field README was read fully (260 lines), SHA256
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
Nyquist producer search `/tmp/tail-nyquist-producer-frontier.txt` identifies seven
existing declarations in `ExplicitNyquistPolarAndChebyshevFactorialProducer.lean`;
inspect their exact statements before a future polar-tail extension, and do not
count their already-proved cell/dyadic error bounds anew.

## Formal progress checkpoint

- `FiniteIntegerTrainPackets.lean`: direct leaf check passed without diagnostics.
- `FiniteIntegerTrainPeak.lean`: final direct leaf check passed without diagnostics.
- `FiniteIntegerTrainEnergy.lean`: direct leaf check passed without diagnostics.
- `FiniteIntegerTrainCompactness.lean`: clean direct leaf check passed after an
  explicit type annotation on an intermediate order inequality.
- `FiniteIntegerTrainPolar.lean`: clean direct leaf check passed after removing
  one unused tactic.
- Drafted, not checked: `TernaryPacketTrain.lean`, `TernaryPacketPolarGrowth.lean`,
  `FiniteIntegerTrainProducers.lean`.
- The endpoint draft constructs an explicit smooth diffuse family, exact error
  1/(n+2), common energy ceiling, correlation/energy convergence and polar divergence.
  All eight drafts are written; checks proceed in dependency order.
- No new imports wired or package counted before the whole certificate is complete.
- Probe `/tmp/finite_train_topology_names.lean`; `Filter.Tendsto.div_const_atTop`
  does not exist. Use positive constant multiplication for atTop limits.

## Next paper result, uncounted

The explicit Nyquist producer admits an absolutely summable all-tail residual,
with operator norm bounded by 1/sqrt(N). A complete paper proof and positive
survivor are recorded in `NyquistPolarIntegrableResidual.md` and
`../2-fully-proven/nyquist-polar-integrable-residual-2026-10-17.md`.
Its Lean formalization has not started; the current train certificate comes first.
