# Coercive contraction for the actual BVI interior martingale

- **ID:** BVI-INTERIOR-CONTRACTION-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / source audit
- **Statement:** For every positive damping parameter, prove a strict contraction of the compensated interior martingale against the actual pronic energy, with a horizon-independent remainder.

## Goal

Build problem 4 of `docs/reports/walls/bezout-wall1-programme.md` as an independent BVI arithmetic theorem. Required conclusion: some delta > 0 and C(epsilon), independent of T, satisfy

    2 M_int(epsilon,T) + 2 c_int(epsilon) H_comp(T)
      <= (1-delta) E(epsilon,T) + C(epsilon).

No assumed analytic budget, numerical experiment, extra axiom, RH work, or use of hgtl7. The field README is read-only. A finite-period identity, conditional criterion, or result restricted to strong damping does not complete this goal.

## Plan and gates

- [x] Read attachment, full field README, project guidance, relevant memories, and current live corpus.
- [x] Locate actual definitions and audit the stated mechanism against source.
- [ ] Form conjectures from source evidence; prove or refute each on paper and retain the strongest positive survivor.
- [ ] Formalize dependency-closed results without open analytic premises.
- [x] Audit the first completed leaf with `lake --old env lean`, audit all public axiom closures, wire umbrella, regenerate index, run formal lint, clean owned scratch. Repeat for later proved leaves.
- [ ] Prove the full uniform strict contraction, then audit every requirement before completion.

## Current checkpoint

The first positive survivor is formalized and wired:
`InteriorJumpOrbitCenteringAndCompensatedBounds.lean`. Its original-source
check exited 0 with no diagnostics (44502); all fourteen public declarations
passed the axiom audit (87987) with only standard Lean axioms. Exact source
hash and evidence are on
`../3-formalized/bvi-interior-jump-orbit-centering-and-compensated-bounds-2026-10-18.md`.
The zero-conditional-mean sub-route is closed, including its positive
survivor, on `../5-failed/bvi-zero-conditional-interior-mean-2026-10-18.md`.

The programme's problem 4 now uses the actual source weight and increment,
and records this theorem without claiming strict contraction. README is
unchanged by this task. The full goal remains active: current pairwise error
has uncontrolled modulus-sum dependence.

Final index refresh passed. `lint --check-generated` has no generated-file
finding and no finding naming the owned module; six unrelated wiring and
placement errors remain. Raw final gates and source/axiom manifest are under
`logs/bvi-interior-orbit-2026-10-18-*`. All owned processes are terminal.
Ten owned temporary files were removed after archiving final audit inputs
and search evidence. Continue from the canonical source and this card.

Next conjecture to test: replace the orbit-length constant m/d by a
logarithmic orbit-length constant using the harmonic weight before taking
absolute values. Then audit the signed gcd-resonant Euler factorization
below and attack the remaining incomplete-orbit bilinear form. A better
single-pair constant alone is not a substitute for the full contraction.

`update_plan` and `multi_tool_use.parallel` are unavailable. This card tracks the plan; independent reads use `Promise.allSettled`. Serena returned no Lean symbols in the active Python project, so Lean source inspection uses corpus search and `rg`.

## Source calibration

The actual `pmBezoutInteriorMartingaleSum` is

    sum_{n=1}^{T-1} a_epsilon(n+1) I_epsilon(n)
      (1/(n+1)-1/(T+1)),

where a is `pmPowerDampedCenteredDivisorCoeff`. It is not the sum with harmonic differences H_T-H_n in the programme prose. Also

    a_epsilon(n+1) = Delta I_epsilon(n) + Delta^2 S_epsilon(n),

where S is `pmActiveSawtoothComponent`. Dropping the second-difference term changes the target. The finite-cutoff interior sawtooth differs from the horizon-free prefix by an explicit affine term; it cannot be silently substituted either.

Verified source locations: `BezoutPronicTotientInteriorMartingaleSynthesis.lean` (definition and affine bridge), `InteriorMartingaleQuadraticGradientAndRenormalizedDriftBudget.lean` (increment law), `CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget.lean` (canonical budget), `PronicPotentialSelfCancellationAndInteriorGradientConservation.lean` (coefficient-one cancellation).

## First conjecture: correct conditional centering before estimating

For a jump modulus d and interior modulus e, test the conditional mean of the actual centered sawtooth, with both endpoint residues deleted, along n = -1 mod d. Coprimality of the endpoint integers does not imply coprimality of these two moduli. Determine the gcd-resonant main term and finite-prefix remainder before claiming orthogonality or summability. A failure of zero conditional mean must retain an exact projection or corrected cancellation theorem as its positive survivor.

## Evidence

## Conditional-centering calculation (paper)

Let psi_e(n) = (n mod e)/e - (e-1)/(2e), and
J_e(n) = -psi_e(n) when e divides neither n nor n+1, and zero otherwise.
For positive d,e, put g=gcd(d,e), m=e/g. The progression n=d-1+dk
runs once through residues g-1+gj (0<=j<m) in m steps. Its mean psi is
(g-1)/(2e). The successor endpoint e-1 is deleted once. The predecessor
endpoint 0 occurs and is deleted precisely when g=1. Therefore

    gamma(d,e) = mean_k J_e(d-1+dk)
      = 0                              if g=1,
      = (e-g)/(2 e^2)                  if g>1.

This is zero exactly when gcd(d,e)=1 or e divides d. Otherwise it is
strictly positive. For the squarefree pair d=3,e=6 it equals 1/24; zero
conditional mean fails even on squarefree moduli. This is not a numerical
experiment: it follows by evaluating the displayed rational formula.

After subtracting gamma, the sequence has period m and zero period sum.
Since |J_e|<=1/2 and 0<=gamma<=1/2, every incomplete period has absolute
sum <=m. Abel summation along the progression then gives, for every L,

    |sum_{k<L} (J_e(d-1+dk)-gamma(d,e))/(d(k+1))| <= m/d.

The same estimate applies to the nonnegative compensated weight
max(1/(d(k+1))-1/(T+1),0). This supplies a genuine bound uniform in the
observation horizon for each pair, not only a cycle identity. Its dependence
e/(d*gcd(d,e)) is not yet summable across the actual growing modulus range;
it does not establish the requested contraction. This exact result is now
formalized and audited in the module listed in the current checkpoint.

The generic fractional-atom gcd orbit mean already exists as
`RHTower.cycleAverage_fracAtom` in `CausalMobiusThetaUniformCycle.lean`.
That input is infrastructure, not a novelty claim. The target here is the
two-endpoint-deleted interior atom, its exact resonant correction, and its
finite compensated progression bound connected to the BVI interior sum.

## Evidence (continued)

### Next conjecture: keep the signed modulus sum intact

The actual weights are `pmPowerDampedRealWeight epsilon e = mu(e) e^(-epsilon)`.
The resonant correction obeys gamma(d,e)<=1/(2e), so its weighted e-series
is absolutely summable for every positive epsilon. The incomplete-orbit
remainder is the difficult term, not the resonant mean itself.

A finite prime-set check gives a further candidate identity. For a finite
set P of primes, D=P intersect primeFactors(d), s=1+epsilon, and
F_s(U)=product_{p in U}(1-p^(-s)), sum over squarefree e supported on P:

    sum_e mu(e)e^(-epsilon) gamma(d,e)
      = (1-F_s(D))/2 * (F_(s+1)(P\D)-F_s(P\D)).

Derivation: split gamma into the difference of the gcd>1 parts of
mu(e)/e^s and mu(e)gcd(d,e)/e^(s+1). Each finite sum factors prime by prime;
the coprime portions cancel. The displayed expression is nonnegative,
and strictly positive when D and P\D are both nonempty. Hence multiplying
by the jump weight mu(d)d^(-epsilon) does not give a uniform negative sign:
the sign alternates with multiplicative depth. This supports preserving
signed cross-depth interactions in the remainder estimate. This calculation
still needs a direct source/Lean audit; a full prime box is not the actual
truncation e<=N and cannot substitute for the required theorem.

Corpus query `moebius gcd Euler product coprime` completed with partial=false;
candidate lemmas and source arguments inspected. It supplies multiplicative
and coprime identities, not an audited instance of this displayed formula.

- Initial hybrid query: `interior martingale contraction coercivity`, filtered to BVI; completed, partial=false, source/compiler freshness mostly pending. Candidate lemmas and source arguments inspected. It finds the exact identities and conditional bridges, not the requested inequality.
- Deep query: `fractional part arithmetic progression gcd sawtooth conditional mean remainder`, session 57183 completed with partial=true after a semantic-retrieval timeout. Returned candidates were inspected; the focused lexical `cycleAverage_fracAtom` query located the reusable exact gcd-orbit mean. Search records are archived under `logs/bvi-interior-orbit-2026-10-18-*`.
- Working tree contains unrelated ongoing work. Preserve it. Existing cofinal arithmetic card is paused and is not this task's write scope.
- `docs/architecture.md` and `docs/testing.md` absent.

## Log

- 2026-10-18 — Opened before proof implementation; corrected target notation from actual source. Full contraction remains open.
- Scratch checks are terminal; their local elaboration errors were corrected.
  They are superseded by the successful original-source check and complete
  public axiom audit in the current checkpoint. Source assembly files are
  temporary implementation artifacts, not continuation inputs.
