# Arithmetic positivity and incidence: 250-contribution programme

- **ID:** apt-aip-250-20261022
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** User brief `/Users/michael/.codex/attachments/e1a6a61a-d287-4ffd-a710-3c9da1ea40ae/pasted-text-1.txt`
- **Statement:** Produce 250 new substantial, field-specific contributions; retain the complete original scope.

## Requirements and counting

Read both programme READMEs completely; leave them read-only. Do not use `hgtl7`.
Search the Lean research corpus before new topics and before Mathlib. No numerical experiments,
added axioms, unproved analytic premises, proof placeholders, or heartbeat increases. Compile one
leaf at a time with `lake --old env lean`; wire completed leaves without building umbrellas.
User clarification: no web searches; use conjecturing and the Lean research search tool only.

A contribution requires a new substantive theorem, a tool solving a previously inaccessible
field problem, a discharged corpus premise, or a major RH-route advance. Do not count constants,
no-go results, renamed known results, proof lemmas, or the existing 2026-10-19 contributions.
Paper, novelty, Lean, and significance audits are separate. An incomplete candidate counts zero.

**Accepted new contributions: 0 / 250.**

## Current authoritative baseline

- Both requested READMEs read completely, including shared criteria, mechanisms, traps, and open problems.
- Read `AGENTS.md`, `formal/AGENTS.md`, formal guide/overview, `docs/reports/STATUS.md`, and
  scoped RW/AIP frontier entries. RH remains open.
- Worktree already contains many unrelated modified and untracked files; preserve them.
- Existing APT loop has at least 22 contributions; none belongs to this programme's new count.
- Research search works. Lexical inventory reports complete coverage; semantic vectors are incomplete
  and generation-lagged; results are source-only until a fresh Lean audit.

## Candidate 1: complete narrow-bump finite-part bridge

**Open source problem:** AIP README open problems 2 and 4. The prime-jump lattice bridge exists in
`BumpBridgeOfThePrimeJumpEnergy.lean`; the archimedean self-energy asymptotic is open.

**Conjecture to audit:** Let `b_j = WeilOneSided.narrowBump j`,
`M_j = integral b_j^2 > 0`, and
`F_(N,j,c)(x) = sum_(a=2)^(N+1) c_a (b_j(x-log a)-b_j(x+log a))`.
Write `E(c)=sum c_a^2` and
`I_N(c)=sum_(a,b) c_a*c_b*(ratioAtom a b+ratioAtom b a-productAtom a b)`.
For an explicit polynomial resolution `j(N,k)=128*(N+2)^4*(k+1)`, establish

`abs((Q(F_(N,j(N,k),c))-2*E(c)*Q(b_j(N,k)))/M_j(N,k)+2*I_N(c)) <= E(c)/(k+1)`.

Here `Q` is the actual complete Weil form, including both poles, Gamma, and all prime atoms.
The estimate must hold for every `N,k,c`; hence the lattice size can grow arbitrarily with `k`.
This is exact self-energy calibration, not a claim to prove a new logarithmic self-energy law.

**Why investigate:** A proved finite-part bridge would extract actual arithmetic interactions
from continuum tests despite their divergent archimedean self-energy. This is a tool for the
documented bump-bridge problem, not an all-aperture positivity theorem or an RH advance by itself.
Significance and corpus novelty remain unverified; do not count it yet.

### Paper proof mechanism and constants

For a real smooth bump with correlation `A`, mass `M=A(0)`, and correlation radius `delta`,
take `m` distinct centres separated by `s>2*delta`, span at most `D`, and amplitudes `d_i`.
Put `E=sum d_i^2`. The train correlation minus `E*A` is exactly
`R(t)=sum_(i != j) d_i*d_j*A(t-(x_i-x_j))`. Thus `R(0)=0`,
`R(t)=0` when `abs t<s-delta` or `abs t>D+delta`, and
`integral abs R <= 2*delta*M*sum_(i != j) abs(d_i*d_j) <= 2*delta*M*m*E`.
The latter follows from `abs A<=M`, its support length `2*delta`, and finite Cauchy--Schwarz.

The exact physical Weil identity gives the calibrated regular remainder
`-integral_(t>0) R(t)*2*omega(t) + 4*integral_(t>0) R(t)*cosh(t/2)`.
On the support of `R` in the positive half-line, `s/2<=t<=D+1` when
`delta<=s/2` and `delta<=1`. Since `sinh t>=t` and `cosh(t/2)<=exp(t/2)`,
`abs(4*cosh(t/2)-exp(t/2)/sinh t) <= (2/s+4)*exp((D+1)/2)`.
Thus the calibrated regular remainder is at most
`2*delta*M*m*E*(2/s+4)*exp((D+1)/2)`.
Using `exp(1/2)<2` gives `2*delta*M*m*E*(4/s+8)*exp(D/2)`.
No prime estimate or additional Lévy-density import occurs in this bound.

For the odd integer lattice, write each centre as `log p-log q` with `p,q` positive integers
at most `N+2`. Every nonzero mismatch between a centre difference and `log n` equals
`log(n*q_i*p_j)-log(p_i*q_j)`. Integer-log separation bounds its absolute value below by
`1/((N+2)^2+1)`, independently of `n`. This also bounds distinct-centre separation.
The span is at most `2*log(N+2)`, the number of centres at most `2*(N+2)`, and their squared
coefficient mass is `2*E(c)`. With `delta=1/(2*(j+1))` and the stated `j(N,k)`, exact prime
sampling applies simultaneously at every integer logarithm. Summing selected atoms gives
`M_j*I_N(c)`; the singleton bump is prime-free. The preceding regular-remainder bound is at
most `M_j*E(c)/(k+1)` by elementary algebra. This proves the displayed candidate on paper
once all normalizations and the finite-sum prime interchange are checked against source APIs.

### Nonduplication audit

- Existing `weilTest_train_select` already proves arbitrary finite-train sampling; reuse it.
- Existing `WeilWorkPBAPGramPackets` realizes finite Gram matrices at rational logarithms.
- Existing `WeilPaperPacketArchEnergy` gives an exact covariance pairing with an unestimated
  archimedean kernel. It does not provide the growing-lattice calibrated operator error above.
- Existing Suzuki small-aperture form scaling already proves the logarithmic diagonal law;
  do not count that law again.
- `DistantCopyPolarEnforcement` estimates a single far translated correlation; the new
  estimate must also cover the shrinking separation of the full integer lattice.
- Primary-source check: Suzuki, arXiv:2606.09096; Laptev--Weth, logarithmic Laplacian spectral
  properties. Generic logarithmic scaling is prior work. These checks preceded the user's
  no-web clarification; no further external searches are authorized. Judge the actual frontier
  by corpus evidence and the requested contribution criteria.

### Formalization decomposition

1. Correlation off-diagonal L1 bound and regular-channel calibrated estimate.
2. Concrete odd integer-log train, unconditional separation and simultaneous prime sampling.
3. Exact full-Weil calibration and uniform `N,k,c` error; fresh leaf and axiom audits.
4. Significance audit against the documented full bump-bridge problem before any count.

**Initial searches:**

- `research "critical factorial prime channel dense scales affine resonance logarithmic diagonal"`
- `research "lattice bump archimedean self energy logarithmic asymptotic renormalized"`
- `research "affine clock prime dilation logarithmic energy" --module arithmetic-positivity-theory`

The bump query returns the existing prime-only bridge and separated-bump positivity. The dense-scale
query returns the existing logarithmic window law and affine detuning, not an all-scale closure.

## Conjecture loop

1. Audit the full bump finite-part candidate against the existing corpus; no web searches.
2. Derive a dependency-closed paper proof and identify a substantive usable conclusion.
3. Formalize and audit the exact result if it passes; revise or reject otherwise and continue.

### Axis refinement conjecture: first jets reverse crossing incidence

An ordinary even bump at centre zero is not the origin packet of an even profile in an odd
gauge. The gauge vanishes at zero: its leading source there is `M'(0)*x*b_w(x)`, whose squared
mass is of order `w^3`, not `w`. Adding an even origin source would change the problem.

For an even bump `b`, use local shapes `b_0(u)=b(u)` and `b_1(u)=u*b(u)` and the odd source

`F(u)=d_0*b_1(u)+sum_a[c_a*(b_0(u-log a)-b_0(u+log a))`
`                           +d_a*(b_1(u-log a)+b_1(u+log a))]`.

At exact integer-log resonances, the mixed local moment is zero. The prime pairing should split
exactly into `M_0*I_minus(c) + M_1*(I_plus(d)+2*d_0*sum_a d_a*atom(a))`, where `I_minus` is
ratio+reverse-ratio−product and `I_plus` is ratio+reverse-ratio+product. Thus the derivative
channel needed by the odd gauge at the axis has **opposite crossing-product sign**, while the
axis couples only to that derivative channel. This is a positive structural candidate, not a
claim that the axis interaction is absent. Same-centre mixed full-Weil energy cancels by parity;
different-centre regular interactions can be bounded after separate self-energy calibration.

Status: paper mechanism conjectured; targeted corpus novelty search underway. No Lean statement,
no complete gauge approximation estimate, no contribution count. The first-jet theorem would
need an actual application to the missing gauge/axis problem, not just a rephrased parity identity.

## Gates

- [x] 0 → 1: original goal and candidate recorded before hard proof work.
- [ ] 1 → 2: complete paper proof, no open dependency.
- [ ] 2 → 3: leaf Lean audit, axiom audit, umbrella wiring.
- [ ] Significance/novelty audit sufficient to count one contribution.
- [ ] Original goal: 250 accepted contributions.

## Log

- 2026-10-22 — Started from current worktree; no contribution claimed. README files remain read-only.
- Drafted `RHTower/ArithmeticIncidenceBumpCorrelation.lean` and
  `RHTower/ArithmeticIncidenceLogPacketGeometry.lean`. Neither is audited or umbrella-wired yet.
  Generic correlation bounds and concrete lattice geometry are proof components, not separate
  contributions. Initial broad-import scratch hit a stale cached reference to the moved
  `ThetaCuspFullReflectionSixthModularSeam`; narrowing the import to the actual correlation
  dependency avoids that reference. No unrelated source or cached artifact was changed.
- Added draft `RHTower/ArithmeticIncidenceBumpArchimedean.lean`: exact calibration identity
  and explicit regular-kernel error estimate. It has not been checked yet.
  Correlation audit reduced to one finite-sum normalization error, now corrected; rerun needed.
  Geometry audit reported only an unclosed `noncomputable section`, now corrected; rerun underway.
  Mathlib support/integration APIs checked in `/tmp/hgt_bump_bridge_mathlib.lean`.
  The prime phase should reuse `summable_atom_indicator`, `primeAtomAtGap`,
  `atomAt_log_sub_log`, and `atomAt_log_add_log` from the existing prime bridge.
- `ArithmeticIncidenceLogPacketGeometry.lean` passed the prescribed leaf audit (exit 0).
  The uniform gap is independent of the sampled integer; both signed copies are injective.
  Added draft `ArithmeticIncidenceBumpPrimeSampling.lean` for the actual full Weil normalization
  and simultaneous atom summation. Complete bridge and contribution count remain unfinished.
- The prescribed plain leaf command typechecks but does not emit a new `.olean`. Consolidated
  the four owned draft leaves, preserving their proof content, into
  `formal/GaloisForLFunctions/RHTower/ArithmeticIncidenceNarrowBumpBridge.lean` (currently 644 lines).
  Removed only the four superseded owned drafts. This avoids importing new unbuilt modules and
  does not use `lake build`, `-o`, or `-i`. The consolidated leaf audit is underway.
- Importing the existing prime bridge, and even its `WeilMarkovPrimitiveHyperplane` atom
  dependency, encounters the stale moved-Theta module. Current consolidated source therefore
  imports only `HyperbolicPolarBalanceAndLevySinhFunctional` and repeats the standard atom
  indicator identities as private helpers. These are prior mathematics and count zero.
  Native full-Weil normalization is retained literally, not replaced by a new functional.
- Scope audit: the proposed odd lattice begins at integer label 2. It does **not** yet solve
  README problem 4 as written, which also asks for the origin/axis packet, nor problem 2's
  explicit self-energy asymptotic. Do not describe either open problem as solved. A potentially
  substantive extension is the full signed lattice including centre 0, with even/odd block
  decomposition, axis coupling in the even block, and the same fixed-resolution error bound.
  The current odd calibrated bridge remains an uncounted candidate until significance is settled.
- Consolidated geometry, correlation, archimedean calibration, and exact prime summation now
  pass elaboration apart from a redundant tactic after a solved goal; that tactic was removed.
  Added the unconditional capstone `fullEnergy_latticeTrain_uniform` at explicit resolution
  `128*(N+2)^4*(k+1)`, with radius, envelope, and error-scale proofs. Fresh audit underway.
  These additions have not yet passed Lean. No umbrella import or contribution count changed.
