# MC: the actual triangular short head retains a three-quarter-scale obstruction

- **ID:** MC-C12.93-short-head
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); unconditional build, direct leaf and axiom audits passed,2026-10-04,1005r.
- **Source:** `../1-in-progress/mc-scaled-liouville-density-cone.md`,1005r.
- **Statement:** `A(U)-Z U^2 H(U)=o(U sqrt(U))`, but `A(U)!=o(U sqrt(U))`, for the literal Mobius short head.

## Objects and scope

For natural U, let

    Z = sum_(n>=1) 1/n^2,
    W(y) = sum_(1<=s<=sqrt(y)) (y/s^2-1),
    H(U) = sum_(m<=U) mu(m)/m,
    V(U) = sum_(m<=U) mu(m)/sqrt(m),
    A(U) = sum_(m<=U) mu(m) W(U^2/m).

The active MC paper reconstruction is `P(U^2)=2A(U)-B(U)`, where B is its complete
short quadratic term. This leaf formalizes A and its scale law. It does not claim
a new formal reconstruction of P, a bound on B, or a bound on their difference.

The result rules out separate absolute payment of A by `O(x^(1/2+epsilon))` for
all positive epsilon, since `x=U^2` and any epsilon below1/4 would imply the
excluded little-o bound. It does not prove two-sided signed excursions or exclude
a one-sided bound for A. It does not falsify MC or RH.

## Dependency-closed paper proof [PROVED HERE]

1. For y>=1, set r=sqrt(y), q=floor(r)>=1. Telescoping reciprocal differences give
   `1/(q+1)<=sum_(s>q)1/s^2<=1/q`. Since q<=r<q+1, these imply
   `|W(y)-Z*y+2sqrt(y)|<=1`. The two endpoints reduce to
   `(r-q)^2/q<=1` and `(r-(q+1))^2/(q+1)-1>=-1`.
2. Sum the exact remainder with the actual Mobius coefficients, whose absolute
   values are at most1. At the moving cutoff every argument U^2/m is at least1.
   Thus `A(U)=Z U^2 H(U)-2U V(U)+E(U)`, with `|E(U)|<=U`.
3. The corpus PNT gives `M(U)=o(U)`. Discrete Abel summation gives
   `V(U)=M(U)/sqrt(U+1)+sum_(m<=U)M(m)(1/sqrt(m)-1/sqrt(m+1))`.
   The weighted differences satisfy
   `0<=m(1/sqrt(m)-1/sqrt(m+1))<=sqrt(m+1)-sqrt(m)`.
   Summing an o(1) multiple of these positive telescoping weights yields
   `V(U)=o(sqrt(U))`. Step2 proves the positive asymptotic law.
4. If A were o(U sqrt(U)), that law and Z>0 would give
   `H(U)=o(1/sqrt(U))`. Inverse Abel summation gives
   `M(U)=U H(U)-sum_(0<=m<U)H(m)`. Positive square-root increments also show
   that the last sum is o(sqrt(U)). Hence M would be o(sqrt(U)), contradicting
   `RHTower.not_mertensFunctionReal_isLittleO_sqrt` after the exact floor transfer.

All dependencies are unconditional. No RH assumption, zero simplicity assumption,
computed zero, numerical experiment, new axiom or unproved sign enters the proof.

## Lean surface

Leaf: `formal/GaloisForLFunctions/RHTower/LiouvilleTriangularShortHead.lean`.
Namespace: `RHTower.LiouvilleTriangularShortHead`.

- `squareTriangle_remainder`: full square-tail remainder, for y>=1.
- `not_harmonic_isLittleO_inv_sqrt`: unconditional actual harmonic-prefix obstruction.
- `mobiusShortHead_asymptotic`: unconditional positive survivor.
- `not_mobiusShortHead_isLittleO`: unconditional actual short-head obstruction.

The reciprocal-square mass, triangular square kernel, and actual Mobius short head
are defined in the same leaf. All generic transfer lemmas are private. The
asymptotic and obstruction statements have no extra mathematical hypotheses.

## Corpus and novelty audit

Four documented deep searches ran to terminal exit0, each `partial=false`:

- Liouville triangular primitive Mobius short quadratic combined lower bound.
- Mobius divisor constraints quadratic completion source positivity half power.
- Mobius harmonic partial square root omega oscillation integrated weighted sum.
- short Mobius square triangular harmonic cutoff oscillation.

Their file counts were65272,65272,65275,65276. Snapshot/current generations were
1223689/1223689,1223694/1223695,1223748/1223750,1223768/1223769. Each reported43
compiled snapshots and2660 stale entries, with most Lean entries source-only or
pending. Semantic coverage was unmeasured and background refresh incomplete.
Candidate declarations, source arguments and generated ingredient sets were
inspected. No applicable combined critical producer was established from these
hits; this is not a claim that the entire corpus lacks one.

Source checks used the actual `MertensSquareRootOmega` theorem, the corpus PNT,
short-quadratic reconstruction statements, and installed mathlib Abel/asymptotic
APIs. The exact new conclusion for this attack concerns the moving square head,
not a generic indefinite quadratic vector or a numerical counterexample.

## Validation and remaining target

Targeted `lake --old build GaloisForLFunctions.RHTower.LiouvilleTriangularShortHead`
passed; the new leaf was reported built in135s. The13545 job count is its dependency
graph, not a full or umbrella build. Existing cached dependency diagnostics were
replayed. Umbrella import is present once. Required direct leaf audit `lake --old env lean GaloisForLFunctions/RHTower/LiouvilleTriangularShortHead.lean` passed with no diagnostics. All four public theorem axiom audits passed from a `/tmp` scratch module, each reporting only `propext`, `Classical.choice`, and `Quot.sound`.

MC still needs the combined signed lower bound
`P(x)>=-C_epsilon*x^(1/2+epsilon)` for every positive epsilon. This result does not
supply that estimate. The next attack must preserve cancellation between the actual
short terms; their separate absolute payment is now excluded.


Index regeneration passed; all seven public declarations occur in `formal/LEAN_API.md`.
Global `scripts/formal_tools.py lint` exited1 on13 unrelated umbrella-reachability
errors, with existing large-file warnings; no error names this leaf. Source has no
forbidden declaration, computational oracle or heartbeat override. No full/umbrella
build, subagent, numerical mathematical experiment, commit or push was used. The
new import is unique. Scratch cleanup is recorded in the active working log.
