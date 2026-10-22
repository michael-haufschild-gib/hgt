# BAG: complete continuous middle-coordinate cancellation

- **ID:** bag-full-band-continuous-cubic-23az
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean); complete continuous producer audited in 24az
- **Source:** bag-covered-global-defect-cancellation.md, 23az
- **Statement:** The sum of norms of the literal full-band continuous q-rows over EVERY noncontracting prime pair p,r is O(N/log³N).

## Goal

Attack the full cubic complement after the complete fixed-radius hyperbolic
packet has been proved. Retain every p,r in the original prime band and
integrate the original q-amplitude against dq/log q over [N,2N]. There is
no hyperbolic cutoff or ordering hole in this target. This would close the
complete continuous producer. It would NOT prove that the full original
prime sum differs negligibly from this continuous sum. That arithmetic
transfer, including all high frequencies, must be proved separately.

## Gates

- [x] 0 → 1: literal source, exact target, corpus-based argument.
- [x] 1 → 2: complete source-derived proof; all-ratio moving boundaries paid before the actual pair sieve.
- [x] 2 → 3: exact unconditional Lean producer, four final foreground leaf audits and imported axiom46903 passed. See ../../../3-formalized/bag-full-band-continuous-cubic-cancellation.md.

## Corpus evidence

Read actual sources, not search-generated proof suggestions:

- ChiPrimeGaussianProgressionProfile:19,92,169 defines the original
  scaled profile, its exact logarithmic correction and uniform first
  regularity on ξ∈[1/2,2], l∈[0,1], x∈[1,2].
- ChiPrimeGaussianCubicHalfResonance:167, primeProfile_fourier_once,
  retains both endpoint terms in signed integration by parts.
- ChiPrimeGaussianCubicRowCancellation:69 proves two signed integrations
  for the frozen ξ=1 profile, whose value and first derivative vanish at
  both endpoints. Its existing prime-row result covers a growing gap
  family, not every full-band prime pair.
- ChiCubicHyperbolicPrimeVariation:225 identifies the literal amplitude
  with the scaled logarithmic profile and original recentered phase.
- ChiCubicHyperbolicPrimeEdges: literal W(1)=W(2)=0 and its compact
  Lipschitz bound. Do not assume that V itself vanishes at those points.
- ChiCubicHyperbolicPrimeMoments:88 provides the actual reciprocal-square
  prime-gap moment. ChiCubicHyperbolicPrimePairs supplies the full prefix.

## Candidate proof, retaining moving boundaries

Write F(ξ,l,x)=W(ξx)V(x)/(1+l log x). Its literal source factors are C²
on a neighborhood of the compact parameter box above: x>0 and
1+l log x≥1 on the box. Joint compactness therefore supplies ONE B
bounding both x-derivatives through order two, uniformly in ξ,l. This
uniform second jet is a new source obligation to formalize; no assumed
derivative budget is allowed in the final producer.

Let L be a Lipschitz constant for W on [0,4]. At x=1,2 the source
endpoint zeros, |V|≤1 and (1+l log x)^(-1)≤1 give

    |F(ξ,l,1)| + |F(ξ,l,2)| ≤ 3 L |ξ-1|.

Two integrations by parts, keeping BOTH boundaries at each step, yield
for every nonzero real τ

    |integral_1^2 F(ξ,l,x) exp(i τ x) dx|
      ≤ 3L |ξ-1|/|τ| + 3B/τ².

The second term pays the two first-derivative endpoint values and the
entire second-derivative integral. The first boundary does not vanish
for moving ξ; dropping it would be false.

For actual p≠r put d=|p-r|, ξ=p/r, l=1/log N and
τ=2πN(p-r)/r. The exact amplitude prefactor is at most
2π/(N log N). Substitution q=Nx contributes N, and the remaining
recentring phase has norm one. Since N<r≤2N,

    |I_full(N,p,r)|
      ≤ 3L/(N log N) + 6B/(π d² log N).

This estimate is uniform in ALL full-band prime pairs, not merely fixed
hyperbolic cells. Summing the first term uses the actual squared prime
band count O(N²/log²N). Summing the second uses the proved complete
reciprocal-square gap moment O(N/log²N), with both gap orientations.
Thus the ENTIRE row-norm sum is O(N/log³N).

The value q=r is measure-zero in this integral. The discrete contraction
must remain excluded in any prime-sampling identity. No estimate for
that sampling error follows from the displayed continuous bound.

## Failed shortcut and retained hard problem

The fixed-M hyperbolic transfer cannot be used with M growing without
re-proving its uniform errors. Likewise, the once-integrated bound
O(1/(d log N)) spends the available logarithm after summing gaps.
The moving-boundary term above is instead O(1/(N log N)); the remaining
gap dependence is summable as 1/d². This is the proposed new mechanism.

Even if this continuous theorem is formalized, cancellation of the FULL
original cubic still requires a complete arithmetic sampling argument.
Growing moments/cofactors, deterministic common-height return and RH
remain open. No new producer is claimed in Lean on this card yet.

## Log

- 2026-10-06,23az: created after two new full fixed-radius packet leaves
  passed their foreground audits. Tail search72587 exit0, nonpartial,
  67634 indexed, index1263644 versus coverage1263652/current1263653;
  older-snapshot and unavailable-semantic-coverage warnings. All20
  candidate lemmas,20 source arguments and proposed ingredients read.
  The generated pair-phase ingredients do not establish a tail estimate.
- Second-derivative search98215 exit0, partial from reranking deadline;
  67635 indexed, index1263668 versus coverage1263675/current1263676.
  All20 candidates and20 source arguments read; proposed prime-decay
  ingredients are inapplicable. Exact lexical search88507 exit0 found
  the actual profile definition and first-regularity theorem; its JSON
  has no coverage/compiler freshness fields. Exhaustive source rg found
  the existing row_fourier_twice proof cited above.
- Evidence JSONs: /tmp/bag-hyperbolic-tail-search-23az.json,
  /tmp/bag-full-band-oscillatory-search-23az.json,
  /tmp/bag-moving-profile-exact-search-23az.json. No numerical experiment.

## 24az — active formalization

Revalidated23az full fixed-radius theorem in the current source and frontier.
It is actual verified progress, while full cubic/tail, growing moments and
common-height return remain open. Current source search58768 is nonpartial,
67640 indexed, index1263776 versus coverage1263780/current1263781, compiler
pending51295/stale2660/error2. No inventory errors; older-snapshot and
semantic-coverage warnings. All20 candidates and20 source arguments plus
ingredients inspected. The proposed exterior-decay ingredients do not prove
this target; the actual compact-derivative and parameter-jet proofs do apply.

Source ChiCubicPhysicalAmplitudeBudgets:29,49,73 supplies the precise
parameter-derivative/compactness mechanism. Its imported actual AFE cutoff
is smooth to ALL orders on x>0 (ChiPrimeGaussianCubicWindowTransition:24).
This exposes the stronger source fact: EVERY fixed spatial jet of the
moving logarithmic profile is uniformly bounded on the whole compact box.
Paper proof: joint smoothness at each point follows from the literal W,V
and nonzero denominator; parameter differentiation preserves smoothness;
joint continuity and compactness give one constant per order. No hidden
analytic premise. This is stronger than the originally requested two jets.

ChiCubicMovingProfileJets final7646 exit0, empty02az log. It proves actual
all-order spatial smoothness and uniform fixed-order bounds. First failure
was explicit uncurry elaboration and the actual BAGTrace namespace; fixed.
ChiCubicMovingProfileFourier now being audited; it keeps both endpoint terms
and constructs its bound from those source jets. Full-pair integral draft
retains the exact original amplitude and no hyperbolic cutoff. Not yet
claiming the full continuous aggregate, prime sampling or tail cancellation.

Fourier final10608 exit0, empty03az log. Actual all-ratio/all-log-parameter
signed Fourier bound now proved with the |ξ-1| boundary term and inverse
square remainder. Both Jets and Fourier wired once. Next audits: original
full-pair integral transport and the ENTIRE row-norm sum. Drafts are present
but not yet verified. The exact paper mechanism remains unchanged.

Sampling search60090 exit0 with partial results (judge malformed JSON and
interrupted retrieval),67646 indexed, index1263938 versus coverage1263946;
compiler pending51301/stale2660/error2, no inventory errors. All20 candidates
and20 source arguments inspected; no ingredient set. Source-read
ChiPrimeGaussianCubicPrimeOnlyVaughan:274–end: the exact full prime-only
expansion retains both masks inside its shared signed joint row. It is an
identity, not the missing analytic saving. Evidence:
/tmp/bag-full-prime-sampling-search-24az.json.

Required next arithmetic target is COMPENSATED sampling: the continuous
q-integral does not see the point q=r, but the discrete prime sum has its
literal q=r contraction and must subtract it. A raw prime-sum versus density
comparison that forgets this term would change the cubic. No absolute
row-error bound or growth-uniform fixed-denominator estimate is assumed.

FullPairIntegral final3239 exit0, empty02az log. Its exact full-band
integral transport and uniform ALL-prime-pair bound are now proved.
Source scaling retains the literal phase, V/W, 1/r and 1/log q; both
moving boundaries remain. Wired once. The aggregate continuous-cubic
leaf is now in its first foreground audit. No full discrete prime
sampling/cubic claim follows from the completed pair theorem alone.

Aggregate60959 exit0: the ENTIRE full-band row-norm sum is O(N/log³N),
and the full continuous middle-coordinate cubic has normalized complex
norm tending to zero. No hyperbolic radius or small-gap truncation remains.
One style warning (unnecessary sequence focus) removed;03az final audit
running, then imported axiom checks. All four leaves are wired once.
The finite summation uses D=floor(2N), which contains EVERY original
nonzero gap. Its scalar constant is B(2A+4E), with A the existing
reciprocal-square moment constant and E the existing prefix constant.

### 24az final result

Final aggregate11416 exit0, empty03az. Imported axiom46903 exit0:
all TEN public declarations depend only on propext,Classical.choice,
Quot.sound. All four new leaves wired once; index30963 passed and all
ten public API rows checked. Final authoritative lint85403 exit1:
367 large-file warnings,29 unrelated unreachable modules, no owned BAG
finding. Global lint is not clean. P3 card records the complete paper
proof, theorem lines and evidence logs. Earlier pending-audit and
not-yet-Lean statements on this working card are superseded.

This is verified progress beyond fixed-radius hyperbolic cancellation:
the COMPLETE continuous middle-coordinate producer is now proved.
The full compensated PRIME-sampling discrepancy, full discrete cubic
and tail, growing moments/cofactors, common-height return and RH remain
open. The RH goal stays active.
