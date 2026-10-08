# P22: mean-square compactness of the actual residual phase

Status: CONJECTURE; no paper proof and no Lean declaration. Full WP04 is OPEN.
This source question follows the L4 periodic-class closure. It does not assume
that an arbitrary source has a periodic or weighted Fourier representation.

## Exact conjecture and competing world

Given the exact internal and external frontier, what would a Fields
Medal-winning mathematician conjecture? Test whether exact integer arithmetic
forces a pure-point translation spectrum for the *actual* residual phase,
even when uniform boundary almost periodicity is unavailable.

For every `hW : WeilPositiveFull lam`, put
`W(t) = quantizationCirclePhase hW t`. Conjecture P22 is the following exact
one-sided Besicovitch approximation statement:

For every ε>0 there exist N∈ℕ, p∈ℂ^N, ω∈ℝ^N and T₀≥1 such that for every T≥T₀,

    (1/T) ∫₀ᵀ |W(t) − Σ_{j<N} p_j exp(i ω_j t)|² dt < ε.

All integrals are Lebesgue integrals. The source provides measurability and
|W|=1; finite exponential sums are continuous and bounded, so these finite
interval integrals exist. Approximation is only on positive time: W is defined
using the cumulative measure from 0 and need not have a compatible negative-time
extension. No uniform convergence, exponential moment, frequency separation,
atomic boundary measure or critical-edge continuation is assumed.

The genuinely incompatible possibility is an actual hW and ε₀>0 for which
every finite exponential sum has mean-square error at least ε₀ along arbitrarily
late T. That would expose a continuous translation-spectral component invisible
to all finite harmonic approximations. It would defeat this source-production
route without itself deciding WP04.

## Attack before proof

1. This is weaker than the weighted Fourier representation used in L4 and L,
   but does not follow from them without proving existence of a representation.
   L4 is a receiver for exact real-periodic representations, not a P22 producer
   or a receiver for this approximation topology.
2. Interior Dirichlet convergence does not justify a boundary compactness claim.
   Brevig–Kouroupis–Perfekt, *Almost periodicity and boundary values of Dirichlet
   series*, Theorems 1.3, 1.6 and 1.7, give bounded analytic Dirichlet-series
   examples with boundary-mean/limit-interchange failures. Their Section 2
   distinguishes the physical vertical orbit from Haar-almost-everywhere
   generalized boundary values. None of those examples is shown to be an hW.
   Primary source: https://arxiv.org/html/2405.03522v2 .
3. AP Wiener factorization supplies a mean-motion exponential and bounded AP
   logarithm *after* membership and a uniform nonvanishing bound are known.
   Asatryan–Kamalyan–Karakhanyan (2019), Section 2, recalls this classical result
   and cites Böttcher–Karlovich–Spitkovsky and Gohberg–Feldman. It cannot supply
   AP membership of this canonical phase or determine its arithmetic index.
   Author-uploaded paper: https://www.researchgate.net/publication/337211564_On_a_Class_of_Integro-Difference_Equations .
4. Generic positivity, local bounded variation and the correct order of growth
   do not imply P22. The diagnostic cumulative function
   C(t)=t log(1+t)/(2π), t≥0, has C'≥0 and O(t log t) growth. Its phase is
   exp(i t log(1+t)). For each fixed ω, the derivative of
   θ(t)=t log(1+t)−ωt is eventually positive and increasing. Integration by parts
   bounds its integral on [A,T] by 3/θ'(A), uniformly for T≥A. Thus every
   fixed-frequency Cesàro coefficient is zero. For any finite exponential sum P,
   the cross term between W and P tends to zero, whereas the mean of |W|² is 1
   and that of |P|² is nonnegative. Hence the limiting mean-square error is ≥1.
   The corresponding even diffuse measure has density C'(|y|/2)/2 and
   ν((0,2t])=C(t); it is locally finite, has no atoms, and has integrable
   (1+y²)⁻¹-weight. This is not an hW or an integer-supported source identity.

Verdict for the generic boundary-inheritance shortcut: FALSE. Its positive
survivor is the precise separation between interior AP/generalized boundary
control and control on the physical boundary orbit; this is known parent
analysis, not new scientific knowledge. No new Lean theorem is warranted for
that rediscovery. The actual-source conjecture P22 is not refuted by this model.
Independent novelty of P22 is unestablished.

## First open core and next attack

[OPEN CORE] Derive the displayed mean-square approximation directly from the
exact hW arithmetic identity. Positive Herglotz representation and existing
local phase regularity do not pay this step. A proof must identify the extra
integer-support constraint that rules out the chirp diagnostic.

The separate receiver gap must remain visible: even P22 would not permit the
existing exponentially weighted dominated-convergence argument. The source
trace/kernel pairing is not proved uniformly bounded at the relevant radial scales. Transferring
mean-square approximation through it requires a proved uniform operator bound,
or a source-specific cancellation law retaining the actual error. Do not
exchange the T→∞ and radial boundary limits merely because both exist.

Next: inspect the exact contour pairing and source coefficient-energy bounds
for this uniform estimate; attack the opposite continuous-spectrum case using
actual arithmetic residues. Do not spend the next cycle formalizing generic
AP factorization or assuming P22 as the missing source premise.


## Current corpus premise audit

The exact deep search returned partial=false and no unfinished stages; compiler
metadata was mostly pending/source-only, and refresh used the running indexer.
All candidate, source-argument and proof-idea sections were inspected. Evidence
is preserved in cycle22-search-evidence.json, including coverage and freshness.

- WeilWorkSingularArithmeticReciprocalMeanSquare.exists_reciprocal_mean_square
  gives actual reciprocal mean-square identities for each fixed σ>1/2. Its
  source proof was inspected. It provides neither a uniform bound as σ↓1/2
  nor compactness of the canonical circle phase at that boundary.
- WeilConeSettledLockRigidity.blockMeans_of_meanSquare requires extra restWeight
  summability, a logarithmic coefficient bound and a quantitative logarithmic
  mean-square decay. blockMeans_of_weightedMeanSquare instead assumes the
  trace-weighted mean-square decay directly. Neither is an hW-only producer.
- WeilConeBoundaryDilationRigidity.isBohrAlmostPeriodic_LSeries_linePt assumes
  absolute series convergence at 1/2. No such premise is established for W.
- The returned canonical-logarithmic-derivative proof idea concerns the ξ
  divisor. Substituting it for an arbitrary hW measure would assume the target.

Actual-source P22 verdict: SURVIVES PRELIMINARY ATTACK; UNPROVED. This search
is not a claim of exhaustive corpus absence or independent scientific novelty.

Cycle23 sharpens the receiver audit in RESONANCE-NORM.md: the normalized
resonance functional has no bounded B² extension for any actual hW, by the
source's positive logarithmic coefficient energy. This does not assert
unboundedness of the actual radial kernel operator and does not refute P22.
The stronger source-frequency conjecture P23 is in SOURCE-FREQUENCY-REGULARITY.md.

The owned contour bounds expose the quantitative difficulty. For every p>0,
Subpolynomial bounds the actual trace by C_p(1+|t|)^p; the existing pair-kernel
bound is at most a fixed multiple of exp(-c_m ε|t|) at height ε+im.
Taking absolute values and applying Cauchy–Schwarz to an error of asymptotic
mean square δ² therefore gives a bound of order C_p δ ε^(-p), not a bound
uniform in ε. A fixed finite approximation cannot be passed through ε↓0 by
this estimate. This does not prove the signed operator unbounded: it identifies
the exact loss in the available absolute estimate. A source-specific signed
cancellation or stronger weighted approximation is needed. The existing
frequency-contour proof avoids this loss by analytic displacement of each
character and an exponentially weighted sum, a property absent from P22.
