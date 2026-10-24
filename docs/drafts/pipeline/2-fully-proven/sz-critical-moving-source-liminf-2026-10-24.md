# Joint critical limit under strong L² source convergence

- **ID:** sz-critical-moving-source-liminf-2026-10-24
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** exact critical Beta tangent, L² correlation stability, literal finite arithmetic assembly.
- **Statement:** On every fixed compact source window, the normalized literal Suzuki deficit has the full extended Weil form as its strong-L² Gamma limit.

## Proof route and remaining blocker

The fixed-source critical limit does not by itself justify exchanging smoothing
and critical-shift limits. The joint lower bound below pays that exchange on a
fixed compact window. It retains the full signed arithmetic source. A growing
window and universal arithmetic positivity remain separate open problems.

## Exact conjecture and outcome — proved on paper

Fix B>0. Let f_j and f be real L² functions vanishing outside [-B,B], with
`||f_j-f||₂→0`, and let `ω_j→0+`. Set

`Q_ω(f)=(autocorr(f,0)-suzukiCriticalSourcePairing(f,ω))/ω`,

`W_ext(f)=sourceLevyEnergy(f)+γ₀ autocorr(f,0)-2 fullPairing(autocorr f)`.

Then, in the extended reals,

`W_ext(f) ≤ liminf_j Q_(ω_j)(f_j)`.

For every f the constant sequence f_j=f is a recovery sequence, because the
full compact-L² first variation gives exact convergence, including infinite
energy. Thus these are the strong sequential Gamma-liminf and recovery laws.
No weak-L² Mosco statement is claimed.

## Dependency-closed proof

Write C_j for autocorrelation, R_j=C_j(0), and D_j=R_j-C_j. The proved Hilbert
estimate gives

`sup_t |C_j(t)-C(t)| ≤ (||f_j||₂+||f||₂)||f_j-f||₂ → 0`.

Consequently R_j→R and D_j(t)→D(t), with D_j≥0. For every t>0 the normalized
primary density tends to K(t). Fatou for the nonnegative products gives

`integral^+ D K ≤ liminf_j integral^+ D_j B_(ω_j)/ω_j`.

This requires neither bounded limiting energy nor a rate of source convergence.
If the limiting compensated energy is infinite, the varying positive energies
tend to infinity.

All remaining terms converge jointly. Choose one correlation cutoff A>2B.
For small ω, primary mass is at most 2. The primary cusp difference between
f_j and f is bounded by twice their uniform correlation error. The pole density
is at most `2 exp(t/2)`; its compactly tested difference is therefore bounded
by `2 A exp(A/2)` times the same correlation error. The existing fixed-source
pole limit and primary cusp limit then give all joint cusp limits.

The exact finite arithmetic decomposition uses the common integer cutoff
`floor(exp A)`. Its non-unit coefficients divided by ω tend to `2 Lambda(n)`.
There are only finitely many terms. The primary mass divided difference tends
to its Gamma constant, and R_j→R. Hence the entire finite signed correction
converges to

`(Re psi(5/4)-log pi)R + 2 integral C(t) exp(t/2)`
`  - sum_(2≤n≤floor(exp A)) 2 Lambda(n) C(log n)/sqrt(n)`.

Adding this convergent finite correction to Fatou's lower bound is legitimate
in the extended reals. Exact positive-tail splitting and the Gamma recurrence
identify the result with W_ext(f). This proves the lower bound; the constant
sequence gives recovery.

## Almost-everywhere support

The same statement holds when the common-window support condition is only
almost everywhere. Replace each source f by `1_[-B,B] f`. This representative
is pointwise supported in the window and equal to f almost everywhere, hence
defines the same L² element and preserves strong convergence. Translation
preserves null sets, so its autocorrelation is identical at every lag.
Both the literal Suzuki pairing and the extended Weil energy depend only on
that autocorrelation. Apply the pointwise-window theorem to these representatives
and substitute the equal quantities back. Constant recovery is unchanged.
This is a representative-invariance bridge, with no additional analytic input
or novelty claim. The shared Lean leaf states the result on an arbitrary
interval `[a,b]`, so the centered window is a specialization.

## Positive consequence

If a concrete compact source has positive full energy, every strongly convergent
approximation in one common compact window inherits a uniform positive deficit
for all sufficiently late approximation indices and all sufficiently small
positive shifts. Otherwise choose indices j_k≥k and shifts 0<ω_k<1/k violating
a fixed margin below the positive limiting energy; the joint liminf contradicts
that sequence. For the critical arithmetic family, positivity is already
proved independently. The source's aperture remains fixed in this consequence.

Verdict: **BRIDGE**. This closes a joint source/shift passage, not the missing
universal sign. No external novelty claim.

## Compact-family uniform shift: paper and novelty audit

Let K be a compact subset of a first-countable parameter space. Suppose the
real L² sources f_p vary continuously in L² on K, share one a.e. support
window `[a,b]`, and satisfy the supplied floor `c≤W_ext(f_p)` for p∈K.
For every δ>0 there is ω₀>0 such that, simultaneously for p∈K and 0<ω<ω₀,

`ω(c-δ) < autocorr(f_p,0)-suzukiCriticalSourcePairing(f_p,ω)`.

Proof: otherwise choose violating pairs `(p_n,ω_n)` with
`0<ω_n<1/(n+1)`. Compactness gives a convergent subsequence p_n→p∈K;
continuity gives strong L² convergence of its sources. The joint liminf is
at least W_ext(f_p)≥c, so the same subsequence eventually has quotient
greater than c-δ/2, contradicting its upper bound c-δ. This includes an
infinite limiting energy. No smoothness or increment-rate bound is used.

This is a compactness corollary of the joint theorem, not an independent
arithmetic positivity principle. The common Weil floor is an explicit input
to this corollary; it is not an extra premise of the Gamma-liminf or recovery
theorems. No novelty credit is assigned. The stronger consequence has a
dependency-closed paper proof; Lean certification remains pending.

## Gates

- [x] Precise moving-source conjecture and complete paper proof.
- [x] Every analytic input derived from L² convergence and a common compact window.
- [x] Formalize the varying-primary Fatou theorem.
- [ ] Formalize joint signed-cusp convergence and complete arithmetic liminf.
- [ ] Direct canonical checks and all public transitive axiom audits.

## Lean checkpoint

The primary-energy component is certified in
`SuzukiCriticalMovingPrimaryEnergy.lean`: fixed-lag L² continuity,
`suzukiCriticalLimitingEnergy_le_liminf_of_L2_tendsto`, and
`tendsto_suzukiCriticalCompensatedEnergy_top_of_L2_tendsto`. Its direct canonical
check and all three transitive axiom audits passed; see the
[primary-energy certificate](../3-formalized/sz-critical-moving-primary-energy-2026-10-24.md).

The [fixed-source compact-L² capstone](../3-formalized/sz-critical-source-extended-energy-domain-2026-10-24.md)
and [literal-family consequence](../3-formalized/sz-critical-family-literal-source-deficit-2026-10-24.md)
are also certified. The shared
`RHTower/Suzuki/SuzukiCriticalMovingWindowDeficit.lean` now contains joint
signed-cusp convergence, the complete arithmetic liminf on arbitrary a.e.
common windows, constant recovery, deficit inheritance, and compact-family
uniformity. Its leaf check and all public transitive axiom audits remain
pending. The redundant local draft is not a second implementation target.
