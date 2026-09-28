# Bounded moment repair of the small-time boundary layer

**Frozen target [R] unchanged, OPEN.** Construct one uniformly bounded real
coefficient array whose full chronological heat residual tends to zero in L².
This attack asks whether explicit tail moment interpolation can provide it.

**Plan:** derive the exact adjustable moments; construct least-coefficient-norm
tail interpolants on the authorized Runpod; test full errors and conditioning;
attack the all-cutoff estimate on paper. Numerical fits are not proof inputs.

For t>0 let r(t)=exp(−t)+Σ a_k h(kt), h(t)=1/t−1/(exp(t)−1).
The analytic extension at zero has

    r(0)=1+½Σa_k,
    r^(2j)(0)=1  (j≥1),
    r^(2j−1)(0)=−1−[B_(2j)/(2j)]Σa_k k^(2j−1).

Thus the even derivatives cannot be cancelled. The proposed constraints are
Σa_k=−2, Σa_k/k=0, and Σa_k k^(2j−1)=−2j/B_(2j), 1≤j≤m.
They remove the constant, harmonic charge and first m odd derivatives, leaving
the even remainder cosh(t)−1. Taylor convergence applies only |t|<2π/N;
no full-norm estimate follows from these identities alone.

**Frozen finite diagnostic [K-test].** N=512,2048,8192; freeze a_k=μ(k)
through M=N/2. For m=0,…,8 choose the unique tail minimizing Σ_(k>M)a_k²
subject to the above exact linear constraints. Compute the small Gram system
and coefficients with high precision, then independently evaluate actual full
norms, coefficient budgets, moment defects and energy inside/outside t≤1/N.
Report infeasibility/numerical failure without changing the family. Prediction:
increasing m will eventually incur substantial coefficient cost and may worsen
the full norm despite improving the boundary germ. This is an exploratory
diagnostic, not an asymptotic conjecture or a claim of optimal full-norm error.

**Hard estimate to attack.** Find m=m(N)→∞ for this explicitly fixed family
with sup_(k,N)|a_k|<∞ and ||r_N||₂→0, or derive an obstruction and its sharp
positive residue. Fixed-m feasibility is weaker than [R] and must be labelled
[BRIDGE]. Do not infer a diagonal construction without a quantitative bound
controlling both coefficient amplification and the remaining t≥1/N region.

**Literature scope.** Polynomial approximation with a separate unresolved
coefficient-control step already appears in Alouges–Darses–Hillion,
[2022, §§1 and 4](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1227.pdf).
Their random-variable/derivative families are not this fixed integer heat
dictionary; no novelty or automatic transfer of their density theorem is claimed.

## Independently frozen obstruction [K-finite]

For each fixed 0<θ<1 and finite-dimensional real subspace V of C¹([θ,1]),
freeze a_k=μ(k) through floor(θN), and require the tail values to be samples
a_k=f_N(k/N), f_N∈V. Conjecture: a positive full-norm error recurs at
arbitrarily large N, uniformly over all f_N, even without a coefficient bound.
This is stronger than the initial bounded-tail question, frozen independently
before completing its proof. It leaves growing-dimensional [K] and [R] open.

Proposed positive residue: the component of
K_ρ(u)=∫₀^θ x^(ρ−1)h(xu)dx orthogonal to
{∫_θ¹ f(x)h(xu)dx : f∈V}, in L²([1,2]), is nonzero at any critical zero ρ.
Its norm measures an unavoidable weighted Möbius oscillation. Exact discrete
orthogonal projection should eliminate tail coefficients without bounding them.
Check that projection converges at O(1/N) before using this strengthening.

**Paper audit outcome:** [K-finite] has a complete paper proof, including
O(1/N) convergence of exact discrete projections. Its positive survivor is
a uniform observation inequality and a nonzero orthogonal critical profile.
[Exact theorem, proof and Lean certificate](../3-formalized/chronological-finite-tail-obstruction.md).
Lean-complete, including the fixed-m least-norm moment-repair corollary
(`leastNormMomentRepair_fixedOrder_obstruction`). No route retirement.

**Independently frozen [BRIDGE K-growing-jet].** An unconditional bounded
array can have exact harmonic charge zero, an exact half-length Möbius prefix,
and an increasing number of matched odd Taylor derivatives. For each fixed
moment order, PNT makes its least-norm tail coefficients tend uniformly to
zero. A finite admissibility search can therefore increase the order slowly.
This gives no full L² estimate; it is not [R]. Prove the actual source
construction and identify precisely the missing quantitative growth bound.

**Paper audit outcome:** fixed-m Gram convergence plus unconditional harmonic
Möbius cancellation proves the bounded growing-jet source. It has an explicit
exponential residual bound on every [δ,∞), δ>0, but no full-norm estimate.
[Construction, exact proof, Lean certificate and remaining gap](../3-formalized/chronological-growing-moment-source.md).
Both results are Lean-complete; the full-norm [R] estimate remains open.

**K-test complete:** best unit-budget errors at N=512,2048,8192 are
4.04774603e−6 (m=3), 1.28472776e−6 (m=7), 5.20263969e−7 (m=5).
N=512,m=8 needs budget 10.2558158 and has worse error 1.59427516e−5.
All 27 vectors passed independent quadrature and high-precision checks.
The remaining error lies predominantly beyond t=1/N; matching more moments
need not reduce it. [Data, figures and report](../2-fully-proven/computations/chronological-boundary-moments-2026-09-06/REPORT.md).

**Next hard step:** quantify the growing moment family at t→0, including
the interval beyond its Taylor radius; formalize the actual weighted Möbius
Mellin obstruction and discrete projection survivor. Do not replace the
missing bound by fixed-m PNT convergence or diagonal feasibility alone.

**Independently frozen [BRIDGE K-window].** For every unit-bounded row with
exact zero charge and an exact half-length Möbius prefix, the residual norm
on [log(N)/N,∞) is at most 8/log(N), for N≥4. Thus [R] for the growing-jet
source is equivalent to controlling the actual rescaled interval

    N⁻¹ ∫₀^(log N) |r_N(u/N)|² du →0.

This is an equivalent moving-window target for those rows, not a weaker
replacement of [R]. The proof uses the sharper geometric bound with separate
denominators (1−exp(−t))(1−exp(−(M+1)t)). This window bound is paper-proved.

**Lean progress:** eight weighted-Mellin declarations and five weighted-boundary
theorems are audited. For bounded measurable compact weights, critical-scale
little-o decay of the actual Möbius sum forces the weight's Mellin moment to
vanish at every critical zero. A nonzero moment gives a positive source height
cofinally. Geometry, discrete projection, integer-scale transfer and the norm
observation still need formalization. [Latest certificate](../3-formalized/chronological-weighted-boundary.md).

**Direct remainder attack.** Freeze the stronger quantitative test of the
actual moment family: after cancellation, bound the exact Bose partial-fraction
remainder on 0≤u≤log N, rather than infer convergence from jets. On 0≤u≤1
the direct absolute bound pays sqrt(N)(2π)^(−2m), so mere m_N→∞ is insufficient.
On the full logarithmic window the same bound instead contains
(log(N)/(2π))^(2m) and eventually worsens with m. This rejects that absolute
estimate as a proof strategy; it does not refute the coefficients or [R].
The remaining signed arithmetic remainder must be estimated before taking
absolute values term by term. The exact expansion and surviving local bound
are recorded in the growing-moment paper; they are not yet Lean proofs.

**Signed projection attack:** the exact Gram formula rewrites the residual as
target forcing plus a Möbius sum against the heat kernel minus its tail-sample
projection. That projection generally introduces an x⁻¹ term outside the
tail interval. Subtracting this pole isolates the exact channel
−N d_(-1)(u) Σ_(k≤M)μ(k)/k and leaves a smooth kernel for Abel summation.
PNT controls that harmonic sum only as o(1); after L² rescaling its factor is
sqrt(N), so this does not close the window estimate. The remaining target is
joint cancellation of these explicit terms, not separate convergence of their
factors. The exact identity is paper-proved in the growing-moment paper;
its Lean formalization and a useful uniform bound remain pending.
