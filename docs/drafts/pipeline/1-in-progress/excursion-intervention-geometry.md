# Chronological tensor geometry — working knowledge

**Verified state:** 122 individual Lean leaf builds; all 1353 declarations audited (1020 theorems, 333 definitions). The full geometric delayed-obstruction theorem is complete: 15 new leaves, 219 declarations. All leaves wired, corpus index refreshed, authoritative lint passed with existing file-size warnings. No owned Lean process remains. Novelty and priority remain unestablished; the broader research goal is paused.

**Research question:** what geometry survives when ordered polynomial observations are quotiented by what their dynamics can retain, and how do actual recovery costs differ from their thermal spectrum? Main account: [chronological tensor geometry](../3-formalized/chronological-tensor-geometry.md). This is a mathematical research program, not an established new field or a physical theory of spacetime.

## Basic objects and established structure

For an endpoint matching D, P_D(x)=∏_(i,j∈D)(x_j−x_i). Capacity is sup |P| over total variation Σ|x_(i+1)−x_i|≤1. The polynomials are classical two-row Specht polynomials; the ordered variation norm supplies the operational geometry. Lean allows arbitrary finite windows as well as genuine matchings.

- Four endpoints: cap(AD+BN)=max(|A|/4,|B|). Monotone probes suffice.
- Cubic modes D=ace and R=S(b+c+d)c: each of 27D and R has capacity one, but cap(27D+R)=K≈1.132005672, with exact maximizer (50−√313)/81. Independent repeated fusion has actual capacity K^n.
- Curved support is φ(q)=(q(1−q)²/4,q²). On 1/3≤q≤√2−1 the sharp supporting coefficients are (8q,(3q−1)(1−q)); the derivative determinant is (1−3q²)/2>0. The AD+R plateau ends at A=12+8√2.
- Full cubic norm: max(J(A,E),4|B|/27,4|C|/27,|D|/4), where J(A,E)=max_(0≤t≤1)|(A/4)t(1−t)²+Et²|. The actual probe complex retracts from a triangle with three extra edges to a diamond ring. The retraction retains B,C,D and loses the curved J-plane; the norm ball itself remains convex.
- Every degree-d form stabilizes after finite enclosure; d(d−1) is a sharp general bound for binary windows. Perfect-matching sharpness remains open. Cubic 27D−R stabilizes at depth one, while its full signed capacity remains unknown.
- Coalescence reduces monotone probes to nonadjacent support of size ≤d, preserving existing zero gaps. Positive enclosure curvature is supported exactly before stabilization; its weighted tail reconstructs the full capacity profile.

Enclosure by the existing net displacement differs from adding fresh outer endpoints. Audited padding/common-cut results identify precisely when the operations agree. There is no knot-isotopy claim.

## Canonical cusp, recovery, and zeta

The smallest flow-invariant observation space W containing the five cubic pairing observations has dimension six. Its final-retraction kernel L has dimension three. Their canonical lost modes generate A=ℝ[u,c²,c³], with u=ace+c²/2−c³/4. Faithful evaluation and normalization give B=ℝ[u,c]. The actual vector quotient B/A has basis [u^k c], of flow weight k+1.

The physical flow extends to the actual graded Hilbert completion. Its basis-independent operator trace is q/(1−q). An actual continuum reference integral and Mellin transformation give −Γ(s)ζ(s) on 0<Re(s)<1, including exactly the strip zero multiplicities. The multiplicity sequence is derived from the quotient, not assumed. This proves geometric occurrence, not an RH zero-location result.

Established extensions:

- All intermediate algebras A⊆S⊆B correspond to ideals in ℝ[u]. Preservation under one half-flow forces A or A_k=ℝ[u,c²,c³,u^k c]. The least flow-invariant repair of P depends only on the vanishing order of coeff_c(P). Finite repair heat/continuum responses converge absolutely to −Γζ throughout the strip.
- Unrestricted polynomial recovery of c from A has explicit uniform error ≤2/(n+2), so uniform separation vanishes. Exact flow compatibility restores a sharp positive separation (17√17−55)/118, with a unique optimizer.
- Every original homogeneous recovery gap δ_k is positive and attained. Its exact norm reduces to a weighted polynomial problem on [0,1/4] with weight (1−√(1−4r))^(k+1), degree ≤k+1, and penultimate coefficient one.
- Multiplication by u extends to a bounded weighted shift with weights δ_(k+1)/δ_k. Positivity of its self-commutator is equivalent to log-convexity of δ. Whether the original δ sequence is log-convex remains open.
- A separate completed [fusion response](../3-formalized/chronological-fusion-zeta-response.md) derives an energy scale log K from actual cubic amplification, faces, joins, and Euler heat. The ring retraction kills that seed, so topology alone does not retain its scale.

## Full geometric delayed-obstruction theorem — complete

[Formal certificate and proof map](../3-formalized/chronological-delayed-moment-obstruction.md); [paper proof](../2-fully-proven/chronological-delayed-moment-obstruction.md).

Keep the same cusp A⊂B, but use the actual wedge K₀={0≤c≤1,c≤u≤3c}. For N=2^(j+4), m=N+1, one homogeneous Chebyshev/cardinal sublevel inequality cuts out K_m. Lean's parameter is n=m−2=N−1.

Every K_m is compact, radial, nonconvex, has interior, and is given by six explicit polynomial inequalities. Full polynomial evaluation is faithful. All graded costs Δ_k are infima over actual representatives, proved positive and attained.

- For k<N, Δ_k is exactly the wedge cost β_k=1/((k+1)2^(k+1)).
- At N, aβ_N≤Δ_N≤hβ_N, with explicit inscribed-core factor a and cut height h<1. The bound 1−a≤11/(32m²) preserves every adjacent strict log-convexity inequality through Δ_N.
- For γ_k=(Δ_k/Δ_0)², an explicit monic shifted Chebyshev square has negative functional value at degree d=N/2. Every nonzero square of smaller degree is strictly positive. The first failing Hankel form has inertia (d,1,0). No positive measure on ℝ represents γ.
- Hausdorff distance to K₀ is at most 33/(32m²). The wedge's actual normalized costs have the explicit representing law of ST/4 for independent uniform S,T on [0,1].
- The new actual graded quotient norms give an isometric dense embedding and an AbstractCompletion. Literal radial pullback has a unique bounded extension with trace q/(1−q). The Mellin response and zeta zero multiplicities remain unchanged.

The main Lean theorem is recoverySurgery_full_geometric_theorem in RecoverySurgeryGeometry. The stronger combined theorem recoverySurgery_arbitrarily_close_delayed_obstruction gives, inside any positive Hausdorff tolerance, a nonrepresentable geometry passing every nonzero square test up to any prescribed degree. This is a geometric realization result, not a prescribed sequence of moments. No numerical calculation enters it.

## What remains hard

The original cubic probe section is different from the surgery family. Its degree-17 Jacobi square has a negative **numerical** functional value, reproduced at 230 digits in coefficient coordinates; its exact sign remains unproved. All 2080 tested Hausdorff differences passed, showing why finite tests were weak evidence. [Numerical report](../2-fully-proven/computations/chronological-recovery-gaps/REPORT.md). Those values never enter Lean.

Paper-only results for the original gaps: [exponential rate](../2-fully-proven/chronological-recovery-exponential-rate.md) ρ≈0.01736004210, and [uniform block growth / shift spectrum](../2-fully-proven/chronological-recovery-uniform-spectrum.md), yielding the closed spectral disc of radius ρ without a moment assumption. Potential-theory dependencies remain to formalize.

Other open problems: full signed cubic norm; sharp enclosure depth for genuine matchings; general arbitrary-form fusion; an observation-sensitive geometry-to-homology theory across all degrees. The literal three-variable ideal quotient and some standalone graded-dimension and finite Gamma/power-sum formulas remain paper-only.

## Failed routes and novelty boundary

Rejected novelty routes: switching-only tensors, first-return renewal, phase-swap braids, general noncommutative realization. The attempted whole-plane enclosure cone failed; its positive survivor is the exact cone AD−BR, 0≤A≤27B. Shared-cut outer arrangements yield the same reduced norm model. A retraction to a ring does not preserve the curved recovery geometry.

Classical ingredients are acknowledged: Specht polynomials, Chebyshev interpolation, exact penalties, cusp normalization, moment positivity, weighted shifts, Sylvester inertia, and Mellin identities. He 1003.2986 §4.1.2 already has the identical weighted Hilbert series; He–McKay 1308.5233 §5 links Hilbert coefficients and ζ. The normalization quotient/delta invariant is classical. Novelty must concern the canonical observation construction, repair laws, or explicit geometric realization—not these ingredients or zeta identities alone. A curvature bridge from the corpus's normalization defects remains unproved. The user's remembered ball-to-ring result is still unidentified.

## RH extension: precise boundary

[Interface assessment](chronological-rh-recovery-interface.md): h(t)=1/t−1/(e^t−1) is exactly minus the classical Müntz transform of e^(−t), also an exponentially smoothed Nyman–Beurling kernel. The smoothing multiplier Γ(s+1) has squared modulus π(τ²+1/4)/cosh(πτ) on Re(s)=1/2; it preserves zeros but has no bounded inverse on its L² range. A known sufficient RH endpoint is a uniformly bounded coefficient array a_(k,N) with e^(−t)+Σ_(k≤N)a_(k,N)h(kt)→0 in L². Novel work would have to construct that array and both estimates from actual chronological repair. The existing compact-domain polynomial recovery bound supplies neither this arithmetic family nor a norm comparison. No novel RH architecture is established by the scalar bridge; the original geometric program remains open.

## Verification and resources

Source directory: formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor. Final new audit checked all 219 declarations with only propext, Classical.choice, Quot.sound. Raw outputs and compact summary: /tmp/recovery_surgery_geometric_axioms.txt and /tmp/recovery_surgery_geometric_axiom_summary.json. Index and lint: /tmp/recovery_surgery_geometric_index.txt and /tmp/recovery_surgery_geometric_lint.txt.

Scratch checks use lake env lean; only individual leaves receive final lake build checks. No umbrella/full builds or numerical certificates. One earlier scratch/final overlap was corrected; no owned process remains. Other researchers work in the shared tree; no commit/push was initiated here. Earlier Runpod work is documented in the linked reports. No new numerical work was needed for the geometric theorem.
