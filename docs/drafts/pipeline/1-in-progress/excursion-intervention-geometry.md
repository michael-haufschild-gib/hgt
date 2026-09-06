# Chronological tensor geometry — working knowledge

**Status:** 107 final leaf builds passed; all 1134 declarations axiom-audited (843 theorems, 291 definitions). All leaves wired; index refreshed. Latest global lint is blocked by another active researcher's unwired RHTower module, `CCMRestrictedWeilPoleDiagonalSharpConstant`; no chronological module was flagged. New-field novelty and priority remain unestablished. Goal active.

**Aim:** develop a coherent theory of ordered tensor observation, with unconditional Lean proofs and an intrinsic appearance of zeta zeros outside RH research. Main account: [chronological tensor geometry](../3-formalized/chronological-tensor-geometry.md). Completed zeta branch: [fusion response](../3-formalized/chronological-fusion-zeta-response.md).

## Primitive

For an endpoint matching D, `P_D(x)=∏_(i,j∈D)(x_j−x_i)`. Observe linear combinations with total variation `V=Σ|x_(i+1)−x_i|≤1`; capacity is `sup|P|`. Monotone capacity restricts gaps to nonnegative values. These are classical two-row Specht polynomials with an ordered variation norm. The Lean foundations allow arbitrary finite windows, a larger class than perfect matchings.

Enclosure means multiplying P by its existing net displacement S to a power. Fresh outer endpoints are a distinct operation; the audited padding/common-cut theorems explain when it reduces to enclosure. No knot-isotopy or spacetime-curvature claim.

## Established structure

- Four endpoints: `cap(AD+BN)=max(|A|/4,|B|)`; monotone probes suffice.
- Cubic amplification: `D=ace`, `R=S(b+c+d)c`; each of 27D and R has capacity one, but `cap(27D+R)=K≈1.132005672`. Exact maximizer `q=(50−√313)/81`. Normalized repeated fusion has actual capacity K^n.
- Curved support: `φ(q)=(q(1−q)²/4,q²)`. For `1/3≤q≤√2−1`, coefficients `(8q,(3q−1)(1−q))` support it with capacity `q²(1−q²)`; derivative determinant `(1−3q²)/2>0`. The `AD+R` plateau ends at `A=12+8√2`.
- Reversal: monotone capacity of 27D−R is one, while a unit signed probe gives 28/27. Its exact signed optimum remains open. Reversal requires at least three active gaps for every genuine pairing family; the cubic attains that threshold.
- Coalescence: every monotone probe is dominated at equal variation by one with nonadjacent support of size ≤d, preserving all original zero gaps. Capacity is exactly the supremum on the physical sparse unit section; terminal unused gaps are removed.
- Full five-generator cubic norm now audited:
  `M(A,B,C,D,E)=max(J(A,E),4|B|/27,4|C|/27,|D|/4)`,
  `J(A,E)=max_(0≤t≤1)|(A/4)t(1−t)²+Et²|`.
  Actual endpoint bijections, sharp witnesses, norm laws, trivial kernels, maximum attainment, and product unit ball are proved. CubicPairings/ArcNorm/Norm/NormLaws add 51 audited declarations.
- The cubic physical complex is a filled triangle with three extra edges. Its explicit strong deformation retraction ends on a diamond ring. It preserves B,C,D and kills A,E; the induced coefficient projection is contractive and splits the norm as a maximum. Thus the homotopy-equivalent ring loses precisely the curved J-plane. The norm ball remains convex.
- Finite enclosure: every fixed form stabilizes exactly. For unrestricted degree d≥2, depth ≤d(d−1), sharp for binary Chebyshev windows. Perfect-matchings sharpness is open. The cubic 27D−R has exact depth one, also with free padding. Capacity is log-convex in depth; `κ_k=C_k−2C_(k+1)+C_(k+2)` is positive exactly before stabilization N, and `C_k=M+Σ_(j<N)(j+1)κ_(k+j)`.

## Canonical observation cusp — completed Lean chain

The [cusp paper](../2-fully-proven/chronological-observation-cusp.md) and main account now have a full second geometry-to-zeta chain. W is the smallest flow-invariant linear space containing the five pairing observations; dim W=6. L=W∩ker T₀ is the space lost under the final ring retraction; dim L=3. Its generated unital algebra is canonically selected by these definitions.

The three modes are `u=ace+c²/2−c³/4`, `v=c²`, `w=c³`, with weights 1,2,3. Faithful polynomial evaluation identifies the actual algebra with A=ℝ[u,c²,c³]. Its normalization in the common fraction field is B=ℝ[u,c]. The actual vector quotient B/A has basis `[u^n c]`, n≥0, with physical flow eigenvalue q^(n+1). Its operator diagonal gives heat 1/(exp τ−1); an actual continuum integral gives 1/τ. The Mellin response of their difference is −Γ(s)ζ(s), with exactly zeta's strip zeros and multiplicities. No multiplicity sequence is assumed.

The concrete algebra and basis are formal; the literal three-variable ideal quotient and standalone graded-dimension formulas remain paper-only.

## Observation repair — completed classification and response limit

[Paper and status](../2-fully-proven/chronological-observation-repair.md). Eleven CubicRepair leaves add 93 audited declarations. All A⊆S⊆B correspond to ideals I⊆ℝ[u]; B remains their normalization in the same fraction field. Preservation under one half-retraction forces I=0 or (u^k), and implies every scaling. The full invariant list is A and A_k=ℝ[u,c²,c³,u^k c]. Their actual quotient bases have k modes, with physical weights 1,…,k. The least invariant repair generated by P depends only on p=coeff_c(P): it is A if p=0, otherwise A_ord₀p. Finite heat and actual finite continuum integrals give b_k=(1−exp(−kτ))b. Absolute Mellin convergence and the limit −Γζ throughout the strip are formal. Only the explicit finite Gamma/power-sum formula remains paper-only.

**Uniform recovery now formal:** [CubicRecovery](../2-fully-proven/chronological-observation-recovery.md), nine audited declarations, supplies P₀=0, P_(n+1)=P_n+(c²−P_n²)/2 in A, with physical uniform error ≤2/(n+2). Hence c has no positive uniform separation from A, despite its nonzero algebraic class. This vanishing uniform separation differs from the graded norm below.

**Flow-compatible recovery now formal:** [four more leaves, 38 declarations](../2-fully-proven/chronological-equivariant-recovery.md). Requiring T_(1/2)P=P/2 inside A forces P=αu. The sharp physical uniform error is δ=(17√17−55)/118>0, uniquely at α=(126+34√17)/59. Realized probes force the lower bound; a factorization gives the upper bound. The theorem is stated on actual observed functions. Thus exact compatibility with the dynamics restores separation that unrestricted uniform recovery erases.

**All-weight boundary and recovery reduction now formal:** [seven leaves, 66 declarations](../2-fully-proven/chronological-homogeneous-boundary.md). C=1−|a−e| and q=c/C represent every physical (u,c) by a contracted edge, including zero corners. Every homogeneous capacity is an attained edge maximum, with norm laws and zero kernel. Weight k has k+1 exact coefficient coordinates; the cusp excludes u^(k−1)c. All recovery errors are exactly the weighted polynomial errors on [0,1/4] with weight (1−√(1−4r))^k, degree ≤k, and coefficient k−1 fixed to one.

**Positive graded gaps and Hilbert completion now formal:** [eight leaves, 79 declarations](../2-fully-proven/chronological-graded-hilbert-defect.md). Every positive weight has an attained strictly positive physical recovery gap δ_k. The actual graded quotient has norm δ_k|λ_k|, defined by the infimum over physical representatives and proved attained. The orthogonal sum is complete; actual B/A embeds densely and isometrically for the induced graded norm. Lean packages an AbstractCompletion, with ‖[u^k c]‖=δ_k. Here k indexes weight k+1.

**Analytic trace and metric rigidity now formal:** six leaves, 59 declarations. The physical flow extends uniquely, is positive and symmetric, and has norm q. Its actual normalized Hilbert basis gives a Hilbert–Schmidt factorization and basis-independent analytic trace q/(1−q). The operator-trace Mellin response is −Γζ, including strip zero multiplicities. On original B/A, the recovery costs and symmetric single half-flow uniquely force the inner form; positive definiteness follows.

**Recovery shift formal:** [five leaves, 45 declarations](../2-fully-proven/chronological-recovery-shift.md) prove 0<δ_(k+1)≤δ_k/4, actual multiplication by u on B/A, its unique bounded Hilbert extension, exact weights w_k=δ_(k+1)/δ_k, and T_qU=qUT_q. The nonzero self-commutator is diagonal. Its positivity on the entire completion is equivalent to gap log-convexity. This standard operator infrastructure is now sufficient.

**Hard target, following the user's correction:** [prove the exact recovery-moment obstruction](chronological-recovery-moment-problem.md); do not substitute more infrastructure. [Runpod exploration](../2-fully-proven/computations/chronological-recovery-gaps/REPORT.md) now gives a degree-17 Jacobi square witness with negative numerical functional value for (δ_k/δ_0)², independently reproduced in coefficient coordinates at 230 digits. Its binomial formula and rational scale are exact; its sign is not yet proved. All 2080 available Hausdorff differences still pass, illustrating the weakness of finite triangle tests. Gap log-convexity remains a separate open question.

**Paper-positive results:** [exact exponential rate](../2-fully-proven/chronological-recovery-exponential-rate.md) lim δ_k^(1/k)=ρ≈0.01736004210, from the fixed potential −½log(1−|t|), and [uniform block growth / exact spectrum](../2-fully-proven/chronological-recovery-uniform-spectrum.md). Correcting the forbidden coefficient of extremal polynomials yields δ_(k+d)≤[t_d+(d/4)t_(d−1)]δ_k for every starting grade. Therefore lim(sup_k δ_(k+d)/δ_k)^(1/d)=ρ and the complexified recovery multiplier has spectrum the closed disc of radius ρ, without a moment assumption. Chebyshev/potential-theory dependencies remain paper only. Novelty is unestablished.

**New analytic obstruction, paper proved:** [explicit semialgebraic geometries with arbitrarily delayed failure](../2-fully-proven/chronological-delayed-moment-obstruction.md). In the same cusp algebra, perturb the actual wedge domain K₀ by one homogeneous Chebyshev/Lagrange sublevel inequality. For N=2^(j+4), the first N actual quotient norms stay exactly β_k=1/((k+1)2^(k+1)); the next drops enough to force a negative square of degree N/2, while every preceding square test and all adjacent log-convexity tests through that cost remain strictly positive. The first failing Hankel matrix has exactly one negative eigenvalue. These nonconvex domains converge to K₀ and retain the same thermal −Γζ response. No numerics enter this proof. This answers a structural realization problem; the original cubic sign conjecture remains open. `RecoverySurgeryGrid.lean` now closes the actual polynomial perturbation: exact cosine expansion, cardinal bound 2, grid separation, selected-node excess, and preservation of every lower grid (40 audited declarations). Next: preserve the penultimate coefficient, identify the actual geometric quotient norms, and formalize the negative square. The full geometric theorem remains paper-only.

Novelty remains open. He 1003.2986 §4.1.2 has the identical weighted Hilbert series; He–McKay 1308.5233 §5 already links Hilbert coefficients and ζ. [Cogolludo-Agustín et al. (2024), §2.3](https://doi.org/10.1007/s40687-024-00457-8) explicitly defines the classical normalization quotient/delta invariant and related series. The candidate is the canonical chronological selection and its repair laws. The corpus's DaiYoshikawa/NormalizationEulerDefect links delta to a curvature correction only at the arithmetic level, with geometric formulas as premises; no curvature bridge is established here.

## Completed spectral branch

The independent-block fusion construction derives levels `E_n=log(K^n)=n log K`. Actual cubic faces, their joins, and reduced Euler coefficient −1 produce Euler heat. Subtracting an actual continuous reference integral gives a convergent Mellin response `−(log K)^(-s)Γ(s)ζ(s)`, with exactly the strip zeta zeros and multiplicities. Every bridge is audited. The ring kills the amplification seed, so topology alone cannot recover this scale.

Separate paper-only alternative: the independence complexes across all pairing degrees give an eta tower; joining two *entire towers* changes its response to `η(s−1)−η(s)`. This is different from repeated fusion of one seed. Keep the constructions separate.

## What failed, what is known, what remains

No novelty claim for classical ingredients: [Specht polynomials](https://arxiv.org/pdf/1912.05266), [polynomial norm balls](https://arxiv.org/html/2408.01741v1), [Chebyshev extrapolation](https://arxiv.org/pdf/math/0703386), [exact penalties](https://web.uvic.ca/~janeye/hosted/papers/ExactPenaltyFinal.pdf), [path-complex topology](https://arxiv.org/pdf/2305.18648), hard-core supersymmetry (0903.0784), Koopman invariant spaces (1510.03007), cusp normalization, and Mellin identities. [Hefetz–Keevash, Lemma 2.3](https://people.maths.ox.ac.uk/keevash/papers/lagrangian-journal.pdf) is a direct comparison for minimal-support mass transfer. Signed gap powers distinguish our setting, not that elementary principle.

[Fused Specht polynomials, Definition 2.13](https://doi.org/10.1090/btran/233) antisymmetrize, divide by Vandermondes, and coalesce variables; our block product differs. Do not claim Specht fusion or its physics connections are new. The related 2606.22228 was read only at abstract level.

Rejected novelty routes include switching-only tensors, first-return renewal, phase-swap braids, and general noncommutative realization. The whole-plane extension of the cubic enclosure cone failed; its positive survivor is the exact cone `AD−BR`, 0≤A≤27B. Shared-cut outer arrangements are indistinguishable by this norm; the positive survivor is their exact common reduced model.

Still open: full signed cubic norm; sharp depth for perfect pairings; general arbitrary-form fusion; comparison of single-diagram capacity with [interval entropy](https://jocg.org/index.php/jocg/article/download/3924/3645/15790); priority and whether this constitutes a distinct field. User's remembered ball-to-ring result remains unidentified; inspected Higgs vacua and annular-tube matches are only analogies.

## Verification and resources

Sources: `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor`. Single foreground Lean process; scratch via `lake env lean /tmp/...`; final exact leaf `lake build`. No umbrella/full builds. All audited dependencies use only `propext`, `Classical.choice`, `Quot.sound`; no numerical certificates. New audit: `/tmp/chronological_recovery_surgery_grid_axioms.txt` (all 40 declarations). Latest verification summary: `/tmp/chronological-recovery-surgery-grid-audit-summary.txt`; global lint failure above belongs to concurrent RHTower work. Earlier audit summary: `/tmp/chronological-recovery-shift-audit-summary.txt`. No owned Lean process remains.

Earlier remote computations: [reports](../2-fully-proven/computations/chronological-chord-capacity/REPORT.md), 24 workers, one BLAS thread each, remote `/root/chronological-chord-capacity`. Numerical leads never enter proofs. Shared tree has other researchers' edits/commits; preserve them. No commit/push initiated here. Plan tool unavailable; this compact document carries current research state.
