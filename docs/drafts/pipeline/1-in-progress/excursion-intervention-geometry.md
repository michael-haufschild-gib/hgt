# Chronological tensor geometry — working knowledge

**Status:** thirteen final leaf builds passed; all 176 declarations axiom-audited (127 theorems, 49 definitions). New-field novelty unestablished.
**Aim:** develop a coherent mathematical theory from corpus connections, with complete paper proofs and unconditional Lean theorems. Novelty must survive comparison with existing mathematics.

## Core question

What geometry appears when invariant tensors are measured using a time-ordered observer with a bounded total variation budget?

Current primitive: a linear combination of chord polynomials
`P_D(x) = ∏_(i,j in D) (x_j - x_i)` on ordered endpoints. These are contractions of alternating two-tensors against affine probes `(1,x_i)`. Define chronological capacity as `sup |P(x)|` over `Σ |x_(i+1)-x_i| ≤ 1`. Translation is immaterial; degree controls scaling. The object retains interference between diagrams, endpoint order, and the cost of changing probes. It is not claimed to be a knot-isotopy invariant.

## What is established

- Corpus search finds leakage/compression, scattering, knot/braid, and recurrence infrastructure, but no exact `firstReturnAmplitude` declaration. Search is ranked and not a proof of absence.
- Ordinary quantum first-return generating functions and their renewal/Schur correspondence are established literature: Bourgain–Grünbaum–Velázquez–Wilkening, [arXiv:1302.7286](https://arxiv.org/abs/1302.7286).
- Arbitrary-operator first-return functions and splitting rules already exist: Grünbaum–Velázquez, [arXiv:1702.04032](https://arxiv.org/abs/1702.04032).
- Inclusion–exclusion selecting trajectories visiting all objects has a close predecessor in irreducible many-body Casimir theory: Schaden, [arXiv:1011.2475](https://arxiv.org/abs/1011.2475). Full-text comparison pending.
- Existing corpus “new field” proposals already include observer homotopy fibres, Gauss–Codazzi comparison geometry, and persistent quantum phase geometry. Repackaging these is insufficient.
- Unweighted switching filtrations are already piecewise symmetric tensor spaces: Lotter–Preiß, [arXiv:2607.04712](https://arxiv.org/html/2607.04712v1). Exact overlap found; do not claim novelty here.
- Noncommutative transfer-function realization is established: Ball–Groenewald–Malakorn, [DOI:10.1137/S0363012904443750](https://doi.org/10.1137/S0363012904443750).
- Finite stabilization uses the established Lipschitz/error-bound mechanism of [exact penalty theory](https://web.uvic.ca/~janeye/hosted/papers/ExactPenaltyFinal.pdf); do not claim that mechanism as new.
- Polynomial sup-norm geometry and curved polynomial norm balls are established, including García et al., [arXiv:2408.01741](https://arxiv.org/html/2408.01741v1), and Pérez-García–Villanueva, [DOI:10.1016/j.jat.2004.01.001](https://doi.org/10.1016/j.jat.2004.01.001), on norm attainment over ℓ₁ balls. Thus curvature alone is not a new field; the chronological chord restriction, its exact laws, and its composition structure need substantive independent results.

## Paper deductions to develop

- For one diagram, replacing every increment by its absolute value preserves cost and can only increase absolute response. Its capacity reduces to maximizing a product of interval masses on a simplex; this is closely related to graph entropy, not a new invariant by itself.
- Disjoint `r` chords have capacity `r^(-r)`; chords sharing a chronological cut have capacity `1` (AM–GM and concentration of variation).
- Four endpoints give the Plücker relation `crossing = disjoint + nested`. For `P = a·disjoint + b·nested`, capacity is exactly `max(|a|/4, |b|)`. Upper bound: with increments `u,v,w` and cost ≤1, `4|uw|+|v(u+v+w)|≤1`; endpoints attain both terms.
- Six endpoints already defeat coefficientwise capacity: let `D = (01)(23)(45)` and `R = (05)(14)(23)`. Separately `cap(27D)=cap(R)=1`, but at increments `(1/3,0,1/3,0,1/3)`, `(27D+R)=10/9`. This is an exact rational paper deduction from the computational lead, not a numerical certificate.
- For `27D+R`, monotone reduction and endpoint AM–GM reduce the exact capacity to maximizing `f(c)=27c(1-c)^2/4+c^2` on `[0,1]`. Its maximizer is `c=(50-sqrt(313))/81`, giving approximately `1.13200567`. Sharp radical value and attainment are checked in `ChronologicalTensor/SixPoint.lean`.
- General disjoint fusion should satisfy `cap(P⊗Q)=cap(P)cap(Q) r^r s^s/(r+s)^(r+s)` for homogeneous degrees `r,s`. Consequently normalizing each term of `(27D+R)⊗m` to capacity one yields total capacity at least `(10/9)^m`. This exposes exponentially large collective response invisible to the maximum of individual coefficients.
- **Curvature is the leading organizing principle.** For the degree-three plane `A·D+B·R`, the response curve is `φ(c)=(c(1-c)^2/4,c^2)`. Supporting coefficient rays are `(8c,(3c-1)(1-c))`, with exact capacity `c²(1-c²)` for `1/3≤c≤sqrt(2)-1`. The certificate is `c²(1-c²)-[2c z(1-z)²+(3c-1)(1-c)z²]=(z-c)²(1-c²-2cz)`.
- **Reversal advantage found by reasoning, outside the earlier ternary search.** For `27D-R`, every monotone unit-budget probe has absolute response ≤1, since each of `27D` and `R` lies in `[0,1]`. Gaps `(1/3,0,-1/3,0,1/3)` have cost 1 and response `-28/27`. Thus signed and monotone capacities really differ. Exact signed optimum is open; `28/27` is only a rigorous witness.
- **Enclosure/degree competition (Lean checked).** Let `P_n=n^(3n)∏(27D_i-R_i)` and seal by multiplying by total signed displacement to power k. Monotone capacity stays exactly 1. Repeating the reversed rational probe gives signed absolute response `(28/27)^n/3^k`. For `n=54(k+1)`, Bernoulli gives `(28/27)^54≥3`, hence response ≥3. Thus no finite enclosure depth uniformly erases reversal sensitivity across all degrees. Positive survivor is this exact compositional law and explicit linear degree-versus-depth bound; fixed-form convergence remains a separate open target.
- `det(φ′,φ″)=(1-3c²)/2>0` on that active arc. Thus degree three exposes a curved dual boundary where degree two has a rectangle. `Curvature.lean` checks actual first/second derivatives and the entire supporting family. For `A·D+R`, the flat branch loses optimality exactly at `A=12+8sqrt(2)`: at the transition two distinct probe motions are optimal. `Transition.lean` checks the iff classification and both witnesses. Strong certificate: `(x+y)³-[(3+2√2)xy²+(x+y)x²]=y(√2x-y)²`. This is response geometry, not spacetime curvature.

## Approaches rejected as novelty claims

- A phase-weighted swap braid: existing corpus construction; Yang–Baxter alone does not create a field.
- Projection leakage plus Schur complement: existing operator/control theory.
- First-return renewal alone: explicitly covered by the literature above.
- Möbius extraction of all-sector trajectories alone: likely known combinatorics/multiple scattering. Keep only as foundational machinery if a stronger theory emerges.
- Counting observation switches alone: the exact tensor spaces are already described by Lotter–Preiß.

These are overlap findings, not mathematical impossibility theorems.

## Exact open work

1. Checked: four/six core, supporting arc, actual derivatives, transition, and reversal advantage. `Fusion.lean` checks exact repeated capacity `K^n`; `Amplification.lean` checks the Boolean expansion and capacity-one normalization of every summand.
2. `Foundations.lean` constructs bounded capacity suprema, a mathlib seminorm, observational kernel, and interval specialization. General fusion for unequal arbitrary forms and the full invariant-theory identification remain open here.
3. **Finite stabilization now proved and final-built.** With M=monotone capacity and L=r·Σ|coefficients|, sealed capacity C_k satisfies M≤C_k≤max(M,L/k) for k≥1. Product telescoping + orientation gives |P(g)|≤M+L(1−|S|). The exact inequality z^k(1+k(1−z))≤1 closes the bound. M=0 implies P=0 via the polynomial t↦P(|g|+t(g−|g|)), zero on [0,1/2]. Thus every fixed form stabilizes exactly in finite depth; growing-degree survivors coexist with this. Lean: ProbeComparison, Sealing. SealingExamples proves exact capacity one for 27D−R at every depth ≥84; minimal depth unknown. Sharp universal degree-only depth r(r−1) is the next formal target. Paper mechanism: Jordan decomposition of a unit-cost probe gives |P(g)|≤M z^r T_r(1/z), z=|S|. T_r(x)≤x^(r²) for x≥1 follows from cosh(nt)≤cosh(t)^(n²). Sharpness in unrestricted homogeneous windows comes from (x+y)^r T_r((x−y)/(x+y)): after k enclosures, the boundary derivative at z=1 is r+k−r². Need formalize all edge cases and the polynomial representation. Mathlib has the classical extremal result in Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean; read fully, reuse it. No novelty claim for Chebyshev extrapolation (Révész survey arXiv:math/0703386). Actual chord-pairing sharpness is separate.
4. Completed: thirteen final foreground leaf builds, all 176 axiom audits, umbrella wiring, generated index, computation report and illustration. Latest global lint has two unrelated unwired-module errors: RHTower.EulerDeletionBalancedPeriodCurvatureNoGo and RHTower.EulerDeletionCurvatureCriticalBoundary; no proof-debt or contribution-specific wiring errors. New-field status remains unestablished.

## Useful corpus anchors

- `formal/GaloisForLFunctions/HTGeometry/ConstraintIdealExcursion.lean`: compression defects through hidden space.
- `formal/GaloisForLFunctions/HTGeometry/KnotTheory/RMatrix.lean`: phase braid and framed trace; inspiration only.
- `formal/GaloisForLFunctions/HTGeometry/KnotTheory/ChordData.lean`: actual ordered chord diagrams.
- `formal/GaloisForLFunctions/HTGeometry/NoncommutativeDiscreteDevelopment.lean`: chronological products; existing unrelated working-tree work, do not edit.
- `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`: checked for prior routes; this project has no RH endpoint.
- User's remembered ball-to-ring result remains unidentified. Closest inspected sources are `AbelianHiggsMechanism.lean` (unit-circle zero-energy vacua) and `ObserverKernelTubeVolume.lean` (annular tubes); neither establishes a norm ball becoming an annulus.

## Verification and resources

Runpod computation directory: `/root/chronological-chord-capacity`; local source/results/report/figure: `docs/drafts/pipeline/2-fully-proven/computations/chronological-chord-capacity`. Two searches used 24 processes, one BLAS thread each. Strong normalized-basis inequality fails from degree three; numerical maxima through degree six are approximately `1, 1.1320, 1.4108, 1.8967, 2.6903`. Detailed paper proofs and audit: `docs/drafts/pipeline/3-formalized/chronological-tensor-geometry.md`. All thirteen leaves wired into `HTGeometry.lean`. Existing shared working tree contains other researchers' work; preserve it. No commit or push was initiated by this research session. Plan tool unavailable; this document carries research state.
