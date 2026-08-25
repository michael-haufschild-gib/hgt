# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope and evidentiary rules

This document is a present-tense topology of the RH research formalized in HTGeometry, HilbertMetric, and RHTower. It records live branch architectures, exact open cores, candidate interfaces, shared structure, and terminal no-gos. It is not chronology, research diary, or catalogue of every theorem.

Evidence surface: declarations indexed from current Lean working tree in HTGeometry, HilbertMetric, and RHTower. Cards and papers are not evidence here. Incomplete intended theorems are not reported as proved.

Status language:

- **Proved** means an unconditional Lean theorem.
- **Endpoint** means a proved implication or equivalence ending in RH; it does not prove its premise.
- **Receiver** means a formal object that detects or classifies off-line zeros after a source law or divisor input is supplied.
- **Producer** means a theorem derived from the literal arithmetic, theta, prime–Gamma, Möbius, or geometric source before selecting a Xi divisor.
- **Live branch label** means source, connector chain, and RH endpoint are formal, with a first independent producer still open. It does not mean the branch is mathematically independent of other labels.
- **Candidate interface label** means a novel formal receiver or source fragment exists, but the source handoff or divisor exhaustion needed for a live branch does not. It may be another realization of an existing open problem.
- **Terminal** means Lean rules out the stated producer or proves every surviving premise equivalent to RH.

No route currently proves or disproves RH.

## Executive topology

The ledger retains **24 live branch labels** and **34 candidate interface labels**. These are indexing handles, not 58 disjoint routes. A branch is a path through several shared mathematical gates; one label can belong to several families, and several labels can terminate at the same receiver.

Live branch labels: CCM-FU, C1, CDC, D2, E, NB/BD, F2, STC, CSB, G, G-CE, L, O, P, Q, CLG/TTF, HB, SP-E, SCE, T1, T2, U, HC, SV2.

Candidate interface labels: TK, FD2, BSH, CFI, UEB, PSRC, PBM, SC, PPM, IRK, HJ, BW, MSC, PEP, EWQ-V, PCS, SEC, LI, BPC, MPLF, W1C, TCD, JAS, K-RVM, APF, S6F, WS2, FZZ-P, RBH, PW-B, WBF, XST, NDS, KMSS.

APF remains the strongest source-index candidate: it is infinite, paired, nonphysical, source-first, reflection-odd, and compact-stable. S6F adds a divisor-free sixth-order odd source weight surviving full Fock completion. WS2 adds the sharp depth-two wild-saddle counterterm that reaches the ordered reciprocal-Xi operator modulo trace class and retains a positive summable quadratic anomaly. None is yet a live branch: APF lacks trace annihilation and divisor exhaustion; S6F lacks a coefficient-faithful Xi/Weil landing; WS2 lacks a source determinant or spectral-occurrence theorem independent of ordered Xi. First-clock recurrence, prime-tail diagonal escape, KSGNS completion, cyclotomic phase-tail hypertranscendence, smooth AFE/Levinson expansion, and ABHN/Stokes classifiers sharpen existing gates but do not define further source-to-RH chains.

### Primitive open gates

| Gate | One underlying mathematical question |
|---|---|
| `ORD` | Can the literal source prove the required signed order, passivity, cancellation, or current budget without absolute-value or divisor-fitted replacement? |
| `COF` | Can one source-selected cofinal family control every ground, escape, scale, aperture, or moving-degree direction rather than one finite packet or trial state? |
| `LAND` | Can source coefficients, multiplicity, prime/depth labels, and orientation survive the required singular boundary, closed-graph, determinant, or physical landing? |
| `ORIENT` | Can the source produce the reflection-odd, off-diagonal, noncentral, higher-compound, or order-sensitive incidence erased by scalar and diagonal receivers? |
| `COMP` | Can a relation proved on finite stages descend through genuine infinite completion, ancestry, or semantic identification without becoming copywise RH? |
| `DYN` | Can the full nonlinear physical source produce the selective scattering law, rather than a target-fed pole, equilibrium, or kinematic classifier? |

These gates are coupled, not a partition. `LAND` is the source/receiver firewall; `ORD`, `COF`, and `ORIENT` are the three dominant mathematical burdens; `COMP` is the infinite-limit form of the firewall; `DYN` is the physical specialization of `LAND + ORIENT`.

At coarsest honest resolution they form two coupled problems:

1. **Source production:** derive a quantitative reflection-sensitive normal datum from literal source (`ORD + ORIENT`, or `DYN`).
2. **Global faithful propagation:** carry that datum through every required scale, state, and completion without loss or copywise fitting (`COF + LAND + COMP`).

Most labels change only carrier used for one of these two problems. A mathematically independent route would need a genuinely different source producer or a genuinely different global propagation theorem, not another exact receiver.

### Shared receiver complexes

| Receiver complex | Branch and candidate labels sharing it | What is genuinely common |
|---|---|---|
| Four-unit Ward/boundary fracture | CCM-FU, G, P, CFI, MSC, parts of O and WBF | Augmented Ward/Schur, principal-relative capacity, and physical residual formulations are exact RH receivers. Distinct labels differ in the proposed source producer. |
| Global Weil/ground/paired-kernel selection | C1, O, Q, CLG/TTF, UEB, SV2, FD2, S6F | Finite positivity, real-rooted completion, explicit seeds, and finite inertia do not control the whole cofinal ground or negative direction. S6F supplies infinite source orientation, but not its Xi/Weil landing. |
| Cofinal approximation/Hankel/Sonin selection | NB/BD, F2, STC, CSB, U, TK, BSH, SEC, BPC, MPLF | Finite sections and moment packets are abundant; missing law selects one compatible cofinal source family and controls its moving cost. |
| Singular Green/BV/Stokes/completion descent | CDC, L, P, PSRC, SC, PCS, TCD, JAS, XST, NDS, KMSS, WBF, completion survivors of R | Finite exactness, Stokes object descent, and L's completed Meyer–Tate differential, singular Gamma-six graph, and physical transport exist. Missing law forces the surviving class to vanish or untwist from source, zero-independently, without erasing coefficients. |
| Prime/Wold signed incidence | D2, E, G-CE, SP-E, SCE, T1, T2, HC, BW, PEP, PPM, HJ, EWQ-V, LI | Same arithmetic burden appears as Hall transport, signed current, phase gradient, free-sector passivity, or coefficient order. |
| Global operator/determinant occurrence | C1, FD2, IRK, W1C, K-RVM, APF, WS2, LI | Every exact self-adjoint Xi determinant carrier has the canonical singular values, exact Schatten abscissa one, genus one, and logarithmic weak-trace law. Trace-class completion preserves weak-Schatten membership and exact measurable logarithmic residue even after passing to modulus square. APF supplies a source Fredholm index and trace; WS2 supplies determinant-grade trace-class relocation. Neither supplies source occurrence/annihilation without ordered-zero or divisor input. |
| Nonlinear scattering selection | HB, FZZ-P, PW-B | Fixed-scale, equilibrium, diagonal, all-pass, copywise balance, and mere mixing are blind. Every HB sector mixes on its adaptive clock; passive stationary mass preserves the off-line chiral defect and finite local/finite-energy returns decay. Only a source-derived common-clock law together with control of a genuinely nondecaying threshold channel can orient the divisor. |

The complexes overlap: P lies in Ward and singular-descent families; WBF lies in Ward, Wold, and completion families; C1 lies in global-ground and operator-occurrence families. Endpoint equivalence proves shared receiver ownership, not shared producer independence.

Route R is terminal as an independent intrinsic producer. Its singular corona, squarefull Stokes normality, information-escape, and two-clock transgression theorems sharpen the completion interface but do not reopen it: every flatness/globalization condition is still central-grade selection. Those survivors feed candidate JAS through a changed paired/cohomological interface. Route K is terminal in quadratic form; K-RVM/WS2 is a different infinite paired operator candidate. XST isolates theta-spin inheritance as a candidate topological source interface. NDS retains multiplicity only in the scheme-theoretic conductor/nearby-cycle channel because every reduced nodal fibre is identical. OPUC’s explicit circle carrier is complete, but both reflected positivity and its sharp radial-Poisson disintegration are exactly RH. Fixed-scale FZZ and Vaidya selection are blind; FZZ-P survives through universal horizon-dilation completeness.

### Live-branch open cores

| Branch | Gates | First independent open core |
|---|---|---|
| CCM-FU | `ORD COF` | Uniformly control in vertical height the surviving centered completed-Chebyshev current at one fixed aperture, while retaining the exact lower/upper Möbius shift cancellation; polar assembly and terminal flux are already closed. |
| C1 | `COF ORIENT` | Construct a literal-source global positive cutoff or signed correction converging to the Weil distribution, and exclude cofinal two-pole antisymmetric escape. |
| CDC | `ORIENT COMP` | Prove the canonical pre-divisor orientation potential descends through the stationary repair semantics, or satisfies three-slot proof erasure, on every closed Xi-error fibre. |
| D2 | `ORD ORIENT` | Prove literal prime–Gamma free-sector passivity above 233/20 inside strict off-critical leakage-cone interiors. |
| E | `ORD COF` | Define one fixed source relation on central squarefree Wold sectors and prove unit load, interval Hall expansion, co-moving cutoff flux, and half-power Gibbs cost for that same relation. |
| NB/BD | `COF` | Construct source-selected finite Nyman–Beurling/Báez–Duarte approximants with distance tending to zero. |
| F2 | `COF LAND` | Produce one source-derived cofinal Sonin aperture section, positive aperture barycenter, or all-moment weld into the continued prime–Gamma germ. |
| STC | `COF LAND` | Identify the target-free fixed-prime Gamma-six/Sonin exterior lift with a canonical all-prime seam, or construct an all-prime source seam, then prove the sub-root Calkin law required by coherence. |
| CSB | `COF LAND` | Find cofinal degrees and apertures with bounded Bernstein source/target discrepancy. |
| G | `ORD ORIENT` | Prove an independent eventual four-unit Ward bound or equivalent signed order on canonical prime-log samples. |
| G-CE | `ORD` | Uniformly bound the normalized signed Möbius–divisor half-order Abel moment. |
| L | `LAND COMP` | Prove a source-selected fixed-system Stokes theorem annihilates the already-constructed Meyer–Tate/Green boundary under the actual Gamma-six/Sonin reader; equivalently untwist genuine covariant Gamma holonomy without assuming neutral grade. |
| O | `COF LAND ORIENT` | Land the source-self-polarized quadratic determinant coefficient-faithfully in the linear actual-head/restricted-Weil floor, then control every near-ground direction. |
| P | `ORD LAND ORIENT` | Transport the universal source Burnol Gram/cubic budget to the actual completed-Xi boundary; equivalently prove the curvature-normalized completed-flux budget on the two tails `abs(Im s) > 233/20`. |
| Q | `ORD ORIENT` | Prove source nonnegativity of the explicit exterior paired diagonal, equivalently passivity of every finite paired-value matrix. |
| CLG/TTF | `COF ORIENT` | Upgrade pointwise nonnegativity of the theta first-moment kernel to positive semidefiniteness of every finite Bezoutian/Krein-difference packet, equivalently exclude every cofinal regular two-pole escape. |
| HB | `ORIENT DYN` | Derive from the complete nonlinear theta backreaction a common standard quadratic Hawking clock for every bright sector, equivalently exclude higher coupling-order jumps, and prove that no source-derived nondecaying threshold channel cancels the controlled stationary chiral defect. |
| SP-E | `ORD ORIENT` | Compare exact signed prime dilation flux with the continuum increment and obtain a uniform amplitude imbalance. |
| SCE | `ORD` | Prove the source checkpoint conjugate is at most the checkpoint moment, or a source recursion forcing it. |
| T1 | `ORD COF LAND` | Transfer the exact two-edge smooth AFE to the affine/core-current carrier, then prove signed short Möbius-block cancellation while retaining the combined current. |
| T2 | `ORD COF ORIENT` | Derive the inverse-log adjacent defect from actual prime shells, sum it at critical weight, and prove signed subhalf continuation. |
| U | `COF` | Prove a cofinal moving-degree source-price/recession law that contradicts the parabolically synchronized strict-frontier renewal phase forced by false RH. |
| HC | `ORD ORIENT` | Build a confluent horizontal divided-difference/log-derivative packet with a subquantum estimate, or prove absolute prime–Gamma collision-current summability. |
| SV2 | `ORD COF ORIENT` | Exclude every finite tail-certified prime-side negative Pick certificate at positive rational shift and Gaussian-rational Euler nodes; alternatively finish both projective charts. |

## Live branch architectures

### CCM-FU — completed current and fixed-aperture Suzuki checkpoint

**Architecture.** Completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoint current → signed event curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.

**Proved frontier.** Critical-chord measure, completed Riesz graph energy, coherent prime–polar–Gamma boundary transport, adaptive cofinal Suzuki landing, signed second-grade cancellation, and exact lower/upper Möbius shift incidence are formal. Mass-shifted Stieltjes integration splits the finite prime source into explicit polar boundary value, terminal completed-error flux, and centered completed-Chebyshev current. The polar term converges exactly, terminal flux tends to zero unconditionally, and the surviving centered current is absolutely integrable at every fixed complex time. Genuine adjacent aperture cells force sharp harmonic endpoint-jump lower bounds on physical fusion energy and normalized dispersion; any energy upper bound gives the corresponding pointwise square-root stability bound. Separately, the arithmetic prime deck orbit gives a target-free paired Fredholm index of signs `-1/+1`, reflection by adjoint, compact-stable odd orientation, and an exact source trace whose Xi multiplier is downstream. CCMGeneralizedVonKoch and CCMSharpPrimeWindowSquareEnergyZeroWidthEquivalence identify Xi width with a prime-window square-energy abscissa and make zero-width/subpower control exactly RH.

**Open core.** Retain the singular lower/upper shift cancellation in one fixed-aperture moving affine current and prove a bound uniform in vertical height for the surviving centered error current. Polar assembly, terminal flux, and fixed-time integrability are no longer open.

**Boundary.** Generalized von Koch, sharp prime-window zero-width, and vanishing of every Fredholm source-trace coefficient are exact receivers, not weaker producers. Fixed positive even shifts, regular source fusion, and universal checkpoint boundedness already hit RH or a formal no-go.

### C1 — class-space quotient and global Weil positivity

**Architecture.** Completed theta/prime–Gamma source → finite adelic bands and trace formula → global class-space quotient/intersection pairing → positive Weil distribution or real spectral realization → RH.

**Proved frontier.** Finite-stage adelic bands, support/Fourier intersection, rapid trace error, finite trace formula, and abstract positivity from convergent positive cutoffs are formal. RouteCHorizontalChargeInterimVerdictPackage supplies the Poincaré–Lelong current, thin-slice horizontal charge, collision conservation, and exact intersection-versus-quotient multiplicity mismatch.

**Open core.** Construct the global cutoff or signed correction from the literal arithmetic source and prove convergence to the Weil distribution while excluding the two-pole antisymmetric escape.

**Boundary.** The raw positive/passive Gamma-sewn supercarrier is terminal: four reflected Stokes atoms already exceed completed zeroth mass. C1 remains live only after allowing source-derived deletion, reweighting, signed correction, or an indefinite intermediate form.

### CDC — constitutive dagger confluence

**Architecture.** Prime-power half-density mate gain → canonical signed pre-divisor potential on two normal repair histories → semantic dagger descent or three-slot proof erasure on completed Xi-error fibres → neutral radial grade → RH.

**Proved frontier.** Finite critical completion supplies one semantic repair with two executable presentations. The canonical orientation potential is defined on the whole parameter plane, is source-calibrated by the actual purified failure-nerve gain, and splits the two metric provenances exactly off the critical line. Pointwise calibrated dagger confluence and canonical proof-erasure consistency each classify the critical line, and fixed pre-divisor descent over all Xi fibres implies RH.

**Open core.** Prove from the literal completed arithmetic semantics that this canonical pre-divisor potential descends, or obeys three-slot proof erasure, on every closed Xi-error fibre.

**Boundary.** Arbitrary pointwise calibrated confluence is exactly the critical-line equation and supplies no producer. Two-slot symmetrization is automatically blind. The only live mechanism is one fixed source potential followed by an independently proved semantic descent law.

### D2 — continued prime–archimedean free-sector passivity

**Architecture.** Continued prime–arch trace → critical fixed-locus Poisson reserve plus free reflection-orbit trace → leakage-cone-localized anti-Herglotz endpoint → RH.

**Proved frontier.** Fixed/free split, complete critical reserve, verified-height band, exact cone boundary, and cone exterior are formal.

**Open core.** Prove from the literal prime–Gamma source that only the free sector is passive above 233/20 and only in strict interiors of off-critical Lorentzian leakage cones.

**Boundary.** Global passivity and unrestricted positive-real formulations are fitted RH receivers. D2 survives because its remaining law is source-localized, not because Lean proves it weaker.

### E — squarefree Wold transport

**Architecture.** Squarefree depth-zero Wold source → opposite-sign half-power supply → fixed physical integer relation → normalized Hall transport across the moving friable/one-large-prime cutoff → Möbius cancellation → RH.

**Proved frontier.** Two-or-more-large-prime Gibbs remainder, positive-depth prime-power tail, prime-anchor capacity, every fixed off-normal Wold breadth tail, coprime opposite-sign supply, finite Wold-moment readers, and exact patch-seam coboundary are formal. Finite differential-algebraic Euler-germ constructions are blind because the depth-zero source has a free infinite prime-clock orbit. Visible-coprime Möbius–Laplace pairs give an exact two-variable renewal law and a divisor-selected mixed-jet orientation receiver.

**Open core.** First declare one relation independently of observed partial-sum imbalance. Then prove, for that same relation in the central normal Wold sector at half-power scale: row load and physical co-degree at most one; interval Hall expansion by distinct opposite-parity integers; co-moving cutoff flux with charges −1 and +1; and total mixed-difference Gibbs cost of half-power order.

**Boundary.** Existential complete-bipartite flow merely restates Möbius imbalance. More moments, patch-seam estimates, scalar phase nodes, static rectangles, finite Euler exhaustion, and G114 mean-square control do not produce the relation. On squarefree hard support valuation depth is identically one; breadth and physical incidence carry the hard cancellation.

### NB/BD — Nyman–Beurling and Báez–Duarte approximation

**Architecture.** Fractional-part dilation source → discrete Nyman–Beurling spans → vanishing Báez–Duarte distance → RH.

**Proved frontier.** Exact L2 carrier, Gram and detector calculus, quantitative off-line floor, Möbius coefficient series, beta-wavelet realization, and fixed Gibbs-channel realization are formal.

**Open core.** Give explicit source-selected finite approximants whose discrete distances tend to zero.

**Boundary.** Current unconditional coefficient decay is only half-order. The full weighted-Mertens tower giving critical decay is exactly RH; fractional-part identities and strip-zero integral equations alone do not select the abscissa.

### F2 — Sonin trace-moment weld

**Architecture.** All-prime principal-relative Sonin residual → positive trace-class energy → intrinsic Hankel moment curve → continued prime–Gamma moment germ → RH.

**Proved frontier.** Actual-Ka phase diagram, bounded strip jets, two-point completeness, divisor/triple Hardy representatives, quotient minimality, conductor pairing, and finite moment transfer interfaces are formal.

**Open core.** Construct one source-derived cofinal aperture section, positive aperture barycenter, or equivalent all-moment weld identifying carrier powers with prime–Gamma moments.

**Boundary.** Bounded or sublinear compact Sonin completions have wrong asymptotic order, lose the floor, or collapse source. F2 is the surviving cofinal all-prime architecture.

### STC — exterior Sonin seam coherence

**Architecture.** Finite Euler/Sonin chart → two one-particle all-prime sections → decomposable exterior prime-pair seam → Calkin sub-root growth → prime-potential coherence → RH.

**Proved frontier.** Exterior factorization, compact-resistant lower bound, coherence theorem, and global RH endpoint are exact. For the literal Gamma-six source at primes two and three, Lean constructs a target-free, reflection-odd Sonin exterior commutator before divisor selection. It is independent of valuation depth, has an exact nonzero Calkin floor off neutral grade, a uniform Calkin upper bound, and automatic cofinal completion.

**Open core.** Prove that the fixed-prime target-free lift is the restriction of the canonical all-prime exterior seam, or construct that all-prime seam directly from source. Then derive the cofinal sub-root Calkin law used by the coherence endpoint.

**Boundary.** Fixed two-prime/depth Calkin control is formal but does not identify or control the all-prime seam. Strong or weak compact approximation is too weak; only Calkin-norm control retains the obstruction.

### CSB — cofinal Bernstein source/target comparison

**Architecture.** Coupled all-prime Sonin channel → positive master effect → normalized Rényi/Hausdorff moment law → cofinal Bernstein packet comparison → prime–Gamma endpoint → RH.

**Proved frontier.** The unconditional endpoint cone contains the full 23 by 58 rectangle; order 24 reduces to an explicit low-zero competition. Finite Bernstein and moment machinery is complete.

**Open core.** Produce cofinal degrees and apertures with bounded source/target Bernstein discrepancy.

**Boundary.** The universal residual tail is RH-equivalent. Enlarging finite rectangles does not establish the cofinal source law.

### G — Ward orientation

**Architecture.** Suzuki/Möbius/Gamma source → marked pre-scalar or signed-channel carrier → exact Ward landing → critical-wall orientation → RH.

**Proved frontier.** Detection covers, completed Ward landings, horizontal charge quantization, and several equivalent scalar/matrix tail endpoints are formal. The finite-prime completed tangent has one upper-half-plane Euler pole with residue `-2 * I`; all-prime completion cancels that pole and replaces it by the shifted Xi divisor, with residue `-2 * I` times analytic multiplicity and holomorphy exactly off that divisor. RouteCHorizontalChargeInterimVerdictPackage collects the source collision current but does not bound it.

**Open core.** Independently prove eventual four-unit Ward scalar control on canonical prime-log samples, or a genuinely source-derived signed order with the same landing.

**Boundary.** Universal four-unit control is exactly RH. BV prime-window ordinary-Hardy landing, positive diagonal repair, and finite local packets do not supply it.

### G-CE — coherent Euler half-order Abel moment

**Architecture.** Prime-free divisor defect → signed Möbius floor-dilation action → half-order Abel moment → coherent unit-Riesz/Green/Chebyshev boundary → RH.

**Proved frontier.** Prime-free defect is unconditionally half-order, and its coefficient-faithful weld to the coherent Selberg moment is exact.

**Open core.** Uniformly bound the normalized signed Möbius–divisor half-order Abel moment.

**Boundary.** Absolute channel estimates erase the dilation cancellation. Repackaging the same normalized moment is an RH receiver.

### L — singular Green/BV-to-physical descent

**Architecture.** Completed Xi Green primitive plus BV/co-Poisson boundary → resolved rational-adelic target with prime, depth, multiplicity, and Xi-jet provenance → singular comparison → existing Burnol/Deninger physical reader → conormal defect zero → RH.

**Proved frontier.** Completed Green operator and nonzero primitive; coefficient-faithful Green-to-Calderón–Witt incidence; relative Tate boundary; Burnol conormal identity and classification; ordinary-integer Hochschild boundary; all-cross-prime Koszul cycle; strict resolved-Xi rational-adelic chain map; and generic all-prime three-term cotangent/Noether differential with d-squared zero are formal. Lean constructs the source-selected cofinal singular Gamma-six graph and its unique continuous transport to the fixed Sonin exterior commutator. It also constructs the literal cofinal Tate-naturality differential: ordinary-prime CCM cycles map densely to the graph, retain their coefficients, and converge to the completed Meyer–Tate/Green vertical boundary. Every finite chain and its completed limit have exactly the same strict actual-Gamma/Sonin readout. On each Xi copy this physical image vanishes exactly on the critical line. Finite Xi-jet analysis is multiplicity-complete: off-line vertical defect rank equals analytic multiplicity, any faithful finite repair memory has at least that dimension, and visible horizontal-anchor rank plus unresolved rank equals multiplicity. A submultiplicity anchor leaves a genuine horizontal pair even under perfect vertical gluing.

**Open core.** Prove from the pre-divisor source one fixed-system Stokes theorem that annihilates this already-constructed completed arithmetic boundary under the existing Gamma-six/Sonin physical reader. Equivalently, prove the genuine covariant Gamma local system untwists to the fixed Deninger system on every Xi fibre without assuming neutral grade. Prime, depth, multiplicity, nonzero Xi coefficient, and the multiplicity-complete horizontal anchor must survive.

**Boundary.** Covariant Stokes flatness on each fibre is unconditional, but its holonomy is the centred grade; passage to the fixed source system is exactly the critical-line condition. Any trace-ideal-preserving comparison leaves the physical Calkin class unchanged, and an exact regular lift exists exactly at neutral grade. Vertical gluing alone conserves arbitrary horizontal defect, while multiplicity cannot dilute it. Generic mapping cones, Koszul exactness, cyclic traces, KMS untwisting, or declaring the physical vector a boundary merely relocate or erase the defect. Differential, singular carrier, dense source provenance, and physical landing are closed; only source-forced fixed-system annihilation remains.

### O — self-polarized restricted-Weil ground selection

**Architecture.** Restricted-Weil operator → canonical actual-head packet → rank-two PSD/chiral carrier → complex Dirac plane → source-self-polarized determinant → coefficient-faithful linear restricted-Weil landing → nonnegative ground floor → RH.

**Proved frontier.** Finite restricted-Weil matrices, reflection, real-rooted completion, nested-floor antitonicity, no-evacuation, pole-uniform prolate comparison, finite defect mass, endpoint envelopes, and source-self-polarized determinant sign are formal. Every nonempty prime-power packet has determinant strictly negative off center and zero only at center. HTWeilCompactDetectorNearRadicalAlternative proves that compactly invisible near-ground sequences must escape every compact or approach the radical.

**Open core.** First prove the quadratic self-polarized scalar lands coefficient-faithfully in the linear actual-head/restricted-Weil block, including spectral integration and collar control. Then classify all near-ground sequences and exclude both compact escape and radical competitors so the explicit source direction controls the whole ground space.

**Boundary.** More seed asymptotics, finite real-zero determinants, or upper Rayleigh bounds cannot give the needed lower floor. Finite-Blaschke inertia, literal kernel negative squares, exact leakage rank, and projective horizontal-layer limits close finite receiver geometry under Hardy coprimality, not arithmetic ground selection.

### P — cubic prime–Gamma collision

**Architecture.** Literal von-Mangoldt prime–Gamma cubic carrier → universal Burnol conormal Gram square and strict subquantum budget → completed boundary-value/curvature transport → high-frequency completed-flux dissipativity → exclusion of strict-right zeros → RH.

**Proved frontier.** Complete non-diagonal collision Gram, global source trace budget, recurrent source packet, cubic subquantum bound, and coefficient-faithful prime-depth identification are formal. Every finite primitive Euler packet is the literal Burnol inverse-window Gram, hence positive semidefinite with exact balanced-source trace and one global budget below two; no Xi-zero expansion enters. The CCM cubic Green test identifies the same source mass before any divisor and isolates only polar–Gamma shorting. Curvature normalization removes the universal first jet and is gauge invariant. Source geometry proves the completed-flux budget throughout `abs(Im s) ≤ 233/20`; the global RH-equivalent budget is therefore exactly its two exterior tails. Separately, two wild-saddle logarithmic steps are the sharp minimum needed to reach the ordered reciprocal-Xi operator modulo trace class, while the surviving source determinant anomaly is positive and summable.

**Open core.** Transport the universal Burnol Gram/cubic budget coefficient-faithfully from canonical Euler nodes to the actual completed-Xi boundary and short the polar–Gamma surplus. Equivalently, prove the curvature-normalized completed-flux budget for `abs(Im s) > 233/20`. Carrier construction, prime summability, central band, and source Gram positivity are closed.

**Boundary.** Assuming trace capacity or the full curvature budget is exactly RH. Depth-zero and boundedly mixed Route-P operators cannot be trace-class-relocated to ordered Xi; finite-rank and trace-class perturbations preserve weak-Schatten-one membership and measurable logarithmic residue, including for positive modulus-square energy. Scalar wall-time or tau-germ rescaling is excluded by projective two-jet mismatch, and its forced first-jet-normalized Malgrange correction has positive quadratic curvature. Two-step wild relocation gives determinant-grade proximity, not determinant or spectral equality. Regular endpoint extraction, finite positive measures, common-modulus repair, source-normal recovery transport, and marginal-gauge correction do not create the completed landing. XiPrimeMarkedAllOrderIncidenceFactorization sends any all-order Route-K burden into this same seam.

### Q — exterior paired-value passivity

**Architecture.** Continued Hurwitz/Cauchy source → countable Gaussian-rational Euler-pole paired kernel → exterior paired passivity → orientation zero → RH.

**Proved frontier.** Explicit paired kernel, finite matrices, Gaussian-rational realization, and exact collapse to the Xi orientation endpoint are formal.

**Open core.** Prove source nonnegativity of the exterior paired diagonal, equivalently passivity of every finite paired-value matrix.

**Boundary.** Current nonnegativity proofs pass through Xi-specific RH capstones. W2C, UEB, and CLG identify the same receiver under different congruences but do not source its sign.

### CLG/TTF — completed theta Bezoutian no-escape

**Architecture.** Literal completed theta source → neutral correlation flux/Xi Bezoutian → invertible diagonal congruence → even-minus-odd two-channel Weil energy → RH.

**Proved frontier.** The actual theta-tail first-moment kernel is pointwise nonnegative, symmetric, reflection invariant, and exactly a two-channel Krein difference. Double Laplace transform identifies its matrix entries with the removable completed-Xi Bezoutian. RH is equivalent to positive semidefiniteness of every finite Bezoutian, equivalently every finite two-Volterra Krein-difference matrix, over every cofinal aperture. Safe-boundary Poisson representation, de-Poissonized prime atoms, and finite-packet survival are formal. An off-line fibre produces a regular two-pole sequence whose source energy tends to negative multiplicity.

**Open core.** Prove finite-packet positive semidefiniteness from the literal theta first-moment source, or equivalently exclude every admissible cofinal two-pole sequence with even energy tending to zero and odd energy tending to its positive fibre multiplicity.

**Boundary.** Pointwise nonnegativity of kernel entries is not matrix positivity. Safe-half-plane positivity is divisor-indexed and horizontally blind; fixed finite apertures and finite packets do not prove cofinal no-escape.

### HB — theta-cusp Hawking causal scattering

**Architecture.** Literal theta-cusp source → modular topological-black-hole pole/shadow pair → exact causal gravitational Jost and bright mediator channels → full nonlinear theta-mirror return → source-synchronized standard quadratic Hawking clock, equivalently theta-shadow confluence → RH.

**Proved frontier.** Every Xi divisor is a modular topological-AdS pole with shadow zero and exact opposing QNM branches. Each upper resonance is excited by a finite-energy causal Hardy wavepacket. Scalar and gravitational hypergeometric Jost descendants are simple physical-boundary zeros/inverse-Green poles, with accidental Gamma collisions excluded. The fundamental chiral radial kernels are nonzero in both mediator rows, and one completed-Eisenstein input makes both rows bright; their factorized two-frequency horizon determinant vanishes exactly on the critical line. Equality of reflected and functional mediator pole multiplicities is another exact RH receiver. For the direct gravitational return, the cross-branch moment is `-4`, the chiral mass-jet numerator is `-12/(Q+2)`, and nonzero absorbed seed gives a simple opposite-branch pole and nontrivial Evans/Cayley return. Passive stationary absorbed mass rescales the chiral defect by the strictly positive factor `1 + M`, so it remains nonzero and eventually oriented on every tilted fibre. Every finite local pump monomial is delay-damped; finite-energy continuum response is integrable, factorized, uniformly damped, and its finite local delayed remainder tends to zero. Any asymptotic cancellation must therefore converge to one explicit nonzero threshold countervalue. The topological mass return has a unique unit-modulus Cayley scattering matrix at every divisor, so its norm is blind; its two-mass spectral-flow area is strictly positive exactly off the critical line, but remains a divisor-fed classifier. The topological Starobinsky defect factorizes into tilt times a mass mismatch, while two distinct masses force criticality. Full nonlinear mirror mixing itself is unconditional: every tilted sector mixes after its sector-dependent adaptive clock. RH is exactly synchronization of all sectors to the common quadratic/van-Hove clock, equivalently absence of higher coupling-order jumps. A controlled bright factorized block and adaptive mixing therefore exist; the nondecaying threshold source and common-clock law do not.

**Open core.** Derive from the complete nonlinear Einstein–Teukolsky/theta backreaction that every bright sector has first nonzero coupling order one and hence the same quadratic Hawking clock. Stationary and decaying-return channels are no longer open. Remaining physical alternative is a genuinely nondecaying threshold/inhomogeneous source whose exact limit cancels the stationary defect or delays it to higher coupling order. Exclude or orient that channel from the literal theta source. A sufficient realization is a nonzero `xi -> -xi` angular component carrying Noether charge `-2*xi`; the common-clock statement is the invariant endpoint.

**Boundary.** Pole/Jost existence, causal excitation, mediator brightness, direct and finite-energy continuum control, passive stationary persistence, finite-coupling mixing, adaptive-clock existence, and sectorwise nonzero response are not open. Mere mixing and mass-Cayley unitarity are blind; the two-mass area detects tilt only after a divisor copy is supplied. The raw continued horizon eigenvalue is not self-adjoint even under RH; only the de-aliased quadratic source weight has the correct reality endpoint. Scalar determinants, unsigned optical energy, KMS/passivity, diagonal completion, multiplicative phase, homogeneous AIME, bare Starobinsky phase, and copywise reciprocity remain shadow-blind or exact RH receivers. A nondecaying threshold channel can still change coupling order or cancel the stationary limit; excluding it requires the full source, not another finite local decay estimate.

### SP-E — signed prime dilation versus continuum

**Architecture.** Natural Suzuki reporter → coherent prime outgoing amplitude minus regular-screw continuum → completed Green/Ward wall → RH.

**Proved frontier.** Prime increments equal quarter-dilation gain minus debt; source and continuum channels and their exact signed flux are formal.

**Open core.** Compare the signed prime flux with the continuum increment and deduce a uniform amplitude imbalance without separating positive pieces.

**Boundary.** Raw Cauchy energy diverges, and the unrenormalized rectangular Ward defect tends to negative infinity along aperture 8n. Anchor-visible linear mass must be removed before a cofinal Gram limit.

### SCE — strict-convex checkpoint energy

**Architecture.** Mangoldt event history plus archimedean reservoir → unique strict-convex checkpoint → restricted Legendre conjugate → nonnegative checkpoint floors → RH.

**Proved frontier.** Strict convexity, unique minimizer, conjugate calculus, Bregman drawdown, and exact RH endpoint are formal.

**Open core.** Prove source-first that checkpoint conjugate is at most checkpoint moment for every N at least two, or derive an event recursion forcing it.

**Boundary.** Drawdown controls displacement from the minimum, not its absolute sign. Universal checkpoint nonnegativity is already exactly RH.

### T1 — theta-tail core current

**Architecture.** Finite Xi-Taylor/theta-tail source → exact reflection bridge → zero-free full-density channel plus canonical transfer current → raw core-current bound → RH.

**Proved frontier.** Support-restricted Vaughan Type-I totals, both Type-II block orientations, gap collapse, explicit fibre-power bounds, full-density aggregate current, and reflection transport are formal under their stated phase hypotheses. The exact Gaussian smooth AFE and both explicit Dirichlet-series edges are formal throughout the open critical strip.

**Open core.** First transfer the exact two-edge smooth AFE coefficient-faithfully into the affine mean-square/core-current carrier. Then prove signed short Möbius-block cancellation that preserves the combined top-row/finite-translation current.

**Boundary.** AFE construction and dual expansion are closed; their carrier handoff and signed cancellation are not. Unsigned block estimates and universal current sublinearity do not discharge the source law; the latter is RH.

### T2 — ordered-prime shell defect

**Architecture.** Ordered-prime Wold source → inverse-log adjacent defect → literal von-Mangoldt slice → forced second Maynard alternative → critical gap energy → residual Hardy continuation/ODE → RH.

**Proved frontier.** Arbitrary-order localization, shell cap, exact base-or-second dichotomy, and critical-gap continuation interfaces are formal.

**Open core.** Prove actual ordered-prime shells supply the inverse-log defect and scale envelope, sum the result at critical weight, and establish signed or renormalized subhalf continuation.

**Boundary.** Zeta/log atoms and block-dependent order are no longer the obstruction. The arithmetic shell defect and signed continuation are.

### U — adaptive shifted-Xi Hankel frontier renewal

**Architecture.** Shifted-Xi hard-edge source → canonical adaptive Hankel admission ladder → false-RH cofinal occupied terminal frontiers → source-priced finite-contact renewal inside the intrinsic parabolic cone → incompatible global source-work/recession law → RH.

**Proved frontier.** Every occupied strict terminal frontier is a singular positive-semidefinite face carrying a source-selected finite first contact, exact positive adaptive mixed/completed terminal charge, and contact-order residue. False RH forces such priced strict renewals cofinally; every canonical frontier lies below an explicit quadratic degree horizon, so this phase is confined to `sqrt mass = O(degree)`. One universal parabolic source floor holds simultaneously in every degree, and the forced fourth-power renormalized source action diverges on every cofinal positive-block schedule. The source numerator is continuous and locally integrable, whereas division by the newborn admission norm gives a nonintegrable wall; arcsine-vacuum subtraction and trace renormalization preserve its positive residue. Every bounded germ gauge leaves the newborn normalized coordinate zero, while any finite nonzero normalization is unbounded with pole order equal to contact multiplicity.

**Open core.** Prove the missing cofinal upper accounting law that synchronizes moving contact degree, frontier mass, positive source price, and cumulative Jacobi dissipation. It must rule out the parabolically synchronized, source-priced renewal sequence forced by false RH; fixed-degree recession and pointwise eventual positivity do not control this moving diagonal.

**Boundary.** Local producer existence, cofinal admission, parabolic mass control, noncollapse, and singularity classification are closed. The nonintegrable wall is genuine rather than excludable by a bounded gauge. Arbitrarily delayed positive schedules show why fixed-degree limits alone are irrelevant; degree-only uniform positivity also fails. The remaining obstruction is quantitative inefficiency between priced Lipschitz persistence and positive-chamber travel along the canonical moving degree.

### HC — horizontal collision charge

**Architecture.** Two-prime/Cayley/Gauss–Hodge source → quantized horizontal collision charge → strict sub-two or absolute prime-summability law → RH.

**Proved frontier.** Horizontal charge current, conservation, intersection/product-versus-quotient mismatch, static Hardy leakage, finite Cauchy energy, shift cocycle, quartet curvature, Euler-orbit failure, Suzuki archimedean sign change, and floor–Möbius split are formal.

**Open core.** Construct a confluent divided-difference/log-derivative horizontal packet with a genuinely subquantum estimate, or prove absolute prime–Gamma source-loss summability.

**Boundary.** Standard Chen–Gupta–Li packets collapse reflection partners to one row and their Proposition 4.6 envelope is at least 288 throughout sigma at most one. They cannot merge the collision charge.

### SV2 — Suzuki projective limit and shifted-kernel inertia

**Architecture.** Literal Suzuki energy space → either a two-chart projective limit or rational shifted-Xi Euler kernels → finite Gaussian-rational Pick witnesses → exclusion of every strict-right divisor → RH.

**Proved frontier.** Canonical subsequences, projective Schur limits, point evaluation at Xi zeros, and the V(0) mass-plus-peak endpoint are formal. Conjugation-closed infinite tail products identify the literal shifted-Xi quotient with its infinite disk Blaschke quotient, and invertible Cayley congruence identifies the regular upper kernel with the arbitrary-inner generalized-Schur value kernel. RH is exactly vanishing of the literal anti-causal shifted-Xi leakage operator at every positive shift, including exceptional shifts. At every shift its complete finite negative-dimension profile and full finite-or-infinite rank index are exactly the uncancelled shifted-divisor leakage rank. At a nonexceptional shift this is literally the multiplicity-copy count of zeros beyond the transverse line. Restriction to the literal Euler half-plane preserves that profile; surviving negative correlation is necessarily nonlocal and begins at packet order at least two. Every fixed finite packet of tame isolated crossing layers has channel rank equal to total analytic multiplicity; its actual Gram defect and off-diagonal Gram tend to zero. Finite spectral peeling gives the corresponding identity-channel spectrum and exact multiplicity trace jump. On every finite transverse tail, the atomic Stieltjes mass is the exact drop in raw divisor count and, at nonexceptional higher shifts, that count is the literal kernel index. Every strict-right Xi zero admits a positive rational shift with a finite Gaussian-rational negative witness. Finite Euler products converge to the exact kernel, and any strict negative energy yields a finite prime packet with rational margin and certified tail. Hence failure of RH is exactly existence of a finite tail-certified prime-side Pick certificate.

**Open core.** Prove directly from finite Euler factors and the certified tail bound that no finite prime-side negative certificate exists at any positive rational shift and Gaussian-rational node packet. Alternatively complete the two-chart target identity and reciprocal convergence.

**Boundary.** Universal leakage vanishing is an exact RH endpoint, not an independent producer. Pointwise contractivity and one-node positivity do not imply matrix positivity. Cancellation-aware full rank, multiplicity-resolved packet peeling, rational nodes, and certified finite-prime tails remove divisor counting, crossing asymptotics, and analytic approximation as ambiguities. What remains is the arithmetic sign of explicit finite prime packets. A single-chart target has an unavoidable pole, and an infinite negative sector cannot be repaired compactly.

## Candidate interfaces

Candidate labels are not counted as live branches until a literal-source handoff and divisor-exhaustion theorem are formal. Gate incidence shows which candidates are alternate interfaces to an existing problem rather than independent routes.

| Candidate | Gates | Lean-derived mechanism | Exact missing theorem or terminal boundary |
|---|---|---|---|
| TK | `ORD COF` | Thermodynamic KMS response and moment limits. | Construct a source-derived growing KMS family; fixed KMS/passivity is horizontally blind. |
| FD2 | `COF LAND` | Finite det-two normal family with bounded energy and real-zero approximants. | Give the literal matrix family, uniqueness/convergence theorem, and uniform Hilbert–Schmidt cap. |
| BSH | `COF LAND ORIENT` | Boolean Sonin full-history section with adjoint mate. | Build the literal prime–Gamma section and prove mate-boundary vanishing. |
| CFI | `ORD LAND` | Complementary lower/upper floor–Möbius shift incidence. | Prove singular cancellation after moving affine normalization and feed CCM-FU. |
| UEB | `ORD ORIENT` | Pointed unit-Euler translated Xi Bezoutian. | Derive a source Gram factorization or positivity before divisor polarization. |
| PSRC | `LAND COMP` | Prime-shift residue graph closability. | Prove source closability of the singular residue graph; bounded Marcinkiewicz/Yoneda descent splits and is blind. |
| PBM | `COF ORIENT` | Prime-boundary monodromy escape. | Derive source cancellation or absence of quantized prime monodromy at infinity. |
| SC | `LAND ORIENT COMP` | Analytic Stokes microstalk/Witt carrier with exact object and morphism descent. | Construct the literal infinite prime–Gamma phase object, coefficient-faithful Xi landing/determinant, and global oriented form; raw positive completion is impossible. |
| PPM | `ORIENT` | Prime-power centered-mark collision. | Prove source forces a mark collision or finite monodromy before choosing a divisor. |
| IRK | `LAND COMP` | Irrational-rotation projective module and K-zero class. | Produce a source projective trace/Chern landing into the completed Xi endpoint. |
| HJ | `LAND ORIENT` | Hurwitz anchor-jet projective reflection. | Derive the projective anchor and reflection law from source before divisor selection. |
| BW | `COF LAND COMP` | Barrelled prime-depth Wold selection. | Construct a literal global barrelled-source certificate; bounded/subexponential depth transport is impossible. |
| MSC | `ORD COF ORIENT` | Moving-aperture Möbius signed-channel Schur projection. | Prove source covariance and a four-unit bound for the moving pointed pole/divisor packet. |
| PEP | `LAND ORIENT` | Projective Euler polarity on the negative Helson sheet. | Continue the source pole-free sheet through the strict right half-strip; paired norm is phase-blind. |
| EWQ-V | `LAND ORIENT` | Nonunitary Euler–Wick completed matrix/jet orientation. | Produce pre-divisor magnitude-changing incidence and an independent source vacuum before normalization. |
| PCS | `LAND ORIENT COMP` | All-prime co-shift secondary boundary complex. | Construct a singular/off-diagonal secondary class; regular finite algebraic exactness erases the obstruction. |
| SEC | `COF COMP` | One-ended adjacent-prime seam coherence. | Prove eventual source compactness of adjacent-prime seam coboundaries. |
| LI | `ORD LAND ORIENT` | Paired Cayley–Li coefficient orientation. | Give a coefficient-faithful prime–Gamma landing across s=1 and prove source order for all coefficients. |
| BPC | `COF LAND` | Bernstein–Pringsheim collar susceptibility. | Continue source susceptibility analytically through the critical collar. |
| MPLF | `COF LAND` | Complete prime-Laplace frame with finite Gram interpolation. | Derive uniform finite Gram bounds from the literal source and pass cofinally. |
| W1C | `LAND COMP` | Closed positive-ray weight-one Clifford operator. | Prove an arithmetic determinant/scattering identity for the closed operator. |
| TCD | `LAND ORIENT COMP` | Literal theta convolution with analytic full-jet defect. | Build a singular Hardy/RKHS lift preserving the complete reflected jet. |
| JAS | `ORIENT COMP` | Bifiltered cubical joint-ancestry completion with infinite reflected polarization. | Construct a zero-independent polarization on the synchronized finite-support/valuation diagram whose prime-Poisson first-jet shadow is closed, single-valued, nonzero, and source-linear. |
| K-RVM | `COF LAND` | Prime-indexed doubled signed Riemann–von Mangoldt operator and universal exact-Xi singular-value, Schatten, weak-trace, and genus-one laws. | Recover an exact carrier, eigenbasis, and determinant from prime source without importing ordered zero ordinates. |
| APF | `ORD LAND ORIENT` | Arithmetic-prime paired Fredholm index, adjoint reflection, compact-stable odd orientation, and source-first trace receiver. | Prove source annihilation of every trace Fourier coefficient and zero-independent Xi-divisor exhaustion. A zero-winding AF limit cannot nucleate the unconditional nonzero Xi boundary winding. |
| S6F | `LAND ORIENT COMP` | Divisor-free sixth likelihood jet with strictly positive odd supertrace after paying every negative-parity sector in infinite Fock completion. | Construct a coefficient-faithful landing of this completed odd weight into the theta Bezoutian, Weil form, or Ward boundary; positivity alone has no Xi incidence. |
| WS2 | `COF LAND` | Source-defined depth-two wild-saddle signed operator, sharp minimal trace-class relocation to reciprocal Xi, and positive summable quadratic determinant anomaly. | Derive an exact determinant/spectral occurrence law from source without the ordered-Xi comparison; trace-class proximity preserves residue but not spectrum or zeros. |
| FZZ-P | `COF LAND DYN` | FZZ scattering asymmetry, all-order Schwarzschild incidence, strict non-Markov response, and horizon-dilation completeness. | Prove no nontrivial cigar Mellin zero is missing from the real horizon spectrum and land the infinite response clock in the horizon/theta/Xi endpoint. |
| RBH | `COF LAND ORIENT` | Reflected bi-heat residue, exact full-window finite-part weld, multiplicity-exact completed jets, and reflected scale tomography. | Derive one pre-divisor source law forcing the two nonzero multiplicity-leading channels to be co-leading at every Xi divisor. |
| PW-B | `ORD ORIENT COMP DYN` | Finite-energy Parikh–Wilczek winding, Borel recurrence, partner-growth asymmetry, and gauge-invariant recoil holonomy. | Derive balance/flatness from source-first finite-mass evaporation or a global aggregate law; every copywise selector is exactly RH. |
| WBF | `COF LAND ORIENT COMP` | All-prime Wold boundary volume, thermofield sector fracture, and splitting-independent source-pointed normal extension jet. | Prove a depth-uniform source-normal completion/equicontinuity law that annihilates the conserved normal anomaly; global jet vanishing itself is exactly RH. |
| XST | `ORIENT COMP` | Literal theta half-density spin coupled to centered Xi monodromy, with faithful three-slot phase thinning. | Prove from closed completed-source error fibres, before copywise fitting, that every Xi fibre inherits ambient theta spin; universal inheritance is exactly RH. |
| NDS | `LAND ORIENT COMP` | Source-first Xi nodal family, non-erasing terminal conductor class, and second-order grade–phase receiver. | Construct the natural analytic conductor-to-nearby-cycle regulator and prove oriented scheme-theoretic coherence on every closed Xi-error fibre; reduced fibres are blind. |
| KMSS | `LAND ORIENT COMP` | Order-independent descent of the all-prime graded-skew Koszul cup into one neutral mixed jet. | Construct one nondegenerate, zero-independent, functorial source lift; arbitrary zero-specific lifts include the trivial lift and universal completion is exactly RH. |

### JAS — joint-ancestry architecture

**Finite source skeleton.** GammaSewnSynchronizedLcmContraction assigns one coordinate to every finite prime support; support cardinality is the Rees grade and insertions give a flat Boolean-cube connection. GammaSewnSynchronizedRecoveryContraction gives a fixed nonexpansive Möbius-signed all-finite-support transport preserving continued Xi-Ward first jets.

**Why one Hilbert graph is insufficient.** GammaSewnXiShiftTangentHilbertKernel proves the exact three-prime determinant contains a rooted second compound and an independent pure tangent third compound. Pairwise Gram data loses source information. XiCTaylorThetaTailCompletedValuationReflection supplies genuine infinite square-index, product-fibre, and valuation-depth support.

**Completion boundary.** Fixed-grade evaluation is split-surjective with zero cokernel and zero degree-one Tor, yet a nonzero tail/completion-migration class survives. Thus the defect cannot live in ordinary algebraic exactness. Conjugate homogeneity alone already forbids a nonzero one-leg reporter on a strict-right fibre, while paired Hermitian incidence survives. Every descended linear observer of the closed two-clock relation is zero, but the oriented clock-area cocycle persists one degree higher as a nonzero relation-kernel character. Off-line abelian information escape is exactly prime-tail diagonal escape: unbounded conditional information can hide in vanishing literal source mass. These theorems force any JAS successor to be paired, cohomologically transgressed, and completion-sensitive.

**Receiver.** XiJointAncestrySuperselection proves that a nonzero closed source-linear sewing of reflected prime-Poisson sectors exists exactly on the critical wall. Reflected prime-source measure class, closed sewing, all-prime Calkin compactness, information tightness, and collective compactness are one local modular-ancestry condition. Internal-only divisor syndrome is equivalent to such sewing. Every hypothetical right-half Xi divisor retains a nonzero square-zero internal channel while simultaneously failing completion, modular/Rees, and prime-source ancestry.

**Open core.** Build one divisor-independent infinite-support reflection polarization on the bifiltered diagram:

- prime-support/compound order in one direction;
- valuation/Rees depth in the other;
- agreement with every finite Boolean face;
- retention of all compound orders;
- realization of the completed theta value/derivative current;
- provenance-continuous completion with no vertical graph ambiguity;
- nonzero closed source-linear prime-torus first-jet shadow.

**Boundary.** The fixed recovery transport is first-jet transparent and cannot cancel transverse defect. The normalized cofinal anomaly is the same scalar in every Xi multiplicity direction, so higher multiplicity cannot rotate or dilute it. Every finite internal-jet prime cylinder is formally étale over its internal base, so no finite cylinder can create two distinct reflection-normal lifts that agree after a nilpotent quotient. Any bifurcation must arise at genuinely infinite completion. Analytic Rees flatness is quasianalytic, while the surviving positive-charge `exp(-c/a)` sector is genuinely nonperturbative; finite analytic jets cannot carry it. Finite completion, one-vector GNS, pairwise Gram, bounded graph descent, and Route R’s intrinsic producer category are terminal.

### K-RVM — prime-indexed signed spectral relocation

**Proved receiver.** PrimeIndexedRVMSignedSkeleton constructs a doubled positive/negative reciprocal RVM diagonal. The target-fed operator built from ordered positive Xi ordinates is self-adjoint; each positive ordinate contributes both signs to its exact approximation-number sequence. Its approximation numbers obey the explicit logarithmic RVM asymptotic, so it belongs to every Schatten class above one, is Hilbert–Schmidt, and is neither trace class nor weak trace class. It lies in the logarithmically enhanced weak-trace ideal with exact residue `1 / pi`. The target operator differs from the smooth prime skeleton by trace class. PrimeIndexedRVMRegularizedDeterminant gives the det-two/canonical product, and a zero-free entire gauge plus an exact self-adjoint determinant identity forces RH while retaining analytic and geometric multiplicities. Under RH, XiOrderedPrimeDeterminantNormalForm gives the normalized Xi determinant and a unitary eigenbasis transport. Stronger transfer theorems show these are not artifacts of that model: every exact self-adjoint Xi determinant carrier has the canonical reciprocal-Xi singular values with multiplicity, exact Schatten abscissa one, minimal regularized determinant genus one, and the same logarithmic weak-trace and partial-trace asymptotics.

**Source-side positive fact.** The physical endpoint RVM relocation is trace class, self-adjoint, off-diagonal, nonzero, Hilbert–Schmidt orthogonal to the skeleton, and strictly increases the quadratic determinant budget.

**Wild-saddle bridge.** Two logarithmic fixed-point corrections to the source RVM phase are necessary and sufficient for trace-class relocation: depth one remains non-summable, depth two is summable and gives a self-adjoint signed operator trace-class-close to both smooth RVM and ordered reciprocal Xi. Primewise signed linear Stokes coordinates cancel, but a strictly positive summable quadratic determinant anomaly survives. This is determinant-grade proximity, not occurrence.

**Open core.** Prove exact prime-source matrix incidence and recover the relocation/eigenbasis/determinant without importing zero ordinates.

**Boundary.** Singular values, exact abscissa one, genus one, multiplicity transfer, determinant convergence, weak-Schatten membership, and logarithmic residue are forced receiver geometry; finite-rank and trace-class perturbations preserve the last two, and trace-class completion of a positive modulus square with positive residue remains non-trace-class. Every finite superquartic critical-prime polynomial-Fock model has Schatten threshold strictly above one and therefore cannot be an exact self-adjoint Xi determinant carrier. Depth-two relocation does not preserve individual eigenvalues or a determinant zero set. Replacing ordered Xi input by literal prime occurrence is the entire remaining route; all-order incidence still factors through Route P’s completed boundary seam.

### FZZ-P — cigar puncture and universal horizon dilation

**Proved receiver.** FZZCigarScatteringSpectralAsymmetry gives an exact boson–fermion Cauchy-density asymmetry, positive reflection deficit, and Fourier delay tower. Protected Jost logarithmic derivatives reconstruct this asymmetry; charge summation and Mellin completion give Gamma times zeta. Thus zeta zeros are zeros of completed delay tomography, while every individual real-momentum Jost sector is all-pass. Every integer delay moment equals the corresponding factorial-scaled Schwarzschild far-zone jet, producing one scale-independent all-order clock. This clock has infinite spectral support, strict log-convexity, and an exact positive non-Markov edge equal to normalized Bose susceptibility and quantum Fisher information. Real horizon-dilation completeness is RH-equivalent, and universality over all finite replica levels selects the imaginary axis while every fixed level is blind.

**Bridge.** VaidyaEvaporationFZZHorizonScale proves variable horizon ratios realize every positive scale and universal Krein sign selects the imaginary axis; every fixed mass-loss rate is blind.

**Open core.** Prove from cigar source that every nontrivial Mellin zero occurs in the real horizon spectrum, and land the infinite FZZ/Schwarzschild response clock coefficient-faithfully in the horizon-dilation and completed theta/Xi endpoint.

**Boundary.** Fixed replica level, mass rate, temperature, individual Jost sector, and ordinary genus/fugacity sum do not select the zeta divisor. No finite-state or Markov closure replaces the all-order carrier. Diagonal Jacobi charge completion stays positive and cannot reproduce the selective off-critical kernel; neutral-pair principal mixing activates every sector regardless of critical-line location. Neutral screening supplies an all-depth coefficient weld and wall hierarchy, but neither principal mixing nor torus neutrality forces reflected-chart orientation or common logarithmic renormalization.

### RBH — reflected bi-heat completion

**Proved source.** The row-subtracted reflected double series is normally convergent and has the exact theta-times-zeta pole decomposition, residue, and canonical Euler–Mascheroni finite part. Regulator holomorphy, full-window singular finite part, phase expansion, sharp remainder, and actual row finite part are welded without premises. At every Xi divisor of multiplicity m, both completed channels vanish through grade m−1 and have nonzero m-th jets; the regular zeta product first appears nontrivially at grade 2m. Their scale-order difference is exactly Re rho minus one half.

**Open core.** Derive before divisor selection one source normalization or comparison law forcing the two nonzero multiplicity-leading reflected channels to have equal aperture scale order at every Xi divisor.

**Boundary.** Functional-equation equality of the completed coefficients holds everywhere and cannot select the wall. Multiplicity tomography preserves the lost information but does not orient it; merely requiring equality of the recovered scale orders is the RH receiver.

### PW-B — Parikh–Wilczek Borel partner

**Proved receiver.** ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint identifies the first physical Borel wall with the nearest finite-energy tunnelling action, gives the exact first-winding Mellin/Borel coefficient, proves its recurrence, and computes partner-growth imbalance as a positive grade factor times transverse displacement. Its source-derived forward/reverse recoil edges have a gauge-invariant closed-history holonomy whose imaginary part is an explicit nonzero factor times height and transverse displacement. Equal real growth, zero holonomy phase, and positive-diagonal Hermitian symmetrizability are each exactly critical-line placement; universal balance over Xi zeros is exactly RH. Off line, the canonical two-mode SU(1,1) completion has nonzero pair mixing.

**Open core.** Derive partner-growth balance or recoil-holonomy flatness from source-first finite-mass evaporation, or replace either copywise condition with a genuinely global source aggregate whose vanishing forces it.

**Boundary.** No physical producer is formal. Generic KMS, CCR, unitarity, Cayley completion, Bogoliubov norm conservation, positive diagonal metric changes, late recoil, and neutral torus counterterms do not force balance or erase holonomy. Merely postulating copywise balance, flatness, symmetrizability, or common logarithmic subtraction assumes an RH-strength endpoint.

### WBF — Wold boundary fracture

**Proved source.** Finite prime-occupation first trace is exactly the inverse Wold boundary volume. The corrected Boolean edge for adjoining one prime is exactly the residual diagonal `-a/p`, its projective norm is `a/p`, and these norms sum to one along every prime enumeration; reciprocal-prime normalization recovers the density-scaled source class. Every finite boundary volume is positive, the all-prime volume tends to zero, and its reciprocal is a canonical cofinal scale tending to infinity. Both reflected irregular branches are polynomially moderate along this scale exactly at centered parameter. Independently, thermofield overlaps converge to the critical sector and reject every other coherent sector. The source-pointed blow-up exposes a canonical normal extension cocycle: it is independent of the right splitting, either zero or coefficient-faithful, constant across every prime/depth cell, and unchanged at infinite depth even when the ordinary source frame collapses. On each Xi copy it is exactly the centered-rate anomaly, changes sign under reflection, and is reflection-fixed exactly on the critical line. The same scalar is the negative Deninger local-Hodge commutator curvature; after the explicit edge/clock gauge, its squared norm is the fixed-source Stokes excess and the prime-clocked logarithmic Meyer/Gamma Radon–Nikodym energy, and it is exactly four times squared transverse spectral displacement. Global vanishing is exactly RH.

**Open core.** Prove a depth-uniform source-normal completion law—equivalently the missing cofinal equicontinuity/graph-domain admission—that carries the finite source transports into the completed Wold boundary and annihilates the conserved normal extension anomaly. It must be derived before Xi-copy specialization; postulating global normal-jet vanishing is exactly RH.

**Boundary.** Exact unit total edge mass is diagonal, thermofield centrality is blind, and fixed finite-Rees normalization loses the source class. Ordinary frame collapse is no longer evidence that orientation disappeared: the splitting-independent normal jet survives it. That jet is a sharp receiver, not a producer. WBF is therefore another `LAND + COMP + ORIENT` presentation of the same source-normal descent obstruction seen in L and completion survivors of R, not an independent arithmetic route.

### XST — Xi source-spin thinning

**Proved receiver.** The literal theta source has half-density monodromy `-1`. Coupling it to the centered Xi logarithmic character changes that spin by the exact centered Hurwitz monodromy; the first theta atom is nonzero, so value-zero censorship cannot fake coherence. Ambient-spin preservation, coefficient-faithful three-slot phase thinning, logarithmic-cover descent, terminal multiplicity-jet descent, and critical-line placement are equivalent for each divisor. Universal spin inheritance is exactly RH.

**Open core.** Derive from the completed source semantics that every closed Xi error fibre inherits the ambient theta spin sector before selecting or fitting a divisor.

**Boundary.** Postulating copywise coherence is an RH endpoint. XST is a candidate because Lean supplies a literal spin carrier and faithful reporter but no zero-independent inheritance theorem.

### NDS — nodal defect superselection

**Proved receiver.** The source-first family `xy = XiC(z)` exists before divisor selection. At every Xi divisor its reduced affine fibre is the same pair of coordinate axes and its projective Legendre fibre is the same nodal cubic. The terminal multiplicity jet embeds nontrivially as the conductor coefficient `(j,0)` in the universal nearby-cycle lattice; this specialization is injective, monodromy-fixed, and fills the complete invariant line. Hermitian formation coherence is exactly the same second-order nodal condition, while bare functional-equation formation has no fixed Xi copy. A fixed bounded-price positive polarized coalition whose packets become norm-dark forces its selected Xi zero onto the critical line. Separately, local nodal superselection, total differential square-zero, second-order arithmetic coherence, and the global master equation are each equivalent to critical-line placement/RH.

**Open core.** Construct a natural regulator from the pulled-back analytic Xi node/Legendre family to the universal conductor/nearby-cycle lattice, preserving the nonzero terminal multiplicity class and its orientation, then prove the resulting scheme-theoretic second-order descent is coherent on every closed Xi error fibre. Alternatively construct one zero-independent bounded-price polarized dark history exhausting all Xi copies; the existing theorem controls only the copy carried by a supplied history.

**Boundary.** Reduced nodal geometry is support-blind and multiplicity-blind; source-first construction of `xy = XiC(z)` does not select a wall. Generic conductor lattices identify the target, and Tate-theta gauges converge compact-open at the cusp, but neither supplies the natural Xi-family regulator between them. Each marginal differential is automatically square-zero, while imposing mixed total nilpotence is exactly RH. The surviving producer must be scheme-theoretic, oriented, and genuinely completion-level.

### KMSS — Koszul mutual-statistics superselection

**Proved receiver.** The actual all-prime graded-skew cup has two source orderings. If one scalar neutral grade–phase jet is their order-independent image, graded skewness forces that jet to vanish and hence enforces local nodal superselection. Universal anomaly-free order-independent completion over all Xi copies is exactly RH.

**Open core.** Construct before divisor selection one nonzero, functorial, order-independent Koszul lift from the literal all-prime source to every completed Xi-error fibre, retaining source legs and coefficient provenance.

**Boundary.** Zero-specific existence is too weak: at a pure defect both source legs may be zero, giving a degenerate lift. Universal completion is an RH endpoint, not its producer. KMSS is distinct from NDS at the source interface—mutual-statistics order independence rather than postulated nodal factorization—but currently feeds the same mixed-curvature receiver.

### LI — paired-Li receiver

Lean constructs an exact-order-one functional-equation/Schwarz-real reflected-Gamma carrier with arithmetic-progression zeros and hypertranscendence. Its divisor-normalized Li coefficients are strictly positive, absolutely summable, and have explicit two-sided linear bounds with uniform margin. A remote off-line quartet has explicit log-phase alignment producing a negative gauged coefficient at scale n divided by H log H tending to four.

This proves the paired coefficient receiver is sharp and robust. It does not identify the carrier with literal Xi prime–Gamma source. LI remains candidate until that source landing and unconditional all-coefficient order are proved.

## Route-neutral bridges and pre-routes

These results constrain live branches but do not supply an independent source-to-RH chain.

### W2C — two-channel Weil bridge

XiWeilTwoChannelResolvent identifies the CLG critical kernel with even plus odd Weil resolvent channels. The literal theta-tail first-moment kernel is pointwise nonnegative and exactly a two-channel Krein difference; its double Laplace transform is the removable Xi Bezoutian, whose finite-matrix positivity is exactly RH. XiWeilApertureChannels gives compactly supported two-sided exponential realizations, dominated convergence, finite-packet convergence, and eventual finite-aperture survival of every negative packet. XiBezoutianPointedIncidence identifies the same kernel with UEB. XiBoundaryPoissonDensity and XiBoundaryCauchyRepresentation give safe-half-plane positive Poisson/Cauchy representations. XiDePoissonizedStationarity removes offset from each prime atom.

Universal aperture-energy or observability-deficit nonnegativity is exactly RH. W2C unifies CLG/TTF, Q, UEB, and finite-aperture O/SV2 receivers. S6F supplies a genuine infinite-completion theta orientation, but no theorem identifies its sixth odd supertrace with this first-moment/Bezoutian form. W2C is therefore still a receiver rather than a producer.

### Horizontal-charge package

RouteCHorizontalChargeInterimVerdictPackage unifies C1, G, and HC receivers: source thin-slice collision charge, conservation, multiplicity mismatch, finite Cauchy energy, shift flatness, unbounded quartet curvature, positive Euler-orbit non-PF2 behavior, archimedean sign change, and floor–Möbius splitting. It proves no absolute four-unit source bound.

The finite-prime completed tangent has a unique upper Euler pole with residue `-2 * I`. All-prime completion cancels that pole and replaces it transversely by the full shifted Xi divisor: the tangent is holomorphic exactly away from the divisor and its residue at a zero is `-2 * I` times exact analytic multiplicity. This closes pole-to-divisor occurrence and multiplicity, not G's source-side four-unit order or HC's collision-current summability.

### Arithmetic Fredholm orientation and recurrence

The literal deck orbit `(Frob_p, log p)` defines paired unilateral Fredholm operators of indices `-1` and `+1`; reflection is adjoint and no compact perturbation erases their odd orientation. The prime Fredholm trace has an exact source formula, with zeta entering only as a downstream multiplier. At source orientation, completed Xi vanishes exactly when every source-trace Fourier coefficient vanishes. This is a genuine infinite, paired, nonphysical source orientation for CCM/G/P/WBF, but Lean does not force those coefficients to vanish or prove that the trace receiver exhausts every Xi divisor. The algebraic AF charge limit embeds faithfully into `Q`, but its canonical finite-stage charge is zero; Lean proves that zero-winding loops cannot converge uniformly to all Xi boundary loops because one Xi loop has unconditional nonzero winding. Thus ordinary zero-charge AF completion cannot supply the missing occurrence theorem.

Reality of every nonzero eigenvalue of the fixed theta kernel operator, pinned-Green isotropy of all its eigenmodes, literal first-clock recurrence, and RH are exact equivalent receivers. First-clock recurrence is also equivalent to cofinal temperedness of every occupied Xi mode at every prime and nonzero polarization. Its failure is one fixed occupied mode escaping every positive finite-shell energy ceiling at every prime and polarization. Thus the next theorem is not another finite energy estimate: it must prove recurrence/temperedness from source or exclude the persistent mode. This sharpens `COF` without creating a separate live branch.

### Prime-tail diagonal escape

Failure of RH is equivalent to finite-stage diagonal escape of the critical Xi-mass prime tail: one nonzero reflection self-intersection charge defeats every moving finite prime-power approximation. The same obstruction is exactly abelian information escape—conditional reflected information diverges while both literal source-mass-weighted currents vanish. Moving truncations therefore cannot outrun an off-line charge, and convergence in source mass can conceal rather than remove it. T1, T2, U, CCM-FU, and WBF still need source cancellation or annihilation of that persistent charge; changing the truncation schedule is not a producer.

### Smooth AFE and Levinson window

The exact Gaussian smooth approximate functional equation is formal at every point of the open critical strip, including arbitrary displaced lines, differentiated heads, explicit truncation errors, shifted chi derivatives, and uniform finite-detector approximation. The linear Levinson mollifier is coefficient-faithful; finite Dirichlet mean-value, GCD reindexing, mollified twisted diagonal, and exact error bounds are formal. The direct displaced AFE head multiplied by that mollifier is one finite Dirichlet polynomial with an exact window mean square and exact positive-natural divisor/Möbius coefficient formulas. On the critical line, the literal zeta-head product coefficient is the normalized Barban–Vehov divisor coefficient divided by `sqrt(k)`, with exact harmonic square energy and an explicit Graham upper bound. The differentiated detector `zeta + lambda*zeta'` has an exact Barban–Vehov plus divisor-log-moment coefficient formula; its value-only specialization recovers the preceding coefficient.

The argument-principle side is also substantially closed: admissible rectangle heights exist, all noncritical edges are bounded, critical-edge zeros are factored out without cost, and the unconditional window inequality converts detector phase advance into odd and singleton Xi-fibre counts. Remaining Levinson content is the full two-head mollified asymptotic and a source upper bound for zeros of the entire detector strong enough to force a quantitative critical-line proportion. Even density one would not by itself prove RH; an RH route still needs a height-uniform quantized exclusion such as HC's sub-two collision law. For T1, the separate open handoff remains transfer of the exact two-edge AFE to its affine core-current carrier followed by signed short-block cancellation.

### Visible-coprime orientation

The primitive visible-coprime Möbius–Laplace pair sum is absolutely summable, satisfies common-dilation renewal and two-variable addition, and has a zeta-quotient Mellin symbol. At an actual zeta/Dirichlet zero its Hermitian mixed jet has sign equal to the side of the critical line. This is an analytic paired receiver, not E’s missing fixed central Hall relation.

Coprime matrix signature is exactly Mertens, tends to zero after PNT normalization, and no fixed-rank correction makes all matrices positive semidefinite. Positive finite-energy diagonal repair is incompatible with a nontrivial analytic critical boundary.

### Finite generalized-Schur inertia

Finite Blaschke generalized-Schur kernels have exact negative index equal to the algebraic rank of the numerator adjoint restricted to the denominator model space, without coprimality. Common inner factors are precisely the cancelled-rank defect, visible even on exterior annuli away from denominator zeros. The arbitrary-denominator operator model has the same full rank profile. Under coprimality this reduces to denominator degree and exact leakage rank.

Finite model spaces satisfy the exact product decomposition `K_(B₀B₁) = K_(B₀) ⊕ B₀K_(B₁)`. Leakage and causal Hardy compression obey a polarized Pythagoras law and operator identity `L†L + T†T = I`; the crossing-channel dimension is exactly disappearing denominator multiplicity, its Gram defect is the square of causal compression, and its off-diagonal defect is the negative causal cross block. Boundary-scale causal decay therefore peels both defects. Horizontal layers converge projectively to Cauchy-resolvent multipliers; finite products converge in operator norm to sums of rank-one leakage channels, with finite exponential Hankel transport. Infinite Blaschke divisors create infinite-dimensional model spaces and dense infinite-rank leakage. Leakage norm is bounded by multiplier norm and bounded below by evaluation at every denominator zero. Nested Hermitian kernel sections have nondecreasing negative index equal to negative-eigenvalue count, so negativity cannot evacuate. This closes receiver geometry, not arithmetic coprimality, source positivity, or whole-ground selection.

### Wold thermofield infrastructure

Diagonal Hilbert–Schmidt purification, exact vector states, pure-tensor shuffles, finite occupation laws, and the canonical all-prime incomplete tensor product are formal. Canonical Paschke–KSGNS completion, minimal pointed uniqueness, weighted cyclic projection, exact centered covariance kernel, and identification of the closed centered span with the projection kernel are also formal. Thus abstract positive-kernel or one-vector carrier construction is not missing. The diagonal kernel remains central: left and right actions agree identically. Source-pointed normal blow-up supplies the missing noncentral coordinate at receiver level: its splitting-independent extension cocycle survives every cell and infinite depth, while the ordinary frame collapses, and its Xi specialization is the reflection-odd centered rate. Hodge curvature, fixed-source Stokes excess, modular logarithmic energy, transverse spectral energy, Hermitian Stokes-barcode width, and absolute reflected prime-tail entropy are exact presentations of this same normal fracture. Global vanishing is exactly RH. WBF therefore needs a source-normal completion/equicontinuity law, not another CP/GNS completion; E, TK, and EWQ-V still require their own arithmetic off-diagonal, signed, or noncentral incidence.

### Irregular Stokes sheaf foundation

Continuous phases on compact bases have closed epigraphs in the compactified enhanced-real direction, with explicit compact-support sheaf, ind-sheaf, bounded/unbounded derived, and generated enhanced-quotient objects. Analytic leading phases specialize these to Stokes-phase exponential objects in both enhanced quotients. Analytic zero-level support cellularizes exactly to the global exponential boundary. For actual Puiseux branch pairs, cellular wall labels are canonically equivalent to analytic walls; analytic wall microstalk functors recover contact order times root rank, their total mass equals the cellular mass, and their pairing is the finite polarized Stokes–Witt pairing. Global cyclic boundary objects restrict to exact local arc/nearby/vanishing sequences. A local object family descends exactly when duplicated arc stalks agree, and every compatible local morphism family glues with exact restriction recovery.

Bordered spaces, exponential-epigraph sheaves, proper epigraph addition, convolution, symmetric monoidal tensor, bounded-below derived pushforward, K-flat total tensor, derived sheafification, ind-extension, proper pullback, translation action, and generated enhanced Verdier quotients are formal. Identifying a generated negligible category with the corresponding bare projection image still requires fullness of derived projection pullback, ultimately a cohomological-contractibility theorem for `EReal`. Object-level and compatible-morphism Stokes descent are formal. For actual Xi types, global Hermitian-dual determinant unitarity holds even off line; only constituentwise polarization and equality of enhanced supports detect the critical line. The raw wall current has unavoidable multiplicity jump, while raw-plus-polar codiagonal completion is continuous but retains exact multiplicity eightfold in the relative character. Analytic Rees flatness is quasianalytic, so the surviving positive-charge exponential-small gauge is necessarily nonanalytic. Missing route content is therefore a literal infinite prime–Gamma phase object with coefficient-faithful, constituentwise, relative, and nonperturbative Xi landing—not another paired determinant or finite analytic jet.

### Finite Hasse and Weyl classifiers

Hasse families are formal as injective local-profile systems: complete local agreement is exactly global equality, and every unequal pair has a separating place. Registries instantiate coefficient, arithmetic, ABHN residue/cohomology, form, free-algebra, linear-operator, central-simple-algebra equation/property/spectral, Kummer–Calderón, Deninger, valuation-shell, wall, and Stanley–Reisner/Čech profiles. Finite continuous cyclic H2 and each torsion-invariant coordinate embed faithfully into the Brauer group; splitness is exactly the zero class. The corpus supplies central-division local degree equality, an integral maximal-degree subfield that is intrinsically a nonarchimedean local field and whose residue extension has degree equal to the division-algebra degree, scalar-compatible exhaustion of the determinant residue, splitting after scalar extension, unramified extensions of every positive residue degree, Frobenius order, denominator exhaustion, and compatible H2/Brauer inflation through finite towers. At any nonzero Euler coordinate, the torsion-twisted local Euler factor faithfully remembers the finite cyclic Brauer class; it equals the actual untwisted Connes–Tate factor exactly for the split class and is stable under denominator refinement. Chosen finite evaluations reconstruct every initial zeta-jet and canonical completed-Xi-jet coefficient packet uniquely. These exact local/tower classifiers still do not construct global finite-ramification reciprocity or a completed Xi occurrence.

Window-jet Weyl and Gohberg–Sigal index laws preserve multiplicity, covariance, and local divisor data. Positive-density transverse relocation constructs exact-order-one functional-equation/Schwarz-real hypertranscendental carriers with the same finite/all-jet source passports and positive-density off-critical zeros. Therefore local jets, finite Hasse data, exact order, hypertranscendence, functional equation, and zero-density passports cannot locate Xi zeros without a coefficient-faithful infinite source landing.

### Other pre-routes

- **ZGC:** convergent-chamber abelian zeta-gas chirality and directed entropy give strict source orientation, but no completed functional-equation involution or Xi landing.
- **SFP:** reflected prime–Gamma Poisson formation has an exact arithmetic thermodynamic interpretation: Bockstein is log-rate affinity, hidden-history density is entropy production, exchange defect is half affinity squared, and bounded work/detailed balance selects neutral grade. On Xi copies global detailed balance is exactly RH, so this is a completed receiver—not an independent formation producer.
- **PLAC/EPC/MEG:** Euler-log Herglotz mass, Euler-position commutators, and multiple-elliptic-Gamma cosets have nonclassical infinite or paired mechanisms but no Xi endpoint.
- **VMG-HCD:** von-Mangoldt/Gamma Hilbert collision data expose source clocks, but strict contraction and unitary recurrence cannot share one real clock.
- **Cayley-HS:** a transverse octonionic grade is invisible to every quadratic shadow but equals the secondary Maurer–Cartan obstruction and parenthesization defect. This is a faithful higher-incidence model for JAS/NDS/KMSS, but has no arithmetic Xi landing.
- **PA-CD:** shifted prime–archimedean moments define finite reflection-invariant circle measures at every shift and strictly positive probability densities through shift twelve, with exact recovery of every nonnegative Fourier moment. At the central shift, the source resolvent is zero-free on the closed disk, its Schur transform is contractive, and its Carathéodory transform has positive real part. Generic radial-Poisson barycenters supply positive Hankel forms, but membership of this explicit source density in the sharp source hull is exactly RH. These are positive survivors of the retired OPUC mechanism, not a reflected-orientation producer.
- **KPG:** the Gamma power-gauge weight has infinitely many positive and negative intervals and bilateral infinite Krein index. More generally, every measurable Schwarz-symmetric Kapustin boundary carrier whose positive and negative sets both have positive measure has two infinite-dimensional Krein sectors. Any bounded self-adjoint correction making the explicit power-gauge carrier positive has essential norm at least one, infinite rank, is noncompact, and lies in no finite Schatten class. No coefficient-faithful Xi landing exists, so this is not a route.
- **THD/S6F:** continuous theta half-density tails have exact primitives, even/odd residual channels, and a shrinking explicit survival corridor. Their antisymmetric slope curvature is an exact Turán integral. The fifth source jet is negative, the sixth is positive on the nonnegative source half-line, and the sixth-order one-particle margin pays the two-particle loss plus every higher negative-parity sector, leaving a strictly positive odd supertrace after infinite Fock completion. This is a genuine source orientation, but no theorem lands it in the completed theta Bezoutian, Weil form, or Xi divisor; S6F remains candidate rather than live route.
- **PEX:** finite-support prime exponentials have dense compact-open holomorphic range, and their nonlinear Euler-flux microimage determines analytic germs. But the graph of holomorphic image versus unrestricted prime coefficients is itself dense in the independent product, so compact-open completion does not recover coefficient provenance. This is a `LAND/COMP` warning, not an occurrence theorem.
- **E2-NB:** the quasimodular transformation law and dense rational cusp images make the unit circle a pointwise natural boundary of disk Eisenstein E2. Every finite primitive retains that boundary, even when its coefficients become absolutely summable and every observed finite jet is differentially algebraic. Finite smoothing and finite-jet regularity therefore do not produce continuation; no Xi landing exists.
- **CTP:** primitive roots of injective prime orders give explicit entire phase-tail series whose bounded-degree phase freedom forces hypertranscendence, including rational-power magnitude profiles. This supplies an infinite cyclotomic source passport but no coefficient-faithful Xi landing or horizontal selector.
- **BTL:** torsion-twisted local Euler factors are faithful finite cyclic Brauer receivers and distinguish every nonsplit class from the actual Connes–Tate local factor. No global finite-ramification reciprocity assembly or completed Xi landing is formal.

## Terminal and retired routes

Closure applies to the named mechanism, not to every future architecture using related objects.

| Route or mechanism | Lean terminal statement | Strongest survivor |
|---|---|---|
| A | Fixed source-faithful physical-phase transport is identity; nonidentity has explicit connection defect. Positive Markov feasibility is source sign, and universal feasibility is RH. Source-trace Hankel positivity and canonical residue closability are also exactly RH; finite Euler orbits and higher grades are blind. | Phase-natural rigidity, barycentric completeness, trace/resolvent identities, moment-germ inversion, and dense finite-Euler orbit classifiers. |
| B | Scaling/grading and distinct prolate parameters cannot share the required unitary transport. | Relative graph and boundary deformation. |
| C2/I | Finite theta/dyadic width saturates its coordinate; missing width is RH-bearing. | Cauchy/Hurwitz interfaces survive in Q. |
| D1 | Finite/local moment positivity does not orient completed all-degree source. | Continued D2 tail and Q exterior kernel. |
| F | Bounded/sublinear compact Sonin completion has wrong order, loses its floor, or collapses source. | F2 cofinal all-prime trace-moment weld. |
| G2 | Required relative-Volterra germ is RH-equivalent. | G marked Ward boundary. |
| H | Even Taylor factorization erases orientation. | Relation-valued indefinite primitive. |
| J | For Lm equal to 6 log m and m at least 25, bad energy is at least log m over 20 at every Julia scale. No uniform unrenormalized budget exists; off-diagonal cancellation cannot remove unit-diagonal mass; post hoc diagonal subtraction breaks one-node capacity. | A principal-relative current defined before good/bad projection; this is not Route J. |
| K | Original quadratic spectral mechanism cannot retain marked source; all-order repair factors through P. Every exact self-adjoint Xi determinant carrier is forced to have the canonical reciprocal-Xi singular values, exact Schatten abscissa one, genus one, and logarithmic weak-trace law, but these remain target-side constraints. | K-RVM is a changed infinite paired operator candidate whose only remaining content is prime-source occurrence. |
| M | Saturated Gamma–Jacobi carrier admits no positively normalized inclusion-compatible cyclic reader with one fixed value on consecutive actual source sections; anchored cofinal flatness is RH. | Complete receiver and singular-reader rigidity. |
| N | Response equality, endpoint contractivity, or bounded polar work is RH-equivalent; bilateral excess is P’s reflected translation/radial-work excess. | Shared receiver for L, P, and G. |
| R | Intrinsic producer category is empty. Fixed-grade evaluation is split with zero cokernel/Tor, so algebraic exactness cannot carry the obstruction. The genuine `(2,3)` singular corona, nonzero physical lift, and source action exist, but its global flatness is RH; arithmetic globalization is exactly squarefull Stokes summability, itself central-grade selection. Detailed balance, exchangeability, bounded formation work, and zero entropy production are the same receiver. | Completion-migration/information-escape class, nonzero two-clock transgression, singular corona, squarefull Stokes coefficient, and joint-ancestry classifiers feed JAS. Any successor must change interface to paired completion-level cohomology, not revive intrinsic regular Route R. |
| IW | Internal Weyl-model existence is exactly desired divisibility; global existence is exactly RH. | Cyclic clock–shift model and divisibility classification. |
| AP | Big-Witt/Scaling-Site completed-Xi pullback is impossible in the stated architecture; surviving stability and preperiodicity conditions are RH-equivalent. | Exact Witt, sheaf, Galois, and perfect-closure geometry. |
| TD/C1 positive supercarrier | Raw reflected Stokes atoms exceed completed central mass. No finite positive Hermitian supercarrier dominating them can represent the completed source. | Any C1 carrier must delete or reweight atoms or introduce signed correction. |
| AF | Copywise convergent abelian class-law certificate exists exactly at centered rate zero; global certificates exist exactly under RH. Canonical finite-stage AF winding is zero, and zero-winding loops cannot converge uniformly to every Xi boundary loop because one Xi loop has unconditional nonzero winding. | Singular/infinite-action or genuinely global charged aggregate interface only. |
| SNR | Reporter aperture can realize arbitrary positive target height independently of source. | Source-native aperture invariant is required. |
| residue-scale fitting | Actual Gauss Fourier diagonals lie unconditionally in weak `S_(2m)`, and the literal quasi-inner Gauss block lies in weak `S_m`, including weak trace class at depth one. The reduced one-prime distinguished block is self-adjoint and its literal modulus square is exactly the actual depth-one Gauss channel. Its positive residue scale is nevertheless a continuous strictly increasing bijection from `(1,∞)` onto every positive target value, so matching a target residue by choosing scale has no horizontal selecting content. Any trace-class completion preserves that measurable modulus-square residue and remains non-trace-class. | Scale must be fixed by an independent source law before residue comparison; the full Hardy-defect/source-occurrence landing remains absent, and weak ideal membership or trace-class repair cannot create orientation. |
| scalar EWQ | Scalar, determinant, unitary, checkerboard, finite-jet, Artin-positive, and auxiliary-vacuum constructions erase odd completed orientation or reduce to RH. | EWQ-V nonunitary matrix/jet candidate. |
| OPUC / positive circle carrier | The explicit central prime–archimedean probability carrier has exact moments and analytic density. Its unitary shift and involutive reflection satisfy `ΘUΘ = U⁻¹`; its Schur function is contractive and its Carathéodory function has positive real part. Yet reflected polynomial positivity and the complete Hankel cone are exactly RH. Equivalently, its normalized density belongs to the uniform closed convex hull—and admits a probability disintegration—of radial Poisson kernels on `[0, 2/41]` exactly under RH. Strictly positive uniformly coercive circle densities can still have a negative reflected monomial square. | Exact source circle state, shift/reflection covariance, Fourier moments, resolvent, ordinary unitary positivity, and sharp radial-Poisson receiver survive; reflected orientation requires a different producer. |
| DQPT | Exact eta/chi slope, rate, and memory-lag observables classify the critical line; universal annihilation is RH. | Sharp receiver, no producer. |
| fixed-scale Hawking/FZZ/Vaidya | Fixed temperature, replica level, mass rate, recoil, or self-similar dilation is horizontally blind or passivates off-line shells. Exact mass-Cayley return is unitary at every divisor; its two-mass area is an off-line classifier only after divisor input. | HB source synchronization/threshold law and FZZ-P universal dilation remain. |
| unsigned Hawking/QNM optical selection | In the modular topological-AdS realization, every Xi divisor is an actual scattering pole with a shadow zero and exact opposing QNM branches, but separated linear energy depends only on the shadow-even angular eigenvalue. Completed triple-Eisenstein angular EKG backreaction is bright and positive at every divisor yet invariant under pole/shadow exchange. Exact scalar radial Jost factors retain both shadow sectors. Schwarzschild/FZZ Jost-zero identification, pure retarded Evans determinants, and unsigned optical energy remain terminal. | Time-oriented QNM splitting is canonical exactly on the critical wall, and a shadow-odd projective Evans wedge is formal. HB requires the full source law synchronizing every bright sector to the standard clock; angular Noether transfer is one realization. |
| diagonal or sector-local Hawking completion | Finite and limiting diagonal FZZ Jacobi charge Grams remain positive and cannot match an off-critical negative selective kernel. Neutral-pair response and the full mirror mix every tilted Xi sector after an adaptive clock, independently of side. Sector-local AIME has nonzero bare susceptibility, but its divisor source amplitude, absorption, and dressed response vanish. | A fixed-angular-sector parity-to-helicity AIME return exists, but it is not common-clock theta-shadow selection. HB survives only through full-source order synchronization. |
| homogeneous nonlinear Hawking/AIME return | Exact fundamental cross-branch radial moment is `-4`; chiral mass-jet numerator is `-12 / (Q + 2)`; nonzero absorbed seed creates a simple opposite-QNM-branch pole and nontrivial Evans/Cayley return at every Xi divisor. Horizon phase cannot erase it. Passive stationary mass only multiplies off-line chiral defect by `1 + M`, while finite local and finite-energy continuum transients decay. | HB survives only through a genuinely nondecaying threshold/inhomogeneous source. It must prevent exact threshold cancellation and higher-order clock delay; a nonzero angular Noether defect of charge `-2*xi` is sufficient but not yet derived. |
| finite-state FZZ/Schwarzschild closure | The common delay/far-zone clock satisfies no positive-order constant-coefficient recurrence or fixed-dimensional realization, and strict log-convexity gives a positive non-Markov remote-edge defect. | Exact infinite clock, Bose susceptibility, and quantum-Fisher defect survive. |
| copywise Parikh–Wilczek balance | Equality of Borel growth, zero recoil-holonomy phase, and positive-diagonal Hermitian symmetrizability are each exactly critical-line placement; universal copywise balance is exactly RH. Generic SU(1,1) completion only preserves norm and mixes every off-line pair. | PW-B survives only through a source-derived global balance/flatness law not fitted to Xi copies. |
| neutral FZZ/PW counterterm sewing | Neutral screening activates every positive depth, but torus locality and renormalizability do not force one logarithmic subtraction for both reflected Mellin charts. The universal sewing predicate is RH-equivalent. | Exact coefficient weld, wall hierarchy, and all-depth mixing survive as PW-B/FZZ-P receivers. |
| reflected bi-heat coefficient balance | Both completed cross coefficients are equal everywhere by the functional equation, while their scale orders agree only on the critical wall. | Multiplicity-exact nonzero leading jets survive; RBH needs a source law forcing their co-leading scale. |
| diagonal thermofield purification | Normalized Wold thermofield kernels are central, so left/right diagonal actions coincide and carry no orientation difference. | WBF’s cofinal sector fracture survives; orientation cannot come from diagonal equality. |
| finite-cylinder double realization | Every finite internal-jet prime cylinder is formally étale over its internal base; two distinct reflection-normal lifts cannot become equal after a nilpotent quotient. | Any JAS/NDS/KMSS completion bifurcation must be genuinely infinite. Finite-cylinder CADR is retired. |
| paired irregular determinant purity | Hermitian-dual determinant unitarity holds for every paired irregular type, including explicit off-critical Xi types. Global paired purity is blind; constituentwise unitarity, enhanced-support equality, and internal sewing are each critical-line receivers. | Constituentwise relative Stokes data and the multiplicity-retaining resolved character survive; a producer must orient constituents before pairing. |
| GIT word-trace gluing | Two flat invertible commuting unipotent pairs can be per-generator conjugate and have every signed/unsigned word trace equal while lying in different simultaneous-conjugacy orbits. | Joint gluing/ancestry needs nonabelian orbit data beyond trace invariants. |
| standard CGL packet | Reflection partners share character and ordinate and collapse; formal envelope is at least 288 before secondary terms. | HC confluent packet or absolute source summability. |
| positive diagonal repair | Finite-energy positive diagonal repair cannot remain analytic through a nontrivial critical boundary; critical jets force singularity or trivial reflection. More sharply, off RH every globally positive repair must inject positive energy into a divisor-isolating reciprocal atom, with at least the bare negative deficit. | Signed, off-diagonal, singular, or explicitly atom-fed correction only; an atom-nonfeeding repair would already prove RH. |
| full-sector compact repair | Positivity over an infinite negative sign sector forces correction essential norm at least one, infinite rank, noncompactness, and exclusion from every positive Schatten class. | A viable correction must be noncompact/full-sector or change the indefinite carrier before repair. |
| bounded strict-frontier gauge | Every gauge bounded on the right germ leaves a positive-order shifted-Xi admission contact at zero. Any finite nonzero normalization is unbounded, with pole order forced by contact multiplicity. | U retains the intrinsic singular contact residue and must control its cofinal source price; bounded trivialization is impossible. |
| boundary-resolvent shortcut | Uniformly bounded inverse on a boundary does not force interior invertibility, already for a scalar family. | A strict relative Neumann defect below one does preserve invertibility along the full homotopy. |
| finite passports | Exact order, functional equation, Schwarz reality, hypertranscendence, any finite/all-jet differential field, finite Hasse profile, and positive zero density admit off-line relocated carriers. No entire differentially algebraic factor times any polynomial exponential gauge can equal completed Xi, so finite-dimensional Painlevé/isomonodromic tau bridges are excluded as well. | Infinite coefficient-faithful arithmetic occurrence. |
| finite commuting-dilation/autonomous spectrum | Every exact analytic proper finite-prime commuting dilation-plus-translation Hamiltonian has absolutely continuous spectral measure and no eigenvectors. Any regular locally unique autonomous complex carrier retaining prime logs through `N` has order at least `floor(pi(N)/2)+1`, so fixed autonomous order cannot follow growing prime support. | A Hilbert–Pólya occurrence must be genuinely all-prime, noncommuting, nonautonomous, or singularly completed. |
| finite critical-prime polynomial-Fock determinant | Every finite superquartic adapted Fock tube has exact Schatten threshold `m / (m - 4) > 1`, whereas every exact self-adjoint Xi determinant carrier has threshold one. The two laws are incompatible. | Shrinking critical-prime radius and prime-mass asymptotics survive as local source geometry, not an exact Xi determinant carrier. |
| Route-P depth-zero relocation and scalar tau matching | Depth-zero/full weak-trace source is not trace-class-close to ordered Xi, and bounded mixing preserves that obstruction. Exact additive correction lies in Hilbert–Schmidt class but outside weak Schatten one. Prime/Gamma wall and Xi tau germs have incompatible projective two-jets under every scalar time rescaling; the required normalized correction has positive quadratic curvature. | Sharp depth-two wild-saddle relocation and its positive summable quadratic anomaly survive as WS2; a successor must be non-scalar and supply exact source occurrence. |
| moving finite-prime escape cure | A nonzero reflection self-intersection charge defeats every moving finite prime-power approximation; finite-stage diagonal escape is exactly failure of RH. | Source cancellation or annihilation of the persistent charge, not a faster truncation schedule. |
| de Branges transcendence selector | A positive zero-free Schwarz-real reciprocal-Gamma gauge changes a differentially algebraic Hermite–Biehler representative into a hypertranscendental one while preserving its inner quotient and canonical spectrum and changing its kernel only by diagonal gauge congruence. | Explicit hypertranscendental reciprocal-Gamma gauge and exact de Branges gauge classification; differential transcendence is not spectral orientation. |
| time-one Gamma-jet Fock boundedness | For every strip divisor and every fixed safe real base point, uniform boundedness of all finite factorial jet energies is exactly critical-line placement; universal boundedness is exactly RH. | Actual time-one Meixner Hilbert vector, coefficient-faithful prime-seam transform, and explicit cofinal off-line divergence form a sharp receiver, not a producer. |
| reduced Xi nodal degeneration | The source-first family `xy = XiC(z)` has the same reduced coordinate-axis fibre, and the same reduced Legendre nodal cubic, at every Xi divisor; reduced geometry sees neither horizontal position nor multiplicity. | The terminal multiplicity jet survives injectively on the universal Picard–Lefschetz invariant conductor line. NDS requires the natural analytic regulator and oriented scheme structure. |
| finite residue positivity | Every nonzero finite residue-mode packet becomes negative arbitrarily late. | Infinite/cofinal control or exact source annihilation. |
| bounded Marcinkiewicz/Yoneda descent | Every bounded-reader graph pushout splits and connecting maps kill actual lifts. | PSRC singular nonclosable graph. |
| reciprocal-Xi Clifford split | Bare supersymmetric/Clifford splitting exists exactly under RH. | W1C requires an independent arithmetic determinant identity. |
| Li finite shortcuts | Finite triangular algebra cannot prove infinite coefficient order; the generator is hypertranscendental and remote quartets can align negatively. | LI paired coefficient receiver. |
| universal squared-Euler anti-Löwner positivity | Positivity of every finite positive-ray anti-Löwner matrix is exactly RH. | Exact sign-switch, collision, Hankel, and three-node receivers. |
| unrenormalized Suzuki Ward energy | Cauchy energy grows linearly while Xi curvature has square-root envelope; defect tends to negative infinity along apertures 8n. | Renormalized signed SP-E comparison. |
| compact Thorin/Markov/seam-log Hankel | Canonical positivity and compact Markov representation are exactly RH; theta-likelihood candidate is not infinitely divisible. | Exact moment identity as receiver. |
| direct prime Ising | Fixed modal finite balanced-tree partitions cannot converge locally uniformly to Xi; rank growth forces scale collapse. | Only singular critical rescaling could define a successor. |
| source-horizontal annealing | Pre-vacuum invariance is RH; post-vacuum attenuation preserves strict-right orbit escape for every nonzero exponent. | Singular source-derived moderation in P/G. |
| C5 pointwise Jensen prime factorization | Critical prime amplitudes are neither absolutely nor square summable; no global critical-line logarithm of zeta or pointwise exponential prime factorization with a nowhere-zero archimedean factor exists. | Boundary prime expansion must remain distributional. Every finite-prime simple root still has an exact analytic Jensen branch and velocity. |
| finite ABHN residue landing | Untwisted rational residue observables vanish while actual finite Connes–Weil terms are nonzero; parity cannot detect cubic Brauer charge. Local degree equality, intrinsic local-field structure and exact residue degree for scalar-compatible residue-exhausting maximal subfields, unramified splitting of central division algebras, every finite residue degree, Frobenius order, denominator exhaustion, and tower inflation are formal, but remain finite/local. | Torsion-twisted local Euler factors faithfully detect finite cyclic Brauer classes, but nonsplit twists differ from the actual Connes–Tate factor. A successor needs global finite-ramification reciprocity and completed Xi landing. |
| fractional-part extraction | Strip-zero integral equations do not select abscissa; omitting jump terms makes the limit diverge. | Correct NB/BD representation and jump-complete expansion. |

## Cross-route conclusions

### 1. Source/receiver firewall

Most routes already possess a sharp RH-equivalent receiver. Rewriting that receiver as positivity, passivity, flatness, divisibility, determinant convergence, zero width, bounded energy, or spectral completeness does not advance RH unless Lean derives its premise from the literal source before choosing a zero.

### 2. Local exactness is abundant; global selection is scarce

Finite packets, all finite jets, exact finite homology, local indices, divisor multiplicities, finite real-zero determinants, and exact functional-equation passports can all be realized or relocated without fixing horizontal zero position. Finite-prime commuting dilation models even have purely continuous spectrum and no eigenvectors. Prime exponentials are compact-open dense and determine analytic germs, yet their coefficient graph is dense in the independent product: analytic completion alone forgets arithmetic provenance. Successful operator routes must use genuinely all-prime, noncommuting, or singular completion; successful arithmetic routes must use infinite/cofinal coefficient-faithful occurrence, not a larger finite certificate.

### 3. Orientation is the common missing datum

Scalar positivity, absolute values, determinants, unitary gauges, positive diagonal completion, and common modular gain repeatedly erase the sign distinguishing a zero from its reflection. The explicit prime–archimedean circle carrier makes this sharp: ordinary probability, coercivity, Schur contractivity, and Carathéodory positivity coexist with negative reflected squares, while full reflected positivity is exactly RH. Live routes must retain orientation through signed incidence, indefinite pairing, paired channels, nonunitary magnitude change, singular boundary value, or source ancestry.

### 4. Pairing is necessary but not sufficient

CLG/TTF, Q, CDC, HB, LI, JAS, K-RVM, APF, S6F, WS2, FZZ-P, RBH, PW-B, WBF, XST, NDS, and KMSS are paired or multi-channel and nonclassical. One-leg complex-linear and even merely conjugate-homogeneous reporters are impossible on strict-right fibres, while paired Hermitian incidence survives. Pairwise Gram data can still be insufficient: an independent third compound appears at three primes, and the Cayley higher-shadow model exhibits a transverse grade invisible to every quadratic obstruction but detected by secondary confluence. Every descended linear observer of the closed two-clock relation is zero, while its oriented area survives by cohomological transgression. Diagonal doubling is blind by thermofield centrality, paired determinant purity is blind for irregular duals, and finite-cylinder doubling is rigid by formal étaleness. The surviving object must carry relative, higher mixed incidence at genuinely infinite completion.

### 5. Positive completion can fail before the spectral problem

TD/C1 fails at zeroth mass. Positive diagonal repair fails at critical jets, and off RH any successful repair must feed divisor-isolating atoms by at least their negative deficit. Route J fails from unavoidable diagonal energy. Repair of a full infinite negative sector cannot be compact or Schatten. These are normalization obstructions, not missing estimates. Viable successors must alter the carrier before positivity projection or accept a genuinely noncompact or atom-fed correction.

### 6. Ground and limit order cannot be interchanged

O needs control of every near-ground sequence, not one good Rayleigh vector. CLG/TTF needs matrix positivity/cofinal no-escape, not pointwise positivity of its explicit theta kernel, and F2/CSB need a source-selected cofinal section rather than arbitrarily accurate finite moments. U shows the same order-of-limits obstruction in moving Hankel degree: fixed-degree recession is positive and cofinal renewal is source-priced, yet only a synchronized upper work law can compare them. A nonzero Xi reflection charge defeats every moving finite prime-power approximation and is exactly conditional information escape hidden by vanishing source mass. Literal first-clock recurrence is exactly cofinal tempering; its failure pins one persistent occupied escape mode. SV2’s nested no-escape and cancellation accounting are closed; its remaining obstruction is the sign of explicit finite prime certificates. Strong/weak convergence cannot replace Calkin norm or singular graph control where those topologies remain active.

### 7. Singular interfaces remain credible

Regular bounded descent is repeatedly terminal in L, R, PSRC, PCS, and P. L has the literal completed Meyer–Tate differential, source-selected singular Gamma-six graph, unique Sonin physical transport, and multiplicity-complete vertical defect; its missing theorem must annihilate the existing physical image in the fixed source system, not construct another comparison. Stokes object/morphism descent and finite analytic Witt pairing are also closed. Covariant Stokes flatness is automatic but fixed-system untwisting is critical-line selection. Rees quasianalyticity proves the surviving exponential-small sector cannot be recovered from all analytic boundary jets. CDC and XST add semantic and spin-cover descent; NDS supplies a non-erasing universal conductor target, while KMSS adds mutual-statistics descent. Reduced nodal fibres and finite formal étaleness are blind, so remaining interfaces are coefficient-faithful boundary-value, closed-graph, residue, Calkin, infinite-action, oriented nearby-cycle, indefinite, nonanalytic, or genuinely completion-level semantic descent.

### 8. Dynamic selectors must act before late-time smoothing

HB, FZZ-P, and PW-B show fixed equilibrium, diagonal charge ensembles, universal neutral-pair mixing, sector-local absorption, recoil, fixed scale, norm-preserving two-mode completion, Jost passivity, and pure retarded Evans determinants do not orient horizontal displacement. HB has causal wavepacket excitation, common bright mediator input, unconditional adaptive-clock mixing, exact passive stationary persistence, and decay of every finite local/finite-energy continuum return. Therefore neither mixing nor late-time smoothing is the selector. Any asymptotic cancellation must come from a nondecaying threshold term with one forced nonzero limit. The unresolved datum is source exclusion/orientation of that threshold together with synchronization to the standard quadratic clock. Angular Noether transfer is one realization of that common-clock law. Strict non-Markov memory supplies a real infinite response channel but not its Xi orientation.

### 9. Corpus-native nonclassical topology

JAS joins finite prime-support cubical connection, valuation/Rees depth, higher compound order, infinite theta reflection current, two-clock transgression, and closed prime-Poisson sewing. CDC treats an off-line zero as one semantic repair splitting into two metric provenances. XST treats it as failure of a completed error fibre to inherit ambient theta half-density spin. NDS retains multiplicity in an oriented conductor/nearby-cycle class after reduced nodal geometry collapses; KMSS asks whether the same mixed jet descends independently of graded source ordering. WBF treats it as fracture of reflected all-prime boundary sectors, equivalently a Hermitian Stokes barcode and hidden-information escape. U treats false RH as a cofinal, source-priced singular renewal phase inside a canonical parabolic degree–mass cone. HB asks whether full nonlinear source synchronizes every causal bright sector to one Hawking clock. S6F retains strict odd orientation after infinite Fock completion; WS2 finds the sharp two-step irregular counterterm and quadratic anomaly. These are corpus-native architectures, not classical zero-free, mollifier, explicit-formula positivity, or Hilbert–Pólya variants.

APF adds a corpus-native infinite paired source index and trace before zeta multiplication; its missing trace-annihilation and divisor-exhaustion laws prevent promotion to a live route. S6F and WS2 are two genuine new interfaces, but not new live branches: one lacks Xi landing, the other exact source occurrence. K-RVM, FZZ-P, RBH, and PW-B are also nonclassical candidates, but their decisive scale, balance, or spectral selection remains target-fed. W2C remains a unifying receiver rather than an independent producer.

## Normalized frontier verdict

The corpus does not support a count of 58 independent attempts. It supports overlapping branch labels built from six primitive gates and seven receiver complexes.

- CCM-FU, G, and P meet at the four-unit Ward/boundary receiver. P has its literal Burnol Gram and central-band curvature budget, while CCM has exact polar/terminal-flux separation; both still fail at completed high-frequency source transport. This collapses endpoint ownership, not their distinct source handoffs.
- C1, O, Q, CLG/TTF, UEB, SV2, FD2, and S6F are different realizations of one global-selection obstruction: finite or pointwise positivity, one explicit seed, finite negative-index control, or even a positive infinite Fock supertrace does not control every cofinal ground direction without a faithful landing.
- NB/BD, F2, STC, CSB, U, and their Sonin/Hankel/Bernstein candidates are cofinal-selection variants. Their finite objects differ; their common missing theorem chooses and uniformly controls one moving source family.
- L, CDC, PSRC, PCS, TCD, JAS, XST, NDS, KMSS, WBF, and the survivors of R are descent variants. Stokes object descent, L's completed arithmetic differential and singular physical transport, and R's singular corona are formal; the common missing theorem is source-forced fixed-system annihilation, orientation, or transgression of the surviving class through singular or infinite completion.
- D2, E, G-CE, SP-E, SCE, T1, T2, HC, and the Wold/Euler candidates are signed-incidence variants. Hall expansion, passivity, shell defect, Abel moment, and current cancellation are presentations of `ORD`, sometimes coupled to `COF`, `LAND`, or `ORIENT`.
- HB, FZZ-P, and PW-B are one nonlinear-scattering family. Exact poles, branch residues, causal brightness, adaptive clocks, mass-Cayley unitarity, and copywise classifiers do not supply `DYN`. Passive stationary and decaying-return cancellation are excluded. HB's remaining law is source control of the nondecaying threshold channel together with common-clock order selection.
- K-RVM, APF, WS2, W1C, IRK, FD2, and operator forms of C1 are operator-occurrence variants. APF supplies source-first odd Fredholm orientation but not trace annihilation or divisor exhaustion. WS2 supplies the sharp trace-class relocation and positive determinant anomaly but not spectral identity. Universal singular-value transfer fixes every exact self-adjoint Xi carrier at Schatten abscissa one, determinant genus one, and the logarithmic weak-trace law; finite superquartic Fock and finite commuting-dilation models are excluded. Remaining `LAND` problem is exact: construct occurrence, spectrum, and determinant from primes without ordered zeros.
- WBF’s conserved source-pointed normal jet is not a new independent route. Lean identifies its extension energy with Deninger Hodge curvature, fixed-source Stokes excess, Meyer/Gamma modular log energy, transverse spectral energy, Hermitian Stokes-barcode width, and reflected prime-tail entropy. These are presentations of one durable `ORIENT` invariant after ordinary frame collapse. Its global vanishing is exactly RH; the open theorem is the same source-normal `LAND + COMP` gate encountered by L and R descendants.

Consequently, recombining labels is progress only when one source theorem discharges a shared gate across more than one receiver complex. A renamed composite, another RH-equivalent endpoint, or a bridge between already equivalent receivers does not create a new route. Current strongest merger architecture is:

`literal source -> reflection-odd mixed incidence -> coefficient-faithful singular completion -> cofinal whole-state/no-escape control -> existing RH receiver`.

Every node has receiver-level or finite-stage realizations in multiple complexes. No Lean theorem supplies one source law with enough quantitative strength, global compatibility, and completion continuity to traverse the chain. That coupled `ORD/COF/ORIENT` producer followed by `LAND/COMP`—or its full nonlinear `DYN` specialization—is the actual frontier.
