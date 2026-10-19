# Hard obstacles: open mathematics and research directions

This report is based on the route ledger docs/reports/rh-current-frontier-map.md

## Open mathematical obstacles, deduplicated

The eight families below organize the gap. They are **not proved irreducible or independent**, and a single successful route could bypass many optional constructions. **B-RH** marks a target sufficient for RH; **B-C** marks an unproved construction/transfer whose truth and ultimate usefulness still require testing.

### O1. Critical arithmetic cancellation and complete weighted energy

**Entries:** WL, MC, PM/FZZ-P, CTF, PBM, RB and JAS; BVI supplies an interface. FU/RP/LI share related history versions listed in O4.

Classical targets include `M(x)=O_η(x^(1/2+η))` for every `η>0`, the square-root-with-logarithms Chebyshev criterion, regularized-series convergence for every `σ>1/2`, or vanishing Nyman/Báez–Duarte approximation error. Each is an unproved **B-RH** target.

A precise current BVI/PM sufficient target is

\[
\forall\delta>0\;\exists\varepsilon\in(0,\delta)\;\exists B_\varepsilon<\infty\;
\forall T\ge1:\quad
\mathcal I_\varepsilon(T)=\sum_{n=1}^{T}
\frac{I_\varepsilon(n)^2}{n(n+1)}\le B_\varepsilon,
\]

with the literal `I_ε=pmBezoutInteriorPrefix ε`. The [receiver](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean) already gives the unconditional range `ε≥1/2`. The missing range is cofinal towards zero, with constants allowed to depend on damping.

The complete Vaughan expansion has five components and 25 ordered Gram terms. Its existing logarithmic source saving produces an energy majorant `n^(−2ε)/(log n)^8`, nonsummable below half damping. This is a failure of that upper-bound method, not proof that the true energy diverges. A concrete research target is a source-derived bound on the **mixed signed sum relative to the diagonal**, leaving summable dyadic losses. Such an estimate must retain density centering, active drift, covariance and endpoints. [Complete Vaughan identity](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CompletePronicVaughanCalibration.lean).

An intermediate bound at one fixed sub-half damping would be meaningful even without reaching RH. It must not be relabelled a complete solution of the cofinal criterion.

### O2. Nonnegativity of the complete arithmetic Weil form

**Entries:** RW, EWU, OWU, CHMD, HF, TT and related PA/SZ formulations; ACT attempts a producer, MSC a transport.

The central **B-RH** target is nonnegative complete form for every test in the receiving class, at every aperture. One exact odd-sector version is

\[
E_{\rm arch}(v)+E_{\rm prime}(v)
\ge \operatorname{phiDoobCoshMass}(v^2)
\qquad(v\text{ odd},\ v\in C_c^2(\mathbb R)).
\]

This is the corpus's [full odd Doob criterion](../../../formal/GaloisForLFunctions/RHTower/WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean), not positivity of one summand. In spectral coordinates it excludes the whole sign-changing odd bound-state band above `1/2`. The full-domain theorem, not finite multiplicity or one-signed exclusion, is missing.

Concrete possible mechanisms remain research: pay the reflected low-prime diagonal/collar by the complete jump remainder; establish a sharp capacity inequality; or construct a source-derived factorization on the actual domain. The single-shift ACT supersolution and uniform THIM absorption shortcuts fail. The survivor is an explicit defect comparison, with admissibility and full-class coverage still required. Near-null families forbid some positive-gap ambitions while leaving semidefinite positivity possible.

### O3. All-order moment, phase and critical-parameter control

**Entries:** TH, HCF, PA, LA, JAS; HJ and SEC expose related divisor/jet tests.

**B-RH:** prove every required Hankel/Bezoutian/heat-grid form positive at a common admissible parameter; all Hausdorff orders at their residual shifts; or the actual critical phase/current condition. A fixed order with its own eventual threshold is not a common all-order theorem. A finite power window with endpoints moving to infinity is not finite work.

HCF already has two prime-log grid criteria after polar cancellation; their arithmetic signs remain open. A single complete grid has aliases. Two-grid positivity and reconstruction of arbitrary packets are distinct problems. Forward heat evolution and positive shifted kernels do not control the original unshifted object. The known [Jensen hyperbolicity results](https://arxiv.org/abs/1902.07321) and [de Bruijn–Newman lower bound](https://arxiv.org/abs/1801.05914) illustrate established progress without supplying the missing quantifiers.

### O4. Complete history bounds and global signed transport

**Entries:** FU, RP, LI, TG, WD, GTA, SZ; APF, EGC and FEL have candidate versions.

**B-RH** for the established receivers: bounded completed Abel moments; a full-history linear floor; paired-Li lower floors on growing windows; a nonnegative residual plus sub-unit integral trace; vanishing Ward cap; rank-uniform transverse decay; or a complete moving-boundary Wronskian sign. These are different observable-specific targets, not one proved interchangeable estimate.

The missing mechanism must pay prior history, newly admitted blocks, moving core, high-LCM terms, cross covariance, residue/Gamma corrections and endpoint drift. A decrease at selected cutoffs, a small difference of two large energies, or strong convergence of every fixed packet is insufficient. Candidate contour/trace/likelihood schemes additionally need a faithful arithmetic landing (**B-C**).

### O5. Deterministic recurrence with conditioned tails

**Entry:** BAG.

**B-RH:** find common physical return heights for actual zeta on each required right-strip disc by controlling the centered tail on finite-head return events. The exact recurrence formulation is a sufficient corpus theorem; its converse is not asserted here.

Unconditioned mean square is already established. Conditioning on density `κ` can cost `1/κ`; the head length, tolerance, event density and tail cutoff are coupled. A valid next theorem must bound this actual conditional mean or otherwise prove common-height recurrence. An arbitrary polynomial or doubly exponential cutoff prescription has no authority without derivation from those parameters.

### O6. Independent arithmetic realizations and source-to-receiver constructions

**Entries:** geometric parts of HF/TG/RN and ACT, APF, BSH, CDC, DR, EWJ, FEL, HJ, IRK, MSC, PCS, PTR, RFHM, SC, SEC, W1C, WBF and PW-B.

These are **B-C** tasks until the proposed object and landing are fixed: positive arithmetic cohomology with the correct trace; a mate or descending potential; a globally compatible root; an integral projective lift; a faithful Sonin transport; a defect-preserving shift model; a continuum port; an arithmetic Lee–Yang limit; or a depth-uniform certificate stream. Their desired full packages would be RH-sufficient where the associated receiver is proved.

None follows from constructing an arbitrary self-adjoint operator, positive finite spin model, formal determinant or scalar genealogy. Prove literal arithmetic coefficients, completion/poles, domain, multiplicity and converse spectral identification where needed. Zero-based proofs remain permitted; what cannot be assumed is the positive/location property the argument is meant to establish.

### O7. Quantitative approximation and limits in the complete receiving form

**Programmes:** APT, BiScale, BVI, THIM; applications across RW/EWU/OWU/HF, PM/CTF, SZ, RN and several candidates.

**B-C:** construct a family whose complete-form approximation error tends to zero in the same regime where it detects a hypothetical negative direction. Track growing support, coefficients, anchor size, height, damping, origin concentration and polar escape. If the resulting family is separating/dense and independently nonnegative, its full theorem becomes **B-RH**.

BiScale's error `K²+2K‖F_ref‖` makes the needed accuracy explicit; it does not make `K` small. APT supplies a joint complete-form smoothing error for arbitrary growing finite translated-tent patterns, and the same family detects an explicit off-line model. **The remaining steps are actual arithmetic sign and sufficient actual-zeta separation/coverage.** Its direct critical-tail analysis is a separate unfinished route. THIM's primitive near-null family is not a density theorem. A candidate compactness theorem must survive the actual-prime escaping packet counterexample, and must preserve the complete form, not only unweighted `L²` mass.

### O8. Every-height exclusion and residual exceptions

**Entries:** LA, XN, WD, HCF, JAS and any localization proposal; SRT is the diagnostic.

**B-RH:** prove that every possible off-line configuration is excluded, including clusters, near-double pairs and a finite residual exceptional set. The corpus's exact diagnostic split is approach-to-line plus the asymptotic abscissa law; it is not a mandated proof format.

A localization mechanism needs joint profile/height/aperture bounds strong enough to reveal the displacement it claims to exclude. SRT shows fixed-profile eventual positivity can hold without this selectivity. XN needs interior disc margins, not just boundary sign. Global zero density and arbitrary finite-height checks do not by themselves remove residual exceptions. A theorem controlling an entire cluster could avoid separately counting its members.