# BiScaleUncertainty: assessment of the independent-field claim

Date: 18 October 2026. Subject: `formal/GaloisForLFunctions/BiScaleUncertainty`.

**Verdict: the current evidence does not justify calling BiScaleUncertainty a new independent field of mathematics. It supports a substantial, coherent research programme within harmonic analysis, operator theory, analytic number theory, and arithmetic signal reconstruction. Some individual results may be original; their originality requires separate assessment.**

“Field of mathematics” has no formal admission test. This verdict concerns mathematical substance and explanatory reach. Neither a directory name nor a collection of correct theorems establishes that status. Conversely, using existing mathematics does not disqualify a new field: the relevant question is whether the work introduces a productive organizing principle with consequences beyond its constituent tools.

| Claim | Assessment |
| --- | --- |
| There is a coherent subject here. | Yes: logarithmic arithmetic grids, correlation constraints, energy, and recovery form a meaningful research theme. |
| Results can be studied independently of RH. | Yes: several statements concern ordinary Hilbert spaces, finite arithmetic signals, or interpolation operators without assuming RH. |
| Every result is already known. | Not established, and not claimed here. |
| Individual results may be new. | Plausible, particularly the precise arithmetic recovery and sharp classification results. |
| A new independent mathematical field has been established. | Not supported by the foundations and evidence examined. |

**1. The proposed distinction from existing harmonic analysis is overstated.**

The [README](../../../formal/GaloisForLFunctions/BiScaleUncertainty/README.md) opens by describing classical harmonic analysis through one locally compact abelian group at a time, then motivates the new discipline through simultaneous translation and dilation. That description is too narrow to support a novelty claim. Wavelet analysis already treats translation and dilation together through the noncommutative affine group. Grossmann and Morlet explicitly use representations of the `ax+b` group in their [1984 wavelet paper](https://epubs.siam.org/doi/abs/10.1137/0515056).

The logarithmic integer grid, chosen weights, and arithmetic constraints can still produce new problems. Their novelty must lie in the precise interaction and resulting theorems, rather than in combining additive and multiplicative operations as such.

Ramanujan spectral coordinates also have established antecedents. Orthogonality and products of Ramanujan sums are studied in [Tóth, *Sums of products of Ramanujan sums*](https://arxiv.org/abs/1104.1906); their use in periodic signal decompositions appears in [Vaidyanathan and Tenneti](https://pmc.ncbi.nlm.nih.gov/articles/PMC6939226/). These sources establish nearby prior mathematics. They do not, by themselves, establish that every exact covariance statement in this repository was previously published.

**2. Several advertised foundations are standard mechanisms in specialized notation.**

| Repository result | Mathematical mechanism | Consequence for the field claim |
| --- | --- | --- |
| `abstract_schur_krein_residual_coupling` in [AbstractBiScaleSystemAndSchurKreinCoupling](../../../formal/GaloisForLFunctions/BiScaleUncertainty/AbstractBiScaleSystemAndSchurKreinCoupling.lean) | Cauchy–Schwarz applied to vectors after orthogonal projection; the code uses scaled, division-free residuals. | Useful infrastructure, but the abstract inequality does not require logarithmic grids or interacting scales. |
| `hyperbolicCasimirInvariant_eq_autocorr` in [HyperbolicLorentzBoostAndMinkowskiLightCone](../../../formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicLorentzBoostAndMinkowskiLightCone.lean) | Integrate the hyperbolic subtraction identity, then divide by the positive factor `cosh(αx)`. | The defined invariant equals the original autocorrelation. This identity alone supplies no additional invariant information. |
| `biScaleJointEnergy_eq_zero_iff_const` in [UniversalRamanujanCovarianceAndBiScaleRigidity](../../../formal/GaloisForLFunctions/BiScaleUncertainty/UniversalRamanujanCovarianceAndBiScaleRigidity.lean) | A sum of nonnegative squares vanishes; adjacent differences then vanish. | The additive term already forces constancy. This particular conclusion does not require multiplicative coupling. |
| Optimal allocation and coupled gain in [OriginAllocationUniquenessAndCoupledSphereGain](../../../formal/GaloisForLFunctions/BiScaleUncertainty/OriginAllocationUniquenessAndCoupledSphereGain.lean) | Euclidean support/triangle inequalities, their equality cases, and Hilbert-space norm comparison. | Exact optimizers and defect formulas can be valuable, but their foundational mechanism is established convex geometry. |

The joint-energy example makes the issue concrete. Its definition is

\[
E_{\mathrm{bi}}(f)=
\sum_{n=1}^{N-1}(f(n+1)-f(n))^2+E_{\mathrm{dil}}(f),
\qquad E_{\mathrm{dil}}(f)\geq 0.
\]

Deleting `E_dil` leaves the same zero-energy characterization. A stronger foundation for a two-scale theory would identify a conclusion whose quantitative strength or qualitative content depends essentially on interaction between both structures.

Likewise, writing `Cαf(u)=cosh(αu)f(u)` and `Sαf(u)=sinh(αu)f(u)`, the identity

\[
h_{C_\alpha f}(x)-h_{S_\alpha f}(x)
=\cosh(\alpha x)h_f(x)
\]

comes directly from `cosh(a)cosh(b) − sinh(a)sinh(b) = cosh(a−b)`. Its applications may be nontrivial. The identity's name does not establish those applications or their originality.

**3. The five capstones do not themselves establish a new unifying theory.**

[FundamentalTheoremsOfBiScaleUncertainty](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FundamentalTheoremsOfBiScaleUncertainty.lean) packages results using conjunctions: covariance identities, rigidity, hyperbolic identities, allocation, polar enforcement, compensated producers, and finite-part estimates. This is a useful reference interface. Bundling these results does not establish a new mechanism connecting them, a classification of coupled systems, or a theorem that explains multiple previously separate phenomena.

The strongest case for a field would come from such a mechanism and its consequences. It cannot be inferred from the number of modules or from calling selected results “fundamental.”

**4. The repository contains stronger research candidates than those labels suggest.**

The current [PrimeFamilyPhaseRecovery](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimeFamilyPhaseRecovery.lean) source contains a concrete classification for its finite odd-prime sieve family:

- `primeFamily_independent_sign_blind`: all affine quadratic observations and translated moments through degree five remain unchanged under independent coefficient sign flips.
- `primeFamily_sixth_iff_common_sign`: full sixth-order translated data determine coefficients up to one common sign, including zero coefficients and empty support.

The [two-mode predecessor](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SixthSievePhaseRecovery.lean) supplies an explicit obstruction: lower-order data agree while sixth moments differ by `960`. These statements specify an observation class, its exact information loss, and a sufficient recovery order. That is substantive mathematical content.

Another concrete classification appears in [DivisorGridClosedRange](../../../formal/GaloisForLFunctions/BiScaleUncertainty/DivisorGridClosedRange.lean): bounded active runs characterize positive coercivity and closed range for the specified interpolation operator.

Neither example should be dismissed merely because its proof uses established tools. However, higher-correlation recovery already belongs to an established research area; [Kakarala's work on bispectral invariants](https://arxiv.org/abs/0902.0196) is one relevant comparison. The precise degree-six arithmetic result needs a theorem-level comparison, with hypotheses and observation families matched. This report does not claim that Kakarala's theorem proves it or makes it redundant.

**5. Formal correctness, novelty, and field status are different claims.**

A successful Lean check establishes a formal statement relative to its definitions and dependencies. It does not establish originality, importance, or independence of a subject.

The [field-closure card](../../drafts/pipeline/1-in-progress/biscale-independent-field-closure-2026-10-18.md) checks off “publication-ready” on the basis of updating the README with five fundamental theorems. That action establishes none of those broader claims.

The initial assessment also found a concrete mismatch between mathematical prose and formal statements. The capstone's opening comment gave

\[
h_{C_\alpha f}(x)^2-h_{S_\alpha f}(x)^2
=\cosh(\alpha x)^2h_f(x)^2.
\]

That identity is false in general. The actual theorem uses

\[
h_{C_\alpha f}(x)^2-h_{S_\alpha f}(x)^2
=\cosh(\alpha x)h_f(x)
\bigl(h_{C_\alpha f}(x)+h_{S_\alpha f}(x)\bigr).
\]

At `x=0`, put `R=h_f(0)` and `S=h_{Sαf}(0)`. Since `h_{Cαf}(0)=R+S`, the left side is `R²+2RS`, whereas the original comment claimed `R²`. Nonzero continuous compact sources supported away from zero with `α≠0` give `R,S>0`. That documentation error has been corrected. [ClassicalFoundationBoundaries](../../../formal/GaloisForLFunctions/BiScaleUncertainty/ClassicalFoundationBoundaries.lean) now formalizes the exact defect, equality condition and an actual smooth-source counterexample. The false statement was not a Lean theorem.

**The mathematical threshold still to meet.**

Follow-up work strengthens the arithmetic reconstruction branch: unconditional stability bounds, actual-sieve examples proving sharp exponents `1/6` and `1/3`, and explicit raw-measurement protocols now pass direct Lean source audits. For `M` allowed odd-prime modes, `64M²` fixed raw observations suffice with noise control; fewer than `M` fixed literal observations force a collision. An exact adaptive decoder needs at most `128M−64` observations for `M≥1`. These are concrete advances in the stated family, including unknown zero support. They do not supply the still-missing common-model classification and substantive discrete-to-continuum transfer. See the [stability evidence](../../drafts/pipeline/3-formalized/biscale-sixth-readout-stability-1810.md) and the [programme](../../drafts/pipeline/1-in-progress/biscale-field-development-1810.md).

A stronger claim needs a reusable theory of the coupled structures, a central result whose strength depends on their interaction, and sharp consequences across meaningfully different families. Existing reconstruction, realization, and energy results provide starting points. Proving exact boundaries, stability, and transfers between those branches would supply more evidence than adding further renamed elementary identities.

Solving RH is not a prerequisite. Nor must the subject stop using Hilbert spaces, Fourier analysis, or classical arithmetic. The missing evidence concerns a distinctive, productive mathematical organization and the new conclusions it enables. The companion [mathematical checklist](field-todo-1810.md) turns that standard into concrete research objectives; completing a checklist cannot mechanically confer field status.

**Assessment limits.** The initial verdict was a source and literature assessment, not an exhaustive correctness or originality audit. It inspected the five capstones, the abstract residual mechanism, selected underlying proofs, and the cited recovery/classification statements without running a Lean build. Subsequent component work has direct source and axiom audits, recorded in the [development programme](../../drafts/pipeline/1-in-progress/biscale-field-development-1810.md). Those checks certify their exact statements, not the whole repository or its originality. The internal searches use snapshots with unmeasured semantic completeness; no absence or global novelty conclusion is drawn from them.
