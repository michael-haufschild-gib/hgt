# RH: mechanisms, intermediate targets, and missing mathematics

The strongest opportunity is to obtain **signed arithmetic control of the complete Weil form at its detection scale**. Existing results supply much more than a collection of RH criteria: they identify the ground state, compute conductor energies, establish growing-overlap positivity, expose exact cancellations, and locate the losses preventing those facts from meeting an RH receiver. The next advance should exploit this structure without discarding its signs.

For intermediate results, two targets stand out: **a moving cyclotomic near-band estimate for a three-quarters strip**, and **a signed prime-pair surplus estimate for 75% simple critical-line zeros**. Both have concrete arithmetic expressions and established transfers to the desired conclusions. Neither missing estimate is currently supplied by the inspected results.

I do not find a supported, wholly different RH proof that avoids all existing walls. I do find a plausible change of mechanism: replace global approximation in operator norm by relative quadratic-form control, supplemented by arithmetic rigidity of hypothetical negative states. This remains a research proposal, not a proof or a claim of novelty across mathematics.

## Evidence and interpretation

This report uses the six requested documents, corpus searches following the programme index from oldest to newest, and the resulting Lean declarations and source. No other Markdown sources, builds, or web searches were used. The index contains repeated programmes; its final reading also includes `EdgeHodgeTheory`, for 61 entries. That directory supplied no Lean source or indexed declarations, so no mathematical claims are attributed to its unread README. Research facts and declaration records are retained in [the research log](../../../logs/astra-rh-research.log) and [corpus evidence](../../../logs/astra-corpus-evidence.jsonl).

“Established” below refers to the mathematical results recorded in the supplied ledgers and inspected Lean statements, not a fresh dependency audit. Proposed estimates are identified explicitly. Global novelty cannot be established from this restricted source set.

Two distinctions change the answers materially:

* **The supplied evidence does not establish the proposed 7/8 baseline.** The frontier map labels the September 2026 quasi-RH manuscript as an external claim. Local detector and exponent results do not discharge its independent continuation input. Thus an improved strip must be treated as a new target, rather than an improvement to a theorem established by this review. See the external-claim discussion in [the frontier map](../rh-current-frontier-map.md) and [killed routes](../rh-killed-routes.md).
* **The local census is substantially ahead of the usual historical baseline.** `simple_critical_proportion_ge_67250071` states
  \[
  \liminf_{T\to\infty}\frac{N_0^{\mathrm{simple}}(T)}{N(T)}
  \ge 0.67250071.
  \]
  This uses the project's pinned `Zeta23` dependency. The separate four-fifths result concerns **distinct ordinate fibres**, not zeros counted with multiplicity. It therefore does not already prove 75% critical-line zeros. Sources: [simple-zero census](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean), [ordinate census](../../../formal/GaloisForLFunctions/RHTower/Zeta23CriticalOrdinateCensus.lean).

### What the chronological development has achieved

The sequence is not merely a succession of renamed routes. It progressively separates four tasks: detecting a defect, representing it arithmetically, identifying its source, and proving its sign or size.

| Programme entries, in supplied order | Mathematical development | Remaining distinction |
|---|---|---|
| 1–10: arithmetic positivity through arithmetic compensation | Detectors, scale laws, incidence energies, continuation, and compensation connect prime errors to zero depth. | A detector and its exact rate do not produce the required arithmetic bound. |
| 11–19: Castelnuovo–Severi through biarithmetic geometry | Intersection, orientation, local divisors, successor arithmetic, and defect rigidity expose signed interactions between addition and multiplication. | Separate positive pieces do not pay their mixed term. |
| 20–32: multiplicative positivity through selective threshold laws | Positive duality, correlation, Künneth, correspondences, polarization, effectivity, gauges, and conjugate-diagonal geometry clarify what selects ζ and what merely reconstructs it. | A positive collided form need not be invariant under the required arithmetic action. |
| 33–40: electrostatics through Lorentzian geometry, including returns to pair correlation and renormalized potentials | Exact conductor energies and renormalizations make the signed boundary contribution visible. | The finite-horizon remainder must be controlled relative to a shrinking spectral floor. |
| 41–49: Gabor pinching through square-root precision | Quantitative census, index descent, counting, shallow-depth information, integer producers, and precision laws produce genuine partial results and sharp receivers. | Density is not uniform exclusion; an arbitrarily small slope excess is not a power-saving error. |
| 50–57: critical correlation through successor-shell arithmetic | All-vector positivity at small power-log overlap, sharper receivers, completed cyclotomic energies, pole-preserving transforms, Hilbertian realizations, and joint shell cancellation narrow the unpaid arithmetic terms. | Profile matching, exceptional directions, and signed mixed terms remain decisive. |
| 58–60: resonance, adelic Krein, renormalized intersection | Dynamical realization obstructions, exact gluing indices, heat-index laws, and the quadratic Riemann–Roch equivalence unify the obstruction. | A constructed carrier or abstract section-function interface is not an independent positivity theorem. |
| 61: Edge Hodge | Listed programme; no Lean mathematics available in the permitted evidence. | No result inferred from its name. |

The [unification ledger](route-unification-ledger.md) and [obstacle analysis](route-obstacles.md) identify a common obstruction: the ordinary index
\[
\kappa_\zeta=\operatorname{negIndex}K_\zeta
\]
counts distinct right-half-plane zeros, and the relevant pole, boost, Markov, and harmonic hyperplanes coincide. In particular, the index should not be confused with a multiplicity-weighted census. Conjugation makes a nonzero ordinary index at least two. RH is therefore equivalent to \(\kappa_\zeta=0\), and also to \(\kappa_\zeta\le1\).

This does **not** prove that every future method must use the existing machinery. Equivalent conclusions can admit different proofs. Likewise, a no-go for a specified information class does not prohibit an estimate using additional arithmetic information. The useful reading of [the walls ledger](walls-ledger.md) is:

* **Σ:** how can arithmetic force the critical sign?
* **Π:** how can it do so at a scale that resolves every possible defect?
* **Γ:** what property makes the argument specific to the actual ζ source?

## 1. A mechanism that could cross a wall

### Preserve the complete signed form through the final estimate

The most promising opening is between the positivity already proved and the way its error is presently estimated.

For the tilted spline, the corpus proves all-vector positivity, with a uniform floor proportional to \(c^{-7}\), throughout
\[
1\le c\le (\log N)^\alpha,
\qquad
0<\alpha<\alpha_*=
\min\!\left(\frac1{500},\frac1{60C_{\rm cut}}\right).
\]
This is a substantial theorem, not merely positivity on finitely many preferred vectors. See `eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_powerLog` in [the power-log positivity theorem](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap.lean).

But its proof mechanism pays a squared residual against the square of the floor. The displayed fixed-conductor contributions include
\[
\text{residual}^2\ \lesssim\
m^4\left(\frac{c^5}{\log N}+\frac{c^3}{\sqrt{\log N}}\right),
\qquad E_1(c)\asymp c^{-7}.
\]
Dividing by \(E_1(c)^2\) introduces \(c^{19}/\log N\) and \(c^{17}/\sqrt{\log N}\). Even the first term alone prevents this argument from reaching exponent \(1/19\); the other terms and growing-conductor summations impose further restrictions. Improving a prime estimate by another fixed logarithmic power does not automatically remove these losses.

There is a second restriction: current confinement places a nonpositive vector inside a conductor cutoff exponential in a power of \(c\). The underlying \(c^{16}\) defect bound already puts pressure on the square-root conductor range; the full positivity proof uses a larger exponent. The established defect-only counterexamples rule out replacing this with subexponential confinement by an abstract argument using only the same defect.

**Proposed change:** estimate the actual signed quadratic form after combining Gamma, pole, prime, and successor-shell terms. Use a relative estimate in its natural conductor energy, rather than an absolute residual estimate followed by division by the smallest floor twice.

Here is a precise formulation of the desired mechanism. On the pole-orthogonal space, choose a finite-horizon decomposition into a weak conductor sector and its full orthogonal complement. After accounting for the actual Gram matrix, write
\[
W_{N,c}=\begin{pmatrix}A&B^*\\B&C\end{pmatrix}.
\]
The task is to prove coercivity of \(C\), then control
\[
A_{\rm eff}=A-B^*C^{-1}B.
\]
If \(E\) is the positive completed-conductor model on the weak sector, a sufficient arithmetic estimate is
\[
\langle(A_{\rm eff}-E)u,u\rangle
\ge-\eta\langle Eu,u\rangle,
\qquad \eta<1.
\tag{S}
\]
The new mathematics would be **the source-specific estimate (S)**. Schur complementation itself is standard and already available in [the corpus](../../../formal/GaloisForLFunctions/HTGeometry/CoerciveFiniteSchurComplement.lean).

Several existing facts make this more concrete than a request to “prove positivity”:

1. The completed ground energy is attained at conductor one, which is the pole direction. Conductors large relative to \(c\) have a positive individual energy floor; fixed low conductors are where the floor degenerates. This identifies a useful decomposition, although positive diagonal energies alone do not establish positivity of the complementary block.
2. The joint top-band shell–pole expression has cancellation unavailable to separately estimated terms. The separate-payment obstruction therefore does not kill a jointly signed estimate. See [joint top-band cancellation](../../../formal/GaloisForLFunctions/SuccessorShellArithmetic/TopBand/NonpolarJointCancellation.lean).
3. Prime dilation has an exact positive square-energy identity on conductor packets. Its diagonal weights are \(\log m+\operatorname{tameDifferent}(m)\); subtracting the appropriate packet-generator pairing cancels the torsion term. This gives a potential arithmetic energy for controlling mixed terms. See [prime dilation energy](../../../formal/GaloisForLFunctions/SuccessorShellArithmetic/Conductor/PrimeConductorDilationEnergy.lean).
4. The pole-preserving physical transform already exposes a positive defect contribution. What remains is the signed potential in the complete expression. An argument that ignores this potential has not paid the Weil form.

The first useful theorem would control **mixed growing-conductor packets after joint cancellation**, with weights comparable to their completed energies. A fixed-conductor calculation alone would not resolve the horizon problem. Nor would positivity of a large-density subset: one exceptional negative direction is enough to obstruct RH.

### Match the profile to the receiver

There is no legitimate shortcut from the tilted-spline positivity theorem to a smoother profile's completeness theorem.

The ledger gives tilted-spline RH receivers at full-space overlap \(2(\log N)^\alpha\), \(\alpha>1/4\), or on the pole hyperplane with \(\alpha>1/2\). Smooth profiles on that hyperplane have receivers at every positive power-log exponent. Their smaller Fourier tails also produce smaller floors. Smoothing changes both sides of the problem.

The sinc construction makes the issue particularly sharp. Its critical overlap satisfies
\[
c_N^*\asymp L(\log L)^2,\qquad L=\log\log N,
\]
and is defined by a Fourier-tail condition \(\tau(c_N^*)\log N\approx1\). The inspected receiver requires positivity at **every fixed multiple** \(Kc_N^*\), or along a divergent multiple \(r_Nc_N^*\) with \(N/(r_Nc_N^*)\to\infty\). One fixed bounded multiple covers only a bounded test-support window. See [the exact sinc overlap](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ReceiverRate/TheSincProfileHasAnExactCriticalOverlap.lean).

Thus a real wall-crossing result would be (S), or another signed complete-form estimate, at a receiver schedule **for the same profile**. A modest improvement within the existing regime would still be valuable if it demonstrates a new dependence on the floor; a better numerical exponent with unchanged losses would be less decisive.

### A complementary mechanism: classify negative states

A second possibility is a concentration-and-rigidity argument. Suppose a sequence of normalized pole-neutral vectors has negative complete energy at the relevant scales. Extract its possible arithmetic concentration profiles, retaining successor, dilation, Gamma, and pole information. Then exclude each profile from the exact source identities.

Candidate alternatives include concentration in a weak conductor packet, concentration near an additive–multiplicative incidence pattern, and escape through growing conductors. These are proposed alternatives to be proved exhaustive, not an established classification.

The decisive difference from killed confinement arguments is the input: **negativity of the complete source-specific form**, rather than boundedness of a source-blind defect. A successful theorem would have to retain the very signed information discarded by the existing counterexamples. It could control exceptional vectors without demanding a uniform small operator norm on the whole space.

## 2. A wildly different route that avoids the walls

**No such route is justified by the inspected evidence.** The project has already explored unusually diverse starting points: integer auxiliaries, sections and intersection forms, scattering, theta and heat flow, spectral realization, affine carriers, gauge selection, and symbolic dynamics. Calling one of these quantum, geometric, dynamical, or categorical does not create a new mechanism.

There is also an important logical distinction. A proof can avoid estimating the present Weil matrices. It cannot avoid having consequences for their index, because those consequences are equivalent to RH. “Avoid the walls” should therefore mean supplying an independent arithmetic principle, not avoiding every equivalent formulation of the conclusion.

The strongest candidate for a different *style of proof* is the nonlinear rigidity strategy above: assume failure, construct a limiting arithmetic object, and prove that it cannot support the simultaneous successor and dilation relations of ζ. That would resemble an exclusion theorem for coherent exceptional states, rather than construction of a positive approximation. However, it still has to solve Σ and Γ and retain Π-level resolution. It does not honestly satisfy the stronger request for a route touching none of the known obstacles.

Two tempting escapes are specifically unconvincing:

* **A new dynamical realization.** Prime-length rigidity and the archimedean obstruction already constrain finite and finite-virtual realizations. An infinite-state system with nonlocal memory could lie outside those no-go hypotheses, but no source-exact model with an independently proved zero-location theorem has been constructed here. Merely allowing infinitely many states moves the realization problem.
* **New section spaces or a Frobenius-like operator.** These could supply a genuinely new input if constructed independently from arithmetic. But the latest quadratic Riemann–Roch equivalence shows that abstract nonnegative section functions with Serre duality and degree-zero subquadratic growth can already encode the missing Hodge inequality. Naming such functions does not construct them. See [quadratic Riemann–Roch and the renormalized Hodge index](../../../formal/GaloisForLFunctions/RenormalizedIntersectionTheory/TheQuadraticRiemannRochIsTheRenormalizedHodgeIndex.lean).

The correct research posture is to pursue a new **source theorem**, with a finite or restricted consequence that can be proved before RH. I would not open another full route solely because its final object looks unlike the current ones.

Finite index and heat continuation do not presently provide an escape either. Finite ordinary \(\kappa_\zeta\) would already imply Lindelöf and a fixed zero-free half-plane, while permitting finitely many off-line zeros. For the external tensor square, finite index already forces RH: tensor amplification has strengthened the required input, not made it available. Likewise, the glued heat state has finite index at positive heat time and index one in the established large-time regime, but transporting that value to time zero requires excluding the very collision events encoded by the obstruction. Continuity of the source alone does not preserve the integer index.

## 3. Improving quasi-RH

Write \(\Theta=\sup\Re\rho\) over nontrivial zeros. A target \(\Theta\le b\) gives the symmetric closed strip \([1-b,b]\). Closed endpoints should not be silently converted into strict exclusion of boundary zeros.

### Best target: the actual cyclotomic near band

The completed arithmetic form has an unusually clean source-specific reduction. Define, for \(j\ge3\),
\[
a_j=\frac{\psi(j-1)-(j-1)}{j\sqrt{j-1}},\qquad a_1=a_2=0,
\]
and
\[
P_Q(z)=\sum_{1\le j<Q}a_j(1+z+\cdots+z^{j-1}).
\]
For \(Q=N+1\) and \(\omega_k=e^{2\pi ik/Q}\), the actual nonnegative remainder is
\[
R_N=\frac1Q\sum_{k=1}^{Q-1}|(1+\omega_k)P_Q(\omega_k)|^2.
\]
These are the literal Chebyshev coefficients, not a freely chosen positive model.

The corpus proves
\[
\Theta\le\frac34
\quad\Longleftrightarrow\quad
\forall\varepsilon>0,\ R_N\ll_\varepsilon N^{3/2+\varepsilon},
\tag{C3}
\]
and the corresponding equivalence between \(\Theta\le5/6\) and exponent \(5/3+\varepsilon\). See [cyclotomic completion](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ChebyshevCyclotomicCompletion.lean).

More usefully than the equivalence alone, there is an exact decomposition
\[
R_N=\operatorname{Far}_{N,K}+\operatorname{Near}_{N,K},
\qquad
\operatorname{Far}_{N,K}\le\frac{288N(N+1)}K.
\tag{C4}
\]
The near band consists of \(0<\min(k,Q-k)\le K\). Taking \(K=\lceil\sqrt{N+1}\rceil\) already pays the far part at order \(N^{3/2}\). The remaining concrete question is
\[
\boxed{\operatorname{Near}_{N,\lceil\sqrt{N+1}\rceil}
\ll_\varepsilon N^{3/2+\varepsilon}.}
\tag{C5}
\]
This would prove \(1/4\le\Re\rho\le3/4\). The missing estimate is not proved by the existing completion identity. See [the near/far decomposition and far-band bound](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ChebyshevCyclotomicTail.lean).

The geometry of this target matters. Each retained root has primitive conductor
\[
\operatorname{ord}(\omega_k)=\frac Q{\gcd(Q,k)}
\ge\frac Q{\min(k,Q-k)}\ge\frac QK.
\]
The unpaid modes are close to the constant frequency but have **large primitive conductor**. Fixed-conductor control or logarithmic conductor ranges do not reach them. Nor are they automatically the weak low-conductor sector of the complete Weil matrix; a transfer between these two decompositions would itself need proof.

For a general target \(b>1/2\), the scale suggested by (C4) is
\[
K\asymp N^{2-2b},\qquad \operatorname{ord}(\omega_k)\gtrsim N^{2b-1}.
\]
This identifies a family of intermediate targets:

| Target right boundary | Near-band width | Primitive conductors reached | Required remainder exponent |
|---|---:|---:|---:|
| \(5/6\) | \(N^{1/3}\) | at least order \(N^{2/3}\) | \(5/3+\varepsilon\) |
| \(3/4\) | \(N^{1/2}\) | at least order \(N^{1/2}\) | \(3/2+\varepsilon\) |

The useful new input would be cancellation for these actual moving packets, using their Chebyshev origin. Applying a source-blind large-sieve envelope to arbitrary coefficients risks reproducing the existing bound. Exact successor/dilation identities might help, but no established bridge currently pays (C5).

### Detector optimization: a narrower opportunity with a ceiling

The local Gram-budget analysis also identifies possible improvements, but they must not be mistaken for arithmetic theorems. For the model
\[
1+P^\nu+P^\kappa/Y,
\]
with \(\nu\ge0\), the five-sixths budget is feasible precisely in the recorded region
\[
\nu\le\frac1{15},\qquad \kappa+4\nu\le\frac43.
\]
Removing exceptional-frequency growth while retaining the ordinary \(P^2/Y\) cost gives the optimized boundary
\[
\frac{23}{27}<\frac78.
\]
That is a useful conditional design target. It is not a proved zero-free boundary: the required actual Gram estimate and continuation argument must still be supplied.

Moreover, even deleting both nonunit contributions leaves a minimum \(29/36>3/4\), due to the retained unit term and reflection allowance. The same detector cannot reach three quarters by improving only those two exponents. See `ordinaryGramBoundary_sharp_minimum` and `unitGramBoundary_sharp_minimum` in [the Gram tradeoff](../../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorGramTradeoff.lean).

### Integer producers: quantify the cost of approaching slope one

The producer result is stronger than a fixed Chebyshev constant:
\[
\forall\varepsilon>0\ \exists C_\varepsilon>0\ \forall x\ge2,
\qquad \psi(x)\le(1+\varepsilon)x+C_\varepsilon\log^2x.
\tag{P}
\]
It is obtained from multivariate parity-selective integer auxiliaries. The missing datum is the dependence of \(C_\varepsilon\) on \(\varepsilon\). See [producers approaching the main term](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/MultivariateParityAuxiliariesReachTheMainTerm.lean).

A useful proposed quantitative target is \(C_\varepsilon\ll\varepsilon^{-r}\) for some \(r>0\), uniformly for small \(\varepsilon\). Optimizing the two terms in (P) would give
\[
\psi(x)-x\ll
x^{r/(r+1)}(\log x)^{2/(r+1)}.
\tag{P1}
\]
Thus \(r<7\) would beat the 7/8 exponent; \(r=5\) would target 5/6; \(r=3\) would target 3/4. The corpus's one-sided precision laws connect these exponents to zero width. See [the integrality exponent law](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheIntegralityExponentIsTheZeroWidth.lean).

This is a conditional optimization, not a new producer theorem. Giving an explicit but exponentially large \(C_\varepsilon\) would not establish a fixed power saving. Any separately introduced \(\varepsilon\)-dependent starting horizon would also need quantitative control. This direction merits attention because it asks for an arithmetic complexity bound on actual constructions, rather than another equivalent definition of the desired exponent.

## 4. Reaching 75% on the critical line

**There is a precise opportunity, but no existing result in the inspected evidence reaches 75%.** The cleanest sufficient target proves 75% *simple* critical-line zeros, which is stronger than the requested multiplicity-weighted critical-line proportion.

The unconditional selected-profile certificate in the pair-correlation programme states, for every \(0<\eta<1/3\) and every \(\varepsilon>0\), that an admissible smooth profile \(u\) exists such that eventually
\[
\left(\frac{29}{36}-\varepsilon\right)N(T,2T)
-S_{u,\eta}(T)+M_{\rm off}(T,2T)
\le N_0^{\rm simple}(T,2T).
\tag{Z}
\]
Here \(S\) is the actual `primeCoalescentSurplus`; \(M_{\rm off}\ge0\) is off-line multiple-zero mass. Proper prime powers have already been removed with an \(o(N(T,2T))\) error. The source is `zeta_primeCoalescent_certificate_simple_and_offLineMultiple` in [the parity-sensitive transfer](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/ParitySensitiveRamanujanStabilizerTransfer.lean).

Consequently, the arithmetic estimate
\[
\boxed{S_{u,\eta}(T)\le
\left(\frac1{18}+o(1)\right)N(T,2T)}
\tag{Z1}
\]
for profiles admissible in (Z) would give 75%, since
\[
\frac{29}{36}-\frac1{18}=\frac34.
\]
The profile quantifiers are essential: an estimate for some unrelated smooth profile cannot be combined with the existential profile in (Z). One needs control of the certificate's selected profiles, or a common construction satisfying both requirements. Summing eventual dyadic-window bounds gives the corresponding asymptotic cumulative proportion.

There is even credit in (Z): a bound on \(S-M_{\rm off}\) would suffice. But using an unknown spectral credit to pay an unknown arithmetic surplus would not supply an independent proof. The purely arithmetic target (Z1) is cleaner.

### What must improve

The difficult term is a **signed, weighted prime-pair discrepancy beyond the usual threshold**. Its parity structure is already explicit: odd-prime pairs have even shift; the first two Ramanujan channels combine; odd moduli and their doubles pair; the surviving top octave cannot be omitted. A one-sided sieve upper bound cannot simply be inserted into a kernel that changes sign.

In the form-factor normalization recorded in the pair-correlation work, the needed trans-threshold integral is at most \(1/9\), whereas the available generic subthreshold positive-definite majorant gives only \(8/27\). Further optimization within the same relaxed information class cannot be assumed to recover the missing signed information. The task is to estimate the discrepancy against the oscillating weight itself, keeping parity and the full singular-series main term together.

The fourth-moment alternative is less mature. A sine-model moment calculation yields \(16/21>3/4\), but the actual ζ higher-moment results have restricted support. Extending a model identity beyond the proved support region is exactly the missing mathematics, not an established route to the percentage.

### Why the nearby results do not imply 75%

Four fifths of ordinate fibres can coexist with only two thirds of zeros on the line: take four heights each containing one critical zero, and a fifth containing a reflected off-line pair. Repetition of this counting pattern gives the stated ratios. This is a logical counting example, not a proposed ζ zero configuration.

Similarly, \(o(T)\) total squared depth or density-one exclusion at each fixed positive depth permits many zeros whose depths shrink with height. A near-line percentage is not an on-line percentage. The remaining shallow pairs are precisely where a signed coalescent statistic can contain information lost by depth moments.

## 5. Three questions to prioritize

These questions expose three different missing inputs. Success on one need not settle the others: a 75% census does not exclude a sparse deep exceptional family; a fixed strip does not force any prescribed fraction exactly onto the line.

### Priority 1 — Can joint arithmetic cancellation control the mixed weak sector relative to its true energy?

Prove an estimate of type (S) for the complete pole-neutral Weil form, including the full complementary block, on a growing schedule for a fixed profile. The eventual destination is an RH-complete schedule for that same profile.

**First decisive result:** a growing-packet signed bound after Gamma–pole–shell cancellation that removes a genuine inverse-floor loss, with the mixed Schur correction included. This is more informative than a stronger estimate on individual diagonal modes.

**Why first:** it attacks the common critical-sign obstruction and uses the project's strongest recent constructive results. It also tests whether the residual-versus-floor wall is partly an artefact of taking norms too early.

**Failure criterion:** if the proposed bound still uses only the source-blind defect, ignores exceptional vectors, or transfers positivity between unmatched profiles, it has not escaped the existing no-go or receiver gap.

### Priority 2 — Can the literal Chebyshev near band satisfy (C5), or its five-sixths analogue?

Estimate the actual packets at growing primitive conductor, beginning with the exact decomposition (C4). A three-quarters bound is the clearest target; five sixths provides a weaker intermediate exponent without changing the source.

**First decisive result:** a new arithmetic cancellation estimate on the moving near band, with its dependence on \(N\), bandwidth, and primitive conductor explicit. A theorem confined to fixed conductors does not address this question.

**Why second:** it offers a substantial zero-free strip from a single isolated nonnegative remainder. The far band, normalization, and transfer to zero width are already available. It also gives a direct test of whether successor/dilation structure can provide a power saving beyond generic coefficient bounds.

**Failure criterion:** proving positivity or coercivity of the completed Gram without an upper bound on its actual Chebyshev energy does not advance the strip.

### Priority 3 — Can the parity-correct signed prime surplus be bounded by \(N/18\)?

Prove (Z1) with the profile compatibility required by (Z), retaining the full trans-threshold range. A direct estimate for the weighted signed surplus is sufficient; a general theorem for all prime-pair correlations is unnecessary.

**First decisive result:** a signed discrepancy estimate for the actual oscillating kernel, controlling its positive and negative parts and improving the current positive-majorant obstruction, including the top octave and parity pairing.

**Why third:** it leads to a concrete 75% theorem and probes source-specific signed cancellation independently of the complete-matrix method. It targets shallow off-line pairs that density and depth estimates leave unresolved.

**Failure criterion:** a one-sided sieve estimate integrated as though the kernel were nonnegative, a sine-model moment substituted for an actual ζ moment, or a change from zeros to ordinate fibres does not prove the requested result.

The quantitative producer problem is the strongest reserve question. I would promote it if a construction begins to control \(C_\varepsilon\) polynomially, rather than merely making it explicit. I would give lower priority to another equivalent index criterion, an abstract section-function interface, or finite-rank positivity without a uniform rank-growth theorem.

## 6. What new mathematical field could supply the missing tools?

### Arithmetic rigidity at critical scale

This is a proposed organizing programme, not a claim that a new field has already been created. Its subject would be:

> How exact additive and multiplicative arithmetic identities constrain signed energy when the positive floor tends to zero, and how those constraints survive the archimedean boundary and growing arithmetic complexity.

The existing programmes already supply many of its objects. The missing contribution is a calculus that preserves cancellation, source identity, and quantitative resolution simultaneously.

### Questions and point of view

The basic question would not be “is this kernel positive?” in isolation. It would be: **which negative states are compatible with all the arithmetic relations that produced this kernel?**

This viewpoint suggests four foundational problems:

1. **Joint arithmetic rigidity.** Can a state remain nearly invariant under the relevant additive and multiplicative operations while being pole-neutral and carrying negative complete energy? If so, classify the states; if not, prove a quantitative incompatibility theorem.
2. **Signed boundary cancellation.** Which identities force a dangerous boundary term to cancel against an arithmetic interaction before either is estimated separately?
3. **Uniformity across scales.** How do horizon, overlap, conductor, rank, and zero-depth resolution interact? Which losses are intrinsic, and which arise from an unsuitable norm or decomposition?
4. **Exceptional-source rigidity.** Why can the actual arithmetic source exclude exceptional states that survive in unitary gauges, twins, or source-blind models?

This is closer to a theory of constrained signed energies than to a new collection of RH-equivalent positivity axioms.

### Objects

The natural objects would carry more information than a kernel alone:

* Arithmetic packets indexed by horizon \(N\), overlap \(c\), conductor \(m\), and an actual profile \(\phi\), together with their finite-horizon Gram matrices.
* Additive differences, such as \(f(n+1)-f(n)\), and prime dilation differences, such as \(f(pn)-f(n)\), with their exact noncommutation and divisor identities retained.
* The complete signed form, its pole functional, Gamma contribution, and prescribed running counterterm. The renormalization is part of the object, not an adjustable error allowance.
* Weighted conductor energies and mixed interaction forms, including Schur corrections and concentration profiles.
* Source data that distinguish actual von Mangoldt weights from gauges, together with theta/Poisson relations and conjugate-diagonal information.
* Integer defect measures and collision indices, accompanied by the analytic scales needed to detect them.

The global pole must be included correctly. The local-pole classification shows that summing local squares does not magically produce the single global square; the archimedean place supplies the necessary coupling. A theory that treats Gamma as an optional tail would discard a structural component of the problem.

### Language and foundational principles

**Exact identities before inequalities.** Keep pole, shell, diagonal, and Gamma terms together until the algebraic cancellation is visible. The prime-dilation square identity and joint top-band cancellation are examples of the required starting point.

**Relative energy before absolute norm.** A perturbation should be measured against the energy of the state on which it acts. The smallest ground floor should not be charged to every conductor and every mixed interaction unless the mathematics forces that charge.

**Source fidelity.** Every limiting or enlarged class must retain enough information to distinguish ζ. Unitary-twist invariance and pointwise closure are already known to lose essential selection information. A general theorem true equally for killed twins cannot establish the missing ζ-specific sign.

**Quantifiers are mathematical structure.** Fixed conductor, growing conductor, average conductor, and every conductor are different objects of study. So are a fixed test window, every fixed window, and a single schedule exhausting all windows. The theory must record these distinctions in its statements.

**Nonholomorphic information is allowed and sometimes necessary.** Collision, orientation, and conjugation cannot always be recovered from a uniformly stable holomorphic local reading. The existing gap-dependent detection results should guide the choice of observables, rather than be bypassed by an assumed universal detection scale.

**No new positivity axiom.** The foundations remain exact arithmetic, analysis, and constructions with independently proved properties. Adding “critical positivity,” “Frobenius compatibility,” or “subquadratic sections” as an axiom would encode the desired answer.

### Research topics

| Topic | First mathematical output sought | Wall addressed |
|---|---|---|
| Relative arithmetic form estimates | A growing-packet lower bound with the mixed correction measured in completed conductor energy | Σ1, Σ13 |
| Arithmetic concentration and rigidity | An exhaustive profile decomposition for negative complete states, retaining successor and prime dilation information | Σ1c, Σ1g, Γ3 |
| Boundary and renormalization identities | Joint control of Gamma, pole, and shell contributions beyond fixed packets | Σ1b, Σ12 |
| Moving-conductor harmonic analysis | A source-specific near-band power bound such as (C5) | Π2, Π9, Π11 |
| Signed prime-pair analysis | Kernel-specific discrepancy estimates that retain parity and crossing of the threshold | Π5, Π8 |
| Quantitative integer approximation | Polynomial dependence of producer cost on slope accuracy, including coefficient and support growth | Π3 |
| Arithmetic conjugation | An independently constructed correspondence explaining why the collided form has the required invariance | Γ4 |
| Effective integer-index detection | Resolution bounds tied to actual arithmetic data rather than an assumed zero gap | Σ8, Π13 |

Arithmetic conjugation deserves a precise caution. The corpus already distinguishes the invariant Weil pairing \(W\) from the positive collided pairing \(D\). For the latter, Hecke translation introduces depth factors; its symmetric second difference is a sum of nonnegative terms involving \(2\cosh(2\,\mathrm{depth}\cdot L)-2\). Vanishing of this defect is exactly the missing assertion. Computing \(D\) from theta data does not make it invariant. See [Hecke invariance of the collided polarization](../../../formal/GaloisForLFunctions/ArithmeticPolarization/HeckeInvarianceOfTheCollidedPolarizationIsRH.lean).

A successful field would explain this invariance from arithmetic construction, or avoid needing it by proving another independent source estimate. Reexpressing the same nonnegative defect in a new vocabulary would not suffice.

### Criteria for genuine progress

The programme should be judged by theorems with consequences before its final RH application:

1. **A new inequality, classification, or construction with discharged arithmetic inputs.** An implication whose premise is another known RH criterion does not qualify.
2. **Survival of the known counterexamples.** State exactly which extra source information excludes twins, exceptional conductors, escaping packets, and shallow clusters.
3. **Correct global coupling.** Preserve the pole-neutral hyperplane, Gamma contribution, and prescribed renormalization under every transfer.
4. **Quantitative usefulness.** Improve a genuine scale, floor dependence, signed surplus, or producer-cost exponent. A statement valid only after fixing every relevant parameter cannot establish a uniform conclusion.
5. **An intermediate consequence.** Examples include a larger matched positivity regime, a new moving-conductor estimate, a better actual census, or a quantitatively controlled family of integer producers.
6. **Exact formal statements.** Once a proposed input has a dependency-closed proof, its formalization should expose the same source, constants, scales, and quantifiers. The report's speculative inputs should not be promoted to established results before that step.

The common research question is therefore specific: **what arithmetic identity or rigidity law controls the exceptional signed interaction at the exact scale where existing positive structure becomes too weak?** The inspected corpus has located that interaction in several concrete forms. Proving one of the source estimates above would contribute new mathematical information; merely transporting the obstruction to another carrier would not.
