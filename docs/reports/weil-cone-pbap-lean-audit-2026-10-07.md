# Weil cone and PBAP in the Lean corpus

Status on 7 October 2026. This report distinguishes unconditional theorems, implications with open hypotheses, excluded constructions, and problems still open in the searched corpus.

**The corpus proves the existence reformulation and many strong rigidity theorems. It does not supply an unconditional integer-supported Weil-positive system, an unconditional proof of PBAP, or a general implication from mere existence to RH.** The remaining gap is mathematical, not just an unformalized compactness or spectral-representation argument.

## Exact objects and logical status

Write \(\Lambda\) for the von Mangoldt function and \(\lambda:\mathbb N\to\mathbb R\). Values at 0 and 1 are irrelevant to the Weil functional; equality statements generally concern \(n\ge2\).

Two different positivity predicates occur:

- `RHTower.WeilPositive`: positivity at every aperture on compactly supported \(C^2\) tests whose Fourier transforms vanish at both polar points \(\pm i/2\).
- `RHTower.WeilPositiveFull`: positivity on **all** compactly supported \(C^2\) autocorrelation tests, retaining the pole term.

Neither definition requires \(\lambda(n)\ge0\). “Weil-positive” describes the quadratic form, not the signs of its coefficients. The full predicate implies the polar predicate. This audit did not locate a converse for arbitrary weights; the two versions must not be interchanged.

For the full cone, set \(\mathcal W=\{\lambda:\operatorname{WeilPositiveFull}(\lambda)\}\). In the corpus's normalization,

\[
Q_\lambda(f)=A_{\rm full}(f)-\sum_{n\ge2}\lambda(n)L_n(f),
\]

where \(A_{\rm full}\) contains the archimedean **and pole** contributions and \(L_n\) is the real symmetric autocorrelation value at \(\pm\log n\), divided by \(\sqrt n\). Each individual compactly supported test sees finitely many integers.

Full PBAP says: every finite nonnegative combination of tests with \(\sum_i\alpha_iL_n(f_i)=0\) for **every integer** \(n\ge2\) has nonnegative combined \(A_{\rm full}\). It is not blindness only at primes, and the underlying test functions need not be nonnegative.

| Statement | Corpus status |
|---|---|
| \(\mathrm{RH}\iff\Lambda\in\mathcal W\) | Proved. [Full Weil criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeExposedPoint.lean:569). |
| Full PBAP \(\iff\mathcal W\ne\varnothing\) | Proved. [Full duality](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeOneSidedCriterion.lean:451). |
| \(\mathrm{RH}\Rightarrow\) full PBAP | Proved. [Forward implication](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeOneSidedCriterion.lean:475). |
| Polar PBAP at every level \(\iff\exists\lambda\), `WeilPositive λ` | Proved separately. [Polar duality](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivityPrimeBlindDuality.lean:558). |
| Full or all-level polar PBAP, without an RH/positivity premise | No proof located. |
| \(\mathcal W\ne\varnothing\Rightarrow\mathrm{RH}\) | No general proof located. Additional sufficient conditions are proved below. |
| Every \(\lambda\in\mathcal W\) equals \(\Lambda\) | No general proof located. This would imply the preceding detection statement, but is a stronger classification claim. |

Thus the proved existence equivalence must not be reported as an RH equivalence. Nor has the corpus established a counterexample to general detection.

## What has been proved beyond the reformulation

### Compactness and the finite to infinite passage

For polar positivity, existence at every finite aperture implies existence of one system positive at all apertures. The weights may depend on the aperture before taking the compactness limit. [Finite-level existence theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistence.lean:119).

For full positivity, the normalized cone \(\lambda(0)=\lambda(1)=0\) is compact in the product topology. More sharply,

\[
\mathrm{RH}\iff\forall N\;\exists\lambda\in\mathcal W\quad
\lambda(n)=\Lambda(n)\quad(2\le n\le N).
\]

The extension must already satisfy **all** full-cone tests. Checking a finite matrix of test vectors is weaker. Compactness supplies the passage to a limit; producing the compatible positive extensions remains open. [Compactness](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeCompactness.lean:166), [finite-prefix criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeCompactness.lean:177).

### An exact extremal target

An explicit Riemann-kernel functional \(\ell\) satisfies

\[
\lambda\in\mathcal W\Longrightarrow
\ell(\lambda-\Lambda)\le0,
\qquad
\ell(\lambda-\Lambda)=0\Longrightarrow\lambda=\Lambda.
\]

There is no additional summability premise in this capstone. Also, if both \(\Lambda+w\) and \(\Lambda-w\) belong to the full cone, then \(w=0\). These prove a supporting inequality and rigidity at equality; they do **not** prove that equality is attained, or that \(\Lambda\) belongs to the cone. Calling \(\Lambda\) an “exposed point” must retain that membership qualification. [Exposure](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeExposedPoint.lean:523), [extremality](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeExposedPoint.lean:532).

The exact remaining optimization target is already an RH criterion: construct a full-positive \(\lambda\) with \(\ell(\lambda-\Lambda)\ge0\). A polar formulation replaces this by explicit archimedean dual inequalities on an exposing ray, at every cutoff and aperture, with a vanishing box-tail correction. **That strengthened dual inequality is RH-equivalent; ordinary PBAP is not known to be.** [Extremal criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeExposedPoint.lean:585), [prime-free dual criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPolarConeExposedDuality.lean:604).

### Spectral representation and continuation are already closed

Assuming only full Weil positivity, Lean constructs a positive boundary measure \(\mu_\lambda\) and proves

\[
W_\lambda(f*\widetilde g)
=\int\widehat f(t)\overline{\widehat g(t)}\,d\mu_\lambda(t).
\]

The completed logarithmic derivative has a holomorphic continuation \(\Phi_\lambda\) to \(\Re s>1/2\), with \(\Re\Phi_\lambda\ge0\). No separate spectral-measure or Herglotz hypothesis remains at this stage. [Polarized representation](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConePolarizedRepresentation.lean:143), [holomorphy](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeHerglotzCriticalHalfPlane.lean:395), [nonnegative real part](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeHerglotzCriticalHalfPlane.lean:386).

Every such system also has a smoothed prime-counting law with error \(O_f(\sqrt x)\), for each fixed admissible autocorrelation smoothing. Its Poisson-smoothed spectral count has zeta's main term, with bounded error in the stated smoothing:

\[
\int K_T\,d\mu_\lambda
=\frac T2\log\frac{T}{2\pi}-\frac T2+O(1).
\]

These are consequences of a hypothetical producer, not constructions of one. The counting theorem is about \(K_T\), not an unsmoothed integer-valued zero count. [Smoothed square-root law](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeSquareRootPNT.lean:85), [spectral counting](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSpectralCounting.lean:317).

### The exact detection obstruction is visible in the residue theorem

On \(\Re s>1\), the deviation series continues as

\[
D_{\lambda-\Lambda}(s)=\frac{\xi'(s)}{\xi(s)}-\Phi_\lambda(s).
\]

At any zero \(\rho\) with \(\Re\rho>1/2\), its residue is **exactly the multiplicity of that zero**. The positive Herglotz term is holomorphic there and cannot absorb that pole. This does not itself give a contradiction: the continued deviation series is not known to be holomorphic throughout that half-plane. Any successful detection argument must prohibit this behavior using additional arithmetic information. [Exact residue theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeDeviationResidue.lean:41).

### Several sufficient detection hypotheses are fully formalized

| Extra hypothesis on a full-positive system | Proved conclusion and remaining issue |
|---|---|
| Half-integer counting: \(2\mu_\lambda((a,b])\in\mathbb N\), for endpoints in one full-measure set | \(\lambda=\Lambda\) and RH. No prescribed zeta ordinates are required. Producing this quantization is open. [Theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilHalfIntegerMassRigidity.lean:297). |
| A positive atomic representation whose cumulative-mass phase settles at a power rate in mean | \(\lambda=\Lambda\) and RH. The theorem retains atomicity, inverse-square mass summability, ordinates tending to infinity with \(t_j\ge1\), and the quantitative phase condition. Nonresonant almost-periodic limiting phases are also covered. [Settled phase](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSettledAtomicPhase.lean:61), [almost-periodic phase](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSettledAtomicPhase.lean:179). |
| Lower spectral-deficit density zero | \(\lambda=\Lambda\), hence RH. Deficit counts every off-line zero copy with weight 1 and missing mass at critical zeros. This hypothesis is not supplied by the smoothed counting main term. [Deficit theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSingularDeficitCounting.lean:445). |
| Bounded \(\zeta/F_\lambda\) on every strict inner half-plane \(\Re s>x>1/2\) | Together with the producer, equivalent to RH. Boundedness also forces weighted absolute control of prime deviations; it is a substantive extra input. [Bounded-quotient criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilProducerZetaQuotientBohrRecurrence.lean:474), [prime-deviation bound](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilProducerZetaQuotientBohrRecurrence.lean:617). |
| \(\lambda\le\Lambda\) everywhere, or \(\lambda\ge\Lambda\) everywhere | Existence of either comparable producer is equivalent to RH. No coefficientwise nonnegativity premise is needed in these current capstones. [Minorant criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeOrderComparableRigidity.lean:68), [majorant criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeOrderComparableRigidity.lean:75). |

For general denominator \(k>0\), the corpus proves an exact correspondence between full positivity plus \(k\mu_\lambda((a,b])\in\mathbb N\) and an entire finite-order degree-\(k\) completed Dirichlet datum, with functional equation, **all zeros on the critical line**, and the prescribed logarithmic derivative. The critical-line condition is part of the right-hand side, not a consequence of the functional equation alone. The correspondence does not prove \(\Lambda\)-rigidity for all \(k\ge3\). [Rational-counting correspondence](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilZetaPowerForward.lean:155).

## Proven no-gos and what survives them

Each exclusion below retains its hypotheses. None rules out every conceivable producer. In the repair formulas, \(*\) denotes Dirichlet convolution and \(\mu\) is the Möbius function.

| Excluded mechanism | Exact formal obstruction and surviving boundary |
|---|---|
| Finite truncations or critically summable weights | If \(\sum|\lambda(n)|/\sqrt n<\infty\), an admissible polar test has strictly negative energy. This excludes zero weights and every finite truncation. An infinite, nonsummable arithmetic contribution is necessary. [Negative witness](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivitySummableWeightsObstruction.lean:1089). |
| Replacing the entire weight system by sparse support | Support counting \(O(N^\theta)\), \(0\le\theta<1/2\), is incompatible even with polar positivity. This is an exclusion of sparse **weights**, distinct from sparse perturbation rigidity below. [Sparse-support theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivitySparseWeightsObstruction.lean:484). |
| Keeping \(\log p\) at primes but deleting proper prime powers | Those exact weights are not polar-positive. This does not exclude every imaginable prime-supported sequence. [Prime-powers theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivityPrimePowersForced.lean:240). |
| A small excess or a small deficit relative to \(\Lambda\) | If either \(\sum(\lambda-\Lambda)_+n^{-s}\) or \(\sum(\Lambda-\lambda)_+n^{-s}\) converges at one real \(s<1\), full positivity forces equality. Therefore every distinct producer has **both** series divergent for **every** \(s<1\). [Rigidity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeOneSidedDeviationRH.lean:430), [necessary divergence](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeOneSidedDeviationRH.lean:386). |
| Log-summable or sufficiently sparse deviations | For some natural \(J\), \(\sum |\lambda(n)-\Lambda(n)|/[\sqrt n(1+\log n)^J]<\infty\) forces equality. The companion support theorem covers sets with summable inverse powers of \(1+\log n\), including geometric progressions and finitely generated multiplicative supports. A different producer must escape these convergence classes. [Log-summable rigidity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLogSummableRigidity.lean:1090), [support version](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLogSummableRigidity.lean:1114). |
| Finite-type Dirichlet repairs | For \(\lambda=\Lambda*a+\mu*f+v\), finitely supported \(a,f\), \(f(1)=0\), and regular \(v\), positivity forces \(a=\delta_1,f=v=0\). Here regularity includes absolute convergence for \(\sigma>1\), continuation across \(1/2\), polynomial strip growth, and normalization at 0 and 1. Existence within this class is exactly RH. [Finite-type theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFiniteTypeUniqueness.lean:435). |
| Infinite boundary-summable dilation and Möbius repairs | The same conclusion \(\lambda=\Lambda\) holds when \(\sum (|a|+|f|)(1+\log n)/\sqrt n<\infty\), \(\sum|v|/\sqrt n<\infty\), \(f(1)=0\), and \(v(0)=v(1)=0\). No continuation across the critical line is needed. Nonsummable boundary behavior remains outside this theorem. [Boundary theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeBoundaryMobiusRigidity.lean:446). |
| A zeta-pole background with a regular correction | \(\beta\mathbf1_{n\ge2}+v\) is never full-positive for boundary-regular \(v\). In the larger pencil \(\beta\Lambda+\gamma\mathbf1_{n\ge2}+v\), full positivity forces \(\beta=1,\gamma=0,v=0\). The positive survivor is an exact classification of the pencil. [Pole obstruction](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeZetaPoleProducerObstruction.lean:191), [pencil classification](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeVonMangoldtZetaPencil.lean:363). |
| Broad squarefree lower floors | Positivity excludes \(\lambda(n)\ge c n^{-\delta}\) on all squarefree \(n\ge2\), for \(c>0,\delta<1/2\). A further resonance theorem gives arbitrarily large squarefree \(n\) with \(\lambda(n)<c\), for every \(c>0\). These are resonance constraints, not complete classification. [Floor exclusion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivityPrimorialResonance.lean:580), [resonance budget](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeResonanceBudget.lean:297), [arbitrarily late small values](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeResonanceBudget.lean:508). |
| Independent random-prime replacements | For measurable \(X_n\in[0,1]\), pairwise independent on squarefree integers with \(\mathbb EX_n\ge c/\log n\), weights agreeing with \(X_n\log n\) on squarefree integers fail full positivity almost surely. Other coefficients may be arbitrary. General correlated constructions are not excluded. [Random-weight theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivityCramerRandomPrimes.lean:496). |
| Very rapidly decaying prime-blind Fourier witnesses | If all integer Dirichlet moments vanish and \(\int|w(t)|e^{\pi|t|/2-K\sqrt{|t|}}dt<\infty\), the Fourier transform vanishes. For prime-only moments, the checked theorem uses \(e^{\pi|t|/2}(1+|t|)^{-a}\). Thus nontrivial witnesses must lie outside these precise admission classes. This does not make PBAP tests vacuous: compactly supported \(C^2\) tests need not meet these exponential decay bounds. [Integer threshold](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindCarlsonThreshold.lean:1346), [prime threshold](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindCarlsonThreshold.lean:816). |

The corpus also excludes a class of one-sided null-potential repairs: for normalized logarithmically bounded coefficients with positive-definite null potential, a uniform bound on the logarithmic-block mass of **either** sign forces the coefficients to vanish. The unbounded, mixed-sign case is not eliminated by that result. [Negative-part theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilNullPotentialSignPartRigidity.lean:398), [positive-part theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilNullPotentialSignPartRigidity.lean:430).

## What the archimedean and finite computations establish

There is an explicit **real-supported signed** producer,

\[
\mathbf1_{(1,\infty)}dx-e^{1/20000}\delta_{e^{1/10000}},
\]

with coercive Weil form. This proves that the fixed archimedean datum and pole weight alone do not force the integer arithmetic. It does not give an integer-supported producer, or a coefficientwise nonnegative real-supported one. [Formal real-support construction](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/LebesgueAtomWeilPositivity.lean:545).

On actual zeta tests, Lean proves a constrained ground-energy lower bound \(1/10\) at logarithmic aperture \((\log2)/2\), and \(1/20\) up to aperture \((\log2+1/50)/2\), including the first prime. These are genuine analytic positivity results on their stated domains. They do not cover all apertures. [First bound](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PoleVanishingWeilPositivityHalfLogTwo.lean:782), [prime-two extension](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PoleVanishingWeilPositivityPrimeTwo.lean:984).

For PBAP geometry, the corpus proves that a measurable dilation-free set has measure at most \(\log2\), and a quantitative Poisson bound for functions vanishing on a logarithmic lattice. Neither statement is itself the required all-test archimedean sign inequality. [Dilation-free measure bound](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/DilationFreeSetMeasure.lean:103), [log-lattice bound](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/LogLatticePoissonAnticoncentration.lean:837).

The older two-walls card labels its nonnegative-test positivity, multi-tiling characterization, and numerical Poincaré threshold as paper results. They are not promoted to Lean theorems here. Likewise, the coefficient-pinning card reports interval-arithmetic certificates and explicitly says its Lean formalization has not started. Finite numerical pinning does not supply exact all-scale equality. [Two-walls card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/producer-existence-two-walls.md), [pinning card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/certified-producer-pinning.md).

One subtlety matters: the summable-weights obstruction uses a prime-blind test with negative **archimedean-only** energy. That preliminary test is not asserted to satisfy the polar vanishing conditions of PBAP; full PBAP retains the pole energy. It is not a Lean counterexample to PBAP.

## The actual open frontier

1. **Unconditional existence.** Prove full PBAP, or construct a real integer-indexed \(\lambda\) positive on every full-cone test. The polar existence problem is separately formalized. Finite-level existence and compactness are already available; their premise remains unproved.

2. **General detection.** Prove that any full-positive integer system excludes off-line zeta zeros, without adding summability, order, quantization, or phase hypotheses. The residue theorem identifies what a hypothetical alternative must do. None of the checked capstones prohibits every such deviation.

3. **The remaining mixed singular class.** Extend rigidity beyond finite-type and boundary-summable repairs. Any distinct producer must evade all the audited classes: both sign parts diverge at every exponent below 1, the weighted log-summability fails, and spectral deficit has positive lower density. These are necessary conditions, not evidence that such a producer exists. “Dense oscillating deviation” is useful intuition, but the proved statements are the precise divergence and deficit conditions.

4. **Produce one sufficient detection property.** Derive half-integer spectral counts, an admitted settled phase, zero lower deficit density, a bounded zeta quotient, or equality in the exposing functional from independent arithmetic input. Each would connect to an existing theorem. Positivity alone has not been shown to supply these properties.

5. **A stronger dual positivity law.** Prove the explicit exposing-ray archimedean inequality at every cutoff and level, or the full one-sided test-cone criterion. Either reaches RH directly and avoids treating mere nonemptiness as sufficient. The requisite inequalities remain open. [One-sided nonpositive criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeOneSidedCriterion.lean:410), [nonnegative criterion](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeOneSidedCriterion.lean:419).

6. **Rational spectral rigidity beyond denominator two.** The degree-\(k\) correspondence is formal, but it does not classify every \(k\ge3\) datum as zeta's power. An independent rational-mass producer and a rigidity theorem for that class are distinct unresolved steps.

Existence and detection are both open. A producer inside one of the already rigid classes would close both at once; an unrestricted PBAP proof would close existence but would still require detection.

## Verification and scope

The audit used the repository's `scripts/formal_tools.py research` in hybrid, deep, and exact lexical modes; inspected both `candidate_lemmas` and `source_arguments`; excluded scratch-module duplicates when selecting evidence; and read the current source statements and relevant definitions. Exact `PrimeBlindPositive` search returned seven declarations in two production modules: definitions, equivalences, and forward implications, with no unconditional PBAP theorem. An exhaustive PBAP/prime-blind text search in production RHTower sources supplemented indexed retrieval.

Hybrid existence, rigidity, spectral, no-go, and archimedean searches completed without reported partial results. The deep open-frontier search returned useful partial results but hit its 90-second reranking deadline. Search inventory coverage reported 68,231 indexed files; compiler metadata was largely pending/source-only, so search hits alone were not treated as kernel checks. An “open” verdict here means no closing theorem located by this audit, consistent with the current frontier ledger; it is not a mechanically proved absence from all possible formulations.

Two `/tmp` Lean scratch files successfully checked **54 declarations from 36 production modules** with `#check` and `#print axioms`. Every checked declaration reports only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or extra analytic axiom occurred. All selected compiled objects were present and no older than their source files when inventoried. This checks the installed compiled exports and their explicit hypotheses; it is not a fresh rebuild of every dependency. The [evidence manifest](/Users/michael/Documents/code/hgt/docs/reports/weil-cone-pbap-lean-audit-2026-10-07-evidence.json) records exact compiled types, source locations and hashes, axioms, search coverage, and lint errors.

The repository-wide `scripts/formal_tools.py lint` returned exit 1 because six unrelated owned modules were unreachable from their theorem-area umbrellas: `XiMarkedIslandSeparation`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`. It also emitted file-size warnings. No proof-debt error appeared in that run. The report therefore makes no claim that the entire working tree passes its formal gate.

No Lean source was modified for this audit.
