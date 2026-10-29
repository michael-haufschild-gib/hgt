# Research briefing — the breakthrough question below RH

Source: docs/reports/review-2910/fable.md. Evidence labels as in the frontier map: [L] integrated Lean, [S] working source. Lean names are entry points; check each statement with `scripts/formal_tools.py research "<name>" --mode lexical` before relying on it. This briefing replaces an earlier version whose question (a power saving in short-window Möbius mean squares) is equivalent to a fixed zero-free strip and is recorded at the end as the larger question.

---

## Answer this question

**Where does Weil positivity leave the unconditional world? Cross the Metzler threshold: prove that the complete Weil form of ζ is eventually nonnegative on the atomic families of one fixed overlap ratio \(c>1\), and locate the overlap ratio at which the zeros of ζ first enter.**

The objects. Fix a \(C^2\) profile \(\varphi\) supported in \([0,1]\) with \(\int\varphi^2>0\) (for instance the plateau `plateau η`). At level \(N\) and width \(w=c/N\), the **atomic family** is
\[
f_x(u)=\sum_{n\le N}x_n\,\varphi\!\Bigl(\frac{u-\log n}{w}\Bigr),\qquad x\in\mathbb R^N
\]
(`atomicTest N x (atomDilate φ (c/N))`, `ArithmeticElectrostatics/TheStabilityLawAtAtomicResolution.lean`). The **overlap ratio** is \(c=w/\delta_N\), \(\delta_N=\log(1+1/N)\) the atom spacing (`atomSpacing`). The **complete Weil form** is \(W(f_x)=\Gamma(f_x)+\text{poles}-\text{primes}\) with Gamma, both poles and every prime power retained (`weilQuad`); its Gram matrix on the atoms at width \(c/N\) is `completeWeilMatrix φ c N` (`RenormalizedArithmeticPotentialTheory/TheCompleteWeilMatrixHasAnExactErrorDecomposition.lean`).

The statement to prove, in one line:
\[
\exists\,c>1,\ \exists\,\varphi:\qquad \forall^{\infty}N,\quad (\texttt{completeWeilMatrix }\varphi\ c\ N).\texttt{PosDef}
\quad\bigl(\text{equivalently }\ \forall x,\ \texttt{weilQuad}(f_x)\ge0\bigr).
\]

Answering it fully means answering four parts:

- **(Q0) The touching ratio.** Decide \(c=1\): eventual positivity at width exactly \(\delta_N\) (Wall 14.34, "\(\rho=1\) open").
- **(Q1) Zero-side content of a fixed ratio.** Determine what eventual positivity at fixed \(c\) implies about the zeros and what implies it. Expected: finite off-line support implies it for every \(c\) (one zero weighs at most a bounded fraction of the diagonal energy at bounded overlap, `norm_Wsummand_atomicTest_dilate_le`); it does not imply finite support or any fixed strip. Prove both directions or exhibit the obstruction.
- **(Q2) The critical growth.** Determine the least growth \(c_N\to\infty\) at which eventual positivity on the families of ratio \(c_N\) is equivalent to RH, or prove that every unbounded growth is. Known: ratio \(\gg(\log N)^{1/4+\varepsilon}\) is RH-complete (`riemannHypothesis_iff_atomicFamilies_nonneg_log_quarter`, condition `OverlapGrowthTwo`), ratio \((\log\log N)^{1+\varepsilon}\) is RH-complete for Denjoy–Carleman profiles (`atomicReceivers_quasiAnalytic_boundary`), fixed width (ratio \(wN\)) is RH-complete (`riemannHypothesis_iff_splineAtomic_negIndex_eq_zero_of_width`).
- **(Q3) Selectivity of a fixed ratio.** Determine the least overlap ratio at which the Liouville twin's complete matrix fails to be eventually positive, and whether that happens at a fixed \(c\) or only under growth. Known: the twin fails under every overlap growth (`liouville_atomicFamilies_negative`); at the spacing scale every twist is positive (`TheSpacingScaleLawIsUniversal`); some twist fails at a finite ratio (`universalThreshold_finite`, with its value \(K_{\rm univ}\) open).

The core deliverable is the theorem in the displayed line, for one explicit \(c>1\), by a mechanism that does not rely on a diagonal gauge of the atomic basis (none exists for \(c>1\), see Context).

---

## Context

**The overlap ratio is the one real parameter on which the whole positivity programme lives.** The corpus brackets it exactly (`SpacingScaleHarmonicAnalysis/UnboundedOverlapIsTheRiemannHypothesis.lean`): at ratio \(\le c_0\) (`spacingWidthRatio`) positivity is unconditional for ζ and for every twist \(|\omega|\le1\) [L]; on the families of one fixed bump, where the ratio \(wN\) is unbounded, positivity is the Riemann hypothesis, and the largest negative index of these Gram matrices is the number of distinct zeros right of the line [L]. In the module's words: "only bounded overlap is left between them."

**What is proved on the bounded part.**

- Ratio \(\le c_0\): the stability law, \(\operatorname{Re}W+2S^2\ge0\) for every twist (`re_W_add_sinh_sq_nonneg_spacing`), and full positivity \(W\ge0\) at a fixed fraction of the spacing (`weilQuad_atomicTest_nonneg`, `fixedWidthRatio`) [L]. Mechanism: the archimedean self-energy \(\log(1/w)\) per unit mass pays the prime Schur rows \(\le\log N+O(1)\) with a tilt \(r(n)=1+n/N\) across scales; the pole is paid by the pole defect (`ThePoleDefectPaysThePole`) up to about a quarter of the Robin–Euler threshold \(K_{RE}\approx0.43\) for plateau profiles (`TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold`, \(\approx0.108\)) [L].
- Ratio \(c<1\) (strictly separated): the complete Weil matrix splits exactly at the spacing; its bounded spectrum is the adjunction spectrum \(E_m=\gamma+\log m+\mathrm{tameDifferent}(m)\) on Ramanujan profiles, with simple eigenlines converging per conductor (`TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum`, `TheSimpleCompleteWeilEigenlinesConvergeToRamanujanLines`) [S]; for a smooth plateau the pole charge compensates the conductor-one loss and every eigenvalue lies above a fixed positive floor, so the matrix is eventually positive definite at each fixed \(c<1\) (`CriticalArithmeticCorrelationTheory/SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive.lean`, `exists_plateau_eventually_completeWeilMatrix_posDef`) [S]. The module states explicitly: "No horizon uniformity in that ratio is asserted"; the frontier records that coercivity degenerates as \(c\uparrow1\).

**Why \(c=1\) is a wall of a different kind.** Below the spacing the atomic intersection form is Metzler (nonnegative off-diagonal) and Weil positivity is a trickle-down inequality (`TheAtomicFormIsMetzlerBelowTheSpacing`, `TheHodgeIndexTricklesDown`) [L]. The threshold is sharp: for every profile positive on \((0,1)\) and every \(c>1\), the atoms \(N-1\) and \(N\) (overlapping, positive pairing) together with the atom \(1\) (separated, negative pairings) form an odd triangle, and no unimodular gauge makes the form Metzler (`TheMetzlerThresholdOfTheOverlapRatioIsOne.lean`, `metzlerThreshold_overlapRatio`) [L]. A proof at any \(c>1\) must leave diagonal gauges of the atomic basis: positivity has to come from cancellation, not domination. This is the first place in the programme where the mechanism is forced to change.

**Why a fixed ratio is not RH.** At overlap ratio \(c\) a single zero, on-line or off-line, carries at most \(m_\rho\,e^{2|\sigma|/k}(\|\varphi\|_1^2/\|\varphi\|_2^2)\,((N+1)/k)/(2\sqrt{\beta(1-\beta)})\) times the diagonal energy, \(k=N/c\), so about \(c\) times a constant (`TheWeightOfOneZero.lean`): "each zero samples the Dirichlet polynomial at the Nyquist rate with weight at most the overlap ratio." Finitely many off-line zeros cannot make the form negative for large \(N\) at bounded \(c\); RH-completeness requires the ratio to grow. This is why (Q1) is expected to place fixed-\(c\) positivity strictly below finite off-line support.

**Where the arithmetic enters.** Beyond the spacing the prime sum reads every lag \(\log k\) that falls within the width of a log-ratio \(\log(n/m)\) (`TheGaugeEntersThroughNonRatioLags.lean`): a term is a ratio lag when \(n=km\) and a non-ratio lag otherwise. The gauge defect of a twist lives only on non-ratio lags; below the spacing there are none; for every \(N\ge3\) there are atoms \(m<n\le N\), \(n\ne2m\), whose log-ratio is within \(4\delta_N\) of \(\log2\) (`exists_nonRatio_pair`). At fixed ratio \(c\) the non-ratio lags are the pairs \(n=km+h\) with \(0<|h|\lesssim c\) and \(km\gtrsim N/c\): a boundary layer of the top atoms. By the diamagnetic inequality the Markov part is universal over twists and ζ is its ground state (`diamagnetic_inequality`); a margin in ζ's favour can only come from the pole or from these non-ratio lags.

**What the zero side says about the family.** The atomic family of ratio \(c\) is a Dirichlet polynomial of length \(N\) at bandwidth about \(N/c\) (`TheAtomicFamilyIsADirichletPolynomial`); the spacing scale is the Nyquist scale (zero density \(\log T/2\pi\) at \(T\asymp N\)). Fixed \(c>1\) is bandwidth \(\lambda=1+\log c/\log T\to1^+\): the family lives exactly at the square-root threshold, a bounded factor beyond it. Positivity of the form is a statement about the joint geometry of on-line and off-line zero evaluations of length-\(N\) Dirichlet polynomials at that bandwidth; (Q1) asks for its exact content.

**Why this question opens something.**

1. It replaces the three walls by one real parameter with known endpoints. Every result on the ladder is a theorem about the same matrix: unconditional below \(c_0\), separated regime \(c<1\) [S], RH at unbounded ratio. The remaining distance is bounded overlap, and (Q2) decides whether it is one step (if any growth suffices, the entire problem is uniformity in \(c\)) or a genuine ladder of intermediate statements with increasing zero content.
2. The theorem at the first \(c>1\) is the first positivity of the complete form past the Metzler threshold, hence the first proved cancellation mechanism for the frustrated form. That mechanism, not the constant \(c\), is the object of value: it is what has to iterate.
3. (Q1) and (Q3) give the first map of where zero information and where selectivity enter the positivity currency: at which ratio a twin first fails, at which ratio the zeros are first seen collectively. The corpus has these only as endpoints (every twist positive at \(c_0\); Liouville fails under growth; unbounded ratio is RH).
4. It is calibrated and falsifiable: under RH the statement is true for every \(c\); over \(\mathbb F_q[t]\) the analogous forms are coercive (the curve comb is uniformly coercive, `ArithmeticCompensationTheory`); a proof that fixed-\(c\) positivity is RH- or FS-equivalent would itself be a new no-go (a discontinuity of the ladder at \(c=1\)).

**Tools in the corpus.** Exact splitting of the complete matrix at the spacing and its error decomposition (`TheFullWeilMatrixSplitsAtTheSpacing`, `TheCompleteWeilMatrixHasAnExactErrorDecomposition`); Ramanujan quasimodes and the two-pole replacement with uniform errors (`TheWeilReplacementErrorsVanishOnRamanujanModes`, `TheTwoPoleReplacementHasUniformErrors`); the sharp prime gap \(2\log2\) and the pole-hyperplane selectivity (`TheSpectralGapOfThePrimeFormIsTwoLogTwo`, `ThePoleHyperplaneSeparatesTheFullWeilForms`); the exact Robin constant and two-atom archimedean pairing (`TheRobinConstantOfAnAtom`, `TheArchimedeanPairingOfTwoAtoms`); the cross-kernel law and tilted rows (`TheStabilityLawAtTheSpacingScale`); the plateau shape and charge limits (`ThePlateauShapeAndChargeHaveTheirIndicatorLimits`); the rank-two reduction \(W\ge0\iff\) Markov sign on the pole complement plus one affine scalar (`TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar`); the index theory for reading the result on the zero side (`HeckeKreinToeplitz`: `negIndex_zetaKernel_eq_iSup_receivers`, `hermNegIndex_weilGram_le_negIndex_zetaKernel`).

---

## Not an answer is

- Positivity at bounded aperture (window tests of a fixed radius, any radius): width-blind by theorem (`resolutionLimit_width_aperturePositivity`). The families here have aperture \(\log N\to\infty\).
- Re-proving the separated regime \(c<1\), or any ratio \(\le1\) obtained by letting the horizon depend on \(c\); the question is one fixed \(c>1\) with one horizon \(N_0(c)\).
- Positivity of a part of the form: the Markov form alone, the prime matrix alone, the pole-hyperplane restriction alone, or a corrected matrix (a positive correction changes the form). The complete form with Gamma, both poles and all prime powers is the object.
- Positivity for a twist or a model in place of ζ (Liouville, \(c\Lambda\), finite flips, Beurling systems, curve data), or positivity on nonnegative coefficient vectors only.
- Any conditional statement (assuming RH, finite off-line support, a zero-free strip, Lindelöf, pair correlation).
- A dictionary: a new equivalence between fixed-\(c\) positivity and another RH-equivalent statement does not answer (Q1); (Q1) asks for the stratum, with proofs.
- Re-deriving the known growth thresholds \((\log N)^{1/4+\varepsilon}\) or \((\log\log N)^{1+\varepsilon}\) for (Q2); (Q2) asks whether slower growth, or any growth, is RH-complete.
- A Lean statement carrying the conclusion as a hypothesis, structure field, typeclass instance or axiom; any `sorry`, `admit`, `native_decide`, raised heartbeat limits.

---

## Question is answered if

**Core (positive).** An unconditional, Lean-formalized theorem
\[
\exists\,c>1,\ \varphi:\quad\forall^\infty N,\ (\texttt{completeWeilMatrix }\varphi\ c\ N).\texttt{PosDef}
\]
(or `weilQuad (atomicTest N x (atomDilate φ (c/N))) ≥ 0` for all \(x\)), with \(c\) and \(\varphi\) explicit, under the project rules (no `sorry`/`admit`/`native_decide`/axioms, no heartbeat increases, `#print axioms` standard), with a pipeline card in `docs/drafts/pipeline/` written first and moved to `3-formalized` after. The proof must state the mechanism that replaces the diagonal gauge (how the frustrated triangle is paid), and report the behaviour of the same argument on the Liouville twin at the same \(c\) (holds, fails, or undecided).

**Map (required with the core).** (Q1) proved in at least the direction "finite off-line support \(\Rightarrow\) eventual positivity at every fixed \(c\)", with the strongest proved converse or a precise obstruction; (Q3) the status of the Liouville twin at the proved \(c\). (Q0) and (Q2) are reported as answered or as open with the exact obstacle (for (Q2): the alias error of the best synthesis at the given growth, in the terms of `TheCriticalExponent` and `TheSecondOrderSynthesis`).

**Negative answer.** A Lean-formalized theorem that eventual positivity at some fixed \(c>1\) (or at \(c=1\)) is equivalent to finite off-line support or to RH. This closes the question as a new no-go (the ladder is discontinuous at \(c=1\)) and must come with its positive survivor: which weaker family at the same ratio remains unconditionally positive.

**Reporting.** Progress in units of the overlap ratio \(c\) (and the horizon \(N_0(c)\)), or of the growth exponent in (Q2). Intermediate results that are neither (new equivalences, finite-aperture certificates, twin positivity) are recorded on the card as context and are not progress on this question.
