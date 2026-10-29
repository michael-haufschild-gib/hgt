# Research briefing — the breakthrough question below RH

Source: docs/reports/review-2910/fable.md. Evidence labels as in the frontier map: [L] integrated Lean, [S] working source, [E] external claim. Lean names are entry points; check each statement with `scripts/formal_tools.py research "<name>" --mode lexical` before relying on it.

---

## Answer this question

**Prove, unconditionally, a power saving in the mean square of the Möbius function over short windows of one power length.** Precisely, prove

\[
\exists\,\alpha\in(0,1),\ \delta>0,\ C:\qquad
\forall Q\ge1,\quad
E_\alpha(Q):=\sum_{Q\le t<2Q}\Bigl(\sum_{t<n\le t+\lceil Q^\alpha\rceil}\mu(n)\Bigr)^2\ \le\ C\,Q^{1+2\alpha-\delta}.
\]

This is the proposition `MoebiusPowerWindowSaving` (`BezoutValuationIncidence/ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis.lean`, with `moebiusWindowEnergy` and `powerWindow α Q = ⌈Q^α⌉`). The trivial bound is \(Q^{1+2\alpha}\); the question asks for a saving of a fixed power of \(Q\) at a single window length.

The following are proved equivalent to it in the corpus [L], and proving any one answers the question:

- **Prime form.** `PrimePowerWindowSaving`: \(\sum_{Q\le t<2Q}\bigl(\sum_{t<n\le t+\lceil Q^\alpha\rceil}\Lambda(n)-\lceil Q^\alpha\rceil\bigr)^2\le CQ^{1+2\alpha-\delta}\) (`primePowerWindowSaving_iff`).
- **Balanced statistic.** `BalancedStatisticPowerSaving`: \(|\Lambda_d(\mu\mathbf 1_{(Q,2Q]})|\le C\,(d^2/Q)\,Q^{-\eta}\) for \(Q^{1-\varepsilon}\le d\le Q^{1+\varepsilon}\), where \(\Lambda_d\) is `kernelStatisticAll (2Q) (moebiusWindowRow Q) d` (`balancedStatisticPowerSaving_iff`; explicit strip \(\Theta\le1-\min(\eta,13\min(\varepsilon,\tfrac12)/800)\) in `zetaZeroAbscissa_lt_one_of_balancedStatisticPowerSaving`).
- **Escaped Möbius law.** `GrowingEndpointEscapedMoebiusLaw θ` for some \(\theta>0\): \(|\sum_{(N-b)/a<j\le N}\mu(j)/j|\le C((N-b)/a)^{-\theta+\varepsilon}\) uniformly in \(a,b\) (`SelectivePositivityAndThresholdLaws/MoebiusEscapedPairingBoundaryLaw.lean`, `growingEndpointEscapedMoebiusLaw_tfae`).
- **Mertens.** \(M(x)=\sum_{n\le x}\mu(n)\ll x^{1-\delta}\), through the absolute-moment law \(\sum_{k\le X}|M(k)|^p=O(X^c)\iff p\Theta+1<c\) (`exists_sum_norm_mertens_rpow_le_iff`).
- **Zero side.** \(\Theta:=\sup\operatorname{Re}\rho<1\), a fixed zero-free strip for \(\zeta\) (`zetaZeroAbscissa`).

So the question is: **produce the first fixed zero-free strip for \(\zeta\), by producing the arithmetic estimate directly.** The zero-side form may not be used as an input; it is the output.

**Proof-of-concept variant (partial answer).** Prove, unconditionally, any power-saving estimate in a parity-sensitive statistic of \(\mu\), \(\lambda\) or \(\Lambda\) at a single scale that is *not* equivalent to a statement about zeros, for example
\[
\sum_{n\le x}\lambda(n)\lambda(n+1)\ll x^{1-\delta}
\qquad\text{or}\qquad
\sum_{n\le x}\mu(n)\mu(n+1)\ll x^{1-\delta}.
\]
This does not give a strip. It counts as a partial answer because it would be the first parity-breaking power saving over \(\mathbb Z\) in any problem, and the mechanism is what the main question needs.

---

## Context

**Why this question.** Every live RH route in the corpus is an RH-equivalent receiver waiting for one arithmetic input, and three theorems fix what that input must be: it must be *parity-breaking* (fail for the Liouville twin \(\lambda\Lambda\), which shares every multiplicative identity, every sign-blind datum and every gauge-invariant correlation: `SelectiveMultiscaleArithmeticPositivity/TheDyadicSignIsRigid.lean`, `ArithmeticCorrelationGeometry/MultiplicativeDataDetermineASourceUpToGauge.lean`); it must be *square-root precise* (fail for \(\Lambda+\varepsilon n^{-\eta}\), \(\eta<\tfrac12\), so nothing with relative error \(o(1)\) qualifies: `TheDyadicSignIsRigid`); and it must act at unbounded aperture. The weakest statement in the RH ladder with the first two properties is a fixed zero-free strip. The ladder is \([\text{open}]<[\ge\text{QRH}]<[\text{LH}]<[\text{FS}]<[\text{RH}]\); a strip is the first rung, is implied by RH, and is implied by neither the Lindelöf hypothesis nor finite off-line support. Every rung above it is the same mechanism at a larger precision level, so the mechanism is born at this rung or nowhere.

**Why the mean-square short-window form.** Any saving in \(E_\alpha(Q)\) is parity-breaking by construction: a sign-blind argument (one that also bounds the windows of \(|\mu|=\mu^2\)) gives \(Q^{1+2\alpha}\) and nothing better. The window length \(Q^\alpha\) with \(0<\alpha<1\) is the balanced regime: BVI proves that below the diagonal (\(Q\ge P^{5/3}\)) the Type-II saving is unconditional, and at the diagonal a power saving is exactly \(\Theta<1\) (`TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean`, `ArithmeticCompensationTheory` centred prime row up to \(Q\le P^{30/17-\delta}\)).

**What is known, unconditionally.**

- The \(o(1)\) version is a theorem. Matomäki–Radziwiłł: \(\sum_{X\le x\le2X}|\sum_{x<n\le x+h}\mu(n)|^2=o(Xh^2)\) for every \(h\to\infty\) (literature). In the corpus, the fibre-averaged mean square of \(\mu\) over windows of length \(\exp((\log x)^\beta)\), \(9/10<\beta<1\), is \(o\) of the trivial size (`RHTower/Sieve/MoebiusMeanSquare.lean`, `averagedMeanSquare_moebius_cardLength`; `ScaledFibreStepOne.lean`; reduction `MRFibreReduction.lean`). The gap between what is known and what is asked is exactly "\(o(1)\) to \(Q^{-\delta}\)".
- The classical growth inputs are formalized and are proved insufficient: Vinogradov–Korobov (`Sieve/VinogradovKorobovZeroFree.lean`, explicit constant), Guth–Maynard large values with \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) and primes in \((x,x+x^{17/30+\varepsilon}]\) (`Sieve/GuthMaynardTheoremOneOne.lean`, `GuthMaynardCorollariesUnconditional.lean`). No density estimate forces a strip: every envelope is \(\ge1\) throughout the strip (`RHTower/DensityEnvelopeNoGo.lean`). Short-interval prime theorems have relative error \(o(1)\) and cannot decide the sign.
- Multiplicative positivity plus growth (the only mechanism that has ever produced a zero-free region) is capped: exclusion iff \(\sqrt A+\sqrt{G\eta}<\sqrt B\), width \((\sqrt B-\sqrt A)^2/G\), \(G\asymp\log t\) from Hadamard; the Fejér barrier \(a_1<2a_0\) caps every finite multi-frequency certificate (`MultiplicativePositivityGeometry`, `exclusion_iff`, `multiFrequency_purchase_le_two`). A fixed strip from this mechanism needs a growth input bounded on a line inside the strip, which does not exist.
- Multiplicative data alone are gauge-blind: they determine a source only up to the gauge torus \((\mathbb R/\mathbb Z)^{\text{primes}}\), square-root cancellation holds at Haar-almost every gauge point and fails at the Liouville point; the exceptional set is null and comeager (`ArithmeticCorrelationGeometry`, `moebius_gauge_trichotomy`, `moebius_exceptional_residual_and_null`). Any estimate for the whole orbit is about the orbit.
- Mertens' function is \(\Omega_\pm(\sqrt x)\) (`RHTower/MertensSquareRootOmega.lean`): the target is a power saving \(1-\delta\), not \(\tfrac12+\varepsilon\).

**Structures not shared by the twins** (the only places an answer can come from):

- The successor \(n\mapsto n+1\) and Bézout relations \(pa-qb=1\), \(\gcd(n,n+1)=1\). Beurling systems lack them (`BezoutValuationIncidence`, `TransHorizonIncidenceMechanics` selectivity class III). SSA has the dilation cocycle \(\prod_{j<m}\sigma_f(mn+j)=\sigma_f(n)\), the one-third agreement floor (density scale only), the hypercube phase diagram with its sign split at half damping, and the sieve functional equation of which \(\mu\) is the unique bounded solution (`SignedSuccessorArithmetic`, `eq_moebiusReal_of_sieve_functional_equation`).
- Integrality: \(\psi(N)=\log|\mathbb Z/\operatorname{lcm}(1..N)|\); RH iff \(\log|\mathbb Z/\operatorname{lcm}(1..N)|=\chi(\sqrt N\,A)+O(\sqrt N\log^2N)\) (`ArithmeticEffectivityTheory`, `riemannHypothesis_iff_logTorsion_sub_eulerChar`). Known extraction (Chebyshev, Nair) reaches linear precision only.
- The Euler product and functional equation used as identities (not as inputs to estimates), and Riemann's theta law, which identify \(\zeta\) rigidly (`ArithmeticPositiveDuality`, theta rigidity; `StripBochnerWeilForcing`, pole-order-one class is \(\mathbb R^\times\zeta\)).
- Kloosterman sums with Weil's bound \(|K|\le2\sqrt p\) and multi-modulus dispersion (`RHTower/EstermannKloostermanSaving.lean`, `ArithmeticCompensationTheory/MultiModulusKloostermanDispersionAndPrimeRowTransfer.lean`); the Type-II barrier \(Q\ge P^{5/3}\) is sharp and the Weil bound is order-sharp, so new saving must come from averaging over moduli or the CRT block, not from a single modulus.
- Transcendence machinery: Stepanov's auxiliary polynomial over \(\mathbb F_{p^n}\) (`RHTower/StepanovCount.lean`), hyperelliptic Hasse–Weil by descent (`HyperellipticDescent.lean`), a Baker-type theorem on linear forms in logarithms with Siegel-lemma auxiliary matrices (`RHTower/BakerGeneralProof/*`, capstone `false_of_long_extrapolation`).
- Lee–Yang and Asano contraction (`HTGeometry/LeeYangAsanoContraction.lean`), prime Ising trees (`RHTower/PrimeIsingTree*.lean`).

**Calibration.** Over \(\mathbb F_q[t]\) the analogue of the question is a theorem: short-interval Möbius sums have square-root cancellation by Weil's bound, and the centred divisor prefix is exactly constant (`ArithmeticContinuationAndCriticalEnergy`, function-field calibration). Any proposed mechanism should reproduce the \(\mathbb F_q[t]\) statement by the same argument.

**Known obstructions to specific shortcuts** (`docs/reports/rh-killed-routes.md`): raw positive prime series have abscissa 1 regardless of RH; uniform escaped-Möbius decay over all multipliers fails; no fixed Vaughan power saving exists without a strip; a saving at the single height of a zero forces an off-line companion; the Weil bound at one prime is order-sharp; averaging Kloosterman packets over moduli is a two-sided quasi-isometry (no sub-diagonal saving from the average alone).

---

## Not an answer is

- Any conditional result: assuming RH, GRH, the Lindelöf hypothesis, the density hypothesis, a zero-free strip for \(\zeta\) or for any \(L\)-function, pair correlation, Chowla, or Hardy–Littlewood.
- Any \(o(1)\) saving: \(E_\alpha(Q)=o(Q^{1+2\alpha})\), savings by powers of \(\log Q\), or Matomäki–Radziwiłł-type statements at any window length. These are proved and are not the question.
- Any statement whose proof is sign-blind: a bound that holds with \(\mu\) replaced by \(\mu^2=|\mu|\), or with \(\Lambda\) replaced by its Liouville twin \(\lambda\Lambda\), or by a majorant; any argument that only uses \(|{\rm coefficients}|\), complete-period quadratic data, or sieve upper bounds.
- Any statement about a model instead of the actual \(\mu\) or \(\Lambda\): Beurling systems, random or probabilistic models, gauge-averaged or almost-every-gauge statements, smoothed or sieve-weighted substitutes, planted or deformed Euler products, function-field results presented as transfer.
- Any statement about a family that does not include \(\zeta\): Dirichlet characters averaged over \(q\) or over non-principal \(\chi\), twists averaged over a torus. A family statement counts only if it includes the principal character and yields the \(\zeta\) statement.
- Reuse of the external quasi-RH manuscript [E] or any unverified external claim as an input.
- Window lengths that make the statement vacuous or false: the window must be a fixed power \(Q^\alpha\), \(0<\alpha<1\) (for \(H\le Q^{\delta}\) the random size \(E\approx QH\) already exceeds the claimed bound).
- A new RH-equivalent or \(\Theta\)-equivalent reformulation, a new dictionary between currencies, a new no-go of an already-classified class, a bound with a constant depending on \(Q\), numerical evidence, or a heuristic.
- A Lean statement that carries the conclusion as a hypothesis, structure field, typeclass instance or axiom; any `sorry`, `admit`, `native_decide`, or raised heartbeat limit.

---

## Question is answered if

**Positive answer (full).** An unconditional proof of `MoebiusPowerWindowSaving`, `PrimePowerWindowSaving`, `BalancedStatisticPowerSaving`, `GrowingEndpointEscapedMoebiusLaw θ` for some \(\theta>0\), or \(M(x)\ll x^{1-\delta}\), with explicit values of \(\alpha,\delta\) (or \(\varepsilon,\eta\), or \(\theta\)), such that:

1. the proof is formalized in Lean under the project rules (no `sorry`/`admit`/`native_decide`/axioms, no heartbeat increases, `#print axioms` shows only standard axioms), with a pipeline card in `docs/drafts/pipeline/` written before the proof and moved to `3-formalized` after;
2. the resulting strip is stated through the existing dictionary (`zetaZeroAbscissa_lt_one_of_moebiusPowerWindowSaving` or its analogues) as an explicit \(\Theta\le1-\kappa\);
3. the proof names the parity-breaking input it uses (which structure not shared by the Liouville twin, by \(\Lambda+\varepsilon n^{-\eta}\), by Beurling systems, or by the gauge orbit carries the saving), and records that the argument fails for those twins;
4. the argument, run over \(\mathbb F_q[t]\), reproduces the known square-root cancellation there.

**Positive answer (partial, proof of concept).** An unconditional Lean-formalized proof of a power saving in a parity-sensitive single-scale statistic not equivalent to a zero statement, such as \(\sum_{n\le x}\lambda(n)\lambda(n+1)\ll x^{1-\delta}\) or \(\sum_{n\le x}\mu(n)\mu(n+1)\ll x^{1-\delta}\), or the Hardy–Littlewood prime-pair asymptotic on average over shifts \(h\le x^\theta\) with a power-saving error term for some \(\theta<1\), with conditions 1, 3 and 4 above. Report explicitly that it does not give a strip, and state what additional step would.

**Negative answer.** A theorem, formalized in Lean, that a precisely defined class of methods cannot produce a power saving in \(E_\alpha(Q)\), where the class is new (not the sign-blind class, not the \(o(1)\)-precision class, not finite-aperture certificates, not positive majorants, all already classified) and contains the methods that prove the known \(o(1)\) results (the bilinear/fibre mechanism behind Matomäki–Radziwiłł, entropy-decrement-type arguments) or the integrality mechanism (Chebyshev–Nair auxiliary integrals). The theorem must identify the exact precision the class reaches, state its positive survivor, and say which structure outside the class remains available. The limit of integrality over \(\mathbb Z\) (whether any auxiliary construction with \(\operatorname{lcm}(1..N)\int P\in\mathbb Z\) can beat linear precision) is an acceptable instance.

**Reporting.** Progress is reported in units \((\alpha,\delta)\), \((\varepsilon,\eta)\) or \(\theta\), or, for the proof-of-concept variant, \(\delta\). Intermediate results that are neither of the above (new equivalences, new models, new no-gos of classified classes) are recorded on the pipeline card as context and are not progress on this question.
