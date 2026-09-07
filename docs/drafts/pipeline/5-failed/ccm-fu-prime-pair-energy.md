# Literal prime-pair energy

- **Stage:** 5-failed for PE1/PE2 and every fixed intermediate-energy ceiling in increasing-prime order.
- **Positive survivor:** first-prime contraction, exact released overlap, and unavoidable late-prime compensation are formalized.
- **Scope:** SD1 and RH remain open; the obstruction applies to the bounded-energy elimination producer in increasing-prime order.
- **Chain:** completed Guinand–Weil source -> marked rectangular current -> affine Suzuki checkpoints -> signed curvature -> coherent prime–polar–Gamma/unit-Riesz boundary -> Xi-screw Green -> RH.
- **Purpose:** use the proved unsigned orientation to obtain actual signed cancellation before the remaining aggregate SD1 bound.

## Frozen source and questions

Let K_d(M) be the literal unsigned channel on the SD1 card, zero for d>=M.
For a finite prime set P, define
`F_P(d)=sum_(a squarefree, all prime factors in P) mu(a)K_(ad)(M)`
on cofactors d coprime to every prime in P. Only products ad<M contribute.
The retained energy is
`Q_P(M)=sum_(d<=M, d coprime to P) mu(d)^2 F_P(d)^2`.

Pairing the p-free and p-divisible terms gives
`F_(P union {p})(d)=F_P(d)-F_P(pd)` for p not in P,
`Q_P-Q_(P union {p})=2 sum_(d<=M, d coprime to P union {p}) mu(d)^2 F_P(d)F_P(pd)`.
The complete signed sum is preserved. Once P contains every prime up to M, only d=1 survives and Q_P is the squared complete signed sum.

For P empty, the new all-cutoff unsigned positivity makes the right side nonnegative for every prime p. This first prime-pair contraction is the unconditional positive statement formalized below.

Two distinct stronger proposals are frozen before screening:

- **PE1:** along primes in increasing order, every successive retained energy is nonincreasing, at every cutoff M.
- **PE2:** along primes in increasing order, every retained energy is at most the original Q_empty(M), at every cutoff M. PE2 permits local increases and still implies SD1 at the terminal stage.

Neither proposal is assumed. Neither the prime order nor the factor-one ceiling will be changed after a failure. A failure does not refute SD1. Before any retirement, preserve the strongest proved contraction and exact residual identity.

## Verification protocol

Screen all M from1 through1024 and every increasing-prime stage with the exact quotient-block formula for K, evaluated in floating point only for guidance. Save every stage and first failures. Independently recompute any decisive small witness directly from the defining half-order sum. No numerical result enters Lean. Prove source inequalities analytically and audit only new declarations. One foreground Lean process; no large or umbrella builds.

## Closed analytic obstruction and positive survivor

Both frozen producers are false. More strongly, no fixed multiple of the original arithmetic diagonal can bound both the actual intermediate smooth-prime head energy and the final signed energy at every cutoff. The first-prime contraction remains valid for every prime and every cutoff.

Define the actual smooth-prime head and late-prime mass by

`H(M)=sum_(d<=M, every prime factor of d<=M/2) mu(d)K_d(M)`,
`T(M)=sum_(M/2<p<=M, p prime)K_p(M)`,
`S(M)=sum_(d<=M)mu(d)K_d(M)`.

The exact source identity is `H(M)-S(M)=T(M)`. Lean proves

`T(4N)>=card{p prime:2N<p<=3N}*sqrt N/40`,
`T(4N)/(4N) -> +infinity`,
`(abs H(4N)+abs S(4N))/(4N) -> +infinity`,
`not exists C, forall M, H(M)^2+S(M)^2<=C*M^2`,
`not exists C, forall M, H(M)^2+S(M)^2<=C*Q_empty(M)`.

All these are unconditional source statements and do not refute SD1. The [actual head asymptotic](../3-formalized/ccm-fu-late-prime-head-asymptotic.md) strengthens the survivor: `S(M)log(M)/(M sqrt(M))->0`, `S(4N)/T(4N)->0`, `H(4N)/T(4N)->1`, and `H(4N)/(4N)->+infinity` are formal. Thus the head itself necessarily carries the superlinear mass, independently of any critical bound on the final aggregate. Leading cancellation is proved; the required linear residual remains open.

## Dependency-closed paper proof

1. Reindex the p-divisible labels by d -> pd. Möbius multiplicativity makes `mu(pd)=-mu(d)` on p-free cofactors, while coefficients with a repeated p vanish. Terms beyond M vanish. This proves exact preservation of S and
   `Q_empty-sum_(p-free d)mu(d)^2(K_d-K_pd)^2 = 2 sum_(p-free d)mu(d)^2 K_d K_pd>=0`.
   Nonnegativity follows from the already closed unsigned orientation at every cutoff. No orthogonal-copy replacement is made.
2. Every n<=M whose prime factors are not all <=M/2 is itself a prime greater than M/2: a proper cofactor would be at least two and make n>M. Thus the smooth-prime head omits exactly the late prime labels. Their Möbius coefficient is -1, giving H-S=T exactly.
3. For 2N<p<=3N and cutoff4N, every time index in the channel has quotient one. Telescope the literal weights:
   `K_p(4N)=D(1)(sqrt(4N)-sqrt p)`.
   The harmonic half-error at4 and an analytic log-two bound give `D(1)>=1/10`. Since `sqrt p<=(7/4)sqrt N`, each such prime contributes at least `sqrt N/40`. All other late-prime channels are nonnegative, so the complete mass satisfies the stated lower bound.
4. The corpus prime-window theorem, derived from its unconditional prime number theorem, gives eventually
   `card{p:2N<p<=3N}>=N/(2 log(2N))`.
   Hence `T(4N)/(4N)>=sqrt N/(320 log(2N))`. The existing analytic fact `log x=o(sqrt x)` makes this lower comparison tend to infinity. No numerical prime count is a proof input.
5. The triangle inequality applied to H-S=T gives `abs H+abs S>=T`. Thus both terms cannot share a fixed linear bound. The scalar inequality `(abs H+abs S)^2<=2(H^2+S^2)` excludes every fixed combined quadratic bound. Finally the closed diagonal ceiling `Q_empty(M)<=722M²` excludes every fixed multiple of the original diagonal as a combined budget.
6. In a finite increasing-prime elimination, expanding the commuting differences `(1-L_p)` shows the d=1 coefficient after all primes through M/2 have been processed is exactly H(M): squarefree products give their Möbius coefficients, and products exceeding M vanish. The stage energy includes H(M)^2. The terminal stage equals S(M)^2. Therefore PE2 would bound their sum by `2Q_empty(M)`, contradicting step5. PE1 implies PE2 and is excluded as well. The Lean no-go is stated directly on the exact head and final-source energies, avoiding an extra conditional receiver predicate.

The strongest positive survivor is a genuine first-prime energy release together with an intermediate head asymptotic to the exact superlinear late-prime mass. Quantitative PNT, logarithmic square-root monotonicity and Cesàro averaging give the dependency-closed asymptotic proof on the linked card. A source proof using increasing-prime order must permit large intermediate amplitudes and control their final signed interaction. This particular head obstruction does not apply to every ordering; the separate [adaptive-order obstruction](ccm-fu-adaptive-prime-energy.md) independently proves that every order increases energy in its final step at cutoff seven, despite strict total diagonal dominance. That closes adaptive stepwise contraction, while an adaptive original-energy ceiling permitting local increases remains unclassified.

## Lean certificates and audit

- [MobiusDivisorPrimePairEnergy.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimePairEnergy.lean): exact signed-sum preservation, exact released overlap, and `sum_mobiusDivisorPrimePair_sq_le` for every prime and cutoff.
- [MobiusDivisorLatePrimeCompensation.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorLatePrimeCompensation.lean): late-prime mass floor/divergence, exact smooth-head compensation, combined normalized divergence, and the three impossibility statements for uniform linear, quadratic, and original-diagonal budgets.

Both modules pass individual foreground `lake env lean` checks, with only their exact oleans produced. Both are wired once into `RHTower.lean`. No large or umbrella build is run. The single axiom audit covers only the ten new public declarations and reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The declaration index is refreshed and task scratch files are removed. Global formal lint passes with existing file-size warnings. The linked head-asymptotic module has its own seven-declaration audit; these ten declarations were not re-audited.

## Numerical guidance, separate from the proof

The [screen and independent direct audit](../2-fully-proven/computations/ccm-fu-prime-pair-energy-2026-09-06/README.md) check every cutoff 1..1024 and increasing-prime stage. PE1 first fails at M=5,p=3; PE2 first fails at M=198,p=43. Direct defining sums confirm both at 70-digit precision. The largest screened stage/original ratio is about 4.10915 at M=903,p=223. These finite witnesses are not Lean certificates for those particular cutoffs; the stronger all-scale obstruction above is analytic and formal. Do not rerun this screen without a new research question.
