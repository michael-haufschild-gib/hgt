# MC exponential-weight prime-phase zero

- **ID:** MC-C12.92
- **Stage:** 3-formalized
- **Type:** THEOREM; unconditional simple-zero survivor and scalar square-root obstruction, Lean audited.
- **Source:** `../1-in-progress/mc-complete-signed-correlation.md`, C12.92; route MC in `docs/reports/rh-current-frontier-map.md`.
- **Statement:** For every sufficiently small t>0, the arithmetic weight w_t(n)=exp(-nt)/n has a simple zero under a bounded completely multiplicative prime-phase evaluation. Consequently it has no absolutely summable complex Dirichlet-convolution square root.

## Goal

Test the proposed unconditional positivity producer for J_lambda(t)=sum lambda(n)*exp(-nt)/n. An absolutely summable real convolution square root of w_t would make J_lambda a real square. A merely formal coefficient square root does not justify that evaluation. The proposed obstruction below concerns the actual weight, with all integers retained. It neither disproves J_lambda>=0 nor proves or refutes RH. The unchanged hard target is J_lambda(t)>=-C_epsilon*t^(1/2-epsilon).

## Gates

- [x] 0 → 1: exact weight and full-source attack specified; current corpus searched.
- [x] 1 → 2: dependency-closed paper proof and corpus overlap audit complete; no claim of global literature novelty.
- [x] 2 → 3: exact simple-zero theorem and no-square corollary formalized and audited.
- [ ] 3 → 4: publication-ready.

## Original paper argument (historical; final proof changes recorded below)

Put t=1/N with N real tending to infinity. All sums below start at n=1.

1. Let f be completely multiplicative, f(2)=i and f(p)=-1 for every odd prime. Set F(u)=sum f(n)*exp(-nu)/n. Its relation to lambda is f=lambda*eta, with eta(1)=1, eta(2^e)=(1+i)*i^(e-1) for e>=1 and eta zero elsewhere. Hence

   F(t)=J_lambda(t)+sum_(e>=1) eta(2^e)/2^e * J_lambda(2^e*t).

   The corpus's unconditional arbitrary fixed logarithmic Mertens bounds transfer to Liouville through lambda=mu*squareIndicator. The harmonic Liouville sum is zero. Abel summation then gives J_lambda(t)=O_A(log(1/t)^(-A)) as t decreases to zero. Splitting e at 2^e=sqrt(N), using the fixed-log bound on the lower part and global boundedness of J_lambda on the upper part, gives F(1/N)=o(1/log N). These transfer steps require their own exact Lean proof; the fixed-log bound is not a critical estimate.

   A direct dependency audit avoids assuming a harmonic Liouville limit separately. Write H_mu(X)=sum_(n<=X) mu(n)/n and similarly H_lambda. The exact finite convolution identity is H_lambda(X)=sum_(k<=sqrt(X)) k^(-2)*H_mu(floor(X/k^2)). For k<=X^(1/4), the corpus's arbitrary fixed-log harmonic bound gives O_A(log(X)^(-A)) after summing k^(-2); floor effects only change a fixed constant. For k>X^(1/4), use |H_mu(m)|<=1+log X and the square tail sum to get O(X^(-1/4)*log X). Thus H_lambda has every fixed-log saving and in particular tends to zero. The finite eta convolution, split at 2^e=sqrt X, gives the same rate for H_f, with upper part O(X^(-1/2)*log X). Finally the exact Abel identity F(1/N)=N^(-1)*integral_0^infinity exp(-x/N)*H_f(x) dx, split at sqrt N, gives O(N^(-1/2))+O_A(log(N)^(-A)); H_f is globally bounded by its limiting zero and its finite initial range.

   An alternative formal transfer uses dominated convergence rather than a moving split. The square kernel has every absolute logarithmic moment, sum_k (1+log k)^A/k^2<infinity. For m=floor(X/k^2)>=1, log X<=2log k+log(m+1); the global boundedness of log(m+1)^A*H_mu(m) supplies a summable logarithmic majorant. The eta kernel has the same moment property. This is a proof mechanism to formalize, not an assumed closure theorem.

2. At infinity, F(u)=exp(-u)+(i/2)*exp(-2u)+O(exp(-3u)). Its argument is therefore not constant on the positive axis. Choose a fixed compact interval [a,b], with 1<=a<b, on which F is nonzero and its argument is not constant. Strictness of the integral triangle inequality gives

   I=integral_a^b F(u)/u du,
   A=integral_a^b |F(u)|/u du,
   delta=A-|I|>0.

   Existence needs no numerical evaluation: if the argument were constant on every sufficiently large interval, the leading real term would force that argument to be zero, contradicting the imaginary second term.

3. Let P_N be all primes in [aN,bN]. For large N this excludes 2. Let C_N be the part of F(1/N) supported on integers with no P_N prime divisor. For each p in P_N define the exact linear coefficient

   A_(p,N)=(1/p)*sum_(m with no P_N prime divisor) f(m)*exp(-pm/N)/m.

   Replacing the restricted cofactor sum by the full sum changes it by an exponentially small amount, uniformly after summing over p: an excluded cofactor has m>=aN, so pm/N>=a^2*N. In particular A_(p,N)=F(p/N)/p plus that error. The corpus's prime-counting PNT, by partial summation on the fixed interval [a,b], yields

   (log N)*sum_p A_(p,N) -> I,
   (log N)*sum_p |A_(p,N)| -> A.

4. Choose beta_p=conj(A_(p,N))/|A_(p,N)| when the coefficient is nonzero, and beta_p=1 otherwise. Define f_(N,z) completely multiplicatively by f_(N,z)(p)=z*beta_p for p in P_N and f_(N,z)(p)=f(p) outside P_N. Then

   W_N(z)=sum_n f_(N,z)(n)*exp(-n/N)/n
         =C_N+S_N*z+R_N(z),
   S_N=sum_p |A_(p,N)|.

   This is entire in z: on any fixed z-disc, the degree (total P_N-prime multiplicity of n) is at most log(n)/log(2), and exponential decay dominates the resulting fixed power of n. R_N contains exactly the integers with total band-prime multiplicity at least two, including prime squares. Such n are at least a^2*N^2. Uniformly on |z|<=1,

   |R_N(z)| <= sum_(n>=a^2*N^2) exp(-n/N)/n,
   |R_N'(z)| <= sum_(n>=a^2*N^2) exp(-n/N).

   The second inequality uses multiplicity<=n. Both bounds are exponentially small in N (the latter allows an additional factor N). No nonlinear term has been omitted.

5. Evaluate the original multivariable sum at band prime values -1. Its linear term is -sum_p A_(p,N), and its terms of band multiplicity at least two obey the same absolute tail bound. Thus

   F(1/N)=C_N-sum_p A_(p,N)+E_N,
   (log N)*C_N -> I,
   (log N)*S_N -> A.

   In particular |C_N|/S_N -> |I|/A<1 and S_N>0 eventually. This retains the actual center; no arbitrary constant is substituted.

6. Put z_N=-C_N/S_N. Choose a fixed radius r>0 such that the closed disc around z_N of radius r lies inside |z|<1 for all sufficiently large N. On its boundary the linear function h_N(z)=C_N+S_N*z has norm S_N*r. The exponentially small remainder is eventually at most S_N*r/3. If R_N(z_N)=0, the center is already a zero. Otherwise `HTGeometry.exists_zero_of_sphere_domination` applies with g=R_N and h=h_N. It produces a zero of W_N in that disc. At every point of the disc, |R_N'|<S_N, so W_N' is nonzero. The zero is simple.

7. Suppose c*c=w_(1/N) and sum|c(n)|<infinity, allowing complex c. Evaluation by f_(N,z) for |z|<1 gives W_N(z)=(sum c(n)*f_(N,z)(n))^2. Absolute convolution interchange is valid because |f_(N,z)(n)|<=1. The inner series is holomorphic on the unit disc by locally uniform convergence, bounded termwise by |c(n)|. Every zero of its square has zero derivative. This contradicts the simple zero from step 6.

## Corpus and novelty audit

Read `HTGeometry/HelsonCharacterLSeries.lean`: its `phaseChar` definition permits arbitrary prime values; the existing unit-norm lemmas alone do not prove the closed-disc bound needed here. Read `HTGeometry/HurwitzClosedZeroLocus.lean`: `exists_zero_of_sphere_domination` supplies the zero from a factor-three boundary gap, with its differentiability and nonzero-center premises retained. Read the actual `Sieve/PrimeCountingBigO.primeCounting_sub_logIntegral_isBigO`: it supplies the fixed-interval prime asymptotic, not a Liouville sign law.

The existing binomial convolution half squares to mu, not w_t. Helson phase algebraic independence and finite-prime logarithmic phase rigidity do not state the simple-zero result above. Deep phase search primarily returned Dirichlet-character L-zero transfers, whose characters, zeros and hypotheses do not substitute for W_N. Prime-integral search returned the PNT input and conditional critical prime-window estimates; no ready weighted scaling limit was identified. Search coverage is partial and does not certify global novelty.

## No-go closure (completed 2026-10-04, 1005i)

- **Killing mechanism:** for every sufficiently small t>0, the actual weight exp(-nt)/n has a simple bounded prime-phase zero. An absolutely summable complex Dirichlet square would evaluate to a holomorphic square, which cannot have a simple zero.
- **Strongest positive survivor:** the complete arithmetic phase source has a simple zero strictly inside the unit disc at every sufficiently large real scale T=1/t. This uses the actual center, a strict prime-response capacity gap, all excluded cofactors, every repeated prime, and the full nonlinear derivative.
- **Exact new insight:** a logarithmically vanishing fixed-twist center and an angular gap of the actual cofactor response produce robust simple zeros of the smoothed arithmetic weight itself. A scalar convolution square cannot be its positivity representation. The literal Liouville evaluation is not bounded by this obstruction.
- **Paper and Lean status:** complete. `RHTower.LiouvillePrimeBand.exists_eventually_simple_prime_phase_zero` and `exists_small_no_summable_dirichlet_square_root` have no analytic or arithmetic hypotheses. The failed scalar-root proposal has its separate card in `../5-failed/mc-exponential-weight-scalar-square-root.md`. MC and RH remain open.

## Verified phase-gap component

`formal/GaloisForLFunctions/RHTower/LiouvilleTwistedDensityPhase.lean` now formalizes the exact fixed twist and its complete density. In namespace `RHTower.LiouvilleTwistedDensity`:

- `density_second_order` bounds the entire tail after q+i*q^2/2 by q^3/(1-q).
- `exponentialDensity_phase_separation` proves Im(conj(F(2u))*F(u))>0 for every u>log16.
- `exponentialDensity_integral_gap` proves the strict weighted integral triangle gap on [u,2u] for that same actual source.
- `exists_exponentialDensity_integral_gap` supplies such an interval with u>1, without an analytic or arithmetic premise.

The integral argument rotates by the phase of the integral. Equality at both endpoints would force collinearity, contradicting the proved positive cross-imaginary part. Continuity then makes the integral inequality strict. It does not assume an unproved nonconstant-phase condition.

Validation: targeted `lake --old build GaloisForLFunctions.RHTower.LiouvilleTwistedDensityPhase` passed (only the changed leaf rebuilt); required direct `lake --old env lean GaloisForLFunctions/RHTower/LiouvilleTwistedDensityPhase.lean` passed. A `/tmp` audit of all 13 public theorems passed, each using only `propext`, `Classical.choice`, `Quot.sound`. The leaf is imported in `RHTower.lean`; no umbrella build. Global `scripts/formal_tools.py lint` exited1 on 13 other umbrella-reachability errors, with no error for this leaf. No new axioms, placeholders, heartbeat changes or numerical experiments.

The exact full simple-zero survivor is still OPEN in Lean. The harmonic transfer and exponential center along a cofinal sequence are now formalized below. Remaining steps: actual finite prime-phase capacity (the two-interval argument below replaces the weighted prime limit); exact moving-prime decomposition with its full nonlinear tail; zero existence and simplicity; convolution-root contradiction. These components do not close the whole no-go or the MC critical estimate.

## Log

- 2026-10-03, 1005f — C12.92 root conjecture tested; simple-zero proof candidate developed. No numerical mathematical computation or RH conclusion.
- 2026-10-03, 1005f — Actual fixed-twist phase gap formalized and audited; full simple-zero formalization remains in progress.
- 2026-10-03, 1005g — Revalidated phase-gap source and current MC frontier. Formalizing the actual harmonic square-dilation transfer: summability of the logarithmically weighted square kernel should carry the proved Mobius harmonic o(1/log N) cancellation to Liouville, then to the prime-two twist. Previous turn is verified progress on the obstruction, not a critical RH estimate.

## Two-interval replacement for the weighted prime-integral limit (1005g, paper)

The verified endpoint phase separation permits a simpler capacity proof. Define
D(x,y)=|F(x)||F(y)|-Re(conj(F(x))*F(y)). It is nonnegative everywhere, and it is strictly positive at the verified pair (u,2u). Continuity supplies disjoint positive-width compact intervals U,V inside (1,infinity), and d>0, such that D(x,y)>=d on U times V. Select only primes p with p/T in U union V. Primes outside this union retain the original twist value, including primes in the intervening gap.

For the ideal coefficients B_p=F(p/T)/p, put S=sum|B_p| and Z=sum B_p. The exact finite identity is

S^2-|Z|^2=sum_(p,q)(|B_p||B_q|-Re(conj(B_p)*B_q)).

Every summand is nonnegative. The two cross rectangles contribute at least 2*d*(sum_(p/T in U)1/p)*(sum_(q/T in V)1/q). The ordinary prime-counting PNT gives each reciprocal mass a lower bound c/log T and gives the total mass an upper bound C/log T. Since F is bounded on U union V, S<=C'/log T. Dividing by S+|Z|<=2S therefore gives S-|Z|>=c'/log T. No weighted prime-integral limit is needed for this conclusion.

Transfer this ideal gap to the exact band-free cofactor coefficients by their total absolute error E_T: the triangle deficit changes by at most 2*E_T. The identity for the actual center adds only |F(1/T)|, the original nonlinear tail, and one further E_T. Thus the center remains strictly inside the linear capacity when all these complete errors are o(1/log T). The nonlinear tail and simple-zero steps remain unchanged, because the least selected prime is still at least a*T for fixed a>1.

This is a paper simplification, not a completed Lean theorem or retired route. The inspected unconditional `pi_alt` and `pi_alt'` in `GaloisForLFunctions/PNTPlus/Consequences.lean` already give the ordinary PNT; an unrelated weighted-integral theorem is not required. The new center proof first treats the cofinal sequence T=(N+1)^2. That sequence suffices for a cofinal family of simple zeros and to falsify a proposed square-root representation for every t>0. The stronger original assertion for every sufficiently small t still requires extending the center estimate beyond this sequence.

## Corpus checkpoint for the two-interval proof

The prime-scaling search returned `HTGeometry/AbelianZetaGas/PrimeWindowCount.lean`. Its inspected theorem `eventually_primeCount_window_ge` already proves that every fixed multiplicative interval (x,Kx] contains at least ((K-1)/2)*x/log x primes eventually. Its `primesInIoc`, `card_primesInIoc`, and `mem_primesInIoc` retain exact finite prime sets and endpoint membership. Use this existing lower bound with x=a*T and K=b/a; bound each reciprocal weight below by 1/(b*T). The upper bound comes directly from the inspected unconditional `pi_alt'`. These facts support the new two-interval proof, not the originally proposed weighted-integral convergence theorem.

The two-band search itself returned generic interval-integral addition, unrelated CCM prime-deficit estimates, and our actual source continuity theorem. Its generated ingredient chain does not prove the angular capacity gap. The gap must be established from `exponentialDensity_phase_separation`, continuity, the exact double-sum identity, and these actual finite prime-window counts. No generated chain or premise from an unrelated RH detector is adopted.

## Verified harmonic and cofinal-center components (2026-10-04, 1005g)

`LiouvilleTwistedHarmonicDecay.lean` proves the exact harmonic square-dilation identity and the exact prime-two convolution. Its two final logarithmic limits are unconditional:

- log(N+1)*H_lambda(N) -> 0;
- log(N+1)*H_f(N) -> 0 for the actual fixed twist from `LiouvilleTwistedDensityPhase`.

The square kernel has summable absolute logarithmic moment. The prime-two kernel has coefficients eta(0)=1 and eta(e)=(1+i)*i^(e-1) for e>=1, giving a geometric logarithmic moment after division by 2^e. A dominated-convergence proof handles every dilation, including the zero-index convention, and never substitutes a finite truncation for the source.

`LiouvilleTwistedDensityCenter.lean` proves the full Abel identity

F(-log q)=(1-q)*sum_(n>=0) H_f(n)*q^n

in the equivalent `density q` notation for 0<=q<1, and the premise-free theorem `tendsto_log_mul_exponentialDensity_square_zero`:

log(N+1)*F(1/(N+1)^2) -> 0.

The identity is stated as `density q=(1-q)*sum H_f(n)*q^n`, including q=0; the expression F(-log q) is used only when q>0. For q=exp(-1/(N+1)^2), splitting the Abel average at n=N bounds the short contribution by B*log(N+1)/(N+1). In the full remaining sum, log(N+1)<=log(n+1), so the actual proved harmonic logarithmic limit controls the tail. All coefficients and both parts remain present.

Both targeted leaf builds passed, and each required direct `lake --old env lean` audit passed. Both imports are present in `RHTower.lean`; no umbrella build. The separate combined axiom audit is recorded after its completion below. Global formal lint exited1 with 14 unrelated umbrella-reachability errors and no error for either new leaf. No placeholders, added axioms, heartbeat raises, numerical mathematical experiments, subagents or commits were introduced by this work.

The cofinal center closes an actual cancellation input to the square-root obstruction. It does not give the Liouville half-power lower bound, the prime-phase capacity inequality, a simple zero, or an RH proof/refutation. The strongest original every-small-t simple-zero statement is still under formalization; the cofinal version already suffices to defeat a proposed convolution square root for every positive t once the remaining steps are proved.

Five corpus searches completed: harmonic, prime-twist, Abel smoothing, prime-scaling, and two-band phase deficit. Harmonic and Abel reported partial=false; the other three were partial. Inventories ranged65045–65072 files, compiled snapshots43, stale2660, compiler-pending49066–49081, generations1216020 through1220753, each with older-generation and semantic-coverage warnings and background refresh. Candidate lemmas, source arguments, proof ideas and ingredient sets were inspected; source scopes were checked directly and the actual used proof names verified in Lean. Proposed chains through finite exponential Mellin sums, unrelated RH detectors and generic interval addition do not discharge the new capacity obligation.

For the forthcoming analytic step, proving entire continuation is unnecessary for the simple-zero argument. At each fixed t>0, choose 1<R<exp(t). The elementary band-degree bound d(n)<=n then majorizes both the defining series and its derivative on |z|<=R by geometric exponential tails (the factor d(n)/n is at most one). This proves holomorphy on a neighborhood of the closed unit disc without first formalizing the stronger logarithmic degree bound. On |z|<=1, the exact nonlinear support still gives the stated derivative tail sum exp(-nt). This is an implementation simplification of the same full simple-zero survivor, not omission of any nonlinear coefficient.

Final 1005g verification: the combined `/tmp` axiom audit exited0 for all14 public theorems across both new leaves; every theorem uses only `propext`, `Classical.choice`, `Quot.sound`. All five searches, both leaf builds, both direct audits, and the combined axiom audit reached terminal status. Owned scratch and captured search/build outputs are removed after this record. The full no-go and RH goal remain open.

- 2026-10-04, 1005h — Previous turn classified as progress: two audited actual-source leaves, including the cofinal center. Revalidated current MC frontier and those source statements. Now formalizing the actual two-interval prime-phase capacity: uniform angular defect for F, exact finite double-sum identity, and full reciprocal prime mass. No critical Liouville estimate or completed simple-zero claim.

## Full-tail simplification for the exact band decomposition (1005h, paper)

With the selected intervals above1 and T>0, every selected prime p is strictly greater than T. A positive cofactor m excluded by band-freeness has a selected prime divisor, hence m>T. Since p/T>1, the complete cofactor error therefore obeys

|A_p-B_p| <= (1/p)*sum_(m>T) exp(-m),
sum_p|A_p-B_p| <= (sum_p1/p)*exp(-T)/(1-exp(-1)).

The prime reciprocal mass bound makes the logarithmically weighted total error tend to zero. This retains every excluded cofactor and needs no moving weighted-integral theorem.

An integer of band multiplicity at least two is divisible by p*q with both selected primes greater than T; p=q is permitted. Thus n>T^2. Band degree d(n)<=n gives, uniformly on |z|<=1,

|R_T(z)|, |R_T'(z)| <= sum_(n>T^2) exp(-n/T) <= (T+1)*exp(-T).

The last inequality uses the exact geometric tail and 1/(1-exp(-1/T))<=T+1, obtained from exp(1/T)>=1+1/T. The original untwisted nonlinear remainder obeys the same bound. These are full-tail paper inequalities awaiting formalization, not numerical estimates or discarded prime-square terms.

### Moving-disc simplification (1005h, paper)

The final simple-zero argument does not need a separate upper asymptotic for the exact capacity S. Once S-|C|>=g>0, the complete remainder is smaller than g/6, and its derivative is smaller than g/2, take z0=-C/S and r=g/(2*S). Then |z0|+r<=1-g/(2*S)<1, while the affine part has modulus S*r=g/2 on the moving circle. The inspected `exists_zero_of_sphere_domination` requires 3*|R|<=|affine|, supplied by the g/6 threshold. If R(z0)=0 the center already is a zero; otherwise that theorem supplies a zero in the closed moving disc. The inequality |R'|<S makes either zero simple. Here g can be a fixed positive constant divided by log(T). The circle may depend on T; no fixed limiting center or limiting radius is required.

Likewise the summed cofactor error only needs the elementary bound on selected reciprocal mass from P_T subset [1,d*T] and p>T: sum_P 1/p<=d (up to an inessential fixed enlargement for the floor). Its exponential decay then absorbs log(T). The PNT is still used in the already-proved capacity gap, but no second reciprocal-prime asymptotic is needed for error transfer. This changes proof dependencies, not the complete-source statement.

### Exact assembly ledger after the full-tail proof (1005h)

Write A_p for the band-free response, B_p=F(p/T)/p, E_A=sum_P|A_p-B_p|, S=sum_P|A_p| and Z=sum_P A_p. The verified ideal gap transfers by two triangle inequalities:

S-|Z| >= (sum_P|B_p|-|sum_P B_p|)-2*E_A.

The exact baseline decomposition is F(1/T)=C-Z+E_original, since every selected prime has baseline phase -1 once T>2. Hence

S-|C| >= kappa/log(T)-2*E_A-|F(1/T)|-|E_original|.

Along T=(N+1)^2, the verified center gives log(T)*F(1/T)->0. The proved cofactor and nonlinear errors, together with the elementary reciprocal-mass upper bound, give log(T)*E_A->0 and log(T)*E_original->0. The right side is eventually at least g=kappa/(2*log(T)). Align A_p by beta_p=conj(A_p)/|A_p| when A_p is nonzero and beta_p=1 otherwise. Then beta_p has unit norm and the complete source is C+S*z+R(z). The moving-disc argument above applies once the full remainder bound is below g/6. Its derivative bound below S excludes multiple zeros.

These last transfer, phase-alignment, moving-disc, and square-evaluation steps remain Lean OPEN at this checkpoint; none is silently assumed in a claimed final theorem. The original every-small-t formulation still requires a full center limit beyond the already-proved cofinal square sequence.

## 1005h formal frontier advance (2026-10-04)

Four new leaves now pass targeted builds and direct `lake --old env lean` checks:

- `LiouvilleTwistedPrimeCapacity.lean`: premise-free existence of two disjoint intervals above1 with a uniform actual-density phase defect, and premise-free existence of kappa>0 with log(T)*(idealCapacity-|idealCenter|)>=kappa eventually. The proof derives actual scaled prime-window counts from `pi_alt`, brackets reciprocal mass, and retains the entire finite pairwise triangle deficit. It uses unrestricted responses B_p=F(p/T)/p.
- `LiouvillePrimeBandAlgebra.lean`: exact selected-prime multiplicity, monomial parameterization, baseline recovery and coefficient decomposition. Degree>=2 supplies p*q dividing n with p=q allowed, hence n>T^2. Positive degree gives n>T. No prime square is discarded.
- `LiouvillePrimeBandAnalysis.lean`: full cofactor error, its sum over every selected prime, complex termwise differentiation of every degree slice throughout the closed unit disc, and bounds |R|,|R'|<=(T+1)*exp(-T). It also identifies the series with the complete arithmetic character evaluation and recovers the actual original twist at baseline phases. The derivative domination uses degree(n)<=n and a geometric majorant on radius exp(t/2)>1; no heartbeat option was raised.
- `LiouvillePrimeBandDecomposition.lean`: the exact linear identity degreeSlice({1})=z*sum_P beta_p*A_p, obtained by reindexing every multiple n=p*m. The full source is C+z*sum_P beta_p*A_p+R, and the actual baseline is F=C-sum_P A_p+E_original. Absolute convergence justifies the complete finite-prime/infinite-integer interchange.

These results close actual source obligations of C12.92. They do not yet prove the simple zero or no-square-root conclusion, and they do not supply the RH-producing half-power lower bound on J_lambda. The next exact formal target is the premise-free cofinal simple-zero theorem using the ledger above, followed by the absolutely summable Dirichlet-square evaluation contradiction. The no-go remains open; no route is retired.

Three corpus searches completed with partial=false: finite complex deficit/prime mass, selected-prime multiplicity, and full exponential/derivative tails. Inventories65081–65098, compiled snapshots43, stale2660, compiler-pending49085–49095; generations1220856/1220986/1221075 with current generations1220857/1221003/1221076. All reported older-generation and semantic-coverage warnings and background refresh. Candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. The finite norm-square identity and actual phase-character/factorization APIs were applicable; suggested chains through prime-ideal multiplicity, unrelated prime tail estimates and positive Dirichlet power-series radii did not discharge the complex band obligations. Used names and proofs were checked against the installed Lean toolchain.

**Final 1005h validation:** all four targeted `lake --old build` leaf builds and all four required direct `lake --old env lean` checks exited0. Separate `/tmp` axiom audits covered all34 public theorems (2 capacity,20 algebra,9 analysis,3 decomposition); every result uses only `propext`, `Classical.choice`, `Quot.sound`. All four imports are present in `RHTower.lean`; no umbrella build. The final global lint exited1 with15 unrelated umbrella-reachability errors and none for these leaves: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, RoutePFinitePrimeCovariance, RoutePPrimeCovarianceBudget, ThetaCuspC5IntrinsicGreenRecovery, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving, and HTGeometry.CompactMonoidMeasureAlgebra. Targeted whitespace and forbidden-declaration checks found no issue. No added axiom, placeholder, heartbeat increase, numerical mathematical experiment, subagent or commit was introduced. All owned searches, builds and audits reached terminal status; owned temporary files are cleaned after this entry. RH goal remains active and unmet.

- 2026-10-04, 1005i — Previous turn is verified progress: four actual-source leaves, all34 public axiom audits and direct file checks passed. Current source revalidated. Route MC's half-power Liouville lower bound remains open. Now attacking a premise-free cofinal simple-zero theorem by transferring the actual capacity gap through all cofactor errors, aligning the full linear response, and applying sphere domination with derivative control. No generic receiver will count as completion of this target.

## 1005i closure: every real scale, simple zero, and no square (2026-10-04)

**Exact final proof.** `LiouvilleTwistedDensityCenter.tendsto_log_mul_exponentialDensity_reciprocal_zero` upgrades the center from the square sequence to every real T tending to infinity. In the exact Abel identity take N=floor(sqrt T): N^2<=T<=(N+1)^2, log T<=2log(N+1), and N/T<=2/(N+1). The complete short sum tends to zero by log(N+1)/(N+1)->0; the entire remaining sum is paid by the existing harmonic logarithmic limit. No subsequence or unproved uniform interpolation remains.

`LiouvillePrimeBandSimpleZero.lean` bounds the sum of all cofactor replacement errors by d*exp(-T)/(1-exp(-1)). The actual response surplus is at least the proved ideal surplus minus twice that error, |F(1/T)|, and b=(T+1)*exp(-T). After multiplying by log T these errors vanish. The final surplus exceeds 6b. Align every actual coefficient A_p and put S=sum|A_p|, g=S-|C|. The disc centered at -C/S with radius g/(2S) lies strictly inside |z|<1. Its affine boundary norm g/2 dominates three times the full nonlinear remainder. Sphere domination yields a zero; |R'|<=b<S makes it simple. This discharges all inputs internally for every sufficiently large real T.

`LiouvilleExponentialWeightNoSquare.lean` uses the literal arithmetic function w_t(0)=0, w_t(n)=exp(-nt)/n. A bounded completely multiplicative character preserves Dirichlet convolution on absolutely summable coefficients, proved via the full twisted L-series product at zero. The coefficient evaluation is holomorphic on the unit disc by its full l1 majorant. A convolution square would therefore make the source E(z)^2. At the established simple zero E(z)=0, forcing derivative zero, a contradiction. Inverting the real scale gives an entire punctured damping interval with no complex l1 square root, and refutes the universal square-root proposal. No assertion about the sign of J_lambda follows.

**Validation.** Three targeted leaf builds passed: modified Center, new SimpleZero, new NoSquare. Each required final `lake --old env lean GaloisForLFunctions/RHTower/<leaf>.lean` passed with empty output. All eight public theorems in those three leaves passed the /tmp axiom audit with only propext, Classical.choice and Quot.sound. New imports are wired into RHTower; no umbrella build. Global `scripts/formal_tools.py lint` exited1 on thirteen other unreachable modules (CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaCuspC5IntrinsicClockGerm, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving, HTGeometry.CompactMonoidMeasureAlgebra). No lint error concerns these three leaves. No new axioms, placeholders, heartbeat increase, numerical mathematical experiment, subagent or commit.

**Core search audit.** Simple-zero search and square-evaluation search completed partial=false; full real-scale center search completed partial=true. Snapshots inventoried65115/65119/65124 files, compiled43, compiler-pending49108/49111/49116, stale2660, no method invalidation pending; generations1221307/1221361/1221425 with newer current snapshots. Older-generation and semantic-coverage warnings, background refresh. Candidates, source arguments, proof ideas and ingredient sets were inspected. The sphere-zero theorem and LSeries convolution product were read and applied with every hypothesis discharged. The weighted Dirichlet algebra's logarithmic-frequency evaluation was not substituted for arbitrary prime phases. Conditional floor transforms and generated unrelated circle-average/L-character chains were not used. Search coverage does not certify global novelty.

**Next hard target.** The scalar-root candidate is retired; the proved simple-zero survivor is retained. The full signed density lower bound J_lambda(t)>=-C_epsilon*t^(1/2-epsilon) remains unchanged. The next source-specific conjecture is recorded in `../1-in-progress/mc-scaled-liouville-density-cone.md`; merely introducing that conjecture does not count as a new critical estimate. Goal active/unmet.

**1005i cleanup complete:** removed all25 exact owned /tmp search/proof/audit files after recording results. Every owned search, Lean and lint process reached a terminal exit; no owned live handle remains.
