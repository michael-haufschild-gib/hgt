# MC exponential-weight prime-phase zero

- **ID:** MC-C12.92
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (paper proof under audit; Lean OPEN)
- **Source:** `mc-complete-signed-correlation.md`, C12.92; route MC in `docs/reports/rh-current-frontier-map.md`.
- **Statement:** For every sufficiently small t>0, the arithmetic weight w_t(n)=exp(-nt)/n has a simple zero under a bounded completely multiplicative prime-phase evaluation. Consequently it has no absolutely summable complex Dirichlet-convolution square root.

## Goal

Test the proposed unconditional positivity producer for J_lambda(t)=sum lambda(n)*exp(-nt)/n. An absolutely summable real convolution square root of w_t would make J_lambda a real square. A merely formal coefficient square root does not justify that evaluation. The proposed obstruction below concerns the actual weight, with all integers retained. It neither disproves J_lambda>=0 nor proves or refutes RH. The unchanged hard target is J_lambda(t)>=-C_epsilon*t^(1/2-epsilon).

## Gates

- [x] 0 → 1: exact weight and full-source attack specified; current corpus searched.
- [ ] 1 → 2: dependency-closed paper proof and novelty audit complete.
- [ ] 2 → 3: exact simple-zero theorem and no-square corollary formalized and audited.
- [ ] 3 → 4: publication-ready.

## Paper argument under audit

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

## No-go closure (not completed)

- **Proposed killing mechanism:** a simple prime-phase zero of the actual exponential weight forbids any absolutely summable Dirichlet square root.
- **Strongest positive survivor:** the full arithmetic Bohr transform has a simple zero in a one-dimensional phase disc; its exact linear capacity has a strict delta/log(N) gap, while the complete nonlinear part is exponentially small.
- **New insight:** prime-phase coherence, which the literal Liouville source possesses, cannot be discarded through an unconditional convolution-square representation of the smoothing weight. This obstruction does not bound the literal Liouville evaluation.
- **Status:** paper argument under audit; exact analytic and arithmetic transfers remain to be formalized. No route retirement or completed no-go claimed.

## Verified phase-gap component

`formal/GaloisForLFunctions/RHTower/LiouvilleTwistedDensityPhase.lean` now formalizes the exact fixed twist and its complete density. In namespace `RHTower.LiouvilleTwistedDensity`:

- `density_second_order` bounds the entire tail after q+i*q^2/2 by q^3/(1-q).
- `exponentialDensity_phase_separation` proves Im(conj(F(2u))*F(u))>0 for every u>log16.
- `exponentialDensity_integral_gap` proves the strict weighted integral triangle gap on [u,2u] for that same actual source.
- `exists_exponentialDensity_integral_gap` supplies such an interval with u>1, without an analytic or arithmetic premise.

The integral argument rotates by the phase of the integral. Equality at both endpoints would force collinearity, contradicting the proved positive cross-imaginary part. Continuity then makes the integral inequality strict. It does not assume an unproved nonconstant-phase condition.

Validation: targeted `lake --old build GaloisForLFunctions.RHTower.LiouvilleTwistedDensityPhase` passed (only the changed leaf rebuilt); required direct `lake --old env lean GaloisForLFunctions/RHTower/LiouvilleTwistedDensityPhase.lean` passed. A `/tmp` audit of all 13 public theorems passed, each using only `propext`, `Classical.choice`, `Quot.sound`. The leaf is imported in `RHTower.lean`; no umbrella build. Global `scripts/formal_tools.py lint` exited1 on 13 other umbrella-reachability errors, with no error for this leaf. No new axioms, placeholders, heartbeat changes or numerical experiments.

The exact full simple-zero survivor is still OPEN in Lean. Remaining steps: fixed-log harmonic transfer to this twist; scaled weighted prime limit; exact moving-prime decomposition with its full nonlinear tail; zero existence and simplicity; convolution-root contradiction. This component closes the phase-gap obligation, not the whole no-go and not the MC critical estimate.

## Log

- 2026-10-03, 1005f — C12.92 root conjecture tested; simple-zero proof candidate developed. No numerical mathematical computation or RH conclusion.
- 2026-10-03, 1005f — Actual fixed-twist phase gap formalized and audited; full simple-zero formalization remains in progress.
- 2026-10-03, 1005g — Revalidated phase-gap source and current MC frontier. Formalizing the actual harmonic square-dilation transfer: summability of the logarithmically weighted square kernel should carry the proved Mobius harmonic o(1/log N) cancellation to Liouville, then to the prime-two twist. Previous turn is verified progress on the obstruction, not a critical RH estimate.
