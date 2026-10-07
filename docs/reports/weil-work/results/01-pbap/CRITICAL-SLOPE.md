# Critical gamma coefficient: paper proof and Lean certificate

Status: dependency-closed paper proof and ten fully audited Lean leaves, including the negative and normalized-null witnesses. Scientific verdict: **SCOPED NO-GO**, novelty unestablished. This establishes a necessary coefficient boundary; it does not prove PBAP at that boundary.

## Exact theorem

For every real `a >= 0`, `b > a`, and `C`, there is a nonnegative finite mixture of smooth compactly supported complex tests, with every symmetric integer-log autocorrelation sample zero, such that

    a Gamma(c) + b Pole(c) + C Mass(c) < 0.

Here `Gamma(f)=(1/(2 pi)) integral |paperFT f(t)|^2 gammaBracket(t) dt`, `Pole(f)=2 Re(paperFT f(i/2) conjugate(paperFT f(-i/2)))`, and `Mass(f)=integral |f|^2`. Each extends linearly to mixtures. These are exactly the two pieces of `WeilOneSided.weilArchRe`, without deleting either pole.

Equivalently, on normalized integer-null mixtures, the infimum of `a Gamma + b Pole` is minus infinity whenever `0 <= a < b`. In particular no bound `-Pole <= a Gamma + C Mass` with `a<1` can prove full PBAP. The coefficient-one endpoint is still open.

## Parent theories and preliminary attack

The sharp multiplicative Toeplitz ceiling and primitive-set mean-square argument already exist in `WeilPositivityMultiplicativeToeplitzBound` and `WeilPrimitiveSetMeanSquare`. Their published signatures use the fixed gamma datum. The coefficient/slack version below is derived, not assumed. The null-cone extension theorem is already generic in `HTGeometry/FinsuppOneSidedFeasibility`.

Booker's *L-functions as distributions* (arXiv:1308.3067v2), Definition 1.3, imposes both coefficient decay/mean-square conditions (A1) and a discrete spectral divisor integral except at finitely many points (A3). Our hypothetical completion permits arbitrary real arithmetic coefficients and has no discrete or integral spectral assumption. Its low-degree classification cannot simply be invoked here. Oliver's arXiv:1601.05009 is a relevant descendant. These comparisons do not establish novelty.

A stronger absolute domination `Gamma >= |Pole|` is already false by the corpus's compact prime-blind negative-gamma test. A mass-only pole bound was already discussed in L239/L244, with a paper Bohr-continuation argument. The theorem here targets the whole strict half-plane `b>a`, with arbitrary constant slack.

## Proof

Suppose the displayed functional is nonnegative on every nonnegative null mixture. The generic null-cone extension theorem applies to the finite sample vectors `logVector(f)`. Its cofinality hypotheses are witnessed by the existing smooth pair tests with sample vectors equal to positive and negative multiples of each coordinate. It supplies real coefficients `lambda(n)`, `n>=2`, such that every smooth compact test satisfies

    sum_{n>=2} lambda(n) logValue(f,n)
      <= a Gamma(f) + b Pole(f) + C Mass(f).                 (1)

Set lambda(0)=lambda(1)=0. The sum is finite for each compact test. No coefficient sign, growth, convergence or spectral representation is imposed.

### 1. Sharp finite multiplicative bound

Use the corpus's centered polar resonator `F_N,c=sum_{m=1}^N c_m g_w(. - log m + (log N)/2)`, where `w=1/(N+1)` and `g_w=psi_w''-psi_w/4`. The two pole moments vanish. Put `m_w=integral |g_w|^2>0`, `S=sum |c_m|^2`. Integer log separation gives exact mass `m_w S` and exact atom pairing

    2 m_w sum_{n=2}^N lambda(n)/sqrt(n)
                    Re sum_{m=1}^N c_(nm) conjugate(c_m),

with `c_k=0` for `k>N`. The source proof's Plancherel/derivative estimate gives

    Gamma(F_N,c) <= m_w (log N + K0) S,

where `K0=log 2+9/2+profileRatio/2` is independent of `N,c,lambda`. This estimate precedes the positivity step in `weil_multiplicativeToeplitz_bound_at`; it uses neither lambda nor (1). Substitution in (1), division by `m_w`, and `a>=0` yield

    2 sum_{n=2}^N lambda(n)/sqrt(n)
                  Re sum_m c_(nm) conjugate(c_m)
        <= (a log N + K) sum_m |c_m|^2,                    (2)

where `K=a K0+C`. The vector supported only at 1 forces `a log N+K>=0` for every `N>=1`; in particular `K>=0`.

### 2. Absolute convergence follows from (2)

For a primitive set `S` in `[2,N]`, put `Q=sum_{n in S} lambda(n)^2/n` and use `c_1=1`, `c_n=t lambda(n)/sqrt(n)` on S. No two elements of S have a proper integer ratio, so (2) becomes `2tQ <= L(1+t^2 Q)` for every real t, with `L=a log N+K>=0`. If Q=0 the claim is immediate; otherwise take t=L/Q. The resulting inequality gives `Q<=L^2` (when L=0 the original inequality with t=1 already forces Q=0).

The interval `(N,2N]` is primitive, hence

    sum_{N<n<=2N} lambda(n)^2 <= 2N (a log(2N)+K)^2.

Cauchy-Schwarz gives `sum_{N<n<=2N}|lambda(n)| <= sqrt(2) N (a log(2N)+K)`. Summing dyadic blocks proves absolute convergence of `D(s)=sum lambda(n)n^(-s)` for every `Re s>1`. This repairs the initially suspected convergence gap without Bohr or Landau. The fixed-datum version is in `WeilPrimitiveSetMeanSquare`; `summable_abs_div_rpow_critical` now proves the modified-datum version.

### 3. Positivity forces the actual pole residue

Choose a real nonnegative nonzero smooth f supported in a sufficiently small interval, so its real even autocorrelation k has support in `[-r,r]` with `0<r<log 2`. Then k is nonnegative and

    B(q)=integral k(u) exp(q u) du

is continuous, strictly positive for real q, and `B(q)=B(-q)`. In particular B(1/2)>0.

Let T be the complex linear functional whose real quadratic form is the right side of (1) minus the left side. Explicitly on a compact smooth test h,

    T(h)=a Gamma(h)+b[paperFT h(i/2)+paperFT h(-i/2)]
         +C h(0)-sum lambda(n)/sqrt(n)[h(log n)+h(-log n)].

Here Gamma(h) denotes the linear Fourier pairing with gammaBracket. This functional is Hermitian. Positivity on autocorrelations implies that `K(y)=T(k(. - y))` is positive definite: every finite Gram sum is T applied to the autocorrelation of the corresponding finite linear combination of translates of f. Consequently `|K(y)|<=K(0)` by the two-by-two positive matrix inequality. This uses no assumed positive spectral measure or Bochner-Schwartz theorem.

The translated gamma term is uniformly bounded, because it is the Fourier integral of `paperFT k(t) gammaBracket(t)`, an absolutely integrable function. The translated mass term is bounded by `|C| sup|k|`. For y>=0 all negative-log atoms vanish, since r<log 2. Thus

    K(y)=a Gamma(k(. - y)) + C k(-y)
         +b B(1/2)[exp(y/2)+exp(-y/2)]
         -sum lambda(n)/sqrt(n) k(log n-y).                 (3)

Multiply by `exp(-(sigma-1/2)y)` and integrate over y>=0, for real `sigma>1`. Absolute convergence from step 2 justifies interchanging the atom sum and integral; each atom integral is exactly `n^(-(sigma-1/2)) B(sigma-1/2)`, since the support interval around log n lies wholly in the positive half-line. Equation (3) gives

    B(sigma-1/2) D(sigma)
      = b B(1/2)[1/(sigma-1)+1/sigma] + R(sigma),

where R is uniformly bounded for `1<sigma<=2`: each of its bounded translated terms is integrated against a kernel of integral `1/(sigma-1/2)<=2`. Hence

    lim_{sigma->1+} (sigma-1) D(sigma)=b.                  (4)

Every term in (4) is the actual absolutely convergent series; no analytic continuation hypothesis is inserted.

### 4. The density ceiling bounds the residue by a

In (2) put `c_m=m^(-1/2)` for `1<=m<=N`. Then

    2 S_lambda(N) <= (a log N+K) H_N,
    S_lambda(N)=sum_{nm<=N,n>=2} lambda(n)/(nm).

Since `H_N<=1+log N`, for each eps>0 there exists M_eps such that, for every real x>=1,

    S_lambda(floor x) <= (a/2+eps)(log x)^2 + M_eps.       (5)

The coefficients are signed; only this upper bound is used. Let `d(k)=sum_{n|k,n>=2}lambda(n)`. Absolute convergence from step 2 implies `sum d(k)k^(-(1+s))=D(1+s) zeta(1+s)` for s>0, and justifies partial summation/Fubini:

    D(1+s) zeta(1+s)
      =s integral_0^infinity S_lambda(floor exp(t)) exp(-s t) dt.

Using (5) gives

    s^2 D(1+s) zeta(1+s) <= a+2 eps+M_eps s^2.

The left side tends to b by (4) and the elementary residue-one formula for zeta. Let s decrease to zero, then eps decrease to zero. We obtain `b<=a`, contrary to b>a.

Therefore a negative null mixture exists. Its mass is positive: a nonnegative mixture of L2 masses can be zero only when each positively weighted smooth test is identically zero, which would make its entire energy zero. Divide the mixture by its mass. Since C was arbitrary, normalized energies are unbounded below. This completes the paper argument.

## Formalization plan and proof boundary

1. Define the modified datum on actual WeilTestFn and instantiate generic null-cone duality.
2. Extract the coefficient/slack resonator bound, then prove its primitive-set summability and harmonic density consequences.
3. Prove the translated-autocorrelation bound for the modified functional, its one-sided Laplace identity, and residue limit.
4. Combine with Abel partial summation and normalize the negative null witness.
5. Targeted `--old` leaf builds, final direct `lake env lean` audits, axiom checks, lint, and umbrella wiring only after completed leaves pass.

All steps use actual functions and finite mixtures. The final negative-witness theorems discharge the intermediate completion premise. No density bound, pole residue, spectral positivity, coefficient sign, summability or continuation assumption remains in those witnesses.

## Source checks

- `WeilPositivityMultiplicativeToeplitzBound.lean`: full one-level proof, exact log selection, mass and derivative estimates checked.
- `WeilPrimitiveSetMeanSquare.lean`: source confirms absolute convergence already holds for every fixed-datum polar-positive system on Re s>1. L244's older statement about only Re s>3/2 is stale for the current fixed-datum corpus. Its extension to the modified datum is now derived in `CriticalCoefficients`, not added as a premise.
- `WeilFullConeBochnerMeasure.lean`: translated Gram positivity checked; only its elementary positive-definite bound is needed, not spectral measure construction.
- `WeilFullConeOneSidedCriterion.lean`: actual sample vectors, pair-test cofinality, and generic extension invocation checked.
- External: [Booker](https://arxiv.org/html/1308.3067v2), [Oliver](https://arxiv.org/abs/1601.05009). Classical Abel summation and positive-definite two-point Cauchy-Schwarz are parents, not novelty claims.

## Implementation progress (2026-10-07)

The following intermediate leaves passed targeted `lake build --old +...` builds:

- `WeilWorkPBAPCriticalResonator`: exact mass, all integer samples, both zero pole moments, and the unconditional sharp gamma upper bound on the actual smooth polar resonator.
- `WeilWorkPBAPCriticalDatum`: duality on smooth finite null mixtures, exact coefficient pairing, and the modified-datum Toeplitz ceiling.
- `WeilWorkPBAPCriticalCoefficients`: primitive-set and dyadic mean square, actual absolute convergence at every real exponent above one, all multiplicative twists of the harmonic bound, and an explicit remainder in the sharp quadratic logarithmic ceiling.
- `WeilWorkPBAPCriticalKernel`: positivity of every translated finite Gram form and a uniform bound on the actual pole-minus-atom remainder.
- `WeilWorkPBAPCriticalWindow`: the literal signed arithmetic window differs from the two pole exponentials by a bounded amount.
- `WeilWorkPBAPCriticalLaplace`: actual signed-series interchange and the explicit Laplace remainder bound `M/sigma`.
- `WeilWorkPBAPCriticalResidue`: the actual real Dirichlet residue equals the pole weight; cleaned source rebuilt successfully.
- `WeilWorkPBAPCriticalAbel`: signed cumulative-series Fubini and the exact quadratic-envelope Laplace bound.
- `WeilWorkPBAPCriticalDensityLaplace`: exact arithmetic cumulative identity, absolutely convergent pair transform and sharp Dirichlet-product ceiling.
- `WeilWorkPBAPCriticalBoundary`: completion forces `b<=a`; `exists_negative_smooth_null_mixture` and `exists_normalized_critical_null_below` prove the stated negative and normalized witnesses. The fixed half-gamma theorem has no proposition input.

All ten targeted builds and all ten final direct-source audits pass without source diagnostics. Twenty-two axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`. All ten imports are wired in `RHTower.lean`; no umbrella build was run. Intermediate completion hypotheses are discharged in the final witnesses; none supplies a PBAP producer. Source hashes and the unrelated global lint failures are recorded in `EVIDENCE.md`.

Additional reusable source located: `WeilOneSided.integral_windowValue_mul_exp` in `WeilShiftPairLandau.lean` already proves the exact single-window Laplace formula for an arbitrary real profile with quarter-unit support. Its `autoLaplaceReal_eq`, `autoLaplaceReal_half`, and continuity machinery remove the need to rebuild those facts. Its series interchange currently specializes to von Mangoldt and must be adapted to the actual signed coefficients using the newly derived absolute convergence. The broad Abel-ceiling search returned `partial=false`; no complete applicable density-to-residue theorem was supplied. A hit for the current under-construction leaf is not independent verification.

The boundary build initially hit an elaboration timeout in the mass-zero integral lemma. Explicitly typed continuity, compact-support composition and nonzero-value facts removed the timeout without changing heartbeat limits. The repaired leaf passed its build, final source audit and capstone axiom checks.

A follow-up external search also located Burnol's [conductor-operator paper](https://arxiv.org/abs/math/9902080), his [support-restricted positivity note](https://arxiv.org/abs/math/0101068), and Connes–Consani's [The Scaling Hamiltonian](https://arxiv.org/pdf/1910.14368.pdf). The first two abstracts were inspected as adjacent parents. The last paper's introduction explicitly identifies a failed Hardy-boundedness step and the importance of global Poisson normalization. These are contextual checks, not substitute proofs of the present arbitrary signed-mixture statement; novelty remains unestablished.

## What this argument cannot decide

At equal gamma and pole weights the two residue limits agree. The constant mass slack disappears after multiplication by the vanishing Laplace parameter. Therefore the leading-coefficient argument cannot distinguish the literal PBAP datum (`C=0`) from any constant mass shift. A proof of endpoint positivity needs additional finite-part or signed-cancellation information tied to the literal normalization. Residue matching alone is not such a proof.
