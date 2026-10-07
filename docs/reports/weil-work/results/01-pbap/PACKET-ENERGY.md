# Narrow integer packets: full-energy growth

Status: full inequality and uniform growth with `N` **Lean-formalized**, with `L>=104`, in `WeilWorkPBAPPacketFourier.lean` and `WeilWorkPBAPPacketEnergy.lean`. Targeted builds, final direct-source checks and twenty axiom audits pass. Verdict: **BRIDGE** to the classical mean-value mechanism, not a scientific novelty claim. This strengthens the antichain-only diagnostic in corpus L353 to arbitrary coefficients in the specific narrow packet family. No integer-null assumption is needed. Full PBAP remains open.

## Exact statement

For integers `N >= 1`, `L >= 105`, put

    beta = narrowBumpC (N*L),
    m = integral |beta|^2,
    x_n = log n - (log N)/2,
    f(x) = sum_{n=1}^N c_n beta(x-x_n),
    S = sum_{n=1}^N |c_n|^2,
    B(N,L) = (1/2) log(1+N*L/4) - 10 - (2/L) sqrt(1+log N).

Then the full pole-plus-gamma functional satisfies

    weilArchRe(f * tilde(f)) >= m*S*B(N,L).

The coefficients are arbitrary complex numbers. The statement includes `S=0` without division. Nonnegative finite mixtures obey the same bound after summing their masses. Thus every mass-one mixture in this packet family has energy tending to positive infinity as `N` tends to infinity, uniformly over `L >= 105` and all coefficient matrices. It also diverges as `L` tends to infinity with `N` fixed. There is no claim about arbitrary compact tests or about a bounded-energy approximation of them.

## Proof

Use the paper Fourier convention `fhat(t)=integral f(x) exp(i*t*x) dx`; changing its sign does not affect the estimates. Let

    r = 1/(4*(N*L+1)),  w = 2*r,  A = integral |beta|.

The literal bump has support in `[-r,r]`, is real and nonnegative, and has positive squared mass `m`. Cauchy–Schwarz on this interval gives `A^2 <= w*m`. Distinct centres have distance at least `1/(N+1)` by the existing integer-log gap bound. Since `2*r < 1/(N+1)`, the translated supports are disjoint; hence `integral |f|^2=m*S`. Plancherel gives `integral |fhat|^2/(2*pi)=m*S`.

Write `P(t)=sum c_n exp(i*t*log n)`. Translation gives `|fhat(t)|=|betahat(t)| |P(t)|`, and `|betahat(t)| <= A`. The source-checked corpus theorem `RHTower.Sieve.dirichlet_meanValue_sharp` bounds the error on `[0,T]` by `104*sum n|c_n|^2` for every real `T`. Put `T=N*L`. Apply the theorem at `T` and `-T`, subtract the oriented integrals, and use `sum n|c_n|^2 <= N*S`. This proves

    integral_{-T}^T |P(t)|^2 dt <= 2*N*(L+104)*S.

Consequently the low-frequency mass obeys

    integral_{-T}^T |fhat(t)|^2 dt/(2*pi)
      <= A^2 * 2*N*(L+104)*S/(2*pi)
      <= m*S * N*(L+104)/(2*pi*(N*L+1))
      <= m*S/2.

The last step uses `pi >= 2`, `L+104 <= 2*L`, and `N*L <= N*L+1`. Thus at least half the spectral mass lies outside `[-N*L,N*L]`, uniformly in every coefficient and every cancellation pattern.

The source-checked theorem `RHTower.log_sub_seven_le_re_digamma_quarter`, together with `gammaBracket_eq` and `log pi <= 3`, gives

    gammaBracket(t) >= log(1+|t|/4)-10.

The logarithm is nonnegative everywhere and at least `log(1+N*L/4)` outside `[-N*L,N*L]`. Integrating against the nonnegative square-transform density therefore bounds the gamma contribution below by

    m*S * ((1/2)*log(1+N*L/4)-10).

All integrals exist: compact smooth tests have square-transform decay sufficient for the corpus's gamma-growth bound. Restricting these integrable functions and splitting the line at `[-N*L,N*L]` is legitimate; endpoints have Lebesgue measure zero.

Retain both pole terms. Put `a_plus=integral beta(x) exp(x/2) dx` and `a_minus=integral beta(x) exp(-x/2) dx`. Both are nonnegative and each is at most `exp(r/2)*A`, so `a_plus*a_minus <= exp(r)*w*m`. The exact pole expression is

    2*a_plus*a_minus * Re[(sum c_n sqrt(n)) conjugate(sum c_n/sqrt(n))].

The common centering cancels between the two factors. Cauchy–Schwarz bounds its absolute value by

    2*exp(r)*w*m*S * sqrt((sum n)*(sum 1/n)).

For `N >= 1`, `sum n=N*(N+1)/2 <= N^2` and `sum 1/n <= 1+log N`. Also `2*w*N=N/(N*L+1) <= 1/L`, while `r <= 1/4` and `exp(1/4)<2`. Hence the signed pole contribution is bounded below by

    -(2/L)*m*S*sqrt(1+log N).

Adding this to the gamma estimate proves the statement. Finally logarithmic growth dominates its square root. Since `2/L <= 2/105`, the lower bound tends to positive infinity uniformly in the permitted resolutions. This last claim is an ordinary real asymptotic, with no spectral or number-theoretic hypothesis.

## What this does and does not establish

The existing realization can approximate torus moments while paying a diverging real-frequency energy cost. Arbitrary signs and divisibility collisions do not remove that cost in this particular construction. Weak prime-torus approximation alone therefore cannot transfer a negative Weil-energy witness from an abstract representing measure.

This does not retire the density/Jensen work: its remaining box-counting, weak-convergence, and explicit Jensen-transfer obligations stay recorded in `TORUS-DENSITY.md`. It does identify why that construction is unsuitable as an energy-preserving approximation. A route to PBAP itself must handle general tests with broad, overlapping support, rather than only this sparse realization.

## Prior-work audit and formal plan

The parent mean-value theorem is classical. [Montgomery's primary survey, sections 5–6](https://www.nato-us.org/analysis2000/papers/montgomery.pdf) gives separated-frequency Hilbert inequalities and their Dirichlet-polynomial mean-square consequence. The proof above deliberately uses the weaker **already formalized constant 104**, not an unverified sharp constant. L353 already uses this spreading mechanism on primitive supports. The present statement's unrestricted coefficients and explicit full-pole error need their own Lean proof; novelty relative to all literature is unestablished.

Deep corpus searches for the exact energy mechanism and the mean-value parent returned partial coverage at 68,367 files. Candidates and source arguments were inspected. The latter located `dirichlet_meanValue_sharp`; direct source inspection located the quarter-point digamma lower bound. Partial retrieval is not evidence that the resulting packet theorem is absent elsewhere.

Implementation order: verify these names in `/tmp`; prove the two-sided mean-square bound and literal packet Fourier factorization; obtain spectral mass outside `[-N*L,N*L]`; prove the full signed pole bound; assemble the displayed unconditional inequality and its uniform divergence. No Lean declaration should accept any of these missing conclusions as a hypothesis. This paper theorem is the next formal target, while full `PrimeBlindPositive` remains the goal.

The initial scratch check `/tmp/wp01-energy-names.lean` verified the cited interfaces and proved the gamma lower bound and two-sided mean-square estimate. The completed leaves now contain the remaining Fourier, low-frequency, gamma and signed-pole arguments.

## Explicit uniform consequence and current formal progress

The same arithmetic permits `L>=104`. The Fourier leaf proves the stronger raw estimate `integral_{-NL}^{NL}|fhat|^2 <= 2*m*S`, together with literal packet mass and Fourier factorization. The energy leaf proves the gamma and signed-pole estimates separately, their full assembly, and the explicit uniform escape statement. All twenty theorem axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`; both final direct-source checks have no diagnostics. Fixed-`N` divergence with `L` remains the elementary paper consequence of the formalized sharp bound; no separate Lean limit theorem is claimed for it.

For `N>=1`, the displayed energy floor is at least `(1/4)*log N-11`, uniformly over `L>=104`. Indeed `log(1+NL/4)>=log N`, `2/L<=1/2`, and `sqrt(1+x)<=1+x/2` for `x>=0`; the last inequality follows by squaring `sqrt(1+x)-1`. Thus the sharper intermediate floor is `(1/4)*log N-10.5`. For any real `E`, choose an integer `K>max(1,exp(4*(E+11)))`. For every `N>=K` and `L>=104`, the full packet energy is at least `E*m*S`, uniformly in every complex coefficient. This proves the stated uniform divergence without choosing coefficients or using a limiting spectral measure. It is an elementary consequence of the same classical parent bound, not a new novelty claim.
