# Gamma-mode truncation on the exact exposing ray

Status: FORMALIZED in WeilWorkExposingRayGammaTruncation.lean; final installed
leaf and all ten public theorem axiom audits passed.
Universal WP02 remains OPEN. This prices an omitted positive contribution;
it does not prove the sign of the complete energy.

## Exact proposed result

Write gamma(t)=archimedeanWeilSymbol(t/(2*pi)), gamma0=gamma(0), and

    b_j(t) = t^2 / ((j+1/4)*(4*(j+1/4)^2+t^2)),
    gamma_K(t) = gamma0 + sum_(0<=j<K) b_j(t),
    E_K(f) = integral |paperFT(f,t)|^2 gamma_K(t) dt,
    R(f) = integral |paperFT(f,t)|^2 t^2/(1+t^2) dt.

There are d>0 and N0, depending only on the literal exposing weights, such
that EVERY finite nonnegative family of actual compact polar C2 sources
matching t*w_N at every integer, t>=0 and N>=N0, satisfies

    sum_i alpha_i R(f_i) >= 32*d*t,
    sum_i alpha_i (archEnergy(f_i)-E_K(f_i)) >= d*t/K^2    (K>=1).

The first inequality is the positive survivor: exact ray data forces a
fixed amount of the bounded frequency moment R, with no aperture, row-count,
or source-representation premise. It follows from two fixed ray samples,
not from an assumed limiting spectral density.

The floor statements also hold for every real t: when t<0 their left sides
are nonpositive and their right sides nonnegative. The formal statements
retain this harmless extension; it introduces no stronger signed-energy claim.

Stronger adaptive consequence: there is one C>=0 such that, for every
0<r<exposingWeightDecayRate/2, there are arbitrarily large
(indeed all sufficiently large) N and
actual exact unit-ray matched families at apertures <=log(N)/2+C such that
on the SAME family, for EVERY choice of natural K_i satisfying
1<=K_i<=exp(r*N),

    sum_i alpha_i E_(K_i)(f_i) < T-tau_N.

Thus bare positive gamma-mode truncation below this exponential scale
cannot certify the required threshold. This does not exclude a certificate
that retains an analytic lower bound for the omitted modes. K_i is a mode
index, not a real-frequency cutoff or Galerkin dimension.

## 1. Literal series and its positive remainder

The corpus theorem `hasSum_digamma_sub`, applied at 1/4 and 1/4+i*t/2,
and `re_one_div_vertical` give

    gamma(t)-gamma0 = sum_(j>=0) b_j(t).

Every term is nonnegative. The series converges for every real t; for j>=1
its term is at most t^2/(4*j^3). No asymptotic replacement of gamma is used.

For K>=1 retain only j=K,...,2K-1 in the omitted tail. For these indices,
0<j+1/4<=2K and 4*(j+1/4)^2<=16K^2, hence

    b_j(t) >= t^2/(2*K*(16*K^2+t^2)).

There are exactly K such indices. Consequently

    gamma(t)-gamma_K(t)
      >= t^2/(2*(16*K^2+t^2))
      >= (1/(32*K^2))*t^2/(1+t^2).

The second comparison follows from K^2>=1. It includes t=0, where both
sides vanish. The remainder is nonnegative for K=0 as well, but the displayed
reciprocal bound is asserted only for K>=1.

## 2. All integrals and the source estimate

For an actual compact C2 source, its squared transform is integrable, and
its product with gamma is integrable by the existing Weil-form API. Also
0<=b_j(t)<=1/(j+1/4), so every finite-mode energy is integrable. The bounded
moment t^2/(1+t^2) lies in [0,1], making R finite. Multiplication of the
pointwise remainder bound by the nonnegative squared transform, followed
by integration, gives

    archEnergy(f)-E_K(f) >= R(f)/(32*K^2).

This holds for all compact C2 sources, whether polar or not. No exchange of
an infinite series with a signed integral is required.

## 3. A fixed two-sample coercivity law

For all real u,v,t set C(u,v)=4+u^2+v^2. Then

    |cos(t*u)-cos(t*v)| <= C(u,v)*t^2/(1+t^2).

If |t|<=1, use |cos(t*u)-cos(t*v)| <=
(1-cos(t*u))+(1-cos(t*v)) <= (u^2+v^2)*t^2/2 and 1+t^2<=2.
If |t|>=1, use the bound 2<=4*t^2/(1+t^2).

The exact cosine-transform identity in `WeilSymbolMertensExpansion` gives

    integral |paperFT(f,t)|^2 cos(t*log n) dt = pi*atomCoeff(f,n).

After subtracting, integrating the absolute bound and summing with alpha_i>=0,
any finite family satisfies

    pi*|sum_i alpha_i*(atomCoeff(f_i,a)-atomCoeff(f_i,b))|
      <= C(log a,log b)*sum_i alpha_i R(f_i).

The exposing weights are eventually strictly positive and tend to zero,
the latter following directly from their proved exponential upper bound.
Choose a>=2 with w(a)>0, then b>=a with w(b)<w(a)/2. Fix these choices
once and for all. Put Delta=w(a)-w(b)>0, C0=C(log a,log b)>0 and

    d = Delta/(64*C0) > 0,       N0=b.

For N>=N0, matching at a and b gives exactly

    pi*sum_i alpha_i*(atomCoeff(f_i,a)-atomCoeff(f_i,b)) = t*Delta/2.

For t>=0 its absolute value is t*Delta/2. Divide the previous inequality
by C0 to obtain sum alpha_i R(f_i)>=t*Delta/(2*C0)=32*d*t.
Combining with section2 gives the asserted d*t/K^2 remainder floor.
The t=0 case remains included; no strictly positive mass assumption was
inserted into the family definition.

## 4. Adaptive exponential complexity boundary

Use the already-proved exact families in `ExposingRayMass.near_threshold_mass`:
apertures <=log(N)/2+C, every integer trace w_N, nonnegative coefficients,
and E=sum alpha_i archEnergy(f_i)<=T+2*tau_N. Their additional physical
mass floor is unnecessary for this argument.

Fix 0<r<kappa/2, kappa=exposingWeightDecayRate. Choose 2r<s<kappa.
The proved tail theorem gives B>0 with tau_N<=B*exp(-s*N). For every
assignment 1<=K_i<=exp(r*N), section2 implies

    sum_i alpha_i (archEnergy(f_i)-E_(K_i)(f_i))
      >= exp(-2*r*N)/32 * sum_i alpha_i R(f_i)
      >= d*exp(-2*r*N).

Since s-2r>0, eventually 3*B*exp(-s*N)<d*exp(-2*r*N). Enlarge N0 to
include this and the exact-family threshold. Then

    sum_i alpha_i E_(K_i)(f_i)
      <= T+2*tau_N-d*exp(-2*r*N)
      < T-tau_N.

This is uniform in the row-dependent mode choices, which are quantified
after the family is chosen. Increasing C if necessary to be nonnegative
also gives N<=floor(exp(2*(log(N)/2+C))) for N>=1. Every receiver-level
condition and the complete zero atom tail are retained.

Scope audit during formalization: C is taken directly from the fixed
near-threshold realization theorem, before r is chosen. Thus the same C
works for every subcritical r; only the eventual threshold depends on r.
The extension to t<0 and this quantifier ordering follow from the displayed
proof, were checked on paper, and carry no separate scientific novelty claim.

## Hostile and parent audit

The positive digamma expansion is classical; [DLMF 5.7](https://dlmf.nist.gov/5.7)
and the corpus already provide it. The scalar inverse-square remainder is
an elementary consequence, not a novelty claim. The proposed additional
content is the actual-ray, two-fixed-sample floor and its uniform exclusion
of adaptive rowwise truncations at exponential mode budgets on the same
exact compact matched families.

The current [finite Guinand--Weil tail paper](https://arxiv.org/html/2607.02828v3)
studies a different archimedean cutoff and finite Galerkin setting. Its
tail-order and certification discussion is relevant ancestry, not a proof
of this statement. No numerical result from it is used. The exact corpus
search was partial (semantic retrieval deadline); its returned entries and
source bodies were checked. Absence from that search is not a novelty proof.

Verdict: BRIDGE with a quantitative method boundary; no claim of significant
new scientific knowledge yet. It improves the scope of the earlier fixed
primitive-surrogate obstruction but does not settle the signed producer.
The lower remainder floor must be formalized together with the negative
truncation result before this restricted method is labelled formally closed.
No estimate on the remaining signed finite core has been proved here.
