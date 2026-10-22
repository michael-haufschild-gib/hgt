# RP-58: ordered-history transfer through the finite inverse source

Route RP, active hard-frontier trial. RP-57 made no frontier progress.
The target is the unconditional linear floor for the original normalized
matched-minus-quantile history. Positive-damping negative work, signed
high-LCM control, and both history debts remain open.

Current corpus supplies a source-uniform finite inverse construction
p=(c_a+B_a)u+error, with explicit source amplitude and c_a bounded below
by exp(a)/2. Its remainder estimate controls B_a*u. The present task is to
construct and estimate a coefficient-faithful transfer of the actual
ordered-history form, retaining c_a and the terminal boundary. A bounded
transfer through the Xi jet norm is already obstructed on native heads
and is not being assumed.

First inspect the exact moment coordinates and form, then derive the
transformed quadratic including all shift and cross terms. No critical
bound, faithful transfer, or Lean theorem claimed yet.

## Trial 1: retain the three physical moments

Write w_n=Lambda(n)/sqrt(n), m=sum w_n, and c_n for either the actual
matched centroid or its mass-matched quantile centroid. The corpus's
parabolic variance balance identifies the unnormalized paired history as

    Q = [m*sum(w*c_M^2)-(sum(w*c_M))^2]
          -[m*sum(w*c_Q^2)-(sum(w*c_Q))^2].

The equal cell widths cancel the cubic-width contribution exactly.
The required bound is Q >= -B*m*X, X=K+2, not merely o(X^2).

Paper construction, not Lean certified: fix phi=indicator[-1,1]. Put
q_c(t)=sum w_n*c_n*phi(t-2log(c_n)). If
kappa_s=integral phi(u)*exp(s*u) du and L_s(q)=integral exp(s*t)*q(t) dt,
then for s=-1/2,0,1/2 the three moment identities are

    L_-(q)/kappa_- = m,
    L_0(q)/kappa_0 = sum(w*c),
    L_+(q)/kappa_+ = sum(w*c^2).

Thus P(q)=L_-(q)*L_+(q)/(kappa_-*kappa_+)-L_0(q)^2/kappa_0^2
recovers each variance before mass division. This is a faithful moment
encoding, not an identification with the Weil quadratic form. Translation
preserves P and can recenter the support. Its finite-exponential budget
is proportional to sum(w*c); it is not cutoff-independent. The alternative
packet sum(w*phi(t-2log(c))) has budget proportional to m, but uses the
three exponents 0,1/2,1 and the corresponding growing moment readouts.

The existing source-uniform Neumann result gives p=c_a*u+B_a*u+r.
For the symmetric bilinear form J underlying P, exact reconstruction is

    P(p)=c_a^2*P(u)+2*c_a*J(u,B_a*u+r)+P(B_a*u+r).

All three terms must be differenced between the two physical sources.
The inverse norm estimate contains 1/c_a, which is canceled by c_a^2 in
the leading quadratic. The readout J also depends on aperture; treating
it as uniformly bounded loses the original moments. The existing
eventual epsilon estimate for B_a*u does not permit choosing an
aperture-dependent epsilon without controlling its threshold. Even an
o(X^2) error for the physical unnormalized history misses the required
O(X^(3/2)) scale when m is of order sqrt(X). No new lower bound follows.

## Trial 2: the joint adjoint moment action

CCMRestrictedWeilPrimePolarArithmeticAction.lean already gives the exact
prime action on e_+(t)=exp(t/2) and its reflection. With
E(Z)=psi(Z)-Z and R(Z)=sum_(n<=Z) Lambda(n)/n, it is

    Prime_a(e_+)(t)=e_+(t)*(psi(exp(a-t))+R(exp(a+t)))

inside [-a,a]. Removing the opposite exponential main term and the
constant pole component leaves exp(t/2)*(E(exp(a-t))+t+bounded error).
The Chebyshev error is still present; the reciprocal error is already
uniformly bounded in the corpus.

The same literal compressed shifts give, on paper, the constant readout

    Prime_a(1)(t)=M(exp(a+t))+M(exp(a-t)),
    M(Z)=sum_(n<=Z) Lambda(n)/sqrt(n).

Consequently the three-moment action does not close on the three
exponentials: it retains the two linked prime-error profiles E and
M-2sqrt. With alpha the corpus's archimedean scalar and
B_a=alpha*I+Polar_a-Prime_a, direct subtraction gives

    B_a(e_+)(t)=(alpha+a-t-E_rec(a+t))*e_+(t)
                  -exp(-a)*e_-(t)-e_+(t)*E(exp(a-t)),
    B_a(1)(t)=alpha-2*exp(-a/2)*(e_+(t)+e_-(t))
                  -A(exp(a+t))-A(exp(a-t)),

where E_rec(v)=R(exp(v))-v and A(Z)=M(Z)-2sqrt(Z).
The negative exponential equation is obtained by reflection. These
displayed adjoint equations were derived on paper only. They expose
the exact arithmetic terms that a joint estimate must pay; no sign of
their physical pairing was proved.

## Trial 3: keep the hyperbola pairing rather than erase it

Testing E(exp(a-t)) against an ideal prime-centroid packet produces
smoothed sums over products of prime powers. This suggested using the
full Mangoldt convolution before estimating the moments separately.
The corpus already contains the exact required square-cutoff law in
RoutePSecondGradeHyperbolaDebt.lean. With R_n=psi(n)-n,
H_n=sum_(d<=n) Lambda(d)/d-log(n)+gamma, floor remainder F_n, and
second-grade discrepancy D, it reads

    D(n^2)+2*n*R_n+R_n^2+2*F_n
       =2*n^2*H_n+2*sum_(d<=n) Lambda(d)*R_(floor(n^2/d)).

Here 0<=F_n<=psi(n) is paid. The future-error pairing on the right is
not paid. The existing D(N)=o(N) result and the Selberg recursion

    |R_N*log(N)+sum_(d<=N) Lambda(d)*R_(floor(N/d))|<=400*N

do not supply a critical estimate for that pairing. In particular,
applying the recursion at N=n^2 introduces the complementary d>n
range; dropping it would change the identity. No closed inequality
for the original history was obtained in this trial.

## Status

No frontier theorem proved. No Lean source changed or build run; no
identity-only leaf or conditional receiver was added. This does not
retire Route RP or prove an inverse-transfer no-go. The useful retained
calculation is the coefficient-faithful moment transfer and its explicit
joint arithmetic defect. It has paper status only, and does not yet
meet the user's frontier criterion for a new formal module.

Next hard conjecture: the joint future-error pairing, harmonic error,
and second-grade discrepancy admit a signed critical estimate when
transported with the original variance coefficients. Attack this full
combination; neither source-norm smallness nor a one-sided estimate of
only one moment is sufficient. Fixed-positive-damping negative work,
signed high-LCM control, and both history debts remain open.

## Corpus and process audit

Four documented deep searches completed, each with budget 300 seconds,
partial=false, errors=[], and no unfinished stages:

- Ordered-history transfer: query generation 1215431; coverage
  1215449/current 1215450; 65007 files, zero pending files.
- Finite-exponential moments: query generation 1215449; coverage
  1215464/current 1215470; 65007 files, zero pending files.
- Prime-polar joint moments: query generation 1215498; coverage
  1215499/current 1215511; 65007 files, zero pending files.
- Selberg exact convolution: query generation 1215499; coverage
  1215511/current 1215512; 65008 files, zero pending files.

All reported an older coverage snapshot, unavailable/unmeasured semantic
coverage, and incomplete refresh while the background indexer runs.
Compiler coverage remained mostly pending/stale; retrieved candidates
were source-only and not treated as newly audited Lean evidence.
Candidate lemmas, source arguments, proof ideas and ingredient sets
were inspected. The suggested moment-square bounds bound energy from
below, not above. The suggested Selberg transfer uses existing symmetry
and retains its O(N) remainder; unrelated log-remainder suggestions do
not apply. Exact relevant source declarations were read directly.

Owned search sessions 77649, 8110, 45516 and 7258 all exited zero.
Temporary result JSON files were removed after this record. No owned
build or search remains. Goal active; no external blocker. The previously
reported global lint failures were not re-tested without Lean changes.
