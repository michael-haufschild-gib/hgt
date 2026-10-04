# Complete theta tails: quantitative and finite-jet inverse boundary

- **ID:** LI-CLOCK-THETA-TAIL-INVERSE-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [completed-clock sign attempt](../1-in-progress/li-clock-completed-forcing-direct-sign.md)
- **Statement:** Every complete positive coefficient tail of the actual theta kernel has an inverse response positive near zero and negative somewhere. Forcing counterexamples retain any prescribed finite literal input and response jets and all actual quantitative ratio-increment bounds.

## Gates

- [x] Literal source admission, prior research and complete root proof.
- [x] Independent audit of every178 paper line and exact finite-jet extension.
- [x] Exact tail classification and counterinput survivors formalized in Lean.
- [x] Named/direct builds, all-public axioms, complete source review and integration.

## No-go closure

- **Exact killing mechanism:** A globally nonnegative tail inverse would have Laplace mass tending to one with an O(p²) mass deficit. Two genuine monotone-convergence steps force positive mass but zero first moment, contradicting its positive origin interval.
- **Strongest positive survivor:** For every tail index, an exact odd-entire selected-growth inverse and both signs; for every finite literal source jet, a counterinput preserving that jet, the response jet and every actual coefficient-increment lower bound.
- **New insight:** Even finite literal jet matching plus quantitative increasing ratios cannot replace complete source correlation. The counterinputs violate the actual narrow upper ratio band; the exact moment-ratio formula remains untested.
- **Status:** PAPER PASS; Lean CLOSED (see Lean certificate). No negative actual response witness, no RH conclusion and no route retirement.

## Audited complete paper proof [PROVED HERE]

The final178-line root proof below is preserved verbatim from
`/tmp/li_root_theta_tail_inverse_boundary.md`, SHA256
`7c6773ff495e85eb5fd8f6a73c64fad266d8fa1fba449b9356480a04aeed48a6`.
Its pending-audit header is historical. Independent audit
`/tmp/li_producer_theta_tail_inverse_audit.md` (118 lines), SHA256
`4e9de8da76527428e9e2098414c6f9a5e6ad96f98fd2bcb2cddbdcdee999a16d`,
passes every original142 line and exact appended36-line extension. Root
read every audit line. Dependencies are the complete
[theta inverse admission](li-clock-theta-forcing-inverse-boundary.md) and
[actual ratio/history proof](li-clock-theta-source-history-boundary.md).

- 2026-10-01 — Paper audits pass; literal r*g<=g and the complete source band remain open. Exact positive survivor awaits Lean formalization.

# Complete theta coefficient tails and quantitative ratio obstruction

2026-10-01. Root paper argument; independent audit PENDING. Uses the
literal actual K, but constructs other forcings. No actual g or S sign,
RH proof, source replacement, numerical experiment or new premise.

## 1. Fixed source and complete tail inverse

Use final291 theta admission and final251 source-history paper:
/tmp/li_producer_massive_theta_forcing_attack.md,
/tmp/li_producer_theta_resolvent_correlation_attack.md.
Their full audited proofs are preserved in Stage2. In particular

    Phi(z)=sum_(j>=0) nu_j z^(2j)/(2j)!, nu0=1, ALL nu_j>0,
    K(t)=sum_(j>=1) k_j t^(2j-1),
    k_j=nu_j/[(2j)!(2j-1)!]>0,
    r+r*K=K, F+F*K=K+tK'.

K and every fixed derivative have every positive exponential type.
r and every fixed derivative have one strict sub-gamma real exponential
bound, gamma=1/300. The same holds for F by the full squared-copy envelope
and finite-upper-level proof that all actual reciprocal zero rates are
bounded strictly below gamma. All causal products below are integrals
on compact intervals, so associativity is admitted by continuous Fubini.

For every integer J>=1 define the COMPLETE positive coefficient tail

    K_J(t)=sum_(j>=J) k_j t^(2j-1)
          =K(t)-P_J(t),
    P_J(t)=sum_(1<=j<J) k_j t^(2j-1),
    q_J=K_J-r*K_J.

All functions are real odd entire; causal convolution of odd entire
functions is odd entire by its beta-coefficient series, locally absolutely
convergent on every compact complex disk. In particular q_J+q_J*K=K_J
by r+r*K=K. Equivalently

    q_J=r-P_J+r*P_J.                              (1)

Formula(1) gives every fixed real derivative of q_J a strict sub-gamma
exponential bound. Indeed P_J is a finite polynomial and a fixed finite
number of integrations of r suffice; choose a positive rate strictly
between the common rate of r and gamma to absorb polynomial factors.
Alternatively differentiate each compact convolution explicitly with its
finite endpoint terms. No infinite residue expansion is used.

At the origin r(t)=O(t), hence r*K_J=O(t^(2J+1)). Therefore

    q_J(t)=k_J*t^(2J-1)+O(t^(2J+1)),

so q_J is strictly positive on some positive interval. J1 is included:
P_1=0, K_1=K and q_1=r.

## 2. Every complete positive tail has a negative inverse value

Fix J>=1 and suppose q_J>=0 on [0,infinity). Positivity of K and the
causal equation give 0<=q_J<=K_J. Since K_J has every positive exponential
type, q_J and K_J have genuine absolutely convergent Laplace transforms
at EVERY p>0. Tonelli applies to their nonnegative convolution and to the
complete coefficient tail, giving

    Khat(p)=Phi(1/p)-1,
    K_Jhat(p)=Phi(1/p)-Q_J(1/p),
    Q_J(z)=sum_(0<=j<J) nu_j*z^(2j)/(2j)!,
    q_Jhat(p)=1-Q_J(1/p)/Phi(1/p).                 (2)

For 0<p<=1, put C_J=sum_(j<J) nu_j/(2j)!. Then

    0<Q_J(1/p)<=C_J*p^(-2(J-1)),
    Phi(1/p)>=nu_J*p^(-2J)/(2J)!,
    0<Q_J(1/p)/Phi(1/p)<=C_J*(2J)!*p^2/nu_J.       (3)

Thus q_Jhat(p)->1 and (1-q_Jhat(p))/p->0 as p decreases to0.
Monotone convergence first gives integral q_J=1. With that finite mass,

    (1-q_Jhat(p))/p
      =integral_0^infinity [(1-exp(-pt))/p]*q_J(t) dt.

Along a decreasing positive sequence p->0, a second monotone convergence
argument yields integral t*q_J(t)=0. This contradicts the strictly positive
origin interval. Consequently for EVERY J>=1 there is T_J>0 with

    q_J(T_J)<0.                                  (4)

This proof uses sign-implied ALL-p admission, not analytic continuation
of a possibly signed Laplace integral. No zero simplicity or RH assumption.

## 3. Arbitrarily large ratio increments still do not orient the inverse

Let a=g'(0)>0 be the literal massive forcing slope and b=K'(0)=nu1/2>0.
Set A=a/b=alpha1, which the actual source proves greater than8/25.
Fix ANY D>0 and choose ANY J>=2. Define

    f_0(t)=(A-D)*K(t)+(D/2)*(K(t)+t*K'(t)),
    z_0(t)=(A-D)*r(t)+(D/2)*F(t).

The possibly negative scalar A-D is harmless: each complete odd
coefficient of f_0 is [A+D(j-1)]*k_j>0. Its inverse is exactly z_0.
For L>=0 put

    f_L=f_0+L*K_J, z_L=z_0+L*q_J.

Then z_L+z_L*K=f_L and z_L is odd entire with all fixed derivatives in a
strict sub-gamma exponential class. The input is odd entire, has every
positive exponential type, and has ALL strictly positive odd coefficients.
Its coefficient ratio to K at degree2j-1 is exactly

    c_j=A+D(j-1)+L*1_(j>=J).

Thus f_L'(0)=a; c_j>=A; and c_(j+1)-c_j>=D for EVERY j>=1. The only
extra jump is at j=J-1. Strictly increasing pointwise f_L/K follows from
the absolutely admitted positive double-series calculation in final251.
In particular every input satisfies f_L>=A*K>K/4 on positive clocks.

Choose T_J from(4) and take a finite L>=0 sufficiently large that
z_0(T_J)+L*q_J(T_J)<0. This gives a genuine negative inverse value while
preserving the exact actual initial slope and the prescribed uniform
increment lower bound D. Taking D>6047/22725 strictly retains the numerical
increment bound established for the literal g.

The result holds for each J>=2: the added perturbation leaves the first
J-1 odd coefficients of the baseline input unchanged. It does NOT claim
to match these coefficients to those of the actual g, except the slope.

## 4. Exact surviving source information and limits

This rules out an inference from the actual slope, positive odd coefficients,
strictly increasing forcing/kernel ratio, any specified positive lower
increment bound, and strict selected growth alone. Every coefficient tail
inverse having a negative witness is the positive classification exposed
by the obstruction. No route is retired before this exact theorem is
formalized.

The counter-input does NOT retain the actual ratio band

    2j*omega^2+nu1-49/909 <= alpha_j < 2j*omega^2+nu1,
    alpha_j=2j*omega^2+nu1-nu_(j+1)/[(2j+1)*nu_j].

In particular a large step L may violate its upper bound. These full actual
ratios and their interdependence remain available; no negative response
for the literal g=-J_S' is claimed. The missing actual inequality remains
r*g<=g at every positive clock. No conclusion on RH follows here.

## 5. Every finite literal source jet can also be retained

The same complete-tail construction gives a sharper statement about the
actual forcing. Fix ANY J>=2 and define, with L>=0,

    f_L=g+L*K_J, y_L=(-S)+L*q_J.

The exact actual equation (-S)+(-S)*K=g and the tail equation give
y_L+y_L*K=f_L. ALL first J-1 odd input coefficients match the literal g;
ALL first J-1 odd response coefficients match the literal -S, by the
proved origin order of q_J. The exact actual slope is retained. The full
input coefficient ratios are alpha_j+L*1_(j>=J), so every actual strict
increment lower bound >6047/22725 survives, with only one additional
positive jump. All positive odd coefficients, coefficient floor and
strictly increasing pointwise input/K ratio are retained.

The selected growth class remains genuine. Choose d<gamma bounding ALL
actual |Im w_q| using the finite-positive-upper-level argument. On real
clocks the complete first and higher derivative sums have weights at
most |w_q|² since |w_q|<1. Their norms are at most A0*exp(d*|t|), where
A0=sum_q |w_q|²<infinity. Full locally uniform complex square-mass bounds
admit every fixed derivative before that real estimate. F itself has the
extra |t| factor, absorbed by any fixed rate strictly between d and gamma.
Thus -S=omega²F-F'' and every fixed derivative have a common strict
sub-gamma real exponential rate; combine it with the rate of q_J.

Take T_J from(4), then choose finite L>=0 large enough that
(-S)(T_J)+L*q_J(T_J)<0. The resulting inverse has a negative value while
retaining any preassigned finite odd jet of the literal input and response,
and ALL of the quantitative increment inequalities. This is an unconditional
construction; no sign of the actual -S at T_J has been assumed.

It still does NOT preserve the exact upper band or moment-ratio formula:
if L>49/909, EVERY j>=J satisfies alpha_j+L>2j*omega²+nu1. Consequently this
stronger finite-jet obstruction does not decide the literal comparison.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.LiClockThetaTailInverse`, `GaloisForLFunctions.RHTower.LiClockThetaTailCounterInput`, `GaloisForLFunctions.RHTower.LiClockThetaInverseClass`, `GaloisForLFunctions.RHTower.LiClockThetaForcingRatioShape`, `GaloisForLFunctions.RHTower.LiClockThetaForcingHistoryMajorant`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange`, `GaloisForLFunctions.HTGeometry.BorelSeriesSmoothRatio`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the umbrellas):
`GaloisForLFunctions.RHTower.LiClockThetaTailInverse`, `GaloisForLFunctions.RHTower.LiClockThetaTailCounterInput` (new), on the theta inverse stack `GaloisForLFunctions.RHTower.LiClockThetaInverseClass`, `GaloisForLFunctions.RHTower.LiClockThetaForcingRatioShape`, `GaloisForLFunctions.RHTower.LiClockThetaForcingHistoryMajorant`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange`, `GaloisForLFunctions.HTGeometry.BorelSeriesSmoothRatio`.

Indexing: the card's tail `K_J` (`J ≥ 1`) is `liClockThetaKernelTail n` with `J = n+1`; its inverse `q_J` is `liClockThetaTailInverse n`; `k_j t^{2j-1} = c_j t^{2j-1}/(2j-1)!`.

| Claim | Declaration |
|-|-|
| §1 complete tails `K_J`, odd polynomial head `P_J`, `K=P_J+K_J`; `K_1=K`, `q_1=r` | `liClockThetaKernelTail`, `liClockThetaKernelHead`, `liClockThetaKernel_eq_head_add_tail`, `liClockThetaKernelTail_zero`, `liClockThetaTailInverse_zero` |
| `q_J=K_J−r⋆K_J`, `q_J+q_J⋆K=K_J`; (1) `q_J=r−P_J+r⋆P_J` | `liClockThetaTailInverse`, `liClockThetaTailInverse_volterra`, `liClockThetaTailInverse_eq` |
| every fixed derivative of `q_J` in a strict sub-`1/300` class; `K_J` every positive exponential type | `liClockSubGammaClass_liClockThetaTailInverse`, `liClockEveryExpType_liClockThetaKernelTail` |
| `q_J` odd entire with explicit coefficients; `q_J(t)=k_J t^{2J−1}+O(t^{2J+1})`; vanishing to order `2J−1`; positive on an origin interval | `liClockThetaTailInverse_eq_oddFactorialSeries`, `liClockThetaTailInverseCoeff_eq_zero`, `liClockThetaTailInverseCoeff_self`, `abs_liClockThetaTailInverse_sub_le`, `iteratedDeriv_liClockThetaTailInverse_zero`, `exists_liClockThetaTailInverse_pos` |
| §2 (2)–(3) under `q_J≥0`: `q_J≤K_J`, all-`p` admission, `K̂_J=Σ_{j≥J}c_jp^{−2j}`, `1−q̂_J=Q_J(1/p)/Φ(1/p)≤C_J p²/c_J` (inside the proof) | `hasSum_integral_Ioi_liClockThetaKernelTail`, `exists_liClockThetaTailInverse_neg` (proof), `false_of_laplace_deficit` |
| (4) for every `J≥1` some `T_J>0` has `q_J(T_J)<0` | `exists_liClockThetaTailInverse_neg` |
| §3 ramp inputs `f_L=(A−D)K+(D/2)(K+tK')+L K_J`, inverse `z_L=(A−D)r+(D/2)F+L q_J`; coefficients `(A+D(j−1)+L·1_{j≥J})k_j>0`; ratios `≥A`, increments `≥D`; `f_L/K` strictly increasing; `f_L≥AK`; slope `A K'(0)`; `z_L` in the class | `liClockThetaRampResponse_volterra`, `liClockThetaRampInput_eq_oddFactorialSeries`, `liClockThetaRampCoeff_div`, `liClockThetaRampCoeff_pos`, `liClockThetaRampRatio_ge`, `liClockThetaRampRatio_increment`, `liClockThetaRampInput_div_kernel_strictMonoOn`, `liClockThetaRampInput_ge`, `hasDerivAt_liClockThetaRampInput_zero`, `liClockSubGammaClass_liClockThetaRampResponse` |
| with `A=α₁` (slope `g'(0)`, `α₁>8/25`) and any `D>0`, `J≥2`: a finite `L≥0` makes `z_L(T_J)<0` | `exists_liClockThetaRampCounterInput`, `eight_div_twentyFive_lt_liClockThetaForcingRatio_one` |
| §5 jet inputs `f_L=g+L K_J`, `y_L=−S+L q_J`, `y_L+y_L⋆K=f_L`; first `J−1` odd input coefficients and slope of `g` kept; response jets of order `<2J−1` equal those of `−S`; ratios `α_j+L·1_{j≥J}`, increments `>6047/22725`; positive coefficients; strictly increasing `f_L/K`; class; negative value | `liClockThetaJetResponse_volterra`, `liClockThetaJetCoeff_of_lt`, `hasDerivAt_liClockThetaJetInput_zero`, `iteratedDeriv_liClockThetaJetResponse_zero`, `liClockThetaJetCoeff_div`, `liClockThetaJetRatio_increment`, `liClockThetaJetCoeff_pos`, `liClockThetaJetInput_div_kernel_strictMonoOn`, `liClockSubGammaClass_liClockThetaJetResponse`, `exists_liClockThetaJetCounterInput` |
| `−S` (hence `y_L`) in the strict sub-`1/300` class | `liClockSubGammaClass_neg_liEvenCrossActualClockMassiveSource` |
| the step leaves the band: `L>49/909` ⇒ `α_j+L>2jω²+ν₁` for every `j≥J` | `liClockThetaJetRatio_gt_band` |

Proof-route note: the sign change (4) is derived from the Laplace deficit `0≤1−q̂_J(p)≤Cp²` against the positive origin interval (`false_of_laplace_deficit`), in place of the two monotone-convergence steps; the conclusion is the card's.

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
