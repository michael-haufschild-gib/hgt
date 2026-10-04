# Actual theta forcing ratios and history comparison boundary

- **ID:** LI-CLOCK-THETA-SOURCE-HISTORY-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [completed-clock sign attempt](../1-in-progress/li-clock-completed-forcing-direct-sign.md)
- **Statement:** Actual forcing g has quantitatively increasing coefficient ratios and strictly increasing g/K, but the two source majorants (g*K)/g and (g*K')/g' are unbounded above cofinally, despite exact positive-origin comparison intervals.

## Gates

- [x] Complete literal source proof, all-p positive Laplace admission and full author/root audits.
- [x] Exact positive survivor formalization, named/direct builds and all-public axiom checks.
- [x] Complete independent Lean source review and integration.

## No-go closure

- **Exact killing mechanism:** Replacing nonnegative actual history y=-S by y<=g cannot give either global finite-factor history bound: genuine Laplace products would force Phi(1/p)-1 bounded for all p>0.
- **Strongest positive survivor:** Actual coefficient increments exceed 6047/22725; g/K is strictly increasing; exact origin ratios are nu_1*t^2/12 and nu_1*t^2/4 to leading order, while each ratio is cofinally unbounded.
- **New insight:** Actual history correlation is necessary. A separate inverse counterexample retains the initial slope and qualitative increasing ratios, but does not preserve the actual quantitative increment bound or full source ratios.
- **Status:** PAPER PASS; Lean CLOSED (see Lean certificate). No blanket exclusion of first-crossing methods, no route retirement and no negative actual S/F witness.

## Audited paper proof [PROVED HERE]

Final251 below is preserved verbatim: `/tmp/li_producer_theta_resolvent_correlation_attack.md`, SHA256 `b79dd871b01daa9fd9c640c3c01fab4094eab1f907a6d5ec0620d9004c08eda9`. Root read all248 original lines and the three-line quantitative-scope guard, checking every coefficient, endpoint, inverse construction and all-p/cofinal argument. The complete [theta forcing and inverse admission](li-clock-theta-forcing-inverse-boundary.md) is the dependency, not an extra sign premise.

- 2026-10-01 — Full paper audits pass. Literal source comparison remains open; formalization required before no-go closure.

# Actual theta resolvent correlation: source comparison attempt

2026-10-01. READ-ONLY source/paper audit. No Lean, compiler, numerical job,
tree/card edit or agent. Author PAPER PASS on statements proved below;
the literal global r*g<=g comparison and S<=0 remain OPEN. No RH conclusion.

## 1. Exact source and inherited admissions

Use precisely the Stage2 packet
/tmp/li_producer_massive_theta_forcing_attack.md, FINAL291 lines,
SHA f7f219376559c6411960d839726a9c6ade09bbab81b1cb83426065f077f05cc2.
No new kernel, normalization or finite-source substitution is introduced:

    nu_j=thetaCuspRawEvenMoment j/thetaCuspRawEvenMoment0,
    nu0=1, nu_j>0 ALLj, nu1=M0,
    Phi(z)=XiC(-I*z)/XiC0=sum_j nu_j z^(2j)/(2j)!,
    B(t)=sum_j nu_j t^(2j)/((2j)!)², K=B',
    F=liEvenCrossActualClockResponse,
    S=F''-omega²F, omega²=c0-M0>4/25.

The full actual source-score inequality is
303nu_(j+1)<=(32j+17)nu_j. All kernel derivatives and forcing derivatives
are entire and compact absolutely/uniformly admitted. All positive-clock
causal convolution integrands are genuinely L1 on compact triangles.
The banked single-Xi law is F*B=tB'; its factor is ONE.

Define EXACTLY

    J_S=S*B=tB'''+2B''-omega²tB'-M0B,
    g=-J_S', y=-S.

Then the complete actual causal equation is

    y+y*K=g, y0=g0=0,
    g>0, g'>0 on positive clocks,
    y=g-r*g, r+r*K=K, r=-u''.

The genuine r is odd entire with all fixed derivatives in a strict
exp(delta|t|) class, delta<1/300. It has positive and negative values.
These are proved actual-source admissions, not assumptions of inverse
positivity or of S's sign. The norm/source definitions are literal single
R0 normalization; no mixed ZA²ZU² normalizer is used.

Primary source spot-check here: BorelSource19-46 has literal B/term,
all-j nu positivity and nu0; Volterra78-113 has the literal F and complete
factorial series; CumulantMinor443-486 proves
M0=nu1 and M1=nu1²/2-nu2/6. The exact installed M1>0 proof was read at
XiThermalSourceRelativeGapBound427-430, using its actual thermal second
moment lower bound. No higher logarithmic cumulant sign is assumed.
The omega bound is /tmp/li_root_massive_completion_comparison_attack.md.

## 2. Actual forcing's stronger ratio structure is independently closed

Write the COMPLETE positive odd kernel terms as

    K(t)=sum_(j>=1) k_j t^(2j-1),
    k_j=nu_j/((2j)!*(2j-1)!)>0.

The actual g coefficient at this SAME degree has ratio

    alpha_j=2j omega²+M0-delta_j,
    delta_j=nu_(j+1)/[(2j+1)nu_j]>0.                (1)

No degree or factorial is changed. The source-score recurrence proves

    0<delta_j<=16/303+1/[303(2j+1)]<=49/909, j>=1.

Consequently, retaining BOTH positive moment ratios,

    alpha_(j+1)-alpha_j
      =2omega²+delta_j-delta_(j+1)
      >2omega²-49/909
      >6047/22725>0.                              (2)

Thus actual g/K coefficients are strictly increasing, with a uniform
positive increment. The origin ratio is also exact:

    alpha1=2omega²+2M1/M0>2omega²>8/25.

Here M0>0, M1>0 are actual source theorems. This confirms only the FIRST
Gaussian-normalized moment contraction delta1<M0. It does not silently
assert delta_j<=M0 at every order.

Compact absolute product/derivative admission from section1 permits the
full double-series identity, with m_j=2j-1:

    g'K-gK'
      =sum_(i<j)(alpha_j-alpha_i)(m_j-m_i)k_i k_j
         t^(m_i+m_j-1)>0, t>0.                    (3)

Every summand is nonnegative, and the i1,j2 term is strictly positive.
Hence the literal pointwise ratio g(t)/K(t) is strictly increasing on
(0,infinity). This is an actual source-positive survivor beyond positivity
of forcing coefficients. It is not yet the signed history comparison.

Tested route: increasing coefficient ratios or increasing g/K, even with
the actual origin slope and forcing>K/4, would orient this actual inverse.
That generic inference is FALSE. Let h=K+tK'. Differentiating the banked
F*B=tK with B0=1 gives F+F*K=h. Since every k_j>0,
h's coefficient ratio to K is 2j. For any epsilon>0, K+epsilon*h has
strictly increasing ratios 1+2j epsilon. Their pointwise ratio is
1+epsilon[1+tK'/K], strictly increasing: tK'/K is the positive power-series
weighted degree average, whose log-t derivative is its strict variance.
All double sums are absolutely admitted before this calculation.

Pick a genuine negative r witness T. Choose epsilon>0 sufficiently small
that r(T)+epsilon F(T)<0. The response to K+epsilon*h is exactly
r+epsilon F. Set a=g'(0)>0,b=K'(0)=M0/2 and rescale by
A=a/[b(1+2epsilon)]>0. The resulting input has EXACT actual g'(0),
strictly increasing coefficient/pointwise ratios, and coefficient floor
>=alpha1*K>K/4, but its genuine response remains negative at T.
This changes higher input coefficients; it is not a negative witness for
the particular g or S. It need not preserve the actual uniform increment
>6047/22725 in(2); that quantitative constraint and the full moment-ratio
formula remain untested by this counterexample. The true F also belongs
to a strict sub-gamma real
class: the same finite-upper-level zero argument bounds ALL |Im w_q|
by d<gamma, then the full squared-copy sine envelope gives
|F(t)|<=A0|t|exp(d|t|)<=C_delta exp(delta|t|), d<delta<gamma.
Thus the counter-input does not escape the selected real growth class.

## 3. Exact particular-g first-crossing comparison tested

Suppose y is nonnegative before its first positive zero T. On [0,T],
K>=0 gives 0<=y<=g. At the zero, the COMPLETE causal laws give

    g(T)=(y*K)(T),
    y'(T)=g'(T)-(y*K')(T).                         (4)

The derivative retains y0=0. Therefore two natural purely source-level
majorants that would exclude a first crossing are

    g*K<g, or g*K'<g', on all positive clocks.      (5)

Strict inequality avoids tangential-zero issues in that sufficient
argument. The weakened uniform-finite-factor versions of BOTH (5) are
also FALSE for the PARTICULAR literal actual g, not just a proxy input.

Precise unconditional source statements:

    for every A>0 and T>=0, exists t>T:
        (g*K)(t)>A*g(t),
    for every A>0 and T>=0, exists t>T:
        (g*K')(t)>A*g'(t).                         (6)

Thus replacing the history y by its bare upper bound g cannot close this
first-crossing argument on an unbounded clock range. This does not exclude
first-crossing estimates retaining additional information about y.

## 4. Genuine all-p proof of the source obstruction

For EVERY epsilon>0 and fixed derivative order m, Cauchy for the entire
ordinary Phi at radius1/epsilon gives

    |B^(m)(z)|<=M_epsilon epsilon^m exp(epsilon|z|).

Since g is an explicit polynomial-in-t combination of fixed B derivatives,
g and g' have every-positive exponential type as well (absorb the finite
t factor using a smaller exponent). K,K' and both convolutions in(6)
are genuinely Laplace L1 at EVERY p>0: choose epsilon<p, bound compact
convolution by a constant times t exp(epsilon t), and integrate. This is
an unconditional positive-function admission; no all-p transform of
signed F,S or r is invoked.

Put Ghat(p)=integral_0^infinity exp(-pt)g(t)dt. Then Ghat(p)>0, because
g>0 on all positive clocks. Complete nonnegative factorial-series Tonelli
and integral of each monomial give

    Khat(p)=Phi(1/p)-1,
    K'hat(p)=p*Khat(p), g'hat(p)=p*Ghat(p).         (7)

Derivative integration by parts is legitimate: the preceding genuine
L1 bounds apply to functions and derivatives, g0=K0=0, and their
exp(-pt)-weighted endpoints tend to0. Positive convolution Tonelli yields

    (g*K)hat=Ghat*Khat,
    (g*K')hat=Ghat*p*Khat.                         (8)

If g*K<=A*g held globally for any finite A, canceling Ghat(p)>0 in(8)
would force Khat(p)<=A for EVERY p>0. The same conclusion follows from
any global g*K'<=A*g', canceling pGhat(p)>0. But actual nu1>0 gives

    Khat(p)=Phi(1/p)-1>=nu1/(2p²),                 (9)

which is unbounded as p decreases to0. Both global bounds are impossible.
This argument preserves full Phi and ALL factorial terms; no degree
truncation or analytic continuation of a signed Laplace transform occurs.

To strengthen global failure to the exact COFINAL form(6), the ratios are
continuous on (0,infinity), with strictly positive denominators. Section5
supplies a finite continuous limit at0. Each ratio is bounded on every
compact [0,T]. If it were bounded by A after any T, combining that bound
with the compact maximum would give a forbidden global finite bound.
This proves(6), without asserting eventual divergence or a specific
negative actual response.

## 5. Sharp origin boundary: these comparisons DO hold locally

The exact actual origin coefficients are

    a=g'(0)=omega²M0+M1>0,
    b=K'(0)=nu1/2=M0/2>0.

Consequently g(t)=a*t+O(t³), K(t)=b*t+O(t³),
g'(t)=a+O(t²), K'(t)=b+O(t²). Genuine compact Taylor/Fubini gives

    (g*K)(t)=ab*t³/6+O(t⁵),
    (g*K')(t)=ab*t²/2+O(t⁴).

On RIGHT-HAND or punctured-positive limits, therefore,

    (g*K)(t)/g(t)=nu1*t²/12+O(t⁴),
    (g*K')(t)/g'(t)=nu1*t²/4+O(t⁴).                (10)

Each ratio has continuous extension0 at0. Both strict comparisons in(5)
hold on some true positive origin interval. These exact coefficients,
together with cofinal unboundedness, are the strongest boundary exposed
by the tested source majorant. An ordinary totalized quotient at0 is not
used to assert the nonzero leading coefficient of the ratio/t².

## 6. Actual source correlation remains the missing step

The exact particular g is unchanged throughout(1)-(10). Its every odd
coefficient, true R0, omega², full reciprocal phase and all-copy source
must be retained. The remaining proof burden is not positivity of g,
its increasing ratios or the failed uniform history majorants. One must
independently bound the weighted ACTUAL history y in(4), or the signed
resolvent history r*g, sharply enough to prove y>=0. No such all-clock
bound is supplied here. Restating r*g<=g alone is another receiver.

The stronger all-order assertion nu_(j+1)<=(2j+1)M0nu_j was checked as a
possible input-shape route, not adopted. Only its j1 instance follows
here from exact M1>0; the source-score recurrence alone gives the different
49/909 fence. Source overlap checked: PrimeArchThetaQuarticRatioGate ALL73
lines defines a supplied Prop and its conditional cubic/Hankel consumers;
it is not an unconditional all-order Gaussian ratio theorem. Relevant
PrimeArchThetaGaussianApertureCurvatureFlow1270-1315,1380-1537,1538-1598
were read: the actual forward barrier explicitly requires next-degree
nonnegative curvature. Neither source may silently close the missing
history admission. Root separately checked the returned half-moment
ratio hit; it uses M_k/[k M_(k-1)], not the even (2j+1) ratio above.
No exhaustive absence or novelty claim is made from these inspected hits.

Prior search is reused from the frozen291 packet and the existing root
ratio/first-crossing research. No new topic query or unavailable compiler
claim is inferred. PAPER PASS on exact actual increasing ratios, same-
kernel guarded inverse shape obstruction, all-p source majorant failure,
cofinal and sharp-origin boundary. Literal all-t S<=0 and the original
finite-eta growing-window sign remain OPEN. No route retirement, no
positive inverse, no unconditional actual negative S witness, no RH
proof/falsification or stronger converse.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.BorelSeriesSmoothRatio`, `GaloisForLFunctions.RHTower.LiClockThetaInverseClass`, `GaloisForLFunctions.RHTower.LiClockThetaForcingRatioShape`, `GaloisForLFunctions.RHTower.LiClockThetaForcingHistoryMajorant`, `GaloisForLFunctions.RHTower.LiClockThetaMassiveForcing`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignedMass`, `GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor`, `GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound`, `GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the umbrellas):
`GaloisForLFunctions.HTGeometry.BorelSeriesSmoothRatio`, `GaloisForLFunctions.RHTower.LiClockThetaInverseClass`, `GaloisForLFunctions.RHTower.LiClockThetaForcingRatioShape`, `GaloisForLFunctions.RHTower.LiClockThetaForcingHistoryMajorant` (all new), on top of the theta inverse stack `GaloisForLFunctions.RHTower.LiClockThetaMassiveForcing`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignedMass`; installed inputs `GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor` (`M₀=ν₁`, `M₁=ν₁²/2−ν₂/6`), `GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound` (`M₁>0`), `GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence`.

| Claim | Declaration |
|-|-|
| §1 `y=−S`: `y+y⋆K=g`, `y(0)=g(0)=0`, `y=g−r⋆g`; `g>0`, `g'>0` on positive clocks (`g'>0` everywhere) | `neg_liEvenCrossActualClockMassiveSource_volterra`, `liEvenCrossActualClockMassiveSource_zero`, `liClockThetaForcingInput_zero`, `neg_liEvenCrossActualClockMassiveSource_eq`, `liClockThetaForcingInput_pos`, `liClockThetaForcingInputDeriv_pos`, `hasDerivAt_liClockThetaForcingInput` |
| `r` odd entire, all derivatives in a strict `e^{δ|t|}` class, `δ<1/300`, with positive and negative values | `exists_liClockThetaResolvent_iteratedDeriv_growth`, `exists_liClockThetaResolvent_pos`, `exists_liClockThetaResolvent_neg` |
| §2 (1) `α_j=2jω²+M₀−δ_j`, `δ_j=ν_{j+1}/((2j+1)ν_j)`; `−e_j=α_j c_j` | `liClockThetaForcingRatio`, `liClockThetaMomentRatio`, `neg_liClockThetaForcingTaylorCoeff_eq`, `liClockThetaForcingInput_coeff_ratio` |
| `0<δ_j≤16/303+1/(303(2j+1))≤49/909` (`j≥1`) | `liClockThetaMomentRatio_pos`, `liClockThetaMomentRatio_le`, `liClockThetaMomentRatio_le_of_one_le` |
| (2) `α_{j+1}−α_j=2ω²+δ_j−δ_{j+1}>6047/22725`; strictly increasing ratios | `liClockThetaForcingRatio_succ_sub`, `liClockThetaForcingRatio_increment_gt`, `liClockThetaForcingRatio_strictMono` |
| `α₁=2ω²+2M₁/M₀>8/25` | `liClockThetaForcingRatio_one`, `eight_div_twentyFive_lt_liClockThetaForcingRatio_one` |
| (3) `g'K−gK'>0` on positive clocks; `g/K` strictly increasing on `(0,∞)` (antisymmetrized double series) | `liClockThetaForcingInput_deriv_cross_pos`, `liClockThetaForcingInput_div_kernel_strictMonoOn`, `oddFactorialSeries_deriv_cross_pos`, `oddFactorialSeries_ratio_strictMono`, `powerSeries_ratio_strictMono` |
| Tested route fails: `h=K+tK'`, `F+F⋆K=h`; input `A(K+εh)` with exact slope `g'(0)`, ratios `A(1+2jε)`, strictly increasing `I/K`, floor `α₁K>K/4`, response `A(r+εF)` in the strict sub-`1/300` class and negative at a positive clock | `liEvenCrossActualClockResponse_volterra_kernel`, `liClockThetaClockInput_eq_oddFactorialSeries`, `liClockThetaShapeResponse_volterra`, `liClockThetaShapeInput_coeff_ratio`, `liClockThetaShapeInput_div_kernel_strictMonoOn`, `liClockThetaShapeInput_ge`, `liClockSubGammaClass_liClockThetaShapeResponse`, `exists_liClockThetaShapeCounterInput` |
| `F` itself (and `−S`) lie in the strict sub-`1/300` class (general inverse `h−r⋆h`, unique; growth propagation) | `liClockSubGammaClass_liEvenCrossActualClockResponse`, `liClockSubGammaClass_neg_liEvenCrossActualClockMassiveSource`, `eq_liClockThetaInverse`, `liClockThetaInverse_volterra`, `liClockSubGammaClass_liClockThetaInverse` |
| §3 (4) first-crossing laws `g(T)=(y⋆K)(T)` at a zero, `y'=g'−y⋆K'` | `liClockThetaForcingInput_eq_history_of_zero`, `hasDerivAt_neg_liEvenCrossActualClockMassiveSource` |
| (6) for every `A`, `T`: `∃t>T, (g⋆K)(t)>A g(t)` and `∃t>T, (g⋆K')(t)>A g'(t)` | `exists_liClockThetaForcingInput_conv_kernel_gt`, `exists_liClockThetaForcingInput_conv_kernelDeriv_gt` |
| §4 every positive exponential type for `g,g',K,K'`; (7) `K̂=Φ(1/p)−1`, `K̂'=pK̂`, `ĝ'=pĝ`; (8) `(g⋆K)^=ĝK̂`; (9) `K̂≥ν₁/(2p²)` | `liClockEveryExpType_liClockThetaForcingInput`, `liClockEveryExpType_liClockThetaKernel`, `integral_Ioi_liClockThetaKernel_mul_exp_neg_eq`, `integral_liClockThetaKernelDeriv_eq`, `integral_liClockThetaForcingInputDeriv_eq`, `integral_exp_mul_volterraConv_of_nonneg`, `liClockThetaGeneratorCoeff_one_div_sq_le_integral` |
| §5 `a=g'(0)=ω²M₀+M₁`, `b=K'(0)=ν₁/2`; `(g⋆K)=O_C`, `(g⋆K')=E_C`, `C₁=ab` | `liClockThetaForcingInputDeriv_zero`, `liClockThetaKernelDeriv_zero`, `volterraConv_liClockThetaForcingInput_kernel`, `volterraConv_liClockThetaForcingInput_kernelDeriv`, `liClockThetaHistoryCoeff_one` |
| (10) `(g⋆K)/g=ν₁t²/12+O(t⁴)`, `(g⋆K')/g'=ν₁t²/4+O(t⁴)`; both ratios →0; strict comparisons (5) on an origin interval | `exists_abs_history_div_forcingInput_sub_le`, `exists_abs_historyDeriv_div_forcingInputDeriv_sub_le`, `tendsto_history_div_forcingInput`, `tendsto_historyDeriv_div_forcingInputDeriv`, `exists_history_lt_forcingInput_near_zero` |

Proof-route note: cofinality in (6) is proved directly from the Laplace bound with a compact prefix (no separate continuous-extension step is needed); the conclusion is the card's.

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
