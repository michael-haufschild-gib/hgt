# Euler--Gamma horizontal-charge density at the 75% threshold

- **ID:** `euler-gamma-horizontal-charge-density-75`
- **Stage:** 1-in-progress
- **Type:** CONJECTURAL SOURCE ESTIMATE / EXACT PROVED REDUCTION
- **Source:** `claude-zeta23-rank-trace-audit.md`;
  `../2-fully-proven/not_new_scientific_knowledge/horizontal-entry-charge-transfer.md`;
  `../2-fully-proven/not_new_scientific_knowledge/euler-shift-pair-incidence-resultant.md`;
  `../3-formalized/not_new_scientific_knowledge/finite-offline-cauchy-energy-threshold-core.md`;
  `../2-fully-proven/not_new_scientific_knowledge/critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`;
  external Zeta-23 paper and Lean artifact
- **Statement:** Prove unconditionally that at least `75%` of Riemann-zeta zero copies lie on the
  critical line, using a quantitative Euler--Gamma estimate that separates positive real shifts
  from diagonal multiplicity even at submicroscopic displacement.  This would improve the
  optimized Zeta-23 constant `q_A = 0.672500703679...` without finite Gabor compression.

## Goal

Let `N(T)` count nontrivial zero copies through height `T`, `N_0(T)` count critical-line copies,
and, at each positive ordinate `gamma`, let `H_gamma` be total horizontal multiplicity.  Define

```text
O(T) = sum_(0<gamma<=T) H_gamma^2
       - sum_(0<Im rho<=T) m_rho^2.
```

The first exact horizontal-incidence target is the source-side density estimate

```text
limsup_(T->infinity) O(T)/N(T) <= 1/4.                    (HC75)
```

This proves the `75%` target because every off-line zero copy belongs to a reflected pair at
the same ordinate, and that pair contributes at least its total multiplicity to `O(T)`.  Hence

```text
N(T)-N_0(T) <= O(T),
liminf N_0(T)/N(T) >= 1-limsup O(T)/N(T) >= 3/4.
```

This reduction is insensitive to how close an off-line pair is to the critical line.  It therefore
avoids the `1/log T` displacement-resolution wall that kills resolvent, slab-variance, Turan, and
smooth detector bounds.

## Gates

- [x] 0 → 1 in-progress: exact target and external comparator identified; internal and external
  frontier audit complete; corpus-native carrier and exact numerical gate identified.
- [ ] 1 → 2 fully-proven: complete unconditional paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 → 3 formalized: exact theorem in Lean; targeted build, lint, and axiom gates pass.
- [ ] 3 → 4 publication-ready: standalone paper, independent proof and priority audit.

## Exact corpus carrier

For centered completed zeta `Xi`, the corpus constructs the positive intersection current

```text
J_Xi = dd^c log|Xi(c-u)| wedge dd^c log|Xi(c+u)|.
```

Twice its thin-slice mass on `Re u>0`, `Im u=0`, pushed to `Im c`, is exactly the measure `O`.
This construction uses completed-function values and Poincare--Lelong, not an enumerated zero
factorization.  The exact identity is paper-proved in
`euler-shift-pair-incidence-resultant.md`; it supplies no estimate by itself.

## Quantized anti-causal Cauchy reduction

The corpus contains a second separator stronger than every smooth displacement detector.  For a
finite positive-height window `W` of strict-right centered zeros

```text
lambda_j=a_j+i gamma_j,    0<a_j<1/2,
ell_W(t)=2 sum_j m_j exp(-(a_j+i gamma_j)t),  t>0,
E_W=integral_0^infinity |ell_W(t)|^2 dt,
```

termwise integration gives

```text
E_W=4 sum_(j,k) m_j m_k
  (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2).           (CE)
```

Every entry of `(CE)` is positive.  Its diagonal therefore gives

```text
E_W >= 2 sum_j m_j^2/a_j > 4 sum_j m_j^2 >= 4 R_W,
```

where `R_W=sum_j m_j` is strict-right multiplicity.  Functional-equation reflection preserves
height and multiplicity, so complete off-line multiplicity in `W` is `2R_W`.  Consequently

```text
N_off(W) < E_W/2.                                        (CR)
```

This is the requested submicroscopic separation: as `a_j->0+`, cost is not lost but diverges like
`1/a_j`; a critical-line zero has no strict-right anti-causal mode at all, regardless of its
diagonal multiplicity.  Unweighted energy is also uniquely phase-noncancelling among natural
power-weighted Hankel energies, by
`anti-causal-cauchy-trace-unique-phase-noncancellation.md`.

For dyadic `W_T=(T,2T]`, a source-defined localization satisfying

```text
E_(W_T) <= (1/2+o(1)) N(T,2T)                            (EG75)
```

would combine with `(CR)` to prove `(HC75)` and hence `N_0/N>=3/4`.  This is weaker than the
corpus's global four-unit contraction, which is RH-equivalent: `(EG75)` asks only for an average
energy budget proportional to the local zero census.

Main definition gate is source-faithful height localization.  A post-divisor cutoff merely
relabels zeros.  Required packet must arise before divisor expansion from completed Euler--Gamma
current, retain nonnegative weights on strict-right residues, exclude critical boundary divisor,
and preserve `(CE)`'s positive cross terms.

## Hostile source audit

Three tempting source transports are already closed by exact corpus theorems.

1. **Safe-offset tuning gives no slack.**  On every absolute-Euler line, the positive
   Caratheodory density and its Cauchy loss de-Poissonize to one offset-independent completed Weil
   form.  Prime weights return exactly to `-Lambda(n)/(2 sqrt(n))`.  Moving farther right only
   hides and then restores the same critical constraint.
2. **A bounded fixed-line continuation cannot carry `(CE)`.**  One pole at depth `a` has bounded
   Euler-line Hardy norm while its anti-causal residue energy grows like `1/a`.  The full
   FE--Schwarz quartet retains this blow-up.  Any valid transfer must use a source-selected
   unbounded graph or an equivalent residue coordinate.
3. **The global four-unit graph estimate is too strong.**  Corpus Ward and CCM theorems prove it
   equivalent to RH.  Reasserting that contraction does not establish the weaker density estimate
   `(EG75)`.  A legitimate advance must average the singular graph over height before taking the
   critical limit and prove only the relative `N(T,2T)/2` budget.

Thus missing knowledge is not Cauchy positivity, residue bookkeeping, or Euler-safe evaluation;
all are formalized.  It is a quantitative, height-local, source-defined incidence theorem that
survives unbounded de-Poissonization while discarding critical-line boundary multiplicity.

## Source-faithful Ward window inequality

The corpus already contains a better submicroscopic normalisation than multiplying each Cauchy
mode by a zero-dependent factor.  Write a strict-right centered zero as

```text
lambda_q = a_q + i gamma_q,     0<a_q<1/2.
```

At the Euler--Gamma probe `w=h+ic`, `h>1/2`, its Schwarz-pair Ward response is the sum of two
positive Lorentzians.  If `|gamma_q-c|<=delta`, the Lorentzian centered at `gamma_q` gives

```text
2h / ((h+1/2)^2+delta^2) <= Re r_q(h+ic).                (WQ)
```

The lower bound is uniform as `a_q->0+`: numerator `h+a_q` is bounded below by `h`, and its
denominator is bounded above by `(h+1/2)^2+delta^2`.  A critical-line zero supplies no
strict-right Ward mode at all, independent of multiplicity.  Thus `(WQ)` separates every positive
horizontal shift from the diagonal boundary at arbitrarily small displacement without an
inverse-`a_q` blow-up.

Let `S` be any finite set of multiplicity copies of strict-right upper zeros in that height
window.  Positivity of every Schwarz-pair response and absolute convergence of their sum give

```text
card(S) * 2h / ((h+1/2)^2+delta^2)
  <= sum_(q in S) Re r_q(h+ic)
  <= Re r(h+ic).
```

Functional-equation reflection absorbs both the complementary divisor term and the complete
Ward boundary self-symbol.  The existing source identity therefore proves the unconditional
Euler--Gamma estimate

```text
card(S) * 2h / ((h+1/2)^2+delta^2) <= B_EG(h,c),          (EGW)

B_EG(h,c)
 = 2 Re[ 1/s + 1/(s-1) + (Gamma_R'/Gamma_R)(s)
         - sum_(n>=2) Lambda(n)n^(-s) ],
s=h+1/2+ic,   Re s>1.
```

Every term on the right is in the absolute Euler region.  No zero location, line multiplicity,
RH premise, or post-divisor scalar normalisation occurs in `B_EG`.  Paper proof is exactly the
three displayed inequalities: the already-proved per-pair Lorentzian bound, finite-sum
monotonicity inside the nonnegative absolutely convergent Ward series, and the already-proved
source-only Ward majorant.

### Sharp endpoint quantum

The first uniform quantum `(WQ)` is not sharp.  Put `H=h+1/2`,
`x=h+a_q in (h,H)`, and `d=gamma_q-c`.  The near-center Lorentzian is

```text
2x/(x^2+d^2).
```

Since `d^2<=delta^2`, it is bounded below by `2x/(x^2+delta^2)`.  This last
function has no interior minimum on `[h,H]`: algebraically,

```text
2x/(x^2+D) - 2h/(h^2+D)
  has sign (x-h)(D-hx),

2x/(x^2+D) - 2H/(H^2+D)
  has sign (H-x)(Hx-D).
```

If `hx<=D`, the first difference is nonnegative; otherwise `D<hx<=Hx`, so
the second is nonnegative.  Therefore every pair in the window deposits the
sharp displacement-uniform endpoint quantum

```text
Q_sharp(h,delta)
 = min(2h/(h^2+delta^2),
       2(h+1/2)/((h+1/2)^2+delta^2)).                 (WQsharp)
```

Replacing `(WQ)` by `(WQsharp)` in the finite-sum argument gives

```text
card(S) * Q_sharp(h,delta) <= B_EG(h,c).               (EGWsharp)
```

This is optimal among lower bounds using only `h<x<h+1/2` and
`d^2<=delta^2`, since `x` can approach either endpoint and `d^2` can approach
`delta^2`.  Near the Euler edge with a narrow window it improves `(EGW)` by
an asymptotic factor `2`.  Numerical hostile sampling over `500000` random
parameter tuples found nonnegative gap, with the smallest sampled gap
`1.71e-8` near an endpoint; the displayed factorization is the proof.

Lean formalization is complete in
`formal/GaloisForLFunctions/RHTower/XiWardSourceWindowMultiplicity.lean`; targeted build and axiom
audit pass.  Formal card:
`../3-formalized/not_new_scientific_knowledge/euler-gamma-ward-window-multiplicity-bound.md`.

This closes the requested *local separator* but not `(HC75)`.  Stirling gives
`B_EG(h,c)~log(|c|/(2pi))`; summing first-moment windows through a dyadic interval therefore has
the same `T log T` order and leading scale as the full zero census.  The raw Ward first moment
cannot supply the missing factor `1/8` for strict-right multiplicity.  A 75% proof still needs a
centered quadratic/correlation estimate, or an index estimate, which removes the universal Gamma
baseline before summation.

### Exact localized quadratic gate

The edge Gram corpus fixes the constant required from that correlation estimate.  Put
`x_q=a_q+1/2 in (1/2,1)`.  On the Euler edge the real part of one Schwarz-pair response is

```text
f_q(t) = 2x_q/(x_q^2+(t+gamma_q)^2)
       + 2x_q/(x_q^2+(t-gamma_q)^2) >= 0.
```

For `1<L<T/2`, let

```text
U_(T,L)=[-2T-L,-T+L] union [T-L,2T+L].
```

If `F_T` is any finite set of strict-right multiplicity copies with `T<gamma_q<=2T`, positivity
before squaring and the two length-`2L` neighborhoods of `+-gamma_q` give

```text
(4pi-16/(3L^3)) card(F_T)
  <= integral_(U_(T,L)) (Re r(1/2+it))^2 dt.             (WQL)
```

Indeed, each centered Lorentzian square has full mass `2pi/x_q`; its two tails beyond `L` have
mass at most `8/(3L^3)`.  There are two centers, and `(sum f_q)^2>=sum f_q^2`.  This is uniform as
`a_q->0+`, uses multiplicity copies, and never charges a critical-line zero.

Let `L=L(T)->infinity` with `L(T)=o(T)`.  The first proposed source gate
`integral_U (Re r)^2 <= (pi/2+o(1))N` was dimensionally wrong: it is sufficient, but vastly
stronger than a `75%` theorem.  Each right-upper copy also deposits `4pi-o(1)` of **linear** mass
on `U`.  If `M_U=integral_U Re r`, `E_U=integral_U (Re r)^2`, and `V_U=|U|=2T+4L`, then
Cauchy--Schwarz gives

```text
((4pi-o(1)) R(T,2T))^2 <= M_U^2 <= V_U E_U.             (WQCS)
```

At the threshold `R=N/8`, the correct raw-energy scale is therefore

```text
E_U >= (pi^2/4+o(1)) N(T,2T)^2 / V_U
    = (pi^2/8+o(1)) N(T,2T)^2 / T.                     (EGQ75-scale)
```

Since `N(T,2T)~T log T/(2pi)`, this is of order `T log^2 T`, not `N~T log T`.  Any bound
`E_U=O(N)` would instead force `R=O(sqrt(TN))=o(N)` and hence density one.  The natural
`T log^2 T` order also explains why the uncentered Gamma baseline cannot be ignored; only its
leading constant and a source-faithful removal of the critical-line channel can decide `75%`.

The exact algebraic scale `(WQCS)` and its `N/8` specialization are formalized in
`XiWardSourceWindowMultiplicity.lean` as
`sq_setIntegral_le_length_mul_setIntegral_sq`,
`ward_raw_quadratic_energy_scale_at_eighth`,
`ward_raw_quadratic_energy_scale_at_eighth_twoTime`, and
`ward_setIntegral_energy_scale_at_eighth`.

Corpus audit finds no proof below the corrected `(EGQ75-scale)`.  `XiWardEdgeImChannelGram.lean` evaluates the quadratic
energy as a positive zero-pair Gram sum, not as Euler--Gamma data.  The source absorption in
`XiWardInteriorReflectionAbsorption.lean` is linear; squaring its uncentered `O(log T)` majorant
only gives `O(T log^2 T)`.  A valid proof must expose cancellation of the Gamma census baseline
through a centered prime--Gamma two-point identity.  The existing moire/Ward audit locates the
same obstruction as the subtraction defect between the full prime trace and the critical-line
spectral trace; bypassing it would amount to assuming the missing correlation.

### Two rejected false shortcuts

1. The exact co-Poisson critical flux `integral_0^X t|P(t)|^2 dt~(1/4)log X` is a dilation-tail
   law, not a height census.  Its multiplier ideal is proved dense and erases divisor classes;
   the matching constant `1/4` has no proved map to the `T log T` zero scale.
2. Normalising a Cauchy mode by `sqrt(2a_q)` makes its self-Gram exactly one and preserves positive
   cross terms, but it is zero-dependent.  It is not produced by the holomorphic Euler--Gamma
   source: a nonvanishing holomorphic scalar `H` with `|H(z)|^2=2 Re z` would make
   `log|H(z)|=(1/2)log(2 Re z)` harmonic, whereas its Laplacian is
   `-1/(2(Re z)^2)`.  The Ward Lorentzian normalisation avoids this defect.

## Horizontal-current alternative

Replace the discontinuous thin slice by a positive microscopic majorant.  For a nonnegative
dyadic height window `w_T` and a nonnegative smooth `kappa` with `kappa(0)=1`, define

```text
O_(T,eta) = 2 integral w_T(Im c) 1_(Re u>0)
              kappa(Im u log(T)/eta) dJ_Xi(c,u).
```

Every same-ordinate reflection atom occurs with full weight, so `O(T,2T) <= O_(T,eta)` up to the
chosen endpoint convention.  The missing theorem is to prove, directly from the completed
Euler--Gamma source, for one explicit `(w,kappa,eta)`,

```text
limsup O_(T,eta)/N(T,2T) <= 1/4.                         (HC)
```

Poincare--Lelong and two integrations by parts turn `(HC)` into a smoothed two-point correlation
of `log|Xi(c-u)|` and `log|Xi(c+u)|`.  Candidate infrastructure is the corpus's full rectangular
Guinand--Weil formula, Selberg prime-square pairing, and completed prime--Gamma cross-kernel.
What must be added is the quantitative nonlinear correlation estimate and all boundary control;
none is presently proved.

The cutoff in `Re u` cannot be harmlessly smoothed.  A continuous cutoff vanishing at `u=0`
misses off-line pairs with arbitrarily small displacement, while one nonzero at `u=0` also charges
the diagonal multiplicity current.  Thus `(HC)` must retain the open-stratum boundary term or
subtract its diagonal contribution by a separately proved source identity.  This discontinuous
separation is the main hostile gate, not a technicality.

This is mathematically different from Zeta-23: it charges the off-line reflection incidence
directly and uses no finite critical-density Gabor system, Gram trace/Frobenius comparison, or
rank--trace multiplicity inequality.  A proof may still encounter an equivalent pair-correlation
barrier; different packaging is not counted as progress.

## Real-shift semigroup annulus

There is a second source-side cancellation that survives hostile algebra.  For one strict-right
upper copy `q`, write its centered zero as `a+i gamma`, where `0<a<1/2`, and let

```text
E_h(q) = integral_R (Re r_q(h+it))^2 dt.
```

Exact Cauchy integration gives

```text
E_h(q) = 4 pi [1/(h+a) + (h+a)/((h+a)^2+gamma^2)].       (SA1)
```

Both shifts `h=3/5` and `h=8/5` lie in the absolute Euler chamber.  Put
`x=3/5+a in (3/5,11/10)` and `g=gamma^2`.  Direct common-denominator algebra proves

```text
1/4 <= (1/x-1/(x+1))
       + x/(x^2+g) - (x+1)/((x+1)^2+g),                 (SA2)
```

and therefore

```text
pi <= E_(3/5)(q) - E_(8/5)(q).                          (SA3)
```

This is uniform in height and remains nonzero as `a` tends to zero from the right.  Its Laplace
weight is the positive annulus `exp(-6u/5)-exp(-16u/5)`, so the zero-frequency Gamma baseline
cancels.  Numerical minimization over the full strip and `g>=0` was used before formalization;
the observed minimum exceeds the deliberately coarse certified constant `1/4`.

`(SA3)` is not yet a census inequality.  In a sum of pair responses, the difference of the two
quadratic energies contains cross terms.  Its spatial Cauchy kernel changes sign for sufficiently
large ordinate separation.  Positive definiteness of the Laplace annulus controls the complete
quadratic form, but does not make that form dominate its diagonal.  Random signs would isolate the
diagonal, yet signs indexed by unknown strict-right zeros are not source-produced.  Likewise, the
two separate source inequalities cannot be subtracted: `R_(3/5)<=B_(3/5)` and
`R_(8/5)<=B_(8/5)` do not imply a bound for their differences.  The exact survivor is thus a
fixed diagonal quantum with Gamma cancellation; the remaining open bridge is a source-faithful
trace/randomization or a direct bound for the negative cross channel.

The first `pi` constant is not close to the local limit.  For arbitrary `x,d>0` and `g>=0`, a
second paper proof gives

```text
d/[x(x+d)] - 1/d
 <= (1/x-1/(x+d))
    + x/(x^2+g) - (x+d)/((x+d)^2+g).                    (SA4)
```

If `g<=x(x+d)`, the second difference is nonnegative.  Otherwise its negative magnitude is at
most `1/d`, because

```text
(x^2+g)((x+d)^2+g) = (g+x(x+d))^2+d^2 g >= d^2 g.
```

Taking `h=51/100`, `d=10`, and hence `x in (51/100,101/100)`, `(SA4)` is greater than `3/4`.
Consequently the source-safe shifts `51/100` and `1051/100` satisfy

```text
3 pi <= E_(51/100)(q) - E_(1051/100)(q).                (SA5)
```

This triples `(SA3)` and approaches the natural `4pi` local ceiling as the first shift approaches
`1/2` from above and the second shift tends rightward.  It does not remove the signed cross/trace
bridge described above.

An explicit near-ceiling instance uses `d=150`.  The same rational bound is at least `39/40`, so

```text
(39/10) pi <= E_(51/100)(q) - E_(15051/100)(q).          (SA6)
```

Thus the certified source-safe diagonal separator reaches `97.5%` of the `4pi` local ceiling.
This percentage is a local energy constant, not a zeta-zero proportion.

## Exact four-moment barrier at bandwidth one

The first possible higher-trace repair does not reach `75%`, even under the conjectural fourth
sine-kernel moment.  Normalize the positive spectral measure so that its positive mass is `m_0`
and its next four moments at bandwidth one are

```text
m_1=1,  m_2=4/3,  m_3=2,  m_4=13/4.
```

For the quadratic polynomial

```text
p(x)=1-(7/4)x+(2/3)x^2
```

direct expansion gives the exact identity

```text
integral p(x)^2 dmu(x)=m_0-31/36.                       (M4)
```

Positivity therefore forces `m_0>=31/36`.  The corresponding off-RH line certificate is only

```text
2m_0-1 >= 13/18 = 0.7222... .                           (M4-line)
```

The bound is sharp for these moments: at equality the positive measure has two atoms at
`(21-sqrt(57))/16` and `(21+sqrt(57))/16`, with respective positive weights
`(75+31sqrt(57))/(72sqrt(57))` and `(-75+31sqrt(57))/(72sqrt(57))`.  Thus first-four-moment
positivity is short of the `75%` target by exactly `1/36` on the positive-mass side.  Equivalently,
holding `m_1,m_2,m_3` fixed, the same quadratic certificate would need `m_4<=29/9`, whereas the
sine-kernel value is the larger `13/4`.

This is the scalar form of the `3x3` Hankel determinant

```text
det [[m_0,1,4/3],[1,4/3,2],[4/3,2,13/4]]
  =(36m_0-31)/108.
```

It confirms that a fourth trace cannot close the target even if its Hardy--Littlewood input were
granted.  The next viable trace route needs at least fifth/sixth-order information at near-unit
bandwidth, beyond the unconditional range `k lambda<2`.

Two adjacent extensions were hostile-tested and rejected:

1. The Chirre--Goncalves--de Laat `0.6792` SDP uses a physical-frequency test function that is
   negative outside bandwidth one and discards that tail using nonnegativity of Montgomery's
   real-ordinate pair-correlation function.  A source-faithful off-RH compression has a positive
   frame metric; its stationary Frobenius lag is an autocorrelation of positive operators and is
   pointwise nonnegative.  It therefore cannot reproduce the negative SDP tail without losing the
   positive-rank block used by the Zeta-23 certificate.
2. Applying horizontal derivatives of order `k` to an Euler-safe Ward probe multiplies its Laplace
   weight by `u^k` and centers it at semigroup time `u asymp k/h`.  Montgomery--Vaughan control of
   the differentiated prime series requires its effective length `exp(k/h)` to be at most `T`, so
   `k=O(log T)`.  Uniform decorrelation of distinct ordinates at gaps `o(1/log T)` would require
   `k>>log^2 T`.  The derivative ladder therefore recreates, rather than defeats, the
   primes-beyond-`T` barrier.

## Zero-frequency obstruction to annular aggregation

The signed cross kernel behind a Ward width annulus has a stronger obstruction than isolated
negative cross terms.  For `x,d>0`, put

```text
K_(x,d)(Delta)
  = 2x/((2x)^2+Delta^2)
    -2(x+d)/((2(x+d))^2+Delta^2).
```

Exact Cauchy integration and diagonal evaluation give

```text
integral_R K_(x,d)(Delta) dDelta = 0,                   (Z0)
K_(x,d)(0) = d/[2x(x+d)] > 0.                           (ZD)
```

Thus the annulus Fourier multiplier vanishes at spatial frequency zero although every diagonal
copy has positive mass.  Dense nearly uniform ordinate packets are an asymptotic blind channel:
their aggregate Toeplitz energy can cancel while the diagonal census grows.  This rules out any
diagonal-dominance inference from `(SA3)`--`(SA6)`, even asymptotically, unless the source supplies
an independent trace, decorrelation, or topological index law.  Lean declarations
`integral_cauchy_cross_shift_annulus_eq_zero` and
`cauchy_cross_shift_annulus_zero_eq_pos` prove `(Z0)`--`(ZD)` exactly.

## Plucker--Ward renormalized positive-shift atom

The preceding no-go points to a singular, rather than fixed-shift, separator.  Let `a>0` be the
horizontal depth of one off-line pair.  Analytic continuation of the critical-density Gabor
sampling identity shows that the negative eigenvalue of its pulled-back hyperbolic block contains
the exact coalescence gap

```text
Phi(2ia)-Phi(0)
 = integral phi(u)^2 [cosh(2au)-1] du.                  (PW1)
```

It vanishes quadratically as `a->0`.  The squared diagonal of the right-half-plane Hardy Cauchy
kernel is `1/(2a)^2`.  Pointwise in frequency,

```text
[cosh(2au)-1] [1/(2a)]^2 >= u^2/2                     (PW2)
```

because `cosh(2x)-1=2sinh(x)^2>=2x^2`.  Hence two inverse-displacement Hardy factors exactly cancel
the Plucker/Gabor coalescence and leave a nonzero quantum for every positive shift, however
submicroscopic.  Under the totalized inverse convention the atom is zero at `a=0`; critical-line
multiplicity therefore does not enter this channel.

The actual continued Xi Ward field is stronger at the node adapted to a strict-right copy `q`.
Writing `a=Re(lambda_q)` and taking any `u!=0`, positivity of every Schwarz-pair response gives

```text
2u^2
 < [cosh(2au)-1]
   |continuedXiAntiCausalWardResponse(conj(lambda_q))|^2. (PW3)
```

`(PW2)` and `(PW3)` are formalized as
`half_sq_le_coshGap_mul_sq_transverseCauchyKernel_self` and
`two_mul_sq_lt_coshGap_mul_normSq_continuedWard_at_adaptedNode`.

The finite-band loss is now quantitatively sharp up to a factor two.  Whenever `|2au|<=1`,

```text
2a^2u^2 <= cosh(2au)-1 <= 4a^2u^2,
u^2/2 <= [cosh(2au)-1]/(2a)^2 <= u^2.                  (PW4)
```

Thus every bounded-frequency reader loses a coalescing pair exactly quadratically; inverse-square
Cauchy normalization is not an artifact of a loose lower bound.  Lean declarations
`cosh_sub_one_le_sq_of_abs_le_one`, `coshGap_le_four_mul_sq_of_submicroscopic`, and
`pluckerWardRenormalizedAtom_mem_Icc` prove `(PW4)`.

This is the first exact corpus-native mechanism found here that simultaneously has all three local
properties requested by the target: positive real-shift support, a displacement-uniform quantum,
and exclusion of diagonal critical-line multiplicity.  It is not yet a density theorem.  Both the
factor `cosh(2au)-1` and the evaluation node depend on the unknown zero.  Summing `(PW3)` from the
Euler--Gamma side requires a source-defined nonlinear sampling/trace identity; simply inserting
the divisor or independently choosing each adapted node is circular.  Boundary-line cubic Ward
mass has the right `a^(-2)` scaling, but its prime-side realization is outside the absolute Euler
chamber and reopens the support/correlation problem.

The uniform jump is necessarily singular.  If a scalar detector `F(a)` were continuous at zero,
vanished at zero, and satisfied `F(a)>=c>0` for every `a>0`, the sequence `a_n=1/(n+1)` would force
both `F(a_n)->0` and `F(a_n)>=c`, a contradiction.  Lean formalizes this general barrier as
`not_exists_uniform_positive_continuous_boundarySeparator` and proves the concrete atom is
discontinuous at the boundary in `not_continuousAt_zero_pluckerWardRenormalizedAtom`.  Thus the
inverse-Cauchy normalization in `(PW2)` cannot be replaced by a bounded continuous source reader.

## Critical-diagonal-retaining Euler--Gamma estimate

Reflection absorption originally discarded every critical-line contribution in the nonright
canonical factor.  Retaining an arbitrary selected critical stratum `C` gives the stronger exact
source inequality

```text
Re Ward_right(w)
 + sum_(rho in C) Re[2i R_rho(iw)]
 <= A_Euler-Gamma(w),                                  (HD1)
```

where `A_Euler-Gamma` is the same pole--Gamma--absolutely-convergent-von-Mangoldt head as `(EGW)`.
For a critical copy of ordinate `gamma`,

```text
Re[2i R_rho(i(h+ic))] = 2h/[h^2+(c+gamma)^2].          (HD2)
```

Consequently finite strict-right and critical packets in one height window obey

```text
|S| Q_right(h,delta) + |C| 2h/(h^2+delta^2)
 <= A_Euler-Gamma(h+ic).                               (HD3)
```

Lean formalizes `(HD1)` as
`re_continued_add_critical_tsum_le_sourceArithmetic`, `(HD2)` as
`re_two_I_relativeResolventTerm_critical_line_eq`, and `(HD3)` as
`finite_strictRight_and_critical_window_charge_le_sourceArithmetic`.

This is the requested source-side separation at finite height, but its first-order global constant
does not improve `0.6725`: one critical copy and one positive-height strict-right copy carry the
same leading Poisson mass, while the omitted FE-reflected copy supplies the other unit in
`N=N_0+2R`.  Height integration therefore recovers natural divisor bookkeeping.

The reflected copy exposes a nontrivial second-order survivor.  Comparing the two FE widths
`h+a,h-a` with a double critical width `h,h` and renormalizing by `a^(-2)` gives

```text
H_h(a)
 = a^(-2)[(h+a)^(-1)+(h-a)^(-1)-2h^(-1)]
 = 2/[h(h^2-a^2)].                                    (RC1)
```

For `0<a<h`, `H_h(a)>=2/h^3`; for `2a<=h`,

```text
2/h^3 <= H_h(a) <= 8/(3h^3),                          (RC2)
H_h(0)=0                                               (RC3)
```

under totalized inversion.  Declarations `horizontalCauchyCurvatureAtom_eq`,
`two_div_cube_le_horizontalCauchyCurvatureAtom`,
`horizontalCauchyCurvatureAtom_le_eight_div_three_cube`, and
`horizontalCauchyCurvatureAtom_zero` prove `(RC1)`--`(RC3)`.  This is a second independent
submicroscopic separator, now arising directly from FE reflection rather than the Gabor Plucker
gap.  Its unresolved producer is again singular source aggregation: the `a^(-2)` normalization
cannot be chosen from a bounded fixed-band source observable without tangent outer-product data.

## Shallow-layer positive Cauchy census

The atom suggests shifting the entire positive Hardy packet rather than subtracting two shifts.
For a finite packet with depths `0<a_j<=h`, ordinates `gamma_j`, and multiplicities `m_j`, define

```text
E_h = 4 sum_(j,k) m_j m_k
        (2h+a_j+a_k)/[(2h+a_j+a_k)^2+(gamma_j-gamma_k)^2].  (SL1)
```

Every entry in `(SL1)` is positive.  Its `j`-th diagonal is

```text
2 m_j^2/(h+a_j) >= m_j/h,                                (SL2)
```

because `a_j<=h` and an integral multiplicity obeys `m_j^2>=m_j`.  Therefore

```text
sum_j m_j <= h E_h.                                      (SL3)
```

Unlike the semigroup annulus, this quadratic form has no zero-frequency cancellation and no
negative cross channel.  At `h asymp 1/log T`, every shallow strict-right copy costs order
`log T`; critical-line copies are absent from the strict-right index.  The generic
multiplicity-exact theorem is
`sum_multiplicity_le_shift_mul_finiteOfflineCauchyEnergy`; the packet-cardinality and actual-Xi
specializations are `card_le_shift_mul_finiteOfflineCauchyEnergy` and
`xiRight_shallowLayer_card_le_shift_mul_finiteOfflineCauchyEnergy`.

Write `R_sh(T;h)` and `R_deep(T;h)` for strict-right multiplicities with depth at most and greater
than `h`.  Since

```text
N(T,2T) = N_0(T,2T) + 2 [R_sh(T;h)+R_deep(T;h)],          (SL4)
```

the exact three-quarters receiver is

```text
h E_h(T) + R_deep(T;h) <= N(T,2T)/8
    ==> N_0(T,2T) >= 3 N(T,2T)/4.                        (SL5)
```

`three_quarters_line_of_shallowEnergy_and_deepCount` proves `(SL5)` in Lean.  This exposes one
precise analytic target, not a proved density result.  The present corpus gives an arithmetic Ward
majorant only in the absolute-Euler chamber `h>1/2`.  Transporting `(SL1)` to
`h asymp 1/log T` requires a source upper bound for the aperture-tangent outer product.  Finite
Hardy multiplier contractivity does not yield that bound by differentiation: the zero-aperture
transport vanishes, while the fixed four-unit term remains and division by the aperture square
blows up.  A Fejer deconvolution of the safe edge lands at the same missing tangent covariance.

## Active labels

- `[LITERATURE]` Zeta-23 proves the optimized unconditional constant
  `q_A = 0.672500703679...` and formalizes it without nonstandard axioms.
- `[PAPER-PROVED REDUCTION]` `N-N_0 <= O`; `(HC)` with constant `1/4` proves `75%`.
- `[PAPER-PROVED REDUCTION]` Anti-causal packet satisfies `N_off(W)<E_W/2`; `(EG75)` proves
  `75%` and strengthens as horizontal displacement tends to zero.
- `[PAPER-PROVED SOURCE ESTIMATE]` `(EGW)` bounds any finite multiplicity-exact strict-right
  height-window packet by an explicit absolutely convergent Euler--Gamma quantity, uniformly for
  arbitrarily small positive horizontal displacement and with critical-line multiplicity absent.
- `[PAPER-PROVED SOURCE ESTIMATE]` `(EGWsharp)` replaces its per-pair quantum by the optimal
  endpoint minimum `(WQsharp)`, gaining up to a factor `2` without changing source assumptions.
- `[FORMALIZED QUADRATIC SCALE CORRECTION]` `(WQL)` gives a uniform localized `4pi` real-channel
  square deposit, while the linear-mass/Cauchy law `(WQCS)` shows the actual `75%` raw-energy
  threshold is `(pi^2/8+o(1))N(T,2T)^2/T`; an `O(N)` bound would imply density one.
- `[FORMALIZED DIAGONAL SURVIVOR]` `(SA1)`--`(SA3)` give a fixed `pi` loss per strict-right copy
  between two absolute-Euler shifts and cancel the zero-frequency Gamma baseline.
- `[FORMALIZED SHARPENING]` `(SA4)`--`(SA6)` raise the explicit source-safe diagonal loss first to
  `3pi`, then to `39pi/10`, and exhibit a family approaching the local `4pi` ceiling.
- `[FORMALIZED ZERO-MODE OBSTRUCTION]` `(Z0)`--`(ZD)` show the annular cross kernel has exactly
  zero spatial mass despite a positive diagonal, closing aggregate diagonal dominance.
- `[FORMALIZED SUBMICROSCOPIC SURVIVOR]` `(PW2)`--`(PW3)` exactly cancel quadratic off-line
  Plucker coalescence by the squared Hardy Cauchy singularity and leave a uniform positive-shift
  quantum while excluding critical-line multiplicity.
- `[FORMALIZED FINITE-BAND SHARPNESS]` `(PW4)` traps the renormalized Plucker--Ward atom in
  `[u^2/2,u^2]` and proves bounded-band coalescence is exactly quadratic.
- `[FORMALIZED HYBRID SOURCE ESTIMATE]` `(HD1)`--`(HD3)` retain critical diagonal multiplicity
  on the left of the same explicit Euler--Gamma source inequality; its leading global charge is
  natural multiplicity bookkeeping, so no proportion gain is claimed.
- `[FORMALIZED REFLECTION-CURVATURE SURVIVOR]` `(RC1)`--`(RC3)` cancel double critical
  multiplicity against FE widths `h+-a` and leave a uniform inverse-square-renormalized charge.
- `[FORMALIZED SINGULARITY BARRIER]` Every continuous detector vanishing on the critical boundary
  loses any uniform positive-shift quantum; the Plucker--Ward atom is therefore necessarily
  discontinuous at zero.
- `[FORMALIZED SHALLOW-LAYER SURVIVOR]` `(SL1)`--`(SL3)` charge every shallow strict-right
  multiplicity by `1/h` in a Cauchy Gram with strictly positive cross terms.
- `[FORMALIZED 75% RECEIVER]` `(SL4)`--`(SL5)` reduce the target to the quantitative source budget
  `h E_h+R_deep<=N/8`; no unconditional proof of that budget is claimed.
- `[FORMALIZED ALL-SCALE SEPARATOR]` `(LP1)`--`(LP8)` give every positive depth the same
  `log(9/8)/h` diagonal charge, make every mixed term positive, exclude critical displacement,
  and remove the shallow/deep split.
- `[FORMALIZED ALL-SCALE 75% RECEIVER]` `(LP9)` reduces the target to
  `h E_h^LP/log(9/8)<=N/8`; the pre-spectral Euler--Gamma upper bound remains open.
- `[FORMALIZED ALL-SCALE SOURCE NO-GO]` `(ES1)`--`(ES3)` show the same `log(9/8)` factor preserves
  the nonsummable balanced von Mangoldt wall, ruling out a finite global Euler Hilbert budget.
- `[FORMALIZED CUBIC SOURCE ADMISSION]` `(CM1)`--`(CM12)` replace `dr/r` by `r^2 dr`, giving
  strict-right self-charge `115/(864a^3)`, uniform quantum `115/108`, and a summable literal
  balanced Euler diagonal dominated by `1/[p(log p)^2] 2^(-e)`.
- `[FORMALIZED METHOD BARRIER]` The exact fourth-moment square `(M4)` forces only
  `m_0>=31/36`, hence only `13/18` on the line; `75%` needs information beyond the first four
  bandwidth-one moments.
- `[PAPER-PROVED CARRIER]` The positive-real thin slice of `J_Xi` equals `O` exactly.
- `[OPEN CORE]` Construct source-faithful dyadic anti-causal localization and prove `(EG75)`, or
  prove a raw/centered prime--Gamma correlation strictly below the corrected
  `(pi^2/8)N(T,2T)^2/T` threshold; equivalently prove `(HC)` with constant `1/4` by a
  source-defined current estimate.  The semigroup-annulus formulation asks for a source trace
  that keeps `(SA3)`'s diagonal while controlling its signed cross channel.  The Plucker--Ward
  formulation asks for a source-defined nonlinear sampling/trace law aggregating `(PW3)` without
  zero-adapted selection.  The sharpest positive-Cauchy formulation is `(SL5)`: for
  `h asymp 1/log T`, prove `h E_h(T)+R_deep(T;h)<=N(T,2T)/8+o(N)` from the prime--Gamma source.
  Its missing analytic object is the aperture-tangent outer-product covariance, not Cauchy
  positivity or multiplicity bookkeeping.

## No-go closure (mandatory when falsified)

- **Resolved dead alternatives:**
  1. resolvent mass and Turan bounds weight high zeros too weakly;
  2. slab variance and bounded displacement energies lose uniform force as a pair approaches the
     line; unweighted anti-causal Cauchy energy has correct inverse-displacement force but no
     proved height-averaged source upper bound;
  3. de Bruijn--Newman flow is monotone toward the line and gives upper extinction-time bounds;
  4. the `0.86864` Zeta-23 result for zeros of `Xi'` does not transfer back to zeros of `Xi`:
     Rolle and Gauss--Lucas point in the wrong direction, while the corpus's Hedenmalm census
     collision premise is RH-bearing;
  5. a lower bound for distinct zero locations does not bound distinct ordinates: simple off-line
     reflected pairs may make every zero location distinct;
  6. smoothing the positive-real-shift indicator either loses submicroscopic off-line pairs or
     imports the collision-conserved diagonal multiplicity charge;
  7. a mass-shifted aperture spectral-flow contact has no source-derived map from contact degree
     to zeta height or multiplicity, so its positive residues do not produce a density census;
  8. mixing bandwidth-one second trace with a subcritical third trace adds no constraint without
     cross-scale moments; creating those moments restores total support beyond one;
  9. the semigroup annulus has exact zero spatial mass, so dense packets defeat aggregate
     diagonal dominance even though the one-copy diagonal approaches `4pi`;
  10. Fejer deconvolution from the absolute-Euler edge preserves a positive Cauchy kernel but
      requires the unproved aperture-tangent outer-product source covariance;
  11. higher trace moments cannot improve the unconditional bandwidth-one certificate: the
      available range is `k lambda<2`, so `lambda>1/2` permits no useful even moment beyond two,
      while `lambda<=1/2` has a nonpositive dimension certificate.
- **Strongest positive survivor:** anti-causal Euler--Gamma density estimate `(EG75)`, with `(HC)`
  as current-theoretic alternative.
- **New insight:** the corpus's absolute `<2` horizontal-charge target is unnecessarily strong for
  this problem.  Relative constant `1/4` suffices, and anti-causal energy supplies a singular
  submicroscopic separator unavailable to bounded smooth detectors.
- **Status:** exact `75%` reductions paper-proved; missing source estimate remains open; no Lean
  headline theorem or density improvement claimed.

## Log

- 2026-08-12 — created in Stage 1 for exact Zeta-23 constant-improvement target.
- 2026-08-12 — scope corrected after user requested a genuinely corpus-native mechanism rather
  than a higher-bandwidth refinement of Zeta-23.  Horizontal charge selected as sole survivor;
  exact threshold and source-current target recorded.
- 2026-08-12 — target raised to `75%`.  Added anti-causal Cauchy reduction `(CE)`--`(EG75)`, which
  separates strict positive shifts from arbitrary critical-line multiplicity at submicroscopic
  displacement.  Global four-unit transport rejected as an RH-equivalent restatement; only a
  height-averaged source incidence can count as progress.
- 2026-08-13 — proved `(EGW)` on paper: finite strict-right window multiplicity is bounded by the
  explicit absolute-Euler Ward source at one interior probe, uniformly down to submicroscopic
  horizontal displacement and with line multiplicity absent.  Constant audit shows its raw first
  moment is census-scale but does not by itself yield `75%`; co-Poisson `1/4` and zero-normalised
  Cauchy shortcuts rejected.
- 2026-08-13 — audited the complete edge Gram stack and obtained the per-copy square deposit
  `(WQL)`.  The initially recorded `pi/2` times `N` source gate was later superseded by the
  linear-mass/Cauchy scaling correction below.  Existing quadratic formulas are zero-side; no
  centered prime--Gamma source upper bound is present.
- 2026-08-13 — conjectured a stronger determinant/trace charge for each FE-conjugate Zeta-23
  off-line block and falsified it: as depth tends to zero the two evaluation vectors coalesce and
  the pulled-back hyperbolic block approaches the positive rank-one equality case of the existing
  rank--trace inequality.  Extracted the sharp positive survivor `(WQsharp)`--`(EGWsharp)`; paper
  proof and numerical pre-certification complete.  Lean declarations
  `xiWardSharpWindowQuantum_le_lorentzian`, `sharp_interior_pair_quantum`, and
  `finite_strictRight_window_card_mul_sharpQuantum_le_sourceArithmetic` pass targeted build and
  standard-axiom audit.  Repository-wide lint is red only on unrelated umbrella reachability gaps.
- 2026-08-13 — found and formalized the real-shift semigroup-annulus survivor `(SA1)`--`(SA3)`.
  It gives a height- and displacement-uniform `pi` diagonal loss between shifts `3/5` and `8/5`
  while canceling the zero-frequency Gamma baseline.  Hostile cross-term audit prevents a density
  claim: the spatial difference kernel changes sign, and neither unknown-zero randomization nor
  subtraction of separate one-sided source bounds is currently justified.
- 2026-08-13 — derived the general width-annulus lower bound `(SA4)` and specialized it to the
  absolute-Euler shifts `51/100` and `1051/100`, giving the stronger `3pi` quantum `(SA5)`.
  Lean proofs compile; global implication remains blocked by the same source-visible trace gate.
- 2026-08-13 — pushed the same unconditional family to the explicit shifts `51/100` and
  `15051/100`, proving `(SA6)`: a `39pi/10` diagonal loss, 97.5% of the local `4pi` ceiling.
  Also formalized the exact cross-kernel sign obstruction: sufficiently separated ordinates make
  the annular spatial cross term negative, so diagonal summation still needs an index/trace bridge.
- 2026-08-13 — corrected the raw localized quadratic scale.  Linear Ward mass plus
  Cauchy--Schwarz shows that an `O(N)` energy estimate would force density one; the exact `75%`
  threshold on a two-sided length-`2T` window is `pi^2 N(T,2T)^2/(8T)`.  Formalized the abstract
  and integral threshold laws in `XiWardSourceWindowMultiplicity.lean`; the remaining source
  problem now has the natural `T log^2 T` order and an honest leading-constant target.
- 2026-08-13 — closed the first-four-moment branch sharply.  The square of
  `1-(7/4)x+(2/3)x^2` is exactly `m_0-31/36` for the sine-kernel moments through order four, so the
  best resulting line certificate is `13/18`, not `3/4`; the two-atom equality measure proves
  sharpness.  Also rejected direct transfer of the `0.6792` signed-tail SDP to a positive
  off-RH frame and the high-horizontal-derivative Ward route, whose effective prime length
  recreates the bandwidth-one barrier.
- 2026-08-13 — proved the exact annular zero-mode obstruction `(Z0)`--`(ZD)`: its positive
  diagonal coexists with zero total spatial mass, so dense uniform ordinate packets close the
  diagonal-aggregation route.  Then conjectured and formalized the Plucker--Ward renormalized atom
  `(PW2)`--`(PW3)`.  Squared inverse-displacement Cauchy growth cancels the exact quadratic Gabor
  coalescence and yields a strict displacement-uniform quantum for every off-line copy.  Remaining
  core is source-side nonlinear aggregation without selecting unknown zero nodes; no proportion
  improvement is claimed.
- 2026-08-13 — proved the forced singularity of every displacement-uniform boundary separator and
  formalized the multiplicity-exact shallow-layer Cauchy law `(SL1)`--`(SL3)`.  All cross terms are
  positive, so the annular zero-mode obstruction disappears.  Formalized the exact 75% receiver
  `(SL5)`.  Source audit leaves one non-circular analytic core: at `h asymp 1/log T`, bound the
  aperture-tangent Cauchy energy plus the deep census by `N/8`.  Existing finite-aperture
  contractivity and Fejer deconvolution do not supply the tangent outer-product covariance.
- 2026-08-13 — retained critical-line diagonal mass inside reflection absorption and formalized the
  hybrid source estimate `(HD1)`--`(HD3)`.  Global constant audit shows its linear Poisson charge
  reproduces natural divisor multiplicity and cannot improve `0.6725` alone.  Extracted two
  positive survivors: the exact finite-band sandwich `(PW4)` and FE reflection curvature
  `(RC1)`--`(RC3)`, both giving displacement-uniform positive-shift charge after the forced
  inverse-square normalization.  Remaining gap is source aggregation of that singular tangent,
  not local separation or critical-multiplicity bookkeeping.

## Log-scale Hellinger--Cauchy separator

`[PAPER-PROVED; LEAN-PROVED] [BRIDGE] [NOT RH] [NO COMPUTATION]`

The finite-band and finite-prime detectors above are continuous at horizontal displacement zero.
They therefore lose every uniform quantum when an off-line pair approaches the critical line.
Inverse-square normalization repairs one atom but introduces zero-adapted singular weights.  A
scale-invariant alternative is to accumulate one fixed dyadic semigroup difference over every
positive horizontal scale.

For `a >= 0` and `r > 0`, define

```text
q_a(r) = exp(-a r) - exp(-2 a r).                         (LP1)
```

Then `q_0=0`.  For `a,b>0`, its logarithmic-scale Gram kernel is

```text
K(a,b)
 = integral_(0,infinity) q_a(r) q_b(r) dr/r
 = log [((a+2b)(2a+b))/(2(a+b)^2)].                       (LP2)
```

The integral converges: at zero its integrand is `O(ab r)`, while at infinity it decays
exponentially.  Expanding the product and grouping it into two Frullani differences gives

```text
K(a,b)
 = integral [exp(-(a+b)r)-exp(-(a+2b)r)] dr/r
   + integral [exp(-2(a+b)r)-exp(-(2a+b)r)] dr/r
 = log((a+2b)/(a+b)) + log((2a+b)/(2(a+b))),
```

which is `(LP2)`.  Moreover

```text
(a+2b)(2a+b) - 2(a+b)^2 = ab,                            (LP3)
```

so `K(a,b)>0` for every `a,b>0`, and

```text
K(a,a)=log(9/8)                                           (LP4)
```

for every `a>0`, independently of its size.  The boundary value is exactly zero when either
argument is zero.  Thus the discontinuity required by the existing singularity barrier is not
inserted as an inverse power of a named zero depth: it is generated by non-uniform accumulation
over all logarithmic scales.

For `h>0`, the vertical damped characters have real Gram kernel

```text
Re integral_0^infinity
  exp(-h t/2-i gamma t) exp(-h t/2+i eta t) dt
 = h/[h^2+(gamma-eta)^2].                                (LP5)
```

Tensoring `(LP1)` with these characters therefore gives the positive pair kernel

```text
Q_h(a,b;gamma-eta)
 = K(a,b) h/[h^2+(gamma-eta)^2].                         (LP6)
```

Let a finite strict-right packet have depths `a_j>0`, ordinates `gamma_j`, and positive integral
multiplicities `m_j`.  Define

```text
E_h^LP
 = sum_(j,k) m_j m_k Q_h(a_j,a_k;gamma_j-gamma_k).        (LP7)
```

Every summand in `(LP7)` is positive.  Its diagonal is

```text
m_j^2 Q_h(a_j,a_j;0) = m_j^2 log(9/8)/h.
```

Hence

```text
sum_j m_j
 <= sum_j m_j^2
 <= h/log(9/8) E_h^LP.                                   (LP8)
```

This proves a multiplicity-faithful separator for every positive real shift, with no shallow-depth
restriction, no zero-adapted scale, no negative cross channel, and exact exclusion of critical
multiplicity.

The corresponding exact three-quarters receiver is

```text
h/log(9/8) E_h^LP(T) <= N(T,2T)/8
  ==> N_0(T,2T) >= 3 N(T,2T)/4.                          (LP9)
```

### Hostile audit and novelty boundary

1. A fixed finite family of Gabor/Weil windows cannot reproduce `(LP4)`: its zero-side block is
   continuous in `a` and an off-line reflected pair converges to an on-line double zero as
   `a->0`.  This branch is `[FALSIFIED]` by continuity and by the existing bandwidth-one collision
   audit.
2. A finite prime cutoff also cannot reproduce `(LP4)`: the proved reflected Hellinger profile
   vanishes when `a log N -> 0`.  Taking `N` from `a` would be zero-adapted selection.
3. `(LP2)` is classical Frullani/Littlewood--Paley semigroup calculus.  No novelty is claimed for
   the integral identity or positivity.  Corpus novelty is only the bridge to the precise
   submicroscopic multiplicity obstruction exposed by the Zeta-23 audit.
4. `(LP8)` is zero-side and unconditional, but not yet an Euler--Gamma source estimate.  The open
   core is to realize the full `dr/r` square function from one pre-spectral prime--Gamma source and
   bound its height-window mass.  Assuming that bound only on named Xi zero packets would be the
   forbidden RH-bearing descent in new notation.
5. The all-scale integral is essential.  Any compact scale interval makes the diagonal tend to
   zero with `a`, returning to the continuous-detector barrier.

### Status

- `[FORMALIZED MULTISCALE SEPARATOR]` `(LP1)`--`(LP8)` in
  `XiWardMultiscaleHellingerCauchySeparator.lean`.
- `[FORMALIZED 75% RECEIVER]` `(LP9)` using `N=N_0+2R`.
- `[OPEN SOURCE CORE]` construct and bound the pre-spectral Euler--Gamma logarithmic-scale square
  function.  No density improvement is claimed before that bound is unconditional.
- 2026-08-13 — conjectured the logarithmic-scale dyadic semigroup separator, hostile-tested it
  against finite-band collision and finite-prime critical-window laws, and closed the exact
  finite-packet proof.  Formalized the kernel positivity, fixed `log(9/8)` diagonal, all-depth
  multiplicity law, Xi specialization, and `75%` receiver in
  `XiWardMultiscaleHellingerCauchySeparator.lean`; targeted build and standard-axiom audit pass.

## All-scale Euler-source wall no-go

`[CONJECTURE FALSIFIED] [POSITIVE SURVIVOR LEAN-PROVED] [NO COMPUTATION]`

The natural next conjecture was that the full logarithmic-scale Gram in `(LP7)` has a finite
pre-spectral realization inside the corpus's biorthogonal Euler primitive source.  That conjecture
fails for the same scale-invariance that makes `(LP4)` useful.

For a prime-valuation label `pe=(p,e)`, put

```text
n_pe = p^(e+1),
lambda_pe = log n_pe > 0.
```

The existing source/co-source product at balanced reflection is exactly

```text
W_pe
 = sourceCoeff(a,pe) star(coSourceCoeff(-a,pe))
 = Lambda(n_pe)/n_pe.                                   (ES1)
```

It is independent of `a`, and its prime-level subseries is `log p/p`.  Apply the horizontal
all-scale Gram to the source frequency `lambda_pe`.  By `(LP4)`,

```text
D_pe
 = K(lambda_pe,lambda_pe) W_pe
 = log(9/8) W_pe.                                       (ES2)
```

The constant is strictly positive.  Since the balanced Euler coefficients in `(ES1)` are not
summable, neither are the all-scale diagonal coefficients `(ES2)`:

```text
not Summable(pe |-> D_pe).                              (ES3)
```

This proves the exact obstruction.  A Hilbert/trace source map retaining the complete `dr/r`
diagonal at the balanced reflection wall cannot have finite norm.  The all-scale zero separator
does not evade the source descent problem; it lands canonically on its nonsummable boundary.

### No-go closure

- **Exact killing mechanism:** dilation invariance makes the diagonal independent of zero depth,
  but also independent of prime-log frequency.  It therefore preserves the divergent critical
  von Mangoldt mass rather than damping it.
- **Strongest positive survivor:** the same fixed constant `log(9/8)` is the exact conversion
  factor on both sides.  Uniform submicroscopic zero charge and nonsummable balanced Euler charge
  are two faces of one scale-invariant law.
- **New insight:** any viable source theorem must be a renormalized/cofinal height-window law, not
  a finite global Hilbert bound.  Compact scale truncation is finite but returns to the continuity
  barrier; its upper scale must diverge and its Euler wall mass must be subtracted or compared
  before the limit.
- **Status:** paper proof and Lean formalization complete using the already formalized
  balanced-reflection coefficient identity and nonsummability theorem.  Declarations
  `xiGammaEulerPrimitiveDyadicAllScaleDiagonal_eq_vonMangoldtWeight` and
  `not_summable_xiGammaEulerPrimitiveDyadicAllScaleDiagonal` are in
  `XiWardMultiscaleEulerSourceDivergence.lean`.  The survivor does not prove a density improvement.

- 2026-08-13 — tested the full all-scale source realization against the actual primitive
  source/co-source carrier.  Falsified finite source norm by `(ES1)`--`(ES3)`, formalized the exact
  nonsummability theorem, and isolated the renormalized cofinal source wall as the remaining route.

## Cubic log-moment separator: finite Euler diagonal with submicroscopic gain

`[OWN CONJECTURE PAPER-PROVED] [SOURCE-DIAGONAL WALL REMOVED] [NO COMPUTATION]`

The all-scale no-go uses the dilation-invariant measure `dr/r`.  It is stronger than needed on the
zero side: zeta horizontal depths lie in `0<a<1/2`, whereas Euler frequencies
`lambda=log(p^(e+1))` are unbounded.  Weighting small logarithmic scales by three additional powers
of `r` separates these two regimes without truncating the large scales needed when `a->0+`.

For `a,b>0`, define the cubic log-moment Gram

```text
C(a,b)
 = integral_0^infinity r^2
     (exp(-ar)-exp(-2ar))(exp(-br)-exp(-2br)) dr.        (CM1)
```

The integrand is strictly positive.  Since

```text
integral_0^infinity r^2 exp(-x r) dr = 2/x^3,
```

termwise integration gives

```text
C(a,b)
 = 2/(a+b)^3 - 2/(a+2b)^3
   - 2/(2a+b)^3 + 2/(2a+2b)^3.                         (CM2)
```

Writing `s=a+b` and `p=ab`, the same quantity has manifestly positive closed form

```text
C(a,b)
 = 9 p (20 s^4+6 s^2 p+p^2)
     / [4 s^3 (2s^2+p)^3].                             (CM3)
```

Indeed `(a+2b)(2a+b)=2s^2+p`, their sum is `3s`, and clearing denominators in `(CM2)` leaves
`9p(20s^4+6s^2p+p^2)`.  Equations `(CM2)` and `(CM3)` are therefore identical.  Totalize
`C(a,b)=0` if `a=0` or `b=0`; this excludes critical-line multiplicity exactly.

On the diagonal,

```text
C(a,a) = 115/(864 a^3).                                (CM4)
```

Hence every strict-right zeta zero, for which `0<a<1/2`, has uniform charge

```text
C(a,a) > 115/108,                                      (CM5)
```

and the charge diverges rather than vanishes as `a->0+`.  This is stronger than the fixed
`log(9/8)` quantum of `(LP4)` and retains the required submicroscopic separation.

Tensor `(CM1)` with the vertical Cauchy Gram

```text
V_h(gamma-eta)=h/[h^2+(gamma-eta)^2],  h>0.             (CM6)
```

For a finite strict-right packet with multiplicities `m_j`, define

```text
E_h^CM = sum_(j,k) m_j m_k C(a_j,a_k)
           V_h(gamma_j-gamma_k).                        (CM7)
```

Every mixed entry is positive.  By `(CM5)`, the diagonal alone yields

```text
E_h^CM >= (115/(108h)) sum_j m_j^2
        >= (115/(108h)) sum_j m_j,

sum_j m_j <= (108h/115) E_h^CM.                        (CM8)
```

Thus the exact density receiver is

```text
(108h/115) E_h^CM(T) <= N(T,2T)/8
  ==> N_0(T,2T) >= 3 N(T,2T)/4.                         (CM9)
```

The decisive source improvement is that `(CM4)` decays cubically at Euler frequencies.  For the
literal balanced primitive source, `n=p^(e+1)`, `lambda=log n=(e+1)log p`, and
`W_(p,e)=Lambda(n)/n=log(p)/p^(e+1)`.  Therefore its cubic-moment diagonal is exactly

```text
D_(p,e)
 = C(lambda,lambda) W_(p,e)
 = 115 / [864 (e+1)^3 p^(e+1) (log p)^2].              (CM10)
```

This family is summable.  Since `p>=2` and `e+1>=1`,

```text
0 <= D_(p,e)
 <= (115/864) [1/(p (log p)^2)] (1/2)^e.               (CM11)
```

The prime factor is a subseries of the convergent integer series
`sum_(n>=2) 1/[n(log n)^2]`; the depth factor is geometric.  Tonelli comparison proves

```text
Summable((p,e) |-> D_(p,e)).                            (CM12)
```

### Hostile audit and remaining gate

1. This is not a compact-scale smoothing.  The integral still reaches arbitrarily large `r`, so
   `(CM4)` strengthens at submicroscopic displacement instead of collapsing by continuity.
2. It does not subtract a Gamma scalar or add finite rank.  The repair is an infinite-dimensional
   source-domain change before the norm: small `r` is suppressed polynomially, exactly where
   high prime-log frequencies live.
3. It evades `(ES3)` for a structural reason, not cancellation: the Euler diagonal changes from
   `Lambda(n)/n` to `Lambda(n)/[n(log n)^3]` and becomes positive summable.
4. It does **not** yet prove `(CM9)` for Xi.  Missing theorem is a source-faithful height-local
   Euler--Gamma landing/upper bound identifying or dominating the zero-side Gram `(CM7)` by this
   finite cubic-moment source trace.  Diagonal summability removes the previous global Hilbert
   obstruction but does not manufacture that comparison.

### Status

- `[PAPER-PROVED NEW MECHANISM]` `(CM1)`--`(CM12)`.
- `[FORMALIZED CUBIC SEPARATOR]` literal cubic Gram integral, positive closed kernel, exact
  `115/(864a^3)` self-charge, finite-packet census, `75%` receiver, exact balanced Euler
  coefficient, and complete source-diagonal summability.
- `[OPEN CORE]` completed Euler--Gamma source-to-zero cubic-moment trace inequality with dyadic
  height localization and threshold `(CM9)`.

- 2026-08-13 — replaced the falsified scale-invariant source trace by the cubic log-moment Gram.
  Paper proof gives uniform/submicroscopically increasing zero charge and, for the first time in
  this branch, a positive summable balanced Euler diagonal on the literal primitive carrier.
  Formalized `(CM1)`--`(CM12)` in
  `XiWardCubicLogMomentHellingerCauchySeparator.lean` and
  `XiWardCubicLogMomentEulerSource.lean`; targeted builds and standard-axiom audits pass.

## Regular cubic landing no-go

`[OWN CONJECTURE FALSIFIED] [POSITIVE SURVIVOR TO FORMALIZE] [NO COMPUTATION]`

Freeze the tempting next conjecture:

```text
[CONJECTURE REGULAR-CM-LANDING]
The summable balanced Euler diagonal `(CM12)` extends through a bounded regular
source-to-zero operator whose one-copy diagonal is `(CM4)` and whose critical-line
value is the totalized value zero.
```

This conjecture is false independently of any global trace constant.  Let

```text
F(a)=C(a,a).
```

Then `F(0)=0`, whereas for every `0<a<=1/2`, `(CM4)` gives

```text
F(a)=115/(864a^3) >= 115/108 > 0.
```

Thus `F` is not continuous at zero.  More strongly, it diverges cubically along the positive
boundary.  A bounded regular Hilbert/source landing has a continuous diagonal matrix coefficient,
so it cannot realize or dominate this atom while retaining value zero on critical multiplicity.
Diagonal summability is therefore necessary source-domain admission only; it is not closability,
boundedness, or a source-to-divisor comparison.

### No-go closure

- **Exact killing mechanism:** cubic source weighting suppresses high prime-log coordinates, but
  the same Mellin homogeneity creates the singular zero-side factor `a^(-3)`.  Totalization at
  `a=0` turns that factor into a discontinuous boundary selector.
- **Strongest positive survivor:** a source landing may still exist as a singular closed graph,
  boundary current, or cofinal renormalized trace.  Its domain and height-local norm must be
  constructed before divisor evaluation; ordinary bounded continuation is ruled out.
- **New invariant:** source-diagonal summability and boundary closability are logically independent
  gates.  Future kernels must be audited against both.
- **Falsifier for every successor:** if the proposed producer is bounded/continuous at the critical
  boundary and its atom vanishes there, it cannot have a displacement-uniform positive quantum.

- 2026-08-13 — froze and falsified `REGULAR-CM-LANDING`.  The cubic kernel's exact self law makes
  its totalized boundary diagonal discontinuous, so no bounded regular landing can supply `(CM9)`.
  Singular graph/current aggregation remains open.

## Cubic holomorphy / entrywise-positivity trilemma

`[CUBIC LANDING ROUTE RETIRED] [POSITIVE NO-GO SURVIVOR LEAN-PROVED] [NO COMPUTATION]`

The cubic packet `(CM7)` was built by tensoring an independently horizontal kernel `C(a,b)` with
an independently vertical Cauchy kernel.  That decoupling is exactly what makes every mixed entry
strictly positive.  It is not, however, a one-complex-variable Euler--Gamma Laplace kernel.

First, every vertically translation-covariant one-variable Laplace kernel has horizontal
restriction determined by the combined abscissa `a+b`.  The cubic Hellinger kernel fails this
necessary test: the pairs `(a,b)=(1,1)` and `(1/2,3/2)` have the same sum but different values.
Lean proves the exact universal negation

```text
not exists F, forall a,b>0, C(a,b)=F(a+b).
```

Second, restoring the holomorphic coupling by using the genuine cubic Laplace feature
`r exp(-zr)` gives cross entry

```text
Re [2/(x+i delta)^3]
 = 2x(x^2-3delta^2)/(x^2+delta^2)^3.                    (HT1)
```

This is negative whenever `x^2<3delta^2`; at the exact witness `(x,delta)=(1,1)` it equals
`-1/2`.  Therefore the source-compatible cubic kernel loses the entrywise positivity needed to
discard cross terms and charge multiplicity by its diagonal.

The resulting trilemma is exact:

1. unweighted holomorphic Cauchy energy is entrywise positive, but its balanced Euler diagonal is
   nonsummable;
2. cubic holomorphic energy has a summable Euler diagonal, but signed cross entries;
3. cubic horizontally split tensor energy has positive cross entries and a summable formal
   diagonal, but is neither a one-variable translation-covariant landing nor boundary-closable.

### No-go closure

- **Exact killing mechanism:** the two properties advertised by `(CM7)` come from incompatible
  analytic realizations.  Cubic damping and phase-noncancellation cannot both be inherited from
  the one-variable completed Euler--Gamma source by this tensor.
- **Strongest positive survivor:** the cubic kernel remains a valid abstract finite-packet
  separator and Euler-coordinate admission test.  A successor needs an intrinsically two-variable
  source current with its own arithmetic trace theorem, or a new signed-index inequality that uses
  the negative holomorphic cross channel instead of discarding it.
- **Status:** the cubic route is retired as a direct source-to-zero landing.  Lean declarations
  `not_exists_cubicLogMomentHellingerHorizontalKernel_eq_fun_add`,
  `holomorphicCubicLaplaceCrossKernel_neg`, and
  `holomorphicCubicLaplaceCrossKernel_one_one` certify the two algebraic obstructions.

- 2026-08-13 — applied the one-variable holomorphy falsifier.  Decoupled cubic positivity fails
  the combined-abscissa test; the source-compatible cubic replacement has explicit negative cross
  entries.  Direct cubic landing retired, with two-variable current/signed-index successors left.

## Cubic height-Bohr fibre and reciprocal-translation gate

`[OWN CONJECTURE HOSTILE-TESTED] [FINITE SURVIVOR LEAN-PROVED] [SOURCE LANDING OPEN]`
`[NO COMPUTATION]`

The signed cross entries in `(HT1)` can be removed without changing the holomorphic cubic
kernel at equal ordinates.  For a finite strict-right packet write

```text
z_j=a_j+i gamma_j,       0<a_j<=1/2,
K_(j,k)=2/(a_j+a_k+i(gamma_j-gamma_k))^3.
```

Phase-modulate the packet by the single global parameter `tau` and form

```text
E(tau)=sum_(j,k) m_j m_k K_(j,k)
          exp(-i(gamma_j-gamma_k)tau).                    (HB1)
```

This is the Gram energy of the cubic Laplace features
`r exp(-(a_j+i gamma_j)r)` after multiplying the `j`-th feature by
`exp(-i gamma_j tau)`.  Character orthogonality gives the exact Bohr mean

```text
M_tau E(tau)
 = sum_(j,k: gamma_j=gamma_k)
     2 m_j m_k/(a_j+a_k)^3.                              (HB2)
```

Every retained entry is positive.  Its diagonal is `m_j^2/(4a_j^3)>=2m_j^2>=2m_j`, so

```text
2 sum_j m_j <= M_tau E(tau).                             (HB3)
```

If `R(T,2T)` is strict-right multiplicity and a pre-divisor arithmetic construction proved

```text
M_tau E_T(tau) <= N(T,2T)/4+o(N(T,2T)),                  (HB4)
```

then `(HB3)` gives `2R<=N/4`, hence
`N_0=N-2R>=3N/4`.  This uses the source-compatible holomorphic cubic kernel, retains all
same-ordinate multiplicity cross terms, and removes the negative distinct-ordinate channel
exactly rather than estimating it.

### Hostile source-visibility test

The phase in `(HB1)` cannot be inserted by scalar normalization of ordinary holomorphic vertical
translation.  For the right-half-plane point `a+i gamma`, genuine translation has character

```text
H_tau(a,gamma)=exp(-tau(a+i gamma)),
|H_tau(a,gamma)|=exp(-tau a),                            (HB5)
```

whereas the dephasing character has modulus one.  For every `tau>0`, no scalar `c(tau)` independent
of `a` can make both `|c H_tau(1,0)|` and `|c H_tau(2,0)|` equal one: strict monotonicity of the real
exponential makes the two norms unequal.  Therefore `(HB2)` is a valid finite-divisor theorem but
post-divisor phase insertion is not the missing Euler--Gamma proof.

The corpus's reciprocal-character theorem identifies the only surviving regular symmetry
mechanism.  Full FE translation acts on an off-line pair by the reciprocal characters

```text
exp(t(a+i gamma)),       exp(t(-a+i gamma)).             (HB6)
```

Their invariant Hermitian pairing cancels the real boost exactly.  Distinct character sectors are
orthogonal, every `a>0` pair is one hyperbolic block, and the `a=0` unitary sector admits the
positive quotient.  This gives qualitative submicroscopic separation by Krein index, already
formalized in the character/fusion corpus.  It does not give `(HB4)`.

### Frozen successor conjecture

```text
[CONJECTURE CUBIC-RECIPROCAL-BOHR-SOURCE-TRACE]
For every dyadic zero window there is a completed prime--Gamma two-leg trace,
defined before divisor expansion on the reciprocal joint prime/depth carrier,
whose invariant/Krein codiagonal has zero-side Bohr mean `(HB2)` and whose
arithmetic trace is at most `N(T,2T)/4+o(N(T,2T))`.
```

Mandatory falsifiers:

1. both source legs and the reciprocal translation action must be fixed before evaluating a Xi
   zero or its ordinate;
2. the finite arithmetic trace must reproduce the literal von Mangoldt/Gamma coefficients, not
   only an abstract hyperbolic block;
3. the construction must survive the balanced-codiagonal nonsummability wall by explicit
   renormalization, not by assuming an ordinary Hilbert pairing there;
4. height localization must remain dyadic before the Bohr/cofinal limit; a global mean that loses
   the `T` window does not imply `(HB4)`;
5. its index/trace estimate must be proved from arithmetic structure.  Defining the trace from the
   zero Gram or assuming its `N/4` budget is circular.

Lean module `XiWardCubicHeightBohrFiber.lean` proves `(HB2)`, `(HB3)`, the exact `75%` receiver,
the norms in `(HB5)`, and the scalar-normalizer impossibility.  The conjectured reciprocal
prime--Gamma trace and bound `(HB4)` remain open.

- 2026-08-13 — replaced the invalid claim that ordinary holomorphic translation supplies pure
  height phases by the exact finite Bohr-fibre theorem and isolated reciprocal Krein translation
  as the only source-compatible successor.  Formalization is axiom-auditable; no `75%` claim is
  made without `(HB4)`.

## Reciprocal invariant-Bohr conjecture falsified

`[OWN CONJECTURE FALSIFIED] [POSITIVE DICHOTOMY LEAN-PROVED] [NO COMPUTATION]`

The frozen conjecture required one invariant reciprocal Krein codiagonal to retain the pure
ordinate phases in `(HB1)`.  These requirements are algebraically incompatible.  For common
vertical translation

```text
V_tau(z)=z+i tau
```

the literal joint-depth source coefficient factors through `w+conj(v)`, and

```text
V_tau(w)+conj(V_tau(v))=w+conj(v).                       (KB1)
```

Thus every scalar observable of the actual codiagonal—including the von Mangoldt Laplace channel
and its Krein matrix coefficient—is constant in `tau`.  The reciprocal Hermitian pairing does not
cancel only the real boost: invariance cancels the ordinate character at the same time.  Its Bohr
mean therefore retains every term and cannot produce the equal-ordinate projection `(HB2)`.

Opposite translation is the exact alternative:

```text
V_tau(w)+conj(V_(-tau)(v))=w+conj(v)+2i tau.             (KB2)
```

This remains source-visible, but it moves the scalar Xi resolvent parameter.  On the zero side it
translates Cauchy poles; it does not multiply each fixed divisor residue by
`exp(-i gamma tau)`.  Hence `(KB2)` supplies a vertical resolvent moment problem, not the finite
fibre dephasing identity `(HB2)`.

### No-go closure

- **Killing mechanism:** conjugate-codiagonal invariance erases real and imaginary character
  components together.  No invariant reciprocal codiagonal can be a nonconstant height phase.
- **Strongest survivor:** source-faithful height motion is the opposite-shift channel `(KB2)`.
  A successor must extract a connected/dyadically localized vertical resolvent trace from that
  channel and prove Gamma-baseline cancellation; it cannot reuse the invariant-Bohr claim.
- **Formal certificate:** `kreinCommonVerticalShift_codiagonal`,
  `kreinCodiagonalObservable_commonVerticalShift_invariant`,
  `xiGammaEulerPrimitiveJointDepthKreinPair_commonVerticalShift`,
  `kreinOppositeVerticalShift_codiagonal`, and
  `xiGammaEulerPrimitiveJointDepthKreinPair_oppositeVerticalShift` in
  `XiWardCubicHeightBohrFiber.lean`.
- **Status:** `CUBIC-RECIPROCAL-BOHR-SOURCE-TRACE` is retired.  Open core pivots from invariant
  Bohr dephasing to a non-invariant connected prime--Gamma vertical resolvent estimate.

## Fixed-translation energy successor

`[OWN CONJECTURE SURVIVES FINITE AUDIT] [LEAN-FORMALIZED] [NO 75% CLAIM] [NO COMPUTATION]`

The reciprocal-codiagonal no-go does not exhaust fixed source translations.  It applies to one
linear invariant joint-depth coefficient.  A nonlinear two-scale energy observable on a single
Hedenmalm conormal fibre has different covariance.

For the fixed normalized real translation

```text
T_L f(x)=exp(-L/2) f(x+L),
ell_z(T_L f)=exp(-L(1/2+i z)) ell_z(f),                 (SG1)
```

define its centered energy gain

```text
G_L(z)=exp(L)|exp(-L(1/2+i z))|^2=exp(2L Im z).         (SG2)
```

At `rho=1/2+a+i gamma`, the centered spectral point is `z=gamma-i a`, so the fixed source
energy difference at scales `r/2` and `r` is

```text
G_(r/2)(z)-G_r(z)=exp(-a r)-exp(-2a r).                 (SG3)
```

Thus the cubic Hellinger feature is not a post-divisor insertion and not a zero-adapted
normalization.  It is an exact difference of two fixed source-energy measurements.  It vanishes
identically for `a=0`, is positive for every `a,r>0`, and its `r^2 dr` Gram is exactly the cubic
kernel `C(a,b)`.  In particular its self-charge remains `115/(864a^3)>=115/108` throughout the
strict-right half-strip.

The vertical phase has a second fixed-source realization.  Apply one normalized integer shift on
each of the line-conjugate evaluation fibres `(z,conj z)` and multiply by `n`.  Horizontal
magnitudes cancel exactly and the gain is

```text
exp(-2 i Re(z) log n)=exp(-2 i gamma log n).            (SG4)
```

Logarithmic harmonic correlation of `(SG4)` converges to the equality projector on ordinates.
For every finite packet, the combined cubic trace therefore converges to

```text
sum_(j,k: gamma_j=gamma_k) m_j m_k C(a_j,a_k).          (SG5)
```

Every term in `(SG5)` is nonnegative and its diagonal gives

```text
(115/108) sum_j m_j <= (SG5).                           (SG6)
```

This construction evades both prior no-go theorems for a precise reason: `(SG3)` is nonlinear in
the conormal evaluation, and `(SG4)` uses two line-conjugate evaluation fibres rather than the
invariant Krein codiagonal.  It does not claim a bounded linear landing at the critical boundary.

### Exact remaining gate

The finite mechanism is not yet an unconditional density theorem.  Required source statement is
now a concrete four-leg correlation theorem:

```text
[OPEN SOURCE-GENERATED CUBIC TRACE BUDGET]
Construct a completed dyadic Euler--Gamma trace, before divisor expansion, whose divisor landing
is `(SG5)`, prove its critical-rigging closure, and prove

(108/115) E_T <= N(T,2T)/8+o(N(T,2T)).                 (SG7)
```

The previously proved summable Euler diagonal is necessary but does not supply the nonlinear
trace identity, Gamma-baseline cancellation, or `(SG7)`.  No arithmetic upper bound has been
assumed or encoded as an interface.

Lean modules:

- `XiWardCubicTranslationEnergySeparator.lean` proves `(SG1)`--`(SG3)` and the exact cubic Gram;
- `XiWardCubicIntegerHarmonicDephasing.lean` proves `(SG4)` and the harmonic projector, including
  actual Xi-ordinate specialization;
- `XiWardCubicSourceGeneratedHarmonicSeparator.lean` proves `(SG5)`, `(SG6)`, nonnegativity, and
  the exact 75% receiver.

- 2026-08-13 — replaced the false invariant-codiagonal successor by fixed translation-energy and
  line-conjugate tensor observables.  Horizontal and vertical separator factors now have exact
  pre-divisor source origins.  The only unproved density input is the completed four-leg
  Euler--Gamma trace construction and quantitative dyadic budget `(SG7)`.

## Five-shift prime-gap Euler--Gamma separator

`[OWN CONJECTURE LEAN-PROVED POINTWISE] [EXACT WEIL--KREIN LANDING]`
`[COMPLETE CRITICAL-KERNEL PRIME--GAMMA POLARIZATION] [DENSITY BUDGET OPEN]`

The cubic route used a positive horizontal Gram but failed one-variable holomorphic source
compatibility.  A different construction starts from the literal gap between the first two Euler
frequencies.  For `r>0`, set

```text
q=e^(-2r),  t=e^(-(6/5)r),  u=e^(-(21/10)r),  x=e^(-2ar),
P_r(a)=x(1-x)(x-t)(x-q)(x-u).                           (FS1)
```

The strict inequalities

```text
3/5 < log 2 < 1 < 21/20 < log 3
```

make `(FS1)` positive on every zeta displacement `0<a<=1/2`, zero at `a=0`, and nonpositive at
every Euler depth `a=log n`, `n>=2`.  Coefficient expansion also gives two exact moment
cancellations: ordinary coefficient sum zero and `e^(-2r)`-weighted sum zero.  These are the two
Gamma-tail cancellations missing from the earlier four-shift attempt.

Functional-equation pairing gives

```text
D_r(a)=-(P_r(a)+P_r(-a)),
R_r(a)=a^(-2)D_r(a),
R_1(a)>=1/81  for 0<a<=1/2,      R_1(0)=0.              (FS2)
```

On every actual Xi multiplicity copy, `D_r(a)` is exactly one weighted combination of the five
reflection-difference norm squares

```text
||F_(kr)(lambda)-F_(kr)(conj lambda)||^2, k=1,...,5.    (FS3)
```

Thus `(FS2)` has an unconditional multiplicity-exact Weil--Krein landing.  It gives the exact
finite `75%` receiver once an arithmetic bound `81E<=N/8` is supplied; that bound is not assumed.

The pointwise critical rigging is also explicit.  For a real-centered Hedenmalm feature,

```text
ell_z(k_t)=2/[1+(z-t)^2]
          = i C_(t-i)(z)-i C_(t+i)(z).                 (FS4)
```

Both Cauchy poles are in Deninger's strict absolute-Euler sectors.  Cross terms in the Weil
polarization are exact Deninger source cups.  The initially suspected missing same-orientation
terms are not genuinely continued-source terms: oddness of `XiC'/XiC` folds them to lower
absolute-Euler divided differences at the opposite real center.  Consequently Lean proves a
complete four-term prime--Gamma formula for the polarization of `(FS4)`.

This does not yet Hermitianize `(FS3)`.  Weil polarization is holomorphic/Krein; `(FS3)` is a
Euclidean negative-sector energy.  The remaining theorem is therefore precise:

```text
[OPEN FIVE-SHIFT HERMITIAN SOURCE BUDGET]
Construct a height-local, source-native inverse-Green or rank--trace current whose zero landing is
the normalized pair-difference charge `(FS2)`--`(FS3)`, and prove its dyadic arithmetic cost is at
most N(T,2T)/8.
```

Boundary rigidity is now proved: `R_1` cannot be continuous at zero, and no continuous
diagonal-vanishing source coefficient can agree with it on the positive half-strip.  Any completion
must therefore retain an unbounded tangent/Green graph or discontinuous index channel; a bounded
regular source operator is ruled out.

Lean modules are umbrella-wired:

- `XiWardFiveShiftEulerGammaPrimeGap.lean`;
- `XiWardFiveShiftEulerGammaQuantitative.lean`;
- `XiWardFiveShiftPairedSubmicroscopicSeparator.lean`;
- `XiWardFiveShiftWeilKreinLanding.lean`;
- `HedenmalmCriticalFeatureKernel.lean`;
- `HedenmalmCriticalFeaturePrimeGammaDecomposition.lean`;
- `XiWardFiveShiftCriticalEvaluationLanding.lean`;
- `XiWardFiveShiftBoundaryRigidity.lean`.

Important guardrail: the theorem giving Euler nonpositivity under `-Im z=log n` inside the
critical-evaluation module has incompatible strip hypotheses for `n>=2`.  It is a valid formal
implication but not a literal critical-rigging Euler sample.  Euler sign belongs to polynomial
symbol `(FS1)` until a genuine source trace evaluates it.

- 2026-08-13 — conjectured the five-shift prime-gap polynomial, proved its zeta/Euler sign split,
  two Gamma-tail cancellations, quantitative inverse-square quantum, exact Weil--Krein landing,
  explicit nonvanishing Hedenmalm kernel, complete four-term absolute-Euler prime--Gamma
  polarization, and forced boundary discontinuity.  No unconditional density improvement is
  claimed; open core is the height-local Hermitian source budget above.
