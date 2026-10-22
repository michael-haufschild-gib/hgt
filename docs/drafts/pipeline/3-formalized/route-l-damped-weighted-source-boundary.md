# Route L: weighted source, literal Mellin values and original circle boundary

- **ID:** L-C44
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** same-source admission / exact surviving boundary
- **Depends on:** [C43 half-density source](route-l-damped-half-density-source-limit.md)
- **Lean:** `formal/GaloisForLFunctions/RHTower/Deninger/DeningerDampedWeightedSourceBoundary.lean`
- **RH status:** unproved

Chain: complete original Green/BV source → agreement with the fixed physical
reader → conormal vanishing → RH. This result closes actual weighted L1
admission and literal zeroth Mellin readings of C43's limit. At damping two,
it identifies a nonzero boundary on every original prime circle. It does
not provide complete Green/BV admission or fixed-reader agreement.

## Conjecture, proof and pivot

**Compatible weighted limits: proved.** For the original finite source g_N,
put `H_c g_N(t)=exp(c*t)g_N(t)`. The literal paired prime operator becomes

`(Id-u_p U_(-log p))(Id-v_p U_(log p))`,
`u_p=p^(-(a+c))`, `v_p=p^(-(a+1-c))`.

Here `U_d f(t)=f(t-d)`; the repository translation parameter has the opposite
sign. Translation is an L1 isometry. For the admitted strip `1-a<c<a`, both
prime exponent series are summable and their terms are below one. Hence

`||E_p f|| <= exp(u_p+v_p)||f||`,
`||E_p f-f|| <= 2*(u_p+v_p)||f||`.

The exact original-prime successor identity, uniform prefix bound and
summable successive differences prove L1 convergence. The successor identity
is recovered from C43 through injectivity of the actual weighted L2 map.
No operator product or source-incidence premise is used.

The identification with C43 is also proved. Choose an almost-everywhere
convergent subsequence of the half-density prefixes, then an almost-everywhere
convergent subsubsequence of the weighted L1 prefixes. The finite functions
satisfy the exponential change of weight exactly. Uniqueness of pointwise
limits identifies the representatives for every admitted c. Thus

`g_a(t)=exp(-t/2)*C43HalfDensityLimit(a)(t)`

is one source, and `exp(c*t)g_a(t)` is the actual weighted L1 limit. This proof
uses the corpus convergence-in-measure subsequence theorem, rather than
assuming continuity of an unbounded exponential multiplier. The earlier
bounded-interval exhaustion proposal was unnecessary.

**Literal Mellin formula: proved.** At `c=Re(s)`, the Mellin integral is the
Fourier evaluation of `H_c g` at `-Im(s)/(2*pi)`, a continuous L1 functional.
The actual finite integrals therefore converge to the actual integral of
g_a. Cofinality of the original prime prefixes, the corpus Euler product
and nonvanishing of zeta in `Re(z)>1` give

`M(g_a)(s)=M(g_0)(s)/(zeta(a+s)*zeta(a+1-s))`,
`M(g_0)(s)=exp((s-1/2)^2/(4*pi))`,

on `1-a<Re(s)<a`. The source is not defined by this formula. At a=1 every
actual Xi coordinate is admitted by its already-proved open-unit-strip
location, and every such literal reading is nonzero. No critical-line
location is used.

**Vanishing original circles at initial damping: disproved, with exact
positive survivor.** At a=2, c=0 and c=1 lie in the admitted interval. Thus
both g_2 and exp(t)g_2 are integrable, and its total mass M(g_2)(0) is nonzero.
For the literal original periodization

`P_L g(t)=sum_(j in Z) g(t+jL)`, `L=log(p)`,

L1 unfolding gives, for every original prime p and every integer k,

`FourierCoeff_k(P_L g_2) = (1/L)*M(g_2)(-2*pi*i*k/L) != 0`.

The reciprocal-zeta formula above gives the full exact coefficient. The
prime, harmonic k, physical circumference and Jacobian remain unchanged.
In particular, P_L g_2 is not zero almost everywhere on its full original
cell. This is a statement about the actual L1 sum, not an assumed smooth
circle representative.

A second direct boundary result is closed: there is no integrable h with
`h(t)-h(t+log(p))=g_2(t)` almost everywhere. The integral of the left side is
zero by translation invariance; the actual source's total mass is nonzero.
This excludes an integrable original undamped Green primitive for this
specific initial source. The surviving weighted source, exact Mellin formula
and all original circle coefficients are formalized; Route L is not retired.

## Exact Lean frontier

The module has 42 public theorems, 11 definitions and one abbreviation.
Main results:

- `deningerDampedWeightedL1Prefix_tendsto`
- `deningerDampedWeightedL1Limit_halfDensity_ae`
- `deningerDampedLogSource_weighted_integrable`
- `deningerDampedLogSource_mellin_integrable`, `_mellin_tendsto`, `_mellin_eq`
- `deningerDampingOne_source_xi_admission`, `_xi_ne_zero`
- `deningerDampingTwo_source_endpoint_integrable`, `_total_mass_ne_zero`
- `deningerDampingTwo_source_primeCircle_coefficient`, `_coefficient_ne_zero`, `_not_ae_zero`
- `deningerDampingTwo_source_no_integrable_primeGreen`

Scratch `lake env lean /tmp/route_l_c44_weighted.lean` check8 passed with no
diagnostics. The final `lake build GaloisForLFunctions.RHTower.Deninger.DeningerDampedWeightedSourceBoundary`
audit passed, rebuilding only this leaf (30 seconds; other graph results were
replayed). The module is wired once into `RHTower.lean`; formal lint passed.
No full/umbrella build, numerical experiment, axiom-print command or proof
placeholder was used. Logs are `/tmp/route_l_c44_weighted_check8.log`,
`/tmp/route_l_c44_weighted_build.log` and `/tmp/route_l_c44_weighted_lint.log`.
`scripts/formal_tools.py index` completed and all 54 public declarations
are present in the generated API. No owned Lean process remains.

## Remaining mathematical work

[Full literal Mellin jets and native Xi coefficient](route-l-damped-full-mellin-jets.md)
now prove polynomially weighted convergence of this same source. The
[complete packet attack](../1-in-progress/route-l-damped-complete-xi-packet.md)
remains open; individual jet convergence is not full divisor-packet convergence. Preserve original
multiplicity, first nonzero Xi coefficient, native Tate depth, horizontal
anchor and unchanged Gamma residue normalization through the full transport.

At a=1 the endpoint weights 0 and 1 lie outside this absolute estimate.
That does not prove divergence of the complete signed source. Any endpoint
cancellation argument must admit its actual arithmetic sum and boundary.
For a>1, a uniform strip bound on the prime factors is available on paper:
`|A_p|<=(1+p^-a)^2`, `|A_p-1|<=3*p^-a`. It must be applied to the complete
Xi packet before transferring C39's full Green/Tate/Sonin identities.

Damping continuation is not proved. The prospective half-density multiplier
`1/|zeta(a+1/2+i*tau)|^2` requires a source prescription at every encountered
zero, retaining multiplicity and its nonzero leading coefficient. A bound
excluding these poles cannot be assumed. Neither the initial source nor
its nonzero original-circle coefficients prove the missing physical comparison.

## Corpus and distant-paper audit

All 20 candidate lemmas and 20 source arguments in each of the following
reports were inspected; generated idea and ingredient lists were empty.

- `/tmp/route_l_c43_weighted_pole_deep.json`: generation 875519; semantic
  2354275/2354825; partial deadline, filter/judge and source refresh.
- `/tmp/route_l_c44_weighted_mellin_deep.json`: generation 875564; semantic
  2354579/2354944; same partial stages. `Lp.cauchy_complete_eLpNorm` was read,
  but the final proof uses Lp completeness and two AE subsequences instead.
- `/tmp/route_l_c44_compatible_limits_deep.json`: generation 875672; semantic
  2355164/2355164; partial deadline, filter/judge and source refresh. Bounded
  multiplication methods require bounds not available globally; no such
  bound is imported. Exact convergence-in-measure and Fourier APIs were
  recovered from current source and verified in scratch.
- `/tmp/route_l_c44_periodization_mass_deep.json`: generation 875888; semantic
  2355235/2355279; partial deadline, filter/judge and source refresh. Its
  `L1PeriodizationFourier` coefficient method was read and used. Abstract
  orbit-energy results require additional pairing/summability premises and
  were not transferred.

Broad single-word arXiv searches used `threshold`, `sewing`, `gluing` and
`interpolation`, preferring June–September 2026:

- [Alimoglu, September 7](https://arxiv.org/abs/2609.10601): threshold
  verification experiment; abstract read, no mathematical transfer.
- [Dong et al., August 10](https://arxiv.org/abs/2608.09528): robotic fabric
  registration; abstract read, no faithful-source gluing theorem transferred.
- [Dimitrić–Vučković–Žigić, September 5](https://arxiv.org/html/2609.06258v1):
  introduction and Theorem 3.4 read. Bounds on selected derivative orders
  control all orders with an explicit parameter loss under smoothness and
  order-spacing assumptions. No Gevrey estimate is assumed for this source.
- [Evangelatos–Haiden, August 21](https://arxiv.org/html/2608.21201v1):
  introduction and phase-gap discussion read. Their categorical gluing
  conditions do not supply an original-source phase bound. No theorem used.

These papers suggested tests, not premises. C44's proof uses the actual
finite source and current corpus analysis.
