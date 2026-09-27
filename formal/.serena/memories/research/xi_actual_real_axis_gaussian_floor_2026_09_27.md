Goal remains ACTIVE: prove or refute RH unconditionally in Lean. Previous turn PROGRESS: actual ξ real-ordinate Gaussian energy floor now verified. It is not the full complex K_t floor; do not conflate them.

Repo /Users/michael/Documents/code/hgt/formal. Projectless /Users/michael/Documents/Codex/2026-09-26/new-chat-3. Working log work/xi-curvature-rh-loop.md. New report outputs/xi-real-axis-gaussian-floor.md; outputs/xi-relative-gaussian-control.md and xi-full-hankel-energy-bound.md link forward. Earlier infrastructure in mem:research/xi_relative_gaussian_phase_quadrature_frontier_2026_09_27 remains intact (24 verified continuous phase/quadrature theorems). Earlier actual complex finite-Hankel small-time results:44 theorems/8modules, not RH.

NEW FOUR RHTower leaves, namespace RHTower,8 unconditional theorems,2definitions. Every leaf audited with foreground lake --old env lean source -o exactolean, warning-free. All4 wired once to RHTower umbrella; current oleans, no forbidden tactics/holes/axioms/heartbeat changes, scoped whitespace clean. All8 #print axioms audit14335 exit0, missing=[],unexpected_axioms={},diagnostics=[]; only propext/Classical.choice/Quot.sound. No full/umbrella builds or commits/push. No owned process remains. Index22534 exit0; metadata lint49193 exit1 for5 unrelated unwired RHTower modules and stale LEAN_API/LEAN_OVERVIEW; FINAL INDEX18849 CONFIRMED EXIT0. Do not re-poll/restart finished handles.

1 RHTower/XiRealAxisSchwartzEnergy.lean (2thms,1def,leaf57226):
summable_xiRealAxisSchwartz_norm_sq (f:SchwartzMap Real Complex) (r:{r:Real//0<r}):
Summable (fun q:XiZeroCopy => ||f(r*Re(xiSpectralPoint q))||²).
Uses f.decay 1 0, squares |x|*||f(x)||<=C, and xiSpectralPoint_normSq_lt_two_mul_sq_re to get ||alpha||²<=2Re(alpha)². Majorant (2C²/r²)/||alpha||², existing xiSpectralPoint_inv_sq_summable.
xiRealAxisSchwartzEnergy f r := tsum_q ||f(r Re alpha_q)||²; nonnegative.
All multiplicities are retained, every positive scale, no RH.

2 RHTower/XiRealAxisGaussianSampling.lean (2thms,leaf30627):
exists_xiRealAxis_sampling_grid:
exists a>0,h>0,q:Nat->XiZeroCopy injective,
a+jh < Re alpha(qj) <= a+(j+1)h.
Uses exists_xiSpectralPoint_in_bounded_windows from XiHeatQuadraticSamplingBands with centers a+(2j+1)w and h=2w. Strictly increasing real coordinates prove injection.
exists_xiRealAxisGaussian_halfLine_sampling_bound:
exists a>0,h>0,forall real polynomial P and positive scale r,
 integral_(ra)^infinity |P(x) exp(-pi x²)|²
 <= rh * xiRealAxisSchwartzEnergy(polyGaussSchwartz P,r)
    +2rh sqrt(4pi(natDegreeP+1))*||Pg||2².
Actual samples converted to within-cell offsets s_j=(gamma_j-a-jh)/h: Icc0,1.
Finite sums <=complete energy via Finset.image q(range N), q injectivity and summability.
New gaussianPolynomial_grid_quadrature_error plus intervalIntegral_tendsto_integral_Ioi passes N->infinity; no cell-count loss.

3 RHTower/EvenGaussianHalfLineEnergy.lean (2thms,leaf5487):
evenPolynomialGaussian_halfLine_energy P:
 integral_(0,infty) |P(x²)g(x)|² = ||P(x²)g||2²/2.
Uses root integral_comp_abs (NOT MeasureTheory.integral_comp_abs), abs square equality.
evenPolynomialGaussian_tail_energy_lower P (R:NNReal):
 (1/2 -9R sqrt(2natDegreeP+1))*M_P <= integral_(R,infty)|P(x²)g|².
Uses existing RHTower.PolynomialGaussianLocalConcentration.norm_polyGaussSchwartz_sq_le (9sqrt(degree+1)*M), constant integration over[0,R], and intervalIntegral.integral_interval_add_Ioi.

4 RHTower/XiRealAxisGaussianCoercivity.lean (2thms,1def,leaf55247):
exists_xiRealAxisGaussian_relative_floor:
exists h>0,C>0,forall realP,r>0,
 (1/2-C*r*sqrt(((2*natDegreeP:Nat):Real)+1))*M_P
 <=r*h*xiRealAxisSchwartzEnergy(polyGaussSchwartz(evenSquarePolynomial P),r).
Choose C=9a+2h sqrt4pi; actual lower windows and concentration are proved, no hypotheses hidden.
xiGaussianParabolicScale P tau : {r:Real//0<r} :=
 exp tau /sqrt(((2natDegreeP:Nat):Real)+1).
exists_eventually_forall_xiRealAxisGaussian_parabolic_floor:
exists h>0, eventually tau atBot, forall P,
 M_P/4 <= r(P,tau)*h*K0(P,r(P,tau)).
One tau cutoff for all coefficients/degrees AFTER degree-dependent spatial scaling. Not all degrees at a fixed heat time.
Real-degree zero polynomial convention included.

Artifacts: work/xi-real-axis-manifest.json, -axioms.lean/.log, -scope-audit.json, -audit-summary.json, -lint.log.
Own4module build and axioms final all passed. No temporary API files created. Preserve other agents' changes; new sources may become externally tracked.

NEXT mathematical task: transfer actual real-ordinate floor K0 to full complex K and phase debt.
Constant-delta continuous L2 bounds cannot be evaluated at different delta(q) pointwise. Need vertical-strip maximal control plus actual local-count upper bounds.
Conjecture11:
- Exact derivative polynomial Q(P)=P.derivative - Polynomial.C(2*pi)*Polynomial.X*P.
- GaussianSchwartz.hasDerivAt_poly_mul_gaussReal P x already proves real derivative identity; exists_poly_iteratedDeriv_polyGauss has existential iterates but no degree control.
- Build Schwartz derivative equality and degree<=d+1, complex analytic derivative representation.
- Existing gaussianPolynomialFullDerivativeNorm_le controls derivative norm by sqrt4pi(d+1).
- Full shifted derivative norm can then use verticalPolynomialGaussianLp and norm_complexTranslatedPolyGauss_le plus exact exp(pi delta²) modulation.
- FTC vertically, followed by Cauchy-Schwarz on the strip, should control maximal variable imaginary displacement; prove integrability/Fubini and discrete upper sampling, no assumed bridge.
- Real heat normalization w=sqrt(t/(2pi))*alpha, polynomial P(w)=Q(2pi*w²), |Im w|<sqrt(t/(2pi))/2. Do not assume real ordinates equal complex alpha.
- Full RH criterion still every N,a,t>0; small parabolic region does not finish it. No actual negative Xi witness or all-time propagation proved.

Corpus searches this turn: xi Gaussian sampling lower, polynomial Gaussian half integral, xi Schwartz summable, even integral Ioi, Gaussian vertical derivative norm. No directly reusable actual Gaussian sampling floor or vertical maximal theorem found. Source searches found unrelated XiShiftedHankelLagrangeCapacity/RedundantSamplingCapacity conditional reciprocal-coordinate results; inspected and not the present Gaussian route. Existing generic even integral lemmas exist; new closed even-polynomial specialization is backed directly by mathlib integral_comp_abs.

Lean details:
- To simplify NNReal mesh=⟨r*h,...⟩, explicit change was needed in coordinate equality; simp[NNReal.coe_mk] left an opaque coercion and was unused.
- Finset.sum_image needs explicit f,s,g in reverse rewrites when q is nested inside norm/evaluation.
- tendsto_atTop_add_const_left atTop const (tendsto_natCast_atTop_atTop.atTop_mul_const hpos) gives endpoints->infty; no line break immediately after field dot.
- MeasureTheory.intervalIntegral_tendsto_integral_Ioi and le_of_tendsto' complete limit.
- Nat casts in sqrt(2*P.natDegree+1) were already in Real; simp Nat.cast_add made no progress, removed.
- field_simp alone closes C*(1/(4*C))=1/4 under C>0; trailing ring causes no-goals error.
- Summable.of_nonneg_of_le named g is lower function, not majorant; pass comparison summability as explicit third argument.
Rules remain: search tool via scripts formal_tools.py research, direct Lean only/no cards, no computations, one foreground Lean build per agent, final --old leaf audit, wire but no umbrella build, no new axioms/premises/heartbeat hacks, no commits/push. No subagents authorized. Serena memory tools only; symbol tools trigger hidden builds. Final links only projectless outputs.