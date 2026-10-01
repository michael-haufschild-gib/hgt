# Actual history retention: complete slope-fraction ceiling

- **ID:** LI-CLOCK-SLOPE-FRACTION-RETENTION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [full history correlation boundary](../3-formalized/li-clock-history-correlation-boundary.md); [active actual-source sign](../1-in-progress/li-clock-integrated-source-sign.md).
- **Statement:** For every fixed alpha>=0, the optimal actual uniform ceiling for Q_t([0,alpha*K(t)/K'(t)]) is 2alpha-alpha² on0<=alpha<=1 and1 for alpha>=1. Exact residual, generic linear rigidity, actual strict atom deficit and every endpoint case are retained.

## Goal and exact boundary

Classify the full retention law exposed by the failed compact Gamma
correlation step. This strengthens its quarter-slope7/16 positive survivor.
It does not supply the signed-history estimate M15 or prove D/P positivity
or RH. Conditional strict first-zero continuation remains the separate
audited683 result under original nonstrict M15.

## Gates

- [x] Literal actual source, full all-fraction statement and symbolic proof.
- [x] [PROVED HERE] owner159 and complete independent274 paper/source/corpus audit.
- [x] Full683 hinge/source dependency dual reviewed; no open paper dependency.
- [x] Exact R01–R27/S01–S14 Lean leaf with complete local compiler/axiom/review gates; global lint limitations recorded below.
- [ ] Publication and external novelty audit.

## Strongest positive survivor

The measure retains b*delta0 and full K'' density. Its mean correction
vanishes exactly and half of its unnormalized second moment is A=B-1.
For0<alpha<=1 the residual gives equality precisely for linear profiles
in the admitted convex C2 class. Actual strict nonlinearity supplies the
explicit deficit b*(2alpha-alpha²)*(t-K/K')²/(2A).

At alpha1 the scalar zero set is an interval; mean/origin rigidity handles
it. Alpha0 has zero mass; alpha>1 saturates at1 at every sufficiently small
positive clock. Literal origin jets prove the full optimal ceiling for
every real comparison constant, with no model replacing the actual source.
Slope length K/K' is distinct from prior elasticity tK'/K.

## Evidence and coverage

- Owner159 SHA `a57b0b262cddd87067ff7c3f7f4d59259fefafad1e00e1b44aaa958ee7eda186`, preserved verbatim below.
- Independent Current274 `/tmp/li_current_theta_slope_fraction_audit.md`, final SHA `78b9c8bbe9f772378e0b18ca0e75e620929a22cba95ff76b3054b21c2940ba96`; root read all274 plus exact one-label correction. Author proof unchanged.
- Root acceptance `/tmp/li_root_theta_slope_fraction_review.md`; primary triangular-law/source anchors checked.
- Root research70197 terminal0, `/tmp/li_root_theta_slope_fraction_research.json`, SHA `393c5f34756aa9feb145078b41ac8ac123dad6c14aa99b70d884dc0d6c1a3569`. ALL61 returned records independently disposed. Partial=false but semantic coverage unmeasured, refresh incomplete, older snapshot and compiler outcomes mostly pending/stale. No corpus absence or novelty claim.

## Log

- 2026-10-01 — Full stronger survivor passed independent paper/source audit and entered formal planning. [Failed step](../5-failed/li-clock-gamma-history-monotone-cost.md) remains Lean-open.

## Complete frozen proof

Author-time pending-audit wording below is historical. The current gates
above record subsequent review; all159 original lines are unchanged.

# Actual history retention at every slope fraction

Status: NEW PAPER CANDIDATE, complete symbolic proof below; corpus search
and independent audit pending. No formal implementation release. This
strengthens C8–C10b of frozen683 without changing C11–C14 or proving M15.
No numerical or mathematical computation job is used.

## S1. Literal source and inherited admissions

Use exactly the actual B,K,A,b and Q_t of frozen683:

 A(t)=B(t)-1=integral_0^t K(x)dx,
 b=K'(0)=nu_1/2=M_0/2>0,
 Q_t(ds)=1_[0,t](s)*K(t-s)/A(t) ds, t>0.

The complete positive source gives K(0)=0, K'>=b, K''>=0 and
tK'(t)>K(t)>0 at every positive t. The strict inequality retains the
positive cubic coefficient nu_2/144, without replacing K by a model.
Set m(t)=K(t)/K'(t); then 0<m(t)<t. For alpha>=0 define

 h_alpha(t)=alpha*m(t), U_alpha(t)=Q_t([0,h_alpha(t)]).

The interval is allowed to reach beyond t; Q_t is still the SAME probability
supported on [0,t]. Its history endpoints have no atoms. In particular
U_0=0; U_alpha=1 whenever h_alpha>=t. No Gamma jump law is substituted.

The finite positive hinge measure is still

 kappa_t=b*delta_0+1_[0,t](r)*K''(r)dr.

Its mass K'(t), length moment integral(t-r)dkappa=K(t), and half-second
moment integral(t-r)^2/2 dkappa=A(t) are exactly C8. All integrals are
genuine on this compact carrier. Writing w=t-r, its mean length is m,
so integral(w-m)dkappa=0. Complete nonnegative compact Fubini gives, for
every h>=0, not only the original ell=m/4,

 A(t)*Q_t([0,h])=integral f_h(w)dkappa,
 f_h(w)=w*min(h,w)-min(h,w)^2/2.                         (S1)

Indeed each hinge contributes integral_0^min(h,w) (w-s)ds. This remains
valid for h>t, since every w lies in[0,t]. The origin hinge is retained.

## S2. Exact full-fraction residual

Fix 0<alpha<=1 and abbreviate m=m(t)>0, h=alpha*m,
c_alpha=2alpha-alpha^2=1-(1-alpha)^2>0. Define

 R_alpha(w)=c_alpha*w^2/2-f_h(w)-h*(1-alpha)*(w-m), w>=0.

For w>=h direct expansion gives

 R_alpha(w)=c_alpha*(w-m)^2/2.                         (S2a)

For 0<=w<=h it gives

 R_alpha(w)=-(1-alpha)^2*w^2/2
            -alpha*(1-alpha)*m*w+alpha*(1-alpha)*m^2. (S2b)

For alpha<1 this expression decreases on[0,h]; its endpoint value is
c_alpha*(1-alpha)^2*m^2/2>0, by S2a. Thus R is nonnegative everywhere,
with its sole zero w=m. For alpha=1, S2b is identically zero on[0,m],
while S2a is (w-m)^2/2 above m. This endpoint degeneracy is explicit;
the false claim of a sole scalar zero at alpha=1 is not used.

Integrating the complete residual and canceling its linear correction by
the EXACT first moment gives

 A(t)*(c_alpha-U_alpha(t))=integral R_alpha(w)dkappa>=0. (S2c)

No second moment was dropped, and no signed cancellation occurs before
admission. This identity is the full positive survivor behind the bound.

## S3. Exact equality class and actual strict deficit

For the generic admitted C2 convex profile class K(0)=0, K'(0)=b>0,
the same construction gives m<=t and the same residual identity. If
U_alpha=c_alpha for any fixed 0<alpha<=1, its origin hinge contributes

 b*R_alpha(t)=b*c_alpha*(t-m)^2/2.

Here t>=m>=h, so S2a applies even at alpha=1. This term must vanish,
forcing t=m, or tK'(t)=K(t). Since K' is continuous and nondecreasing,
K(t)=integral_0^t K'(x)dx=tK'(t) forces K' constant on[0,t]; hence
K(x)=b*x there. Conversely this linear profile has m=t and direct
integration gives U_alpha=2alpha-alpha^2 for 0<=alpha<=1.

Thus, within the stated class and for every fixed 0<alpha<=1,

 U_alpha=c_alpha iff K(x)=b*x for every x in[0,t].      (S3a)

Equivalently the hinge length is m almost everywhere. For alpha<1 this
follows directly from the sole scalar zero. For alpha=1, zero residual
puts lengths at most m; their mean is m, so they equal m almost everywhere.
This supplies the full measure rigidity even at the degenerate endpoint.

For the ACTUAL source, t>m. Retain its indispensable origin atom in S2c:

 U_alpha(t)<=c_alpha-
       b*c_alpha*(t-m(t))^2/(2*A(t)) < c_alpha,        (S3b)
 Q_t((h_alpha(t),t])>=1-c_alpha+
       b*c_alpha*(t-m(t))^2/(2*A(t)) > 1-c_alpha.      (S3c)

These hold for every t>0 and 0<alpha<=1. The source is never replaced by
the equality profile. At alpha=1/4 they are exactly C10, since h=ell,
c_alpha=7/16 and m=4ell. At alpha=1/2, where the convexity lower bound
still gives H_t(s)>=0 throughout[0,h], recent mass is strictly below3/4.
These are probability statements and do not orient D or its correlation.

## S4. Actual sharpness and full optimal uniform ceiling

Actual ordinary origin jets give K(t)/t->b, K'(t)->b and A(t)/t^2->b/2
as t->0+. Hence m(t)/t->1 and h_alpha(t)/t->alpha for fixed alpha>=0.
Differentiability at zero gives uniform control

 |K(t(1-r))/t-b*(1-r)|<=epsilon, 0<=r<=1,

for sufficiently small positive t. This follows from
|K(u)-bu|<=epsilon*u for all 0<=u<=t, including u=0.
With e_alpha(t)=min(h_alpha(t)/t,1), exact substitution gives

 [integral_0^min(h_alpha,t) K(t-s)ds]/t^2
       =integral_0^e_alpha(t) K(t(1-r))/t dr.

Uniform convergence and e_alpha(t)->min(alpha,1) admit the moving endpoint
directly. Dividing by A(t)/t^2->b/2>0 yields

 U_alpha(t) -> C(alpha):=
   2alpha-alpha^2, if 0<=alpha<=1;
   1,             if alpha>=1.                       (S4a)

For alpha=0 the equality U_0=0 is exact. For 0<alpha<=1, S3b supplies
the strict global bound U_alpha<C(alpha). For alpha>1, the probability
bound U_alpha<=1 is exact and attained at every sufficiently small positive
t: h_alpha(t)/t->alpha>1, so h_alpha(t)>t there.

Consequently, for every fixed alpha>=0 and every real gamma,

 [for EVERY t>0, U_alpha(t)<=gamma] iff C(alpha)<=gamma. (S4b)

The forward implication follows from the actual zero-clock limit; the
reverse uses S3b when alpha<=1 and the probability bound when alpha>=1.
Thus the COMPLETE optimal uniform ceiling is classified for all nonnegative
slope fractions. It is not inferred from an auxiliary linear example.
There is no large-clock limit claim and no estimate of M15.

## S5. Boundary and audit requirements

The source admissions and hinge moment proof are those of frozen683,
SHA cf885634d37e11490bccba01b1ada3d8e9612deac2e400726709340fec5ec7d7.
That paper has root complete mathematical PASS and independent review pending.
S1–S4 are stronger paper candidates requiring their own full independent
audit and corpus check before inclusion in any approved formal contract.
At alpha=1 the scalar residual's zero set is an interval; rigidity uses
the mean or origin hinge, not a false strict scalar inequality. At alpha>1
only probability saturation is used. Alpha0 is a separate zero-mass case.

The conditional first-zero reserve C11–C13 is unchanged. Actual M15,
undamped D positivity, original P sign and RH remain OPEN. No formal
theorem, world novelty, corpus absence, or numerical evidence is claimed.


## Formal certificate — 2026-10-01

LOCAL_FINAL_READY: `formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockHistoryRetention.lean`, 2003 lines, SHA256 `5b4ed65207f355b8761d353d23e9401967805968f5ba74088f11a9fa85e1d4fd`. All41 approved public contracts: 11 definitions/30 theorems; 136 private definitions/theorems. Complete all-fraction ceiling, alpha0/1/>1 endpoints, exact residual/AE mean rigidity, generic global-C2 linear rigidity, strict actual origin-atom deficit, outside reserve, all-n factorial moments and sharp zero-clock limits retained. The public source-curvature theorem includes endpoint0. No M15/D/P/RH sign asserted.

Root and independent complete177 declaration reviews PASS. All112 frozen complete helper bodies, all65 new bodies, all41 literal approved plan contracts, all177 full axiom reports and15 source pins audited. Promotion differs from reviewed scratch2006 only by two mathematical-comment replacements; both forward/reverse byte checks and independent delta review PASS.

Targeted named82245 exit0 (full420-line log read; four replayed upstream style warnings, no leaf diagnostic). Exact promotion-copy direct27673 exit0/empty. Imported ALL41 public axiom6038 exit0; all exactly propext, Classical.choice, Quot.sound, no extra diagnostic. Scratch ALL177 axiom36748 has same foundational-only result. Unique umbrella import verified; index36183 exit0, all41 API rows present.

Global lint31444 is NOT green: 11 unrelated unreachable modules, plus existing size warnings and this 2003-line leaf's size warning. Approved single-leaf design preserves private helper scope and exact reviewed proof allocation; no broad build or unrelated repair performed. Full gate record `/tmp/li_root_theta_history_retention_tree_gates.json`; full root review `/tmp/li_root_theta_history_retention_review.md`; literal177 ledger `/tmp/li_pole_theta_history_retention_assembly_ledger.md`.

The separate [HistoryBarrier B01–B17](li-clock-history-correlation-boundary.md) now passes complete local Lean gates. The combined selected monotone-cost step has its exact retention/crossing positive survivor formalized; actual M15 and RH remain open. Repository-wide lint remains separately non-green.

## Complete independent formal audit

# Retention41 complete independent scratch audit

**PASS — ALL177 declarations; ALL41 approved public contracts; no mathematical blocker.**

Frozen source: `/tmp/li_pole_theta_history_retention_assembly.lean`, ALL2006 lines,101481 bytes, SHA256 `11f22a0e13eb3a7649fa1e637df73f4ae0870bd3cd84f013b9f549c8a3e5a4b5`. Rechecked unchanged at finish. Exact frozen762 plan SHA256 `0a9a345397438929f6819de9edc9196528d69c34d6f7c54c574f87f2b9a2212d`.

Ledger1494 SHA256 `5277b51fd927618e2d9a191f95f2d41fa7d584a391bf944063c7b9881b95b360`; owner metadata4294 SHA256 `0186ddc2dd1d7240997ebfa2863244e95efed3cb56056f70ea62aac3e676048c`; owner certificate55 SHA256 `b7cd69550d5046bf3f566a3bbf7dcf5c36a9ce679041511935927c2eb9e41c1b`.

Read-only review: no compiler, Lean/tree/card edit, numerical experiment, new agent, or strengthened source premise. Sole outputs are this report and matching audit metadata.

## Complete scope and correspondence

Read ALL2006 mathematical source by exact complete-copy reuse plus exhaustive new-body/scope review; read ALL1494 ledger lines/full177 contracts and ALL13 pinned probes. All41 public types/full definition bodies match exact R01–R27/S01–S14 plan after whitespace removal and word-bounded expansion of `m t` to public `liEvenCrossActualClockHistorySlopeLength t`. No truncation at typed theorem inner `let :=`: actual outer proof delimiter checked for every theorem.

Every112 complete private header/body block is an untrimmed byte-exact substring of its certified original, including final newline. All seven original hashes independently checked. Each original/assembly range and declaration hash appears in audit metadata; no copied helper proof was inferred from its name or compiler exit.

| Certified packet | Exact copied declarations | Namespace/scope disposition |
|---|---:|---|
| `hinge`: `0427c6e67276cf85a439ae72318be0f0a135245369c5de7d1d46844abe9043b3` | 22 | PASS; global namespace retained; noncomputable section explicitly closed. |
| `source`: `0ea2415c7fd9bc1ab4a860787ef36a9481499839b95a248c30c75b21904ab536` | 40 | PASS; RHTower namespace retained; original types/bodies unchanged. |
| `scalar`: `8f2220c2a5dec35cea7c172375641de0e8dff9108d3f262d76793348799a2e9b` | 12 | PASS; RHTower namespace retained; original types/bodies unchanged. |
| `origin`: `442cf1243df6d1a7d953b35db46fe9267b8e843ac819f30f1a25a5e9ad8a95db` | 12 | PASS; RHTower namespace retained; original types/bodies unchanged. |
| `age`: `7bd678f9423323f883db8dd9bfb9840401d4f3f196048f00c0829126dec5b1b1` | 13 | PASS; RHTower namespace retained; original types/bodies unchanged. |
| `rigidity`: `4dfbf798569fdb17496b4d144580faaab816e5e5ec772041f82b78f322a94b5a` | 10 | PASS; RHTower namespace retained; original types/bodies unchanged. |
| `zero`: `c9738862c50aec5f26559f4af325f4458b3f4cf9afdecb49d995ef93117a7655` | 3 | PASS; RHTower namespace retained; original types/bodies unchanged. |

Age copies only13 additions; rigidity only10 additions; zero only3 additions, avoiding duplicated source/scalar/hinge proofs. Imports deduplicated. Age `open intervalIntegral` contained in explicit section; no ambient ambiguity leaks into later wrappers. Global hinge and RHTower helpers remain private. All24 new bridges and all41 new public bodies read directly, without sampling.

## Full177 declaration coverage

The following112 complete copied declarations inherit their already-complete independent proof reviews only after exact byte/hash/scope checks. Every remaining declaration receives direct body review below.

**hinge, ALL22: PASS.** `hgt_history_hinge_mass`, `hgt_history_hinge_measure`, `hgt_history_hinge_age`, `hgt_history_hinge_cap`, `hgt_history_hinge_derivatives`, `hgt_history_hinge_deriv_lower`, `hgt_history_hinge_linear_lower`, `hgt_history_hinge_guards`, `hgt_history_hinge_linear_ibp`, `hgt_history_hinge_square_ibp`, `hgt_history_hinge_representation`, `hgt_history_hinge_icc_integral`, `hgt_history_hinge_density_admissions`, `hgt_history_hinge_density_support`, `hgt_history_hinge_admissions`, `hgt_history_hinge_moments`, `hgt_history_hinge_age_admissions`, `hgt_history_hinge_age_probability`, `hgt_history_hinge_age_cutoff`, `hgt_history_hinge_cap_continuous`, `hgt_history_hinge_cap_curvature`, `hgt_history_hinge_cap_identity`.

**source, ALL40: PASS.** `hgt_history_source_term`, `hgt_history_source_series`, `hgt_history_source_coefficient_le_inverse_factorial`, `hgt_history_source_term_bound`, `hgt_history_source_envelope_summable`, `hgt_history_source_norm_summable`, `hgt_history_source_summable`, `hgt_history_source_term_hasDerivAt`, `hgt_history_source_series_hasDerivAt`, `hgt_history_source_series_zero`, `hgt_history_source_iteratedDeriv`, `hgt_history_source_first_deriv`, `hgt_history_source_hasDerivAt_iterated`, `hgt_history_source_continuous_iterated`, `hgt_history_source_compact_uniform`, `hgt_history_source_two`, `hgt_history_source_three`, `hgt_history_source_derivative_series`, `hgt_history_source_hasDerivAt_B`, `hgt_history_source_hasDerivAt_K`, `hgt_history_source_hasDerivAt_K1`, `hgt_history_source_contDiff_K`, `hgt_history_source_contDiff_K1`, `hgt_history_source_contDiff_K2`, `hgt_history_source_origin`, `hgt_history_source_excess_zero`, `hgt_history_source_term_nonneg`, `hgt_history_source_nonneg`, `hgt_history_source_K1_lower`, `hgt_history_source_K2_nonneg`, `hgt_history_source_curvature`, `hgt_history_source_excess_pos`, `hgt_history_source_defectTerm`, `hgt_history_source_defect_series`, `hgt_history_source_defect_coefficient`, `hgt_history_source_defect_nonneg`, `hgt_history_source_defect_second`, `hgt_history_source_cubic_defect`, `hgt_history_source_strict_defect`, `hgt_history_source_geometry`.

**scalar, ALL12: PASS.** `hgt_history_scalar_cap`, `hgt_history_scalar_residual`, `hgt_history_scalar_upper`, `hgt_history_scalar_lower`, `hgt_history_scalar_ceiling_pos`, `hgt_history_scalar_lower_pos`, `hgt_history_scalar_upper_zero`, `hgt_history_scalar_nonneg`, `hgt_history_scalar_quarter`, `hgt_history_scalar_quarter_eq`, `hgt_history_scalar_quarter_nonneg`, `hgt_history_scalar_quarter_lower`.

**origin, ALL12: PASS.** `hgt_history_origin_slope`, `hgt_history_origin_excess`, `hgt_history_origin_scale`, `hgt_history_origin_quadratic`, `hgt_history_origin_quadratic_limit`, `hgt_history_origin_remainder`, `hgt_history_origin_cap_ratio`, `hgt_history_origin_cap_zero`, `hgt_history_origin_fraction`, `hgt_history_origin_eventually_cap`, `hgt_history_origin_eventually_one`, `hgt_history_origin_ceiling`.

**age, ALL13: PASS.** `hgt_history_age_dividedPower`, `hgt_history_age_continuous_dividedPower`, `hgt_history_age_dividedPower_deriv`, `hgt_history_age_integral_dividedPower_convolution`, `hgt_history_age_term`, `hgt_history_age_shifted_hasSum`, `hgt_history_age_term_hasSum`, `hgt_history_age_power_beta`, `hgt_history_age_term_integral`, `hgt_history_age_integrated_series`, `hgt_history_age_beta_series`, `hgt_history_age_base_series`, `hgt_history_age_integral_eq`.

**rigidity, ALL10: PASS.** `hgt_history_rigidity_residual_continuous`, `hgt_history_rigidity_mean_correction`, `hgt_history_rigidity_residual_integral`, `hgt_history_rigidity_origin_reserve`, `hgt_history_rigidity_equal_mean`, `hgt_history_rigidity_mean_linear`, `hgt_history_rigidity_linear_deriv`, `hgt_history_rigidity_linear_fraction`, `hgt_history_rigidity_slope`, `hgt_history_rigidity_quarter`.

**zero, ALL3: PASS.** `hgt_history_zero_mean`, `hgt_history_zero_residual_nonneg`, `hgt_history_zero_residual_iff`.

## ALL24 new private assembly bridges

| Source lines | Complete declaration | Proof disposition |
|---|---|---|
| 1602–1603 | `hgt_history_assembly_smooth` | PASS: Transfers certified global C2 of actual K; no assumed derivative source. |
| 1604–1607 | `hgt_history_assembly_curv` | PASS: Transfers only actual K2≥0 to the closed-interval curvature guard; endpoint/slope guards are established elsewhere. |
| 1608–1612 | `hgt_history_assembly_mass` | PASS: Oriented FTC on all real clocks proves integral K=B−1; exact B0=1. |
| 1613–1616 | `hgt_history_assembly_hinge` | PASS: Literal full hinge measure equals admitted generic measure, including b dirac0. |
| 1617–1619 | `hgt_history_assembly_bpos` | PASS: Exact b=nu1/2=M0/2 with actual source positivity. |
| 1620–1621 | `hgt_history_assembly_age` | PASS: Literal actual density equals admitted generic age law. |
| 1659–1666 | `hgt_history_assembly_age_test` | PASS: Continuous tests have genuine age-law L1 and exact density integral, not merely formal rewriting. |
| 1673–1684 | `hgt_history_assembly_cutoff` | PASS: Exact min cutoff for arbitrary h≥0 from probability density and oriented FTC. |
| 1691–1698 | `hgt_history_assembly_cap` | PASS: Transfers complete capped integral with genuine L1 to literal A and true Q. |
| 1705–1705 | `hgt_history_assembly_fraction` | PASS: Literal fixed-alpha fraction, no implicit sign hypothesis. |
| 1706–1709 | `hgt_history_assembly_mean` | PASS: Genuine finite/L1 lag integral exactly m times hinge mass. |
| 1710–1713 | `hgt_history_assembly_m_geometry` | PASS: Positive m<t and K1>0 from actual source cubic strictness. |
| 1714–1734 | `hgt_history_assembly_slope_residual` | PASS: Full continuous scalar residual admitted under finite hinge; first mean removes compensation term. |
| 1735–1755 | `hgt_history_assembly_slope_eq` | PASS: Zero integral iff AE lag=m, including alpha1 via exact mean; all scalar/L1 guards discharged. |
| 1756–1780 | `hgt_history_assembly_outside` | PASS: Exact disjoint Icc/Ioc union equals support; finite probability complementary real mass. |
| 1781–1816 | `hgt_history_assembly_slope_reserve` | PASS: Positive origin atom and exact residual at lag=t give explicit strict deficit and outside reserve. |
| 1817–1820 | `hgt_history_assembly_quarter_fraction` | PASS: Quarter e=m/4 equals fixed-alpha fraction with alpha1/4. |
| 1821–1828 | `hgt_history_assembly_quarter_residual` | PASS: Quarter scalar residual equals full slope residual at1/4, including compensation coefficient. |
| 1829–1833 | `hgt_history_assembly_quarter_deficit` | PASS: Exact rational specialization of full atom deficit: 7/32 and t−4e. |
| 1834–1840 | `hgt_history_assembly_origin_A` | PASS: Derivative-origin limit yields A/t²→b/2 in nhdsWithin0(Ioi0). |
| 1841–1846 | `hgt_history_assembly_origin_scale` | PASS: Exact scale m/4, denominator positivity, and m/t→1 imply e/t→1/4. |
| 1847–1857 | `hgt_history_assembly_origin_fraction` | PASS: Moving min-cutoff and genuine A quadratic limit give all-alpha piecewise origin ceiling. |
| 1966–1971 | `hgt_history_assembly_whole_cap` | PASS: H≥t covers full supported probability; H=t included and no atom endpoint drift. |
| 1984–1994 | `hgt_history_assembly_slope_bound` | PASS: All-alpha bound uses residual for alpha≤1 and true probability bound for alpha>1. |

## ALL41 exact public contracts and integrated bodies

Order below is exact source order and R01–R27/S01–S14 plan order. Eleven complete definitions and thirty full theorem types are preserved in audit metadata, with full source-block hashes. All typed lets and binder hypotheses retained.

| Target | Source lines / public declaration | Disposition |
|---|---|---|
| R01 | 1580–1580 `liEvenCrossActualClockHistoryExcess` | PASS: Literal A=B−1; A(0)=0, distinct from positive spectral source mass. |
| R02 | 1581–1581 `liEvenCrossActualClockHistoryOriginSlope` | PASS: Literal b=nu1/2, exact single-Xi normalization. |
| R03 | 1582–1582 `liEvenCrossActualClockHistoryScale` | PASS: Literal quarter scale e=K/(4K1), totalized definition with positivity guards later. |
| R04 | 1583–1585 `liEvenCrossActualClockHistoryAgeMeasure` | PASS: Full age density K(t−s)/A on Icc 0 t, no source truncation. |
| R05 | 1586–1588 `liEvenCrossActualClockHistoryHingeMeasure` | PASS: Full hinge b·dirac0 plus nonnegative K2 density, origin atom retained. |
| R06 | 1589–1590 `liEvenCrossActualClockHistoryCappedHinge` | PASS: Exact scalar capped hinge; min includes h>t and h=0. |
| R07 | 1591–1592 `liEvenCrossActualClockHistoryResidual` | PASS: Exact quarter residual; affine mean compensation retained. |
| R08 | 1623–1625 `liEvenCrossActualClockHistory_origin` | PASS: K0=0, K1(0)=b, b=M0/2>0; exact source identity. |
| R09 | 1626–1629 `liEvenCrossActualClockHistory_geometry` | PASS: Positive A/K1/e and strict e<t/4 from genuine cubic source reserve. |
| R10 | 1630–1636 `liEvenCrossActualClockHistoryHinge_admission` | PASS: Finite hinge, AE support and all continuous-test L1 before integration. |
| R11 | 1637–1646 `liEvenCrossActualClockHistoryHinge_moments` | PASS: Exact mass K1, first lag K, second lag²/2=A; genuine integrals. |
| R12 | 1647–1657 `liEvenCrossActualClockHistoryAge_admission` | PASS: Public probability/support and all-natural-power L1; atomlessness and continuous-test L1 are established privately. |
| R13 | 1667–1672 `liEvenCrossActualClockHistoryAge_moment` | PASS: All natural moments: n! outside complete source sum; both factorials and A divisor exact. |
| R14 | 1685–1689 `liEvenCrossActualClockHistoryAge_recent_eq` | PASS: Public quarter cutoff at e; arbitrary h/min cutoff is private and supports S05. |
| R15 | 1699–1702 `liEvenCrossActualClockHistoryHinge_recent` | PASS: Quarter cap integral equals A times age fraction; no missing factor2. |
| R16 | 1859–1861 `liEvenCrossActualClockHistoryResidual_nonneg` | PASS: Quarter pointwise residual nonnegative on genuine lag domain. |
| R17 | 1862–1867 `liEvenCrossActualClockHistory_residual` | PASS: Full residual identity 7/16−Q equals hinge integral/A. |
| R18 | 1868–1873 `liEvenCrossActualClockHistory_recent_eq_iff` | PASS: Finite/L1 exact mean used to close AE equality; no vacuous nonintegrable zero. |
| R19 | 1874–1880 `liEvenCrossActualClockHistory_class_rigidity` | PASS: Global C2, k0=0, positive origin slope and interval curvature imply equality iff linear on closed interval. |
| R20 | 1881–1886 `liEvenCrossActualClockHistory_recent_atom_deficit` | PASS: Strict actual origin-atom deficit 7b(t−4e)²/(32A), all t>0. |
| R21 | 1887–1891 `liEvenCrossActualClockHistory_recent_lt` | PASS: Genuine strict recent fraction <7/16, actual source and atom reserve. |
| R22 | 1892–1897 `liEvenCrossActualClockHistory_outside_atom_reserve` | PASS: Exact Icc/Ioc support partition supplies outside >=9/16 plus same positive deficit. |
| R23 | 1898–1899 `tendsto_liEvenCrossActualClockHistoryExcess_div_sq` | PASS: Punctured-right A/t² limit b/2; totalized endpoint not silently included. |
| R24 | 1900–1901 `tendsto_liEvenCrossActualClockHistoryScale_div` | PASS: Punctured-right e/t limit1/4. |
| R25 | 1902–1906 `tendsto_liEvenCrossActualClockHistory_recent` | PASS: Punctured-right recent mass tends7/16; moving cutoff admitted. |
| R26 | 1907–1910 `liEvenCrossActualClockHistory_recent_ceiling_iff` | PASS: 7/16 is optimal constant for all positive clocks, using exact right limit. |
| R27 | 1911–1912 `liEvenCrossActualClockHistory_source_curvature` | PASS: Public endpoint-inclusive K1≥b, K2≥0 and K1 monotone on Ici0; private dependency repaired. |
| S01 | 1914–1914 `liEvenCrossActualClockHistorySlopeLength` | PASS: Literal m=K/K1, exact public replacement of plan local m notation. |
| S02 | 1915–1916 `liEvenCrossActualClockHistorySlopeFraction` | PASS: Literal all-alpha recent fraction from true age probability, including alpha0. |
| S03 | 1917–1918 `liEvenCrossActualClockHistorySlopeCeiling` | PASS: Literal piecewise C_alpha: 2alpha−alpha² through1, then1. |
| S04 | 1919–1920 `liEvenCrossActualClockHistorySlopeResidual` | PASS: Literal all-alpha scalar residual with mean compensation. |
| S05 | 1925–1927 `liEvenCrossActualClockHistoryHinge_capped` | PASS: All arbitrary h≥0 capped hinge identity, full source law and true L1. |
| S06 | 1928–1931 `liEvenCrossActualClockHistorySlopeResidual_nonneg` | PASS: Public 0<alpha≤1 lag residual nonnegative; alpha1 degenerate branch retained; alpha0 handled separately. |
| S07 | 1932–1940 `liEvenCrossActualClockHistory_slope_residual` | PASS: Exact all-alpha integral residual; complete type lets preserved. |
| S08 | 1941–1947 `liEvenCrossActualClockHistory_slope_eq_iff` | PASS: AE equality iff lag=m under finite/L1/support/exact mean, including alpha1. |
| S09 | 1948–1955 `liEvenCrossActualClockHistory_slope_class_rigidity` | PASS: Generic admitted C2 class rigidity for every0<alpha≤1; positive origin atom available. |
| S10 | 1956–1965 `liEvenCrossActualClockHistory_slope_atom_reserve` | PASS: Strict deficit d=b*C_alpha*(t−m)²/(2A), outside reserve and strict recent ceiling; denominator positive. |
| S11 | 1972–1980 `liEvenCrossActualClockHistory_slope_endpoints` | PASS: Alpha0 fraction0; all alpha≥0 with alpha*m≥t fraction1, including equality cutoff. |
| S12 | 1981–1983 `tendsto_liEvenCrossActualClockHistory_slope_fraction` | PASS: Right-origin fraction tends piecewise C_alpha for every alpha≥0, including alpha>1. |
| S13 | 1995–1999 `liEvenCrossActualClockHistory_slope_ceiling_iff` | PASS: Piecewise C_alpha is exact optimal positive-clock ceiling, no stronger alpha band assumed. |
| S14 | 2000–2003 `liEvenCrossActualClockHistory_slope_eventually_one` | PASS: Every fixed alpha>1 saturates to1 eventually at right origin; no global saturation claim. |

## Source, normalization and genuine admissions

Literal source B is actual single-Xi theta Borel kernel; K=B′, K1=K′, K2=K1′. Full factorial derivative series admitted before positivity/curvature transfer. All eight live actual dependency hashes match pinned certified source core. Primary spot-check: `PrimeArchThetaCumulantMinor.lean:449–461`, complete `normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment` proof uses actual derivative recurrence/raw moments and strictly positive raw normalizer to obtain nu1=M0. Thus b=nu1/2=M0/2; no symmetric-square factor2 substituted.

HistoryExcess A=B−1 satisfies A(0)=0. This is the mandatory H13 notation correction; source xiShiftAbsoluteMass0 is positive and never identified with A(0). Actual nu2 positivity supplies tK1−K>=nu2*t³/72>0 for t>0, so m=K/K1<t and e=m/4<t/4.

Hinge κ retains BOTH positive b·dirac0 and full continuous K2 density on closed [0,t]. All continuous tests genuinely L1 with finite measure before every integral; exact mass K1, lag-first K and lag-square/2 A. Age density is K(t−s)/A on [0,t], true probability and atomless; all-n factorial moment expansion uses complete compact beta/tsum domination. R13 gives n!/A times full series nu_(j+1)t^(2(j+1)+n)/[(2(j+1))!(2(j+1)+n)!]. At n0 this is exactly A/A=1.

Arbitrary cap f_H(h,w)=w min(h,w)−min(h,w)²/2 includes h0 and h>t. No hidden cutoff truncation. Exact age cutoff uses min(h,t), followed by supported Icc/Ioc partition for outside mass.

For 0<alpha<=1, finite/L1 mean is exactly m times hinge mass. At alpha1 scalar zero interval is larger than a singleton, but exact mean forces AE lag=m; no vacuous nonintegrable zero or omitted endpoint. Generic rigidity assumes global C2, k0=0, strictly positive origin slope, nonnegative curvature only on [0,t]. Positive atom at0 then makes equality equivalent to linearity on the full closed interval. No hb>=0 extension asserted.

C_alpha=2alpha−alpha² through alpha1. Actual strict deficit d=b*C_alpha*(t−m)²/(2A)>0 yields U<=C_alpha−d<C_alpha and outside>=1−C_alpha+d. Quarter specializes to ceiling7/16 and reserve7b(t−4e)²/(32A); outside9/16 retains same reserve.

Alpha0 fraction0. For every alpha>=0, if alpha*m>=t then fraction1; alpha>1 has eventual right-origin saturation. Piecewise ceiling is1 above1. Sharp origin limits are RIGHT/punctured (`nhdsWithin 0 (Ioi 0)`), not ordinary nhds0 for totalized ratios. A/t²→b/2, m/t→1, e/t→1/4 give exact all-alpha recent limit and optimal ceiling.

Public R27 exposes source curvature including t0 and monotonicity of K1 on Ici0, resolving the prior private cross-leaf dependency. It provides no signed inverse/first-zero history orientation.

## Terminal evidence independently checked

- Whole93682 terminal0 reported by owner; exact frozen source unchanged; full log EMPTY. API21092 terminal0, all13 specialized probes, log EMPTY. Reviewer launched no compiler.
- ALL177 axiom36748 terminal0 explicitly observed by owner and communicated to reviewer. Independently parsed complete227-line20529-byte log, every report, exact unique source order and namespace-qualified source command. Only `[propext, Classical.choice, Quot.sound]` in each; no extra diagnostics or unreviewed reports.
- Axiom source2184 begins frozen2006 bytes exactly; suffix contains exactly177 unique #print commands, matching every declaration in source order. Log SHA256 `fdca10f5937e73e9cef6c91e03b991823cd468b63ab69920c56b286f8d13e912`; axiom source SHA256 `26790550f29a60e9e91ff23ee7fb0c89a26db50f01dacd94fa563ce414d8f89c`.
- Owner metadata final terminal fields and all177 report records match actual parsed logs; stale historical active lifecycle fields are not treated as live jobs. Owner certificate55 read in full.

## Verdict and strict boundary

**PASS_SCRATCH_REVIEW.** ALL112 copied bodies, ALL24 new private bridges, ALL41 public definitions/types/bodies and ALL177 unique foundational axiom reports reviewed; no unresolved mathematical/API/source-admission blocker found. Exact source remains2006 SHA11f22a0e13eb3a7649fa1e637df73f4ae0870bd3cd84f013b9f549c8a3e5a4b5.

This is an independent scratch review, not tree FINAL_READY or authorization to alter source. Named/direct/imported tree gates remain root/owner obligations after explicit promotion release. Theorems establish positive history-age bounds, sharp ceilings, atom reserves and rigidity. M15 first-zero correlation, literal undamped D0/P sign and RH remain OPEN. No first-zero existence, positive inverse or original clock sign inferred.

## Exact comment-only promotion delta

Root proposed `/tmp/li_root_theta_history_retention_promotion.lean`, ALL2003 lines, SHA256 `5b4ed65207f355b8761d353d23e9401967805968f5ba74088f11a9fa85e1d4fd`. Read BOTH full diff hunks and complete delta JSON. Exactly two mathematical-comment replacements: source-derivative paragraph removes scratch/process language while retaining complete raw-moment/factorial description; origin paragraph now describes right-origin slope/capped-fraction limits. Both comments accurately describe certified bodies.

Independently applied both unique replacements to frozen2006 source and obtained promotion bytes exactly; reverse replacements recover original11f22 source byte-for-byte. Every import, namespace, notation, declaration, full type and mathematical proof body remains unchanged. Comment-only reduction2006→2003 has no contract/admission change. **PASS promotion-delta review**; original frozen-source audit and compiler evidence remain pinned to11f22. Fresh named/direct/imported axiom gates for promoted tree remain root obligations; this report does not claim those gates passed.
