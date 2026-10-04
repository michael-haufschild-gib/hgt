# Literal clock derivative and Green forcing: cofinal signs

- **ID:** LI-CLOCK-DERIVATIVE-COFINAL-SIGN-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [completed-clock sign attempt](../1-in-progress/li-clock-completed-forcing-direct-sign.md)
- **Statement:** The genuine derivative of the full-copy actual clock, and its actual massive Green forcing, each take both signs cofinally; under RH their resonant Cesaro masses give quantitative positive and negative variation.

## Goal

This excludes the proposed one-signed Green-forcing argument. It preserves
the exact source correlations and the missing inequality F>=0. No negative
value of F under RH, RH converse, or finite-window counterexample is claimed.

## Gates

- [x] Literal source and prior-corpus search fixed.
- [x] Complete dependency-closed paper proof, [PROVED HERE], independent full audit.
- [x] Formalize the complete positive survivor, including genuine derivatives and quantitative variation.
- [x] Owned direct/named builds, all-public axioms, independent source review and integration.
- [ ] Repository-wide formal lint green;11 unrelated unwired modules remain.

## Formalization checkpoint

The first leaf's24 planned public contracts are complete in frozen scratch
`/tmp/li_current_clock_derivative_frozen.lean` (751 lines), SHA256
`fff4b0de22a3f69c2a18167246648ea6d153649f8f971789ab77760605dae8ae`.
Root read every public/private body and all24 headers: source/API PASS.
The actual all-real Green formula is proved by growth-selected ODE
primitives and improper FTC, with genuine integrability and both endpoint
limits supplied from actual source bounds. This preserves every contract
without requiring the planned complex-mode Fubini implementation.
Author's whole-source scratch check exited0 with empty log; all24 scratch
axiom reports contain only standard foundations. Independent all751-line
review passes every public/private body; its184-line certificate is
`/tmp/li_producer_current_derivative_independent_review.md`, SHA256
`03b32a9f7f26771adebfb81a7a2b2d8aabccb8b05408c664675aff73efd9130a`.
Root read every certificate line. Identical source is promoted to
[LiEvenCrossActualClockDerivative.lean](../../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockDerivative.lean)
and its umbrella import is wired. Root's exact final tree direct check
`lake env lean GaloisForLFunctions/RHTower/LiEvenCrossActualClockDerivative.lean`
exited0 with empty log. Named
`lake --old build GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivative`
exited0 with no own-leaf diagnostics. Imported all24 source-order axiom
reports also exited0 and contain only `propext`, `Classical.choice`,
`Quot.sound`; root read every report and the complete final certificate
`/tmp/li_current_clock_derivative_final_certificate.md`.
All first-leaf proof/compiler/axiom gates are complete.
Index generation exited0; all24 generated public
API rows were checked. The subsequent `lint --check-generated` exited1
solely on eleven unrelated unwired modules; catalogs passed freshness and
neither owned leaf nor active proof debt was reported. Exact diagnostics:
`/tmp/li_root_clock_derivative_lint.log`. The second leaf's18 sign/variation
contracts now pass all owned proof/compiler/integration checks. Repository-wide
lint remains red on unrelated modules, as recorded below.

### Second leaf: complete source and dual review

`LiEvenCrossActualClockDerivativeOscillation.lean`857 is byte-identical to the
documented candidate SHA256
`6a3c80ea9aedf4735b2bef4feaadf07cc29112d280316498e14f7cd0df61a948`.
It retains all18 public contracts and44 private bodies from frozen817,
SHA `6ff62c50a5dcd6cf7855546b49006566d5105f42f20ddaf2c850fc49d53f50fd`.
Root read ALL817 and ALL277 ledger lines plus every19-comment insertion.
Root complete audit `/tmp/li_root_clock_derivative_oscillation_review.md`, SHA
`978403baf05799840d97d9d4b6e4fec7fa739790c0db39e2370746e6556364e0`.
Producer independently read ALL817/857/277; complete196-line certificate
`/tmp/li_producer_clock_derivative_oscillation_peer_audit.md`, SHA
`a45f894604a11b6b91cb097bde6b98546becd7f76ad644b67c621a88946e8acd`,
read completely by root. Both semantic reviews PASS all18/44.

Whole scratch99854 terminal0/empty; ALL18 scratch axioms91242 terminal0,
root read all reports, foundations only. Promotion preserves every proof,
API, import and bound; root cmp/hash verified. Umbrella wired after the
first derivative leaf. Named6532 terminal0,14394/14394 jobs, owned leaf
warning-free; dependency warnings recorded separately. Exact final direct79568
terminal0/empty; imported ALL18 axioms68334 terminal0. Root read every report;
each contains only `propext`, `Classical.choice`, `Quot.sound`. Complete81-line
final certificate `/tmp/li_current_clock_derivative_oscillation_final_certificate.md`,
SHA `a0aca544f25228e5c582d7f1e714d87bb0050117db608a7b06110e5198481546`,
read completely by root. Index47749 terminal0;
root read all18 API rows and verified exact source-order coverage. Initial
coverage script missed indented theorem declarations; whitespace-aware check
passes all18. Lint74901 terminal1 solely on11 unrelated unwired modules;
catalogs fresh, no owned reachability or proof-debt error. Repository-wide
lint remains red; all42 two-leaf public targets pass their owned checks.
Quantitative variation/density/mass results retain explicit RH; only
the four cofinal strict-sign theorems are unconditional.

## Exact objects and source admission

F is `liEvenCrossActualClockResponse`, w_q=(xiSpectralPoint q)^(-1) for EVERY
q:XiZeroCopy, a_q=w_q^2, and A=sum_q|a_q|>0. Installed source gives
F(t)=Re sum_q w_q sin(tw_q), w_q!=0, |a_q|<1/150,
|Im w_q|<gamma=1/300 and complete square summability.

On |t|<=T, each derivative atom a_q cos(tw_q) is bounded by
|a_q|exp(gamma*T). This is a complete summable majorant. Original atoms
vanish at zero; uniform derivative convergence therefore gives the genuine
continuous derivative h=F'=Re sum_q a_q cos(tw_q). Every further fixed
derivative has the same majorant times a bounded power of |w_q|. Thus F is
smooth; no first-power reciprocal summability is assumed.

Let omega^2=c0-m0, with literal completion moment c0 and actual F'(0)=m0.
The independently audited source jets give 1/4<omega<2/3. Define
G=F'''-omega^2 F'. Then G is even, continuous, and

`G(t)=-Re sum_q a_q(a_q+omega^2)cos(tw_q)`,
`|G(t)|<=A(omega^2+1/150)exp(gamma*|t|)`.

## Full-copy resonant mass and variation [PROVED HERE]

Under RH all w_q are real and all a_q>0. Fix any actual q0 and b=w_q0!=0.
Let S_b=sum_{q:w_q=b or w_q=-b}a_q, retaining every multiplicity copy.
It is summable and S_b>=a_q0>0.

For L>0, uniform convergence admits the finite-interval integral of the
complete h series. Product-to-sum proves that the average of
cos(w_q s)cos(bs) on [0,L] tends to 1/2 at either resonant sign and to zero
otherwise. Both frequencies cannot vanish because b!=0. Each normalized
integral has absolute value at most one, so full summable dominated
convergence proves

`average_[0,L](h(s)cos(bs)) -> S_b/2`.

Also average(h)=F(L)/L->0 by the installed RH sublinear response theorem.
Writing P_L,N_L for averages of max(h,0),max(-h,0),
P_L-N_L->0 and P_L+N_L>=|average(h cos(bs))|. Hence

`liminf P_L >= S_b/4`, `liminf N_L >= S_b/4`.

For every 0<eta<S_b/4, h>eta and h<-eta each occur cofinally. More strongly,
since |h|<=A, each threshold set has lower density at least
`(S_b/4-eta)/(A-eta)>0`. Indeed its signed part is at most eta outside
that set and at most A inside it. Both signed variation integrals therefore
diverge at least linearly. These quantitative statements retain RH.

Exactly the same argument for G uses positive summable weights
a_q(a_q+omega^2), with total mass B=sum_q a_q(a_q+omega^2)>0. It gives

`average(G)->0`,
`average(G(s)cos(bs))->-(b^2+omega^2)S_b/2`,
`liminf average(max(+-G,0)) >= (b^2+omega^2)S_b/4`.

For 0<eta<(b^2+omega^2)S_b/4, the corresponding threshold-set lower
density is at least `((b^2+omega^2)S_b/4-eta)/(B-eta)>0`.

## Unconditional cofinal derivative signs [PROVED HERE]

If h>=0 eventually, FTC makes F eventually bounded below. The installed
not-RH cofinal arbitrarily negative response forces RH. Under RH, eventual
h>=0 and average(h)->0 make average|h|->0: the fixed initial negative
part contributes only O(1/L). This contradicts the positive resonant limit.
Thus h<0 occurs beyond every threshold, unconditionally.

If h<=0 eventually, FTC bounds F above on a final ray, contradicting the
installed unconditional cofinal unboundedness above. Thus h>0 also occurs
cofinally. No unconditional fixed-amplitude bound is asserted by this proof.

## Unconditional cofinal forcing signs [PROVED HERE]

The admitted growth-selected whole-line inverse is

`h(t)=-(2omega)^(-1) integral_R exp(-omega|t-s|)G(s)ds`.

Absolute admission follows from gamma<omega. Its fundamental solution has
the correct derivative jump -2omega. The difference of two selected
solutions is c exp(omega*t)+d exp(-omega*t); the two-sided sub-omega growth
excludes both terms. Evenness supplies the negative end.

If G>=0 on [T,infinity), the nonpositive tail contribution and the fixed
prefix give, for t>=T,

`h(t)<=C_T exp(-omega*t)`,
`C_T=(2omega)^(-1) integral_0^T [exp(omega*s)+exp(-omega*s)]|G(s)|ds`.

Integrating bounds F above, impossible by unconditional upper escape.
Therefore G<0 occurs cofinally. If G<=0 eventually, the opposite bound
h(t)>=-C_T exp(-omega*t) bounds F below and forces RH. Under RH, the zero
mean of G and its nonzero resonant mean contradict eventual G<=0 exactly
as above. Therefore G>0 also occurs cofinally, unconditionally.

## No-go closure

- **Killing mechanism:** Actual h and G have both signs arbitrarily late; a blanket G<=0 cannot orient F through a globally nonnegative derivative.
- **Strongest positive survivor:** Genuine full-copy smooth differentiation, exact resonant Cesaro mass, quantitative RH signed variation and threshold-set density, and unconditional cofinal signs of BOTH h and G.
- **New insight:** A proof of F>=0 must accommodate its unavoidable derivative/forcing oscillations and control the integrated signed Green source.
- **Status:** Complete root/independent paper audit. Lean OPEN; no no-go retirement or closure.

## Verification and provenance

Root160 certificate `/tmp/li_root_clock_derivative_sign_boundary.md`, SHA256
`d634811d35f11c357fc187a41c48ae7538f7c4b1f6e598b471d8667533895980`.
Independent192 audit `/tmp/li_current_clock_derivative_sign_boundary_audit.md`,
SHA256 `fca5d719a4ef8b735a18c00c38b0b5332ebb46cd51f86251a8c45f4e74ba3d1c`.
Root read all192 and separately re-audited its stronger cofinal-G proof.

Source statements/bodies checked in SineSource, DampedResolvent,
XiCanonicalProduct, XiReciprocalSquareSecondMomentRadius,
PrimeArchValuationSectorCones, XiWallLogDerivativeCones, SineDecay,
NegativeResponse and the complete UnboundedResponse file. Current305 and
Producer233 establish the massive coefficient and Green identity; their
all-p transformed R/Q continuation is not needed for the cofinal-sign proof.

Prior direct deep query is `/tmp/hgt-li-clock-derivative-orientation-research.json`:
terminal0, partial255.975s, interrupted text/source/semantic retrieval;
20 candidates,20 source arguments,20 declarations,one unverified ingredient
set inspected. Relevant source contracts were checked directly. No corpus
completeness, external novelty, current compiler or RH claim.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivative`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivativeOscillation`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockUnboundedResponse`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockNegativeResponse`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineDecay`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.RHTower`):
`GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivative`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivativeOscillation`,
`GaloisForLFunctions.RHTower.LiEvenCrossActualClockUnboundedResponse`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockNegativeResponse`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineDecay`.

| Claim | Declaration |
|-|-|
| `F` smooth, genuine derivative `h=F'=Re Σ_q a_q cos(tw_q)`, higher derivatives | `contDiff_liEvenCrossActualClockResponse`, `hasDerivAt_liEvenCrossActualClockResponse`, `liEvenCrossActualClockDerivative_eq_tsum_cos`, `iteratedDeriv_two_liEvenCrossActualClockResponse`, `iteratedDeriv_three_liEvenCrossActualClockResponse` |
| `|h(t)|≤A e^{|t|/300}`; under RH `|h|≤A` | `abs_liEvenCrossActualClockDerivative_le`, `abs_liEvenCrossActualClockDerivative_le_of_rh` |
| `ω²=c₀−m₀`, `1/4<ω<2/3` | `liEvenCrossActualClockGreenRate`, `liEvenCrossActualClockGreenRate_bounds` |
| `G=F'''−ω²F'` even, continuous, `G=−Re Σ a_q(a_q+ω²)cos(tw_q)`, `|G|≤B e^{|t|/300}`, `B≤A(ω²+1/150)` | `liEvenCrossActualClockGreenForcing_even`, `continuous_liEvenCrossActualClockGreenForcing`, `liEvenCrossActualClockGreenForcing_eq_tsum_cos`, `abs_liEvenCrossActualClockGreenForcing_le`, `liEvenCrossActualClockGreenAbsoluteMass_bounds` |
| Full-copy resonant mass `S_b>0` | `liEvenCrossActualClockResonantMass_bounds` |
| RH: `avg(h cos bs)→S_b/2`, `avg(h)→0`; `G` analogues | `tendsto_liEvenCrossActualClockDerivative_resonantAverage`, `tendsto_liEvenCrossActualClockDerivative_average_zero`, `tendsto_liEvenCrossActualClockGreenForcing_resonantAverage`, `tendsto_liEvenCrossActualClockGreenForcing_average_zero` |
| RH: `liminf P_L, N_L ≥ S_b/4` (linear signed variation); `G` analogue | `liEvenCrossActualClockDerivative_signedVariation`, `liEvenCrossActualClockGreenForcing_signedVariation`, `tendsto_..._signedMass_atTop` |
| RH: threshold-set lower density `≥(S_b/4−η)/(A−η)`; thresholds exceeded cofinally | `liEvenCrossActualClockDerivative_thresholdDensity`, `liEvenCrossActualClockGreenForcing_thresholdDensity`, `..._threshold_cofinally` |
| Growth-selected Green inverse `h=−(2ω)⁻¹∫e^{−ω|t−s|}G(s)ds` | `integrable_liEvenCrossActualClockGreenKernel`, `liEvenCrossActualClockDerivative_eq_greenIntegral` |
| Unconditional cofinal signs of `h` and of `G` | `liEvenCrossActualClockDerivative_negative_cofinally`, `liEvenCrossActualClockDerivative_positive_cofinally`, `liEvenCrossActualClockGreenForcing_negative_cofinally`, `liEvenCrossActualClockGreenForcing_positive_cofinally` |

## Log

- 2026-10-01 — Complete proof and independent audit pass. Stronger cofinal-G and quantitative variation survivors separately re-audited. Stage2; full formalization remains mandatory.

- 2026-10-01 — Leaf2 complete817-line frozen source `/tmp/li_current_clock_derivative_oscillation_frozen.lean`, SHA6ff62c50a5dcd6cf7855546b49006566d5105f42f20ddaf2c850fc49d53f50fd, whole99854 terminal0/empty. Root read ALL817 bodies and ALL277-line API/private ledger:18 public/44 private semantic PASS; certificate `/tmp/li_root_clock_derivative_oscillation_review.md`, SHA978403baf05799840d97d9d4b6e4fec7fa739790c0db39e2370746e6556364e0. Scratchall18axioms91242 terminal0, root ALL18 reports read/foundations only; peer audit pending; no Leaf2 tree promotion or all42final claim.
- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
