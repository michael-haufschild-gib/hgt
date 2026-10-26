# Compact logarithmic states from compensated physical producers

- **ID:** compact-physical-box-producers
- **Stage:** 2-fully-proven; historical-report completion in progress
- **Type:** THEOREM (paper; main construction and limits Lean-verified)
- **Status:** Recovered-report supplements now have clean transitive axiom audits: 134 public declarations across seven leaves, plus the reused finite-form theorem. All three supplements passed final direct checks and are wired. The comment-edited original producer still needs its final direct check before promotion.
- **Source:** continuum-coprime-shear; physical-box-average-affine-regularity
- **Statement:** Construct compact logarithmic primitive states from arbitrary physical velocities using interval truncation, explicit zero-integral compensation and box smoothing, with quantitative errors and compact-source form convergence.

## Paper theorem

The original report path `docs/reports/BiScaleUncertainty/CompactLogarithmicPhysicalProducers.md`
is absent from this worktree. The construction is fully proved in the existing
Lean producer; its previously missing convergence argument is supplied below and
formalized in the two new convergence leaves.

For n∈ℕ set r=n+1, α=exp(−r), β=exp(r), L=exp(2r), h=exp(−2r).
For arbitrary q∈L²(ℝ), put q_n=1_(α,β]q, m_n=∫_α^βq,
c_n=(m_n/L)1_(β,β+L], v_n=q_n−c_n and w_n=M_(−2r)v_n.
The exact identities ‖c_n‖²=m_n²/L and
‖v_n‖²=‖q_n‖²+m_n²/L give ‖c_n‖≤exp(−r/2)‖q‖ and
‖v_n‖²≤(1+exp(−r))‖q‖². Zero total integral removes the primitive tail.
The smoothed logarithmic state F_(w_n)∘exp is compact C¹, with support
inside [log(α−h),log(β+L)] and exact weighted Dirichlet energy.

The paper proves convergence w_n→P₊q in physical L², uniform compact
logarithmic trace convergence, explicit affine commutator bounds, and
convergence in every constructed compact source-mass-plus-jump form.
Its explicit source coefficient is K(ψ)=∫ψ(x)²exp(x)dx.
Negative physical velocity is invisible to the logarithmic state; the
physical limit is P₊q, not the full q. No independently added constants,
full uncut SourceGraph closure or divisor-domain invariance are claimed.

## Completed formal foundation

### Completion proof for convergence

The referenced report is absent from the current worktree. The following supplies
the convergence argument explicitly, retaining the card's construction and constants.
Write `p=P₊q`, and let `r=n+1` and `q_n,c_n,v_n,w_n` be exactly as above.

The functions `1_(exp(-r),exp(r)]q` converge pointwise to `1_(0,∞)q`.
Their squared difference is bounded by `q²`, including at zero, so dominated
convergence proves `‖q_n-p‖²→0`, hence `q_n→p` in L². The already proved bound
`‖c_n‖≤exp(-r/2)‖q‖` gives `c_n→0` and `v_n→p`. Box averages are contractions
and converge strongly to the identity as their width tends to zero. Therefore

`‖w_n-p‖ ≤ ‖q_n-p‖ + exp(-r/2)‖q‖ + ‖M_(-2r)p-p‖ → 0`.

For any physical velocity `u`, Cauchy–Schwarz on `[0,exp x]` gives
`|F_u(exp x)|²≤exp(x)‖u‖²`. Consequently, for every real upper endpoint `b`,

`sup_(x≤b) |g_n(q)(x)-f_q(x)| ≤ exp(b/2)‖w_n-p‖ → 0`.

This proves the claimed uniform convergence on every compact logarithmic interval,
and a stronger estimate on each left half-line. The negative component cancels
because `f_p=f_q`; it is never asserted that `w_n→q` in physical L².

For a compact continuous source `ψ`, define the actual finite coefficient
`K(ψ)=∫ ψ(x)² exp(x) dx`. Its integrand is continuous with compact support.
Multiplying the preceding squared trace bound by `ψ²` and integrating gives

`sourceMass(ψ,w_n-q,0) ≤ K(ψ)‖w_n-p‖²`.

The constructed compact jump form already satisfies
`jumpEnergy(D_ψ,w_n-q) ≤ R(ψ,weights)‖w_n-p‖²`, with finite resistance mass.
Adding the two estimates proves convergence to zero in every compact
source-mass-plus-jump form. The energies themselves also converge: the uniform
bound `‖w_n‖²≤2‖q‖²` dominates their integrands by
`ψ(x)²(2c²+4exp(x)‖q‖²)` and `2 resistance(e)‖q‖²`, respectively.
Both majorants are integrable, so pointwise trace convergence and dominated
convergence apply. No finiteness premise is added: compact source support supplies
both coefficients.

The endpoint support inequalities for `g_n`, together with its everywhere derivative
`exp(x)p_n(exp x)` and continuity of that derivative, give an actual compact C¹
function. Thus regularity, support, quantitative errors and limits refer to the
same constructed sequence, with no replacement by abstract density.

## Exact Lean coverage

All paths below are relative to `formal/GaloisForLFunctions/BiScaleUncertainty/`.

| Mathematical claim | Leaf and declarations |
|---|---|
| Actual interval restrictions and positive projection; contraction, exact squared norms, primitive tails and positive-half-line invisibility | `PhysicalIntervalRestriction.lean`: `physicalIntervalRestriction`, `positivePhysicalVelocity`, `norm_sq_physicalIntervalRestriction`, `primitive_positivePhysicalVelocity`, `logPrimitive_positivePhysicalVelocity` |
| Exact compensator norm, orthogonality, zero integral, quantitative decay | `CompensatedPhysicalLogarithmicProducer.lean`: `norm_sq_compensatorVelocity`, `norm_sq_compensatedVelocity`, `integral_compensatedVelocity_eq_zero`, `norm_compensatorVelocity_le` |
| Same sequence's support, everywhere derivative and weighted Dirichlet identity | `CompensatedPhysicalLogarithmicProducer.lean`: `smoothedLogarithmicState_eq_zero_of_le`, `smoothedLogarithmicState_eq_zero_of_upper_le`, `hasDerivAt_smoothedLogarithmicState`, `smoothedLogarithmicState_dirichlet_energy` |
| Exact affine commutator and physical approximation bounds | `CompensatedPhysicalLogarithmicProducer.lean`: `smoothedCompensatedVelocity_affine_energy_le`, `norm_smoothedCompensatedVelocity_sub_positive_le` |
| Actual physical L² limits | `CompensatedPhysicalProducerConvergence.lean`: `truncatedVelocity_tendsto`, `compensatorVelocity_tendsto`, `compensatedVelocity_tendsto`, `smoothedCompensatedVelocity_tendsto` |
| Compact C¹ packaging and uniform traces on every left half-line | `CompensatedPhysicalProducerConvergence.lean`: `contDiff_smoothedLogarithmicState`, `hasCompactSupport_smoothedLogarithmicState`, `compactSmoothedLogarithmicState`, `abs_logPrimitive_sub_le`, `smoothedLogarithmicState_tendstoUniformlyOn` |
| Exact source coefficient and compact source-plus-jump error convergence | `CompensatedPhysicalProducerConvergence.lean`: `sourceTraceCoefficient`, `sourceMass_smoothedCompensatedVelocity_sub_le`, `compact_formError_smoothedCompensatedVelocity_tendsto` |
| Actual source, jump and combined energy convergence, for every fixed additive constant | `CompensatedPhysicalProducerFormLimits.lean`: `sourceMass_smoothedCompensatedVelocity_tendsto`, `compact_jumpEnergy_smoothedCompensatedVelocity_tendsto`, `compact_formEnergy_smoothedCompensatedVelocity_tendsto` |
| Exact two-tail identity (14), separate integral and norm limits, explicit separate-tail producer bound | `CompensatedPhysicalProducerTailBounds.lean`: `norm_sq_truncatedVelocity_sub_positive_eq_tails`, `producer_physical_tail_integrals_tendsto`, `producer_physical_tail_norms_tendsto`, `norm_smoothedCompensatedVelocity_sub_positive_le_tail_norms` |
| Square-root norm bounds (6), full physical regularity (8), derivative and affine norm costs (19), compact support and zero smoothed integral, uniform physical traces including zero | `CompensatedPhysicalProducerQuantitative.lean`: `norm_compensatedVelocity_le_sqrt`, `norm_compensatedVelocity_le_one_add_decay`, `smoothedCompensatedProfile_regular`, `absolutelyContinuous_smoothedCompensatedProfile`, `ae_deriv_smoothedCompensatedProfile`, `norm_smoothedCompensatedProfile_derivative_le`, `smoothedCompensatedVelocity_affine_norm_le`, `hasCompactSupport_smoothedCompensatedProfile`, `integrable_smoothedCompensatedVelocity`, `integral_smoothedCompensatedVelocity_eq_zero`, `primitive_smoothedCompensatedVelocity_tendstoUniformlyOn` |
| Exact combined coefficient (22), explicit three-term error and affine form bounds, individual limits in (23) | `CompensatedPhysicalProducerFormBounds.lean`: `compact_formEnergy_le_traceCoefficient_add_resistance`, `compact_formError_smoothedCompensatedVelocity_le_explicit`, `compact_formEnergy_affine_smoothedCompensatedVelocity_le`, `compact_formError_components_smoothedCompensatedVelocity_tendsto` |

The physical declarations use namespace
`GaloisForLFunctions.BiScaleUncertainty.SobolevShear`; source and form limits use
`GaloisForLFunctions.BiScaleUncertainty.PathCongestion`. No analytic premise,
finiteness premise, extra regularity assumption on `q`, or replacement sequence is
introduced. Compact `ψ` and the constructed mixture supply the finite coefficients.

## Recovered original report

The full report is retained at commit `727dc15d1`, path
`docs/reports/BiScaleUncertainty/CompactLogarithmicPhysicalProducers.md`; deletion
from the current tree occurred in `80971df8c`. Its displayed claims (1)–(23)
have been matched to the declarations above. The exact primitive box formula
(9) is the existing `primitive_physicalBoxAverage`; the producer's two support
proofs use it with the vanishing `physicalSecondPrimitive` at the smoothing
step. The regularity statements in Quantitative reuse the actual box-profile
regularity and derivative results. No statement or constant was weakened.

## Verification certificate

- 134 public declarations across seven leaves, plus the reused
  `PathCongestion.compact_formEnergy_ne_top`, passed transitive axiom audits.
  Every list is contained in `{propext, Classical.choice, Quot.sound}`.
  The complete exact-name manifest is
  `/tmp/leftovers-physical-complete-public-names.json`.
- Convergence, FormLimits, TailBounds, Quantitative and FormBounds passed final
  direct `lake --old env lean -j 1 <file>` checks with exit 0 and empty logs.
  The original producer's mathematical source is unchanged; its module comment
  was clarified and its final direct check remains pending. Restriction retains
  its earlier source/axiom certificate and unchanged hash.
- The convergence olean was produced only for the downstream FormLimits import.
  No supplement olean was needed or produced; no existing olean was rebuilt.
  No full build or umbrella check was run.
- All seven modules are imported exactly once by `BiScaleUncertainty.lean`.
  Corpus search returns the new smoothed-integral declaration; prior searches
  returned convergence and energy limits. No proof shortcuts or raised limits
  occur in these sources.
- A prior global lint run reported unrelated structural errors; no
  repository-wide green claim is made. Final scoped whitespace/placement check
  remains part of closure.
- Successful axiom logs: `/tmp/leftovers-physical-axioms.log`,
  `/tmp/leftovers-physical-supplements-audit-r2.log`, and
  `/tmp/leftovers-physical-smoothed-integral-audit.log`. The last log contained
  one no-op-tactic warning; that tactic was removed before the clean final
  Quantitative check. The failed first supplement log is not a certificate.
- Convergence final check is recorded as successful tool session `43673`.
  Remaining final logs: `/tmp/leftovers-physical-form-limits-final.log`,
  `/tmp/leftovers-physical-tail-bounds-final.log`,
  `/tmp/leftovers-physical-quantitative-final.log`, and
  `/tmp/leftovers-physical-form-bounds-final.log`.
  Index evidence: `/tmp/leftovers-physical-smoothed-index.json`.

Source SHA256 values:

| Leaf | SHA256 |
|---|---|
| `PhysicalIntervalRestriction.lean` | `4938cd172ffc68c118e4eed48f8b8f5617986182a17d8e334cd20efe1a7fb1c7` |
| `CompensatedPhysicalLogarithmicProducer.lean` | `0ee3aaf100f4e26f9fbbe7744c3d22799fe820cd37b8d9718ddd9ac7030e3322` |
| `CompensatedPhysicalProducerConvergence.lean` | `43491978b37a82426238a50f613cad5f9c41668c49c0c275c688d94888bd7e4b` |
| `CompensatedPhysicalProducerFormLimits.lean` | `1c6395c813ef8bef632af5da336298646e933ac0aa3702bc3d736a809d509742` |
| `CompensatedPhysicalProducerTailBounds.lean` | `f9173370526c3974a9fe276803e207c96a7407ef2cd6922d7a5ac76411d63179` |
| `CompensatedPhysicalProducerQuantitative.lean` | `a1c74ac5998d9c930330d03dc65380cf43c632b04a853d7c3e8763dc4b2dff2a` |
| `CompensatedPhysicalProducerFormBounds.lean` | `bc50af499e6bc2ee98264bd7f15de8a206e1b87086d33e4c50e43c8d1904c86d` |
