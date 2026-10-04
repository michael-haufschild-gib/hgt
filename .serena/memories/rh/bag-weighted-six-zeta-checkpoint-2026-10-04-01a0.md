BAG ONLY, no subagents. Active unbudgeted goal unconditional Lean RH proof/falsification; not achieved. Repo /Users/michael/Documents/code/hgt; Lean cwd formal. C28.56y succeeds on complete weighted arithmetic trace, not critical distributional action or physical cubic.

THREE FINISHED PRODUCTION LEAVES, namespace RHTower.BAGTrace:
ChiRamanujanWeightedCubicLocal.lean: full complex signed weighted valuation sum and finite product HasSum, balanced specialization, exact mixed local correction H_p-1=z²(1-U^-1)(1-V^-1)*[U+V-1-z²-U/V-V/U+z/U+z/V]/[(1-z)²(1-zV/U)(1-zU/V)].
ChiRamanujanWeightedCubicTrace.lean: base p s=p^(-s); complete_weighted_trace_six_zeta for Reσ>1 and Reα=Reβ=0. ALL valuation pairs at each finite prime set then ALL primes -> H * ζ(σ+α)ζ(σ+β)ζ(σ-α)ζ(σ-β)/(ζ(σ+β-α)ζ(σ+α-β)). H normal on Reσ>7/8, |Reα|,|Reβ|<1/16. Exact H(σ,0,β)=H(σ,α,0)=1. analyticOnNhd_cubicEulerCorrection gives JOINT holomorphy on cubicCoordinateTube (Fin3→ℂ).
ChiRamanujanWeightedCubicContractions.lean: complete_weighted_axis_two_zeta with K=prod[1-z²(1-U^-1)²/(1-z)²]; K normal across critical plane; K(σ,0)=1; hasDerivAt_axisEulerCorrection_zero proves full-product complex frequency derivative zero for Reσ>7/8. weightedOffAxesTrace literally masks BOTH zero valuation vectors, theorem weightedOffAxesTrace_eq subtracts BOTH COMPLETE contractions +origin. complete_weighted_offAxes_trace gives full Z-Dβ-Dα+1 limit.

AUDITS TERMINAL: direct lake --old env lean <leaf> -o <productionolean> for local56774, trace16460, contractions41569 all exit0 no diagnostics. ALL46 public theorem axiom queries1895 exit0 only propext/Classical.choice/Quot.sound (11local,19trace,16contractions). Logs /tmp/bag-weighted-{local-production,trace-production,contractions-production,axioms}-01a0.log. Umbrella imports wired after ChiRamanujanCompleteCubicTrace. No full/umbrella build. Index74952 exit0; API/overview/gaps regenerated, all46 names present. Lint42395 exit1 ONLY14 unrelated unreachable modules, no newleaf/proofdebt/freshness error. /tmp/bag-weighted-{index,lint}-01a0.log. Whitespace passed. Owned /tmp/bag-weighted-{local,sum,normal,axis,axioms}-01a0.lean probes removed. No live owned processes; search and audit logs retained. No raised heartbeats/numerics/axioms/commits.

DOCS:
P3 docs/drafts/pipeline/3-formalized/bag-weighted-six-zeta-cubic-trace.md exact statement/proof/audit.
P1 docs/drafts/pipeline/1-in-progress/bag-weighted-cubic-critical-trace.md retains next hardest boundary proof and NEW concrete integral-quotient plan.
Frontier docs/reports/rh-current-frontier-map.md C28.56y updated from source-only local to full weighted trace, joint H regularity, contractions.
Workinglog appended docs/drafts/pipeline/1-in-progress/bagchi-quantitative-sparse-recurrence-working-log.md.
Prior x balanced trace remains; do not rediscover six-zeta algebra or optimize32 bound.

CORPUS SEARCHES completed and all candidate/source/proof/ingredient sections inspected:
weighted-critical-trace nonpartial inv65385;
multivariable-normal-search nonpartial65404, found actual HTGeometry/MultivariableVitali analyticOnNhd_of_tendstoLocallyUniformlyOn and PolydiscWeierstrass; used them.
weighted-boundary-next nonpartial65411, freshen incomplete/background index, source compiler mostly pending/stale. JSON /tmp/bag-{weighted-critical-trace,multivariable-normal-search,weighted-boundary-next}-01a0.json. Treat sources as grounded but applicability verified Lean.

NEXT HARD CONJECTURE: actual critical compact-test boundary of Zσ-Dσ(u)-Dσ(v)+1, σ=1+ε, α=iu,β=iv. Retain -π²δ_(0,0) AND -2 PV(1/u)⊗PV(1/v). Existing P1 rational-product card has exact proposed limit:
-π²δ-2PV⊗PV+vB1 PV_u+uB1 PV_v-2B1-M1(u)-M1(v)+1.
Now construct ACTUAL pole-removed source quotients, not generic conditional receiver.

SOURCE INPUTS READ:
ZetaResidueFactorDerivative.lean 1–110 has public F=zetaResidueFactor=Function.update((s-1)ζs)1 1, F1=1, differentiable_zetaResidueFactor entire, HasDerivAt at1 Euler gamma. Best actual regulator for J.
ZetaLineLowerBound.lean 1–110 zetaPoleFactor same if definition, continuous and nonzero Re≥1. Equality to F elementary but not yet added.
Sieve/InvZetaRegular.lean1–125 invZeta=(s-1)/(zetaResidueUnit s), valueZERO at1. Raw ζ reciprocal at1 is assigned nonzero junk: MUST NOT substitute into critical limit.
HTGeometry/BoundaryCauchyKernel.lean1–177 fully read: actual Cauchy density approx identity tendsto_integral_cauchyPDFReal_mul for real integrable continuous test atγ, scale c^-1, c→∞. Generalizes to complex/2D with proofs.
ConnesPrincipalValueInverse names only: connesPVinv compensated inner+outer integrals; inner/outer integrability for Schwartz.
ConnesSgnPrincipalValue contains oscillatory PV limit ~line257 (body not yet read).

NEW PAPER MECHANISM (not Lean yet):
Jσ(u)=F(σ+iu)F(σ-iu), even/nonzero σ≥1 includingu0. a=Jσ0.
A=Jσu Jσv Hσ(u,v)/Jσ(u-v), axes=A=a.
B smooth extension via ∫[0,1]² ∂u∂v Aσ(tu,sv)dsdt.
M via ∫[0,1](1-t)∂u²(JσKσ)(tu)dt. J even and full K derivative0 give (JK)'0=0.
These integral forms supply joint smoothness/uniform derivative convergence on each compact box using normal H and analytic source F. Need joint K analyticity or parameter Cauchy derivative continuity; only joint normal convergence and slice derivative is currently exported, but Fin2 Weierstrass is straightforward required step.
Let Qε=ε/(ε²+u²), Pε=u/(ε²+u²), Rε=u²/(ε²+u²).
Exact connected source decomposes:
-a Qε(u)Qε(v)-2a Pε(u)Pε(v)+vB Pε(u)+uB Pε(v)-ε²B Pε(u)Pε(v)-2B Rε(u)Rε(v)-M(u)Rε(u)-M(v)Rε(v)+1.
Prove uniform order-two bound for Pε⊗Pε against moving B*test by subtracting both axis values using symmetric[-1,1] cutoffs. Inner double-compensated numerator <=|uv| sup mixed derivative; outer strips/corner integrable. DCT gives PV tensor and THEN ε² remainder0. Q product givesπ²pointmass; R bounded1, tends1ae. Need source derivatives up to4A for B*test order2. All this is paper plan, not formal theorem.

SCOPE: directed prime-coordinate trace; a single unordered ℚ-positive double-tsum and orthogonality reindexing NOT formalized. Arithmetic axes not yet physical prime diagonals; damping1/ε vs logN scale, finite-height near-resonances c-ab~1/N, actual-profile growth/derivatives and coupled damping/band limit remain hard. Growing moments/moving cofactors/positive common-height self-return/RH not proved.

Lean implementation lessons:
DifferentiableOn.div and .finsetProd in current mathlib scalar DOMAIN only; for tuple domain use mul inv and finite induction. Coordinate composition required explicit f/s parameters and small private lemmas to avoid200k unification; no heartbeat changes.
Pi function operations vs pointwise functions often need convert ... using1 <;>try rfl; .fun_finsetProd for derivative limits. Finset.prod_coe_sort needs explicit function to rewrite subtype product. HasProd congr_fun expects NEW=OLD, not reverse. Standard cpow names checked: Complex.cpow_ne_zero_iff.mpr (.inl...), cpow_add hasimplicitbase+twoexponents+nonzero.
Serena initialized/readmemories earlier; don't call initial_instructions huge dump again. No update_plan tool available. No skill used. User no subagents and no commit/push persist.