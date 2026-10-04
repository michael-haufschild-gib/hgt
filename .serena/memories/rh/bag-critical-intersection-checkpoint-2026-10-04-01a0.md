# BAG C28.56z — actual regular cubic source and intersection mass

Repo /Users/michael/Documents/code/hgt; Lean cwd formal. Active unbudgeted goal: unconditional Lean proof or falsification RH by BAG ONLY. Still active; RH NOT proved. No subagents, numerical experiments, added axioms/proof debt, heartbeat increases, full/umbrella builds, commit/push. One owned foreground Lean build at a time; final audit lake --old env lean leaf -o .lake/build/lib/lean/...olean. All jobs below TERMINAL. Current session's three /tmp bag-critical-{source,intersection,axioms}-01a0.lean probes removed. Evidence logs/search JSON retained.

Prior C28.56y (see mem:rh/bag-weighted-six-zeta-checkpoint-2026-10-04-01a0):
Complete weighted valuation-pair trace = H*ζ(σ±α)ζ(σ±β)/[ζ(σ+β−α)ζ(σ+α−β)], Reσ>1 imaginary frequencies. H normally convergent jointly holomorphic through σ=1, axes1. Complete contractions D=Kζ(σ±α), K normally convergent, K(σ,0)=1, derivative frequency0. Literal two-axis mask limit Z−Dβ−Dα+1. DO NOT redo.

NEW PRODUCTION C28.56z, namespace RHTower.BAGTrace:
1. formal/GaloisForLFunctions/RHTower/ChiRamanujanCubicRegularSource.lean (~343lines,26 public theorems).
Imports WeightedCubicContractions, ZetaResidueFactorDerivative. Entire F=RHTower.zetaResidueFactor, F1=1.
residuePair σ α=F(σ+α)F(σ−α).
regularCubicSource σ α β=Jα Jβ H/J(α−β).
regularAxisSource σ α=Jα K.
residuePair nonzero on Reσ>=1 imaginaryα (proved directly using closed-half-plane zeta nonvanishing and F1).
A axes=Jσ0, A(1,0,0)=1.
cubicRegularDomain : Fin3→ℂ = cubicCoordinateTube + Jden!=0. analyticOnNhd_regularCubicSource genuinely joint.
axisCoordinateTube : Fin2→ℂ. analyticOnNhd_axisEulerCorrection proves JOINT K analyticity (cofinal sequence + corpus multivariable Weierstrass), analyticOnNhd_regularAxisSource.
realCubicSource σuv=A(σ,iu,iv); realAxisSource σu=T(σ,iu).
contDiffAt_realCubicSource (line297), contDiffAt_realAxisSource: joint real C∞ at EVERY point with σ>=1. No zero-freeness hypothesis added.
complete_weighted_offAxes_regular_kernel (line190): actual complete directed trace limit exactly
  (Aσ(u,v)−Tσu)/D_u + (Aσ(u,v)−Tσv)/D_v
  − ε² Aσ(u,v)/(D_u D_v) − 2uv Aσ(u,v)/(D_u D_v)+1
where ε=σ−1, D_u=ε²+u².
Both finite-part numerators vanish on their singular axis. All signed sectors retained.
Auxiliary zetaPair, poleDenominator, cubicMellinValue, axisMellinValue identify actual trace before algebra.

2. formal/GaloisForLFunctions/RHTower/ChiRamanujanCubicIntersectionMass.lean (~227lines,9 public theorems).
exists_bound_tested_realCubicSource: for ANY continuous compactly supported complex Φ:R²→ℂ, ∃C>=0, ∀σ∈[1,2], ∀w, norm(Aσ(w)Φw)<=C. Uses actual source continuity, compact product support; outside support zero.
cubicIntersectionDensity w=(1+w1²)^−1(1+w2²)^−1. integrable, integral π².
tendsto_scaled_cubic_intersection: simultaneous scaling both frequencies, actual A(1+ε,εu,εv)*Φ(εw), product-space DCT→π²Φ0.
cubicIntersectionKernel εw=ε²/[(ε²+w1²)(ε²+w2²)].
integrable_tested_cubicIntersectionKernel for EVERY ε>0.
integral_cubicIntersectionKernel_scale: exact two-dimensional Haar change of variables, no numerical approximation, no sequential-limit shortcut.
tendsto_cubic_intersection gives +π² mass.
cubicIntersectionKernel_smul explicit complex/cast bridge to literal original trace summand.
tendsto_literal_signed_cubic_intersection line207 gives limit of integral of LITERAL negative ε²*A/(D_uD_v)*Φ = −π²*Φ(0,0).
Only this summand's boundary is closed. Do not claim full boundary or physical cubic. Other terms may not be discarded.

Audits:
source production3941 exit0 /tmp/bag-critical-source-production-01a0.log;
intersection production52688 exit0 /tmp/bag-critical-intersection-production-01a0.log.
Both no diagnostics, exact lake --old env lean productionleaf -o target.
ALL35 public theorem #print axioms2309 exit0; expected names exhaustively verified, only propext Classical.choice Quot.sound. /tmp/bag-critical-axioms-01a0.log.
Both umbrella imports added immediately after ChiRamanujanWeightedCubicContractions (~22285); NO umbrella build.
index70100 exit0 regenerated LEAN_API/GAPS/OVERVIEW; all35 names checked in API. /tmp/bag-critical-index-01a0.log.
lint1295 exit1 EXACTLY14 unrelated unreachable-module errors, no newleaf/proofdebt/freshness error; /tmp/bag-critical-lint-01a0.log.
Scoped whitespace pass. No active owned job; three owned Lean probes removed.

Docs:
P3 docs/drafts/pipeline/3-formalized/bag-cubic-regular-source-intersection-mass.md exact scope, paper proof and audits.
P1 docs/drafts/pipeline/1-in-progress/bag-critical-cubic-finite-part.md OPEN, includes detailed remaining cancellation proof below.
P1 bag-weighted-cubic-critical-trace.md appended checkpoint.
docs/reports/rh-current-frontier-map.md C28.56z row immediately aftery (intersection closed; finitepart/PV open).
Working log docs/drafts/pipeline/1-in-progress/bagchi-quantitative-sparse-recurrence-working-log.md C28.56z complete checkpoint.

NEXT HARD PROBLEM, same BAG route:
Complete actual compact-test distributional boundary, retaining two finite parts and mixed product PV. Current work closed a real subproblem; now formalize the cancellation, do not redo mass/products, no weaker generic receiver-only result.
Fix smooth compact Φ, choose R enclosing support. fσ=AσΦ, gσ=(Aσ−Tσ(u))Φ, hσ=(Aσ−Tσ(v))Φ. Exact gσ(0,v)=0, hσ(u,0)=0. Joint source C∞ gives uniform second-frequency derivative bounds on [1,2]×[-R,R]².
First reflected quotient for u>0:
 [gσ(u,v)+gσ(−u,v)]/u² =
 ∫t0..1 (1−t)[∂uu gσ(tu,v)+∂uu gσ(−tu,v)]dt.
Linear terms cancel. This extends continuously to u0 and is uniformly bounded.
Full first pairing ∫box gσ/(ε²+u²) = ∫_(0,R)×(-R,R) quotient*u²/(ε²+u²).
Multiplier in[0,1], tends1 offnullaxis, source quotient convergesσ→1, DCT. Second same v/h.
Mixed Δf=f(u,v)−f(−u,v)−f(u,−v)+f(−u,−v).
For u,v>0:
 Δfσ/(uv)=4∫t0..1∫s0..1 ∂uv fσ((2t−1)u,(2s−1)v) ds dt.
Continuous extension axes and uniform bound. Reflect full uv*f/(D_uD_v) to positivequadrant; quotient multiplied by [u²/D_u][v²/D_v]. DCT gives product PV, coefficient−2 retained. Combine with alreadyproved−π²Φ0 and∫Φ.
This simultaneously supplies uniform distributional control; do not justify any ε² remainder only by pointwise vanishing.
Potential implementation: clamp only σ to max(1,σ) BEFORE frequency-remainder construction; frequency derivatives of unclamped smooth source evaluated at clamp remain globally continuous, so global parameter-integral APIs apply. Agrees with actual σ=1+ε for ε>0; never clamp/drop frequencies or modes.
Required Lean: parameterized remainders, actual derivative bounds, reflection identities and DCT assembly. Current card is proof mechanism, not a claimed formal full boundary.

Relevant reads/API:
- Mathlib Analysis/Calculus/TaylorIntegral.lean66–125:
  map_add_eq_sum_add_integral_iteratedFDeriv; n1 gives second integral remainder, only ContDiffAt along segment. Uses fderiv Fréchet/iterated derivatives, applies ℂcodomain as ℝBanach.
- ContDiff/Comp.lean724 fderiv_right (hf)(hmn:m+1<=n), continuousAt_fderiv816, iteratedFDeriv_right.
- MeanValue.lean500 Convex.norm_image_sub_le_of_norm_fderiv_le;550 primed fixed-linear-map remainder;695 norm_image_sub_le_of_norm_hasDerivWithin_le. Deriv/Comp.lean389 HasFDerivAt.comp_hasDerivAt.
- IntervalIntegral.Basic.lean768 norm_integral_le_of_norm_le_const;755 dominated normintegral.
- HTGeometry/NavierStokesHadamardQuotient.lean read ENTIRE; scalar real h only, smoothCoordinateQuotient via average deriv. Does NOT give parametric smoothness.
- HTGeometry/InterfinityGeometry/HadamardDivision.lean40–76 read; continuous_parametric_intervalIntegral_of_continuous for global continuous integrand in parameter,t; rest names via rg.
- HTGeometry/AnalyticSlopeFactor.lean1–175 read: scalar complex analyticSlope, second/iterated analytic Taylor remainder; local scalar not jointparameter.
- ConnesPrincipalValueInverse25–113, ConnesPVIntegrand1–110, ConnesSgnPrincipalValue35–130/240–300 earlier read: compensated PV Schwartz, odd symmetric integral=0. Existing limit uses oscillatory(1−cos)/u, not our damped u/(ε²+u²).
- Haar/NormedSpace.lean92–132 integral_comp_smul(_of_nonneg), dimension prod2. Product volume lemma is Measure.volume_eq_prod.
- ImproperIntegrals269–290 integrable_inv_one_add_sq, integral_univ_inv_one_add_sq.
- Integral/Prod integrable.mul_prod, integral_prod_mul. DominatedConvergence67 filterDCT.
- Source C∞ embedding: use contDiff_pi then fin_cases and Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i), .mul contDiff_const; fun_prop alone misses vecCons/ofReal.
- Explicit f arguments essential in ContinuousAt.comp; tuple constructor inferred as Matrix.vecCons otherwise.
- Many Pi/Complex instance diamonds resolve by typed local functions and convert using1 plus rfl. Avoid free metavariable continuous_const.smul continuous_id; type full ε-scaling map or explicitpair.
- HasCompactSupport.mul_left/smul_left: supply explicit f to avoid200k unification timeout. Noheartbeatincrease.
- Beware simp expanding real division before complexcast: explicit change then rw ofReal_div,pow,mul beats broad simp/ring.
- Every primitive used above was checked in current scratch/production toolchain; don't trust recallednames.

Corpus search evidence:
 /tmp/bag-critical-quotient-search-01a0.json nonpartial65413/65413.
 /tmp/bag-critical-kernels-search-01a0.json nonpartial65441/65441.
 /tmp/bag-critical-pv-search-01a0.json nonpartial65452/65452.
All candidate/source/proof/ingredient sections inspected. Poor unrelated Cauchy-sequence/filtration and derivative-at-zero suggestedingredients rejected. No applicable jointmoving-source boundary theorem found in these results; not a claim corpusgloballylacksone.
Current scope remains directed prime-coordinate arithmetic trace. Rational double-tsum reindex/orthogonality, physical diagonalmatching, actualprofilegrowth, finiteheight nearresonances/coupled dampingbandlimits, growingmoments, movingcofactors, positive commonheight selfreturn remain hard gaps. No RHproof.
