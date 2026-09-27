# Actual uniformly coercive finite complex prime-packet spaces

## Final mathematical result
Active goal RH via arithmetic conservation / Noether remains ACTIVE. RH neither proved nor falsified. This turn resolves the diagonal deficit on selected actual prime-packet spaces, extending previous clique correction work. Unconditional endpoint:
`exists_cofinal_ccmComplexPrimeClique_coercivity`: ∃κ>0∀N n∃actual smooth u, v_i (i:Fin n), primesp_i≥N with2pi<pj, commonradiusr>0, commonaperturea, physicalmassμ>0. Supports u=ball0r andv_i=ball(logpi)r. Signed family f_none=-u,f_somei=v_i has all physical norms²=μ, positive offdiagonal real polar couplings, LinearIndependent ℂ f, and for ALL complexz:
κμΣ|zi|² + cliqueCorrection(Re z) + cliqueCorrection(Im z) ≤ Q(Σzi fi).
Each correction≥0. κ independent of dimension and prime cutoff; primes,r,μ depend on them. Literal complex phase energy Q(Σ exp(iθi)fi)=V(θ)≥κμ(n+1)>0 for every θ.
Source family and all estimates are conclusions, no positivity/sign/existence premise. Generic supporting lemmas retain honest structural hypotheses. Only standard foundational axioms.

Important limit: selected spaces not proved nested or dense. Their positivity does not settle arbitrary-source Weil positivity/RH. Next work must control assembling enough pieces and their cross-interactions; cannot infer RH from unbounded positive finite dimensions.

Repo /Users/michael/Documents/code/hgt/formal. Prior memories `mem:research/noether_clique_repair_and_many_prime_sources_2026_09_27`, `mem:research/noether_global_finite_triangle_correction_2026_09_27`.

## Seven new modules, ALL FINAL AUDITS PASSED
Every leaf audited with lake --old env lean <file> -o .lake/build/lib/lean/<module>.olean, sequential foreground, clean final audits. No agents, commits, full/umbrella builds, numeric experiments, heartbeat increases.

1. FiniteCollectiveDiagonalGap.lean (session15634 passed).
- finiteSignedSeparateLower_uniform_gap: diagonals≥d, |offdiag|≤e≥0 ⇒ (d-card*e)Σxi²≤separateLower.
- finiteSignedClique_uniform_gap retains full clique correction for symmetric M.

2. ThetaPrimePacketBounds.lean (session45924 passed).
- exists_thetaTranslatedBump_prime_bound_radius hnprime: ∃eps>0∀0<r≤eps, |fullpolar(0,logn)|≤2*(Λn/√n)*mass0. All prime-power atoms retained. Isolating radius + finite mass inequality; continuous pairing≤(w/4)mass0.
- exists_thetaTranslatedBump_atomFree_bound_radius gap hatom heta: ∃eps>0∀r≤eps, |polar(c,d)|≤eta*mass0. Fullpolar=continuouspairing; r≤eta/(2exp((d-c+1)/2)).

3. ThetaFinitePrimeDiagonalControl.lean (session90245 passed).
- exists_cofinal_thetaFinitePrime_diagonal_control: ∃C>0∀N n∃p_i,r>0. Allprimes≥N,2pi<pj fori<j. EVERY translate's packet diagonal≥C*mass0. Hub edgesnegative,leafedgespositive; absolute eachcoupling≤C/(2(n+1))*mass0.
- Proof existing exists_thetaReal_center_independent_gap; Λn/√n→0 selects threshold K; spacedPrimeSequence(max N K). Common finite min over Unit(delta/2), hub(negative+bound radii), leaves(positive+bound radii). All constructed internally.

4. CCMRealGramComplexEnergy.lean (session76710 passed).
- ccmRestrictedWeilForm_smul_left/right,sum_left/right,neg_left/right,complex_sum.
- ccmRestrictedWeilForm_real_source_im_zero: real-valued smooth sources have purely real mixed form. Uses actual realCore realization and prior ccmRestrictedWeilForm_realCore_mixed_im_eq_zero; no symmetry assumption substituted.
- ccmRestrictedWeilSourceQuadratic_complex_sum_realImag: Gram imaginaryparts0 ⇒ Qcomplexsum=Qrealcoeffsum+Qimagcoeffsum. Uses explicit casts ((zi).re:ℂ), ((zi).im:ℂ) to avoid module-instance issues.
- ccmWeilFinitePhaseEnergy_eq_complex_phase (line94): exact twochannelV=singlecomplexQsum(exp(iθi)ui).

5. CCMPrimeCliqueCoercivity.lean (initial47016 passed, STRENGTHENED final11721 passed).
- ccmWeilRealPolar_neg_right.
- exists_cofinal_ccmPrimeClique_coercivity: κ=C/2, actualsmoothsources at allfinite dimensions, supports and physicalmassμ, offdiagpositive, EVERY MIXED FORM imaginarypart0 (new conjunct before realcoercivity), allrealcoeff κμΣxi²+cliquecorrection≤Q.
- One commonaperture from compactunion; exactcompactreal sourcebridges. M_none_none uses two neg polar laws. Physicalnormnegativehub uses map_neg,norm_neg. ComplexGram reality uses u/v pointwiseim0 and four Option cases with full-form neg laws.

6. CCMCoercivePrimePhaseAction.lean (initial65259 passed, updated stronger tuple final35269 secondleaf passed).
- ccmFinite_collective_gap_linearIndependent: real LI from positivegap.
- ccmFinite_collective_gap_phase_floor: V≥d*card+gain*[card(card−2)+(Σcosθ)²+(Σsinθ)²].
- phase_floor_basic: V≥d*card.
- exists_ccmPrimeClique_positive_phase_action (line88): actualprime/source/mass data, LinearIndependentℝf, allphaseV≥κμ(n+1)>0, explicit commonrotation Newton equations as conclusions. It does NOT construct arbitrary relative-phase Newton trajectories.
- Destructuring module5 tuple now ignores TWO conjuncts after physicalmass (offdiagpositive and mixedGramreal), then hgap.

7. CCMComplexPrimeCliqueCoercivity.lean (initial95448 passed warning; omit unusedDecidableEq; FINAL35269 firstleaf passed).
- ccmFinite_realGram_complex_collective_gap combines real/imag inequalities retaining both clique corrections.
- ccmFinite_complex_gap_linearIndependent from d>0 and Q≥dΣnorm².
- exists_cofinal_ccmComplexPrimeClique_coercivity (line61): main endpoint described above. No material premise remaining.

All7 wired exactly once in RHTower.lean, currently19788–19794 after prior CCMFinitePhaseNoether (order genericdiagonal,primebounds,ThetaDiagonal,RealGram,RealCoercivity,PhaseAction,ComplexCoercivity).

## Final validation / housekeeping
- CoercivePrimeAxiomAudit.lean printed13 important endpoints; PASSED session8135 exit0. Every result depended only propext,Classical.choice,Quot.sound. Scratch DELETED.
- No sorry/admit/axiom/native_decide/#eval/maxHeartbeats in seven sources. No trailing whitespace; targeted umbrella gitdiff --check clean.
- All Lean processes completed; no active own Lean process.
- Index initial refresh passed13changed0removed. Global lint54160 exit1: unrelated unwired MoebiusMollifiedCriticalMoment,MoebiusMollifiedErrorThreeLines,MoebiusMollifiedZetaField,XiGaussianDerivativeOrientation,XiGaussianDerivativePhase,XiGaussianThirdDerivativeSaving,ZetaZeroDensityPowerSaving; concurrent metadata staleness LEAN_GAPS/LEAN_OVERVIEW. Final index refresh40868 PASSED exit0 (9changed0removed), regenerated API/GAPS/OVERVIEW. All own processes finished. Do not repeat global lint against active unrelated edits or wire others' unfinished leaves.
- Earlier tracked deletion TriangleAxiomAudit.lean remains intentional own cleanup; do not restore. Own new audit absent. Preserve other chats' edits/commits.

## Cache recovery during this turn
New leaf first hit missing old .oleans. Restored ONLY needed prerequisites, each foreground lake --old env lean file -o object: ThetaPrimeShiftNoetherIntegrated,SuzukiScrewOperatorSymmetry; dependency scan then8: SuzukiCanonicalHankelLemma43,CCMUnitRieszCoherentPolarSamplingNoGo,SuzukiWeilPropOneTwo,SuzukiWeilPropThreeOneCapstone,SuzukiV2CharacteristicTarget,PrimeSquareRootGapClustering,XiHeatCassiniLogMeshPrimeGapQuadrature,XiMassFourierBesselRealTime. Allpassed, sourceunchanged. Someexistingwarnings. No fullbuild. Final transitive scan left only ownpendingmodules, nowaudited.
Serena find_symbol on prior negative-radius theorem timedout235s; no oldtheorem modified; actual Lean files read and newleaves created.

## Lean lessons
- add_le_add_right shadowed/flipped convention; use add_le_add h le_rfl.
- Equal-index simp uses ite_true.
- Real LI scalar conversion: `have hzero : (Σj,(xj:ℂ)•uj)=0 := by convert! hx using 1` closes directly. Trailing simp produces No goals.
- Finitesum inner API `sum_inner`,`inner_sum`, not inner_sum_left/right. Complex real sum API `Complex.re_sum`, not sum_re.
- Explicit complexcasts for real/imagcoeffs prevent moduleinstance ambiguity; RCLike real_smul simp can print identical but mismatched goal/term.
- Removed unnecessary `<;> ring` and unused DecidableEq section instances; no heartbeat change.

## Next mathematical frontier
Stronger conjecture: positive form on sums of arbitrary compact smooth components in the selected balls, not only canonical bumps. General pair bound |polar|≤tau*(mass_i+mass_j) follows same finiteatom/Cauchy/continuous estimates. Apply to alreadyweighted components and sum; then extend to complex/localphase profiles via existing ThetaComplexGroundComponents. Need actual finite-sum source bridge and support decomposition before arbitrary-source density.
For global RH, selected sparse spaces alone insufficient. Their assembly reintroduces uncontrolled mixed terms. Need retain arithmetic cancellations in dense arrangements rather than assuming positive-subspace existence implies allsourcepositivity.
