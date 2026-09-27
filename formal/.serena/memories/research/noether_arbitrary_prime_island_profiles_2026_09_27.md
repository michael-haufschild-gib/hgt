# Arbitrary-profile prime-island coercivity — 2026-09-27

## Goal and status
Active goal remains proving RH via arithmetic conservation/Noether. RH is NOT proved or falsified. No claim of literature novelty. This round strengthens selected bump-vector families to arbitrary compact smooth profiles in finitely many support regions. Do not mark goal complete or blocked for mathematical difficulty.

Repo /Users/michael/Documents/code/hgt/formal. One own foreground Lean process at a time; no full/umbrella builds, numerical computations, sorry, new mathematical axioms, heartbeat changes, commits/pushes, or subagents. Preserve concurrent work. Search actual Lean with ../scripts/formal_tools.py research; no cards as mathematical evidence. Previous context: `mem:research/noether_coercive_finite_prime_spaces_2026_09_27` and `mem:research/noether_clique_repair_and_many_prime_sources_2026_09_27`.

## New verified modules (all wired into RHTower.lean)
1. ThetaPrimeIslandPairBounds.lean
- exists_thetaPrime_island_pair_bound: for prime p, there is eps>0 such that every 0<r<=eps and arbitrary compact real Schwartz phi,psi supported in balls at 0,log p satisfy |fullPolar(phi,psi)| <= (Lambda(p)/sqrt(p))*(mass(phi)+mass(psi)). Uses Function.support, not tsupport. No shape, positivity, or equal-mass assumptions. Complete prime-power contribution retained; isolation shows only p active.
- exists_thetaAtomFree_island_pair_bound: if d-c exceeds screwSignThreshold and differs from every log integer >=2, then for any eta>0 a sufficiently small common radius gives |fullPolar|<=eta*(mass sum), for arbitrary compact real profiles at c,d. Again Function.support.

2. CCMSmoothFiniteSum.lean
- ccmSmoothFiniteSum u z is literal compact smooth source x |-> sum_i z_i*u_i(x), same aperture.
- ccmSmoothFiniteSum_toCCMFormVector: its actual vector equals sum_i z_i • u_i.vector.
- ccmThetaGroundProfile_finiteSum: ground profile equals sum_i z_i • ground(u_i).

3. FiniteSourceMassBudget.lean
- finiteSignedQuadratic_mass_gap: any finite real matrix M and nonnegative masses m, with diagonal >=C*m_i and offdiag abs <=e*(m_i+m_j), has Q_M(ones)>=(C-2*card*e)*sum m_i. Requires no symmetry. Generic premises are explicitly mathematical; no missing estimate assumed in existential endpoints.

4. ThetaFiniteSourceQuadratic.lean
- hasCompactSupport_schwartz_finite_sum.
- thetaRealWeilPolar_compact_self and compact_symm.
- thetaRealArithmeticQuadratic_finite_sum: exact complete Q(sum phi_i)=sum_ij fullPolar(phi_i,phi_j), for any finite compact real Schwartz family. Proof constructs common actual CCM aperture and uses literal source finite sums.

5. ThetaPrimeIslandCoercivity.lean
- exists_cofinal_thetaReal_primeIsland_coercivity:
  exists k>0, forall lower bound N and finite n, exists primes p:Fin n -> Nat and r>0, all p_i>=N, 2p_i<p_j for i<j, such that EVERY family phi:Option(Fin n)->Schwartz(R,R), compact and with tsupport(phi_i) in ball(center_i,r), satisfies
  k * sum_i thetaGroundNormSq(thetaComplexify(phi_i)) <= thetaRealArithmeticQuadratic(sum phi_i).
  center_none=0, center_some_i=log p_i.
- Proof: center-independent local gap C; eta=C/(4(n+1)); choose primes beyond Lambda/sqrt threshold; finite minimum of diagonal, prime-pair and atom-free pair radii; symmetric reverse pairs; mass-budget lemma gives k=C/2.
- k independent of N,n. Primes/radius depend on n; no nesting/density.

6. CCMPrimeIslandCoercivity.lean
- thetaRealComponent_finite_sum, thetaImagComponent_finite_sum.
- exists_cofinal_thetaComplex_primeIsland_coercivity: same uniform construction for arbitrary compact COMPLEX Schwartz profiles. Exact real/imag split of full energy and mass; components preserve support.
- exists_cofinal_ccm_primeIsland_coercivity: actual arbitrary complex smooth CCM components in those balls, any aperture; k*sum physical L2 masses <= Q(ccmSmoothFiniteSum u ones).
- ccmCosLocalizedSource_finiteSum, ccmSinLocalizedSource_finiteSum: localizations commute with literal finite superposition.
- exists_cofinal_ccm_primeIsland_phaseEnergy_gap: same regions and gap, for all smooth theta and all real t, k*sum original physical masses <= ccmPhaseLocalizationEnergy(sum u_i,theta,t).
  This is the COSINE/SINE TWO-CHANNEL phase potential. Do not identify it with Q(exp(i*theta)*u) for arbitrary complex u without accounting for imaginary mixed terms.

## Mathematical meaning and remaining gap
This rules out negative Weil-energy witnesses throughout selected support-region classes, including oscillatory/sign-changing real profiles and arbitrary complex profiles. Main advance from previous turn: arbitrary component functions and unequal masses, not just chosen equal bumps.
Mechanism: large primes weaken direct arithmetic couplings, narrowing supports weakens continuous/atom-free pair terms, local diagonal reserve covers their total mass cost. This is a candidate building block for RH, not RH itself. Need positivity for general sources: a dense/nested exhaustion or a decomposition whose cross-region interactions remain controlled. Summing vectors from individually positive spaces does not preserve positivity automatically.
Potential next work: exploit exact finite expansion and collective signed-edge/clique corrections on arbitrary source decompositions; crude absolute-value interaction bounds probably lose crucial cancellations for dense covers. Build missing infrastructure instead of merely restating a conditional RH endpoint.

## Verification
All six final leaf audits passed clean using lake --old env lean file -o corresponding .lake/build/lib/lean/...olean. Terminal successful sessions: pair bounds34646 (earlier context), smooth finite sum35868, mass budget98472, finite quadratic53766, real coercivity75126, complex/phase coercivity36956. No own live Lean processes remain.
PrimeIslandAxiomAudit.lean checked18 declarations, session86804 exit0; every dependency list exactly [propext, Classical.choice, Quot.sound]. Audit scratch removed. Umbrella imports added; no umbrella build.
Index session72534 exit0,6 changed modules. Global lint session40455 finished exit1 solely on unrelated unreachable modules: RHTower.LatticeMasksDeepPair, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ThetaPrimePowerBernsteinGauge, ThetaTranslationGaugeFlux, ZetaZeroDensityPowerSaving; HTGeometry.CompletedPseudoDiffOpAdicCompleteness, CompletedPseudoDiffOpVectorArtinian, CompletedPseudoDiffOpVectorLattice. No generated-metadata drift reported, so no repeat index needed. All six own imports independently confirmed exactly once at umbrella lines19804-19809. No live own Lean or lint/index process remains. No commit/push. Existing tracked deletion TriangleAxiomAudit.lean is prior intentional scratch cleanup; preserve concurrent modifications.

## Lean lessons
- HasCompactSupport (sum_i phi_i) may elaborate as a sum of coerced functions! State HasCompactSupport (⇑(sum_i phi_i)) and likewise tsupport explicitly for Schwartz finite sums. Convert HasCompactSupport.finset_sum, then funext/simp.
- Continuation after `using` inside parenthesized `by` needs proper indentation; easiest `by` newline indented full simpa line.
- Pair bounds use Function.support; when endpoint gives tsupport use subset_closure.trans hs.
- Schwartz finite sum evaluation: simp only [sum_apply,smul_apply,smul_eq_mul]; protected SchwartzMap.sum_apply deprecated.
- norm of ccmArchimedeanFormToAperture and embedding mathematically/definitionally equal, but simp-only matching may not unfold codRestrict. File6 uses private `physicalNorm_toAperture a v : norm(ToAperture a v)=norm(Embedding a v) := rfl` and rewrites explicitly.
- Do NOT simp_rw thetaGroundNormSq_realImag indiscriminately: it can recursively expand newly inserted component masses. Establish finite sum equality via Finset.sum_congr, rewrite sum_add_distrib once, then rw equality.
- ccmSmoothFiniteSum proof requires explicit ccmArchimedeanFormToAperture_coe rewrite in physical AE representatives before matching embedding.
- Finset.sum_congr named args s₁,s₂ work. map_sum (SchwartzMap.postcompCLM Complex.reCLM) chi Finset.univ gives component finite-sum law.
