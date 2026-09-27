# Noether/RH continuation: genuine prime-log cells with all atoms retained

## Status
Persistent goal remains active: prove RH via actual arithmetic conservation/Noether route, sustained conjecture/proof loop. RH remains unproved and unfalsified. This turn made verified progress; no blocker. Six new leaves individually audited with `lake --old env lean <leaf> -o <fresh olean>`, no warnings. Eleven endpoint `#print axioms` audits show only `propext, Classical.choice, Quot.sound`. No sorry, new axioms, numerical experiments, heartbeat changes, full/umbrella builds, commits or pushes. Own scratch `work/noether_prime_log_cell_audit.lean` deleted. All six imports wired in RHTower.lean lines19745–19750 at completion. Index refreshed, no generated staleness. Final global lint still flags five OTHER unfinished/unwired modules: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, XiCriticalSourceTailBudget, ZetaZeroDensityPowerSaving. Do not wire their work. No own running process.

Repo `/Users/michael/Documents/code/hgt/formal`. Shared checkout, other agents/chats modify concurrently. New six files remain untracked; preserve all other work. No subagents. Session init/skills/manual already done. Use corpus `../scripts/formal_tools.py research QUERY --mode lexical --no-refresh --budget-seconds 45 --per-module 0`, actual Lean reads, no cards. Keep commentary <=60sec. Previous state: `mem:research/noether_far_gap_full_complex_coercivity_positive_phase_flow_2026_09_27` and `mem:research/noether_integer_log_gap_decay_prime_sensitive_polarization_2026_09_27`.

## Main discovery
The preceding full-integer-log-free construction was too restrictive. Euler reciprocal-prime divergence yields cofinally arbitrarily small gaps divided by sqrt(p). Existing local proper-power leakage controls *all* von Mangoldt weights in those cells. Combining these with the exact finite prime correlation identity and the already proved center-independent local diagonal gap proves uniform positivity for all two-component sources fitting in cofinally many genuine consecutive-prime-log cells. No integer/prime-power avoidance required. Arbitrary complex amplitudes and all smooth localized phase potentials inherit the same mass gap.

This is positivity on a restricted source class. It is not all-source positivity, not RH, and does not justify combining arbitrarily many pieces. No literature novelty claim; new corpus bridge.

## 1. PrimeSquareRootGapClustering.lean
Imports XiMassAdjacentPrimeMask and Mathlib.Analysis.PSeries.
Namespace RHTower.
- `exists_nthPrime_sqrt_gap_lt {eps} (heps:0<eps) N` : exists n>=N with sqrt(p_(n+1))-sqrt(p_n)<eps.
  Contradiction: eventual lower gap eps forces sqrt(p_(N+k))>=k eps. Reciprocal tail dominated by (1/eps^2)/(k+1)^2, summable, contradict `not_summable_nthPrime_reciprocal`.
- `nthPrime_gap_div_sqrt_le_three_sqrt_gap n`: (q-p)/sqrt p <=3(sqrt q-sqrt p). Bertrand q<=2p yields sqrt q<=2sqrt p, then difference of squares.
- `exists_nthPrime_gap_div_sqrt_lt`: cofinally normalized additive gap < every eps>0. This is existence, NOT a bound on every prime gap.
Useful proof APIs: `summable_nat_add_iff`, `Real.summable_one_div_nat_pow`, `one_div_mul_one_div` (forward rewrites product of reciprocals to reciprocal product). Local `let p` needs `dsimp only [p]` before exact_mod_cast.

## 2. PrimeLogCellAtomBound.lean
Imports above, XiHeatCassiniWoldChebyshevErrorIncrement, Sieve.MaynardLocalPrimePowerLeakage, HTGeometry.WindowRpowIntegral.
- `primeLogCellAtomMass N := sum n in Finset.Ioc p_N p_(N+1), Lambda(n)/sqrt(n)`.
  Includes every interior proper power AND endpoint prime; endpoint inclusion is a harmless overestimate for open support differences.
- `primeLogCellAtomMass_nonneg`.
- `primeLogCellAtomMass_le_local_leakage N`:
  W_N <= [log q +(log q/log2)*(sqrt(gap)+1)*log q]/sqrt p.
  Uses psi increment = finite von Mangoldt sum, `chebyshevTheta_nthPrime_succ_sub`, existing local leakage.
- `primeLogCellAtomBudget x := (10/log2)*(log x)^2/sqrt(sqrt x)`.
- `primeLogCellAtomMass_le_budget N hgap` for gap<=sqrt p. q<=2p, log q<=2log p, sqrt(gap)+1<=2sqrt(sqrt p), p>=2. Algebra gives stated constant10.
- `tendsto_primeLogCellAtomBudget_zero` via `HTGeometry.tendsto_logPow_div_rpow` (ROOT namespace HTGeometry, not GaloisForLFunctions.HTGeometry), exponent1/4, k2.
- `exists_primeLogCell_small_budgets {eps} heps N`: exists n>=N with BOTH gap_n/sqrt p_n<eps and W_n<eps. Choose eventual budget small index M; prime-gap result at max(N,M) with min(eps,1).
Missing import hazard: importing Sieve.CharacterWindowMass pulled missing olean SmoothAFEZetaSquareDualRouteTBudget. Used lighter MaynardLocalPrimePowerLeakage and local proof of psi finite identity, no new duplicate public theorem. No missing dependencies remain in final imports.

## Existing infrastructure reused (important search discovery)
`Sieve/MaynardLocalPrimePowerLeakage.lean:99`:
`chebyshevPsi_window_le_theta_window_add_local_primePower {a b} (ha:2<=a)(hab:a<=b)(hd:1<=b-a)`:
psi b-psi a <=theta b-theta a +(log b/log2)*(sqrt(b-a)+1)*log b.
Counts root intervals locally. It obviated inventing/counting higher powers from scratch.
`XiHeatCassiniWoldChebyshevErrorIncrement.lean:26` filter_prime_Ioc_consecutive_nthPrime equals singletonq; line61 theta jump=logq.
`HTGeometry/WindowRpowIntegral.lean:28` root namespace HTGeometry, `tendsto_logPow_div_rpow ha k`.

## 3. ThetaFinitePrimeAtomPolarization.lean
Namespace RHTower.ThetaSourceWard.
- `thetaGroundShiftCross phi psi h := integral x, (k x*phi x)*(k(x+h)*psi(x+h))`.
- `integrable_thetaGroundShiftCross phi psi (hc:HasCompactSupport phi) h` (only phi needs compactness; psi Schwartz).
- `abs_thetaGroundShiftCross_le_mass`: absolute cross<= (Mphi+Mpsi)/2. Integrate 2|ab|<=a²+b², translation invariance of integral. Actual integrability proved.
- `thetaPrimeScalingCross_difference_eq_finite phi psi S hsep hactive`:
  P(phi+psi)-P(phi-psi) = sum n in S, 2*(Lambda(n)/sqrt n)*shiftCross(phi,psi,log n).
  hsep: ordered supports x in supppsi,y in suppphi=>x-y>0.
  hactive: for such x,y and IsPrimePow n with x-y=logn, n in S.
  Exact pointwise polarization; reverse overlap0 because logn>=0; then Fubini/counting integral finite sum. Uses known integrability of prime density.
- `abs_thetaPrimeScalingCross_difference_le_finite_mass`: <= (sumS Lambda/sqrt)*(Mphi+Mpsi), same hsep/hactive plus compactphi.
Lean gotcha: integral pointwise sum needs `hp.fun_add hq`, not `hp.add hq`, to allow rewrites and avoid function addition left folded. For Cauchy inequality use one `rw [abs_mul]` at outer product; full `simp [abs_mul]` overexpands factors and prevents nlinarith from recognizing the square certificate. `integral_prod`, `integral_countable hi.integral_prod_left`, simp count singleton, `tsum_eq_sum` worked.

## 4. ThetaPrimeLogCellCoercivity.lean
Namespace RHTower, open ThetaSourceWard and GaloisForLFunctions.RHTower.
- `abs_thetaPrimeScalingCross_primeLogCell_difference_le`: actual P difference <=W_N*(Mphi+Mpsi), for supports in balls c1,c2 radiusr and [c2-c1-2r,c2-c1+2r] within [logp,logq]. Uses strict ball support inequalities and log monotonicity to put every active integer in Ioc p q.
- `abs_thetaRealArithmeticQuadratic_primeLogCell_full_difference_le`:
  |Qplus-Qminus|<=2*(gap/sqrtp +W_N)*(Mphi+Mpsi).
  Combines preceding prime estimate with existing continuous cross bound.
- `exists_thetaReal_cofinal_primeLogCell_coercivity` line85:
  exists kappa>0, forall N exists n>=N, forall compact real Schwartz phi,psi and balls fitting inside that cell,
  kappa*(Mphi+Mpsi)<=Q(phi+psi) AND <=Q(phi-psi).
  No excluded atoms or unproved positivity premise. From existing local delta,C choose budgets epsilon=min(C/4,delta), kappa=C/2. Cell width log(q/p)<=gap/p<=gap/sqrtp<delta forces r<delta. Center-independent local gap, parallelogram and |Qplus-Qminus|<=C*M yield both signs.

## 5. CCMCofinalPrimeLogCellCoercivity.lean
Imports real result + CCMFarGapPhaseCoercivity (already verified helpers).
- `exists_thetaComplex_cofinal_primeLogCell_coercivity` line21: same uniform kappa, cofinal selected n BEFORE arbitrary complex compact chi,eta, same geometry, both +/- Qfull lower bounds. Split real/imag exactly.
- `exists_ccm_cofinal_primeLogCell_coercivity` line51: actual complex smooth CCM source pair u,v in common arbitrary aperture, same geometry, both full source quadratic endpoints. Ground reconstruction exact; norm squared physical masses.
- `exists_ccm_cofinal_primeLogCell_phaseEnergy_gap` line80: same kappa and cofinal cells, all actual source pairs geometry, EVERY Schwartz angle theta and real phase t:
  kappa*(Mu+Mv)<=ccmPhaseLocalizationEnergy (u.combo v u 1 0) theta t.
  Cos/sin preserve supports, commute with combo, sum physical masses exactly; apply actual source bound to both. Neither localization-error sign assumed. This strengthens the allowed class for the earlier Noether phase potential; no new dynamical/kinetic interpretation claimed.

## 6. ThetaPrimeLogCellPositivePairs.lean
Imports real cell coercivity + ThetaFarPositiveBumpPairs for positive mass lemma.
- `thetaGroundShiftCross_pos_of_balls` line23: real nonnegative profiles with exact supports balls0r and ballcr, compactphi, c-2r<h<c+2r => shiftCross>0. Midpoint x=(c-h)/2 gives both factors positive, k>0; continuous nonnegative integrable product has positive integral. No numerical evaluation.
- `exists_cofinal_primeLogCell_positive_full_pairs (N)` line56:
  exists n>=N, compact nonnegative nonzero phi,psi,c,r>0,
  c-2r=logp_n, c+2r=logp_(n+1), supports EXACT balls0r and ballcr,
  phi0>0,psic>0,
  EVERY h in open whole cell has shiftCross>0,
  and 0<Qplus,0<Qminus.
  Explicit smooth bumps inner r/2 outerr, c=(logp+logq)/2, r=(logq-logp)/4. This is a nonvacuous full-cell realization. Does NOT assert those selected cells contain a proper prime power; if one is present its cross correlation is definitely positive. Do not overclaim guaranteed active arithmetic atoms in the selected cofinal sequence.

## Next mathematical directions (unproved plans)
1. Guarantee actual nonzero atom interactions by centering narrow bump pairs at log m for every sufficiently large prime power m. Current finite-S identity handles S={m}; Lambda(m)/sqrt m<=log m/sqrt m tends0. Isolate m between log(m-1),log(m+1), shrink radius for continuous cross and local positivity. This should yield positive actual sources at genuine arithmetic resonances without needing short prime gaps around squares (the latter is NOT established here).
2. More surprising sign experiment: at a fixed active atom, narrow equal bumps give atomic correlation of order r versus continuous cross order r². Should force Qplus-Qminus<0 for sufficiently narrow resonance, opposite the already proved atom-free modulus increase. Need build quantitative bump overlap/integral lower infrastructure; do not assume it.
3. Global RH still needs control of arbitrary, especially many-component sources. Pairwise/cofinal positivity does not automatically glue. Noether energy conservation alone supplies no global sign bound. Continue conjecture/proof loop; no genuine blocker and do not mark goal complete.
