# CCM-FU: all-cutoff prime-fibre interpolation and packet bound

Goal remains active/unbudgeted. RH, SD1, PE4, PE4G OPEN. This turn made verified progress, not a wait or blocker. Full chain: completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.

## New exact source law
For prime p and ANY cutoff M, let N=M/p (natural quotient), theta=(sqrt M-sqrt(p*N))/(sqrt(p*(N+1))-sqrt(p*N)). Proven 0<=theta<1. For every d, unsigned K_(pd)(M)=sqrt p*K_d(N)+(sqrt M-sqrt(p*N))*D(N/d)=sqrt p*((1-theta)K_d(N)+theta K_d(N+1)). The clipped last block is exactly telescoped in the square-root clock. All zero and terminal indices included. Coprime p,d gives the reflected signed formula; repeated p gives zero larger channel.

For p unprocessed and absent from label R, define B(R)=(1-theta)F_(N,P)(R)+theta F_(N+1,P)(R). Then F_(M,P)(insert p R)=-sqrt p*B(R) and F_(M,insert p P)(R)=F_(M,P)(R)-sqrt p*B(R). NO p>N restriction. Prime-square exclusions automatic in p-free smaller label. F_N+1 retains new coefficient d=N, while d=N+1 terminal is zero.

For a legal prime p<M, exact complete energy update E_M(insert p P)-E_M(P)=(-2sqrt p)*sum_R F_(M,P)(R)*B(R), over the entire p-free powerset of Pi(M). Removed partner square cancels copied square. Signed inner product remains unbounded.

## New unconditional packet estimate
For any finite p-free label family T,
sum_T B(R)^2=(1-theta)sum_T F_N^2+theta sum_T F_N+1^2-theta(1-theta)sum_T(F_N+1-F_N)^2.
Every finite label family's energy <= full retained E at that cutoff because labels outside source universe vanish. Thus sum_T F_M(insert p R)^2 <= p*((1-theta)E_N(P)+theta E_N+1(P)). Same processed P at both smaller cutoffs, essential. This is an ACTUAL component-energy bound; does NOT bound signed mixed merger or original-diagonal endpoints. Do not infer compatibility from separately chosen smaller-cutoff good paths.

## Verified files — DO NOT REBUILD/RE-AUDIT
1. formal/GaloisForLFunctions/RHTower/MobiusDivisorClippedHomothety.lean,134 lines, root namespace RHTower. 8 public theorems + def divisorPrimeClipWeight. Theorems: divisorUnsignedDilationChannel_eq_range; divisorUnsignedDilationChannel_mul_add (r>0,t<=r); divisorUnsignedDilationChannel_succ (all N,d); divisorPrimeClipWeight_nonneg; divisorPrimeClipWeight_lt_one; divisorPrimeClipWeight_mul_step; divisorUnsignedDilationChannel_prime_interpolation (all M,p,d,p>0); mobiusDivisorDilationChannel_prime_interpolation (prime p,p not dvd d).
2. formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimeFibreInterpolation.lean,233 lines, root RHTower. Def mobiusDivisorInterpolatedFibre. 9 public theorems: mobiusDivisorSelectionFibre_prime_interpolation; mobiusDivisorSelectionFibre_insert_interpolation; mobiusDivisorSelectionHead_insert_interpolation; mobiusDivisorSelectionEnergy_insert_interpolation; sum_mobiusDivisorSelectionFibre_sq_le_energy (any Finset of Finset Nat labels); sum_mobiusDivisorInterpolatedFibre_sq (exact Jensen defect); sum_mobiusDivisorInterpolatedFibre_sq_le; sum_mobiusDivisorPrimeFibre_sq_eq; sum_mobiusDivisorPrimeFibre_sq_le.
Both scratch and foreground lake env lean <leaf> -o <exact olean> passed without warnings. All19 new public declarations audited ONCE, only propext, Classical.choice, Quot.sound. Both wired exactly once after MobiusDivisorSquareRootTerminalOrder in RHTower umbrella. No umbrella/full/dependency builds. No old declaration re-audits. No numerical inputs.

## Documentation
New docs/drafts/pipeline/3-formalized/ccm-fu-prime-fibre-interpolation.md: paper proof, exact source, energy, boundaries, audit. Updated PE4 card (new all-cutoff section formal), SD1 card, current-state frontier row+detailed paragraph. Universal STATUS new route-independent MUST-CLIPPED-SOURCE-COMPATIBILITY. Existing anchor homothety and square-root terminal ordering remain valid, not recompiled or audited.

## Research evidence and live next action
Read RHTower/Sieve/RamareEnergy.lean: sum_ramareCofactor_energy_le bounds reweighted coefficient energy, not merged cross energy; cannot claim complete signed bound. PrimeMobiusPhaseFidelity is normalized Bernoulli phase fidelity, not literal divisor source. Corpus queries for mobius supermodular, signed energy potential, mobius total positivity found no applicable producer. Whole-corpus prime overlap and cofactor searches identified prior first-pair/source recursions. The new law fills their ALL-CUTOFF gap and removes p>N restriction by exact cofactor-label exclusion. Next task must attack the actual signed mixed comparison / compatible path using this complete recursion, rather than add another assumed endpoint receiver. RH still not proved.

## Workflow and cleanup
User: one foreground Lean process per agent, scratch checks, only exact needed oleans, no full/umbrella/large rebuilds, audit new work once, cleanup. All owned Lean sessions terminal. Seven task scratch/audit/lint files cleaned at turn end. No subagents authorized, no commits/pushes. Preserve many concurrent edits.
Single global lint run: 10 unrelated concurrent modules missing umbrellas (ThetaCuspFactoredReflectionBound/Error; ThetaCuspFirstAtomScaleSevenProfiles; ThetaCuspScaleSevenEntryErrors/Likelihood; ThetaCuspSharpFiniteCooling; HTGeometry.FirstAtomOddScaleSevenBounds/Lower; LogarithmicLaplaceScoreBounds; ScaleSevenHankelPerturbation). Neither new CCM-FU leaf flagged. Do not repair unrelated concurrent wiring or rebuild them.

## Lean tips
Nat.mod_add_div M p: M%p+p*(M/p)=M. Nat.div_add_mod M p has product first. Prefix sum_range_add + existing integer homothety + sum_range_sub proves exact clipped block. Real.sqrt_lt_sqrt takes nonnegative lower argument then strict comparison. A term can be moved through denominator via div_mul_cancel₀ with clip denominator positive. Sieve.moebius_prime_mul NOT imported by PrimeFibreHomothety; use ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hp.coprime_iff_not_dvd.mpr hpd), then moebius_apply_prime. For inverse insert-label equalities, explicit rw[if_neg (fun h => he (heq.mp h)),if_neg he,if_neg he] works; unnamed function in simp list failed to discharge the implication. Axiom-output parser must handle wrapped lists via re.S.
