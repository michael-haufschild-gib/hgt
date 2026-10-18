# Exact correction-tail phase cells and mass — 2026-10-18

Persistent goal: unconditional RH in Lean, still NOT achieved. This turn made verified WL/RW progress by producing an actual fixed-window tail mass lower bound and transferring it through literal normalized smoothing. Predecessor: `mem:biscale/factorial-muntz-tail-prime-polar-budget-2026-10-18`.

## Artifacts and status

Card `docs/drafts/pipeline/3-formalized/factorial-muntz-tail-phase-mass-2026-10-18.md`; active parent `docs/drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md` updated. Two leaves in `formal/GaloisForLFunctions/BiScaleUncertainty`, each imported exactly once by its umbrella:

- `FactorialMuntzTailPhaseCells.lean`: 6 public theorems +1 definition. SHA256 `868a0b72a7dc0ca2b424af13f3d4f3565cbf6deb3635edf61187c089ec1068c9`. Imports only FactorialMuntzUniformTail.
- `FactorialMuntzTailMass.lean`: 11 public theorems. SHA256 `810e6f1953bddd0cbab112581e4a7e645019f91fdc8ac58dfcf776258a63ce67`. Imports PhaseCells and TailPrimePolarBudget.

Namespace `GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar` throughout. Both final direct `lake --old env lean -j 1 <leaf> -o ...` checks pass without errors or warnings. API probes and all18 public declarations pass `/tmp/bsu-tail-mass-axioms.lean`, using only propext, Classical.choice, Quot.sound. Source hashes rechecked unchanged; all4 card links resolve.

Evidence `/tmp/bsu-tail-mass-verification.json`, `/tmp/bsu-tail-mass-leaf.log` (empty clean final output), `/tmp/bsu-tail-mass-axioms.log`. `scripts/formal_tools.py index` passed. `lint --check-generated` exited1 for a single unrelated missing RHTower umbrella import: `GaloisForLFunctions.RHTower.GammaThetaFullSupportCreation`, plus381 size warnings. Previous BVI missing-import failure was fixed by concurrent work. Generated catalogs current at this gate. Logs `/tmp/bsu-tail-mass-index.log`, `/tmp/bsu-tail-mass-lint.log`. All own handles terminal; no build snapshot, full build, heartbeat increase, computation/experiment, web/novelty audit or commit. Preserve concurrent unrelated edits.

## Exact mathematics

N=n+1, epsilon=sourceFactorialCollar N, T_n=factorialMuntzCorrectedTail n, U_(n,k)=factorialMuntzSmoothedTail n k.

`sourceFactorialCollar_scaled_le_twelfth {N} hN` proves N*epsilon<=1/12 from the actual cubic identity (1+epsilon)^3=1+1/(4N). No asymptotic collar assumption.

`clampedLatticeSum_eq_nat_of_cell {epsilon a t} hε ha ht m hm0 hm1`:
 if m<=a/t and a*(1+epsilon)/t<=m+1, the literal infinite clamped sum equals m. Proof counts m exact unit samples and proves every later term zero, including endpoints. No floor expansion or sampling experiment.

`factorialMuntzSum_eq_zero_on_phase n j hj1 ht hy0 hy1`:
 j<2N, t>0, j<=N/t<=j+1/16 imply factorialMuntzSum n t=0. No lower bound on j is required (stronger than initial plan). The collar shift epsilon*(N/t)<=1/6; for d=1,2,4 the counts are d*j, so 4j-4*(2j)+4*j=0.

`factorialMuntzTailPhaseCell n j` is Icc(log(N/(j+1/16)), log(N/j)). For N<=j<2N:
- `factorialMuntzTailPhaseCell_nonpos` and `_bounds` derive the logarithmic-phase inequalities.
- `factorialMuntzCorrectedTail_on_phaseCell` gives T_n(x)=exp(x/2)/(2*sqrt N), exactly, including endpoints.
- `factorialMuntzTailPhaseCell_subset_window` puts the cell in [-log2,0].
- `factorialMuntzTailPhaseCell_disjoint n i j hi hij` proves disjointness when N<=i and i<j.
- `factorialMuntzTailPhaseCell_sq_integral` computes the exact squared integral as (1/4)*(1/j-1/(j+1/16)).
- `factorialMuntzTailPhaseCell_sq_integral_lower` bounds it below by 1/(256*N^2).

`factorialMuntzCorrectedTail_sq_integrable` uses the literal global exponential envelope. Summing N disjoint cells gives the main unconditional endpoint:
`factorialMuntzCorrectedTail_sq_integral_window_lower n` (line105):
  1/(256*N) <= integral_[Icc(-log2,0)] T_n(x)^2 dx.
`factorialMuntzCorrectedTail_sq_integral_lower n` gives the same whole-line lower bound.

`factorialMuntzSmoothedTail_tendsto_ae n` uses the actual normalized bump approximate identity and Lebesgue measure. The uniform rate3/2 envelope produces an integrable square majorant, so `factorialMuntzSmoothedTail_sq_integral_tendsto n` proves convergence of the full squared-mass integral to the literal tail mass. This statement is squared-mass convergence; do not describe it as an explicit L2-difference convergence theorem.

`factorialMuntzSmoothedTail_sq_integral_eventually_lower n` (line180): eventually k, integral U_(n,k)^2 >=1/(512*N). Threshold may depend on n.

`factorialMuntzSmoothedTail_zero_arch_mass_budget n` (line193): eventually k,
 |Re W(U,U)-Arch(U)| <=512*(factorialMuntzTailPrimeBudget+144*exp(1)^2)*integral U^2.
Constant is independent of n, smoothing threshold may depend on n. This uses the previous actual prime/pole budget, keeping both polar branches. No source/domain/convergence/positivity premise at the actual endpoints. It is not an archimedean growth or positivity claim.

## Remaining frontier and concrete next conjecture

The actual normalized tail cannot lose mass faster than1/N and already has enough mass in a fixed compact window. Need actual low-frequency/weighted-primitive suppression to obtain logarithmic archimedean growth. Mixed terms and the original compact-ramp coupled margin remain open; neither all-source RW positivity nor RH follows yet.

Relevant source inspected: `formal/GaloisForLFunctions/RHTower/WeilWorkExposingRayPrimitiveSharpness.lean`, namespace RHTower.ExposingRayPrimitive. `logarithmic_mass_ratio_bound hf hs` proves
 (log(fourierMass f/primitiveMass f)/4-coercivityConst)*fourierMass f <=archEnergy f
 for compact C2 sources. fourierMass=integral |paperFT f(tau)|^2; primitiveMass=integral |paperFT f(tau)|^2/(tau^2+1/4)^2. `fourierMass_eq` keeps the exact 2*pi conversion. Its compact-support/domain hypotheses have NOT yet been discharged for the noncompact smoothed tail; the fixed-window mass bound may support compact localization.

Concrete conjecture from the existing exact clamped-lattice remainder R(y)={y}(1-{y})/2: Q(r)=r^2/4-r^3/6-r/12 has equal endpoint values and derivative R(r)-1/12. A bounded periodic extension should supply a bounded primitive of every R(a*(1+epsilon)*y)-R(a*y). All relevant y are positive (at least N); check the existing Nat.floor convention when connecting to any Int.fract/Bernoulli API. Integrating by parts against the literal Mellin weight aims at |tail readout_(1/2+i*tau)|<=C*(1+|tau|)/N^(3/2). That would bound weighted primitive mass by O(N^-3), against the newly proved mass Omega(N^-1), suggesting a logarithmic ratio. This cancellation estimate, its analytic exchanges, and compact localization remain UNPROVED; do not turn them into assumed wrappers.

Corpus query `factorial Muntz tail logarithmic archimedean translation energy lower bound` saved `/tmp/bsu-tail-arch-search.json`; candidate/source-argument summaries all inspected. partial=false but background refresh incomplete and substantial compiler-pending/stale coverage; relevant source APIs verified in actual Lean. Keep user constraints: no old Markdown research browsing, no web/novelty, no numerical experiments, one own foreground leaf Lean process, no full builds; README/frontier map read-only.

## Lean API repairs learned

Use Nat.card_Ico, not Finset.card_Ico. `Real.log_div` needs both nonzero proofs. `setIntegral_congr_fun` can leave beta-redex functions: use explicit `change` before rewriting. Avoid `on` notation without its scope; explicit lambda relation works for Set.Pairwise (S : Set Nat). For dominated convergence, explicitly give the envelope and `refine ... ?_ ?_ hi ?_`; `apply ... _ _ _ hi` left the envelope as an extra goal. Unneeded `ring` after `field_simp` caused warnings and was removed. All such repairs are in the final clean source.
