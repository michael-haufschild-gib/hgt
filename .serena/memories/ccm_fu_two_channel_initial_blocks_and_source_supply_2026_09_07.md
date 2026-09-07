# CCM-FU: actual initial blocks with two active cofactor channels

Goal remains ACTIVE: unconditional Lean proof/falsification of RH via CCM-FU. RH, SD1, all-cutoff two-prime ceiling, middle quotient profiles, and complete growing adaptive schedule remain OPEN. This goal turn has PROGRESS: 8 new source theorems in 2 verified leaves, including an unconditional nonempty block supplied by the actual prime source. Do not claim a complete schedule or preserved signs after an arbitrary additional small prime.

## Rules
One foreground Lean/lake process per agent. Use lake env lean, no full/umbrella/dependency rebuilds. Generate only needed new oleans. Audit ONLY new declarations ONCE. Clean exact owned scratch/processes. No numerical experiments as proof premises. No subagents/commit/push authorized. Extensive unrelated concurrent work: preserve it.

## Proof chain
Guinand–Weil source -> marked rectangular current -> affine Suzuki checkpoints -> signed curvature -> prime–polar–Gamma/unit-Riesz boundary -> Xi-screw Green -> RH. Current arithmetic bottleneck remains complete signed source/SD1 or full growing adaptive ceiling, not an initial block.

## New leaves, all verified and wired once
1. formal/GaloisForLFunctions/RHTower/MobiusDivisorTwoChannelPrimeBlocks.lean (330 lines, imports MobiusDivisorLargePrimeOrientation, 5 public theorems):
- divisorUnsignedDilationChannel_double_le_half_of_two_mul_le_five_mul:
  all M,p>0 with 2M<=5p, 2 K_(2p)(M)<=K_p(M).
  Private actual D1>=1/10,D2>=0 from harmonic correction at16 and analytic log bounds.
  Exact second block Kp=sqrtp*(sqrt2-1)*D1+(sqrtM-sqrt(2p))*D2.
  Child first block K2p=(sqrtM-sqrt(2p))*D1.
  sqrtM<=8sqrtp/5, sqrt2>=7/5 give expenditure ratio; M<=2p childzero.
- divisorUnsignedDilationChannel_second_block_lower:
  all positive p, 2p<=M<=3p ->sqrtp/40<=Kp.
- exists_divisorUnsignedDilationChannel_mutual_large_quotient_comparison:
  exists T>=1, all M,d,e>0 with T<=M/d and T<=M/e ->Kd(M)<=2Ke(M).
  Same exact-mean unit band and same positive clipped clock on BOTH channels.
  epsilon=(a-1/6)/4; U=a-1/24+eps <2L, L=a-5/48-eps.
- mobiusDivisorOrientedFibre_sparse_prime_block:
  P consists of primes, every distinct pair product>=M, R prime label disjointP:
  O_P(R)=K_productR - sum_pInP K_(p*productR).
  Exact insertion induction, no joint active source. Processed/nonprime labels zero via private direct source lemmas.
- exists_mobiusDivisorTwoChannelBlockParity:
  exists M0, all M>=M0, all L of primes p<M with 2M<=5p and sum_L Kp<=K1,
  EVERY P subsetL has all oriented fibres in [0,original oriented fibre], E_P<=E0,
  V_P<=V0, and every available next prime contracts E_P.
  At M>=10 pair products>=M; d>=3 childzero. Head budget + 2K2p<=Kp + K1<=2K2 controls cofactor2.
  It does NOT assert parity after an arbitrary next prime.

2. formal/GaloisForLFunctions/RHTower/MobiusDivisorTwoChannelPrimeSupply.lean (192 lines; imports new blocks + DivisorUniformSquareRootBound, 3 public theorems):
- divisorUnsignedDilationChannel_two_channel_window_lower:
  every p in primesInIoc(8N,9N), Kp(20N)>=sqrtN/20.
- eventually_two_channel_window_covers_unit_source:
  full actual pool mass eventually >=K1(20N).
  Corpus PNT window ratio9/8 yields card>=x/(16logx), x=8N.
  logx<=2(sqrtx-1) yields >=sqrtx/32, eventually >=700 primes.
  pool mass>=35sqrtN>=7sqrt(20N)>=K1(20N).
- eventually_exists_mobiusDivisorTwoChannelPrimeBlock:
  unconditionally for all sufficiently large N exists NONEMPTY L subset primesInIoc(8N,9N),
  head 0<=F_L(empty)<=sqrt(20N)/15;
  0<=O_L({2})<K2(20N) (strict positive child expenditure for every selected prime);
  E_L<=V0+(20N)/225;
  EVERY P subsetL preserves all parity, E_P<=E0,V_P<=V0,and every available nextprime contracts.
  Nonempty selection: preselect one pool prime (weight<=sqrtM/15<=K1), then existing cover-from-below theorem on remainder.
  No assertion L has at least2 primes, no consumption of full pool, no full growing schedule.

## Verification COMPLETE — do NOT repeat
Both scratch files and exact leaves passed lake env lean.
Generated ONLY the 2 required new oleans with direct -o (base needed by supply, supply needed by own axiom scratch).
8 new public theorems axiom-audited ONCE: only propext, Classical.choice, Quot.sound. No sorryAx/Lean.ofReduceBool/newaxioms.
Formal lint PASS, 132 existing largefilewarnings only.
Formal declaration index refreshed once (reported1changed due concurrent indexing).
New card links, added references, newfile whitespace, scoped git diff --check, both umbrella imports verified.
Owned /tmp/ccm_fu_two_channel.lean, /tmp/ccm_fu_two_channel_supply.lean, /tmp/ccm_fu_two_channel_axioms.lean removed.
Strict final ps executable snapshot: ZERO lean/lake. No running process handles. No numerical diagnostic this turn.

## Docs
Stage3 complete paper proof:
docs/drafts/pipeline/3-formalized/ccm-fu-two-channel-prime-blocks.md.
Own stage1 card promoted/removed.
Updated current CCM-FU row + detailed paragraph in rh-current-frontier-map.md;
adaptive-prime-ceiling.md; mobius-divisor-source-diagonal-dominance.md.
Universal STATUS existing MUST-PRESERVE-NEXT-STEP-ORIENTATION now includes budgeting every changed component, actual expenditure/reserve ratios, and support justification for dropping joint terms.

## Next work
Need move beyond selected initial corrections toward control that remains valid through enough interacting operations to consume every required prime. The actual two-channel expenditure identity can support such analysis, but the present theorem controls only a head-budgeted initial block. Arbitrary smaller-prime sign changes remain a real obstruction. Do not pass off another conditional wrapper, finite diagnostic, or initial block as the missing complete cancellation proof.
Previous memory: mem:ccm_fu_large_prime_orientation_and_middle_quotient_frontier_2026_09_07.
