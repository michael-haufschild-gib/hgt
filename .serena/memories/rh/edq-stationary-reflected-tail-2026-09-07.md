# EDQ whole outgoing stationary-tail cancellation — verified; RH open

Goal remains unconditional closed Lean proof/falsification of RH through EDQ. Neither achieved. Keep goal active. Previous SHR turn was verified progress; this SRT turn proves full outgoing-sector identities and quantitative bounds, not another small threshold extension.

## New source
`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryReflectedTail.lean`: 453 lines, 30 declarations (24 theorems, six definitions), namespace RHTower.DeletionMixedRefinement. Imports ArithmeticStationaryQuadrantComparison, ReflectionCocycleClass, VanDerCorputWeightedSecondGeneral. Wired once after ArithmeticStationaryHeightReserve in RHTower.lean.

For s=sigma+it,t>0, B=t/(2*pi), b_k=B/k. Define stationaryOutgoingAtom s N k=N^(star s+1)*integral_Ioi(b_k) bernoulliFourierTerm(-k,star s,x), and stationaryIncomingAtom analogously on Ioc N b_k. Define common factor C=stationaryReflectedTailFactor s N=N^(star s+1)*integral_Ioi(B) term(-1,star s,x).

Existing integer-frequency dilation extends to positive real integration cutoffs with Jacobian. This proves exactly T_k=C*k^(star s-1). Every positive finite frequency set F has sum T=C*sum_F k^(star s-1) and EXACT norm product; cancellation retained before norms. For K with 2*pi*K*N<=t and sigma>0,N>=1, negativeFourierSection s N K=H(s,N,K)+C*rawPrefix(1-star s,K), H=stationaryIncomingSection=sum incoming actual heads. In particular this holds for full stationaryComplexBudget at K=floorNat(t/(2*pi*N)).

At a strip zero, powerSum_zeta_star and riemannZeta_one_sub_eq_zero_iff remove reflected zeta only. Exact reflected prefix is K^(star s)/(star s)+K^(star s-1)/2+powerSumRemainder(1-star s,K). These terms MUST remain; reflection is not a selector.

## New quantitative estimate
For a>0,beta>1,t>=1,omega>0,omega*a=t, complete actual mode integral over Ioi a of x^-beta exp(i*(-omega*x+t*log x)) has norm <=28*a^(1-beta)/sqrt(t). Proof: weighted second-derivative bound on [a,2a] costs 20*a^(1-beta)/sqrt(t); after 2a conjugate phase speed>=omega/2, weighted first-derivative bound plus improper limit costs <=8*a^(1-beta)/sqrt(t). No asymptotic or numerical certificate.

Define stationaryReflectedTailEnvelope Q(s,N)=28*N^(sigma+1)*w_1*B^(-sigma-1)/sqrt(t). norm C<=Q for sigma>0,t>=1,N>=1. Full outgoing family bound Q*norm(reflected coefficient sum) retains cross-frequency cancellation. Full source inequality bounds scaled Im g by Im H + Q*norm(rawPrefix reflected K) + positive-frequency ceiling - negative mean.

At every strip zero, K>=1, explicit reflectedPrefixZeroEnvelope P(s,K)=K^sigma/norm(s)+K^(sigma-1)/2+norm((1-star s)*(2-star s))/(2-sigma)*K^(sigma-2). Existing centered-remainder estimate proves norm rawPrefix reflected <=P. Consequently norm(negativeFourierSection-H)<=Q*P with no unproved source input. Every closed-right strip zero has nonempty unit stationary sector. `stationaryIncomingSection_im_lowerBound_at_closed_right_zero` transfers old displacement+mean-ceiling lower bound to actual incoming H after subtracting Q*P.

Key theorem names: stationaryOutgoingAtom_eq_reflected_term; sum_stationaryOutgoingAtom_eq_reflected_sum; norm_sum_stationaryOutgoingAtom_eq; stationaryComplexBudget_eq_incoming_add_reflected; rawPrefix_reflected_eq_at_zero; norm_integral_logarithmicFourierMode_at_saddle_le; norm_stationaryReflectedTailFactor_le; normalizedWeightedRemainder_scaled_im_le_incoming_reflected; norm_negativeFourierSection_sub_incoming_le_at_zero; stationaryComplexBudget_eq_incoming_reflected_at_zero; stationaryIncomingSection_im_lowerBound_at_closed_right_zero.

## Limits and next frontier
Remaining actual source is cumulative incoming/pre-saddle aggregate H, compared against complete opposing sectors while retaining explicit outgoing error. No sign or sufficiently small upper bound for H proved. Do not claim QP fits opposing budget at every parameter. Existing positive-frequency ceiling almost cancels mean, so generic outgoing norm control alone does not settle that comparison. Conclusions include critical zeros; no RH selection claimed.

Possible next investigation, NOT PROVED HERE: finite Fubini after the same frequency dilation may write H as N^(star s+1)*integral from N to B of first-frequency term(y)*rawPrefix(1-star s,floor(y/N)) dy. This would expose the full incoming source as a cutoff-dependent reflected-prefix integral; it is not itself a sign law. Check corpus, write paper card, and control endpoint/floor conventions before formalizing. Avoid replacing the global head comparison with more coordinate identities or tiny cutoff extensions.

## Audits DONE — do not repeat
Complete scratch passed without warnings. Final foreground LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryReflectedTail compiled EXACTLY ONE leaf in 4.5s (9903 jobs are cached dependency traversal/replay, not compilations). New-only /tmp axiom audit exact-matched all 30 declarations: only propext, Classical.choice, Quot.sound. No prior declaration rebuilt/re-audited. Own-tree declaration basename collision search passed. Final source counts, exact audit-name coverage, single umbrella import, promoted certificate, whitespace checked; git diff --check passed.

Global formal lint FAILED only on concurrently added unwired `GaloisForLFunctions.RHTower.ThetaCuspAllOrderLikelihoodCooling`, outside this work; no own-leaf error. Do not modify/rebuild/re-audit unrelated work or repeat unchanged lint. Index refreshed once: 32744 files,399826 declarations,3911 gap markers.

Owned handles all terminal: probe87373 (one unknown HardyZ name, replaced by existing powerSum_zeta_star); scratch93956,4689,16330,49063,14778; build52038; lint50619; new-only audit93512. Process check found no own Lean/Lake. Removed /tmp/edq_reflected_tail_probe.lean,edq_reflected_tail.lean,edq_reflected_tail_axioms.lean,edq_reflected_tail_names.txt. Logs retained /tmp/edq_reflected_tail_{build,axioms,lint,index}.log. No numerical experiments/computational certificates/new axioms; no commits.

## Documentation
Promoted `docs/drafts/pipeline/3-formalized/edq-stationary-reflected-tail-sum.md`, complete paper proof, quantitative estimates, exact scope, audit records. Frontier current EDQ paragraph and row updated; unknown cumulative incoming head and explicit outgoing error identified. STATUS existing 'Must compare magnitudes in an oppositely signed decomposition' now explains retained coefficient-sum cancellation; header date updated to 2026-09-07 after current environment date changed. Preserve concurrent repo edits.

Lean discipline persists: one owned foreground process; scratch lake env lean; final targeted leaf lake build --old only; no umbrellas/full rebuilds; new-only axiom audit and cleanup.