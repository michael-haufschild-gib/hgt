# CCM-FU: actual complete coprime-column transport

Goal remains ACTIVE. RH NOT proved. Frontier map READ ONLY; this turn did not edit it. No computations this turn. No subagents.

Card: docs/drafts/pipeline/1-in-progress/ccm-fu-coprime-column-transport.md.
New leaf: formal/GaloisForLFunctions/RHTower/MobiusDivisorCoprimeColumnTransport.lean, imported in RHTower.lean beside RetainedPrimeTopHomothety.

Five unconditional theorems: coprime_moebius_floor_summatory; coprime_moebius_primeFreeDivisorDefect; mobiusDivisorCoprimeHead_eq_supported_abel; mobiusDivisorCoprimeHead_succ_sub; mobiusDivisorGcdCross_one_eq_coprimeHeads.

Actual math: complete coprime Möbius inversion of floorSummatory F leaves sum of F(floor(N/n)) over n whose prime factors divide r. D=primeFreeDivisorDefect is floorSummatory psiDefect, so the actual column retains signed psiDefect, not the supported-index count. H_r(M)=sum k<M sqrtStep(k) sum supported n<=k psiDefect(k/n), exact weights/endpoints. Primitive cross G_1(M)=sum d<=M C_d(M) H_d(M)-C_1(M)^2. The subtraction is the unique coprime diagonal pair.

Direct attempt to transfer the existing subpower supported-count floor-column estimate to actual divisor-Abel channels did NOT yield the needed magnitude bound. n=1 occurs in every inner column and retains the full defect. The remaining target is cancellation in the actual outer pairing sum mu(d) U_d(M) sum_k sqrtStep(k) sum_supported psiDefect(k/n), retaining nonprimitive gcd sectors for the full energy. Do not claim identities improve the O(M) complete-head bound or prove RH. Do not add more transport wrappers as a substitute for this estimate.

Broader OR searches used --any (AND is default). Relevant extra inspected modules EulerDeletionCompletedColumnMain, EulerDeletionCoprimeHeadSubpower and EulerDeletionCoprimeCrossCompletion have different kernels/weights; their quantitative results do not directly bound the actual Abel pairing.

All new theorems scratch-checked; installed leaf olean. Axioms audited ONCE for only the five new theorems: propext, Classical.choice, Quot.sound. Final cache-only exact leaf lake build passed (75s, byte-identical source, fresh olean). No dependency/full/umbrella builds. Corpus index and formal lint passed. All owned /tmp scratch files and final cache audit directory removed; no owned Lean/Lake processes remain. Do not repeat these audits.

STATUS existing reversible-transform entry extended with general fact: counting surviving indices leaves their source weights uncontrolled, linked to this card. Shared tree has unrelated concurrent modifications (including frontier edits by others); preserve them.

Previous turn: mem:ccm_fu_charge_safe_order_2026_09_08; earlier arity formal work: mem:ccm_fu_arity_charge_2026_09_08.