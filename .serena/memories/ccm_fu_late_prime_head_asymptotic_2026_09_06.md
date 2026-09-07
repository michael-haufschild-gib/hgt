CCM-FU active goal: unconditional Lean RH proof/falsification; RH and SD1 remain OPEN. This turn made verified progress; do not mark goal complete or blocked.

New module formal/GaloisForLFunctions/RHTower/MobiusDivisorLatePrimeHeadAsymptotic.lean (namespace RHTower) proves seven unconditional public declarations:
1 tendsto_psiDefect_mul_log_div: psiDefect(k)*log(k)/k→0.
2 sum_mobiusDivisorDilationChannel_eq_psiDefect_abel: complete sum S over Icc1M equals sum k in Ico1M of (sqrt(k+1)-sqrtk)*psiDefect(k), including zero cutoffs.
3 tendsto_sum_mobiusDivisorDilationChannel_log_normalized: S(M)*logM/(M*sqrtM)→0.
4 eventually_mobiusDivisorLatePrimeMass_ge: eventually N*sqrtN/(80log(2N))≤T(4N).
5 tendsto_total_div_mobiusDivisorLatePrimeMass: S(4N)/T(4N)→0.
6 tendsto_mobiusDivisorHalfPrimeHead_div_latePrimeMass: H(4N)/T(4N)→1.
7 tendsto_mobiusDivisorHalfPrimeHead_div_atTop: H(4N)/(4N)→+∞.

Inputs all from corpus: ChebyshevPsiErrorInputs.exists_psi_error_eventually; Sieve.TwoRangeSchedule.tendsto_logRpow_mul_expSaving; exact Möbius inversion; mathlib Real.log_div_sqrt_antitoneOn (Ici exp2); Tendsto.cesaro; prior late-prime mass lower count and exact H-S=T. Proof: a(k)=abs(psiDefect(k)*logk/k)→0 by PNT. For M≥k≥exp2, step(k)*abs(psiDefect(k))*logM/sqrtM≤a(k), using step(k)*sqrtk≤1. Finite early prefix vanishes after normalization; late sum is bounded by Cesaro(a). T lower gives abs(S/T)≤640abs(S(4N)log(4N)/(4N sqrt(4N))) eventually. Exact H-S=T gives H/T→1 and H/(4N)→∞.

Meaning: actual intermediate head itself, without assuming a bound on final S, carries superlinear late-prime mass. Leading relative compensation is proved. This is NOT the critical S(M)=O(M) source bound and does NOT imply SD1 or RH. Do not propose another relative normalization as if it closes critical residual. Next research must target signed residual at linear scale.

Validation: scratch passes; final leaf passes `lake env lean GaloisForLFunctions/RHTower/MobiusDivisorLatePrimeHeadAsymptotic.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/MobiusDivisorLatePrimeHeadAsymptotic.olean` with no output. One exact olean, no old dependency builds, no umbrella or large builds. Module wired once into RHTower.lean. A single /tmp axiom audit of only seven new declarations gives exactly propext, Classical.choice, Quot.sound. Do not repeat these audits. Global formal lint PASSES now with existing size warnings; previous unrelated AlternatingPairJetIntegral wiring failure resolved concurrently. Index refreshed.

Docs: new card moved to docs/drafts/pipeline/3-formalized/ccm-fu-late-prime-head-asymptotic.md, dependency-closed paper proof and certificates. Updated SD1 card, failed prime-pair card's strongest positive survivor, frontier CCM-FU row/detail/terminal row. Universal STATUS MUST-217 adds route-independent requirement to quantify cancellation at final required scale; vanishing relative error at a larger diverging mass does not imply smaller-scale absolute bound. Preserve other concurrent docs edits.

Cleanup: /tmp/ccm_fu_head_api.lean, /tmp/ccm_fu_head_asymptotic.lean, /tmp/ccm_fu_head_axioms.lean removed. All task Lean sessions terminal, ps confirms 0 owned task Lean processes. No numerical experiments this turn.

API lessons: use explicit real Nat.cast Tendsto when inference ambiguous. `tendsto_id.const_mul_atTop` is a semifield lemma, does not apply to Nat; use tendsto_atTop_mono (fun N:Nat => show N≤4*N by omega) tendsto_id. Imported duplicate real LE instances can leave convert goals Real.instLE=Real.partialOrder.toLE; use `convert h using 1 <;> first | rfl | ring`. push_cast at both h and target before comparing logs of Nat products. RHTower.add_le_add_left is shadowed/reordered: use add_le_add le_rfl htail. Avoid one-line nested have with semicolon; it misparses proof continuation. Real.log_div_sqrt_antitoneOn available from Mathlib.Analysis.SpecialFunctions.Log.Monotone. Prior memory: mem:ccm_fu_prime_pair_energy_and_late_compensation_2026_09_06.