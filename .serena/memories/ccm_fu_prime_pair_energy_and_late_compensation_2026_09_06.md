CCM-FU: concrete first-prime cancellation is CLOSED, and every uniformly budgeted prime-elimination producer (PE1/PE2) is terminal. RH and SD1 remain OPEN; keep active goal intact. This builds on all-cutoff U1/U2 in mem:ccm_fu_unsigned_orientation_closed_2026_09_06; do not reprove or re-audit those.

Chain remains completed Guinand–Weil -> marked current -> Suzuki checkpoints -> signed curvature -> coherent prime–polar–Gamma/unit-Riesz boundary -> Xi-screw Green -> RH.

New module formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimePairEnergy.lean (99 lines):
- mobiusDivisorPrimePair M p d = mu(d)*(K_d(M)-K_(pd)(M)).
- sum_mobiusDivisorPrimePair {p}(Prime p) M preserves complete S when summed over p-free d<=M.
- sum_mobiusDivisorPrimePair_sq_eq identifies paired energy as Q - 2 sum_(p-free d)mu(d)^2 K_d K_pd.
- sum_mobiusDivisorPrimePair_sq_le closes first-prime contraction for every prime and cutoff using all-cutoff unsigned K>=0.
Reuses Sieve.moebius_prime_mul and sum_Icc_filter_dvd_reindex from EulerDeletionQuasiShuffleConvergence. These oleans existed; no dependency rebuild needed.

New module MobiusDivisorLatePrimeCompensation.lean (263 lines):
- mobiusDivisorLatePrimeMass M := T(M)=sum_(M/2<p<=M, prime)K_p(M).
- mobiusDivisorLatePrimeMass_four_mul_ge: T(4N)>=card(primes in (2N,3N])*sqrt N/40.
- tendsto_mobiusDivisorLatePrimeMass_div_atTop: T(4N)/(4N)->+infinity.
- mobiusDivisorHalfPrimeHead M := H(M)=sum_(d<=M, all p in d.primeFactors satisfy p<=M/2) C_d(M).
- mobiusDivisorHalfPrimeHead_sub_total: H(M)-S(M)=T(M), exact at every natural M.
- tendsto_halfPrimeHead_add_total_abs_div_atTop: (abs H(4N)+abs S(4N))/(4N)->+infinity.
- not_uniform_halfPrimeHead_and_total_linear: no real C uniformly bounds abs H+abs S by C*M.
- not_uniform_halfPrimeHead_and_total_quadratic: no C uniformly bounds H²+S² by C*M².
- not_uniform_halfPrimeHead_and_total_diagonal: no C uniformly bounds H²+S² by C*Q(M), where Q=sum C_d².
All public target source laws are unconditional. No assumption about RH or SD1 is used; p-prime is just the natural parameter restriction of the first pairing theorem.

Proof: the first-block channel for 2N<p<=3N at M=4N equals D(1)*(sqrt(4N)-sqrt p). Analytic harmonic half-error at4 and log-two upper bound give D1>=1/10; sqrt p<=7/4 sqrt N gives Kp>=sqrt N/40. All other late channels are nonnegative. The existing GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge in HTGeometry/AbelianZetaGas/PrimeWindowCount gives count>=N/(2log(2N)) eventually. Thus T(4N)/(4N)>=sqrt N/(320log(2N))->infinity. This uses the corpus unconditional PNT, not numerical counts. Any d<=M with a prime factor >M/2 is that prime itself. Hence H omits exactly the negative late-prime coefficients and H-S=T. Triangle and scalar square bounds force no common linear/quadratic budget; Q<=722M² excludes a fixed original-diagonal multiple.

Interpretation: after all primes up to M/2 are eliminated via (1-L_p), the d=1 coefficient is H. This follows by expanding the finite commuting differences: squarefree smooth products have exactly their mu coefficient and terms beyond M vanish. The stage energy includes H²; the terminal stage is S². Any uniform stage/original ceiling would bound H²+S² by twice that ceiling times Q, contradicting the closed theorem. This does NOT refute SD1; if S has its desired bound, the intermediate head must carry a large late-prime contribution. A proof must allow large intermediate amplitudes and control genuine final signed compensation, not another bounded-energy elimination path.

Research card moved to docs/drafts/pipeline/5-failed/ccm-fu-prime-pair-energy.md with dependency-closed paper proof and both positive survivors. SD1 card, frontier current-state row/detail/terminal table, and MUST-217 updated. Universal addition: no common intermediate/final bound when their exact difference has positive mass growing faster than that bound.

New numerical guidance only: docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-prime-pair-energy-2026-09-06. Frozen PE1=successive energy decrease, PE2=all stages<=original Q, increasing prime order, every M1..1024. PE1 first fails M5,p3: .00609689583812863 -> .00706214354756525. PE2 first fails M198,p43: 48.46632844675 > 48.39472170756, ratio1.00147963944537. Largest screened ratio4.10914953517 atM903,p223. Full stages.csv saved. Independent direct half-order sums plus explicit smooth-factor coefficient expansion confirm first two failures at70-digit precision in direct-audit.json. No computation enters Lean. Do not rerun screens without a new question. Finite witness cutoffs themselves were not formalized; the stronger all-scale obstruction is analytic and formal.

Both modules checked in foreground with lake env lean, exact oleans produced, wired once into RHTower.lean. Only TEN new public declarations audited once: exactly propext, Classical.choice, Quot.sound. No added or computational certificate axioms. Do not repeat old axiom audits. No large/umbrella build. Latest user insists serial Lean and cleanup. All own Lean sessions completed; five task scratch files were removed. Formal index refreshed. Global formal lint currently FAILS only because another concurrent task created HTGeometry.AlternatingPairJetIntegral without wiring it into HTGeometry.lean. Do not claim global lint passed. Both new CCM-FU modules are wired once and individually checked; no unrelated file was modified to mask that concurrent failure.

Toolchain details: global isLittleO_log_rpow_atTop (NOT Real.isLittleO_log_rpow_atTop). tendsto_atTop_mono' takes explicit filter first. Function inverse may require hinv.congr with change (log x/sqrt x)^-1=...; simp Pi.inv_apply did not rewrite it. abs_sub_le is ternary; use middle0 and simp sub_zero/zero_sub/abs_neg for abs(H-S)<=absH+absS. abs_sub_le_abs_add_abs is unknown. Rewriting a predicate under a decidable finite-forall ite can fail dependent motive; simp only [iff] works. Put whitespace after closing absolute-value bar before multiplication (`|C| * 722`); `|C|*` tokenizes badly.
