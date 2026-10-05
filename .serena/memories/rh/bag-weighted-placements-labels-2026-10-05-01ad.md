BAG continuation01ad complete; RH goal ACTIVE. No signed physical cubic saving or uniform growing-profile estimate. Hard gaps: actual rational-node grouping/normalization and full near-cone/tail transfer, signed o(N/log²N), growing moments, moving cofactors, common-height self-return. No subagents, computations/experiments, resource hacks, axioms, full builds, commits. One foreground owned Lean process at a time; final lake --old env lean leaf -o. ALL owned processes terminal; /tmp completed scratch sources removed, logs/search JSON retained.

Two new production leaves, namespace RHTower.BAGTrace:
1. ChiRamanujanWeightedDistinguishedCubic (223lines,15 public, production77712 exit0 emptylog). Imports ChiRamanujanWeightedThirdShift.
- weightedValuationDiagonal z x y k v := if v1+v2=k then c_z(v1)c_z(v2)x^v1 y^v2 else0. Its HasSum is finite sum i=-1..k+1, ALL integer k and complex zxy, via finite pair atoms.
- weightedConeOffset W_k summand c_z(i)c_z(j)c_z(i+j+k)x^i y^j.
- coefficient predecessor private: c(t-1)=c(t)+h atom(-1)t-(1+h)atom0t, h=z/(1-z), valid evenz1.
- weightedConeOffset_pred exact pointwise identity for ALL k.
- D_-1=-h(x^-1+y^-1), D0=1-h(y/x+x/y), D1=x+y-h(y²/x+x²/y).
- W_-1=W0-h²(x^-1+y^-1)-(1+h)D0; W_-2=W_-1+hD0-(1+h)D1; full HasSum for ||x||,||y||<1.
- weightedConeEuler chooses four explicit values ONLY used for -2<=k<=1. weightedConeOffset_hasSum uses that range.
- weightedShiftedLocal zxy a b c; translation for nonzero x,y to x^-a y^-b W_(c-a-b), full HasSum.
- primeWeightedShiftedLocal_hasSum p tau upsilon (a b c : Fin2) unconditional with z=p^-1, x=p^(-1-i tau), y=p^(-1-i upsilon). All placements including coincidences.
- finitePrimeWeightedShiftedCubic_hasSum for every finite prime set and arbitrary Fin2 placement functions, complete (Z²)^P lattice, no analytic hypotheses. No infinite-prime or Mellin integral interchange.

2. ChiRamanujanDistinguishedPrimeLabels (117lines,6public incl2abbrev, production87443 exit0 emptylog).
- ramanujanDistinguishedPrimeEntry P p n = logp (I_p(n)-I_p²(n)) prod_(q in Pprime erasep)(1-I_q(n)).
- nonneg for primep; composite band entry individually0 since sum of nonnegative entries equals actual known prime-only multiplier0.
- RamanujanBandPrime M subtype prime inrange(M+1), RamanujanCoveredCoordinate M subtype Icc2M.
- ramanujanDistinguishedPrimeEntry_band M p n = ifn=p thenlogp else0; NO hypotheses beyond finite subtype domains.
- ramanujanDistinguishedPrimeEntry_projector: entryproduct times ACTUAL ramanujanNoncontractingProjector(M+1) on triple Fourier character equals entryproduct times that character with label exclusion p=r OR q=r. Both contractions and intersection retained. This closes physical label matching, not rational node grouping or old valuation-axis matching.

All21 public names checked by axiom25745 exit0, only propext/Classical.choice/Quot.sound. Index30505 exit0; all21 API entries and exactly one umbrella import each checked. Lint75464 exit1,33 unrelated unreachable modules, no new-leaf/proof-debt error. Global lint NOT clean. Frontier C28.56ag.9, P2/P3 bag-weighted-distinguished-cubic, P1 bag-critical-distinguished-prime-source, workinglog current.

Search86824 /tmp/bag-weighted-shifts-search-01ad.json: partial filter/judge malformed JSON, full65733 inventory, background refresh incomplete compiler mostlysource_only/pending. All20+20 and ingredients inspected. Exact weightedThirdShift lexical searched/revalidated.
Search97782 /tmp/bag-rational-node-grouping-search-01ad.json: partial interrupted text retrieval, full65736 inventory, same refresh/compiler limitations. All20+20/ingredients inspected. Useful sum_filter_reducedModulus_eq in EstermannRamanujanMainTerm lines46-101 (exact residue grouping). Infinite pmPowerDampedRamanujanWeight_eq_euler requires epsilon>0, cannot shortcutcriticalfinite.

NEXT CONJECTURE (NOT PROVED): Actual critical grid mass.
Q=ramanujanPrimeRadical(P)^2. Group ALL literal critical prime-only atoms modulo1 at k/Q, k:ZModQ.
For retainedprimep define d_p(k)=I_(p²|k.val)-I_(p|k.val)/p, t_p(k)=I_(p|k.val)/p-1/p².
Target groupedmass G_P(k)=sum_p logp*t_p(k)*prod_(q!=p)d_q(k).
Local full Fourier multipliers expected: d_p ->1-I_p(n), t_p ->I_p(n)-I_p²(n). FiniteCRT and existing audited ALL-INTEGER critical-source factorization should prove equality by finiteDFT injectivity.
CRT inverses produce units in character coordinates, but divisibility indicator multipliers invariant under units.
DO NOT implement CRT from scratch: source-read Mathlib/Data/ZMod/QuotientRing.lean lines78-93:
ZMod.prodEquivPi (a:ι→Nat) (coprime:Pairwise(Nat.Coprime on a)) : ZMod(prod_i a_i) ≃+* Pi_i ZMod(a_i);
ZMod.prodEquivPi_apply = castHom(dvd_prod_of_mem...) component.
ZMod.equivPi also factors Nat modulus by its prime factorization.
Actual character CRT lemma source-read in HyperKloostermanRootNumber.lean83:
GaloisForLFunctions.RHTower.HyperKloosterman.stdAddChar_crt (h:m.Coprime n) (x:ZMod(m*n)), [NeZero m,n]:
stdChar_(mn)x = stdChar_m((CRT h x).1*(n:ZModm)^-1) * stdChar_n((CRT h x).2*(m:ZModn)^-1).
Namespace VERIFIED! Also RHTower.stdAddChar_mul_complement_chineseRemainder in ReducedFrequencyMobiusAliasCollapse147 handles frequencya*d and projects toq.
Mathlib Analysis/Fourier/ZMod: ZMod.dft is LINEAR EQUIVALENCE (line88), dft_def111, dft_dft177. Scratch-probe these APIs beforeusing.

Predicted node classification AFTER rawGproof:
- zero when reduceddenominator has squares at two distinct primes;
- if reduceddenominator d squarefree dividingR, groupedweight A_P*m_P(d)*(L_P-logd), A=prod(1-1/p), m=prod_(p|d)(-1/(p-1)), L=sum_p logp/p;
- unique squaredprime forces only that distinguished term.
Normalizedtagged local coefficient should be z*c_z(i+1), but full node match remains unproved. Keep zero node, all residues, all lifts. Do not substitute predictedweights in physicalMellin action withoutproof.

Lean corrections this turn (not mathfailures): zpow_ofNat normalization needed before ring for finite diagonal square terms; function-levelsimp doesn't unfold partial function underHasSum, use explicitfunext identity foroffset0 and change foroffset1. In entry_at_prime rewrite whole product hprod BEFORE unfolding torsion indicators. Annotate nonnegative sum binder ∀q∈Q explicitly. Final physical projector residual if-function application needs split_ifs after simp_all. No resource-limit changes.

Prior memory mem:rh/bag-critical-source-shifted-trace-2026-10-05-01ac retains full physical transverse action and source arithmetic context.