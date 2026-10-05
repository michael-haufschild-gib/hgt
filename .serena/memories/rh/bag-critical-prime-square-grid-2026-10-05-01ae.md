BAG continuation01ae COMPLETE audited checkpoint; RH goal ACTIVE. No signed growing cubic saving, growing moments, moving cofactor law, common-height self-return or RH proof. No owned live process. No subagents/computations/axioms/heartbeat hacks/full builds/commits. Final leaf audit uses lake --old env lean leaf -o. All owned completed scratch .lean/.inc files removed; logs/search JSON retained.

NEW production leaf formal/GaloisForLFunctions/RHTower/ChiRamanujanCriticalGridSource.lean,489lines,25 public declarations, namespace RHTower.BAGTrace. Imports CriticalDistinguishedPrime, CompleteCubicTrace and Mathlib.Logic.Equiv.Fin.Basic. Wired once after CriticalDistinguishedPrime in RHTower.lean.

Definitions/local results:
- ramanujanGridBase p k (k:Fin(p²)): delta_(k.val=0) -p^-1 I_(p|k.val).
- ramanujanGridTag p k: p^-1 I_(p|k.val)-p^-2.
- Base_fourier and Tag_fourier evaluate the COMPLETE p² local Fourier sums to 1-I_p(n) and I_p(n)-I_p²(n), for p!=0, all integern. Subtorsion proof uses finProdFinEquiv coordinates b+p*a; no experiments.
- RamanujanGridPrime P = subtype p in P.filterPrime. RamanujanLocalGrid P = Pi_p Fin(p.val²).
- ramanujanLocalGridNode x = sum_p x_p/p².
- ramanujanLocalGridWeight P x = sum_p logp * product_q(if q=p then tagq elsebaseq).
- ramanujanLocalGridWeight_fourier: full all-integer multiplier equals the ACTUAL previously audited distinguished source, NO hypotheses.
- ramanujanGridModulus P = rad(P)² (always nonzero, private localinstance).
- ramanujanCriticalGridIndex a = a.1.2.val*(Q/a.1.1.val)+a.2.2.val*(Q/a.2.1.val²) in ZModQ.
- ramanujanLocalGridIndex x = sum_p x_p*(Q/p²) in ZModQ.
- both *_phase theorems prove exact standard-character equality with real rational nodes for allintegern.
- ramanujanCriticalPrimeAtomWeight_grouped: exact equality of grouped actual mass and grouped product-local mass at EVERY k:ZModQ. FiniteDFT injectivity uses allfreqidentity; no limits.
- ramanujanLocalGridIndex_injective/bijective: cofactor Q/p²=product_(q!=p)q² is unit modp², projection kills other coordinates; equal finite cardinalQ gives bijective. No CRT library character reconstruction needed.
- ramanujanCriticalPrimeAtomWeight_localProduct: actual mass at localindexx equals W(x), no hypotheses.
- ramanujanGridValuation p k: 0 ifk0, -1 ifk!=0 andp|k, -2 otherwise.
- ramanujanGridBase_normalized p:Nat.Primes,k: base=(1-z)c_z(i), z=1/p.
- ramanujanGridTag_normalized: tag=(1-z)z*c_z(i+1), NO analyticpremise. The normalized distinguished shift is NOW ACTUAL SOURCE, not conjecture.
- ramanujanCriticalGridWeight P k = sum_p logp*(I_(p|k.val)/p-1/p²)*prod_(q!=p)(I_(q²|k.val)-I_(q|k.val)/q).
- ramanujanLocalGridWeight_eq_direct: W(x) equals directweight atlocalindexx; unit preservation of every d|p² proves divisibility matching.
- ramanujanCriticalPrimeAtomWeight_grid: actual grouped mass equals explicit directweight for ALL P,k, NO premises. Main source closure, source line460.
- ramanujanCriticalGridWeight_two_primitive: if two distinct retainedprime coordinates p,q both do not divide k.val, weight0. Equivalently two squared reduced-denominator prime factors annihilate source; each term has only one tag.

AUDITS: production97363 exit0 EMPTY /tmp/bag-critical-grid-production-01ae.log; axiom73382 exit0 all25 onlypropext/Classical.choice/Quot.sound (valuationdef justpropext), /tmp/bag-critical-grid-axioms-01ae.log. Index61870 exit0 /tmp/bag-critical-grid-index-01ae.log, all25 exact module/name API rows and1import verified. Lint37187 exit1 /tmp/bag-critical-grid-lint-01ae.log,36 UNRELATED unreachablemodules, all errors inspected and no newleaf/proofdebt. Global lint NOT clean. No full/umbrella build. P2/P3 bag-critical-prime-square-grid same content; frontier C28.56ag.10; P1 bag-critical-distinguished-prime-source and workinglog updated.

SEARCHES:20154 /tmp/bag-critical-grid-search-01ae.json nonpartial65744/65744 inventory;91212 /tmp/bag-grid-growing-transfer-search-01ae.json nonpartial65751/65751. Both refresh incompletebackgroundindexer/compiler mostlypending/source-only. All20candidate+20sourceargs andproposedingredients read, emptyproofideas. First torsionphase/product identity useful; second confirms shiftedfiniteHasSum and oldrationaltraces, no automaticcriticaltransfer. Noabsenceinference. Read current WeightedRationalTrace lines1-195 and RationalCubicTrace1-175.

NEXT HARD CONJECTURE (paper derived, NOT Lean-audited): Let finiteprimeS, A=prod(1-1/p), L=sum logp/p. The ACTUAL NORMALIZED balanced finite-prime cone trace with bothlabel exclusions p!=r,q!=r, retainingp=q, should equal
 -A*sum_(r in S) log(r)/(r-1)*(L-log(r)/r)^2.
Derivation from audited primeShiftedLocalTriple_hasSum: localshift a=1_(ell=p),b=1_(ell=q),c=1_(ell=r); multiply tagged z^(a+b+c) and local z^-c*c_z(a+b-c)/(1-z)^2. Atell=r onlyc=1, gives c_z(-1)=-z/(1-z); atp,q gives z_p*z_q; globalA³ cancels product(1-z)^-2 toA. Sum p,q !=r gives square. Strictnegative when >=2primes. Prove exact signed identity; do not claim it is a physical estimate or labelprojector killsbalancedcone.

CRITICAL DOMAIN INSIGHT: old finite primeSupportCut/complexPrimeSupportCut restrict BOTH positive and negative prime valuations toP, i.e. numerators AND denominators. Actual finitegrid with allintegerlifts restricts denominators only, allows arbitrarynumerator primesoutsideP. Cannot substitute finiteprime HasSum and discard these cofactors. For the FULL denominator-restricted rational cone in Re(s),Re(t)>1, outsideP positivevaluations predict Eulerfactor zeta(s)zeta(t)*prod_P(1-p^-s)(1-p^-t). Thus predictedbalanced double-pole coefficient is A² times the finitecone value above, notzero. No criticalfullunorderedHasSum: integerpair absolute subseries already harmonic fornonemptyP (actualmass atintegers=A*L>0). These are paperobservations to formalize, NOT a no-go of BAG. Next attack exacttagged/cofactorMellin source and ACTUAL physical pole/near-cone pairing. Full physicalwindow/Mellinline/lifts/projectors remain essential. Earlier physicalsources and gaps in mem:rh/bag-critical-source-shifted-trace-2026-10-05-01ac and mem:rh/bag-weighted-placements-labels-2026-10-05-01ad.

LEAN lessons: Finset.prod_coe_sort/sum_coe_sort take Finset FIRST thenfunction; explicit args needed for higher-order matching under subtype.val. Finset.prod_attach/sum_attach alsoexplicit functions fixed rw failures. Fintype.prod_sum under dependentPi needed explicit function+convert, notsimp_rw. ZMod.castHom and cast_natCast require explicit (m:=p²)(n:=Q)(R:=ZModp²) to avoid underconstrained inference; projection proof change toZMod.cast then explicitcast_natCast works. ZMod.natCast_eq_zero_iff a b is theorem FUNCTION so use (ZMod.natCast_eq_zero_iff _ _).mpr, not .mpr directidentifier. Complex.ofReal_ite nonexistent: private grid_cast_ite avoids broad apply_ite distributing expressions incorrectly. Fin.ext_iff zero needs explicit @... then simp Fin.val_zero. field_simp ONLY syntax unsupported; supply p-1!=0 and -1+p!=0 fromprimeone_lt. No mathematicalfailure or newpremise in development. Scratch API probes had explicit universe levels. Production import narrowed fromWeightedCubicLocal toCompleteCubicTrace, audit passed.