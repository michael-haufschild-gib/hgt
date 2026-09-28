# Signed moment charge, local capacity, reflection energy (2026-09-28)

## Status
Goal ACTIVE: formal RH proof. RH and uniform square-root remainder bound NOT proved. Continue conjecture/prove/fail/learn; do not stop because hard. Repo /Users/michael/Documents/code/hgt/formal. No subagents, commits, pushes, computations/#eval/native_decide, sorry/custom axioms, heartbeat increases. One own foreground Lean process, no full/umbrella builds. Final leaf audit lake --old env lean FILE -o .lake/build/lib/lean/...olean. Corpus search formal_tools.py research, direct Lean, no cards. Preserve concurrent work.

## Verified work
Six new leaves, all passed final individual Lean audits, imported exactly once into RHTower.lean after CCMCoherentExteriorMomentBoundaryLayer. 56 public theorems plus 3 public wrappers in existing modules = 59. Dedicated #print axioms audit PASSED all59: only propext, Classical.choice, Quot.sound. Scratch CCMSignedMomentAxiomAudit-qabkf27z.lean removed. Final ChargeFlow proof cleanup re-audited without warnings. All own Lean processes finished, last session29012. Search indexes regenerated. Shared-repo lint reports unrelated concurrent unwired modules and generated-file staleness from concurrent edits; all six own imports confirmed. Do not wire others' unfinished modules. Serena project was inactive; activated /Users/michael/Documents/code/hgt/formal.

Notation g=ccmGammaHigherBinetModeDensity, k=ccmGammaHigherBinetDualDensity, g(r)k(r)=1 for r>0, both0 at0. M(T,N,r)=ccmActualHeadMidpointSignedMoment, actual prime-cell sum plus oriented terminal. E=integral M²k(|r|). Q=integral rM. A=integral r²g(|r|).

### CCMCoherentSignedMomentCharge.lean (7)
Arbitrary-test cell and oriented terminal transport identities:
integral_ccmOutgoingQuantileCellDensity_mul n F; integral_ccmActualHeadQuantileTerminalDensity_mul T N F. No continuity premise on F.
Integrable rM, individual cell/terminal charge formulas.
ccmActualHeadSignedMomentCharge_eq_completedMoment:
Q=-pi[sum_{n<N}w_n log²n +(2exp(T/2)-(2+P_N))T²-integral0T exp(h/2)h²].
Completed cosine symbol''(0)=-4pi Q (ccmActualHeadCompletedCosineCurvature_eq_signedMomentCharge).

### CCMCoherentSignedMomentGammaControl.lean (10)
Integrability of capacity density; 0<A<=8.
Public helpers ccmGammaHigherBinetModeDensity_abs_nonneg; ccmGammaSignedMomentCapacityDensity_le_abs (r²g|r|<=|r|); ccmGammaSignedMomentWeightedSquare.
Dual square 2tQ<=E+t²A. Q²<=AE<=8E. Completed curvature²<=128pi²E.
A<=8 via r²g(r)<=r exp(-r/2), positive-ray integral4, reflection. Exact symbolic proof.

### CCMCoherentSignedMomentArithmeticAction.lean (6)
Quadratic profile Q=pi[sum w_n(T²-log²n)-integral0T exp(h/2)(T²-h²)].
Physical head N=floor(exp H)+1, H:NNReal:
ccmActualTimeSignedMomentCharge_eq_completedErrorAction:
Q=-2pi integral0H h*(completedError(h)-2(1-exp(-h/2))).
criticalMellinThresholdCenteredError_eq_chebyshevVolterra:
completedError(h)-2(1-exp(-h/2))=-(1+R(h)+.5 integral0h R),
where R=criticalMellinNormalizedChebyshevError=(psi(exp h)-exp h)/sqrt(exp h).
ccmActualTimeSignedMomentCharge_eq_chebyshevVolterra:
Q=2pi integral0H h*(1+R(h)+.5 integral0h R).
Squared actual-action bounds by AE.
IMPORTANT: Q is a smoothed quadratic observable, not RH deficit D. Do not equate them or assume a uniform bound on Q is the correct scale; polynomial drift may remain.

### CCMCoherentSignedMomentLocalCapacity.lean (12)
Restricted A_s,Q_s,E_s for arbitrary s:Set Real. Nonnegative A_s,E_s, global domination, dual square, Q_s²<=A_s E_s including zero-capacity case handled internally, absolute sqrt bound.
For R:NNReal and s=[-R,R]: A_s<=R², |Q_s|<=R sqrt(E_s).
Exact charge and energy window/tail decompositions.
abs_ccmActualHeadSignedMomentCharge_le_local_energy_tail:
|Q|<=R sqrt(E_inside)+sqrt(A_outside)sqrt(E_outside).
This retains shrinking displacement scales but does not prove actual prime concentration.

### CCMCoherentSignedMomentChargeFlow.lean (8)
Q(T,N+1)-Q(T,N)=pi*w_N*(T²-log²N).
ccmActualHeadSignedMomentCharge_primeAdmission: Q(log N,N+1)=Q(log N,N).
Fixed-head derivative dQ/dT=-2pi T*(2exp(T/2)-(2+P_N)); HasDerivAt, deriv, Continuous proofs.
Derivative admission increment=2pi T w_N.
At physical head, frozen derivative equals -2pi H*centeredCompletedError(H), or +2pi H*(1+R(H)+.5 integral0H R).
Do not differentiate floor-valued moving head at entries: derivative jumps.

### CCMCoherentSignedMomentOddEnergy.lean (13)
O(r)=(M(r)-M(-r))/2; V(r)=(M(r)+M(-r))/2.
Reflection identities, weighted integrability and nonnegative energies.
ccmActualHeadSignedMomentGammaEnergy_eq_odd_add_even: E=Eodd+Eeven exactly.
Eodd<=E.
ccmActualHeadSignedMomentCharge_eq_odd_charge: Q=integral rO.
Odd dual bound; sq_ccmActualHeadSignedMomentCharge_le_odd_energy: Q²<=A Eodd.
sq_ccmActualTimeChebyshevVolterraAction_le_odd_energy: actual action pays only displacement asymmetry. This removes an entire even transport energy contribution exactly; no cancellation assumption. No uniform cutoff growth result.

## Existing modules extended, audited
CCMActualHeadOutgoingQuantileStieltjesCrossing: public criticalMellinStieltjesPairing_quadraticNonnegativeTimeCutoff (H:NNReal), intervalIntegrable_criticalMellinCompletedError_nonnegativeTime (H:NNReal), wrappers of existing private proofs.
CCMActualHeadOutgoingQuantileTransportProducer: sum_range_succ_criticalMellinAtomWeight_mul_eq_Icc N F, omits zero-weight atoms0,1 from arbitrary weighted tests.

## Lean lessons
Use H.coe_nonneg for H:NNReal in rewrites, not H.2. The latter inserts Subtype.val and mismatches toReal at instances transparency. Unfolding NNReal.toReal can make goals ill-typed at instances transparency; use NNReal.mk and simp NNReal.coe_mk.
Use convert! to avoid irrelevant Real-instance equality goals from convert. Simplify id_eq, Pi.pow_apply/sub_apply explicitly.
Integrable.neg may leave unapplied function negation that simp Pi.neg_apply does not eta-expand; use h.congr (Eventually.of_forall fun r => ...), change pointwise expression, ring.
integral_id is GLOBAL (Mathlib.Analysis.SpecialFunctions.Integrals.Basic).
integral_complex_ofReal is the Complex set-integral cast API.
integral_neg_eq_self f volume; Integrable.comp_neg; MemLp.comp_measurePreserving (Measure.measurePreserving_neg volume).
Avoid global expansion of mul_add across M; pointwise helpers preserve frequency factors.

## Next concrete candidate: direct RH exponential-ramp bridge (derived on paper, NOT formalized)
Actual criterion in CCMRestrictedWeilPoleCompressionRHCriterion:
D(T)=ccmLogChebyshevDeficitPrimitive T=integral0T(exp t-psi(exp t));
RH iff exists B>=0, all T>=0, |D(T)|<=B exp(T/2).
Choose F_T(h)=exp((h-T)/2)*(T-h), F_T(T)=0.
At physical N=floor(exp T)+1, continuous-minus-prime transport tested by F_T should equal exp(-T/2)*(D(T)-T).
Set a(r)=exp(r/2)-1, b(r)=-r exp(r/2).
A_TN(r)=sum_{n<N} c_n(r) exp((log n-T)/2)*(T-log n).
B_TN(r)=sum_{n<N} c_n(r) exp((log n-T)/2)+c_terminal(T,N,r).
Cellwise expansion gives transport density a*A_TN+b*B_TN. Candidate identity:
exp(-T/2)D(T)=T exp(-T/2)+integral_r(a*A_TN+b*B_TN).
Ingredients: new arbitrary-test transport formulas; telescope quantile intervals; criticalMellinAtomWeight_mul_exp_log_half in CCMCriticalMellinGrowingCumulative; ccmLogChebyshevDeficitPrimitive_eq_prime_log_tents in CCMPrimeDeficitPrimeWork:96; integral0T exp(h)(T-h)=exp T-T-1 via antiderivative exp(h)*(T-h+1).
Joint Gamma capacity integral g(|r|)*(a²+b²) is finite: near0 a,b=O(r); positive tail g~exp(-2.5r) and a²+b²=O(r² exp r). Existing coarse g<=exp(-r/2)/r does NOT suffice for this tail: build sharper r>=1 estimate using denominator1-exp(-2r)>=1-exp(-2), and handle near0 separately.
This would connect directly to the actual RH observable. It still requires arithmetic control, probably localized and signed; do not replace the completed field by absolute prime masses.
Search 'quantile exponential ramp' returned no matches; direct rg also none. Search by actual symbols again and inspect existing CCMRestrictedWeilPoleWallFieldWeld etc to avoid duplication.
