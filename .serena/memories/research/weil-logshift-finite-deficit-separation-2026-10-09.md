# Exact finite deficits separate countable log-shift positivity from full Weil positivity

User restriction: Lean corpus ONLY; no web or external papers. Active open-ended research goal remains active. This increment is verified progress, not goal completion.

New verified source: formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteDeficitSeparation.lean. Imports WeilTailPanelSharpPrefix and WeilFullConeSummableDeficitRigidity. Namespace RHTower. Two public theorems:

1. exists_weilLogShift_exact_deficit_prefix (base : Nat) (lam height : Nat -> Real). Let N=weilLogShiftSharpLiftIndex base=ceil(2exp(2(base+1)))-1. Constructs mu >= lam everywhere, mu=lam for n<N, mu>=vonMangoldt for n>=N, exact normalized deficit D(mu,n)=if n<N then D(lam,n) else 0, Summable D(mu), and every panel k>=base+1 strictly above height k. D(lam,n)=max(vonMangoldt n-lam n,0)/sqrt n is the RAW deficit from existing full-cone theorem (do not replace silently by guarded WeilExcess.deviationDeficit).

Proof prepares v=lam below N and max(lam,Lambda) elsewhere, then applies sharp prefix completion at B=N-1. Pointwise identity gives finite support and summability. Exact positive survivor, arbitrary input prefix and height function.

2. exists_weilLogShift_single_deficit_separation(t : Real). Constructs lam with WeilLogShiftTestsPositive lam (the entire original predicate), lam n>=Lambda n for n != 2, lam 2=Lambda 2-exp(t)*sqrt 2, D(lam,n)=if n=2 then exp(t) else0, Summable D(lam), and NOT WeilPositiveFull lam. Seed a single negative spike at2; apply general theorem atbase0, target0; prove2<N0. Window0 has no valid probe. Full positivity contradicts existing eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit at2.

This REFUTES replacing full Weil positivity by countable log-shift positivity in summable-DEFICIT or eventual-majorant rigidity. It does NOT refute the separate summable-EXCESS replacement: excess summability of this family is unproved. Existing deficit proof uses combRiemannKernel and full summable-deviation rigidity; excess proof uses modulated Fejer tests plus general Fourier deviation-pairing vanishing. Next possible investigation: summable-excess reduction, or arithmetic/coherent completion constraints, after Lean-corpus audit.

Card: docs/drafts/pipeline/5-failed/weil-logshift-summable-deficit-receiver-no-go.md. Failed premise reduction; strongest selected positive survivor paper PROVED, Lean VERIFIED. Search34summable/excess declarations acrossbothpages and exhaustivepredicate references completed before writing. No external novelty claim.

Verification2026-10-09: final leaf session27184 exit0,no diagnostics, default heartbeat; emittedolean. Scratch import/signature/axioms session95716 exit0, both public theorems depend exactly[propext,Classical.choice,Quot.sound]. Umbrella import exactlyonce observedline6921. Index88467exit0,2publicAPIrows. Scoped whitespace checks no diagnostics. Authoritative lint12344exit1 only13unrelated unreachablemodules: RHTower.{CCMEvenFullGroundSecondMomentRH,CanonicalProductE1SecondDerivative,PaperCircleEnergyLocalization,StretchedBoseDefect}; HTGeometry.{ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra,PaperFourierLLogL.Compress.Params,PaperFourierLLogL.Compress.Theorem,PaperFourierLLogL.Thermal.Piece,PaperFourierLawMeasure}. No own leaferror. No full/umbrella build, numericalexperiment, heartbeatincrease, commit orpush.

All own jobs terminal. Owned scratch prefix /tmp/hgt-weil-summable* inventoried10files and cleanup performed at closure. Predecessor memory: `mem:research/weil-tail-panel-sharp-prefix-2026-10-09`.
