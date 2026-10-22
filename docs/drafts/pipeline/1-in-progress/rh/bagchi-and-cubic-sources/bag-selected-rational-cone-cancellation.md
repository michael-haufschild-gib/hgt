# BAG literal selected rational cone cancellation

2026-10-06,01ay. Hard frontier subtarget. No Lean closure yet.
Depends on moving-test cancellation currently in scratch audit7627.

Corpus search /tmp/bag-moving-sharp-action-search-01ay.json: partial deadline,
reranking deadline; generation1257935,coveragepending,refreshincomplete.
All20candidate and20source-argument statements inspected. Actual
criticalRationalCone_physical_line_hasSum in ChiPrimeGaussianCubicMovingMellin
read in full; selected normalized cone and complete log profile inspected.
Source-only index metadata is not a compiler audit.

Conjecture: for A_N the literal controlled original physical Schwartz
amplitude at edge widthN^(1/4), the ENTIRE positive rational cone action
sum_w criticalRationalMass(P_N,w)*Fourier(A_N)(coneNode(point(w))) is
admitted and has complex norm o(N/log²N). Both growing numerator cofactors,
both exclusions, every rational point and collision sector remain.

Paper route: exact corpus HasSum equals the source/Mellin integral at
sigma_i=1+1/logN. The actual normalized physical cone f_N is exactly
(logN)^3/N times coneSchwartz(A_N), eventually. The moving selected Mellin
profile is exactly its logarithmic pullback at those same parameters.
Log pullback and Fourier transform preserve scalar multiplication.
The normalized source divides bylogN, so their full integral is exactly
(logN)^2/N times the original rational cone action. Carry the proved
moving-test cancellation through that identity, then take complex norm.
Prove admission before any use of tsum; no totalized-sum shortcut.

A_N uses the already constructed controlled cutoff on its admissible
range, with zero only outside that range. Prove eventual literal physical
amplitude identity. No existential replacement cutoff is selected.

Scope: this positive rational cone is not yet identified with the whole
sharp cubic action. Nonzero transverse defect/off-cone terms remain, as
do growing mixed moments and deterministic common-height return. Current
corpus also has an independent local prime-height axes reduction; its
axes operator must not be conflated with this rational cone without proof.
No RH claim.

Next full-action search /tmp/bag-full-defect-cancellation-search-01ay.json:
partialrerankingdeadline,generation1258049,coveragepending,refreshincomplete.
All20candidate and20source statements inspected; no proof ideas/ingredients.
It supplies exact completeintegerdefect andlocalprimeheight actions,
existing signed-variation obstructions and fixed rational-row approximation.
These do not identify the whole source with its exact-cone restriction.
Actual localaxes source inspected: pinned/mixed operators agree on the
physical band and axes retain(1-r^-2) of the full row. Its complementary
localnonzero channel is uniformly bounded96, but that local algebraic
channel is distinct from all global nonzero transverse lattice defects.
Cannot substitute one for the other. Next research must preserve every
congruence-admitted global defect and the complete complementary source.

Firstaudit39766/log01 terminal1: all exact profile/source/HasSum/admission
and normalization identities elaborated. Only final norm rewrite failed:
Complex.norm_real leaves the realnorm, so use verifiedReal.norm_of_nonneg.
Removed one redundant ring afterfield_simp. Productionleaf
ChiCubicSelectedRationalConeCancellation created with these two fixes;
productionauditnext. No theoremclosureclaimedbeforeaudit.

Cutoffobligationexplicit: this nativecone source is P_N. The exact fullsharp
physicalband[N,2N] uses the covered source throughfloor2N. A cofinal
source/physicalscale coupling mustbeproved beforeclaiming that attachment.
Uniformactual Cauchy already permits comparing f_N withf_(2N), but source-
weighted exterior transfer at the split scales mustalso bepaid. This is
source matching, not a numerical-bound refinement. All global nonzero
transverse defects remain after that matching.

SELECTED POSITIVE RATIONAL CONE CANCELLATION CLOSED. Production12330emptyPASS,
all5importedaxioms8568standard3,index21706PASS/API5,importonce23616,
scopedcode/generateddiffPASS. LeafChiCubicSelectedRationalConeCancellation
173lines. Lint70244:367warnings25unrelatedunreachable,noownedfinding;
exactP2/P3 bag-selected-rational-cone-cancellation. Actualadmission+exact
Mellin/scalar identity givesnormaction*log²N/N->0 forsourceP_N/physicalN.
Covered-band source2N/physicalN remainsP1bag-covered-source-mellin-transfer;
itscandidate/tmp/bag-covered-mellin-01ay.lean firstaudit50387running.
Wholeoriginalsharpaction/globaldefects and RHremainopen.
