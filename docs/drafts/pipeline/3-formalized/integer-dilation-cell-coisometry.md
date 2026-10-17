# Integer dilation, explicit block producers and infinite variance

- **ID:** integer-dilation-cell-coisometry
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Actual physical dilation intertwines with bounded integer block aggregation; explicit replication gives sharp coisometry, convergent variance and exact successor covariance.

## Certified result

For every real a, construct A_aq(t)=a q(at) on actual physical L², with
‖A_aq‖²=|a|‖q‖² and F_(A_aq)(t)=F_q(at). It is a bounded linear
multiplicative semigroup, including a=0. With S unit-cell synthesis and
B=S*, H_m=B A_m S has coordinates Σ_(r<m)w_(mj+r) and B A_m=H_m B.
For every natural m, H_mH_n=H_(mn), H_mR^m=R H_m and ‖H_m‖=√m.

The explicit adjoint T_m repeats z_j on its m-cell block; T_0=0.
H_mT_m=m id, ‖T_mz‖²=m‖z‖². For m>0, T_mz/m is a right inverse.
K_m=(1/m)T_mH_m is idempotent, and the actual nonnegative variance series
has sum m‖w−K_mw‖²=m‖w‖²−‖H_mw‖². Convergence is proved from ℓ².
For Q=SB, the full physical defect is

    m‖q‖²−‖B A_mq‖² = m‖q−Qq‖²+Σ_j V_j(m,Bq).

For m>0, equality holds exactly for cellular q with block-constant Bq.
Explicit packet q_m=S(T_mδ_0) has energy m and dilated analysis energy m².
All-scale statements include the constructed zero operators at m=0.

## Domain obstruction and positive survivor

unitCell1 belongs to every full-family completed divisor domain, but its
physical dilation by2 belongs to no completed divisor domain: its first
primitive trace is1, whereas every completed divisor state has trace0 there.
The positive survivor is the unrestricted physical operator, exact infinite
variance and sharp packet calculus above, proved on paper and in Lean.
No full affine-unitary, SourceGraph, unweighted logarithmic H1 or RH claim.
Classical change of variables, Hilbert adjoints and finite variance are
parent tools, not external novelty claims.

## Verification

Paper preceded Lean: docs/reports/BiScaleUncertainty/IntegerDilationCellCoisometry.md.
Five leaves: PhysicalDilation156/17, IntegerBlockAggregation101/14,
IntegerBlockCoisometry125/12, IntegerBlockVariance133/13,
IntegerDilationTraceDefect152/16 (lines/public). Total667lines and72public:
62theorems+10defs. Count once: certified17/100; overarching goal stays active.

All five serial direct leaf checks pass with empty logs/current outputs.
All72 public axiom audits pass with only propext,Classical.choice,Quot.sound;
23principal signatures and53mathlib API probes inspected. Five unique imports
and72 exact catalog source locations verified. No added axiom, admission
premise, numerical experiment, heartbeat increase or full/umbrella build.
README fully read260lines, read-only and hash unchanged. Trap10 applied via
explicit block producers and unconditional errors; no receiver-only bound
or pre-floor counterterm subtraction. Later arithmetic stencils must act on
unmodified factorial T(N), handling smooth counterterms after summation.

Global lint --check-generated exits1 for nine unrelated unreachable modules:
CenteredRamanujanVarianceAndAbelCofactorCancellation, CoherentKernelSplitting,
DivisorAverageChebyshevAndDyadicBlockVarianceProducer,
MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity,
NyquistWeightCellAsymptotic, NyquistWeightKernel, NyquistWideSourceEnergy,
RightNodeCollarPartition, RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge;
also concurrent LEAN_API/LEAN_OVERVIEW drift. No own/proof-debt error.
Indexes refreshed after lint; do not claim global lint passed.

Evidence: /tmp/integer-dilation-{axioms,lint-final,index-post-lint}.log,
/tmp/integer-dilation-{audit-names,leaf-checks,lint-errors}.json,
/tmp/integer-dilation-api-entries.txt, /tmp/integer_dilation_axioms.lean.
All five direct leaf logs retained. Audit/catalog scripts are in /tmp.

## Prior-research audit

Physical L² dilation/block aggregation query: all20 candidates and20 source
arguments inspected. partial=true, text/source interrupted; inventory73727
complete, snapshot1446744/current1446745; compiler mostly pending/source-only,
refresh incomplete/background_indexer_running. Focused lexical dilation
query returned9 declarations; no semantic/compiler coverage supplied.
Finite shear/trace and actual cell synthesis are parents. No matching
infinite operator package returned; not an absence or novelty proof.
Primary mathlib Haar and oriented-interval substitution sources linked in
paper. Initial query and new affine-producer candidate evidence retained.

## Next unproved candidate

../0-backlog/physical-affine-commutator-producers.md: actual physical
translation/anchored affine action and explicit alternating packets for
sharp commutator norm/nonattainment. Unproved, uncounted, no Lean assigned.
