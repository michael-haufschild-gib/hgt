# WP04 cycle 21 checkpoint — PROGRESS, goal active
2026-10-08. Assigned full target remains OPEN: arbitrary hW : WeilPositiveFull λ must give half-integer counting on one full-measure endpoint set. No phase representation producer has been assumed. Use hgtl7 every turn and corpus research commands before new topic/Lean.

## New verified result T21
Every active harmonic of every exponentially weighted periodic representation with real base r>1 of a nonrigid actual source has rational scale exp(k log r). Previous L3p forced only one arithmetic harmonic / some rational power of the base.

Broader countable result: if every scale exp(ω_j/2) is a positive radical and hp=Σ‖p_j‖exp(|ω_j|/2)<∞, the actual represented phase has zero aggregate frequency mass at every positive irrational scale. Duplicate frequencies may cancel; only injectivity permits individual coefficient elimination. Final version has NO separate target-radical premise: outside radical support, mass vanishes directly.

## Six new finished leaves (formal/GaloisForLFunctions/RHTower prefix WeilWorkQuantization)
DirichletInverse, DilationInverse, RadicalTranslation, RadicalResidues, FrequencyMass, RadicalMass.
All six final direct lake --old env lean -o .lake/build/lib/lean/<module>.olean <module>.lean exited 0 with no diagnostics. One foreground Lean at a time; no full/umbrella builds. All six wired exactly once; 56 quantization leaves total.
Final scratch audit checked all 29 declarations/types and #print axioms: only propext, Classical.choice, Quot.sound. Complete log docs/reports/weil-work/results/04-quantization/radical-mass-lean-audit.txt.
Default-heartbeat failure in FrequencyMass was fixed by explicit sum interchanges / scalar exponent equalities. No heartbeat/recursion increase.

## Mechanism and APIs (namespace RHTower.WeilSpectral)
- quantizationInverseCoeff λ = dirichletExp(fun n => -lamLog λ n).
- quantization_inverse_lseries hW hs: reciprocal series converges absolutely for Re s>1 and equals exp(-LSeries(lamLog λ)).
- quantization_inverse_convolution hW n: inverse ⋆ forward = if n=1 then1 else0.
- quantization_actual_dilation_inverse hW hbound x: the two actual coefficient sequences weighted at s=3/2 invert their dilation action on every bounded f. No extra coefficient/summability premise.
- quantization_radical_translate_rational hx hN hM hq hs: x>0, positive powers of x and x+1 rational imply x rational. Complex conjugate/two tangent circles/separability proof; classical bridge.
- quantization_phase_resonance_periodic (cycle20 T20) supplies B(x+1)=B(x).
- quantization_phase_radical_residue_zero hW hp hphase hrad hx hxr hxi: B(x)=0 at positive irrational radical x; infinite resonances retained.
- quantizationFrequencyMassTerm p ω x j = if exp(ωj/2)=x then pj*exp(-ωj/2) else0.
- quantizationFrequencyMass = tsum above, globally bounded by hp moment.
- quantization_frequencyMass_dilation hW hp hx:
  Σ_n term(a,3/2,n)*Mass(x/n) = exp(-3 log x/2)*B(x).
- quantization_frequencyMass_inverse hW hp hx:
  Mass(x) = Σ_n term(b,3/2,n)*exp(-3log(x/n)/2)*B(x/n).
- quantization_phase_radical_mass_zero hW hp hphase hrad hx hxi: Mass(x)=0. Final API omits hxr; nonradical case paid from support.
- quantization_periodic_frequencyMass hr p k isolates pk*exp(-klogr), since r>1 makes scales injective.
- quantization_periodic_irrational_harmonic_zero hW hr hp hphase hN hq hki: pk=0 if its scale irrational and r^N=q rational.
- FINAL quantization_rigidity_or_rational_harmonics hW: R OR every weighted periodic represented source has all active scales rational. R=(∀n≥2 λn=Λn)∧RH. Only hW is source input.
- source-only residue alternative also in RadicalResidues.

## L4 paper proof CLOSED; final Lean step OPEN
RADICAL-PERIODS.md has dependency-closed full proof of arbitrary-real-periodic rigidity, plus separately audited stronger T21. Inversion retains every infinite integer-power resonance chain.
Remaining formal work: rational-exponent subgroup generator, reindex, apply existing L1 integer / cycle20 L2 noninteger rational receivers. Do not call L4 fully formalized yet; do not mark goal complete.

Efficient next implementation:
S={k:ℤ | ∃q:ℚ,(q:ℝ)=exp(k log r)} is additive subgroup. L3p gives nonzero member, hence Nontrivial S. Subgroups of ℤ are cyclic. Mathlib/Algebra/Order/Group/Cyclic.lean:38 defines LinearOrderedCommGroup.Subgroup.exists_generator_lt_one with generated additive counterpart exists_neg_generator. Source read lines1–66; verify exact additive qualified name in /tmp before use. Negate negative generator to get a:ℤ>0 with S=aℤ; q=exp(a log r)>1 rational. All active k belong S by T21.
Reindex p'(j)=p(a*j) using Function.Injective.tsum_eq; source InfiniteSum/Basic.lean:608–641 inspected (multiplicative tprod_eq support-range condition). Transfer hp via Summable.comp_injective. log q=a log r makes frequency/weight identity algebraic. Reduce rational q to coprime positive numerator/denominator, use L2 if denom≥2 or L1 if denom1. These new generator/reindex APIs are source-inspected, NOT scratch-verified or used in Lean yet.
Do not redo proven inverse/radical work.

## Literature/novelty
Primary Perucca, Linear relations among radicals, arXiv:2511.02498, https://arxiv.org/pdf/2511.02498 read lines0–405. Real-field Kneser criterion confirms radical independence classical. Earlier inaccessible publisher link is no longer a blocker. Inversion also classical. New-to-inspected-corpus actual-source support collapse is T21; independent scientific novelty unestablished.
Five compact research records saved cycle21-search-evidence.json (4 deep, 1 lexical; includes coverage, source_arguments, ingredients). Some generated candidates irrelevant; no applicability inferred without Lean.

## Durable state, verification and cleanup
RESULT.md corrected stale signed L2-open intro from prior cycle; T20/L2 cycle20 closure reconciled in EVIDENCE.md. RESULT.md now describes T21, 56 leaves, and L4 reindexing gap. NEXT-CONJECTURE.md has exact handoff. Pipeline card updated, all nine hgtl7 self-audit answers posted in chat and saved in EVIDENCE.md.
Latest scripts/formal_tools.py lint exited1, ONLY seven unrelated unreachable modules:
RHTower.WeilWorkSettledPhaseLocalPolynomialModels; RHTower.WeilWorkSettledPhaseLocalPolynomialPeriods;
HTGeometry.ApertureConeCalculus; ApertureConeWinding; ApertureLogTranslation; ApertureOpenHistoryIdeal; BoundaryCoronaCStarAlgebra.
No quantization-module error. Do not modify unrelated files.
All owned build/search handles reached terminal exits. Ten named /tmp cycle21 scratch/search/lint files removed; durable audits/evidence and finished .oleans retained. No commits/push/devserver. Goal remains active.
