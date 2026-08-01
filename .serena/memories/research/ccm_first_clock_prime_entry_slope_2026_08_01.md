# CCM first-clock prime-entry slope tomography (2026-08-01)

Status: paper-proved, Lean-proved, corpus-new bridge, not RH.

Whole-HT audit verdict: generic Herglotz/KMS/Pick positivity, finite jets/unpointed HT, divisor-only data, and positivity-preserving regularization do not yield literal first-clock sign. Positive survivor is source crease tomography.

For active atom `A_k(L)=criticalMellinAtomWeight(k)*sin((2*pi/L)*log k)`, at `L=log k`, `A_k=0` and slope is `-2*pi*criticalMellinAtomWeight(k)/log k`. Hard-entered atom has left slope 0 and this right slope. Normalization `-log(k)/(2*pi)` recovers exact weight. For `k=p^e`, slope is `-2*pi*p^(-e/2)/e < 0`; for non-prime-powers, 0. Any finite packet decomposes at distinguished entry into differentiable background plus unique kink atom.

Lean: `formal/GaloisForLFunctions/RHTower/CCMFirstClockPrimeEntrySlopeTomography.lean`; umbrella wired. Main capstone `ccmFirstClockEnteredPrimePacket_entry_smoothDecomposition`. Direct check green; final build 9262/9262; capstone axioms exactly `[propext, Classical.choice, Quot.sound]`. Lint has no new forbidden declaration and only unrelated HTGeometry umbrella gaps.

Research card: `docs/drafts/pipeline/3-formalized/needs-audit/ccm-first-clock-prime-entry-slope-tomography.md`. Working log: `docs/drafts/pipeline/1-in-progress/rh-whole-formal-corpus-frontier-audit.md`.

Novelty collision: `SuzukiPrimeTangentTomography.lean` is analogous high-clock tangent tomography, not moving-first-clock entry law. Keep claim conservative.

Open core remains unconditional construction of first-clock lower floor / asymptotic Bohr model from prime-Gamma source. Full published-source kink theorem still needs exact Gamma-polar summand smoothness in same normalization. Goal RH remains active; do not mark complete.