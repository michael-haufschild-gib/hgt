# WD actual parabolic source landing (2026-10-15)

Formalized a formation-order advance, not a global source-sign theorem.

New modules:
- formal/GaloisForLFunctions/HTGeometry/ParabolicCauchyAveraging.lean
- formal/GaloisForLFunctions/RHTower/XiWardCubicParabolicSourceLanding.lean
- formal/GaloisForLFunctions/RHTower/XiWardCubicParabolicDirectionalMultiplicity.lean

Existing XiWardCubicPositiveShiftAveragedMultiplicity integrates already-extracted residue germs. New xiWardParabolicSourceAverage uses the literal continued covariance average at z+i h^2 with horizontal shifts 0..h, then multiplies by i h^2. After rescaling, the moving pole factors through i h/(-u+i h); domination and atomless averaging remove it. The endpoint retains full analytic multiplicity. The concrete cubic tensor theorem has no hypotheses, valid at every complex point.

Homogenized existing damped cubic radial mask C(a,e)=1-(108/115)e^3[2/(2a+2e)^3-4/(3a+3e/2)^3+2/(4a+e)^3], with a=max(0,Re z-1/2), is inserted before taking any residue limit. C(0,e)=0 for e>0; at fixed a>0 it extends continuously to e=0 with value one. Capstone tendsto_xiWardCubicParabolicDirectionalSource (z : C) states actual source tends to analytic multiplicity for Re z>1/2 and zero otherwise. Finite packets share one regulator. Arithmetic identity retains the literal pole–Gamma–von-Mangoldt source in its absolute-Euler chamber.

This implements averaging as the real-source survivor of the entire-scalar cubic landing no-go. Do not claim RH, an infinite-packet interchange, or global Stokes/signed source contraction: those remain open.

All three leaf modules passed lake --old env lean. All five audited capstones depend only on propext, Classical.choice, Quot.sound. Wired both umbrellas; no full build, heartbeat raises, numerical experiments, web search, external novelty audit, or commits. Final global lint found only five unrelated concurrent unwired CHMD/Deninger modules, no findings in these new files.

Research proof/failed conjecture ledger: docs/drafts/pipeline/3-formalized/wd-parabolic-cubic-directional-multiplicity-2026-10-15.md.

Serena find_symbol did not locate known Lean symbols (project language Python); used rg and apply_patch fallback. Correct old flag syntax is lake --old env lean, not lean --old.
