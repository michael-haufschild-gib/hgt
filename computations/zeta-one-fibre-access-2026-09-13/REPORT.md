# Finite and escaping approaches to the value 1

The experiment followed solutions of zeta(s)=w from 64 cached positive zeros while w approached 1. Three target paths differed in their final approach angle: 0 and ±π/3. Each ended a distance 2^−48 from 1. The frozen finite classifiers compared the trajectories near distances 2^−32 and 2^−48; they do not assert an infinite limit.

All 192 paths completed at 80 digits. Each direction produced 18 escape-like and 46 finite-like trajectories, with no unresolved classifications. Starting from the first zero along the real target approach reached approximately 48.000000004+13.597080429i. Starting from the sixth reached a finite solution of zeta(s)=1 near 1.367688181122+38.419105560643i. Selected examples passed separate 100/160-digit and independent-formula challenges; the complete classification remains exploratory.

The larger lesson is that a common target value can be approached through different inverse branches. The far-right approximation zeta(s)−1≈2^−s predicts behavior after an escaping branch enters that region. It does not tell us which zero enters it, and it does not describe the finite branches. An RH route based on inverse geometry must retain both kinds of access and ultimately prove a constraint on the special fibre zeta(s)=0.

The positive result is a concrete access map that can be compared with the independently measured critical-point graph. Stable counts across directions should not be confused with stable labels; the mixed experiment tests that distinction explicitly. Neither finite sampling nor numerical escape is a proof of global inverse-surface topology.

Reproduce with `python guard.py experiment.py`. The three literal paths, predetermined classifiers, full trajectories, source search, environment and original checksums are included. Figures show finite trajectories only. No Lean builds.
