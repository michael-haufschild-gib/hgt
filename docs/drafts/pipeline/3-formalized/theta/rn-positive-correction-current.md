# RN: global positive-correction current

2026-10-04. Formalized in ThetaTailCorrectionCurrent.lean, nine public theorems.

For the literal theta logarithmic decay slope p and all t,y>0, put
Q=(p(t+y)-p(t))/y+(p(t+y)-p(t))/(2t)+1/(2t²).
The exact current Q_y-(p(t+y)-p(y))*Q is strictly negative. Consequently
k(t+y)/k(y)*Q is positive and strictly decreasing in y for each t>0.

The complete proof uses actual-source curvature growth and projective bounds,
quadratic chord remainders, and a finite curvature increment comparison.
It covers the entire positive quadrant. No truncation, numerical experiment,
RH premise, added axiom or heartbeat increase is used. Paper proof and hard
successors: ../../1-in-progress/rn-positive-correction-current.md.

Validation:
- Foreground `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaTailCorrectionCurrent.olean GaloisForLFunctions/RHTower/ThetaTailCorrectionCurrent.lean`: exit0.
- Required `lake env lean GaloisForLFunctions/RHTower/ThetaTailCorrectionCurrent.lean`: exit0, empty diagnostics.
- All nine public `#print axioms` checks in /tmp: exactly propext, Classical.choice, Quot.sound.
- Wired into GaloisForLFunctions/RHTower.lean; no umbrella build.
- `scripts/formal_tools.py lint`: exit1, twelve unrelated unreachable modules; no error in this leaf and no forbidden proof declaration reported.

Build routing: an earlier targeted Lake build was canceled after starting a
large import rebuild. Only its owned process group was stopped and its exit
verified. Two missing import objects (FiniteLogConvolution and BinaryGrowthFlow)
were restored with direct foreground Lean checks, both exit0. The successful
commands above checked the actual leaf; the canceled target is not a passing build.

Scope: this proves the correction kernel's sign. The full Schur current has
a retained positive cost. Its payment, general anchors, arbitrary-rank
positivity and arithmetic RH transfer remain open. RH is not proved.
