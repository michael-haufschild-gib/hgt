# K–P source audit corrections (2026-08-15)

Primary source: Kaczorowski–Perelli, arXiv:2603.13885v1 (HTML lines 313–318, 359–364, 385–393, 484–493, etc.).

## New audited Lean modules
- `RHTower/SelbergClass/FunctionalEquationLocal.lean`: codiscrete FE → exact equality on pair-analytic locus.
- `RHTower/SelbergClass/GammaCriticalLine.lean`: completed value analytic and FE exact at `1/2+tI`.
- `RHTower/SelbergClass/InvariantRootNumber.lean`: raw `ω` vs invariant `ω_F=ω ∏ λ_j^(-2 i Im μ_j)`.
- `SelbergClass/MultipleStandardTwistAnalytic.lean`: damped twist is globally analytic in C^N.
- `MultipleStandardTwistContinuationUniqueness.lean`: global analytic candidates agreeing on exact initial open domain coincide.
- `MultivariableVitaliAccumulationCounterexample.lean`: entire zero/first-coordinate functions agree on an accumulating complex hyperplane in C² yet differ globally.
- `MultipleStandardTwistSpectrum.lean`: source spectrum, finite fibre, source-corrected Xi (conjugated coefficients and `n^(s-1)`), finite-Xi entireness, source hyperplanes. `totalRootNumber` was corrected to invariant phase.

All listed modules were source-checked/exact target-built/axiom-audited where noted in task logs; no custom axioms.

## Literal source defects / repairs
1. Lemma 7 states SCV Vitali from convergence on any accumulating set. False for N>=2. Narasimhan’s cited proposition requires a uniqueness set. Application uses D∩C_1^N, nonempty open, so a repaired theorem needs convergence on an open uniqueness subset plus normal-family bounds.
2. L3 starts at height K, but following estimates use V although only V>=K. Use K (source K bound suffices) or split [K,V].
3. Damping estimate after (3.2) writes `exp(-α z_X...)` although z_X already contains α; RHS confirms only `exp(-z_X...)` is intended.
4. Remainder (3.24) product has `s^*_{0,ν}` in a factor indexed μ!=ν; intended `s^*_{0,μ}`.
5. D restricted coordinatewise Re s<=3/2 cannot itself cover mixed points such as (3,0,...). Plausible variable-starting-line repair is unproved.
6. Current `Re w=2` Fubini does NOT supply K–P (3.4), which needs arbitrary c>max(0,(1-Re s_i)/κ_i).

## Current direct tasks
- `general_line_mellin`: general c Gamma inverse Mellin identity; scratch real-positive route compiles.
- `spectral_sublevel_finiteness`: hidden finite strict-sublevel/right-gap source bound.
- `asymmetric_fe`: derive source (2.2) on a pole-free locus from raw completed FE, avoiding totalized Gamma poles.

Do not call the published continuation fully formalized or C1/C2 solved. Source corrections are literature-audit findings, not novelty claims by themselves.