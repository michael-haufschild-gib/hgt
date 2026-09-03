# Convolution-inverse analytic twins are zero-free (2026-09-03)

Report mechanism `a*d=1` cannot carry a right-half divisor when both coefficient L-series admit holomorphic continuations on `rightHalf`. On `Re(s)>1`, absolute convergence gives `L(a,s)L(d,s)=L(a*d,s)=1`; analytic uniqueness propagates `A(s)D(s)=1` through connected `rightHalf`, so neither factor can vanish.

Formalized in `formal/GaloisForLFunctions/RHTower/ConvolutionInverseAnalyticZeroNoGo.lean` as closed proposition `AnalyticConvolutionInverseZeroPair` and theorem `not_analyticConvolutionInverseZeroPair`. Direct Lean and targeted build pass. Axioms only `propext`, `Classical.choice`, `Quot.sound`. Wired into `RHTower.lean`.

Positive survivor: analytic twins must multiply to Xi itself, not convolution unit; `TwinRigidity` then reduces them to actual right-half square root times analytic unit, exactly `RHLadder 1`.