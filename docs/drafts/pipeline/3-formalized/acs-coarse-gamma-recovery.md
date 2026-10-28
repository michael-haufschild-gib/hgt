# Coarse Gamma recovery with simultaneous detail payment

- **ID:** acs-coarse-gamma-recovery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: actual complete-cell sources → effectivity → Riemann–Roch and ampleness → Hodge index → RH.
- **Parent:** [complete-cell mixed payment](../1-in-progress/acs-complete-cell-mixed-payment.md)
- **Statement:** One explicit universal square-mass error recovers the entire coarse Gamma energy while retaining logarithmic detail payment in the same complete source.

## Exact statements

Put `wₐ=logCellWidth a`, `Mₐ=haarMass a`, `E=exp(1/2)`, `δ=log(3/2)`, and `T=gammaTailMass δ`. The explicit nonnegative constant is

`C = 2*completePairGammaRowConstant = 26*E + 4*T`.

For every finite positive logarithmic-cell family and every common real translation, the sum of actual off-diagonal pair replacement errors in row `a` is at most

`ofReal((12*E+2*T)*wₐ)`.

For the actual complete pairs, the row including exterior averaging loss satisfies

`completePairGammaErrorRow X a ≤ ofReal((13*E+2*T)*wₐ)`.

Every `completePairExteriorCharge q X` is finite before conversion to real numbers. For all signed coefficient functions `q,d : ℕ → ℝ` and every horizon `X`, let

`g=averageSectionProfile q X`, `f=completePairProfile q d X`.

The recovery and simultaneous estimates are

`Γ(g) ≤ (1/2)*completePairMeanGraph q X + (completePairExteriorCharge q X).toReal + C*∫ g²`,

`Γ(g) + Σ_(a=1..X) log(a)*Mₐ*d(a)² ≤ Γ(f) + C*∫ g²`.

Here `Γ=levyEnergy`, and the actual coarse square mass is exactly

`∫ g² = Σ_(a=1..X) wₐ*q(a)²`.

Both original cell coefficients remain arbitrary: the same inequality is proved for `Σ_a u(a)*rawCell(2a)+v(a)*rawCell(2a+1)`, with `q(a)=haarRightCoeff(a)*u(a)+haarLeftCoeff(a)*v(a)` and `d(a)=u(a)-v(a)`. No sign, mean-zero, or analytic-payment premise is imposed on these coefficients.

## Matched proof

Partition every off-diagonal finite row into upper nearby, lower nearby, distant, and adjacent cells. The already formalized endpoint telescoping estimates pay the nearby rows by `6*E*wₐ` and `2*E*wₐ`. The distant cells form a disjoint union inside two separated half-lines; integrating that union costs `2*T*wₐ`, without a cardinality factor. Both touching cells together cost `4*E*wₐ`. Nonnegative finite-sum subadditivity therefore pays the entire pair-error row by `(12*E+2*T)*wₐ`.

The actual complete-pair endpoints are the common `log 2` translate of the logarithmic partition. Exact finite reindexing removes the zero diagonal. The exterior is contained in the complement of each source interval, so its integrated averaging loss costs another `E*wₐ`. Each weighted exterior far charge is bounded by a finite actual exterior-kernel integral; summing finitely many such bounds proves finiteness independently of real conversion.

Write `G=completePairMeanGraph q X` and `B=completePairExteriorCharge q X`. Actual coarse-source accounting and the symmetric finite error estimate give

`2*ofReal(Γ(g)) ≤ ofReal(G) + 2*B + 4*Σ_a ofReal(q(a)²)*row(a)`.

The uniform row estimate bounds the last sum by `ofReal(completePairGammaRowConstant*Σ_a wₐ*q(a)²)`. The mean graph is nonnegative and the exterior charge is finite, so conversion to real numbers yields the recovery inequality. Exact indicator values on each complete pair, with only null endpoints excluded, identify the coefficient mass with `∫ g²`.

Finally the existing simultaneous lower bound is

`detail payment + G/2 + B.toReal ≤ Γ(f)`.

Combining it with recovery retains full coarse Gamma and logarithmic detail payment in the same original source. It does not spend the detail reserve a second time.

## Lean evidence

All three exact project checks and thirteen transitive axiom audits passed without warnings. Every audit contains only `propext`, `Classical.choice`, and `Quot.sound`. No analytic premise, placeholder, kernel bypass, or raised proof limit is used.

- [LogCellGammaUniformRows.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/LogCellGammaUniformRows.lean): `gamma_logCell_pairRow_le`.
- [CompleteCellGammaUniformRows.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellGammaUniformRows.lean): `completePairGammaRowConstant_nonneg`, `completePairGammaErrorRow_le`, `completePairExteriorCharge_ne_top`.
- [CompleteCellGammaRecovery.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellGammaRecovery.lean): `integral_coarseProfile`, `integral_averageSectionProfile_sq`, `completePairMeanGraph_nonneg`, `averageSectionProfile_gamma_recovery`, its integral version, `completePairProfile_gamma_ge_coarse_add_detail`, its integral version, `exists_completePair_gamma_coarse_detail_bound`, and `cellPairSum_gamma_ge_coarse_add_detail`.

Final checks passed with `lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/<Module>.lean`, individually from `formal/`. Audit logs: `/tmp/acs-logcell-gamma-uniform-rows-final.log`, `/tmp/acs-complete-cell-gamma-uniform-rows-final.log`, `/tmp/acs-complete-cell-gamma-recovery-final.log`.

## Remaining ACS obligation

This card addresses only uniform Gamma recovery and simultaneous detail payment. Full signed prime–pole payment, growing prime sets, low-index directions, and mixed scales remain on the parent card. Full-source effectivity and RH are not claimed.

## Log

- 2026-10-28 — All three requested results passed exact Lean checks. Promoted directly from stage 1 to stage 3; no stage-2 parking. Umbrella imports wired; no umbrella build.
