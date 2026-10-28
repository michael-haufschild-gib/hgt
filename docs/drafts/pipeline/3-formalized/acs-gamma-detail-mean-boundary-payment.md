# Gamma pays local variance, mean differences, and exterior displacement together

- **ID:** acs-gamma-detail-mean-boundary-payment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [complete-cell mixed payment](../1-in-progress/acs-complete-cell-mixed-payment.md)
- **Statement:** The original Gamma energy pays the coherent logarithmic local-variance charge, a positive graph on actual interval means, and their displacement from the exterior source simultaneously.

## Exact result

Let `I_i=(a_i,b_i)` be any finite disjoint family of nonempty intervals, with widths `w_i≤1`. Write `m_i=(∫_I_i f)/w_i`, `V_i=∫_I_i(f-m_i)²`, `F=(⋃I_i)ᶜ`, and let `k=archLevyDensity` be the original Gamma density. Define

`E_ij = w_i*w_j*(m_i-m_j)²*k(max(b_j-a_i,b_i-a_j))`,

`R_i = ∫_F w_i*(m_i-f(y))²*gammaFarCharge(a_i,b_i,y)`.

For every compact BV source, Lean proves

`Σ_i log(1/w_i)*V_i + (1/2)Σ_ij E_ij + Σ_i R_i ≤ levyEnergy f`.

The exterior integrals are nonnegative extended integrals. Their sum is proved finite from the original energy bound before conversion to a real number. No exterior integrability premise, mean-zero restriction, sign restriction, or vanishing condition is assumed.

The stronger coherent theorem, valid for every measurable L² source and arbitrary positive interval widths, retains

`2Σ_i V_i*∫_ℝ gammaFarCharge_i + Σ_ij E_ij + 2Σ_i R_i ≤ ∫_ℝ∫_ℝ gammaDifference f`.

The mean graph uses explicit far-end weights. No claim equates it with the entire Gamma energy of the piecewise-constant average source.

## Exact complete-cell specialization

For independent coefficients `u_a,v_a` on cells `2a,2a+1`, set

`q_a = haarRightCoeff(a)*u_a + haarLeftCoeff(a)*v_a`, `d_a=u_a-v_a`.

`cellPairSum_levyEnergy_ge_detail_graph_exterior` proves

`Σ_(a=1..X) log(a)*haarMass(a)*d_a² + (1/2)*completePairMeanGraph(q,X) + completePairExteriorCharge(q,X).toReal ≤ levyEnergy(Σ_a u_a*rawCell(2a)+v_a*rawCell(2a+1))`.

Both extra charges depend only on the actual weighted averages `q`. The source is zero almost everywhere on the family complement, so the exterior charge is exactly the far-end Gamma integral of `logCellWidth(a)*q_a²`. This retains boundary payment even when all pair averages coincide and their difference graph vanishes. All original cell coefficients remain arbitrary.

## Matched proof


For product weights `w≥m≥0`, `v≥n≥0`, split each weight into its minimum plus its nonnegative remainder. The constant product pays both base variances and `m*n*|I|*|J|*(mean_I-mean_J)²`. The two mixed product pieces pay the remaining variance charges. The final product piece is nonnegative. This proves both variance charges and the mean square in one inequality.

Each exponential slice of the actual Gamma density is such a positive product. Nonnegative summation retains all three charges. Against an exterior point, the exact identity `∫_I(f-t)²=V_I+|I|*(mean_I-t)²` retains its full mean displacement.

Partition the source plane into interval pairs, the two interval–exterior orientations, and the exterior–exterior block. Pair symmetry accounts for both variance orientations and the full mean graph. The exterior term also appears twice. The omitted exterior–exterior block is nonnegative. The symmetric difference integral equals twice the original Lévy energy. Each full far-end charge pays the reciprocal-width logarithm. These facts give the displayed real inequality, including finiteness of its exterior term.

## Lean evidence

- [IntervalVarianceRemainder.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/IntervalVarianceRemainder.lean): `integral_sub_const_sq_eq_variance`, `productWeight_twoInterval_mean_variance_le`, `rankOne_twoInterval_mean_variance_le`.
- [GammaVarianceRemainder.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaVarianceRemainder.lean): `gamma_twoInterval_mean_variance_ge`, `gamma_free_mean_variance_ge`.
- [GammaMeanVarianceCapacity.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaMeanVarianceCapacity.lean): `gamma_coherent_mean_variance_farCharge`, `levyEnergy_ge_log_variance_add_mean_graph_add_exterior`, `levyEnergy_ge_log_variance_add_mean_graph`.

- [CompleteCellMeanGraph.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellMeanGraph.lean): `completePairProfile_levyEnergy_ge_detail_graph_exterior`, `cellPairSum_levyEnergy_ge_detail_graph_exterior`.

All four exact project files passed `lake --old env lean <module>.lean`, without warnings. Ten transitive axiom prints contain only `propext`, `Classical.choice`, `Quot.sound`. Logs: `/tmp/acs-variance-remainder-final.log`, `/tmp/acs-gamma-variance-remainder-final.log`, `/tmp/acs-gamma-mean-variance-capacity-final.log`, `/tmp/acs-complete-cell-mean-graph-final.log`. Imports are wired into the ACS umbrella; the umbrella was not compiled.

## Remaining parent obligation

The complete-cell specialization and [coarse Gamma recovery](acs-coarse-gamma-recovery.md) are formalized. Together they retain the entire original coarse Gamma energy and logarithmic detail payment, with one explicit universal error times the actual coarse square mass. Full signed Gamma–prime–pole payment remains open; no positive full Weil residual is asserted.

## Log

- 2026-10-28 — Exact project checks and transitive audits passed. Promoted directly to stage 3; no stage-2 parking.
