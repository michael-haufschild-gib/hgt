# Theta-source exterior pseudospectral separation

- **Stage:** 3-formalized; 2026-09-05. **Verdict: BRIDGE.** The significant-novel-knowledge gate is not met merely by this formalization.
- **Question:** Does the literal compact theta inverse have spectrally tame exterior resolvents? This is a stability question, not a proposed RH equivalence.
- **Primary claim:** For every `1/2 < |h| < 1` and `0 < δ < π/4`, source-selected unit Esscher vectors have adjoint residual at `λ = -1/(-τ-hi)` bounded by `C exp(-δ|τ|)/|-τ-hi|`, whereas every true spectral point is separated from `λ` by at least `d/(|λ⁻¹|(|λ⁻¹|+d))`, `d=|h|-1/2`. No RH assumption.
- **Mechanism:** Exact Esscher source row → one-dimensional residual; completed-source horizontal decay → exponential accuracy; reciprocal Xi divisor and unconditional open-half-strip → polynomial spectral separation. No zero enumeration enters the vectors.
- **Checked corpus:** `HedenmalmThetaEsscherResolventFrame`, `HedenmalmThetaEsscherCyclicity`, `XiHorizontalStripDecay`, `HedenmalmThetaSourceCompressedInverseDeterminant`; `research` searches for theta/resolvent/exponential/pseudospectral/Cayley growth found no such bound. Existing ordinary skew-adjoint defect is weaker and is not rediscovered here.
- **RH-chain edge:** Quantifies stability cost of retaining the literal source Hilbert norm in the Hedenmalm spectral-realization architecture. Does not discharge spectral reality, boundary admissibility, or prime-faithful positivity.

## Literature / hostile audit

- [Hedenmalm, *Spectral interpretation of Riemann zeta zeros*](https://arxiv.org/abs/2606.17494), June 2026: source differential-operator pair and open metric/domain problem; not this compact quantile operator's pseudospectral estimate.
- [Krejčiřík–Siegl–Tater–Viola, *Pseudospectra in non-Hermitian quantum mechanics*](https://arxiv.org/abs/1402.1082), J. Math. Phys. 56 (2015), 103513: generic pseudomode/similarity obstruction is established, not claimed new.
- Searches of arXiv and journal-indexed results through **2026-09-05** found no exact-source estimate above. This is a provisional novelty audit, not proof of exhaustive absence through future September dates.
- **Rejected headline:** Mere non-self-adjointness or failure of a bounded normalizing metric: ordinary defect is already in corpus, and a zero-eigenvalue Jordan obstruction may make the latter elementary. Quantitative separation, not that headline, is the target.
- **Circularity check:** Uses only known zero-free exterior strip, not RH. Perturbations inferred from pseudomodes need not preserve Euler coefficients; no arithmetic perturbation claim.

## Paper proof

Write `B=thetaKernelOperator`, `P(z)=I+zB`, `A(z)=XiC(z)/M`, `e=pinnedOne`, and `Eτ=thetaEsscherFourierFamily h τ`. Exterior zero-freeness makes `P(z)` invertible. The exact row gives `P(z)* Eτ = conj(A(z)) e`. The Gram law gives `||Eτ||=||E0||>0`. Consequently the unit vector `vτ=Eτ/||E0||` has

`||(B* - conj(λ))vτ|| = |XiC(z)| ||e|| / (M |z| ||E0||)`.

Horizontal completed-source decay supplies the advertised upper bound. For a nonzero spectral point `μ=-1/α`, the divisor law gives `|Im α|<1/2`, hence `|α-z|≥d`. Triangle inequality gives `|α|≤|α-z|+|z|≤|α-z|(1+|z|/d)`. Thus `|μ-λ|≥d/(|z|(|z|+d))`. For `μ=0`, the same bound follows from `|λ|=1/|z|`.

The exact row also yields `||P(z)⁻¹||≥c exp(δ|τ|)`. This quantifies an unavoidable source instability even when every possible Xi divisor lies on the real axis.

## Formal status

Module `RHTower/HedenmalmThetaExteriorPseudospectralSeparation.lean`:

- `adjoint_thetaSourcePencil_esscher`: exact one-direction source defect.
- `norm_adjoint_thetaSourcePencil_pseudomode` and `norm_thetaExteriorPseudomode_residual`: exact completed-Xi residual coefficient.
- `thetaExterior_pseudospectral_separation`: primary theorem, including unit normalization, exponential residual and separation from **every** spectral point, including zero.
- `exists_exponential_thetaComplexResolvent_lower`: exponential exterior inverse-pencil growth.

`lake env lean /tmp/ThetaExteriorProof.lean` passed; both capstone axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Exact checked source copied into module, wired into `RHTower.lean`; no umbrella build. Global lint found unrelated active-agent modules not yet wired (`Rydberg*`, `SpinTorsion*`), no error in this module.

## Next-cycle audit

Checked `HedenmalmThetaBoundaryDirectCayleyFlow`: RH is already equivalent to subexponential growth of its rank-two observation. This result does not supply that growth bound. [Wakaiki, J. Evolution Equations 24 (2024), 48](https://link.springer.com/article/10.1007/s00028-024-00979-2) studies Cayley estimates under bounded-semigroup hypotheses; those cannot be silently supplied here. Sharp source-dynamics growth remains unproved; neither a square-root growth law nor a bounded normalizing metric is claimed by this card.
