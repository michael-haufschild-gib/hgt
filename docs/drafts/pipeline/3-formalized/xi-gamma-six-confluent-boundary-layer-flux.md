# Xi Gamma-six confluent boundary-layer flux

- **Route:** HC
- **Stage:** 3 — formalized in Lean 4
- **Active claim:** one
- **Frontier map:** read-only; no edit planned

## Frontier

- `[CORPUS]` `XiGammaSixFilteredBoundaryControl.lean` factorizes the literal second boundary jet
  as `C_m L_m(p) G_m(p) F(p) H_t(p)` and proves its harmonic summability wall.
- `[CORPUS]` `XiGammaSixFilteredBoundaryHarmonicResidue.lean` proves
  `J_p(t) = R_m(t)/p - D_p(t)` with `D(t) ∈ ℓ¹`, and classifies the unique scalar harmonic
  coefficient `R_m(0)=0`, `R_m(t)=log 2/m²` off the wall.
- `[CORPUS]` `HedenmalmStokesOrientedFirstTraceQuantizedJump.lean` proves a distinct oriented
  prime-energy current has a quantized one-sided wall jump by the residue-one prime-logarithmic
  Dirichlet law.
- `[LITERATURE]` Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494,
  constructs the theta differential pair and its spectral boundary problem, but not the Gamma-six
  prime-harmonic boundary layer below.
- `[LITERATURE]` Kawalec, *On the series expansion of the prime zeta function about s=1 and its
  coefficients*, arXiv:2603.21535, records the prime-zeta singular expansion and logarithmic
  derivative series near one. It does not identify the HC source splice below.

## Conjecture

`[CONJECTURE]` For `m ≥ 1`, set

`K_{m,p}(t) = (log 2/m²) p⁻¹ (1-p⁻|t|)²`.

Then:

1. `K_{m,p}` is continuous at the neutral wall for every prime.
2. The literal Gamma-six jet has a source-confluent decomposition
   `J_{m,p}(t) = K_{m,p}(t) - E_{m,p}(t)`, where `E ≥ 0` and `E(t) ∈ ℓ¹` for every `t`.
3. For `t>0`, the derivative current `∑ₚ ∂ₜK_{m,p}(t)` converges absolutely and
   `t ∑ₚ ∂ₜK_{m,p}(t) → log 2/m²` as `t → 0+`.

The scalar wall jump is therefore the exact flux of a coefficientwise-confluent prime boundary
layer, not an arbitrary discontinuous choice.

## Hostile audit

- A prime-dependent counterterm evades the scalar no-go because its harmonic asymptotic is not
  uniform as `t→0`; no contradiction with `no_continuous_principalCoefficient_universalAdmission`.
- The jet/counterterm defect should be uniformly `O_m(p⁻²)`: the horizontal factor is retained,
  and only Gauss, depth-gap, and Fisher defects remain.
- The derivative identity should reduce exactly to
  `(log 2/(4m²)) [E_HG(t/2)-E_HG(t)]`, where `E_HG` is the existing physical prime Hardy--Green
  energy. Its residue-four scaling then gives flux `log 2/m²`.
- This does not prove RH: it localizes the obstruction. It changes the producer question from
  “choose a discontinuous residue” to “control or cancel a canonical continuous boundary-layer
  flux without erasing horizontal charge.”

## Paper proof

`[PAPER-PROVED]` Put `C=log 2/m²`, `z=p⁻¹`, `u=|t|`, and

`L=(1-z)^(2m)`, `G=(1-p⁻ᵐ)²`, `S=(1+z)⁻²`, `H=(1-p⁻ᵘ)²`.

The existing Gamma-six factorization and the exact Fisher identity give

`J=C z H L G S`, while `K=C z H`. Hence `E:=K-J=K(1-LGS)`.

For `p≥2` and `m≥1`, all four factors lie in `[0,1]`. Bernoulli gives
`1-L≤2mz`; direct squaring gives `1-G≤2p⁻ᵐ≤2z`; the existing Fisher harmonic-difference bound
gives `1-S≤3z`. The elementary product-defect inequality therefore gives

`0≤E≤C z ((2m+2+3)z)=C(2m+5)p⁻²`.

Thus `E(t)` is absolutely summable for every `t`, with a majorant independent of `t`. For fixed
`p`, `t↦p⁻|t|=exp(-|t|log p)` is continuous, so `K_{m,p}` is continuous and vanishes at zero.

For `t>0`, differentiation gives

`K'_{m,p}(t)=2C log(p)[p^(-1-t)-p^(-1-2t)]`.

With `W_d(p)=log(p)p^(-1-2d)` and the corpus energy
`E_HG(d)=8∑ₚW_d(p)`, this is `2C(W_{t/2}(p)-W_t(p))`. Both series converge absolutely, hence

`∑ₚK'_{m,p}(t)=(C/4)(E_HG(t/2)-E_HG(t))`.

The proved residue law `d E_HG(d)→4` gives
`tE_HG(t/2)→8` and `tE_HG(t)→4`. Therefore

`t∑ₚK'_{m,p}(t)→(C/4)(8-4)=C=log 2/m²`.

Every dependency is unconditional; no RH statement or divisor-location premise is used.

## Lean status

`[LEAN-PROVED]` `XiGammaSixFilteredBoundaryConfluentFlux.lean` formalizes coefficientwise
continuity and wall vanishing, exact jet/counterterm/defect decomposition, nonnegative `ℓ¹`
defect, pointwise derivative current, exact Hardy--Green difference, and scaled wall-flux limit.
Target-module source check and `lake build` pass. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Hostile verdict

`FORMALIZED; SURVIVES HOSTILE ATTACK`. Parent theory explains the prime-zeta residue and generic
boundary layers, but the coefficient-exact identification of HC's Gamma-six harmonic class with
this continuous source-layer flux is absent from the audited corpus and sources. Scientific
priority remains provisional pending independent expert review.
