# Fixed-height mass gap for positive annihilators

- **Stage:** 1-in-progress
- **Type:** CANDIDATE — paper proof complete; Lean verification pending.
- **Obstacles:** B13, B112.
- **Statement:** For a normalized positive two-prime Dirichlet polynomial vanishing at `σ+δ+iγ`, `δ>0`,
  `H(σ) ≥ 1/M`, where `M=max(-cos(γ log 2) exp(-δ log 2), exp(-δ log 3))`.
  Reflected-pair annihilators at fixed `γ` approach `exp(δ log 2)` iff `cos(γ log 2)=-1`.

## Proof

Write `v_d=c_d exp(-σ L_d)≥0`, so `H=Σv_d`. The first nonconstant frequency is `a=log 2`, uniquely at `(1,0)`; every other frequency is at least `b=log 3`: either the second exponent is positive, or the first is at least two and `log 4>log 3`.

Real cancellation at the right-hand zero gives
`1=Σv_d[-cos(γ L_d) exp(-δ L_d)]`.
The bracket is at most `M`: use its exact value at the first frequency and the bound `exp(-δ b)` elsewhere. Hence `1≤MH`; `M>0` gives the stated bound.

If `cos(γa)≠-1`, both entries of the maximum are strictly below `exp(-δa)`, so `1/M>exp(δa)`. This uniform excess prevents approach to the unrestricted floor, even without requiring a reflected zero.

If `cos(γa)=-1`, then `sin(γa)=0`. The scaled prime-two monomial has value `-1` at `σ+iγ`, exactly as at the reference height `π/a`. Therefore the explicit positive trinomials from `TheHyperbolicCostOfReflectedZeroPairs` vanish at both `σ±δ+iγ`. Their masses are
`sinh(δ(B_m+a)/2)/sinh(δ(B_m-a)/2)`, `B_m=(2m+2)a→∞`, and converge to `exp(δa)`. This proves sufficiency at the prescribed height.

## Novelty and limits

Corpus baseline: unit-mass phase equality, harmonic-packet equality and unrestricted reflected-pair infimum. The isolated first-frequency estimate adds a positive fixed-height gap and classifies every height where that gap disappears. No assertion about actual zeta ordinates; B13 and B112 remain open. All claims count as one contribution after Lean audit.
