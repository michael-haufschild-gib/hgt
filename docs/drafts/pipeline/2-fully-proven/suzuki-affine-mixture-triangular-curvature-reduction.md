# Suzuki affine mixture to discrete triangular curvature

Status: `[PAPER-PROVED] [NOVELTY UNVERIFIED]`

## Exact RH chain

Exact signed Suzuki curvature cells
→ discrete third-grade triangular transform
→ `CCMFUSuzukiCanonicalCheckpointAffineTailBound`
→ `riemannHypothesis_of_ccmFUSuzukiCanonicalCheckpointAffineTailBound`
→ RH.

## Internal frontier

- `[CORPUS]` `suzukiCheckpointAffineSlope_succ_sub_eq_signedCurvatureCell` identifies exact
  slope jumps.
- `[CORPUS]` `suzukiPsi_log_nat_eq_affine_add_signedCurvatureGreen_add_resets` gives endpoint
  Green reconstruction.
- `[CORPUS]` `summable_suzukiCheckpointEventCurvatureJump` proves finite reset variation.
- `[CORPUS]` `ccmGuinandWeilThirdGradeCesaroTriangularWeight_eq_rectangularMixture` identifies
  each positive hinge response with exact third-grade triangular weight.
- `[CORPUS]` no theorem combines these into full floor-selected CCM-FU affine mixture.

## External frontier

Suzuki's screw-function papers (arXiv:2206.03682, 2209.04658, 2209.12832) and 2026
Weil-quadratic-form synthesis (arXiv:2606.09096) treat continuous screw/Weil criteria. Audit found
no integer-event floor decomposition, signed-curvature Green transform, or exact triangular
checkpoint formula. Priority remains provisional pending expert review.

## Conjecture C-TRI1

For `H ≥ 2`, define

`T(H) = ∑ j ∈ Ico 2 (suzukiCheckpointEventIndex H),
  suzukiCheckpointSignedCurvatureCell j *
    ccmGuinandWeilThirdGradeCesaroTriangularWeight H (log (j+1))`.

Then the canonical affine mixture is exactly

`base affine mixture + T(H) + reset-prefix mixture`,

the base and reset mixtures are uniformly bounded in `H ≥ 2`, and therefore uniform boundedness
of `T(H)` is equivalent to `CCMFUSuzukiCanonicalCheckpointAffineTailBound`.

## Hostile audit

Verdict: `SURVIVES PRELIMINARY ATTACK`.

- Not a scalarized curvature limit: moving triangular weights retain every prefix and critical
  cancellation.
- Not an RH hypothesis: claimed identities and nuisance-channel bounds use only finite algebra,
  event reconstruction, positivity of marked density, and absolute reset summability.
- False-RH escape remains entirely in `T(H)`, so reduction preserves rather than assumes open core.
- Exact new burden is a discrete signed arithmetic transform; floor selection, continuous
  integration, base affine memory, and positive reset variation disappear.

## Paper-proof obligations

1. Extend endpoint Green reconstruction to every `t ≥ log 2`:
   affine current = base affine + signed hinge Green current + reset prefix.
2. On `[1,H]`, replace moving event prefix by fixed finite hinges indexed below
   `floor(exp H)`.
3. Exchange finite sum and integral and apply exact rectangular-mixture identity cellwise.
4. Prove uniform marked bounds for base affine and reset-prefix mixtures.
5. Deduce bounded-difference and uniform-bound equivalence.

## Dependency-closed paper proof

Write `N(t)=floor(exp t)`, `Δ_j` for the signed curvature cell, `r_j` for the positive
event reset, and

`B(t)=Psi(log 2)+s_2 (t-log 2)`,

`G(t)=sum_{2≤j<N(t)} Δ_j (t-log(j+1))`,

`R(t)=sum_{2≤j<N(t)} r_j`.

For `t≥log 2`, the selected event satisfies `N(t)≥2` and
`t∈[log N(t),log(N(t)+1)]`. The affine-current cell theorem gives

`A(t)=Psi(log N(t))+s_{N(t)}(t-log N(t))`.

Substitute the proved endpoint Green formula for `Psi(log N(t))` and the proved slope formula
`s_N=s_2+sum_{2≤j<N}Δ_j`. Collecting coefficients gives the exact pointwise law

`A(t)=B(t)+G(t)+R(t)`.

Fix `H≥2` and put `N=N(H)`. For `1≤t≤H`, monotonicity of `floor(exp t)` gives
`N(t)≤N`. For every `2≤j<N`,

`j<N(t) ↔ log(j+1)≤t`.

Indeed, the forward implication uses `j+1≤N(t)≤exp t`; the reverse implication uses
`j+1≤exp t` and the defining floor inequality. Hence on `[1,H]`

`G(t)=sum_{2≤j<N} Δ_j max(0,t-log(j+1))`.

The sum is finite, so it may be exchanged with the interval integral. Since `j≥2` gives
`1<log(j+1)≤H`, each hinge vanishes on `[1,log(j+1)]`. Therefore the bulk hinge integral plus
the forced endpoint atom is

`integral_[log(j+1),H] density(H,t)(t-log(j+1)) dt
 + 32/H^4 (H-log(j+1))`,

which is exactly `ccmGuinandWeilThirdGradeCesaroTriangularWeight H (log(j+1))` by the proved
rectangular-mixture identity. Linearity yields

`M_H(A)=M_H(B)+T(H)+M_H(R)`.

It remains to show the two discarded responses are uniformly bounded. The base is affine,
`B(t)=a+b t`. On `1≤t≤H`, positivity and the proved density estimate give

`density(H,t)|B(t)| ≤ 384(|a|+|b|)/t^4`.

The inverse-quartic tail is integrable uniformly in `H`; the endpoint atom is bounded by
`32|a|/H^4+32|b|/H^3`. Thus `M_H(B)` has one finite ceiling.

All `r_j` are nonnegative and `sum_j r_j<∞`. Consequently
`0≤R(t)≤C_R:=sum_j r_j`. Positivity of the marked density and its endpoint atom gives

`0≤M_H(R)≤C_R (integral_[1,H] density(H,t) dt+32/H^4)`.

The parenthesized mass is exactly the third-grade error kernel at `1`, uniformly at most `96`.
Thus `M_H(R)` has one finite ceiling.

Therefore `|M_H(A)-T(H)|` is uniformly bounded for every `H≥2`. Adding or subtracting that
fixed error proves equivalence between uniform boundedness of `T(H)` and
`CCMFUSuzukiCanonicalCheckpointAffineTailBound`.

Every step uses an existing exact source identity, finite sum/integral algebra, positivity, or
absolute reset summability. No zero-free statement, RH premise, limiting interchange, or
unproved estimate occurs. Hostile checks at integer walls pass because the new event includes the
preceding zero-length hinge and reset exactly; arbitrary noninteger `H` is covered by the fixed
event set below `floor(exp H)`.

`[PAPER-PROVED]` Obligations 1–5 are closed. Next gate: exact Lean formalization.
