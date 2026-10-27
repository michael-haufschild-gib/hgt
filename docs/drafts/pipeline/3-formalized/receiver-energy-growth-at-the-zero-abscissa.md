# Receiver energy growth at the zero abscissa

- **ID:** receiver-energy-growth-at-the-zero-abscissa
- **Stage:** 3-formalized
- **Type:** THEOREM — uncredited infrastructure
- **Source:** review-2610 W7(viii), B3.2; actual Abel-escape dominance premise
- **Statement:** For every positive damping ε and κ > max(0, 2Θ − 2ε − 1), the actual damped Möbius receiver satisfies Eε(T) ≤ Cε,κ (T+1)^κ, where Θ is the actual zeta zero abscissa.

## Goal

Discharge the energy-growth premise in the actual-source Abel atom and capacity
laws at every attained rightmost zero. No zero-free strip, simplicity,
residue-summability, or energy bound is assumed to obtain the upper bound.
Simplicity remains a restriction of the existing simple-pole atom formula.
This does not prove RH or resolve escape at infinite height.

## Gates

- [x] 0 → 1: precise actual-source statement; existing subpower reciprocal-zeta input located.
- [x] 1 → 2: dependency-closed paper proof.
- [x] 2 → 3: exact Lean theorem, individual `lake --old env lean` check, transitive axiom audit, umbrella import.

## Existing inputs and novelty audit

`InvZetaAbscissaSubpolynomial` proves subpower bounds for the actual reciprocal
zeta right of Θ. `TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa`
and `AdmissionBelowHalfDampingAboveTheZeroWidth` use these to prove admission
when ε > Θ − 1/2. The exponent upper bound below that admission threshold was
not found in the corpus search. `TheAbelEscapeAtomsOfZetaAreItsDominantZeros`
still takes polynomial energy bounds as explicit hypotheses.

## Approach

For σ > max(1/2, Θ − ε), prove square integrability of
u ↦ exp(−σu) Aε(floor(exp u)). Its Laplace transform is the pole-cleared
function ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s. Convexity for ζ and the subpower bound
for its reciprocal give a square-integrable majorant on vertical lines.
Paley–Wiener and Laplace uniqueness identify the Hardy datum with the actual
receiver. Positive log-cell weights then give Eε(T) = O((T+1)^(2σ−1)).

The value at s=1 must be regularized explicitly; Lean's value of ζ at its pole
cannot be used as an analytic continuation. The discrete receiver is centered
at integers, so the existing Mellin-cell formula includes the centering term
−mε ζ(s), not −mε/(s−1).

## Status

Verified Lean modules:

- `ArithmeticCorrespondencePositivity/TheCenteredReceiverSymbolIsHardy.lean`
- `ArithmeticCorrespondencePositivity/TheReceiverEnergyGrowthAtTheZeroAbscissa.lean`

Both modules passed individual `lake --old env lean` checks and are imported
by the ACP umbrella. The main theorem is
`exists_receiver_energy_le_of_zeroAbscissa`; its actual-source corollaries are
`receiver_dominance_at_zeroAbscissa`,
`tendsto_receiver_window_atom_at_zeroAbscissa`, and
`tendsto_receiver_abelGram_atTop_at_zeroAbscissa`.
The Hardy input and main conclusions have transitive axiom lists exactly
`[propext, Classical.choice, Quot.sound]`.

No contribution credit: the frontier labels W7(viii) corollary assembly.
The estimate removes an energy premise at attained rightmost zeros but leaves
residue summability and infinite-height completeness unresolved.

## Formalized paper derivation

Write `mε = 1/ζ(1+ε)` and `Θ = zetaZeroAbscissa`. The regular reciprocal
`invZeta` is holomorphic on `Re s > Θ`, including its removable zero at `1`.
For ε > 0 define

`Qε(s) = ((s−1)ζ(s))/s · dslope(z ↦ invZeta(z+ε), 1, s)`.

The first factor uses the entire residue unit. The divided difference is
holomorphic wherever `Re s+ε > Θ`, since that half-plane contains `1`.
Consequently `Qε` is holomorphic on `Re s > max(0, Θ−ε)` and agrees, off `1`,
with `ζ(s)(invZeta(s+ε)−mε)/s`.

Fix σ ≥ 1/2 with σ+ε > Θ. The proved convexity bound, conjugation, and the
absolutely convergent series on `Re s ≥ 9/8` give
`|ζ(s)| ≤ A(1+|Im s|)^(5/16)` outside a compact neighborhood of the pole.
The proved reciprocal bound gives
`|invZeta(s+ε)−mε| ≤ B(1+|Im s|)^(1/8)` on `Re s ≥ σ`.
Also `(1+|Im s|)/4 ≤ |s|`. Therefore
`|Qε(s)| ≤ K(1+|Im s|)^(−9/16)` there; continuity fills the omitted compact
region. The square of this majorant is integrable. Thus `w ↦ Qε(w+σ)` is
half-plane Hardy.

For `0 < ε < 1/2` and σ < 1 choose
`b = (max(σ,1−ε)+1)/2`. The elementary bound
`Eε(T) ≤ C(T+1)^(1−2ε)` supplies absolute Laplace convergence on `Re s=b`.
The existing Mellin-cell identity gives the Laplace transform of
`φε,σ(u)=exp(−σu)Aε(floor(exp u))` on `u>0` as `Qε(w+σ)` on
`Re w=b−σ`. The existing Hardy uniqueness theorem identifies this actual
profile with the Paley–Wiener datum. Hence `φε,σ` has finite square mass.

The exact log-cell identity is
`Eε(T)=∫_0^log(T+1) exp(−u)Aε(floor(exp u))² du`.
On this interval the integrand equals
`exp((2σ−1)u)|φε,σ(u)|²`, so
`Eε(T) ≤ (T+1)^(2σ−1) ∫_0^∞ |φε,σ(u)|² du`.

Given κ > max(0,2Θ−2ε−1), use σ=(1+κ)/2 when
`κ < 1−2ε`; the displayed inequalities ensure σ is in `(1/2,1)` and
σ+ε>Θ. Larger κ follow from the elementary bound. For ε≥1/2 the existing
admission theorem suffices. This proves the proposed upper bound without a
zero-free-strip or energy-growth assumption.

If a zero ρ attains Θ and `ε < Re ρ−1/2`, the bound supplies exactly the
dominance premise of `tendsto_receiver_window_atom` and
`tendsto_receiver_abelGram_atTop`. Simplicity and noncancellation are conditions
on the selected zero in those corollaries; neither is used in the upper bound.
