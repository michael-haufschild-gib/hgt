# Finite critical projectors split positive Meyer energy

- **ID:** finite-critical-projectors-split-positive-meyer-energy
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Q-II; positive-meyer-degrees-and-the-infinite-source-tail.
- **Statement:** For every positive Hermitian degree and every finite critical packet, the actual causal projector splits the full sharp-square degree into its exact weighted critical-value contribution and a nonnegative residual.
- **Status:** [PROVED HERE, paper]; Lean draft unverified; external novelty unverified.

## Complete paper proof

The source quotient is separated by its full Xi jets. For any finite set S,
the existing causal projector P_S retains every lower jet at points in S
and kills every lower jet at every other point. Hasse coefficients of a
product are finite convolutions of the local coefficient lists. Consequently
P_S(u)v=P_S(uv): at points of S, every local product coefficient is unchanged;
elsewhere the P_S factor has every lower jet zero, so every product
coefficient is zero. Full jet separation gives equality in genuine
cohomology. The same coordinate argument gives P_S²=P_S (also already
proved in the corpus). If S consists of critical points, arithmetic sharp
fixes each selected point and only changes jet parity; hence it commutes
with P_S.

Put p=P_Su and r=u-p. Then P_Sr=0. The preceding product identity gives
p sharp(r)=P_S(u sharp(r))=u P_S(sharp(r))=u sharp(P_Sr)=0.
Its sharp conjugate is also zero. Expanding the actual sharp square gives

    u sharp(u) = p sharp(p) + r sharp(r).

Apply the complex-linear degree d and take real parts. Positivity gives
E_d(r)>=0. The first product belongs to the finite selected packet; the
proved finite degree formula kills all its positive-order jets and gives

    E_d(P_Su) = sum_(rho in S) w_rho |value_rho(u)|²,
    w_rho = Re d(e_(rho,0)) >= 0.

Here the zeroth sharp-product value is the ordinary norm square because
rho is critical. This establishes the exact energy decomposition, not just
an inequality. In particular the finite weighted sum is bounded by E_d(u),
and the residual vanishes exactly when the bound is saturated.

All objects are actual quotient classes and existing finite causal
projectors. No prescribed infinite jet family, positive norm, spectral
location hypothesis on unselected points, or continuity of d is added.

## Scope

This proves a finite-to-global square-energy bound for every actual class.
It does not identify the infinite residual with zero. That is the open
question on `../1-in-progress/positive-meyer-degrees-and-the-infinite-source-tail.md`.

## Source audit and formalization

`DeningerMeyerFiniteXiCausalSplitting` supplies the actual projector,
idempotence, exact selected jets, and off-packet vanishing. The new finite
Hasse algebra and positive-degree classification have complete paper proofs
and unverified Lean drafts. Their actual leaf checks must precede promotion
of this theorem. The complete unrun draft `/tmp/QIIFiniteCriticalProjectorEnergyDraft.lean`
contains exact block selection, central multiplication, sharp compatibility,
zero mixed product, degree decomposition, residual saturation, and the
weighted finite energy formula/bound. Its finite sum is indexed by the
existing full-jet slot type with only order zero retained, equivalently one
term for each selected Xi point.

The generic block-selection and central-multiplier proof has been isolated in
`/tmp/QIIMeyerFiniteProjectorAlgebraDraft.lean` for reuse by the algebraic
character classification. The energy draft imports its planned module; both
are still unverified.

## Stronger survivor: arbitrary finite packets [PROVED HERE, paper]

Criticality of the whole selected packet is unnecessary for a positive
Hermitian degree. Let S be any finite set of Xi points and P_S its full causal
projector. For every genuine class u,

    d((P_S u) sharp(u-P_S u)) = 0,
    E_d(u) = E_d(P_S u) + E_d(u-P_S u).

The selected energy is exactly

    E_d(P_S u) = sum_(rho in S, Re rho=1/2) w_rho |M_u(rho)|²,

with the same nonnegative zeroth-class weights. It is at most E_d(u), and
saturation is equivalent to zero complementary square energy.

Here the first identity is degree annihilation, not necessarily a zero
cohomology product. Its proof closes the extra obligation explicitly. The
mixed product lies in the finite range of P_S by the central multiplier law.
Apply the finite positive-degree classifier: higher coefficients and off-line
blocks contribute zero. At a surviving critical point rho in S, sharp reads
conjugate value at the same point, while the complementary source has value
zero there. Thus every surviving summand is zero. Hermitian symmetry kills
the reverse mixed degree, proving the decomposition.

For the exact selected energy, its sharp square again lies in the finite
range of P_S. The same finite classifier leaves only critical values, and
P_S preserves each selected value. Those square values are exactly the stated
absolute squares. Positivity of the remaining square proves the bound, with
no continuity or infinite summation step.

Internal novelty search found only unrelated finite Hilbert matrix projection
bounds. This stronger theorem is not yet Lean-certified. All six general-packet
endpoints are now in the existing energy draft, including exact finite weights
and saturation; their actual-file verification remains pending. The critical-packet algebraic
zero-product statement remains stronger at the class level and is retained.
