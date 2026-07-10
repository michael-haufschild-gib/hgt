# Completed-flux germ rigidity and transverse finite witnesses

- **ID:** completed-flux-germ-rigidity
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (Lean) — formalized, not new scientific knowledge
- **Source:** `CompletedFluxCrossOrderReflection.lean`, `SeamFluxCompletion.lean`,
  `CompletedFluxLaguerreReader.lean`
- **Statement:** `[PROVED, BRIDGE]` The residue-filled completed-flux germ determines its base point.
  Consequently its functional-equation and Schwarz images have equal germs, equivalently equal
  Taylor coefficients at every order, exactly when the base point lies on the critical line.

## Goal

Give the Euler--Gamma constraint program an all-order transverse coordinate that is defined even at
zeros of `xi`.  The result introduces no carrier, cutoff, limit, flow, or operator.  It is an exact
analytic interface: every off-critical point creates a disagreement at some finite order between
the completed-flux jets based at `1 - ρ` and `conj ρ`.

This bridge is not an RH proof.  Feeding it an off-line zero merely restates that the zero is
off-line.  Progress requires a source-side theorem forcing the two full jets to agree at every
`xi` zero, or another source constraint incompatible with their finite mismatch.

## Theorems

For arbitrary `a,b : ℂ`, local equality at the origin of the analytic germs

\[
x\longmapsto \operatorname{completedFluxGermAt}(a,x),\qquad
x\longmapsto \operatorname{completedFluxGermAt}(b,x)
\]

implies `a=b`, including when either base is a zero of `xi`.  Away from zeros the proof converts
germ equality into global proportionality of two translates of `xi`; the functional equation turns
that proportionality into a genuine period, and the established aperiodicity of `xi` forces the
translation to vanish.  At zeros the residue-filled germ is peeled locally and compared at a nearby
nonzero point.

Hence, for every `ρ : ℂ`,

\[
\operatorname{completedFluxGermAt}(1-ρ)
=\operatorname{completedFluxGermAt}(\bar ρ)
\quad\Longleftrightarrow\quad
\operatorname{Re}ρ=\tfrac12.
\]

Analyticity converts germ equality into equality of the entire Taylor sequence:

\[
\left(\forall n,\ c_n(1-ρ)=c_n(\bar ρ)\right)
\quad\Longleftrightarrow\quad
\operatorname{Re}ρ=\tfrac12.
\]

In contrapositive form, every off-critical point has a finite transverse witness

\[
\exists n,\quad c_n(1-ρ)\ne c_n(\bar ρ).
\]

## Relation to the quadratic RH falsifier

The order-two line coefficient has a separate exact interpretation already formalized in
`CompletedFluxLaguerreReader.lean`:

\[
(\Xi'(t))^2-\Xi(t)\Xi''(t)=-\Xi(t)^2c_2(\tfrac12+it).
\]

Therefore

\[
\exists t,\quad \Xi'(t)^2<\Xi(t)\Xi''(t)
\]

is equivalent to a positive real quadratic completed-flux coefficient at a nonzero line value and
implies `¬RH`.  This is the program's terminal falsification port:

- one source-forced positive value of `Re c₂(1/2+it)` proves `¬RH`;
- `Re c₂(1/2+it) ≤ 0` for all `t` proves only the first necessary Laguerre inequality;
- an RH proof must constrain the all-order transverse sequence, not merely its quadratic member.

## Main declarations

- `xi_shift_eq_const_mul_of_seamFlux_germ_eq`
- `seamFlux_germ_injective`
- `completedFluxGermAt_germ_injective`
- `completedFluxTaylorCoeff_all_eq_iff_germ_eq`
- `completedFluxCriticalPhaseAt_iff`
- `completedFluxTaylorCoeff_line_pair_all_eq_iff`
- `exists_completedFluxTaylorCoeff_line_pair_ne_of_re_ne_half`

## Scientific status

`[BRIDGE]` The proof combines analytic identity, functional symmetry, and aperiodicity in a new
project interface, but this does not clear the novelty gate for new scientific knowledge.  The
scientific open core is source-side:

`[OPEN CORE]` Find an Euler--Gamma relation among the all-order coefficients that cannot be
satisfied by the finite transverse mismatch attached to an off-line zero.  The relation must be
derived without assuming the zero location and without replacing the fixed source by a cutoff,
carrier, limiting normalization, or propagated flow.

## Gates

- [x] 0 → 1: the all-point residue-filled germ and transverse comparison were well-posed
- [x] 1 → 2: germ injectivity, all-order coefficient equivalence, and finite witness were proved
- [x] 2 → 3: exact module build passed; all declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
- [ ] 3 → 4: requires a genuinely new source-side exclusion theorem, not this bridge alone
