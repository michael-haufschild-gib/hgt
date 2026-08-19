# Big-Witt Arakelov source-endomorphism terminal

- **ID:** big-witt-arakelov-source-terminal
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Connes--Consani arithmetic Jacobian and zeta-cycle literature; internal `ArakelovPowerOrbitRH.lean`
- **Statement:** Big-Witt Frobenius realizes the Arakelov square on Teichmüller reporters, but no global entire completed-Xi source endomorphism or actual Scaling-Site cover can induce it; right-half divisor descent is exactly RH.

## Goal

Close the Big-Witt/centered-prime-mark to completed-Xi spectral-fibre route: either obtain unconditional RH or dependency-close every literature-compatible pivot and identify the exact surviving RH core.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `bigWittArakelovCompletedXi_source_endomorphism_terminal`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Paper proof

`[PROVED HERE]`

1. Define reporter `T(w(rho))` in the canonical big-Witt ring. Frobenius two sends it to `T(w(rho)^2) = T(w(P₂ rho))`.
2. Classify fixed points of `P₂`: injectivity of `w` reduces `P₂ rho = rho` to `w(rho)^2 = w(rho)`, hence `rho ∈ {0,1}`.
3. Scaling-Site covers fix every zeta-circle critical point, whose real part is `1/2`; therefore they cannot induce `P₂`.
4. Algebra gives `P₂(rho) = rho^2/(2 rho - 1)` with total inverse at the exceptional point. The inverse-linear denominator is not continuous at `1/2`: conjugating by `z ↦ (z+1)/2` would otherwise make inversion continuous at zero. Dividing `P₂` by the nonvanishing continuous numerator near `1/2` transfers this contradiction to `P₂`.
5. If an entire-algebra endomorphism acted by precomposition with `P₂`, its value on the coordinate function would be `P₂`; every element of the source algebra is differentiable, contradicting Step 4. Thus the requested global source endomorphism does not exist.
6. Restriction to the open right half-plane avoids the pole, but completed-Xi divisor descent is `XiRightArakelovPowerStable 2`, already equivalent to RH.
7. Compare remaining literature actions: arithmetic-Jacobian idele action is translation/character-preserving; local Euler Adams is coordinate dilation, not ramification; scaled-Xi pullback changes the receiver ideal.

Every implication uses already formalized source laws or elementary complex algebra. No Xi zero, RH premise, new axiom, or numerical computation enters.

## No-go closure

- **Exact killing theorem/mechanism:** actual covers preserve the Xi label, while `P₂` moves every critical-line point; globally `P₂` has a critical-line pole.
- **Strongest positive survivor:** exact Big-Witt reporter equivariance `F₂(T(w(rho))) = T(w(P₂ rho))`, plus terminal classification of all possible pivots.
- **New insight:** obstruction is not absence of a power law. Power law exists functorially on reporters, but cannot cross to the fixed completed-Xi global source. Only right-half quotient descent survives, and that condition is RH-equivalent.
- **Status:** dependency-closed paper proof and Lean theorem in `BigWittArakelovSourceEndomorphismTerminal.lean`; targeted build PASS; axiom set `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-18 — created in 1-in-progress after corpus and primary-literature audit.
- 2026-08-18 — paper proof closed; formalized and moved to 3-formalized.
