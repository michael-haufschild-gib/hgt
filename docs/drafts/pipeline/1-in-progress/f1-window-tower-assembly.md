# F1: positivity through the window tower

- **ID:** F1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0211/obstacles-summary.md`, §2.3 F1
- **Statement:** Prove unconditional Weil positivity on every window by a compatible stage-local payment of the frozen arithmetic form.

## Mathematical core

At level `N+1`, write `ℓ=log(N+1)`, `ε=A−ℓ`, `w=Λ(N+1)/√(N+1)`,
`C=∫collarWeight(A,ε)H²`, and `F=foldEnergy(A,ℓ,H)`. The exact identity is
`Q(H)=Q_N(H)+w(F−C)`. The proved exit bound is `Ω(ε)C≤J∞(H)` and `w≤Ω(ε)`.
Neither proves `Q_N≥Ω(ε)C`; that stronger estimate is proposed in F1, not established by the
transfer theorem. Its claimed equivalence to RH needs an independent converse audit.

## Gates

- [x] Source statements: `TheTransferAcrossAStage`, `TheExitChargePaysEveryNewFold` inspected.
- [ ] Audit the base range and the exact remaining stage payment.
- [ ] Construct a lossless bridge from the nonlocal payment tools to that payment.
- [ ] Prove the remaining arithmetic inequality without an assumed positivity input.
- [ ] Formalize proved advances, integrate imports, and audit transitive axioms.

## Open conjecture

The exact signed fold cost `w(C−F)` can be paid uniformly along the tower. The sufficient costs
`wC` and `Ω(ε)C` discard the positive fold contribution; their validity is a separate conjecture.

## Audit findings

- The base is already proved through length `181/250`, all real C² tests, by
  `fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths` (SP). F1's `3/5` base is stale.
- ACCE `ThresholdVanishingAndCollarDominanceOfThePrimeShell` already proves the exact threshold
  ladder: every spectral drop between consecutive entrances is frozen-operator domain relaxation.
  Its ground-state collar sandwich also exists. Repackaging these is not a new bridge.
- WTZ README §7 reports numerical odd negativity of the prime-free form after length about
  `0.76`. This would refute F1's stronger loan on the first-prime stage. This is a lead, not proof.

## Current analytic test of the stronger loan

Try the odd C² polynomial window `f(x)=x(1−x²)^3` on `[-1,1]`, zero outside, dilated to length
`109/100 < log 3`. Its pole contribution is nonpositive. A rigorous upper bound for the prime-free
archimedean form would suffice to refute the nonnegative-loan target.

Useful exact kernel identity, for `t>0`:
`ω(t)=1/(4 sinh(t/2))+1/(4 cosh(t/2)) ≤ 1/(2t)+1/4`.
Compare the interior jumps with this logarithmic kernel and retain the exact tail `Ω(A)`.
For an odd unit-mass profile at length `A`, the constant-kernel contribution cancels its
autocorrelation integral, giving the candidate upper quotient
`L(f)+A/2+2Ω(A)`, where `L` is the scale-invariant logarithmic lag quotient.
Target exact bounds: `L(f)≤29/12`, `Ω(109/100)≤119/100`, and `−Ω_Γ>107/20`.
These imply a strictly negative prime-free archimedean Rayleigh quotient. All three remain to audit.

The polynomial identity
`f=16(P₁/105−P₃/55+P₅/91−P₇/429)` exposes a finite exact rational expression for `L(f)`.
The logarithmic exit average is `H₁₃−H₆+1/15`. Prove the comparison and rational evaluation;
no numerical result is accepted. If the stronger loan fails, preserve the signed fold and
seek joint Schur payment of the frozen negative direction and the new fold.
