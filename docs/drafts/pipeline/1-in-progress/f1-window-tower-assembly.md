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

Use the continuous odd cubic `f(x)=x max(1−4x²,0)`, supported in `[-1/2,1/2]`.
For `0≤t≤1`, its proposed exact autocorrelation is
`C(t)=2/105−2t²/5+2t³/3−2t⁵/5+4t⁷/35`; it vanishes for `t≥1`.
Thus `E=C(0)=2/105`, `∫₀¹ C=0`, and `∫₀¹(E−C(t))/t=(457/210)E`.

The existing AIP theorem `archLevyDensity_le_inv` gives `ω(t)≤1/(2t)+1/4`.
It yields `J∞≤(457/210+1/2+2Ω(1))E`. The existing antiderivative expansion gives
`Ω(1)≤251/200`; standard logarithm and Euler-constant bounds give `−Γ>26/5`.
Consequently the proposed prime-free bound is `Q₁(f)<−(29/2100)E`.
These identities and inequalities await Lean verification. Existing continuous-source
mollification preserves the energy limit and produces C² tests inside a slightly enlarged
window still shorter than `log 3`.

If this refutes the stronger loan, preserve the signed fold. The positive survivor must
jointly pay the frozen negative direction and the new fold; a negative statement alone
does not retire F1.

For the same cubic, the proposed positive survivor is `Q(f)≥E/100` after inserting prime `2`.
Exact moments are `∫₀¹t(E−C)=7E/12` and `∫₀¹t²(E−C)=47E/120`.
The sharp lower Gamma kernel, `Ω(1)≥log 2+π/4−1/4+1/96`, `−Γ≤269/50`,
`C(log 2)≤−33E/100`, `log 2/√2≥49/100`, and polar cost `≤7E/225` give this margin.
This would exhibit strict negative frozen energy and strict positive complete energy on the
same smooth first-stage test. The bounds and smoothing transfer remain to formalize.
