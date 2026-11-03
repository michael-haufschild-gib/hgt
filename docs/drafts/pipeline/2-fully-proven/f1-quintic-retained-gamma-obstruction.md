# The quintic defeats the retained Gamma lower form

- **ID:** F1-QG
- **Stage:** 2-fully-proven; Lean audit in progress
- **Type:** THEOREM (continuous test); C² transfer open
- **Source:** [Joint first-fold payment](../1-in-progress/f1-joint-cubic-prime-payment.md)
- **Statement:** The continuous odd unit-window source
  `F(x)=2x(1−4x²)(1−2x²)` inside `[-1/2,1/2]`, zero outside, has `P(F)<0`,
  where `P` is the retained Gamma/prime/pole lower form on the source card.

## Proof

The exact correlation is
`C(t)=62/1155−(334/315)t²+(2/3)t³+(88/21)t⁴−(86/15)t⁵
 +(268/105)t⁷−(16/21)t⁹+(64/693)t¹¹` for `0≤t≤1`.
Integrating its deficit gives

- `E=62/1155`, `∫xF=11/210`;
- `L=∫₀¹(E−C)/t=167/315−2/9−22/21+86/75−268/735+16/189−64/7623`;
- `M₁=∫₀¹t(E−C)=167/630−2/15−44/63+86/105−268/945+16/231−64/9009`.

Put `l=693147180/10⁹`, `h=693147181/10⁹`. In the displayed correlation polynomial,
replace positive powers by their values at `l`, negative powers by their values at `h`;
call the resulting rational number `c₋`. The bounds `l<log2<h` give `c₋≤C(log2)`.
Since `c₋<0` and `0≤log2/√2≤4902/10000`, the prime contribution is at most
`−2(4902/10000)c₋`.

The source is nonnegative on the positive half-window. Oddness and `sinh y≥y` for
`y≥0` give `sinhPairing F≥∫xF=11/210`; hence its half-square is at least `121/88200`.
Finally,
`γ+logπ+log2 ≥ 577215/10⁶+1098612/10⁶+1−3/(314159/10⁵)+l =: c₀`.
Here `logπ≥log3+1−3/π` follows from `log z≤z−1`, and the scalar bounds are proved
in the corpus and mathlib. Therefore

`P(F) ≤ L−c₀E−M₁/24−(11/210)²/16−121/88200−2(4902/10000)c₋ < 0`.

`WindowTowerOfSpecZ.TheQuinticWindowHasExactLagData` proves the exact lag and position
data. `WindowTowerOfSpecZ.TheRetainedGammaLowerFormHasANegativeDirection` proves
`retainedOddGammaLowerForm_quintic_neg`, including every integral identification,
constant bound and the signed prime/pole enclosure. Both individual `lake --old env lean`
source audits pass with `[propext, Classical.choice, Quot.sound]` only. Both modules are
wired into the umbrella. The remaining proof is the C² transfer below.

## Scope and survivor

The zero extension is not C². The support-preserving transfer uses
`rₙ=1/(4(n+1))`, `aₙ=1+2rₙ`, and `Fₙ(x)=(ηₙ*F)(aₙx)`, with the corpus's even
normalized mollifier of radius `rₙ`. Each `Fₙ` is smooth, odd and supported in the
same unit window. The quintic is globally Lipschitz with constant `16`; the smoothed,
rescaled sources have Lipschitz constant at most `24` and converge pointwise to `F`.
The increment identity gives `0≤(Eₙ−Cₙ(t))/t≤576t` for `0<t≤1`: the union of the two
translated supports has measure at most two. Dominated convergence proves convergence
of the logarithmic term and all remaining compact integrals, hence eventual negativity.
This C² transfer still needs its Lean proof. The complete Weil form's sign is not
decided by this obstruction, and the first-fold route remains active.

The positive survivors are the [exact retained Gamma identities](../3-formalized/f1-gamma-lag-moment-payment.md)
and [complete coercivity off two odd moments](../3-formalized/f1-complete-odd-two-moment-complement.md),
both individually Lean-audited with standard-only transitive axioms. The Gamma remainder
discarded in `P` remains available to pay the low moments jointly with the signed reflection.
