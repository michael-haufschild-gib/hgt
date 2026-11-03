# The quadratic endpoint cutoff tests the reserved Gamma form

- **ID:** F1-QC
- **Stage:** 1-in-progress
- **Type:** THEOREM (negative direction); positive survivor under audit
- **Source:** [Two-moment payment](f1-primitive-variance-joint-payment.md)
- **Statement:** The odd unit-window profile `F(x)=2x(1−4x²)²` on `|x|≤1/2`, zero outside, has `P(F)+∫F²/64<0`; the inequality persists under support-preserving smoothing.

## Exact candidate data

`E=128/3465`, `m=∫xF=4/105`, and, for `0≤t≤1`,

`C(t)=128/3465−(256/315)t²+(128/21)t⁴−(128/15)t⁵
 +(512/105)t⁷−(128/63)t⁹+(256/693)t¹¹`.

Centering the overlap at `−t/2` reduces the correlation to the integral of
`(z²−t²)[z⁴−2(1+t²)z²+(1−t²)²]²` on `0≤z≤1−t`.
Thus the logarithmic lag and first lag are rational integrals of this polynomial.
The sinh pole is at least `m²/2`, since `xF(x)≥0`.

## Proved obstruction

The smooth witness refutes both the uniform floor `P≥−E/64` and the sufficient
two-moment sign `D≥0`, because `D≤P+E/64`. Complete Weil positivity remains open:
the exact local Gamma remainder and the reserve beyond `E/64` remain present.

`exists_odd_unit_reservedGamma_neg` and `exists_odd_unit_firstFoldTwoMoment_neg`
in `TheUniformGammaReserveCannotPayTheFirstFold.lean` pass the individual source
check with `[propext, Classical.choice, Quot.sound]` only. The polynomial sign and
smoothing continuity lemmas have the same axiom audit; all are umbrella-imported.

For smoothing, multiply the existing odd unit-supported smooth quintics by
`(1−4x²)/(1−2x²)`. On the unit interval this multiplier lies in `[0,1]`, has
Lipschitz constant `8`, and has nonzero denominator. Outside the interval the
product vanishes locally. The resulting C² family has size at most `1`, Lipschitz
constant `32`, and the quadratic cutoff as pointwise limit. Dominated convergence
preserves the strict retained-energy sign.

## Gates

- [x] Exact correlation and rational sign certificate compile with standard-only transitive axioms.
- [x] Strict sign transfers to an odd C² test with exact unit support; individual source check and standard-only transitive-axiom audit pass.
- [ ] Identify and prove the strongest positive survivor before retiring this target.

## Positive survivor under audit

For `0<t≤1`, the exact local Gamma remainder satisfies
`r(t)≥t³/960+t⁴/192`. Set `z=t/2`. Taylor bounds give
`z/sinh z≥1−z²/6+z⁴/60` and `1/cosh z≥1−z²/2+z⁴/6` on `0<z≤1/2`.
The identity `e^(t/2)/sinh t=1/(2sinh z)+1/(2cosh z)` yields the claim.
Multiplication by `E−C(t)≥0` retains the corresponding third and fourth lag
energies. `TheGammaRemainderRetainsHigherLags.lean` contains the proposed proof;
its individual Lean audit is pending.

Four exterior Laplace modes give the sharper candidate reserve `δ>193/20000`,
using `exp(−1/2)≥60653/100000`. Combined with the local bound, the proposed
replacement is `Q≥P+(193/10000)E+M₃/960+M₄/192`, where
`Mₖ=∫₀¹tᵏ(E−C(t))dt`.

A further candidate consequence uses `∫₀¹(E−C)=E` and
`∫₀¹t²(E−C)=E/3+(∫xF)²`. The identity

`t³/960+t⁴/192−(13/3840)t²+1/2560
 =(t−1/2)²(t+1/4)/960+(t²−1/4)²/192`

gives local reserve `17E/23040+13(∫xF)²/3840`. Its Lean audit is pending.

For the same quadratic cutoff,
`Mₖ=256/[315(k+3)]−128/[21(k+5)]+128/[15(k+6)]
−512/[105(k+8)]+128/[63(k+10)]−256/[693(k+12)]`.
The exact candidate certificate in
`TheHigherGammaReserveRepairsTheQuadraticCutoff.lean` tests whether these retained
terms repair the same direction. This certificate and its smoothing transfer
remain unverified.

The full joint Gamma/prime/pole inequality remains active.
