# CCM-FU: second centering of the modular hyperbola

- **Stage:** 3-formalized
- **Parent:** [unit-channel comparison](../1-in-progress/ccm-fu-two-prime-local-blocks.md)
- **Type:** sharper analytic source bound, not a numerical certificate
- **Boundary:** this tightens the unsigned source estimates; the unit factor-two comparison and RH remain open.

## Exact source bounds

For the centered residue ramp, the first primitive is `P_d(N)=-r(d-r)/(2d)`, where r=N mod d. Its period mean is `-B_d`, with `B_d=(d^2-1)/(12d)`. The centered shifted primitive

`S_d(N)=r(d-r)(d-3-2r)/(12d)`

satisfies `S_d(N+1)-S_d(N)=P_d(N+1)+B_d` and `|S_d(N)|<=d^2/12`. A second Abel summation for w and its decreasing nonnegative difference g gives

`|sum ramp_d(k) w(k)+B_d w(0)-(B_d+P_d(N))w(N)| <= (d^2/12)g(0)`.

For the half-order clock born at d^2, the first clock difference is exactly

`g(k)=2/[(sqrt(x)+sqrt(x+1))(sqrt(x+1)+sqrt(x+2))(sqrt(x)+sqrt(x+2))]`, x=d^2+k.

It is nonnegative and decreasing, with `g(0)<=1/(4d^3)`. Thus the error per modulus is at most `1/(48d)`. Summing over all actual square births retains the moving terminal phase and costs only a harmonic error. With s=floor(sqrt(M-1)), w_M=sqrt(M+1)-sqrt(M), and H_s the harmonic number, the exact resulting bounds for the centered Abel source C(M) are

`-s/24-s(s+1)w_M/48-H_s/16 <= C(M) <= -s/24+s(s+1)w_M/24+5H_s/48`.

The square-root birth and harmonic bounds give, at every natural cutoff,

`-5 sqrt(M)/96-log(M+1)/16-7/96 <= C(M)`,

`C(M) <= -sqrt(M)/48+5 log(M+1)/48+1/6`.

For every epsilon>0, eventually `(-5/96-epsilon)sqrt(M)<=C(M)<=(-1/48+epsilon)sqrt(M)`. The literal centered contribution therefore tends to negative infinity. No convergence to one coefficient is asserted.

## Improved actual unit-channel floor

Retain the square-root error in the existing smooth-prefix estimate instead of absorbing it into a constant: `sum_(k<=N) smooth(k)>=N/6-17 sqrt(N)`. The exact clock difference satisfies `sqrt(k)(w_k-w_(k+1))<=1/(4k)`. Abel summation, with its terminal term bounded separately, yields

`smoothAbel(M)>=sqrt(M)/6-17 log(M+1)/4-13`.

The exact arithmetic identity `K_1=smoothAbel+2C` then gives

`K_1(M)>=sqrt(M)/16-5 log(M+1)-14`.

For every epsilon>0 the actual unsigned unit channel is eventually at least `(1/16-epsilon)sqrt(M)`. These are closed analytic source bounds. They do not supply the factor-two upper/lower comparison, an original two-prime ceiling, a complete growing schedule or SD1. A sharper upper comparison or a direct relation between dilations is still required.

## Lean certificate

`HTGeometry.SecondCenteredModularAbel` contains the exact mean, cubic primitive, second Abel identity, clock-difference formula, reciprocal error and literal square-birth transport. `RHTower.DivisorSecondCenteredHyperbola` contains nine public theorems, including the finite source bounds, eventual negative coefficient band, negative divergence, smooth-prefix transport and improved unit floor. Together they contain two definitions and twenty public theorems.

Both complete scratch proofs and both exact leaf checks passed with `lake env lean`; the required leaf oleans were generated without dependency or umbrella builds. All 22 new public declarations were audited once in a separate scratch file: their dependency closures use only `propext`, `Classical.choice` and `Quot.sound`, with no added axioms or computational certificates. `python3 scripts/formal_tools.py lint` passed (existing large-file warnings only). No channel table was recomputed, and no numerical result enters any proof. The two leaves are wired in their respective umbrellas without building those umbrellas.
