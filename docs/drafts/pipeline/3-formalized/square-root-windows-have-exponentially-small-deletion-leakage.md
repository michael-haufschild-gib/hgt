# Square-root windows have exponentially small deletion leakage

- **ID:** B130-PTA-L
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `../1-in-progress/b130-positive-tail-annihilation-and-scale-locality.md`
- **Lean:** `SurfaceOfSpecZ/ScaleLocality/SquareRootWindowLeakage.lean`

## Statement

Let `f(u)=Σ Re(c_j exp(w_j u))`, `A=Σ|c_j|<∞`, and
`|Re w_j|≤D` on nonzero coefficients, with `D≥0`. Fix `r>0` and
put `V₀=r²/(16(D+1))`. An infinite positive deletion of square cost
`V≤V₀` satisfies

`F(t)≥-K-2A exp(DB+D²V₀-T)`

whenever `T≥0`, `|t|≤T+B`, `K≥0`, and
`f(u)≥-K` for `|u-t|≤r√T/2`. Here `F` denotes the limiting
filtered trace. The leakage is uniform over bounded displacement windows.

## Proof

In the translated Gaussian floor choose `q=4(D+1)√T/r`.
Since `(D+q)²≤2D²+2q²`, `q r√T/2=2(D+1)T`, and
`q²V₀=(D+1)T`, the leakage exponent is at most

`D(T+B)-2(D+1)T+D²V₀+(D+1)T = DB+D²V₀-T`.

## Audit and limit

`infinite_tail_squareRoot_floor` passes Lean. Its transitive axioms are
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.

This is the quantitative local estimate. The zeta depth criterion and
prime-window transfer still require formal completion. B130 remains open.
