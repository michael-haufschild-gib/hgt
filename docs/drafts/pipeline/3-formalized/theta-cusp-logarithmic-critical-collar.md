# A logarithmic critical collar for every finite theta rank

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6
- **Statement:** There is `c>0`, independent of rank, such that every actual signed center-mixed theta Hankel section of size `n≤N` is positive definite whenever
  `|a−1/2| < c/(1+log(N+1))`.

## Proof

Write `J(a,b)` for the actual Xi Fourier current. The corpus's logarithmic
zero-free sign theorem gives `J(a,b)≥0` on `|b|≤T` when `a>0` and

`a ≥ 1/2−1/[58 log(T+1/2)]`.

The low-height rectangle supplies the same sign below height four. At a
zero of Xi the current vanishes, so the logarithmic-derivative formula
introduces no nonvanishing premise.

Boundary strictness and the uniform aperture Lipschitz bound give fixed
`m,r,ε>0`, `r≤1`, such that `J(a,b)≥m` on `[0,r]` whenever
`|a−1/2|≤ε`. For the truncated current on `[-T,T]`, the factorial moment
coercivity therefore gives

`m r^(2N+1)‖v‖² ≤ B_N vᵀH_trunc(a,T)v`,

where `B_N=N!((2N)!)^N`. This uses the uniform moment matrix on `[0,1]`:
clearing its denominators gives an integer determinant floor; its
cofactors bound the inverse quadratic form; diagonal rescaling gives
coercivity on `[0,r]`.

Uniform Xi decay gives fixed `M>0`, `K≥1`, `κ=π/8` with

`|∫_(|b|>T) b^k J(a,b) db| ≤ M K^k k! exp(−κT)`

for `|a|≤3/4`, `T≥0`, every `k`. Hence the tail quadratic form is at most
`N M K^(2N)(2N)! exp(−κT)‖v‖²` in absolute value.

Set `S=1+M+2/m+1/r+K`. The elementary bound `k!≤exp(k²)` gives

`2 N M N!((2N)!)^(N+1)K^(2N)/(m r^(2N+1))`
`≤ exp((4S+6)(N+1)^3)`.

Choose `D=4+(4S+7)/κ`, `T=D(N+1)^3`. The tail then costs at most half
the positive truncated floor. Finally,

`log(T+1/2) ≤ (log(D+1)+3)(1+log(N+1))`.

Taking `c=min(ε,1/8,1/[58(log(D+1)+3)])` enforces both the fixed positive
core and nonnegativity up to `T`. Exact truncation plus the tail estimate
makes the raw moment matrix strictly positive. The normalization
`m_k(a)=2π·2^(−k)·s_k(a)` is a positive diagonal congruence, and principal
submatrices give the claim simultaneously for every `n≤N`.

## Lean

`GaloisForLFunctions/ThetaCuspSections/LogarithmicCriticalCollar.lean`,
namespace `GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar`:

- `signedHankel_posDef_logarithmic_collar`
- `signedHankel_posDef_logarithmic_collar_upto`

Canonical source checks and transitive axiom audits use only `propext`,
`Classical.choice`, `Quot.sound`. Imported by `ThetaCuspSections.lean`.

**Open:** a rank-independent collar, or any fixed rank above eight
throughout `0<a<1/2`. The logarithmic collar still shrinks with rank;
Σ6 remains partially solved.
