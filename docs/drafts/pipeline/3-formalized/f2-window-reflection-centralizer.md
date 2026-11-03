# The reflection centralizer of the window Dirichlet algebra

- **ID:** f2-window-reflection-centralizer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** F2 reflection assembly; `WindowTowerOfSpecZ/TheReflectionCentralizerOfTheWindowAlgebra.lean`.
- **Statement:** For `A≥0`, the truncated Dirichlet actions commuting with `σ_A H(u)=H(−A−u)` are precisely scalar actions, on both the full supported-function module and the smooth window test space.

## Exact classification

Write `ρ_A(f)H(u)=Σ_{1≤n≤floor(exp A)} f(n)/√n · 1_{u≤0}H(u−log n)`.

| Domain | Commutation criterion | Resulting action |
|---|---|---|
| All functions supported on `[−A,0]` | `f(n)=0` for every active `n≥2` | `f(1)H` |
| `C²` functions supported on `[−A,0]` | `f(n)=0` whenever `n≥2` and `log n<A` | `f(1)H` |

At an exact boundary `log n=A`, the shift annihilates continuous tests. The smooth coefficient condition is therefore sharp.

## Proof

On the full module, test commutation on the indicator of `{−A}` and evaluate at `−log n`. The reflected forward action is `f(n)/√n`; all forward shifts of the reflected endpoint vanish there. Distinct logarithms isolate each coefficient. Conversely, vanishing of those coefficients leaves only the term at `1`.

For a continuous supported function, its nonzero set is open and lies in `[−A,0]`, hence lies in `(−A,0)`. Thus shifts of length at least `A` act by zero.

For an interior coefficient `n≥2`, `log n<A`, set `c=−(A+log n)/2` and `x=(log n−A)/2`. Both points lie inside the window. The finite set of competing samples consists of `x−log k` for active `k≠n`, and `x+log k` for all active `k`. It excludes `c`: the first equality would force `k=n`; the second would force `log k=−log n<0` although `k≥1`.

The open window minus these finitely many points contains `c`. A smooth function with exactly that support is nonzero at `c` and zero at every competing sample. Evaluating commutation at `c` gives `(f(n)/√n)H(c)=0`, hence `f(n)=0`. Conversely, the interior coefficients vanish and all remaining full-length shifts act by zero, leaving the scalar term.

## No-go closure

- **Excluded construction:** a non-scalar reflection-commuting operator inside the forward window Dirichlet representation.
- **Positive survivor:** exact centralizer classification, including the smooth boundary exception.
- **Implication for F2:** a non-scalar Hecke action must use adjoint shifts, a larger operator algebra, or the period cusp channel. This theorem does not exclude those extensions or establish Weil positivity.

## Lean audit

- `windowRepFun_commutes_reflection_iff`
- `windowRepFun_commutes_reflection_iff_scalar`
- `smooth_windowRepFun_commutes_reflection_iff`
- `smooth_windowRepFun_commutes_reflection_iff_scalar`

Individual final check: `lake --old env lean GaloisForLFunctions/WindowTowerOfSpecZ/TheReflectionCentralizerOfTheWindowAlgebra.lean`.
All four transitive axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`. The module is imported by `WindowTowerOfSpecZ.lean`.
