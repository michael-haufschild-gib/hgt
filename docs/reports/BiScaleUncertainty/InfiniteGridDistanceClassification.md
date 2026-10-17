# Distance-to-grid classification of separated polar copies

## Statement and domain

Write `h_f(x)=integral f(u)f(u+x)du`, `R_f=h_f(0)`, and
`E(f)=J_arch(f)/R_f`. For `T>=2`, define

\[
N(T)=\lfloor e^T\rfloor,\qquad
d(T)=\min\{T-\log N(T),\ \log(N(T)+1)-T\}.
\]

Consider compact smooth nonzero sources `k` with correlation support radius at most `1/2`,
and their canonical polar copies `g= k-exp(-T/2)k(.-T)`.

**Classification.** Such a source whose copy satisfies `h_g(log n)=0` for every `n>=2`
exists if and only if `T` is not a logarithmic-grid node. Every such copy obeys

\[
\frac{e^{-1/2}}4\log\frac1{d(T)}\le E(g),
\]

and one constant `C` independent of `T` supplies an actual smooth compact source with

\[
E(g)\le C+\log\frac1{d(T)}
\]

at every off-grid center `T>=2`. Its polar moment vanishes exactly. Both energy inequalities
concern actual scalar sources. No admissibility or analytic estimate is assumed at the
existence endpoint. The leading lower and upper coefficients are not claimed equal or optimal.

## Nearest-node geometry [PROVED HERE]

Since `e^T>=T+1>=3`, `N(T)>=2`. The floor inequalities give
`log N(T)<=T<log(N(T)+1)`. Hence `d(T)>=0`.
Every integer `n>=2` lies either at or below `N(T)` or at or above `N(T)+1`.
Monotonicity of logarithm then gives `d(T)<=|log n-T|`. One of the two bracketing nodes
attains equality. Consequently `d(T)=0` exactly at grid nodes, and `d(T)>0` exactly off-grid.
The already certified ceiling node has displacement in `[0,exp(-T)]`, so
`d(T)<=exp(-T)<=1`.

## Exact-node obstruction and lower bound [PROVED HERE]

The stronger lower statement allows any nonzero real coefficient `a` and any compact C²
source `f` with positive origin mass, correlation radius `D>=0`, and `T>D+1`.
Choose a nearest grid node `x=log n`, so `|x-T|=d(T)<=1`.
Then `x>=T-1>D` and `x+T>D`. The exact copy formula reduces to

\[
h_{f-a f(.-T)}(x)=-a\,h_f(x-T).
\]

Grid admissibility and `a!=0` force `h_f(x-T)=0`. Evenness gives `h_f(d(T))=0`.
If `d(T)=0`, this contradicts `R_f>0`; this is the exact-node obstruction.
Otherwise the certified logarithmic increment bound gives

\[
e^{-1/2}R_f(-\log d(T))\le4J_{\rm arch}(f).
\]

Local preservation holds at displacement `d(T)<=1`, since `T>D+1`. Thus the copy itself
has correlation zero at `d(T)` and origin mass `(1+a^2)R_f>0`. Applying the same increment
bound to the copy gives the asserted lower bound for both base and copy.
For the radius-`1/2` class, `T>=2` supplies the required separation automatically. ∎

## Actual off-grid construction and upper bound [PROVED HERE]

Choose once a nonzero smooth compact seed `f` from the certified bump construction,
a positive correlation radius `D`, and the certified constant `A` with
`E(f(L .))<=A+log L` for `L>=D`.
For any off-grid `T>=2`, put `d=d(T)>0`,

\[
L=\frac{4(D+1)}d,\qquad k(u)=f(Lu),\qquad \rho=d/4.
\]

Here `L>=1`, `L>=D`, and `L rho=D+1>D`. Therefore `h_k(x)=0` whenever `|x|>rho`.
Since `d<=1`, `rho<=1/4<1/2`. Every grid node `log n`, `n>=2`, exceeds `rho`, because
`log 2>=1/2`. Every node has distance at least `d>rho` from `T`; also `log n+T>rho`.
All three terms in the copy correlation formula vanish, proving every infinite-grid zero.

Scaling and translated-copy subtraction preserve smoothness and compactness. Local preservation
gives positive copy mass `(1+exp(-T))R_k`; the existing exact polar identity gives its zero
cosh moment. Apply the polar-copy error bound with correlation radius one:

\[
|E(g)-E(k)|\le P(k,1)e^{-T}=L^{-1}P(f,1)e^{-T}\le P(f,1).
\]

Since `log L=log(4(D+1))-log d`, the upper bound follows with
`C=A+log(4(D+1))+P(f,1)`. The previous lower bound applies to this constructed source.
This proves the full classification and matching growth order. ∎

## Interpretation and audit boundary

The relevant quantity is the distance from a tail center to the grid, not separation alone.
At fixed large scale, approaching a grid node forces logarithmically diverging energy; at the
node, the separated two-copy class is empty. Off-grid centers retain actual polar sources.
This is the positive classification surviving the exact-node obstruction.
Multiple interacting packets and the unrestricted polar class are not classified here.

Current corpus search: `/tmp/infinite-grid-distance-current-search.txt`. Its useful hits supply
the preceding certified inputs; source-only results were checked against their actual files.
The general classification was not found in that search or the exhaustive scoped text search.
Logarithmic scaling itself is classical; see
[Laptev–Weth, Lemma 2.5](https://www.ma.imperial.ac.uk/~alaptev/Papers/laptev-weth-2020-revised.pdf).
The contribution claimed is the connected corpus classification, not an exhaustive external novelty claim.
## Lean certificates and checks

`LogarithmicGridDistance.lean` contains 8 nearest-node geometry theorems.
`InfiniteGridDistanceClassification.lean` contains 7 source and energy theorems, including:

- `subtractCopy_infinite_grid_distance_energy`: positive distance and logarithmic lower bounds
  for both base and copy, for arbitrary nonzero coefficient and separated compact C² seed.
- `exists_smooth_polar_source_at_off_grid_center`: actual smooth compact polar recovery at
  every off-grid center, with a uniform upper constant and the matching-order lower bound.
- `exists_smooth_separated_polar_grid_source_iff`: exact center classification.

Both leaves passed `lake --old env lean` without diagnostics. All 15 new theorems were checked
in `/tmp/infinite_grid_distance_audit.lean`; only `propext`, `Classical.choice`, and `Quot.sound`
occur. Both modules are wired into the umbrella; the refreshed API contains all 15 declarations.
No numerical experiments, new axioms, heartbeat changes, or full builds were used.

Logs: `/tmp/infinite-grid-distance-{geometry,classification,axioms,index,lint}.log`.
Global lint reports four concurrent foreign modules missing umbrella reachability:
`NonTemperedShiftedZetaPairCountermodel`, `WeilConeMismatchWitnesses`,
`ZeroCountRemainderNotIntegrable`, and `OddMultiplierLeakageFamily`.
Neither new module has a lint error; repository-wide green is not claimed.
Count: one significant package, number 3 in the dedicated ledger.
