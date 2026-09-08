# CCM-FU: complete fixed-core quadratic energy limit

- **Stage:** 3-formalized; exact-file and new-declaration axiom checks passed; Lake packaging pending.
- **Parent:** [energy and signed reserve target](../1-in-progress/ccm-fu-fixed-core-energy-limit.md).
- **Closed:** Every fixed finite prime core, including the empty core, has an explicit complete quadratic energy limit. Its nonnegative block series converges.
- **Open:** Signed dilation correlation control, reserve renewal through changing cores, exhaustive selection, uniform signed Abel bound, RH.

## Exact result

For any fixed finite set of primes P, put

`C_P=(3/5)*2^(card(P)-1)`

with natural truncated subtraction in the exponent. Let b_(P,n) be the
explicit actual block mass from the
[density and moment proof](ccm-fu-fixed-core-density-moments.md), with b_(P,0)=0.
Then

`b_(P,n)>=0`, `sum_n b_(P,n)<infinity`,

`Q_P(M)/M² -> kappa_P=sum_n b_(P,n)`.

Every source index and every quotient depth is retained. P may be empty,
so the original baseline has the same formal coefficient description.
There is no numerical or unknown analytic premise.

The stronger uniform remainder statement is, for every M and positive T,

`sum_(squarefree 1<=r<=M, primeFactors(r) disjoint P, M/r>=T) r*I_P(M,r)^2`

`<= (C_P²/T)*M²`.

Consequently finite quotient depth approximates Q_P(M)/M² with arbitrarily
small nonnegative error, uniformly over all M, including M=0 under Lean's
total division convention. This estimate depends on P through its cardinality;
it does not give uniform control when P grows.

## Dependency-closed paper proof

The source profile already represents Q_P as the squarefree sum over r<M.
At r=M the physical clipping weight is zero and H_P(1)=0, so the sum may
include the terminal index. Group this inclusive source by M/r=n.
The difference between Q_P and its first T quotient blocks is exactly the
nonnegative sum with M/r>=T.

For a squarefree source integer r avoiding P, the exact interpolation and
Möbius-square identities identify r*I_P(M,r)² with F_P(M,primeFactors(r))².
The existing all-source amplitude theorem bounds its square by C_P²*M.
The quotient tail has at most floor(M/T) indices, since every such r obeys
1<=r<=floor(M/T). Hence the complete tail is at most C_P²*M²/T.
This argument also covers the empty core; head cancellation is unnecessary
for existence of the energy limit.

Every finite block sum converges by the proved source density and weighted
moments. Given epsilon>0, choose T with C_P²/T<epsilon/3. The full normalized
energy lies within epsilon/3 of its finite-block approximation for every M.
The finite approximation is Cauchy, so the full sequence is Cauchy in the
complete real field and converges to some kappa_P.

Each block mass is nonnegative by passage from nonnegative source energies.
Every finite sum of block masses is at most kappa_P. Therefore their series
is summable. The uniform remainder estimate forces the series sum to equal
kappa_P: any positive difference would exceed the arbitrarily small allowed
remainder. This proves the stated explicit limit.

## Lean validation

Six public theorems in `MobiusDivisorFixedCoreEnergyLimit.lean` pass a
foreground scratch check and exact-leaf emission via
`lake env lean <file> -o <leaf.olean>`. A separate scratch audit of these
six new declarations reports only `propext`, `Classical.choice`, and
`Quot.sound`. The formal lint gate passes; the declaration index is refreshed.
The leaf is wired into `RHTower.lean`. No full or umbrella build is run. The known Lake packaging
audit remains pending to avoid its broad prerequisite rebuild.

Owned scratch files and validation logs are removed; no owned Lean process remains.
