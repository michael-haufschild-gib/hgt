# CCM-FU: sharp weighted terminal head barrier and source escape

- Stage: 3-formalized.
- Type: derived arithmetic obstruction with sharp positive amplitude law.
- Main [fixed-weight complete-path candidate](../1-in-progress/ccm-fu-weighted-head-dissipation.md): unchanged and open.
- Restricted [small-head terminal completion claim](../5-failed/ccm-fu-small-head-weighted-terminal-completion.md): false.
- Modules: `SquareRootAbelSqrtContinuation`, `MobiusDivisorSqrtGrowthObstruction`, `MobiusDivisorSqrtGrowthEscape`, `WeightedScalarMergeAmplitude`, `MobiusDivisorWeightedTerminalHeadBarrier`.

## Exact arithmetic conclusion

Let `S(M)=sum_{1≤d≤M} mobiusDivisorDilationChannel M d`, H denote the
actual empty-label head, V the nonempty energy, and `L_alpha=V+alpha H²`.
A terminal core has processed every prime with square below M, so every
remaining label is a singleton. A complete monotone order inserts each
remaining actual prime exactly once and never increases L_alpha.

For every fixed positive integer c, positive real alpha, real C,
integer J and threshold N₀, there is N≥N₀ such that every terminal core
at M=cN with remaining quotients M/p≤J and a complete monotone order
has `|H|>C sqrt(M)`. Therefore no uniformly square-root-sized family of
such cores admits complete fixed-positive-weight monotone orders, even
eventually along one fixed integer grid.

The result applies directly to the [actual small-core construction](ccm-fu-small-terminal-core.md).
There is b≥8 such that, for every alpha>0, epsilon>0 and threshold N₀,
some N≥N₀ and actual core P at `M=7(b+1)(4N)` satisfy all of:

- P processes every prime outside the positive quotient-seven window and negative late window.
- P is terminal, with `|H|≤5 sqrt(M)`.
- Its complete successor envelope is at most `epsilon M²`.
- P has **no** complete monotone L_alpha continuation.

This is a closed theorem about actual source cores, without RH, numerical
certificates or a prepared-state existence premise. It does not refute
complete monotone paths from the empty processed core: such paths can
avoid these small-head terminal states.

## Sharp positive amplitude law

A terminal step absorbs one signed leaf a into head h and removes a²
from V. Its weighted descent condition is exactly

`alpha(h+a)²≤alpha h²+a²`.

If `|h+a|≤|h|`, the head has not crossed its previous ceiling. Otherwise
`(h+a)a>0`; rearrangement gives

`2alpha |h+a||a|≤(1+alpha)|a|²`.

Since a is nonzero and alpha positive,

`|h+a|≤max(|h|,kappa|a|)`, where `kappa=(1+alpha)/(2alpha)`.

This coefficient is sharp. The unit leaf a=1 with h=kappa−1 gives exact
energy equality, strictly increases head magnitude, and ends at kappa.
Thus a sequence of leaves bounded in magnitude by A satisfies at every
step `|head|≤max(|initial head|,kappa A)`.

Exact terminal fibre transport and the uniform prime-fibre bound give
`|a|≤(3/5)J sqrt(M)` for every remaining prime with M/p≤J, independently
of the later processed state. Consequently every complete terminal order
satisfies

`|S(M)|≤max(|H|,kappa(3/5)J sqrt(M))`.

For `|H|≤C sqrt(M)`, this is a uniform square-root endpoint bound with
constant `max(C,kappa(3/5)J)`. This is stronger than merely bounding the
endpoint by the initial total weighted energy.

## Unconditional source escape

Möbius inversion in the existing corpus gives

`S(M)=sum_{1≤k<M}(sqrt(k+1)-sqrt(k))(psi(k)-k+2gamma)`.

For `g(n)=Lambda(n)-1`, the generic twice-Abel prefix A(N) therefore obeys

`A(N)=S(N+1)-2gamma(sqrt(N+1)-1)`.

Suppose |S(M)|≤C sqrt(M) for every M. Then A has square-root growth.
The existing twice-Abel kernel has unit difference bounded by
`(3|s||s+1|+|s|) n^(-Re(s)-3/2)`. Multiplication by A(n+1) gives a
summable bound of order `n^(-Re(s)-1)`, locally uniform on Re(s)>0.
Thus its sum F is holomorphic throughout that half-plane.

Square-root growth also implies the existing linear prefix bound, so the
proved finite two-Abel transfer identifies F with the actual L-series
on Re(s)>3/2. On the safe Euler half-plane,

`F=-zeta'/zeta-zeta`.

Let `R=zeta-1/(s-1)` be the entire regularization and
`Z=(s-1)R+1` the entire pole-filled zeta, with Z(1)=1. Then G=F+R is
holomorphic on Re(s)>0, and the source identity gives `Z'+GZ=0` on
Re(s)>2. The identity theorem extends that equation to Re(s)>0.
The corpus's unconditional nontrivial zeta zero rho lies in this domain
and gives Z(rho)=0. Analytic first-order ODE zero propagation contradicts
Z(1)=1. Therefore **no** uniform square-root bound for S exists.

No assumption about the real part of rho beyond `0<Re(rho)<1` is used.
This argument does not exclude the O(M) bound required for RH.

## Fixed grids and finite prefixes

A finite prefix cannot absorb the unbounded ratio |S(M)|/sqrt(M), since
S(0)=0 and sqrt(M)≥1 at positive integer cutoffs.

Chebyshev's unconditional bound gives, for k≥1,

`|psi(k)-k+2gamma|≤D k`, with `D=log(4)+5+2|gamma|`.

The exact source increment then satisfies `|S(k+1)-S(k)|≤D sqrt(k)`;
the k=0 increment is zero. For a≤b, telescoping yields

`|S(b)-S(a)|≤D(b-a)sqrt(b)`.

Take a=c floor(M/c). Then a≤M and M−a<c. A bound
`|S(cN)|≤C sqrt(cN)` at every sampled cutoff would force
`|S(M)|≤(|C|+Dc)sqrt(M)` globally, contradicting source escape.
Finite-prefix absorption on the sampled sequence proves cofinal escape
on every fixed positive integer grid. The terminal amplitude theorem
then gives the stated head requirement.

In the prepared-core construction, the two remaining prime windows
both satisfy M<8p, so every remaining quotient is at most seven.
Intersect the eventual core-existence threshold with the cofinal grid
escape threshold. Any constructed core there has head at most 5sqrt(M),
contradicting the necessary head size for a complete monotone order.

## Corpus audit and scope

Starting points were the literal terminal transport, signed scalar merge
order, uniform quotient-fibre bounds, twice-Abel kernel and transfer,
nontrivial zeta-zero existence, pole-filled zeta, and analytic ODE zero
propagation already in the corpus. The new content is the sharp weighted
amplitude law, its actual complete-path transport, the stronger prefix
continuation and cofinal fixed-grid source obstruction, and their
unconditional application to the existing small-core construction.
No claim of priority over external mathematical literature is made.

No experiment was run: the implications were determined by reasoning
from these formal source identities. No numerical output enters Lean.
The full RH chain still lacks a uniform O(M) signed endpoint bound or
complete fixed-positive-weight paths producing it. The result forces
any such path with bounded remaining quotients to retain a head that
escapes every constant multiple of sqrt(M) at the selected cutoffs.

## Validation

Scratch checks and exact foreground `lake env lean` leaf emissions pass
for all five modules. They are wired into RHTower; no umbrella or full
build was run. All 21 new public theorems were audited once in a temporary Lean file;
each depends only on `propext`, `Classical.choice`, and `Quot.sound`.
Generated indexes were refreshed. The single
`scripts/formal_tools.py lint --check-generated` run reported eight
unrelated concurrent modules missing their theorem-area umbrella imports:
`SelbergMaassTraceEnergy` in RHTower; `CavityInteractionCoefficients`,
`CavitySpinHierarchy`, `DiscreteTimeCrystalIndicatorStability`,
`PolyatomicConservation`, `PolyatomicKinematics`,
`QuadraticResponseCorpusApplications`, and `QuadraticResponseHierarchy`
in HTGeometry. No changed proof leaf or proof-debt error was reported.
Those unrelated modules were not edited or built. Owned-scope whitespace
checks passed. All six owned scratch files were removed and every owned
Lean process exited.

A scoped Lake package audit remains pending because earlier package
planning expanded prohibited broad dependencies; that planning was not
repeated. The frontier map was read only.
