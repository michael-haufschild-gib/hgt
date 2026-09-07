# CCM-FU: actual growing batches of both prime signs

- **ID:** CCM-FU-SIGNED-BATCHES
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Result:** A fixed small prime core exposes positive and negative isolated source pools of superlinear mass. Selected subpools consume arbitrarily many linear units of both signs, with a complete batch order under one uniform quadratic energy ceiling.

## Exact unconditional statement

Let `P0={p prime: p<8}` and `F_M(P,R)` be the literal retained divisor fibre.
There exists a fixed integer `b>=8` such that, for every real T and every
sufficiently large integer N, at cutoff `M=7(b+1)(4N)` there are subpools

`L subset {p prime: b(4N)<p<=(b+1)(4N)}`,

`R subset {p prime: M/2<p<=M}`,

with `sum_L F_M(P0,{p})>=TM` and `sum_R -F_M(P0,{p})>=TM`.
A complete distinct order of `L union R` has, at every prefix W,

`E_M(P0 union W)<=2^8*722*M^2=184832*M^2`.

Every partial preparation of P0 has the same bound. The constant is independent
of T, b, N, and the selected subpools. The batch itself stays below `E_M(P0)`.
No original-diagonal bound is assumed for its endpoint, and no zero-location
premise occurs in the capstone.

This is a growing **partial** prime schedule. It leaves middle primes
unprocessed and does not establish complete prime coverage, SD1, or RH.

## Positive source supply

The corpus proves `A=S(7)<0` for the complete actual signed source. Set
`B=S(8)`, `c=-A/2>0`, and `K=|B-A|`. Choose an integer `b>=8` with `70K<=bc`.
For `bN<p<=(b+1)N` at `M=7(b+1)N`, the exact quotient is seven. The literal
clipping weight w satisfies

`w sqrt(p)(sqrt(8)-sqrt(7))=sqrt(M)-sqrt(7p)`.

The analytic square comparisons `sqrt(8)>=14/5` and `sqrt(7)<=27/10` give a
gap of at least `1/10`. Also

`(sqrt(M)-sqrt(7p))*sqrt(p)<=M-7p<=7N`.

Consequently `wp<=70N` and `bw<=70`. Thus

`(1-w)A+wB=A+w(B-A)<=A+wK<=A+c=-c`.

All source primes at both adjacent cutoffs seven and eight belong to P0.
The exact clipped prime-fibre recursion therefore gives

`F_M(P0,{p})=-sqrt(p)((1-w)A+wB)>=c sqrt(p)>=c sqrt(N)`.

This holds for every prime in the fixed window, at every N. The corpus prime
count theorem supplies eventually at least `N/(2 log(bN))` such primes.
Their total retained positive mass divided by M is at least

`c sqrt(N)/(14(b+1)log(bN)) -> +infinity`.

The limit uses the proved analytic estimate `log(x)=o(sqrt(x))`. No numerical
experiment or computed channel value is used.

## Isolated pools before the terminal phase

If the processed set P contains every source prime below `floor(M/p)+1`,
the two adjacent quotient fields vanish at every nonempty retained label.
The prime-containing field is therefore its singleton or zero. Processing
other primes in such an isolated pool leaves each surviving singleton fixed.
In particular, P0 isolates every unprocessed prime with `M<8p`. Both the
positive window above and the late window satisfy this condition.

For any isolated pool U, write `h=F_M(P,empty)` and `c_p=F_M(P,{p})`. For L
contained in U, exact source insertion gives

`E_M(P union L)=E_M(P)+2h sum_L c_p+(sum_L c_p)^2-sum_L c_p^2`.

The energy is a constant plus the signed scalar merger energy. The corpus's
complete signed scalar-order theorem therefore supplies an order of U below
`max(E_M(P),E_M(P union U))`. No assumption about signs or either endpoint
is needed for that order theorem.

## Matching with removed-square reserve

For any nonnegative finite supply w with total at least a nonnegative target t,
there is a subpool J crossing t whose overshoot obeys

`(sum_J w-t)^2<=sum_J w^2`.

Use the corpus crossing-square lemma with the total supply as a finite upper
bound on each weight. This retains the square of the crossing term and does
not replace it by an absolute-mass estimate.

Let the positive supply have mass alpha and the negative supply magnitude beta,
with both at least `|h|`. If `h+alpha<=beta`, consume the entire positive pool
and cross target `h+alpha` in the negative pool. Otherwise consume the entire
negative pool and cross target `beta-h` in the positive pool. Both targets
are nonnegative and covered. In either case the final head square is at most
the selected removed singleton-square sum. Both consumed signed magnitudes
are at least `min(alpha,beta)-|h|`. The exact energy identity then bounds the
final energy by the starting energy; the signed scalar order bounds every
prefix by that same starting energy.

## Fixed-core preparation and actual assembly

The proved good/defect split gives `G+D=E` and merger gain at most
`2sqrt(GD)<=G+D`. Thus each prime merger costs at most a factor of two, and
processing a finite core P costs at most `2^card(P)` times the original
energy. Every subset of P0 has at most eight elements, and the corpus diagonal
bound is `E_M(empty)<=722M^2`. This proves the uniform preparation bound above.
The head square is part of the energy, so `|F_M(P0,empty)|<=184832M`.

Pass to N replaced by 4N. The positive-window mass remains superlinear. At the
same cutoffs the existing late-prime mass theorem applies by composition;
late retained singletons are exactly `-K_p(M)<=0`. The terminal endpoint M
is composite, so all primes in that late pool are strictly below M. The two
pools are disjoint and both are isolated after P0.

For any T, both total masses eventually exceed `(max(T,0)+184832)M`.
The matching theorem therefore consumes at least TM of each sign. Its
complete distinct order stays below the fixed-core energy and hence the
uniform quadratic ceiling. All constants and quantifiers are fixed before
the choice of the selected batch.

## Remaining frontier

The full proof chain is Guinand–Weil source → marked rectangular current →
affine Suzuki checkpoints → signed curvature → prime–polar–Gamma/unit-Riesz
boundary → Xi-screw Green → RH. Its complete signed-source producer remains
open. The construction proves actual growing signed consumption with an
independent energy bound; it does not cover the unprocessed middle primes or
control the changes they make to the remaining pools. Continued compatible
supply, those overlapping-label steps, and final complete-source control still
require proof. PE4, PE4G, SD1, the all-cutoff two-prime ceiling, and RH are open.

## Lean and validation

- `MobiusDivisorPositivePrimeSupply`: two public theorems, including uniform
  positivity of the actual macroscopic window and its superlinear mass.
- `MobiusDivisorSignedPrimeBatches`: ten public theorems for source isolation,
  exact energy transport, complete orders, core preparation, and matched batches.
- `MobiusDivisorGrowingSignedPrimeBatches`: the unconditional capstone
  `exists_mobiusDivisorGrowingSignedPrimeBatches`.

Scratch checks and all three exact leaves passed foreground `lake env lean`.
Only the three new required oleans were generated; no dependency, umbrella,
or full build was run. All three leaves are wired once in RHTower. All thirteen
new public theorems were axiom-audited once in a separate scratch file: only
`propext`, `Classical.choice`, and `Quot.sound`, with no added axioms,
`sorryAx`, or computational certificate. The printed capstone has no external
premise. Global formal lint passes with 132 existing large-file warnings;
none concerns these new leaves. Scoped tracked whitespace checks pass.
No numerical experiment was run.

The declaration search index was refreshed once. New-file whitespace, all added
links, and all three umbrella imports were checked. All eight owned scratch/log
files were removed; no owned Lean or lake process remains.
