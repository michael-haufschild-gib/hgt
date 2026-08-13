# Route E whole-anchor capacity--displacement conservation law

- **ID:** ROUTE-E-WHOLE-ANCHOR-CAPACITY-DISPLACEMENT-001
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SHARP FULL-ALLOCATION NO-GO / POSITIVE CONSERVATION LAW
- **Parent:** route-e-whole-anchor-bidirectional-harmonic-e3-law.md
- **Source:** OPEN-SOURCE-001
- **RH used:** no
- **Computation used:** no
- **Lean target:** RHTower/MobiusWholeAnchorCapacityDisplacement.lean
- **Lean status:** target module formalizes the exact finite core: E3 breadth addition, reservoir
  band decoding, opposite-sign/displacement packet, full-subset reciprocal Euler mass, and sharp
  row-stochastic capacity inequalities (`(4)`, `(9)`). As of 2026-08-13 the global layers are also
  formalized, unconditional and umbrella-wired: `Sieve/AlmostPrimeGlobalCount.lean` proves the
  effective Chebyshev bound, the Mertens upper bound `∑_{p≤N} 1/p ≤ log log N + K`, the
  least-factor count recursion, and the fixed-order Hardy–Ramanujan bounds
  (`exists_squarefreeOmegaCount_two_bound`, `exists_squarefreeOmegaCount_three_bound` = `(10)`);
  `MobiusWholeAnchorGlobalTerminalCapacity.lean` defines the literal terminal universe
  (all window integers `t_R·m` over band-reservoir subsets of bounded product and squarefree
  three-prime tokens), proves the label split `(11)`/`(12)`
  (`wholeAnchorTerminalUniverse_card_le_sum` + per-label Hardy–Ramanujan window bound), the
  Mertens band product bound `(13)` (`bandPrimes_eulerProduct_le`,
  `∏_{W<p≤Z}(1+1/p) ≤ K₂ log Z/log W` from the sharp second Mertens theorem), and the boxed
  capacity bounds `(2)`/`(14)`: `exists_wholeAnchorTerminalUniverse_card_le` (Euler-product form)
  and `exists_wholeAnchorTerminalUniverse_card_le_theta` (θ form, with the band floor
  `A·(log log b + K) ≤ log W` as the exact `W ≥ (log X)^A` regime hypothesis). Module builds pass;
  axiom audits `[propext, Classical.choice, Quot.sound]` on all nine leading theorems. Remaining
  for stage 3: the `o(1)` sequence corollary `(3)`, the kernel-composition corollary combining
  `(2)` with `(4)`, and the proposed-band specialization `(5)`/`(6)`.

## 1. Statement

Consider full-allocation whole-anchor Route E relation with terminal
\[
q=tm,
\]
where \(m\) is squarefree with exactly three prime factors and every reservoir subset of each
prescribed breadth at most \(3L\) in band \(W<p\le Z\) is an allocation, with
\(L=\log\log X\). Assume terminals lie in fixed multiplicative window \([cX,CX]\). Put
\[
\theta_X=\frac{3L\log Z}{\log X};
\qquad t\le X^{\theta_X}.                                      \tag{1}
\]
Then full physical terminal universe \({\cal T}_X\), even after granting every reservoir product
and every squarefree \(E_3\) cofactor, obeys
\[
\boxed{
\#{\cal T}_X
\ll_{c,C}
\frac{XL^2}{\log X}
\prod_{W<p\le Z}\left(1+\frac1p\right)
\ll_{c,C,A}\theta_X X}
                                                               \tag{2}
\]
whenever \(W\ge(\log X)^A\), \(A>0\).

If full-band construction requires uniform critical half-scale bound on every allocation, then
\(\theta_X=o(1)\), so
\[
\#{\cal T}_X=o(X).                                             \tag{3}
\]
For every nonnegative row-stochastic kernel from sources \({\cal A}_X\) to physical terminals,
\[
\boxed{
\max_{q\in{\cal T}_X}\sum_{n\in{\cal A}_X}P_X(n,q)
\ge\frac{\#{\cal A}_X}{\#{\cal T}_X}.}                         \tag{4}
\]
Thus \(\#{\cal A}_X\gg X\) forces unbounded column load. Representation multiplicity, allocation
weights, both grade directions, and use of every \(E_3\) token do not change (4).

For proposed band
\[
W=\exp(\exp\sqrt L),\qquad Z=\exp(\log X/L^2),                  \tag{5}
\]
one obtains
\[
\#{\cal T}_X\ll X\exp(-\sqrt L+O(\log L)),\qquad
\max_q\sum_nP_X(n,q)\ge\exp(\sqrt L-O(\log L)).                 \tag{6}
\]
Hence proposed full-band whole-anchor relation cannot be central-density Route E closure at
bounded column load. A source-predeclared, adaptively product-truncated subset of a much wider
prime band is not covered and becomes a separate frontier.

## 2. Exact finite conservation law

Let \(A,T\) be nonempty finite sets and \(P:A\times T\to\mathbb R_{\ge0}\) satisfy
\[
\sum_{q\in T}P(n,q)=1\quad(n\in A).                            \tag{7}
\]
Changing order of summation gives
\[
\sum_{q\in T}\sum_{n\in A}P(n,q)
=\sum_{n\in A}\sum_{q\in T}P(n,q)
=\#A.                                                          \tag{8}
\]
Some column is therefore at least \(\#A/\#T\), proving (4). More generally, column ceiling
\(C\) forces
\[
\#A\le C\#T.                                                   \tag{9}
\]
These statements are exact and make physical capacity, rather than representation count,
invariant.

## 3. Global \(E_3\) capacity

Write
\[
E_3(Y)=\#\{m\le Y:\mu(m)\ne0,\ \omega(m)=3\}.
\]
Fixed-order Hardy--Ramanujan gives
\[
E_3(Y)\ll \frac{Y(1+\log\log Y)^2}{\log Y}.                    \tag{10}
\]
For fixed \(t\), condition \(tm\in[cX,CX]\), uniformly for \(t\le X^{o(1)}\), therefore gives
\[
\#\{m:tm\in[cX,CX],\mu(m)\ne0,\omega(m)=3\}
\ll_{c,C}\frac{XL^2}{t\log X}.                                 \tag{11}
\]
Dropping coprimality, forbidden-support, band-separation, structured-shape, and breadth conditions
only enlarges terminal set. Summing over every reservoir subset gives
\[
\begin{aligned}
\#{\cal T}_X
&\ll_{c,C}\frac{XL^2}{\log X}\sum_R\frac1{t_R}\\
&=\frac{XL^2}{\log X}
\prod_{W<p\le Z}\left(1+\frac1p\right).                        \tag{12}
\end{aligned}
\]
This grants all breadths, more than proposed two source-dependent breadths.

By \(\log(1+u)\le u\) and reciprocal-prime Mertens,
\[
\prod_{W<p\le Z}\left(1+\frac1p\right)
\ll\frac{\log Z}{\log W}.                                      \tag{13}
\]
Since \(\log W\ge AL\) and \(\log Z=\theta_X\log X/(3L)\),
\[
\#{\cal T}_X
\ll_A\frac{XL^2}{\log X}\frac{\theta_X\log X}{3AL^2}
\ll_A\theta_X X,                                               \tag{14}
\]
proving (2).

## 4. Why full allocation forces displacement loss

At terminal scale \(q\asymp X\), square-root token interval at argument \(X/t\) produces
\[
|q-n|\asymp t\sqrt{X/t}=\sqrt{Xt},                             \tag{15}
\]
up to subpower logarithmic factors. Its Gibbs first-difference cost at \(x\asymp X^{-1}\) is
\[
X^{-1}|q-n|=X^{-1/2}t^{1/2+o(1)}.                              \tag{16}
\]
Uniform critical half scale over every full-band allocation requires \(t=X^{o(1)}\) uniformly.
Allocations at upper band edge make this \(\theta_X=o(1)\), up to harmless breadth constants.
Equations (14) and (4) finish no-go.

Result is conservation law: increasing full-band reservoir entropy enlarges terminal capacity
only by increasing maximum reservoir product, while same product worsens displacement through
square-root Jacobian.

## 5. Proposed-band specialization

For (5),
\[
\frac{\log Z}{\log W}
=\frac{\log X}{L^2\exp\sqrt L}.
\]
Substitution into (12) gives first estimate in (6); (4) gives second for linear-size central
source set.

## 6. Conjecture--proof--failure loops

### Loop A: natural-density \(E_3\) closes unit load

[CONJECTURE] Full \(E_3\) density supplies enough physical terminals.

[FALSIFIED FOR PROPOSED BAND] Granting entire global \(E_3\) set already gives (12), which is
sublinear by (5).

### Loop B: representation multiplicity restores capacity

[CONJECTURE] Many reservoir/token representations let one physical terminal absorb row mass
without column growth.

[FALSIFIED] Equation (8) is evaluated after projection to physical terminals. Splitting and
remerging a column preserves total load.

### Loop C: widen reservoir band

[CONJECTURE] Larger \(Z\) restores linear full-band capacity.

[FAILED FOR FULL ALLOCATION] Equation (14) requires \(\theta_X\gg1\); full allocation then includes
fixed-power products and (16) loses fixed power. This does not exclude predeclared
product-truncated subfamily.

### Loop D: use all breadths

[CONJECTURE] Source-dependent breadth caused capacity loss.

[FALSIFIED] Equation (12) already grants every subset and every breadth.

## 7. Positive survivor and exact new frontier

Positive survivor is exact invariant
\[
\boxed{\text{bounded column load}\Longrightarrow
\text{physical terminal density comparable to source density}.} \tag{17}
\]
Whole-anchor \(E_3\) remains useful for sparse exceptional sources or local sign correction.
Central-density route now has four honest options:

1. use product-truncated high-band reservoir family, whose harmonic row mass is now proved in
   `route-e-product-truncated-reservoir-harmonic-mass-law.md`, and prove its missing fine physical
   columns while remaining on \(t=X^{o(1)}\);
2. use growing token arity with \(X^{1-o(1)}\) population without large reservoir;
3. use genuinely many-to-many physical operation not reducible to one reservoir times one
   fixed-arity token;
4. cancel before ordinary-integer column projection and prove source-faithful descent which does
   not reintroduce (4).

Option 1 is no longer a joint mass/capacity problem.  Exact finite truncation inequality proves a
fixed proportion of elementary-symmetric harmonic mass survives.  Its sole remaining obstruction
is local structured-token density versus inverse \(\omega=s\) layer incidence, with factorial
constants sharp enough for unit physical columns.

## 8. Status

[PROVED HERE] [NOVELTY UNVERIFIED] for full-allocation band. Proof uses finite mass conservation,
fixed-order global almost-prime upper bound, reciprocal-prime Mertens law, and displacement
scaling. It does not use RH, computation, unique decoding, structured-token lower bounds, or any
unproved Route E premise.  Child theorem
`route-e-product-truncated-reservoir-harmonic-mass-law.md` proves full-allocation no-go does not
extend to harmonically weighted product truncation; it does not overturn physical-capacity law.
