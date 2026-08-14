# Gate-walk Green--Bellman tropicalization law

- **ID:** `gate-walk-green-bellman-tropicalization-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / external circuit calibration / positive-linearization no-go
- **Parent:** `../3-formalized/static-orbit-net-no-go-and-circuit-bellman-law.md`
- **Status:** `[PAPER-PROVED] [LEAN-CERTIFIED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-09

## Public sentence

Approximate circuit complexity is the zero-fugacity exponent of a killed random walk on the local
gate graph.  At finite fugacity this gives an explicit robust Bellman lower certificate, but every
positive linearization pays an exact circuit-entropy price; avoiding dimension-scale replicas
therefore requires the genuinely nonlinear zero-temperature transfer, not another moment bound.

## Setup

Let `(X,d)` be a metric space on which a finite gate dictionary `G` of cardinality `M>=2` acts by
isometries.  Fix a seed `chi in X`.  For a word

\[
 w=(g_1,\ldots,g_\ell)\in G^\ell,
 \qquad W_w=g_\ell\cdots g_1,                                  \tag{1}
\]

define robust word complexity

\[
 C_\epsilon(v)=\inf\{\ell\geq0:
      d(W_w\chi,v)\leq\epsilon\text{ for some }w\in G^\ell\}. \tag{2}
\]

The value is `infinity` if no such word exists.  Put

\[
 A_\epsilon(v)=\mathbf1_{\{d(\chi,v)\leq\epsilon\}},
 \qquad
 (Pf)(v)={1\over M}\sum_{g\in G}f(g^{-1}v).                    \tag{3}
\]

The operator `P` is defined only from the one-gate action.  Induction gives

\[
 P^\ell A_\epsilon(v)
 ={1\over M^\ell}\#\{w\in G^\ell:d(W_w\chi,v)\leq\epsilon\}. \tag{4}
\]

For `0<a<1`, define the normalized killed gate-walk Green function

\[
 \mathcal G_{a,\epsilon}(v)
  =(1-a)\sum_{\ell\geq0}a^\ell P^\ell A_\epsilon(v)
  =(1-a)(I-aP)^{-1}A_\epsilon(v).                              \tag{5}
\]

Equivalently, choose a geometric word length `L` with
`Pr{L=ell}=(1-a)a^ell`, then choose a uniform `L`-gate word.  Equation `(5)` is exactly the
probability that its endpoint lies in the `epsilon`-ball about `v`.

## Theorem A -- exact Green sandwich

If `c=C_epsilon(v)<infinity`, then

\[
 \boxed{
 (1-a)\left({a\over M}\right)^c
 \leq \mathcal G_{a,\epsilon}(v)
 \leq a^c .}                                                   \tag{6}
\]

If `C_epsilon(v)=infinity`, then `mathcal G_(a,epsilon)(v)=0`.

Consequently every finite complexity obeys the two-sided estimate

\[
 \boxed{
 {\log(1-a)-\log\mathcal G_{a,\epsilon}(v)\over\log(M/a)}
 \leq C_\epsilon(v)
 \leq{-\log\mathcal G_{a,\epsilon}(v)\over\log(1/a)}.}        \tag{7}
\]

### Proof

No word of length below `c` reaches the target ball, so the corresponding terms in `(5)` vanish.
At least one length-`c` word reaches it, and that word has uniform probability `M^(-c)`.  Keeping
only this term gives the lower bound in `(6)`.  Bounding every remaining word probability by one
gives

\[
 \mathcal G_{a,\epsilon}(v)
 \leq(1-a)\sum_{\ell\geq c}a^\ell=a^c,
\]

which is the upper bound.  Taking logarithms yields `(7)`.  If the complexity is infinite, every
term in `(5)` vanishes.

## Theorem B -- complexity is a tropical Green exponent

For every finite `C_epsilon(v)`,

\[
 \boxed{
 C_\epsilon(v)
 =\lim_{a\downarrow0}
 { -\log\mathcal G_{a,\epsilon}(v)\over\log(1/a)}.}            \tag{8}
\]

The same limit is `infinity` for an unreachable target.  Thus minimum circuit length is not merely
analogous to a gate-graph free energy: it is exactly the zero-fugacity valuation of the local
Markov resolvent `(5)`.

### Proof

Divide the logarithmic form of `(6)` by `log(1/a)`.  Both outer expressions converge to `c`,
because `log M/log(1/a)` and `log(1-a)/log(1/a)` tend to zero.  The unreachable case follows from
`mathcal G=0`.

## Theorem C -- an external robust Bellman calibration

The hard target in `(5)` is discontinuous.  For `beta>0` replace it by

\[
 K_{\beta,\epsilon}(x,v)
 =\exp\{-\beta(d(x,v)-\epsilon)_+\}                            \tag{9}
\]

and define

\[
 \widetilde{\mathcal G}_{a,\beta,\epsilon}(v)
 =(1-a)\sum_{\ell\geq0}a^\ell
 {1\over M^\ell}\sum_{w\in G^\ell}
 K_{\beta,\epsilon}(W_w\chi,v).                              \tag{10}
\]

Then

\[
 \Phi_{a,\beta,\epsilon}(v)
 ={\log(1-a)-
    \log\widetilde{\mathcal G}_{a,\beta,\epsilon}(v)
   \over\log(M/a)}                                             \tag{11}
\]

has all three properties

\[
 \boxed{
 \Phi_{a,\beta,\epsilon}(v)\leq C_\epsilon(v),}               \tag{12}
\]

\[
 \boxed{
 \Phi_{a,\beta,\epsilon}(gv)
 \leq\Phi_{a,\beta,\epsilon}(v)+1
 \quad(g\in G),}                                               \tag{13}
\]

and

\[
 \boxed{
 |\Phi_{a,\beta,\epsilon}(v)-
   \Phi_{a,\beta,\epsilon}(v')|
 \leq {\beta\over\log(M/a)}d(v,v').}                         \tag{14}
\]

Unlike the exact-penalty distance to a circuit set, `(10)` is a formula in the one-step gate
transfer operator and a fixed radial kernel.  It neither minimizes over circuit words nor invokes
circuit complexity in its definition.

### Proof

If a length-`c` word reaches the target ball, its kernel value in `(10)` is one.  Therefore

\[
 \widetilde{\mathcal G}_{a,\beta,\epsilon}(v)
 \geq(1-a)(a/M)^c,
\]

and rearrangement proves `(12)`.

For every word `w`, appending `g` gives a word with one extra gate and

\[
 d(gW_w\chi,gv)=d(W_w\chi,v).
\]

Keeping these appended words inside `(10)` gives the gate Harnack inequality

\[
 \widetilde{\mathcal G}_{a,\beta,\epsilon}(gv)
 \geq {a\over M}
       \widetilde{\mathcal G}_{a,\beta,\epsilon}(v),           \tag{15}
\]

which is equivalent to `(13)`.

The map `v mapsto (d(x,v)-epsilon)_+` is one-Lipschitz.  Hence every summand satisfies

\[
 e^{-\beta d(v,v')}K(x,v')
 \leq K(x,v)
 \leq e^{\beta d(v,v')}K(x,v').                               \tag{16}
\]

Positive summation preserves `(16)`.  Taking logarithms and dividing by `log(M/a)` proves `(14)`.

## Theorem D -- one scalar quenched estimate controls the complete circuit union

Let `V` be any random endpoint and let `R` be any measurable retained event, for example the
complement of one target-independent return/fast-forwardable filtration.  For every integer
`s>=0`,

\[
 \boxed{
 \Pr\{R\text{ and }C_\epsilon(V)\leq s\}
 \leq
 {\mathbb E[\mathbf1_R
   \widetilde{\mathcal G}_{a,\beta,\epsilon}(V)]
  \over(1-a)(a/M)^s}.}                                        \tag{17}
\]

### Proof

On `R intersect {C_epsilon(V)<=s}`, the proof of `(12)` gives

\[
 \widetilde{\mathcal G}_{a,\beta,\epsilon}(V)
 \geq(1-a)(a/M)^{C_\epsilon(V)}
 \geq(1-a)(a/M)^s.
\]

Markov's inequality proves `(17)`.

Equation `(17)` replaces an adaptive union over all shallow targets by one collision probability
between two physical processes: the static Hamiltonian endpoint and an independently, geometrically
killed local random circuit.  Circuit preparation structure is retained by the transfer operator.

## Theorem E -- exact entropy--temperature price of positive linearization

Let `0<=K_w(v)<=1` be any endpoint reporter at a fixed word length `ell`, and for `1<=p<infinity`
put

\[
 Q_{\ell,p}(v)
 =\left({1\over M^\ell}\sum_{w\in G^\ell}K_w(v)^p\right)^{1/p},
 \qquad
 Q_{\ell,\infty}(v)=\max_{w\in G^\ell}K_w(v).                 \tag{18}
\]

Then

\[
 \boxed{
 M^{-\ell/p}Q_{\ell,\infty}(v)
 \leq Q_{\ell,p}(v)
 \leq Q_{\ell,\infty}(v).}                                  \tag{19}
\]

Both constants are sharp.  In particular, a worst-case multiplicative approximation

\[
 Q_{\ell,p}\geq e^{-\eta}Q_{\ell,\infty}                     \tag{20}
\]

requires

\[
 \boxed{p\geq{\ell\log M\over\eta}.}                         \tag{21}
\]

If a degree-`r` positive replica reporter is linearized by the `p`-th power in `(18)`, its linear
moment order is `rp`.  Preserving the max within its natural error `e^{-kappa r}` therefore forces

\[
 rp\geq {\ell\log M\over\kappa}.                              \tag{22}
\]

At Brown depth `ell=Theta(D/log M)`, every such positive linearization has total replica order
`Omega(D)`.  Low replica order remains sufficient for the nonlinear complete maximum; it cannot
remain low after replacing that maximum by a positive Markov average.

### Proof

The normalized `L^p` norm of `M^ell` nonnegative numbers lies between their maximum divided by
`(M^ell)^(1/p)` and their maximum.  A vector with one entry one and all remaining entries zero
saturates the lower constant; a constant vector saturates the upper constant.  Rearranging the
sharp lower constant gives `(21)`.  Substituting `eta=kappa r` gives `(22)`.

## Conjecturing protocol and hostile attack

### C0 -- averaging circuit paths necessarily loses the existence of one shortcut

**Verdict:** `[FALSE AFTER GEOMETRIC KILLING]`.

One shortcut of length `c` has exactly known path weight `(1-a)(a/M)^c`.  This proves the lower
half of `(6)` and the complete-union probability law `(17)` without target enumeration.

### C1 -- the killed Green function is only another circular definition of complexity

**Verdict:** `[FALSE AT FINITE FUGACITY; TRUE IN THE TROPICAL LIMIT]`.

At finite `a`, equations `(5)` and `(10)` are resolvents of the one-gate Markov operator.  They are
external Bellman subsolutions and can in principle be attacked by transfer-operator, replica, or
quenched free-energy methods.  Their zero-fugacity valuation recovers complexity exactly by `(8)`;
that limit is a characterization, not by itself an estimate.

### C2 -- finite-temperature positive transfer retains the low-replica advantage

**Verdict:** `[FALSIFIED SHARPLY]`.

Equation `(22)` shows that a positive linear transfer pays the complete word entropy.  At Brown
depth it recreates dimension-scale replica order.  The earlier low-replica correction remains
valid only because it takes the complete circuit maximum before scalarization.

### Strongest positive survivor

The external Green calibration `(11)` closes the representation gap left by the bare Bellman law,
and `(19)--(22)` classify exactly what is lost by linearizing it.  The genuine dynamical core is a
zero-temperature, quenched gate-transfer estimate.  More Jacobians, positive moments, or ordinary
annealed gate-walk mixing cannot remove the entropy price.

A later hostile attack exposed a second distinction.  Raw endpoint Green mass is not pure
preparation mass: the entrance--return law in
`first-entrance-gate-renewal-prefix-law.md` factors it into first entrance followed by a return
resolvent.  The same child proves
`(1-a) F_(a,epsilon) <= G_(a,epsilon) <= F_(a,epsilon)`, so their surprisals
differ by at most `-log(1-a)`.  The Green theorems above therefore remain quantitatively sharp at
fixed fugacity.  First entrance is the loop-free interpretation and capacity coordinate, not an
asymptotically stronger Brown estimate.

## Exact next move

For each geometric Brown-skeleton time `T_j` and target depth `s_j`, let
`F_(a,epsilon)(v)` be discounted first-entrance mass of the uniform inverse-gate word process into
the robust target tube.  Prove after one common return and shortcut-carrier excision the loop-free
estimate

\[
 \mathbb E_\theta\!\left[
  \mathbf1_{R_{n,j}^c}
  \mathcal F_{a,\epsilon}
   (e^{-iT_jH(\theta)}\chi_n)\right]
 \leq\delta_j(a/M_n)^{s_j},                                  \tag{23}
\]

or a corresponding quenched first-entrance free-energy bound.  The first-entrance complete-union
law and the geometric-skeleton theorem would then give the continuous lower ramp.

The first-entrance child sharpens the quenched option: `-log((1-a)F_(a,epsilon)(v))` is exactly the
minimum KL cost of conditioning the local gate prior to a **first-hit** witness.  First-hit words
are prefix-free, and fixed-fugacity surprisal is bilipschitz-equivalent to robust circuit complexity.
Thus `(23)` is an annealed sufficient condition; a quenched lower tail for the same first-entry
surprisal is equivalent up to explicit constants.

For a finite reversible inverse-gate model, the further child
`first-entrance-gate-capacity-discrepancy-law.md` identifies the expectation in `(23)` with gate
capacity plus one signed directional discrepancy.  Global resolvent convergence is the wrong
target because it lower-bounds chi-squared distance and conflicts with permanent non-Haar locality.
The exact surviving target is the directional pairing with the seed-tube equilibrium potential.

## Boundary and novelty audit

1. **No Brown estimate yet.**  Theorems A--E solve the representation and entropy accounting, not
   `(23)`.
2. **Exponential precision is load-bearing.**  At `s=Theta(D/log M)`, the denominator in `(17)` is
   `exp(-Theta(D))`; an `exp(-poly(n))` estimate is insufficient.
3. **Soft leakage matters.**  Fixed `beta` leaves a large background in `(10)`.  Brown-scale use
   needs `beta` growing with dimension or the hard target `(5)`.
4. **Recurrence is compatible.**  First-entrance mass equals one and its surprisal equals zero when
   the target tube contains the seed.  Every decay theorem must retain explicit return excision.
5. **Gate model is finite.**  Continuous gate controls, free ancillas, measurement and
   postselection require a measure-valued transfer operator and their stated operational costs.
6. **Priority.**  Shortest-path generating functions, Markov resolvents, `L^p`--`L^infinity`
   comparison and tropical limits are standard separately.  The direct circuit-complexity
   calibration, complete-union quenched criterion, and Brown-replica entropy classification were
   not found in the targeted external search.  External priority remains unverified, so no novelty
   claim is made.
7. **Formalization.**  Every theorem of this card is Lean-certified; see the certificate below.
   The first-entrance and capacity children are certified in their own cards.

## Lean certificate

The whole card is formalized unconditionally.  The killed Green function is realized as a weighted
sum over gate words rather than over lengths, so the transfer-operator definition and the word
count are connected by an explicit iterate identity; the soft-target calibration, the gate Harnack
inequality and the complete-union bound are then word-level statements about the same sum.

Modules:

- `GaloisForLFunctions.HTGeometry.GateWalkGreenBellmanTropicalization` (pre-existing: Theorem A in
  the `approxComplexity` encoding)
- `GaloisForLFunctions.RHTower.GateWalkGreenBellman`
- `GaloisForLFunctions.HTGeometry.StaticCircuitEnsembleZeroTemperature`

| Card statement | Lean declaration |
|---|---|
| `(3)` one-gate transfer operator | `gateAvgOp`, `backAct` |
| `(4)` iterate counts reaching words | `gateAvgOp_iterate`, `reachingWordCount` |
| `(5)` killed Green function | `gateGreen`, `gateGreenReal` |
| Thm A `(6)` | `gateGreen_ge`, `gateGreen_le`, `gateGreenReal_sandwich`, and `gateWalkGreen_sandwich` |
| Thm A unreachable case | `gateGreen_eq_zero_of_unreachable` |
| Thm A `(7)` | `complexity_log_sandwich` |
| Thm B `(8)` | `tendsto_neg_log_gateGreenReal` |
| `(9)` radial soft kernel | `softKernel`, `softKernel_le_one`, `softKernel_of_mem_tube` |
| `(10)` soft Green function | `softGreen`, `softGreenReal`, `softGreen_le_one` |
| `(11)` calibration | `bellmanCalibration` |
| Thm C `(12)` | `bellmanCalibration_le` |
| Thm C `(13)`, `(15)` | `bellmanCalibration_gate_step`, `softGreen_gate_harnack`, `softGreenReal_gate_harnack` |
| Thm C `(14)`, `(16)` | `abs_bellmanCalibration_sub_le`, `softKernel_le_mul`, `softGreen_le_mul` |
| Thm D `(17)` | `measure_reachable_le_lintegral` |
| Thm E `(18)` | `finiteDictionaryLpNorm`, `finiteDictionaryMax` |
| Thm E `(19)` | `finiteDictionaryLpNorm_le`, `le_finiteDictionaryLpNorm` |
| Thm E sharpness | `finiteDictionaryLpNorm_oneHot` |
| Thm E `(20)`--`(21)` | `log_card_div_le_of_exp_le`, `mul_log_div_le_of_exp_le` |
| Thm E `(22)` | `log_card_div_le_mul_of_exp_le` |

Every listed declaration reports exactly `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-08-09 -- Conjecture loop produced the killed gate-walk Green calibration, proved exact
  tropical recovery and robust Bellman/Harnack laws, then falsified finite-temperature
  low-replica closure by the sharp entropy--temperature theorem.
