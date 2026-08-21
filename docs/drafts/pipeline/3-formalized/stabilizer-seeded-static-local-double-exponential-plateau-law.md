# Stabilizer-seeded static-local dynamics has doubly-exponential hard plateaux

- **ID:** `stabilizer-seeded-static-local-double-exponential-plateau-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / pathwise static-local complexity plateau / recurrence lower bound
- **Parents:** `fixed-shell-angular-dephasing-static-local-plateau-law.md`,
  `local-clifford-return-excised-phase-incidence-law.md`
- **Status:** `[FORMALIZED] [FRONTIER ADVANCE] [NOVELTY SEPARATION PASSED]`
- **Date:** 2026-08-08

## Public sentence

A fixed, ordinary nearest-neighbour Hamiltonian can turn an efficiently prepared state into an
exponentially complex state and keep that same state complex continuously for a doubly-exponential
time before it recurs, while the dynamics remains efficiently distinguishable from Haar randomness
throughout.

The plateau onset is finite but non-effective.  Initial linear growth is not proved.

## Frontier crossed

The fixed-shell angular theorem gives high complexity at each sufficiently late common time, but
its probability is evaluated separately at each time.  Recurrence forbids replacing those
one-time statements by one common Hamiltonian set which is hard forever.  The unresolved question
is whether one draw of a time-independent local Hamiltonian can remain hard on a whole long time
interval.

For a fixed product input, the available spectral-collision estimate is only `(2/3)^n`, giving
complexity and logarithmic plateau duration on the `(3/2)^n` scale.  The new step is to use a
globally distributed but efficiently preparable stabilizer seed.  Stabilizer states form an exact
projective two-design, so their mean collision against **every** eigenbasis is exactly
`2/(2^n+1)`.  This restores the full Hilbert-dimension scale without Haar-random input states or
eigenvectors.

The bad collision set is a property of the Hamiltonian--seed pair and is removed once.  It is not
paid again at each time.  The remaining one-time shortcut probability is exponentially small in
`2^n`; a time grid of exponentially many points therefore survives a union bound.  A uniform
operator-speed estimate fills every gap in the grid.  This converts an annealed fixed-time plateau
into a same-pair, continuous, doubly-exponential plateau block.

## Setup

Fix `n>=2`, put

\[
 D=2^n,\qquad m=3n+9(n-1)=12n-9.                                  \tag{1}
\]

Let `P_1,...,P_m` be all one-site Pauli matrices and all nine two-site Pauli orientations on every
edge of the open path.  With normalized Pauli convention

\[
 D^{-1}\operatorname{Tr}(P_aP_b)=\delta_{ab},
\]

define, for `theta` on the coefficient unit sphere,

\[
 H(\theta)=\sum_{a=1}^m\theta_aP_a,
 \qquad D^{-1}\operatorname{Tr}H(\theta)^2=1.                      \tag{2}
\]

This normalization fixes one common total interaction rate.  If physical convention instead
requires order-one root-mean-square local coefficients, replace every member by
`H_phys(theta)=sqrt(m) H(theta)`.  This is one common deterministic rescaling: every statement
below is unchanged after dividing all displayed times and interval lengths by `sqrt(m)`.  In
particular, the plateau duration remains doubly exponential, with only one additional polynomial
factor.

Let `sigma` be uniform spherical measure.  Let `Stab_n` be the finite set of normalized `n`-qubit
stabilizer states with uniform measure `nu_n`.  Every member of `Stab_n` is preparable by a
polynomial-size Clifford circuit; write `b_n=O(n^2)` for any uniform preparation bound.

Fix a finite one- and two-qubit gate dictionary containing a standard Clifford generating set, or
more generally equipped with a proved polynomial compiler for stabilizer states.  After locations
and padding are included, let `M_n>=2` bound the number of choices at each word position.  Let
`C_epsilon(psi)` denote ancilla-free state complexity from the standard product reference in
pure-state trace distance.  With the literal Clifford alphabet, every stabilizer has exact
preparation depth `b_n=O(n^2)` in this same complexity model.

Choose two error radii

\[
 0<\epsilon_-<\epsilon_+<1,
 \qquad a_+=1-\epsilon_+^2,
 \qquad \gamma=\epsilon_+-\epsilon_->0.                            \tag{3}
\]

## Universal law exposed -- collision controls height and lifetime

The stabilizer theorem is one sharp instance of a more general law.  Let a fixed-shell ensemble
obey angular dephasing, let `G` be any time-independent Hamiltonian--seed event on which

\[
 C_H(\chi)\le c,
\]

and put

\[
 r_c=\left\lfloor{(1-\epsilon_+^2)^2\over32c}\right\rfloor.
\]

The same proof below certifies, up to the displayed integer rounding,

\[
 \boxed{
 \text{plateau depth}\ \ge \Omega\!\left({1\over c\log M_n}\right),
 \qquad
 \log_2(\text{continuous plateau lifetime})
 \ge \Omega\!\left({1\over c}\right).}                            \tag{CL}
\]

More exactly, the complete depth-`s` shortcut probability on `G` is at most `2^(-r_c/2)` when
`s+1<=r_c log(2)/(2 log M_n)`, and one fixed pair remains hard continuously on a block containing
up to `2^(r_c/4)` Lipschitz grid points, apart from `Pr(G^c)` and an arbitrarily small angular
transfer error.

Thus reciprocal spectral collision is simultaneously the circuit-capacity scale and the
logarithmic lifetime scale.  Product seeds, stabilizer seeds and equal-weight Choi seeds are not
three unrelated constructions: their different plateau laws are the shadows of `(CL)`.  The
two-design identity below supplies `c=2L/(D+1)` for an ordinary `n`-qubit state without doubling
the system.

## Theorem A -- exact two-design collision law

For every Hermitian `D`-level Hamiltonian with any orthonormal eigenbasis `e_1,...,e_D`, put

\[
 C_H(\chi)=\sum_{j=1}^D|\langle e_j,\chi\rangle|^4.                \tag{4}
\]

Then

\[
 \boxed{
 {1\over|\mathrm{Stab}_n|}\sum_{\chi\in\mathrm{Stab}_n}C_H(\chi)
 ={2\over D+1}.}                                                   \tag{5}
\]

Consequently, for every `L>=1`, the fixed pair ensemble obeys

\[
 \Pr_{\theta,\chi}
 \left\{C_{H(\theta)}(\chi)>{2L\over D+1}\right\}
 \le {1\over L}.                                                   \tag{6}
\]

### Proof

The stabilizer two-design identity is

\[
 {1\over|\mathrm{Stab}_n|}\sum_\chi
 |\chi\rangle\langle\chi|^{\otimes2}
 ={I+F\over D(D+1)}.                                               \tag{7}
\]

Contracting `(7)` against `|e_j><e_j|^(tensor 2)` gives

\[
 {1\over|\mathrm{Stab}_n|}\sum_\chi
 |\langle e_j,\chi\rangle|^4={2\over D(D+1)}.                     \tag{8}
\]

Sum `(8)` over the `D` eigenvectors to prove `(5)`.  Averaging also over `theta` changes nothing;
Markov proves `(6)`.  No property of the eigenbasis, spectrum or Hamiltonian ensemble is used in
this step.

The same proof works for every finite exact projective two-design whose members have a supplied
preparation bound.  Stabilizers are the canonical efficient instance.

## Theorem B -- all-late common-time near-maximal state complexity

For `L>=1`, define

\[
 r=r_{n,L}:=
 \left\lfloor {a_+^2(D+1)\over64L}\right\rfloor                  \tag{9}
\]

and assume `r>=1`.  If

\[
 s+1\le {r\log2\over2\log M_n},                                  \tag{10}
\]

then

\[
 \boxed{
 \limsup_{t\to\infty}
 \Pr_{\theta,\chi}
 \{C_{\epsilon_+}(e^{-itH(\theta)}\chi)\le s\}
 \le {1\over L}+2^{-r/2}.}                                       \tag{11}
\]

More sharply, if

\[
 G_L=\{(\theta,\chi):C_{H(\theta)}(\chi)\le2L/(D+1)\},           \tag{12}
\]

then

\[
 \boxed{
 \limsup_{t\to\infty}
 \Pr_{\theta,\chi}
 \bigl(G_L\cap
 \{C_{\epsilon_+}(e^{-itH(\theta)}\chi)\le s\}\bigr)
 \le2^{-r/2}.}                                                    \tag{13}
\]

Equation `(13)`, rather than the coarser `(11)`, is load-bearing for the pathwise theorem: the
probability `1/L` is paid once for the pair, not once per sampled time.

### Proof

Fix one pair `(theta,chi)` in `G_L`, outside the null spectral discriminant.  Let

\[
 p_j=|\langle e_j(\theta),\chi\rangle|^2,
 \qquad \sum_jp_j^2=C_{H(\theta)}(\chi)\le{2L\over D+1}.           \tag{14}
\]

On the completed spectral phase torus, the heavy-sector replica-incidence theorem bounds capture
by all circuit outputs of length at most `s` by

\[
 M_n^{s+1}r!
 \left({16C_{H(\theta)}(\chi)\over a_+^2}\right)^r
 \le
 M_n^{s+1}r!
 \left({32L\over a_+^2(D+1)}\right)^r.                            \tag{15}
\]

By `(9)`, `r!<=r^r` makes the last expression at most

\[
 M_n^{s+1}2^{-r}.                                                  \tag{16}
\]

Condition `(10)` makes `(16)` at most `2^(-r/2)`.

The fixed-shell spectral theorem proves that no nonzero integer projective spectral action is
constant on an open coefficient-sphere patch.  Coarea and Riemann--Lebesgue therefore give

\[
 (\theta,t\omega(\theta))_\#\sigma
 \Longrightarrow\sigma\otimes m_{\mathbb T^{D-1}}.               \tag{17}
\]

Adjoining the independent finite stabilizer variable preserves `(17)`.  The low-circuit event is
a finite union of closed fidelity superlevel sets.  Intersect it with the closed collision
sublevel `(12)`, exhaust the null discriminant by compact simple-spectrum charts, and apply the
Portmanteau upper bound.  Integrating `(15)--(16)` proves `(13)`.  Equation `(6)` then proves
`(11)`.

No Haar-random eigenbasis, unitary design, stochastic drive, minimum gap, random time or random
interaction strength occurs.

## Theorem C -- one fixed pair stays hard continuously for doubly-exponential time

For a desired plateau length `W>0`, put

\[
 N_W=\left\lceil{W\sqrt m\over\gamma}\right\rceil+1.              \tag{18}
\]

For every `q>0` there is a finite, generally non-effective time
`T=T(n,L,epsilon_-,epsilon_+,s,W,q)` such that **every** interval origin `A>=T` obeys

\[
 \boxed{
 \Pr_{\theta,\chi}
 \left\{
   \forall t\in[A,A+W],\quad
   C_{\epsilon_-}(e^{-itH(\theta)}\chi)>s
 \right\}
 \ge1-{1\over L}-N_W2^{-r/2}-q.}                                  \tag{19}
\]

In particular, if

\[
 N_W\le2^{r/4},                                                    \tag{20}
\]

then

\[
 \boxed{
 \Pr_{\theta,\chi}
 \left\{
   \forall t\in[A,A+W],\quad C_{\epsilon_-}(e^{-itH(\theta)}\chi)>s
 \right\}
 \ge1-{1\over L}-2^{-r/4}-q.}                                    \tag{21}
\]

Thus one may take, up to harmless endpoint rounding,

\[
 \boxed{
 W={\gamma\over\sqrt{12n-9}}
       \left(2^{r/4}-2\right).}                                   \tag{22}
\]

For a standard local finite gate alphabet, `log M_n=O(log n)`.  Hence:

- fixed `L` gives depth `Omega(2^n/log n)` for continuous duration
  `2^(Omega(2^n))`, with fixed positive success probability;
- any `L_n -> infinity` gives success probability `1-o(1)`, depth
  `Omega(2^n/(L_n log n))`, and duration `2^(Omega(2^n/L_n))`;
- for example `L_n=log n` gives a high-probability plateau of depth
  `Omega(2^n/(log n)^2)` lasting `2^(Omega(2^n/log n))`.

These durations are doubly exponential in the physical qubit number.

### Proof

Every Pauli matrix in `(2)` has operator norm one.  Cauchy--Schwarz on the unit coefficient
sphere gives the uniform speed bound

\[
 \|H(\theta)\|_{\mathrm{op}}
 \le\sum_a|\theta_a|\le\sqrt m.                                  \tag{23}
\]

For pure Schrödinger evolution,

\[
 \Delta(e^{-itH}\chi,e^{-iuH}\chi)
 \le\|(e^{-i(t-u)H}-I)\chi\|
 \le\|H\|_{\mathrm{op}}|t-u|
 \le\sqrt m|t-u|.                                                 \tag{24}
\]

Partition `[A,A+W]` into `N_W` grid points with mesh at most `gamma/sqrt(m)`.  If an intermediate
time `t` has an `epsilon_-`-approximation by a circuit word of length at most `s`, the left grid
point `t_j` obeys, by `(24)` and the triangle inequality,

\[
 C_{\epsilon_+}(e^{-it_jH}\chi)\le s.                             \tag{25}
\]

Therefore hardness at radius `epsilon_+` on all grid points implies hardness at radius
`epsilon_-` throughout the continuum.

By `(13)`, for any `delta>0` there is one `T_delta` such that every `t>=T_delta` satisfies

\[
 \Pr\bigl(G_L\cap\{C_{\epsilon_+}(e^{-itH}\chi)\le s\}\bigr)
 \le2^{-r/2}+\delta.                                               \tag{26}
\]

Take `delta=q/N_W`.  A finite union bound over the grid, followed by the one-time estimate
`Pr(G_L^c)<=1/L`, proves `(19)`.  Equations `(20)--(22)` are immediate.

The same `(theta,chi)` is used at every time.  No temporal independence is assumed.

## Corollary -- a genuine low--plateau--recurrence trajectory

For every stabilizer seed, `C_0(chi)<=b_n=O(n^2)`.  For all sufficiently large `n`, the depth `s`
in `(10)` is much larger than `b_n`.

For each fixed stabilizer `chi`, the set of `theta` for which `chi` has nonzero overlap with every
eigenvector is conull.  To see that the relevant Krylov determinant is not the zero polynomial,
choose local one-qubit bases in which all `2^n` product-basis amplitudes of `chi` are nonzero; such
bases exist because each amplitude is a nonzero analytic function of the local bases and there are
only finitely many amplitudes.  The one-local Hamiltonian

\[
 H_0=\sum_{j=0}^{n-1}3^j U_jZU_j^*                               \tag{27}
\]

has distinct balanced-ternary energies and makes `chi` cyclic.  It lies in the allowed local
space.  Since `Stab_n` is finite, all stabilizer seeds are cyclic simultaneously outside one null
set.

The existing path-local spectral theorem also gives maximal projective rational rank outside a
null set.  Kronecker--Weyl then makes every such orbit recur arbitrarily close to its initial seed
after every time.

Consequently, on the event in `(19)` and outside a null set, one and the same trajectory has:

1. polynomial initial complexity at `t=0`;
2. complexity above `s` at every instant of `[A,A+W]`;
3. a later recurrence to complexity at most `b_n` at error `epsilon_-`.

In particular, the first `epsilon_-` recurrence after the start of the hard block is later than
`A+W`.  Equation `(22)` is therefore a doubly-exponential lower bound on the post-plateau
recurrence gap for a high-probability set of ordinary static-local Hamiltonian--seed pairs.

The bounded-weight Pauli locality witness from the existing corpus distinguishes the same
`e^{-itH(theta)}` from the Haar benchmark with two queries at every real time.  Hence maximal-scale
state complexity throughout the plateau does not erase the observable fact that the generator is
local.

## Conjecturing protocol

### C0 -- space--time coarea flux is the missing invariant

**Verdict:** `[FALSIFIED AS SUFFICIENT]`.

Raw flux counts an easy eigenstate tube for its entire lifetime.  Quotienting that longitudinal
sheet removes the physical fibre multiplicity which the incidence law was designed to retain.

**Positive survivor:** remove persistent spectral-collision carriers once, then control transverse
shortcut crossings on the remaining fixed pair set.

### C1 -- the product input already gives a Brown-scale plateau block

**Verdict:** `[TRUE BUT SUBOPTIMAL]`.

The product-local-Clifford collision law gives only `C_H<=L(2/3)^n`, hence replica order and
logarithmic duration on the `(3/2)^n` scale.

**Positive survivor:** replace the product seed by an efficiently preparable global two-design
seed.

### C2 -- a Haar-random seed is needed for collision `O(1/D)`

**Verdict:** `[FALSIFIED]`.

The exact stabilizer two-design identity `(7)` gives the same fourth moment, while every seed has a
polynomial Clifford preparation.

### C3 -- the `1/L` collision tail must be paid at every grid time

**Verdict:** `[FALSE]`.

Collision depends only on the fixed Hamiltonian--seed pair.  Restricting to `G_L` before angular
transfer proves `(13)`; `G_L^c` is charged once after the complete temporal union.

### C4 -- fixed-time annealed hardness cannot yield a pathwise plateau because of recurrence

**Verdict:** `[FALSE AS A FINITE-BLOCK CLAIM; TRUE FOR AN INFINITE TAIL]`.

Recurrence forbids one pair set hard for all late time.  It does not forbid a common finite block.
The off-return shortcut probability is `exp(-Omega(D/L))`, so a grid of
`exp(Omega(D/L))` times survives; temporal stability fills the grid gaps.

### C5 -- one needs independence between times

**Verdict:** `[FALSIFIED]`.

The proof uses only marginal all-late angular dephasing, one union bound, and deterministic
Lipschitz motion.  Static temporal correlations are unrestricted.

### C6 -- the theorem proves the full Brown--Susskind law

**Verdict:** `[FALSE]`.

It closes a near-maximal plateau, its continuous doubly-exponential duration, a recurrence-gap
lower bound, later recurrence, and permanent non-Haar locality.  It does not quantify the first
plateau onset or prove a pointwise linear ramp from time zero.  Those remain the exact open core.

## Hostile review

1. **Non-effective onset remains.** Riemann--Lebesgue supplies a finite common `T` but no bound in
   `n`.  Equation `(22)` quantifies plateau duration after onset, not the absolute first saturation
   time.
2. **No linear growth theorem.** Polynomial initial complexity, a later hard block, and eventual
   recurrence prove qualitative low--plateau--low ordering, not `C(t)=Theta(t)` before saturation.
3. **Random efficient seed.** Probability is over the fixed Hamiltonian and one independently
   sampled stabilizer seed.  This is not the same as a fixed product input.  Averaging `(5)` also
   proves existence of one fixed stabilizer seed per `n` with the same mean collision bound, but no
   explicit uniform selector is claimed.
4. **Disordered fixed-shell family.** Translation-invariant and deterministic chains are not
   covered.  Every Hamiltonian is nevertheless an ordinary fixed-strength, time-independent,
   nearest-neighbour two-local spin Hamiltonian.  Rescaling by `sqrt(m)` gives exactly unit
   root-mean-square local coefficients and changes all times only polynomially.
5. **Finite gate dictionary.** Continuous adjustable gates or ancilla disposal require a proved
   metric net and its entropy.  No such extension is silently claimed.
6. **State rather than full unitary complexity.** The theorem concerns an ordinary `n`-qubit state
   orbit, avoiding the doubled-system Choi semantic loss.  It does not prove `Omega(D^2)` unitary
   complexity.
7. **Probability--depth tradeoff is explicit.** Fixed `L` reaches the Haar-volume state scale up to
   `log n` but gives fixed success probability.  Probability tending to one costs the freely
   visible factor `L_n`.
8. **No fresh-noise surrogate.** Hamiltonian and seed are drawn once.  No gate, coupling, Brownian
   increment or measurement is refreshed during the interval.
9. **Blockwise, not one common infinite-tail set.** For every chosen late origin `A`, `(19)` gives
   high probability over pairs which remain hard on that entire block.  The successful pair set
   may depend on `A`; no one conull pair set is hard on all late blocks.  Recurrence forbids that
   stronger quantifier.
10. **Formal publication gate remains closed.** Per current refactor instruction, no Lean source was
   written or built.  This card is Stage 2 and cannot yet authorize a final-paper claim.

## External separation audit

- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove growth, saturation and recurrence for random
  circuits and stochastic local Hamiltonian evolution.  Their Hamiltonian noise is refreshed; they
  explicitly separate the static time-independent problem:
  <https://arxiv.org/abs/2205.09734>.
- Kotowski--Oszmaniec--Horodecki prove extremal complexity jumps for GUE and Haar-random-eigenbasis
  Hamiltonians.  Their ensembles are nonlocal, eigenbasis randomness is load-bearing, and recurrence
  is listed as open: <https://arxiv.org/abs/2303.17538>.
- Kueng--Gross prove that all qubit stabilizer states form a projective three-design, hence the
  two-design identity `(7)`: <https://arxiv.org/abs/1510.02767>.
- Dehaene--De Moor give efficient one- and two-qubit synthesis of Clifford operations:
  <https://arxiv.org/abs/quant-ph/0304125>.
- Kra--Shah--Sun study general equidistribution of dilated submanifolds.  This supplies classical
  context for angular dephasing, not the local-spectral nonflatness, stabilizer collision,
  circuit-incidence or continuous plateau-block consequence:
  <https://arxiv.org/abs/1712.02907>.

The searched literature contains no theorem combining a one-time draw of a fixed-strength
nearest-neighbour Hamiltonian, an efficiently preparable design seed, same-pair continuous
near-maximal state complexity for `exp(Omega(2^n))` time, later recurrence, and permanent efficient
non-Haar locality.  This is separation evidence, not a legal priority guarantee.

## Lean realization after corpus refactor

No Lean file is created or modified now.  Read-only corpus interfaces already available:

1. fixed-shell projective spectral-action nonflatness target and angular dephasing paper theorem;
2. general-input heavy-sector replica incidence and circuit-word entropy;
3. stabilizer/Clifford finite-state infrastructure and pure-state trace distance;
4. finite-horizon Duhamel/operator-speed bounds;
5. maximal projective rank, cyclicity, recurrence and permanent two-query non-Haar separation.

Future dependency order:

1. exact stabilizer two-design collision identity `(5)`;
2. collision-good angular Portmanteau bound `(13)`;
3. fixed-shell operator-speed mesh lemma `(23)--(25)`;
4. finite-grid pair-preserving plateau theorem `(19)`;
5. double-exponential capstone `(21)--(22)`;
6. cyclic stabilizer genericity and low--plateau--recurrence corollary.

Until those capstones are formalized and axiom-audited, manuscript language must label this result
as paper-proved research, not Lean-certified final evidence.

## Lean status -- Theorem A is already in the corpus

Searched before building; Theorem A is formalized in full, including the Markov step.

| Card item | Existing declaration |
|---|---|
| **`(5)`, the exact stabilizer two-design collision law**: against any family of unit states the collision of a stabilizer state averages to `2/(D+1)` | `exists_stabilizer_states_collision_eq` (`HTGeometry/StabilizerPureState.lean`) |
| Markov's inequality on a finite index set | `finite_markov` (`HTGeometry/StabilizerCollisionMarkov.lean`) |
| **`(6)`**: at most a fraction `1/L` of stabilizer states exceed `2L/(D+1)` | `card_filter_collision_gt_mul_le` (same module) |
| the capture bound at the two-design collision scale | `measureReal_capture_le_return_add_two_rpow_of_design` (same module) |

`exists_stabilizer_states_collision_eq` is stated against an arbitrary family of unit states, which
is exactly the card's "no property of the eigenbasis, spectrum or Hamiltonian ensemble is used in
this step", and it therefore covers `(4)`--`(5)` for every Hermitian `H` at once.  `(7)`--`(8)`, the
two-design identity and its contraction, are internal to that proof.

### What remains

Theorem B (all-late common-time near-maximal state complexity) and Theorem C (one fixed pair stays
hard continuously for doubly-exponential time).

## Lean progress -- Theorem C, the continuous plateau

`formal/GaloisForLFunctions/HTGeometry/ContinuousPlateauGrid.lean` (new, umbrella-wired,
axiom-clean) proves Theorem C in the exact generality its proof uses: a uniform orbit speed, a
positive radius gap, and a family of one-time smallness bounds.  Nothing about circuits,
stabilizers or Pauli architecture enters, so the same theorem serves every card in the cluster
whose late-time clause is a grid statement.

| Card item | Declaration |
|---|---|
| `unitaryEvolution H t = unitaryEvolution (tH) 1` | `unitaryEvolution_eq_smul_time` |
| **`(23)`--`(24)` in operator form**: `‖e^{-itH} − e^{-iuH}‖ ≤ ‖H‖·\|t−u\|` | `norm_unitaryEvolution_time_sub_le` |
| the same on a state | `norm_unitaryEvolution_mulVec_time_sub_le` |
| **uniform orbit speed** for a family of generators of norm at most `speed` on unit seeds | `dist_unitaryOrbit_le` |
| the window grid `N_W = ⌈W·speed/γ⌉+1` and its points | `plateauGridCount`, `plateauGridPoint`, `one_le_plateauGridCount` |
| every window time is within one mesh of a grid point | `exists_plateauGrid_near` |
| **`(25)`**: a shortcut at radius `ε₋` at time `t` is a shortcut at radius `ε₊` at every time within `γ/speed` | `easySet_subset_of_speed` |
| **`(19)`, union-bound form**: grid smallness on the good set gives whole-window hardness | `measureReal_forall_notMem_ge` |
| **`(19)`**: from the late fixed-time bound, one time `T` beyond which *every* origin `A ≥ T` works | `exists_time_forall_interval_hard` |
| **`(19)`--`(21)` assembled with the speed mesh** | `exists_time_forall_interval_hard_of_speed` |

`measureReal_forall_notMem_ge` uses only monotonicity and subadditivity of the measure, so no
measurability hypothesis on the shortcut events is needed: the bad set is covered by
`Gᶜ ∪ ⋃ⱼ (G ∩ easy_{ε₊}(tⱼ))` and the complement bound comes from
`1 = μ(univ) ≤ μ(bad) + μ(badᶜ)`.  The uniform speed `√m` of `(23)` is
`opNorm_pauliCombination_le_sqrt_card` on the coefficient unit sphere.

`(20)`--`(22)` are arithmetic consequences of the displayed grid count: with `speed = √m` and
`γ = ε₊ − ε₋`, `plateauGridCount W (γ/√m) = ⌈W√m/γ⌉ + 1 = N_W`, so `N_W ≤ 2^{r/4}` is exactly the
card's condition and `W = γ(2^{r/4} − 2)/√m` its inverse.

### What remains

Theorem B alone.  Its capture bound `(15)`--`(16)` is already the corpus theorem
`measureReal_capture_le_return_add_two_rpow_of_design`; what `(13)` still needs is the angular
equidistribution `(17)`, which is Theorem B of the parent card
`fixed-shell-angular-dephasing-static-local-plateau-law`, together with the Portmanteau upper
bound against the closed low-circuit event.

## Lean progress -- Theorem B (2026-08-21)

The parent card `fixed-shell-angular-dephasing-static-local-plateau-law` reached stage 3 on
2026-08-21, so its Theorem B `(17)` and the whole Portmanteau/compact-exhaustion assembly are
available on the card's own nearest-neighbour Pauli family.  Theorem B of this card follows.

`formal/GaloisForLFunctions/HTGeometry/StabilizerSeededPlateauLaw.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| finite subadditivity of an upper limit (`atTop` on `ℝ` is not a countable-inter filter, so `ENNReal.limsup_add_le` does not apply) | `limsup_add_le_atTop`, `limsup_finsetSum_le` |
| **the two-design law with the stabilizer family chosen *before* the eigenbasis** | `exists_stabilizer_family_collision_eq` |
| the seed on the numbered register and its unit norm | `stabIndex`, `card_stabIndex`, `stabSeed`, `stabSeed_comp`, `finiteComplexInner_stabSeed` |
| the eigenbasis read on the register | `registerEigenBasis`, `sum_normSq_registerEigenBasis`, `crossCollision_stabSeed` |
| **`(13)`: the plateau bound at a fixed seed** | `limsup_sphereLaw_seedCapture_le` |
| **`(11)`: the seed-averaged plateau bound** | `limsup_sphereLaw_stabilizerSeeded_sum_le` |

The reordering of quantifiers in `exists_stabilizer_family_collision_eq` is the step that makes the
card's argument work at all: the corpus's `exists_stabilizer_states_collision_eq` produces the
stabilizer family *after* being handed an eigenbasis, so its family depends on `θ`, while the card
needs one family of seeds and the collision law at every `θ` simultaneously.  Inspecting the proof
shows the family comes from `exists_stabilizer_pure_state`, which does not see the eigenbasis at
all, so moving `∀ e` inside the existential is legitimate and the proof is unchanged.

`(11)` is stated as a sum over the seed index `stabIndex n = lagrBases n ×ˢ univ` rather than as an
average, so no division in `ℝ≥0∞` appears; dividing by `|stabIndex n|` gives the card's
`Pr_{θ,χ}` form verbatim.  The `1/L` half is the two-design Markov bound
`card_filter_collision_gt_mul_le` applied *pointwise in `θ`* and integrated by
`lintegral_finsetSum`; this is legitimate because the good angular set of the parent card is
**open** -- the collision is `∑_j ‖w_j(θ)‖²` in the gauge-invariant cross-weights, continuous
exactly on the (open) simple-spectrum locus.

### What remains

The corollary: cyclic stabilizer genericity and the low--plateau--recurrence trajectory.  Its
ingredients are the corpus's `kronecker_approx_atTop`, the maximal-projectivity genericity of the
chain shell, and the permanent two-query locality separator
(`haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero`); what has to be written is the seed
recurrence `∀ A, ∃ R > A, 1 − fidelity(e^{-iRH}χ, χ) < ρ²`, which is
`norm_finiteComplexInner_unitaryEvolution_eq` with `v = χ` (whose cross-weights are the occupation
probabilities `p_j ≥ 0` summing to one) plus Kronecker recurrence at the projective frequencies.

## Lean progress -- the seed recurrence (2026-08-21)

`formal/GaloisForLFunctions/HTGeometry/SeedOrbitRecurrence.lean` (new, umbrella-wired,
axiom-clean) closes item 3 of the corollary:

| Card item | Declaration |
|---|---|
| maximal projectivity gives rationally independent anchored gaps | `linearIndependent_rat_projectiveFrequency` |
| **the orbit returns to its seed at arbitrarily late times** | `exists_late_seed_recurrence` |

```
theorem exists_late_seed_recurrence {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam)
    (hmax : MaximallyProjectiveEnergy lam) (i₀ : α)
    (Om : α → ℂ) (hOm : finiteComplexInner Om Om = 1)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ s : ℝ, A < s ∧ 1 - ρ ≤ ‖finiteComplexInner (unitaryEvolution H s *ᵥ Om) Om‖
```

**Cyclicity is not needed.**  The card invokes the balanced-ternary Hamiltonian `(27)` to make the
seed cyclic, so that the Krylov determinant is nonzero.  That is required to make the *orbit* dense
in the full phase torus, but the corollary only needs the orbit to return to *its own seed*, and
the overlap with the seed is the phase average `∑_j e^{-is(λ_j-λ_{i₀})} p_j` of the occupation
probabilities.  Maximal projectivity makes every anchored gap frequency rationally independent, so
Kronecker recurrence returns every phase to one at arbitrarily late times regardless of which `p_j`
vanish.  The corollary's genericity requirement therefore reduces from "cyclic *and* maximally
projective" to "maximally projective".

### What remains

One item: almost-sure maximal projectivity on the nearest-neighbour shell, i.e.

```
∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel n)))),
  MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ).eigenvalues
```

Both ingredients exist.  The corpus's
`realHermitianSubmoduleMaximalSet_dense_residual_fullMeasure` says that a real Hermitian matrix
subspace containing **one** maximally projective Hamiltonian has full-measure maximal projectivity
in its *canonical* basis coordinates, and the seed `exists_pauliChainSeed` supplies that one
Hamiltonian inside `pauliChainSpan n` (its spectrum is the maximally projective `E`, transported by
`maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket`).  What has to be written is the
transport of the full-measure set from the canonical coordinates of the submodule to the
`chainPauliFin` coordinates -- a linear isomorphism of `ℝ^N`, under which null sets are null -- for
which one needs `Module.finrank ℝ (pauliChainSpan n) = Fintype.card (ChainLabel n)`, i.e. the real
linear independence of the nearest-neighbour Pauli strings inside the self-adjoint space.

## Lean progress -- the corollary is closed; the card is fully formalized (2026-08-21)

`formal/GaloisForLFunctions/HTGeometry/ChainShellMaximalProjectivity.lean` (new, umbrella-wired,
axiom-clean) supplies the genericity the corollary needs.

| Card item | Declaration |
|---|---|
| a rectangular unitary conjugation preserves the characteristic polynomial | `charpoly_unitary_conj_diagonal`, `matrixCharpolyRelation_diagonal` |
| **the seed is one maximally projective member of the nearest-neighbour family** | `seedSpectrumFin`, `exists_chainShell_maximallyProjective_witness` |
| the obstruction-generic set is measurable, and membership is maximal projectivity | `measurableSet_polynomialMatrixProjectiveGenericSet_compl`, `map_spectralGenericMatrix_eq`, `mem_genericSet_iff_maximallyProjective` |
| maximal projectivity is scale invariant | `maximallyProjectiveEnergy_spectralEnsemble_smul_iff` |
| **almost every shell direction is maximally projective** | `maximallyProjectiveEnergy_chainShell_ae` |
| **item 3 of the corollary, almost surely** | `ae_exists_late_seed_recurrence_chainShell` |

The witness is the endpoint-complete Pauli seed itself: `exists_pauliChainSeed (k+1)` produces
`H = U diag(E) Uᴴ` inside `pauliChainSpan (k+3)` whose spectrum is the maximally projective `E`,
and `charpoly_unitary_conj_diagonal` identifies its characteristic polynomial with that of
`diagonal E`, so `maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket` transfers maximal
projectivity to the canonical eigenvalues.  The corpus's one-witness theorem
`polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure` then gives full Lebesgue measure,
and the same cone/`toSphere` argument as for the simple spectrum transports it to the shell.

### Status of the card

| Card statement | Declaration |
|---|---|
| **Theorem A `(5)`** -- exact stabilizer two-design collision law | `exists_stabilizer_states_collision_eq`, and with the family chosen first `exists_stabilizer_family_collision_eq` |
| **Theorem A `(6)`** -- the Markov form | `card_filter_collision_gt_mul_le` |
| **Theorem B `(13)`** -- the plateau bound at a fixed seed | `limsup_sphereLaw_seedCapture_le` |
| **Theorem B `(11)`** -- the seed-averaged plateau bound | `limsup_sphereLaw_stabilizerSeeded_sum_le` |
| **Theorem C `(19)`--`(22)`** -- the continuous doubly-exponential plateau | `exists_time_forall_interval_hard_of_speed`, `plateauGridCount`, `dist_unitaryOrbit_le` |
| **Corollary item 2** -- hardness at every instant of the window | `exists_time_forall_interval_hard_of_speed` |
| **Corollary item 3** -- a later recurrence, almost surely | `ae_exists_late_seed_recurrence_chainShell`, `exists_late_seed_recurrence` |
| the permanent two-query locality separator | `haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero` |

Corollary item 1 (`C_0(χ) ≤ b_n = O(n²)`) is the card's own setup hypothesis -- the existence of a
polynomial Clifford compiler for stabilizer states -- not a theorem to prove.

All statements are unconditional and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`
only).  The card is fully formalized.
