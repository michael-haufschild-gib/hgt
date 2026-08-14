# Local-circuit heap capacity law

- **ID:** `local-circuit-heap-capacity-law`
- **Stage:** 3-formalized
- **Type:** theorem / circuit-capacity correction / Brown-front advance
- **Parents:** `first-entrance-gate-renewal-prefix-law.md`,
  `capacitary-observer-sector-excision-law.md`,
  `fixed-shell-angular-dephasing-static-local-plateau-law.md`
- **Status:** `[LEAN-PROVED] [PROVED HERE] [FRONTIER ADVANCE]
  [CLASSICAL TRACE-MONOID ENGINE] [APPLICATION NOVELTY UNVERIFIED]
  [THEOREMS A AND B LEAN-FORMALIZED]`
- **Date:** 2026-08-13

## Public sentence

Geometrically local circuit capacity is controlled by the dependence graph of the gates, not by
the number of places at which the next gate could be written.  Quotienting only the exact
commutations of disjoint gates changes the robust state-complexity capacity of a bounded-degree
architecture from the raw `D/log n` counting scale to a linear-in-`D` scale.  For static local
dynamics this removes a spurious `log n` from the plateau and from the remaining first-cut
incidence budget; it does not prove the first cut.

## 1. Why raw word entropy is not intrinsic

Let `Sigma` be a finite alphabet of `M` padded unitary gates.  Give each letter `a` a finite support
`supp(a)` in the hardware graph.  If

\[
 \operatorname{supp}(a)\cap\operatorname{supp}(b)=\varnothing,
 \tag{1}
\]

the padded gates commute exactly.  Therefore the two circuit words `uabv` and `ubav` have the same
endpoint.  Counting them separately in `M^ell` is safe but not intrinsic.

Let `a I b` mean that `a` and `b` are distinct and satisfy `(1)`.  Let `Dep` be the complementary
dependence relation on distinct letters, and let `G_Dep` be its simple graph.  Put

\[
 \Delta=\max_{a\in\Sigma}\deg_{G_{\rm Dep}}(a).                  \tag{2}
\]

The trace monoid is

\[
 \mathcal M(\Sigma,I)
 =\Sigma^*/\langle uabv=ubav:\ a I b\rangle.                    \tag{3}
\]

All representatives of a trace have the same length.  Since independent padded gates commute,
circuit evaluation factors through `(3)`:

\[
 \operatorname{ev}:\mathcal M(\Sigma,I)\longrightarrow U(\mathcal H).
 \tag{4}
\]

No commutation of overlapping gates and no presentation-completeness claim is used.  Any further
gate relation only identifies more endpoints and strengthens every upper bound below.

## 2. A bounded-dependence trace count

Write `h_ell` for the number of traces of length `ell`.

### Theorem A -- pair-projection trace bound

For every `ell>=0`,

\[
 \boxed{
 h_\ell
 \le {M+\ell-1\choose\ell}\,2^{\Delta\ell}.}
 \tag{5}
\]

The free-word bound also remains valid, so

\[
 h_\ell\le
 \min\left\{M^\ell,{M+\ell-1\choose\ell}2^{\Delta\ell}\right\}.
 \tag{6}
\]

### Proof

Fix a multiplicity vector `n=(n_a)_(a in Sigma)` with `sum_a n_a=ell`.  For a word `w`, retain,
for every dependence edge `{a,b}`, only the letters `a` and `b`.  This gives a binary word with
`n_a` copies of `a` and `n_b` copies of `b`, hence at most

\[
 {n_a+n_b\choose n_a}                                             \tag{7}
\]

possibilities.

These pair projections, together with the multiplicities, determine the trace.  To see this
without importing a trace-monoid normal-form theorem, index occurrences of each letter in their
word order.  Order two occurrences whenever their labels are equal or dependent and their order
is recorded by the corresponding pair projection; take the transitive closure.  This is the heap
poset of the word.  Two words with the same pair projections induce the same poset.  Conversely,
every representative of the trace is a linear extension of this poset.  Any two linear extensions
of a finite poset are connected by adjacent swaps of incomparable elements: move the first element
of one extension leftward in the other and continue inductively.  Incomparable heap elements have
independent labels, so every such swap is one of the relations in `(3)`.  The two words therefore
represent the same trace.

For the fixed multiplicity vector, the number of traces is consequently at most

\[
 \prod_{\{a,b\}\in E(G_{\rm Dep})}{n_a+n_b\choose n_a}
 \le 2^{\sum_{\{a,b\}\in E(G_{\rm Dep})}(n_a+n_b)}
 =2^{\sum_a\deg(a)n_a}
 \le2^{\Delta\ell}.                                                \tag{8}
\]

There are exactly `binom(M+ell-1,ell)` multiplicity vectors.  Summing `(8)` proves `(5)`.  Every
trace has a word representative, which also gives `h_ell<=M^ell` and `(6)`. `square`

### Corollary A.1 -- bounded-degree hardware has constant gate entropy

For `s>=1`, let

\[
 H_s=\sum_{\ell=0}^s h_\ell.                                      \tag{9}
\]

Then

\[
 \boxed{
 H_s\le(s+1){M+s-1\choose s}2^{\Delta s}.}
 \tag{10}
\]

In particular,

\[
 \log H_s
 \le \Delta s\log2
   +M\log\!\left(e\left(1+{s\over M}\right)\right)
   +\log(s+1).                                                     \tag{11}
\]

If `M=O(n)`, `Delta=O(1)`, `D=2^n`, and `s=Theta(D)`, then

\[
 \boxed{\log H_s\le\Delta s\log2+o(D)=O(D).}                     \tag{12}
\]

Thus location choice does not contribute `s log n` intrinsic entropy on a bounded-degree
architecture.  It contributes the subleading multiplicity-profile term in `(11)`; noncommuting
local dependencies contribute the extensive term.

### Proof

Both factors in `(5)` are nondecreasing for `0<=ell<=s`, which gives `(10)`.  The standard
binomial estimate

\[
 {M+s-1\choose s}\le {M+s\choose M}
 \le\left({e(M+s)\over M}\right)^M
 \tag{13}
\]

gives `(11)`.  When `M=O(n)` and `s=Theta(2^n)`, the second term is `O(n^2)=o(D)` and the last term
is `O(n)=o(D)`, proving `(12)`. `square`

## 3. The heap Green reporter

Let the trace monoid act isometrically on a metric state space `X` through `(4)`.  Fix a robust
seed target `A subset X`, and define

\[
 C_A(x)=\min\{|\tau|:x\in\operatorname{ev}(\tau)A\}.              \tag{14}
\]

The definition agrees with ordinary word complexity: passing from words to traces changes neither
length nor endpoint, and every trace has a word representative.

For `0<z<2^(-Delta)`, define the trace partition function and positive heap reporter

\[
 \mathcal Z(z)=\sum_{\tau\in\mathcal M}z^{|\tau|},
 \qquad
 \mathcal G_{A,z}(x)
 =\sum_{\tau\in\mathcal M}z^{|\tau|}
   \mathbf1_{\operatorname{ev}(\tau)A}(x).                         \tag{15}
\]

### Theorem B -- dependency-normalized accessibility law

The series in `(15)` converge absolutely and

\[
 \boxed{
 \mathcal Z(z)\le(1-2^\Delta z)^{-M}.}                            \tag{16}
\]

For every finite positive endpoint measure `nu` and every `s>=0`,

\[
 \boxed{
 \nu\{C_A\le s\}
 \le z^{-s}\int_X\mathcal G_{A,z}\,d\nu.}                        \tag{17}
\]

If one has the target-uniform estimate

\[
 \nu(\operatorname{ev}(\tau)A)\le B
 \qquad(\tau\in\mathcal M),                                     \tag{18}
\]

then

\[
 \boxed{
 \nu\{C_A\le s\}
 \le Bz^{-s}(1-2^\Delta z)^{-M}.}                                \tag{19}
\]

For `s>=1`, the optimal value in this proved upper bound is

\[
 z_*={s\over 2^\Delta(M+s)},                                     \tag{20}
\]

and gives

\[
 \boxed{
 \nu\{C_A\le s\}
 \le B\,2^{\Delta s}
       \left(1+{M\over s}\right)^s
       \left(1+{s\over M}\right)^M.}                            \tag{21}
\]

### Proof

Theorem A and the negative-binomial series give

\[
 \mathcal Z(z)
 =\sum_{\ell\ge0}h_\ell z^\ell
 \le\sum_{\ell\ge0}{M+\ell-1\choose\ell}(2^\Delta z)^\ell
 =(1-2^\Delta z)^{-M},                                           \tag{22}
\]

proving convergence and `(16)`.  If `C_A(x)=c<=s`, one trace of length `c` contributes `z^c` to
`G_(A,z)(x)`.  Since `0<z<1`, this is at least `z^s`; hence

\[
 \mathbf1_{\{C_A\le s\}}(x)\le z^{-s}\mathcal G_{A,z}(x).
 \tag{23}
\]

Integration proves `(17)`.  Tonelli and `(18)` give

\[
 \int\mathcal G_{A,z}\,d\nu
 =\sum_\tau z^{|\tau|}\nu(\operatorname{ev}(\tau)A)
 \le B\mathcal Z(z),                                             \tag{24}
\]

which proves `(19)`.  Differentiating the logarithm of the right side of `(19)` gives

\[
 -{s\over z}+{M2^\Delta\over1-2^\Delta z}=0,
 \tag{25}
\]

whose unique solution in the convergence interval is `(20)`.  Substitution proves `(21)`.
`square`

The normalized likelihood `G_(A,z)/Z(z)` is one collision against a random trace drawn with
probability proportional to `z^|tau|`.  Unlike the raw gate walk, it is invariant under every
reordering of disjoint gates.  It is a positive linear reporter, not a hidden minimum over
circuits.

## 4. One-dimensional local-gate specialization

Suppose the alphabet has `K_1` one-site gate types at every site of an open chain and `K_2`
nearest-neighbour gate types at every edge.  Then

\[
 M=K_1n+K_2(n-1),                                                 \tag{26}
\]

and the dependence degree obeys

\[
 \boxed{
 \Delta\le
 \max\{K_1-1+2K_2,\ 2K_1+3K_2-1\}.}                            \tag{27}
\]

Indeed a one-site letter overlaps only the letters on the same site and the two incident edges.
An edge letter overlaps only letters on its two endpoint sites and on that edge and its two
neighbouring edges.  Boundary supports only reduce these counts.

Thus `Delta` is independent of `n` for every fixed finite geometrically local gate alphabet.

## 5. Consequence for static-local plateau capacity

Let `D=2^n`, and fix `0<epsilon<1/2` such that

\[
 q_\epsilon
 :={\pi(1-\sqrt{1-4\epsilon^2})\over2}<e^{-1},
 \qquad
 \alpha_\epsilon:=-{1+\log q_\epsilon\over2}>0.                  \tag{28}
\]

The proved Choi/thermofield-double phase-cap theorem gives the target-uniform bound

\[
 \mu_n(VA_\epsilon)\le B_D(\epsilon)
 :=D e^{D/2}q_\epsilon^{(D-1)/2}
 =\exp[-\alpha_\epsilon D+o(D)]                                  \tag{29}
\]

for every normalized circuit target `V`.  For the bounded-degree geometric dictionary above,
`(10)` gives

\[
 \mu_n\{C_\epsilon\le s\}
 \le H_sB_D(\epsilon).                                           \tag{30}
\]

Choose any fixed

\[
 0<c<{\alpha_\epsilon\over\Delta\log2}                         \tag{31}
\]

when `Delta>0`, and put `s=floor(cD)`.  Equations `(12)`, `(29)`, and `(30)` give

\[
 \boxed{
 \mu_n\{C_\epsilon\le cD\}
 \le\exp[-(\alpha_\epsilon-c\Delta\log2)D+o(D)].}              \tag{32}
\]

For `Delta=0`, the same conclusion holds for every fixed `c`, with the evident omission of the
zero denominator in `(31)`.

The fixed-shell angular dephasing theorem transfers every finite union of continuity-set target
tubes to every sufficiently late common laboratory time.  Therefore, for the same fixed-shell
Hamiltonian ensemble,

\[
 \limsup_{t\to\infty}\Pr_\theta\{C_\epsilon(\Phi_{H(\theta)}(t))\le cD\}
 \le\exp[-(\alpha_\epsilon-c\Delta\log2)D+o(D)].                 \tag{33}
\]

This upgrades its ordinary time-independent nearest-neighbour Hamiltonian lower bound from depth
`Omega(D/log n)` to depth `Omega(D)` for a fixed geometrically local gate dictionary.  The parent's
conserved-source experiment remains nonzero at all times, so a linear-in-Hilbert-dimension
state-complexity lower bound and permanent efficient distinguishability from Haar still coexist on
the same late-time event.

This is an unconditional plateau-capacity theorem.  Its common-time onset remains non-effective
in `D`, exactly as in the angular-dephasing parent.

## 6. Exact change to the first-cut core

For an arbitrary physical endpoint law `nu_t`, define the finite heap incidence

\[
 \mathfrak I_s^{\rm heap}(\nu_t,A)
 =\sum_{\ell=0}^s\sum_{\substack{\tau\in\mathcal M\\|\tau|=\ell}}
   \nu_t(\operatorname{ev}(\tau)A).                               \tag{34}
\]

Then, without any probability or spectral premise,

\[
 \boxed{
 \nu_t\{C_A\le s\}\le\mathfrak I_s^{\rm heap}(\nu_t,A).}       \tag{35}
\]

The infinite reporter `(15)` is its dependency-weighted Green completion.  On completed phase,
`(29)` pays `(34)` at the intrinsic heap entropy `(11)`.  At first-cut time, the remaining theorem
is a quenched upper bound on `(34)` or `(17)` after the already named return and fast-forwardable
carrier excision.  For a path-local dictionary its extensive circuit-entropy charge is now
`Delta s log 2`, not `s log M_n`.  Thus the advance removes a spurious `log n` from the exact open
budget but does not supply the physical-time incidence decay.

## 7. Conjecture--failure--survivor loop

### C0 -- `M_n^s` is the intrinsic number of local circuits

Verdict: `[FALSIFIED]` by `(3)--(5)`.  It counts every ordering of spacelike-disjoint gates as a
different circuit endpoint.

### C1 -- quotient by all exact circuit endpoint relations

Verdict: `[UNNECESSARY AND NONLOCAL]`.  Deciding the complete relation ideal can be as hard as
circuit equivalence.  The trace quotient uses only support-disjoint commutations, is explicit, and
every omitted relation can only improve the bound.

### C2 -- bounded dependence makes circuit capacity polynomial

Verdict: `[FALSE]`.  The factor `2^(Delta ell)` in `(5)` is genuinely exponential.  Local
noncommutation retains an extensive capacity, but its rate is system-size independent.

### C3 -- heap normalization proves the first cut

Verdict: `[FALSE AS A CONCLUSION; POSITIVE SURVIVOR PROVED]`.  Theorem B pays the complete union at
dependency entropy and `(32)` closes the full completed-phase plateau scale.  It gives no
fixed-time bound on the physical heap incidence `(34)`.  That incidence is the stronger surviving
first-cut target.

## 8. Hostile audit

1. **No Brown ramp yet.**  Equations `(32)--(35)` change capacity and entropy accounting, not the
   laboratory-time first escape.
2. **Geometry is load-bearing.**  For all-to-all two-qubit placements the dependence degree grows
   with `n`; `(6)` then reverts to the better raw-word bound.  No all-to-all `Theta(D)` plateau is
   claimed from this theorem.
3. **Finite alphabet.**  Continuously parameterized local gates require a separate robust net and
   its parameter entropy.  The theorem is stated for the finite robust dictionary used by the
   parent programme.
4. **Trace count is an upper bound.**  Different traces may still evaluate to the same unitary.
   This never invalidates a circuit-union upper bound, but `(5)` need not be sharp.
5. **No invariance premise is hidden in `(18)`.**  The measure need not be gate-invariant; `(18)`
   is a uniform target-volume statement.  Its Choi specialization is imported from the proved
   phase-cap theorem.
6. **Classical engine.**  Cartier--Foata trace monoids, heaps, and pair-projection descriptions are
   classical.  A 2024 paper titled *Enumeration of Circuits with n Quantum Gates* also explicitly
   applies partially commutative monoids to quantum-circuit enumeration.  Novelty is not assigned
   to trace theory or circuit enumeration alone.
7. **Provisional application priority.**  Targeted search found circuit enumeration and compiler
   uses of commuting gates, but not the dependency-normalized Green reporter `(15)--(21)`, its
   static completed-phase capacity upgrade `(32)`, or the resulting first-cut entropy correction.
   Absence in search is not priority certification.
8. **Formal boundary is explicit.**  Theorem A, including dependent-pair completeness, exact
   maximum-degree count, and cumulative-depth bound, is formalized in
   `formal/GaloisForLFunctions/RHTower/LocalCircuitTraceCapacity.lean`.  Theorem B, the
   one-dimensional degree bound `(27)`, the finite heap incidence `(34)--(35)`, the exact capacity
   form of `(30)`, and the entropy split `(11)`/`(13)` with its `o(D)` profile limit `(12)` are
   formalized in `formal/GaloisForLFunctions/RHTower/LocalCircuitHeapGreenReporter.lean`.  The
   Choi/thermofield phase cap `(29)` and the fixed-shell dephasing transfer used in `(33)` are
   theorems of sibling cards and are consumed here only as the caller-supplied target-uniform bound
   `B` of `(18)`.

## 9. External boundary

- Cartier and Foata, *Probl\`emes combinatoires de commutation et r\'earrangements* (1969), is the
  classical source for trace monoids and their generating functions.
- *Enumeration of Circuits with n Quantum Gates* (2024) uses partially commutative monoids to count
  circuits.  The present card therefore makes no standalone enumeration novelty claim.
- Chen--Haah--Haferkamp--Liu--Metger--Tan, *Incompressibility and spectral gaps of random circuits*
  (arXiv:2406.07478), proves robust linear growth for refreshed random circuits.  Its moment gaps do
  not give `(34)` for one static Hamiltonian; heap normalization also shows exactly which intrinsic
  circuit entropy a future transfer would have to beat.

## Gates

- [x] exact trace quotient and evaluation factorization
- [x] dependency-degree trace count with dependency-closed proof
- [x] convergent heap Green reporter and optimized complexity bound
- [x] bounded-degree path-local specialization
- [x] linear-in-Hilbert-dimension completed-phase plateau corollary
- [x] hostile and external collision audit
- [x] Lean formalization of Theorem A and its cumulative-depth corollary
- [x] Lean formalization of Theorem B heap Green reporter
- [ ] quenched physical-time heap-incidence estimate closing first cut *(open research target, not a
  theorem of this card)*

## Lean certificate

Module: `GaloisForLFunctions.RHTower.LocalCircuitHeapGreenReporter`.

| Card equation | Lean declaration |
|---|---|
| `(15)` reporter | `heapGreenReporter`, `heapAccessible` |
| `(16)`/`(22)` | `tracePartitionSum_le`, `tsum_ofReal_pow_traceLength_le` |
| `(17)` | `measure_heapAccessible_le_lintegral` |
| `(23)` | `indicator_heapAccessible_le_reporter` |
| `(24)` | `lintegral_heapGreenReporter`, `lintegral_heapGreenReporter_le` |
| `(18)`--`(19)` | `measure_heapAccessible_le_partition`, `measure_traceHeapAccessible_le` |
| `(20)`--`(21)` | `measure_traceHeapAccessible_le_optimal` |
| `(26)` | `card_chainLetter` |
| `(27)` | `chain_incidentEdgeCount_le` |
| `(30)` exact form | `measure_traceHeapAccessible_le_cumulativeTraceCount`, `chain_measure_traceHeapAccessible_le` |
| `(11)`/`(13)` | `log_cumulativeTraceCount_le`, `choose_le_exp_mul_div_pow`, `choose_profile_le_choose_alphabet` |
| `(12)` `o(D)` profile | `tendsto_capacityProfile_div_pow_two` |
| `(34)`--`(35)` | `heapIncidence`, `measure_heapAccessible_le_heapIncidence` |

Every listed declaration reports exactly `propext`, `Classical.choice`, `Quot.sound`.
