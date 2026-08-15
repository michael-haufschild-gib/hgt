# Quenched causal replica-action law

- **ID:** `quenched-causal-replica-action-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / quenched replica law / Brown-front advance
- **Parents:** `concurrent-causal-heap-accessibility-law.md`,
  `circuit-complexity-selection-synthesis-divergence-law.md`,
  `quenched-observer-spectral-action-law.md`
- **Status:** `[PAPER-PROVED] [PROVED HERE] [FRONTIER ADVANCE]
  [CLASSICAL ENTROPY-DUALITY ENGINE] [APPLICATION NOVELTY UNVERIFIED]
  [LEAN CERTIFIED]`
- **Date:** 2026-08-13

## Public sentence

A growing-replica proof of autonomous quantum complexity must replicate candidate preparations,
not the Hamiltonian.  When all replicas see the same static Hamiltonian, their exact incidence
mass is a Laplace transform of causal preparation action.  Its exponent is the minimum of
Hamiltonian-source rarity plus replicated preparation cost.  Source rarity is therefore amortized
by replica number: growing replicas expose rare easy carriers instead of averaging them away.

This law identifies the exact quenched object and exact carrier debt.  It does not prove that the
debt is Brown-scale for an ordinary local-Hamiltonian ensemble.

## 1. Shared-source replica mass

Let `(Omega,rho)` be any probability space of ordinary time-independent Hamiltonian sources, or
any other autonomous sources.  Let `x:Omega->X` be a measurable endpoint map.  In the intended
application,

\[
 x(H)=\Phi_H(t)=e^{-itH}\chi.
 \tag{1}
\]

Fix a finite local-gate trace monoid, fugacity `z` in its convergence interval, and robust seed
target `A`.  Let

\[
 F(H)=F_{A,z}(x(H)),
 \qquad
 J(H)=-\log F(H)
 \tag{2}
\]

be the concurrent causal accessibility and preparation action proved in the parent.  Thus
`0<=F<=1`, with `J=+infinity` when `F=0`.

For an integer `r>=1`, define the **quenched causal replica mass**

\[
 \boxed{
 Z_r(\rho;x,A,z)=\int_\Omega F(H)^r\,d\rho(H)
 =\int_\Omega e^{-rJ(H)}\,d\rho(H).}
 \tag{3}
\]

Only candidate circuit heaps are replicated.  The same `H` and same occupied endpoint `x(H)` are
used in every factor.

## 2. Product-incidence and complexity law

Let `T_1,...,T_r` be independent with finite heap law `pi_z`.  For fixed `H`, write

\[
 E_H^{(r)}=
 \{(T_1,\ldots,T_r):
   \forall j\ \exists u_j\preceq T_j,
   \ x(H)\in\operatorname{ev}(u_j)A\}.
 \tag{4}
\]

### Theorem A -- exact quenched replica incidence

For every `r>=1`,

\[
 \boxed{
 Z_r
 = (\rho\otimes\pi_z^{\otimes r})
   \{(H,T_1,\ldots,T_r):(T_1,\ldots,T_r)\in E_H^{(r)}\}.}
 \tag{5}
\]

For every integer `s>=0`,

\[
 \boxed{
 \rho\{H:C_A(x(H))\le s\}
 \le z^{-rs}Z_r.}
 \tag{6}
\]

The same statement holds with the soft reporter `S_(A,z,delta)` from the parent:

\[
 \rho\{C_A(x(H))\le s\}
 \le z^{-rs}\int_\Omega S_{A,z,\delta}(x(H))^r\,d\rho(H).
 \tag{7}
\]

The Lipschitz constant of the integrand in `(7)` is at most `r/delta` in endpoint distance and at
most `r|t|/delta` in Hamiltonian operator norm.  It is independent of Hilbert-space dimension and
the complete circuit count.

### Proof

Conditional on `H`, each event in `(4)` has probability `F(H)` and the heap draws are independent.
Its conditional probability is therefore `F(H)^r`.  Integrating proves `(5)`.  If
`C_A(x(H))<=s`, the causal-cylinder law gives `F(H)>=z^s`, hence

\[
 \mathbf1_{\{C_A\le s\}}(H)
 \le z^{-rs}F(H)^r.
\]

Integration proves `(6)`.  The soft law gives `S>=z^s` on the same event and proves `(7)`.  Since
`0<=S<=1`, the map \(v\mapsto v^r\) is `r`-Lipschitz on `[0,1]`; compose with the parent's endpoint
and Duhamel bounds. `square`

Equation `(5)` retains, before any coarea transformation:

- the original source measure and every source fibre;
- one common quenched Hamiltonian across replicas;
- the occupied endpoint image `x(H)`;
- all distinct causal circuit heaps;
- all prefix-cylinder overlaps through an exact union probability rather than a description sum.

## 3. Exact source--preparation action duality

### Theorem B -- quenched replica-action law

If `Z_r>0`, then

\[
 \boxed{
 -\log Z_r
 =\inf_{q\ll\rho}
   \left\{D(q\Vert\rho)+r\int_\Omega J(H)\,dq(H)\right\}.}
 \tag{8}
\]

The minimizer is

\[
 \boxed{
 {dq_r^*\over d\rho}(H)={e^{-rJ(H)}\over Z_r}
 ={F(H)^r\over Z_r}.}
 \tag{9}
\]

Equivalently, on the full product space,

\[
 \boxed{
 -\log Z_r
 =\inf\left\{
 D(Q\Vert\rho\otimes\pi_z^{\otimes r}):
 Q(E^{(r)})=1\right\},}
 \tag{10}
\]

where `E^(r)` is the incidence event in `(5)`.  The optimizer is the product prior conditioned on
`E^(r)`.

### Proof

For any `q<<rho`, expand relative entropy against `(9)`:

\[
 \begin{aligned}
 D(q\Vert q_r^*)
 &=D(q\Vert\rho)+r\int J\,dq+\log Z_r.
 \end{aligned}
 \tag{11}
\]

Nonnegativity and rigidity prove `(8)--(9)`.  The event-projection identity `(10)` follows by the
same calculation against the product prior conditioned on `E^(r)`, whose mass is `(5)`. `square`

### Corollary B.1 -- exact causal-replica certificate criterion

For any real `L`,

\[
 \boxed{
 Z_r\le e^{-L}
 \quad\Longleftrightarrow\quad
 D(q\Vert\rho)+r\int J\,dq\ge L
 \quad\text{for every }q\ll\rho.}
 \tag{12}
\]

In particular, the desired bound

\[
 Z_r\le z^{rs}e^{-\kappa r}
 \tag{13}
\]

is equivalent to the family of source--preparation separation inequalities

\[
 \boxed{
 {1\over r}D(q\Vert\rho)+\int J\,dq
 \ge s\log{1\over z}+\kappa
 \quad(q\ll\rho).}
 \tag{14}
\]

Thus, **within this growing-replica certificate**, complete causal preparation and quenched source
rarity are the two summands of one exact action inequality.

## 4. Rare-carrier amortization

### Theorem C -- replicas select the easiest surviving carrier

The sequence `(Z_r)` obeys

\[
 1\ge Z_r\ge Z_{r+1}\ge0,
 \tag{15}
\]

is log-convex in `r`, and satisfies

\[
 \boxed{
 \lim_{r\to\infty}Z_r^{1/r}
 =\|F\|_{L^\infty(\rho)}
 =e^{-\operatorname*{ess\,inf}_\rho J}.}
 \tag{16}
\]

If a measurable carrier `B` has `rho(B)>0` and `J(H)<=j` on `B`, then

\[
 \boxed{
 Z_r\ge\rho(B)e^{-rj},
 \qquad
 -{1\over r}\log Z_r
 \le j+{1\over r}\log{1\over\rho(B)}.}
 \tag{17}
\]

Conversely, if `J(H)>=j` almost surely on a retained source sector, its contribution to `Z_r` is at
most `e^{-rj}` times that sector's mass.

### Proof

Monotonicity follows from `0<=F<=1`; log-convexity is Hölder's inequality.  Equation `(16)` is the
standard `L^p`-norm limit on a probability space, proved directly as follows.  The upper bound is
`Z_r^(1/r)<=||F||_infinity`.  For every `eta>0`, the set
`{F>||F||_infinity-eta}` has positive measure, which supplies the matching lower limit; then send
`eta` to zero.  Equations `(17)` and its converse follow by integrating `e^{-rJ}` over the named
sector. `square`

Equation `(17)` is the rare-carrier law.  A carrier's source cost `-log rho(B)` is paid once, while
its preparation cost is paid in every replica.  Dividing the exponent by `r` amortizes source
rarity as

\[
 j+{1\over r}\log{1\over\rho(B)}.
 \tag{18}
\]

Therefore larger replica order does not make an annealed proof automatically more typical.  It
makes the easiest positive-mass quenched carrier increasingly dominant.

### Corollary C.1 -- replica schedules have an upper as well as a lower frontier

Define normalized replica action and the depth-`s` certificate exponent by

\[
 a_r=-{1\over r}\log Z_r=-\log\|F\|_{L^r(\rho)},
 \qquad
 \Gamma_r(s)=r\left(a_r-s\log{1\over z}\right).
 \tag{18a}
\]

Then

\[
 \boxed{
 a_{r+1}\le a_r,
 \qquad
 \lim_{r\to\infty}a_r=operatorname*{ess\,inf}_\rho J,}
 \tag{18b}
\]

and `(6)` is exactly

\[
 \boxed{
 \rho\{C_A(x(H))\le s\}\le e^{-\Gamma_r(s)}.}
 \tag{18c}
\]

Hence the replica orders with positive normalized gap

\[
 a_r>s\log(1/z)
\]

form an initial interval of the positive integers.  If a carrier `B` has `J<=j<s log(1/z)` on it,
then `(17)` forces the necessary schedule ceiling

\[
 \boxed{
 r< {\log(1/\rho(B))\over s\log(1/z)-j}}
 \tag{18d}
\]

for any positive certificate exponent at that order.

### Proof

`L^p` norms on a probability space increase with `p`, proving monotonicity in `(18b)`; `(16)` gives
the limit.  Rewrite `(6)` using `(18a)` to obtain `(18c)`.  Finally `(17)` gives

\[
 a_r\le j+{1\over r}\log(1/\rho(B));
\]

positivity of `Gamma_r(s)` implies `(18d)`. `square`

This is not a claim that small `r` suffices.  Spectral or coarea control may impose a lower replica
order.  A viable proof needs overlap between that analytic lower requirement and the carrier upper
ceiling `(18d)`.

## 5. Exact recurrence extraction

Let `1` denote the empty circuit heap.  It has probability

\[
 p_0=\pi_z(1)={1\over\mathcal Z(z)}>0.
 \tag{19}
\]

### Theorem D -- common recurrence mass is isolated once

For every endpoint `x`,

\[
 \boxed{
 F_{A,z}(x)=1\quad\Longleftrightarrow\quad x\in A.}
 \tag{20}
\]

Moreover,

\[
 x\notin A\quad\Longrightarrow\quad
 F_{A,z}(x)\le1-p_0.
 \tag{21}
\]

Consequently,

\[
 \boxed{
 \rho\{x(H)\in A\}
 \le Z_r
 \le \rho\{x(H)\in A\}
   +\rho\{x(H)\notin A\}(1-p_0)^r,}
 \tag{22}
\]

and hence

\[
 \boxed{
 \lim_{r\to\infty}Z_r=\rho\{H:x(H)\in A\}.}
 \tag{23}
\]

### Proof

If `x in A`, the identity prefix succeeds in every heap, so `F=1`.  If `x notin A`, the empty heap
has no successful prefix and has mass `p_0`; hence `F<=1-p_0<1`.  Integrate the `r`th powers on the
recurrence set and its complement to obtain `(22)--(23)`. `square`

This is stronger than merely observing that recurrence contaminates moments.  The common
recurrence mass is the exact nondecaying replica sector; removing it once is necessary and
sufficient for `Z_r->0` as `r->infinity`.  It is not sufficient for Brown-scale decay at a prescribed
replica schedule because nonrecurrent low-`J` carriers can still dominate through `(17)`.

## 6. Exact open core of the growing-replica route

For each physical time in the formalized geometric skeleton, let `rho_t^circ` be the original
static-Hamiltonian source restricted by one target-independent recurrence and fast-forwardable
carrier cut.  Define

\[
 Z_{n,r}^{\rm causal}(t)
 =\int F_{A_n,z}(\Phi_H(t))^r\,d\rho_t^\circ(H).
 \tag{24}
\]

The growing-replica route to Brown's first cut is now the following exact action-gap problem:

\[
 \boxed{
 \text{prove}\quad
 {1\over r_n}D(q\Vert\rho_t^\circ)
 +\mathbb E_qJ_{A_n,z}(\Phi_H(t))
 \ge s_n(t)\log{1\over z}+\kappa
 \quad\text{for every }q\ll\rho_t^\circ,}
 \tag{25}
\]

for one growing replica schedule and all retained skeleton times.  By `(12)--(14)`, this is
necessary and sufficient for the corresponding quenched causal-replica bound; by `(6)`, it is
sufficient for the complete circuit event at depth `s_n(t)`.  It is not claimed necessary for a
direct lower-tail proof that does not pass through `Z_r`.

The source relative entropy in `(25)` is taken on the original Hamiltonian parameter space.  Coarea
may be used to prove it, but no endpoint pushforward, Jacobian pseudodeterminant, or minimum spectral
gap is the invariant.  Any such device is adequate only if it proves the source--preparation action
gap for **every tilted source law `q`**.  This retains fibre-sheet multiplicity and occupied endpoint
image automatically.

## 7. Conjecture--failure--survivor loop

### C0 -- replicate independently drawn Hamiltonians

Verdict: `[FALSIFIED AS QUENCHED]`.  It yields `(E_rho F)^r` and erases the shared static source.
The quenched mass is `E_rho F^r`, with the same `H` in every replica.

### C1 -- growing replicas wash out rare Hamiltonians

Verdict: `[FALSIFIED]` by `(17)--(18)`.  Source rarity is paid once and divided by replica number;
large `r` selects the easiest surviving positive-mass carrier.

### C2 -- remove recurrence separately at every replica order

Verdict: `[UNNECESSARY]`.  Theorem D identifies one exact nondecaying sector, independent of `r`.
One common source cut removes it for all orders.

### C3 -- inside the replica route, moment estimate and complete causal union are separate tasks

Verdict: `[FALSIFIED]`.  The causal cylinder calibration `(6)` and action duality `(12)` combine
them into the single necessary-and-sufficient inequality `(25)`.

### C4 -- source entropy plus preparation action is the surviving replica invariant

Verdict: `[PROVED AS AN EXACT REDUCTION; PHYSICAL GAP OPEN]`.  Theorems A--D prove the law for every
source probability, endpoint map, and finite local circuit heap process.  Ordinary static-local
geometry must still prove the positive gap in `(25)`.

## 8. Hostile audit

1. **The entropy variational formula is classical.**  Gibbs/Donsker--Varadhan duality and
   `L^p` limits are not new.  Provisional novelty lies only in the causal-heap, shared-static-source
   specialization and its exact growing-replica first-cut criterion.
2. **No Brown growth is claimed.**  Equation `(25)` is a mathematically sharper open core, not its
   solution.
3. **Replica growth can hurt.**  The rare-carrier law proves this rather than hiding it.  Any chosen
   `r_n` must balance synthesis amplification against source-rarity amortization.
4. **The replica route can be strictly stronger than the desired event bound.**  A very rare easy
   carrier may have acceptably small contribution to `rho{C<=s}` yet dominate `Z_r` because the
   certificate also pays `z^(rs)`.  Such a carrier must be charged in one common cut, resolved by a
   stratified moment estimate, or handled by a direct non-moment lower-tail proof.
5. **Return removal is exact but not magic.**  Theorem D removes only `J=0`.  Gapped eigenlines,
   fast-forwardable sectors, and other small-positive-action carriers need one common quantitative
   classification.
6. **Endpoint pushforward is not forbidden.**  It is insufficient when used only through cover
   entropy.  A pushforward or coarea proof is valid if it establishes `(25)` for every source tilt.
7. **Auxiliary heap probability is not Hamiltonian noise.**  `pi_z` is a coding/preparation law;
   `rho` is the physical source law.
8. **Finite alphabet and fugacity remain explicit.**  Continuous gate parameters require a robust
   net and its coding measure.
9. **Priority remains provisional.**  Negative targeted search is not a priority certificate.
10. **Lean certified.**  Every proved statement of this card is closed unconditionally in Lean 4;
    only the open core `(25)` carries no formal obligation.

## 9. External boundary

- Gibbs/Donsker--Varadhan variational duality, information projection, Hölder log-convexity, and
  the `L^p`-to-`L^infinity` limit are classical.  No abstract probability novelty is claimed.
- Rizzo, *A replica trick for rare samples* (arXiv:1403.1828), explicitly uses replicas to select
  rare quenched Hamiltonian samples in disordered systems.  Rare-sample replica selection is
  therefore not claimed as new.
- Targeted searches found no source combining one shared static local Hamiltonian, a finite
  trace-monoid preparation law, causal-prefix union probability, exact recurrence extraction, and
  criterion `(25)` for robust circuit complexity.  This is evidence only, not priority proof.

## Gates

- [x] exact shared-H product-incidence formula
- [x] growing-replica complete-circuit bound
- [x] exact source--preparation action duality
- [x] necessary-and-sufficient Brown action criterion
- [x] rare-carrier amortization and replica-limit law
- [x] exact common recurrence extraction
- [x] soft dimension-free replica regularity
- [x] hostile audit
- [ ] ordinary static-local action gap `(25)`
- [x] Lean formalization of every proved statement

## Lean certificate

Unconditional and closed in Lean 4; every declaration below has axiom set
`[propext, Classical.choice, Quot.sound]`.

| Card statement | Lean declaration |
|---|---|
| `(2)` accessibility `F`, preparation action `J` | `RHTower.causalAccessibility`, `RHTower.preparationAction`, `HTGeometry.preparationActionOf` |
| `(3)` quenched replica mass `Z_r` | `HTGeometry.quenchedReplicaMass`, `HTGeometry.quenchedReplicaMass_eq_integral_exp` |
| `(4)` replicated incidence event `E_H^{(r)}` | `RHTower.replicaIncidenceEvent`, `RHTower.measurableSet_replicaIncidenceEvent` |
| `(5)` exact quenched replica incidence | `RHTower.measure_replicaIncidenceEvent`, `RHTower.measureReal_replicaIncidenceEvent` |
| `(6)` growing-replica complete-circuit bound | `RHTower.measureReal_heapAccessible_le_quenchedReplicaMass` |
| `(7)` soft-reporter form | `RHTower.measureReal_heapAccessible_le_softReplicaMass` |
| `(7)` Lipschitz constant `r/δ` | `RHTower.abs_softCausalReporter_pow_sub_le`, `RHTower.lipschitzWith_softCausalReporter` |
| `(8)` quenched replica-action law | `HTGeometry.isLeast_quenchedReplicaAction`, `HTGeometry.isLeast_gibbsAction` |
| `(9)` minimizing density `dq_r^*/dρ = F^r/Z_r` | `HTGeometry.rnDeriv_tilted_quenched` |
| `(10)` event-projection form | `HTGeometry.isLeast_relativeEntropy_conditioned` (with `(5)` for the event mass) |
| `(11)` relative-entropy expansion | `HTGeometry.integral_llr_tilted_quenched` |
| `(12)` exact certificate criterion | `HTGeometry.quenchedReplicaMass_le_exp_iff` |
| `(13)`–`(14)` normalized separation inequality | `HTGeometry.quenchedReplicaMass_le_exp_iff_normalized` |
| `(15)` `1 ≥ Z_r ≥ Z_{r+1} ≥ 0` | `HTGeometry.quenchedReplicaMass_le_one'`, `HTGeometry.quenchedReplicaMass_antitone'`, `HTGeometry.quenchedReplicaMass_nonneg'` |
| log-convexity in `r` | `HTGeometry.quenchedReplicaMass_sq_le` |
| `(16)` `lim Z_r^{1/r} = ‖F‖_∞ = e^{-ess inf J}` | `HTGeometry.tendsto_quenchedReplicaMass_rpow`, `HTGeometry.essSup_eq_exp_neg_essInf`, `HTGeometry.essInf_preparationActionOf` |
| `(17)` rare-carrier lower bound and its converse | `HTGeometry.quenchedReplicaMass_ge_of_carrier`, `HTGeometry.measureReal_le_quenchedReplicaMass` |
| `(18a)` normalized replica action `a_r` | `HTGeometry.quenchedReplicaAction`, `HTGeometry.quenchedReplicaAction_eq` |
| `(18b)` `a_{r+1} ≤ a_r`, `lim a_r = ess inf J` | `HTGeometry.quenchedReplicaAction_antitone`, `HTGeometry.tendsto_quenchedReplicaAction` |
| `(18c)` `ρ{C_A ≤ s} ≤ e^{-Γ_r(s)}` | `RHTower.measureReal_heapAccessible_le_exp` |
| `(18)`, `(18d)` amortization and schedule ceiling | `HTGeometry.quenchedReplicaAction_le_of_carrier`, `HTGeometry.lt_of_pos_certificate_exponent` |
| `(19)` empty-heap mass `p_0 > 0` | `RHTower.traceLaw_singleton`, `RHTower.traceWeight_one_pos`, `RHTower.traceWeight_one_le_one` |
| `(20)` `F = 1 ⟺ x ∈ A` | `RHTower.causalAccessibility_eq_one_iff` |
| `(21)` `x ∉ A ⟹ F ≤ 1 - p_0` | `RHTower.causalAccessibility_add_traceWeight_one_le_one` |
| `(22)` two-sided recurrence sandwich | `RHTower.measureReal_recurrent_le_quenchedReplicaMass`, `RHTower.quenchedReplicaMass_le_recurrent_add` |
| `(23)` `lim Z_r = ρ{x(H) ∈ A}` | `RHTower.tendsto_quenchedReplicaMass_recurrent` |

Supporting infrastructure built for this card:

- `HTGeometry/GibbsVariationalPrinciple.lean` — the Gibbs/Donsker--Varadhan duality on an arbitrary
  probability space (`gibbsAction`, `neg_log_integral_exp_le_gibbsAction`, `gibbsAction_tilted`,
  `isLeast_gibbsAction`).  Not in mathlib.
- `HTGeometry/ConditionalInformationProjection.lean` — the information projection onto an event:
  the least relative entropy of a law carried by an event is the negative logarithm of its mass,
  attained by the conditioned law.  Not in mathlib.
- `HTGeometry/PowerMeanEssSupLimit.lean` — power means of a unit-bounded density increase with the
  exponent (Hölder against the constant one) and converge to the essential supremum.  Not in
  mathlib.
- `RHTower/CircuitTraceLaw.lean` — the Boltzmann weights of the trace monoid as a probability
  measure on circuit heaps, with `traceLaw (causalSuccessEvent) = ofReal (causalAccessibility)`.
- `RHTower/QuenchedCausalReplicaIncidence.lean`, `RHTower/QuenchedCausalRecurrenceExtraction.lean`
  — the Fubini product-incidence identity and the recurrence extraction.

Sections 6 and 7 of this card are the open core and the audit; `(24)`--`(25)` state the remaining
open problem rather than a proved theorem, so they carry no Lean obligation.  By `(12)`--`(14)` the
criterion `(25)` is exactly `quenchedReplicaMass_le_exp_iff_normalized` instantiated at the
static-local source, which remains open.
