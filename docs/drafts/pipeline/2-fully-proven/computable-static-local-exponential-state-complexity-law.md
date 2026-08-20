# Computable static-local exponential state-complexity law

- **ID:** `computable-static-local-exponential-state-complexity-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** quenched-to-fixed-time transfer / nonuniform circuit lower bound
- **Parent:** `../1-in-progress/static-local-complexity-law.md`
- **Input theorem:** `local-clifford-return-excised-phase-incidence-law`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED] [LEAN DEFERRED]`
- **Date:** 2026-08-08

## Public sentence

There are bounded, rational, nearest-neighbour two-local Hamiltonians whose autonomous evolution
from a fixed product state reaches states of exponential circuit complexity.  Such witnesses can
be selected by one terminating algorithm, although the theorem does not yet bound their arrival
times or description lengths.

## Why this is a frontier statement

The completed-phase plateau theorem proves that almost every fixed Hamiltonian spends nearly all
completed time outside a large circuit ball.  By itself that is a quenched, non-effective
statement: the first hard time may depend on the Hamiltonian and no common physical time is
identified.  The first theorem below transfers the quenched phase law through time averaging and
shows that an unbounded sequence of **common deterministic times** has a positive Gaussian mass
of exponentially hard static-local endpoints.  The second theorem converts that positive-mass
statement into rational and uniformly computable witnesses.

This crosses the existence part of the nonuniform endpoint-circuit frontier.  It does not cross
the effective-time part: no upper bound on the first such common time is proved.

## Setup

Fix `n>=2`.  On the open path with `n` qubits, let

\[
 H_n(J)=\sum_{a=1}^{m_n}J_aP_a                                      \tag{1}
\]

contain every one-site Pauli and every two-site Pauli orientation on each nearest-neighbour edge.
The coefficients are independent standard real Gaussians.  This is the support-isotropic
nearest-neighbour specialization of the ensemble in the input theorem; harmless fixed rational
support weights can be included as well.

Let `Omega=|0>^(tensor n)`.  Let `G_n` be a finite gate dictionary with uniformly computable
matrix entries and let `M_n>=2` bound the number of padded gate choices, including locations, at
one word position.  Write `Z_(n,s)` for the finite set of states obtained from `Omega` by words of
length at most `s`.  Complexity is ancilla-free approximate state complexity over this fixed
dictionary.

Fix a rational error `0<epsilon<1/2`, put

\[
 a=1-4\epsilon^2,
 \qquad
 r_n=\left\lfloor {a^2\over128}\left({3\over2}\right)^n\right\rfloor,
 \qquad
 \ell_n=\lceil\log_2M_n\rceil,                                  \tag{2}
\]

and, whenever `r_n>=8`, set

\[
 s_n=\left\lfloor {r_n\over4\ell_n}\right\rfloor-1,
 \qquad
 \eta_n=2^{-3r_n/4}.                                             \tag{3}
\]

The spare factors in `(2)--(3)` are deliberate: the completed-phase theorem is applied at error
`2 epsilon`, leaving a robustness margin for rational approximation.

## Theorem A -- common-time positive-mass exponential hardness

There is an explicit integer

\[
 B_n=\left\lceil\sqrt{2\log(8m_n)}\right\rceil+1                 \tag{4}
\]

and a measurable coefficient set

\[
 \mathcal G_n\subset[-B_n,B_n]^{m_n}                              \tag{5}
\]

of standard Gaussian probability at least `1/2` such that every `J in G_n` obeys

\[
 \limsup_{T\to\infty}{1\over T}
 \left|\left\{t\in[0,T]:
   C_{2\epsilon}(e^{-itH_n(J)}\Omega)\le s_n\right\}\right|
 \le\eta_n.                                                       \tag{6}
\]

Consequently, with

\[
 g_n(t)=\Pr_J\!\left\{
 C_{2\epsilon}(e^{-itH_n(J)}\Omega)>s_n\right\},                 \tag{7}
\]

one has the deterministic fixed-time law

\[
 \boxed{
\liminf_{T\to\infty}{1\over T}\int_0^Tg_n(t)\,dt
 \ge {1\over2}(1-\eta_n).}                                      \tag{8}
\]

The same lower bound holds with `g_n(t)` replaced by the smaller restricted probability

\[
 g_n^{\mathcal G}(t)=\Pr_J\!\left\{J\in\mathcal G_n,\ 
 C_{2\epsilon}(e^{-itH_n(J)}\Omega)>s_n\right\}.                 \tag{8a}
\]

In particular,

\[
 \boxed{
 \limsup_{t\to\infty}g_n(t)\ge {1\over2}(1-\eta_n),}           \tag{9}
\]

so there is an unbounded sequence of common deterministic times `t_(n,k)` at which a positive
fraction of ordinary time-independent nearest-neighbour Hamiltonians have `2 epsilon`-approximate
state complexity greater than

\[
 s_n=\Omega\!\left({(3/2)^n\over\log M_n}\right).                \tag{10}
\]

For a standard fixed two-qubit gate alphabet with arbitrary locations,
`log M_n=O(log n)`.

### Proof of Theorem A

Let

\[
 C_J=\sum_j|\langle e_j(J),\Omega\rangle|^4                       \tag{11}
\]

be the input spectral collision.  The local-Clifford collision theorem with `L=4` gives

\[
 \Pr\{C_J>4(2/3)^n\}\le1/4.                                     \tag{12}
\]

The standard Gaussian tail estimate and the union bound give

\[
 \Pr\{\max_a|J_a|>B_n\}
 \le2m_ne^{-B_n^2/2}<1/4.                                       \tag{13}
\]

Simple spectrum, maximal projective rational spectral rank, and full input spectral support hold
outside a Gaussian-null set by the input theorem.  Intersecting these generic events
with the complements in `(12)--(13)` produces `(5)` with probability at least `1/2`.

For `J in G_n`, apply the completed-phase circuit bound at capture threshold
`a=1-(2 epsilon)^2`.  Equations `(2)--(3)` imply

\[
 M_n^{s_n+1}2^{-r_n}
 \le2^{r_n/4}2^{-r_n}=\eta_n.                                   \tag{14}
\]

One-sided Kronecker--Weyl equidistribution therefore gives `(6)`.  Put

\[
 f_T(J)={1\over T}\int_0^T
 \mathbf1_{\{C_{2\epsilon}(e^{-itH_n(J)}\Omega)>s_n\}}\,dt.     \tag{15}
\]

For every `J in G_n`, `(6)` says `liminf_T f_T(J)>=1-eta_n`.
Fatou's lemma and Tonelli's theorem now give

\[
\begin{aligned}
 \liminf_{T\to\infty}{1\over T}\int_0^Tg_n(t)\,dt
 &=\liminf_{T\to\infty}\int f_T(J)\,d\gamma(J)\\
 &\ge\int_{\mathcal G_n}\liminf_{T\to\infty}f_T(J)\,d\gamma(J)\\
 &\ge\gamma(\mathcal G_n)(1-\eta_n)
 \ge {1\over2}(1-\eta_n),                                      \tag{16}
\end{aligned}
\]

which is `(8)`.  The average of a bounded nonnegative function cannot have lower limit larger
than its upper limit along unbounded times, proving `(9)`.  Equation `(10)` follows from
`(2)--(3)`.

Applying the same calculation to `1_(G_n)(J)f_T(J)` proves `(8a)`.  In particular, its restricted
probability is positive at an unbounded sequence of common times.  This stronger restricted form
is what supplies bounded coefficients in Theorem B.

Every target set is finite, so all events in `(6)--(16)` are finite unions or intersections of
continuous overlap inequalities; no selector measurability is hidden in Tonelli's theorem.

## Theorem B -- rational common times and uniformly computable autonomous witnesses

For every `n` covered by Theorem A there is a rational common time

\[
 \widetilde t_n\in\mathbb Q_{>0}                                  \tag{17}
\]

at which

\[
 \boxed{
 \Pr_J\!\left\{
 C_\epsilon(e^{-i\widetilde t_nH_n(J)}\Omega)>s_n\right\}>0.}    \tag{18}
\]

There is also a rational coefficient vector

\[
 \widetilde J_n\in\mathbb Q^{m_n}\cap[-B_n-1,B_n+1]^{m_n}        \tag{19}
\]

such that

\[
 \boxed{
 C_\epsilon(e^{-i\widetilde t_nH_n(\widetilde J_n)}\Omega)>s_n.} \tag{20}
\]

Moreover, the sequence `(J_tilde_n,t_tilde_n)` can be selected by one total algorithm.  After a
common-denominator rescaling, the same endpoint can be written as rational-time evolution under
an integer-coefficient nearest-neighbour two-local Hamiltonian.

### Proof of Theorem B

Choose a common time `t` from `(8a)` for which the set

\[
 A=\{J\in\mathcal G_n:
 \min_{z\in Z_{n,s_n}}d_{\rm tr}(e^{-itH_n(J)}\Omega,z)>2\epsilon\} \tag{21}
\]

has positive Gaussian measure.  This set is the countable union over positive integers `k` of

\[
 A_k=\{J\in A:
 \min_{z\in Z_{n,s_n}}d_{\rm tr}(e^{-itH_n(J)}\Omega,z)
 \ge2\epsilon+1/k\}.                                             \tag{22}
\]

Thus some `A_k` has positive measure.  On the coefficient box,

\[
 \|H_n(J)\|\le m_nB_n.                                          \tag{23}
\]

Duhamel's inequality gives, uniformly for `J in A_k`,

\[
 \|e^{-it'H_n(J)}-e^{-itH_n(J)}\|
 \le |t'-t|m_nB_n.                                              \tag{24}
\]

Choose a positive rational `t_tilde_n` so close to `t` that `(24)` is below `1/(2k)`.  Every
`J in A_k` remains farther than `2 epsilon+1/(2k)>epsilon` from every target at this rational
time.  This proves `(18)`.

Choose one coefficient vector `J in A_k`.  Since `Z_(n,s_n)` is finite,

\[
 \delta=\min_{z\in Z_{n,s_n}}
 d_{\rm tr}(e^{-i\widetilde t_nH_n(J)}\Omega,z)-\epsilon>0.       \tag{25}
\]

The finite-dimensional exponential map and pure-state trace distance are continuous in `J` at
the now fixed rational time.  Hence some open neighbourhood of `J` keeps every distance above
`epsilon`.  Rational coefficient vectors are dense, so that neighbourhood contains a vector
`J_tilde_n` satisfying `(19)--(20)`.

For uniform computability, enumerate all rational pairs satisfying `(17)` and `(19)`.  For each
pair, enumerate the finite word ball of length `s_n`.  Matrix exponentials of rational finite
matrices, the uniformly computable gate endpoints, and their finitely many trace distances are
uniformly computable reals.  Run all candidates and precision levels dovetailed; accept the first
candidate whose certified lower distance from every target exceeds `epsilon`.  Strictness in
`(20)` makes such a certificate appear after finite precision, and existence above makes the
search terminate for every covered `n`.  This defines one total witness-selection algorithm.

Finally, write all coefficients and `t_tilde_n` over one common positive denominator.  Moving the
rational scale between Hamiltonian and time preserves the product `tH` and therefore the endpoint;
clearing the coefficient denominators gives the integer-coefficient form.

## Conjecturing protocol

### C0 -- collision and bandwidth determine phase-completion onset

**Verdict:** `[FALSIFIED]`.  Fix `N>=2` and `0<theta<1`.  Give `N` clustered levels probabilities
`(1-theta)/N` and one tail level probability `theta`.  Their collision

\[
 C={(1-\theta)^2\over N}+\theta^2                                \tag{26}
\]

is independent of the level positions.  Put the clustered energies in `[0,delta]` and the tail
energy at one, choosing the cluster positions so that the projective spectrum has maximal
rational rank.  The projective bandwidth remains one.  If `H_delta` is this Hamiltonian and
`H_0` collapses the cluster to energy zero in the same eigenbasis, then

\[
 \|e^{-itH_\delta}\psi-e^{-itH_0}\psi\|
 \le |t|\,\|H_\delta-H_0\|\le |t|\delta.                         \tag{27}
\]

Thus collision, bandwidth, full support, and maximal projective rank can all remain fixed while
the orbit stays arbitrarily close to a two-phase motion throughout any prescribed finite window.
These invariants cannot supply an effective phase-completion time.

**Positive survivor:** collision controls completed-time capacity, but Brown onset needs an
additional scale-dependent noncommutative word-metric invariant.  Equation `(27)` does not prove
that circuit hardness itself must wait for phase completion.

### C1 -- quenched completed hardness yields a common fixed time

**Verdict:** `[PROVED]`.  The non-effective Hamiltonian-dependent times do not obstruct an
annealed common-time statement.  Fatou plus Tonelli gives `(8)`, and hence the unbounded
fixed-time subsequence `(9)`.

### C2 -- positive-mass fixed-time hardness yields rational witnesses

**Verdict:** `[PROVED]`.  Finite circuit balls are closed and endpoint evolution is continuous.
On a bounded coefficient box, Duhamel continuity is uniform in time.  A positive-measure strict
margin therefore survives at a nearby rational common time; openness in coefficients then gives
rational witnesses.

### C3 -- the witnesses have polynomial-bit descriptions and occur by exponential time

**Verdict:** `[NOT PROVED; EFFECTIVE CORE]`.  Rational density proves finite descriptions but no
useful bit-length bound.  Approximating `H` at a late time costs precision proportional to the
inverse time through Duhamel continuity.  Kronecker--Weyl is qualitative here, so neither
`log t_tilde_n=poly(n)` nor a Brown--Susskind onset scale follows.

### C4 -- nevertheless the witness family is uniformly computable

**Verdict:** `[PROVED]`.  A finite word ball and a strict metric margin make hardness
semi-decidable for each rational candidate.  Existence makes exhaustive dovetailing terminate.
Computability is strictly weaker than efficient constructibility and is stated as such.

## Hostile audit

1. **Not the Brown--Susskind ramp.**  Equations `(8)--(9)` locate an unbounded common-time
   subsequence, not first hard time, linear growth, plateau onset, or recurrence scale.
2. **No polynomial description bound.**  `J_tilde_n` and `t_tilde_n` are finite and uniformly
   computable, but their bit lengths and the search runtime are uncontrolled.
3. **Finite gate dictionary.**  The theorem is ancilla-free and uses a finite computable alphabet.
   Continuously parameterized gates or discarded ancillas require separate metric-entropy bounds.
4. **State, not unitary, complexity.**  The endpoint is one fixed product-input state.  No channel
   or all-input simulation lower bound is claimed.
5. **Exponential, not maximal.**  The proved scale is `(3/2)^n/log n`, below the unrestricted
   `2^n/poly(n)` state scale.
6. **Existence is not typicality at every late time.**  The lower bound in `(8)` is a time average
   of annealed probabilities.  It implies the subsequence `(9)`, not a uniform tail in `t`.
7. **Novelty unverified.**  Fatou, rational density, and exhaustive search are classical.  Candidate
   novelty is their composition with the quenched ordinary-static-local plateau to produce
   `(8)--(10)`, the positive-mass rational common time `(18)`, and the autonomous rational witness
   `(19)--(20)`.
8. **Publication gate remains closed.**  The input phase-incidence theorem is paper-proved but its
   Lean formalization is deferred during corpus refactoring.  Therefore this card is Stage 2 and
   cannot authorize a final manuscript claim under the Lean-only publication rule.

## External separation audit

- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove saturation and recurrence for random local
  circuits and stochastic local-Hamiltonian evolution, not one ordinary time-independent
  nearest-neighbour Hamiltonian or the fixed-time transfer `(8)`:
  <https://arxiv.org/abs/2205.09734>.
- Ippoliti proves a random-matrix spectral ramp for a specially clock-embedded static local
  Hamiltonian.  That is a spectral-form-factor theorem, not an endpoint state-circuit lower bound
  for the Gaussian nearest-neighbour ensemble: <https://arxiv.org/abs/2606.30635>.
- Jia--Wolf construct constant-description families with exact exponential circuit complexity and
  approximate hardness for almost every parameter, using large transcendence degree.  Their result
  is stronger on description length and can reach maximal complexity; it does not place the state
  on autonomous evolution from a fixed product input under an ordinary bounded nearest-neighbour
  two-local Hamiltonian: <https://arxiv.org/abs/2205.06977>.
- General counting proves that high-complexity states exist.  It does not place one on the
  autonomous orbit of a bounded ordinary two-local Hamiltonian from a fixed product input.

The searches found no prior theorem matching `(8)--(10)` or `(18)--(20)`.  This is evidence of
separation, not a complete priority proof.

## Lean status

The refactor-time instruction is superseded.  The Gaussian box `(4)`--`(5)` of Theorem A is formal:
`formal/GaloisForLFunctions/HTGeometry/GaussianBoxMass.lean` (new, umbrella-wired, axiom-clean).

| Card item | Declaration |
|---|---|
| a standard Gaussian is subgaussian with proxy one | `hasSubgaussianMGF_of_standardGaussian` |
| its two-sided tail at level `B` is at most `2exp(-B²/2)` | `measureReal_abs_ge_le_of_standardGaussian` |
| **`(4)`--`(5)`**: with `B² >= 2 log(8m)` the coefficient vector lies in `[-B,B]^m` with probability at least `1/2` | `half_le_measureReal_box` |

No independence between coefficients is used -- only subadditivity -- so the same box works for the
support-weighted ensembles the card allows.

The quenched-to-fixed-time transfer `(15)`--`(16)`, i.e. the whole passage from `(6)` to `(8)` and
`(9)`, is formal as well:
`formal/GaloisForLFunctions/HTGeometry/QuenchedFixedTimeTransfer.lean` (new, umbrella-wired,
axiom-clean).  The event is an arbitrary jointly measurable `S ⊆ Ω × ℝ`; here `Ω` carries the
Gaussian coefficient measure and `S` is the hard set `{(J,t) : C_{2ε}(e^{-itH_n(J)}Ω) > s_n}`.

| Card item | Declaration |
|---|---|
| `(15)`, the window time fraction `f_T(J)` | `quenchedTimeFraction` |
| `(7)`, the fixed-time probability `g_n(t)` | `quenchedFixedTimeProb` |
| the window average `(1/T)∫_0^T g_n` | `quenchedWindowAverage` |
| Tonelli: `∫ f_T dγ = (1/T)∫_0^T g_n` | `lintegral_quenchedTimeFraction_eq` |
| `(6)` in complement form gives `liminf_T f_T(J) >= 1-η_n` | `le_liminf_quenchedTimeFraction_of_limsup_compl_le` |
| Fatou: `liminf_T (1/T)∫_0^T g_n >= c·γ(G_n)` | `le_liminf_quenchedWindowAverage` |
| **`(8)`**: `liminf_T (1/T)∫_0^T g_n >= (1-η_n)/2` from `γ(G_n) >= 1/2` | `half_mul_one_sub_le_liminf_quenchedWindowAverage` |
| **`(9)`**: `limsup_t g_n(t) >= (1-η_n)/2` | `le_limsup_quenchedFixedTimeProb` |
| the unbounded sequence of common deterministic times | `frequently_lt_quenchedFixedTimeProb` |

Fatou's lemma is applied in `ℝ≥0∞` along the filter `atTop` on `ℝ` directly -- no sequence
extraction and no integrability side conditions -- and the split `(8a)` is the same theorem applied
to `S ∩ (G_n × ℝ)`.

What the rest of Theorem A still needs is the deferred input theorem `(6)` itself, i.e. the
completed-phase circuit bound at capture threshold `1-(2ε)²` together with the one-sided
Kronecker--Weyl step and the counting inequality `(14)`.  Theorem B's rational-density and
computable-search layers are untouched.

## Lean progress -- Theorem A's remaining inputs (2026-08-21)

Three new umbrella-wired, axiom-clean modules, plus a non-invasive strengthening of
`HTGeometry/GaussianBoxMass.lean` (its index type is now an arbitrary `Fintype`, and the
quarter-tail estimate that its proof already established is exposed as a theorem; the original
`half_le_measureReal_box` is unchanged and is now a two-line corollary).

`formal/GaloisForLFunctions/HTGeometry/CompletedTimeCircuitDensity.lean` -- **the completed-phase
circuit bound `(6)` at the level of the phase-torus density**:

| Card item | Declaration |
|---|---|
| the counting chain `h_r·r!·(16C/a²)^r ≤ \|Z\|·2^{-r} ≤ 2^{-r/2}` | `replicaMoment_le_two_rpow` |
| **the completed-time density of the complete circuit union is at most `2^{-r/2}`** | `limsup_completedTime_capture_le_two_rpow` |

This is the composition the card calls "the completed-phase circuit bound at capture threshold
`a = 1-(2ε)²` together with one-sided Kronecker--Weyl equidistribution": the Kronecker--Weyl step is
the parent card's `limsup_finiteTorusPhaseProbabilityMeasure_evolutionCapture_le`, applied at a
maximally projective spectrum, and the counting is `CircuitCountingCollisionBound`'s chain.

`formal/GaloisForLFunctions/HTGeometry/GaussianGoodCoefficientSet.lean` -- **`(5)`, `(12)`, `(13)`**:

| Card item | Declaration |
|---|---|
| the law of one Gaussian coefficient | `map_coordinate_centredProductGaussian` |
| **`(5)`**: the bounded, collision-good coefficient set `G_n` | `gaussianGoodSet` |
| **`(12)`+`(13)`**: its complement has Gaussian mass at most `1/2` | `measureReal_gaussianGoodSet_compl_le` |
| **`(5)`**: `γ(G_n) ≥ 1/2` | `half_le_measureReal_gaussianGoodSet` |

`(13)` is `measureReal_box_compl_le_quarter` at `B² ≥ 2log(8m_n)` and `(12)` is the corpus's
`measureReal_collision_pauliEnsemble_zeroProductState_ge_le` at `L = 4`.  Measurability of the
collision functional -- which is genuinely absent, since an eigenbasis is not continuous in the
matrix -- is **not needed**: subadditivity gives `1 ≤ γ(G) + γ(Gᶜ)` for an arbitrary set, so the
two quarter-bounds already force `γ(G) ≥ 1/2`.

`formal/GaloisForLFunctions/HTGeometry/CircuitDictionaryCounting.lean` -- **`(14)`** and the
coordinate change:

| Card item | Declaration |
|---|---|
| **the eigenbasis coordinate change** `⟨u,v⟩ = ∑_j conj⟨e_j,u⟩⟨e_j,v⟩` | `parseval_finiteComplexInner` |
| the padded depth-`s` dictionary has `M^s` members | `card_wordIndex`, `card_wordIndex_le_pow` |
| **`(14)`**: `(s+1)⌈log₂M⌉ ≤ r/4` implies `(s+1)log M ≤ (r/2)log 2` | `circuitCount_log_le` |

### What remains on this card

Only the *instantiation wiring* of Theorem A, and Theorem B.  Concretely: transporting the physical
time interval `[0,T]` of `(6)` to the centred sampling of
`finiteTorusPhaseProbabilityMeasure` (the parent's `finiteTorusPhasePoint` at `A(2u-1)`); packaging
the depth-`s` circuit dictionary as the target family `z` in eigencoordinates through
`parseval_finiteComplexInner`; and then `QuenchedFixedTimeTransfer` already carries `(15)`--`(16)`,
`(8)`, `(8a)` and `(9)` verbatim.  Theorem B's Duhamel step, rational density and dovetailed search
are untouched.
