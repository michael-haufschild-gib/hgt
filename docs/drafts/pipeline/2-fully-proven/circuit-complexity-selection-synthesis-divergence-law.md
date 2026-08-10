# Circuit-complexity selection--synthesis divergence law

- **ID:** `circuit-complexity-selection-synthesis-divergence-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** universal information identity / gate-relative rate--distortion law / recurrence split
- **Parents:** `gate-walk-green-bellman-tropicalization-law.md`,
  `fixed-time-phase-graph-sobolev-blindness-law.md`,
  `cubic-phase-seeded-static-local-full-scale-plateau-law.md`
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN DEFERRED DURING REFACTOR]`
- **Date:** 2026-08-10

## Public sentence

Knowing **which** quantum state is wanted and knowing **how to make it** are exactly different
currencies.  Circuit length is the sum of information selecting a gate word and the word
distribution's divergence from the physical local-gate production law.  An autonomous Hamiltonian
can therefore visit states requiring exponentially many gates even when only logarithmically many
bits locate those states along the orbit.

## 1. Why another entropy is needed

The parent phase-graph law proves two facts that seem contradictory only if description and
preparation are conflated.

1. At fixed time an `O(n)`-parameter static-local ensemble has an arbitrary metric codebook with
   only `O(n^2)` index bits through exponential time.
2. Existing static-local plateau theorems contain continuous orbit blocks whose every state has
   `Omega(2^n/log n)` approximate circuit complexity.

Ordinary Shannon rate--distortion charges the index identifying a reproduction point.  It does not
charge whether that point is itself physically producible by a short local circuit.  The missing
quantity is not a second ad hoc complexity measure.  It is relative entropy to the actual local
gate-word prior.

The theorem below gives an exact decomposition, not an analogy.  Its information-theoretic engine
is classical; its role is to identify which summand must carry static Hamiltonian complexity after
the source-entropy and Haar-mixing routes fail.

## 2. Local gate-word prior

Let `Gamma` be a finite gate alphabet with cardinality `M>=2`, let `Gamma^*` be its finite words,
and let `|w|` denote word length.  Fix `0<a<1` and define the geometrically killed local-word prior

\[
 \boxed{
 \pi_a(w)=(1-a)\left({a\over M}\right)^{|w|}.}                         \tag{1}
\]

This is a probability law because

\[
 \sum_{w\in\Gamma^*}\pi_a(w)
 =(1-a)\sum_{\ell\ge0}M^\ell(a/M)^\ell=1.                              \tag{2}
\]

Let `(X,mu)` be any standard Borel probability space of target states.  A stochastic circuit
encoder is a Markov kernel `Q(dw|x)` on `Gamma^*`.  Write `W` for its output word, `q` for the
marginal law of `W`, and use natural logarithms throughout.  Assume `E|W|<infinity`.

The discrete output then has finite entropy.  Indeed, conditional on `|W|=ell` there are at most
`M^ell` words, so

\[
 H(W)\le H(|W|)+\mathbb E|W|\log M<\infty,                              \tag{3}
\]

where a nonnegative integer law with finite mean has finite entropy.  Thus all terms below are
well-defined and finite.

## 3. Exact two-currency decomposition

### Theorem A -- selection information plus synthesis divergence equals gate cost

Every stochastic circuit encoder with finite expected word length satisfies

\[
 \boxed{
 \log(M/a)\,\mathbb E|W|
 =H(W\mid X)+I(X;W)+D(q\|\pi_a)+\log(1-a).}                            \tag{4}
\]

Equivalently, since `H(W|X)+I(X;W)=H(W)`,

\[
 \boxed{
 -\mathbb E\log\pi_a(W)
 =H(W)+D(q\|\pi_a).}                                                   \tag{5}
\]

For a deterministic encoder, `H(W|X)=0`, and `(4)` becomes

\[
 \boxed{
 \log(M/a)\,\mathbb E|W|
 =I(X;W)+D(q\|\pi_a)+\log(1-a).}                                      \tag{6}
\]

The two nonconstant terms have operationally different meanings:

- `I(X;W)` is **selection information**: how many nats the word reveals about which target was
  requested;
- `D(q||pi_a)` is **synthesis divergence**: how atypical the selected word population is under
  independent geometrically killed local-gate production.

### Proof

Equation `(1)` gives the pointwise identity

\[
 -\log\pi_a(w)=-\log(1-a)+|w|\log(M/a).                                \tag{7}
\]

Averaging proves

\[
 -\mathbb E\log\pi_a(W)
 =-\log(1-a)+\log(M/a)\mathbb E|W|.                                    \tag{8}
\]

On the other hand, the definition of relative entropy gives

\[
 \begin{aligned}
 H(W)+D(q\|\pi_a)
 &=-\sum_wq(w)\log q(w)
   +\sum_wq(w)\log{q(w)\over\pi_a(w)}\\
 &=-\sum_wq(w)\log\pi_a(w).
 \end{aligned}                                                         \tag{9}
\]

Equations `(8)--(9)` prove `(5)` and `(4)` after using the mutual-information chain rule.  A
deterministic encoder has zero conditional entropy, proving `(6)`. `square`

### Corollary A.1 -- exact boundary of every entropy-only complexity law

For a deterministic encoder,

\[
 -\log(1-a)+\log(M/a)\mathbb E|W|=I(X;W)                               \tag{9a}
\]

holds if and only if

\[
 \boxed{q=\pi_a.}                                                       \tag{9b}
\]

### Proof

By `(5)--(6)`, the difference between the two sides of `(9a)` is exactly
`D(q||pi_a)`.  Relative entropy vanishes exactly when its two probability laws agree. `square`

Thus ordinary source information accounts for all preparation cost only in the matched-prior
regime.  Static Hamiltonian dynamics is not generated by the local random-circuit prior, so an
entropy-only identification has an explicit correction term rather than a philosophical caveat.

### Theorem B -- expected approximate circuit complexity has the exact split

Let a finite alphabet act continuously on a metric state space from one fixed reference state.
Order all words first by length and then lexicographically.  For `epsilon>0`, suppose the robust
word complexity `C_epsilon(x)` is finite `mu`-almost surely and integrable.  Let `w_*(x)` be the
first shortest word whose endpoint is within `epsilon` of `x`.

Then `w_*` is a measurable deterministic encoder, `|w_*(x)|=C_epsilon(x)`, and

\[
 \boxed{
 \log(M/a)\,\mathbb E C_\varepsilon(X)
 =I(X;W_*)+D(q_*\|\pi_a)+\log(1-a).}                                  \tag{10}
\]

### Proof

For each word `w`, its selection cell is its closed `epsilon`-tube minus the countable union of all
earlier qualifying word tubes.  It is Borel, so `w_*` is measurable.  Minimality gives the length
identity.  Apply `(6)`. `square`

Equation `(10)` is the promised ontological reversal.  Expected circuit complexity is not an
entropy of the state source.  It is a preparation cross-entropy, which splits into source-selection
information and mismatch from local gate production.

## 4. Exact gate-relative rate--distortion functional

For a target `x`, let

\[
 G_\varepsilon(x)
 =\{w:d(W_w\chi,x)\le\varepsilon\},
 \qquad
 \mathcal G_{a,\varepsilon}(x)=\pi_a(G_\varepsilon(x)).                 \tag{11}
\]

The second expression is exactly the hard killed gate-walk Green function of the first parent.

### Theorem C -- hard Green surprisal is the exact preparation-relative distortion rate

Among all stochastic encoders which reproduce `x` within `epsilon` with probability one,

\[
 \boxed{
 \inf_{Q:\,Q(G_\varepsilon(x))=1}
 D(Q\|\pi_a)
 =-\log\mathcal G_{a,\varepsilon}(x).}                                \tag{12}
\]

Both sides are interpreted as `+infinity` when `G_epsilon(x)` is empty.

The optimizer is the conditioned gate prior

\[
 Q_x^*(w)={\pi_a(w)\mathbf1_{G_\varepsilon(x)}(w)
             \over\mathcal G_{a,\varepsilon}(x)}.                      \tag{13}
\]

For a random source `X`, allowing a separate encoder conditional on each target gives

\[
 \boxed{
 \inf_{Q:\,Q(G_\varepsilon(X)\mid X)=1}
 \mathbb E_XD(Q(\cdot\mid X)\|\pi_a)
 =\mathbb E_X[-\log\mathcal G_{a,\varepsilon}(X)].}                    \tag{14}
\]

### Proof

For any `Q` supported on `G=G_epsilon(x)`, expand relative entropy against the conditional prior:

\[
 D(Q\|\pi_a(\cdot\mid G))
 =D(Q\|\pi_a)+\log\pi_a(G).                                           \tag{15}
\]

Nonnegativity proves `(12)`, with equality exactly at `(13)`.  Because the word space is countable
and every endpoint tube is Borel, the conditioned kernel `(13)` is measurable wherever its
denominator is positive.  Integrate the pointwise identity to obtain `(14)`. `square`

Thus the Green function is not merely a convenient Bellman certificate.  Its negative logarithm
is exactly the zero-distortion relative-entropy cost of forcing the physical gate process to hit
the requested state.

Two immediate bounds recover growth and recurrence in this new variable.  If `s>=0` is an integer
and `C_epsilon(x)>s`, every successful word has length at least `s+1`, hence

\[
 \boxed{
 -\log\mathcal G_{a,\varepsilon}(x)
 \ge(s+1)\log(1/a).}                                                   \tag{16}
\]

If one successful word has length `b`, then

\[
 \boxed{
 -\log\mathcal G_{a,\varepsilon}(x)
 \le-\log(1-a)+b\log(M/a).}                                           \tag{17}
\]

Equation `(16)` uses only the geometric length tail
`pi_a{|w|>=s+1}=a^(s+1)`; `(17)` keeps the mass of one witness word.

## 5. Low information can force large synthesis divergence

### Theorem D -- curve codebooks separate selection from preparation

Let `gamma:[0,W]->X` be `v`-Lipschitz.  Fix `epsilon,delta>0` and suppose

\[
 C_{\varepsilon+\delta}(\gamma(t))\ge S
 \qquad(0\le t\le W),                                                   \tag{18}
\]

while every orbit point has finite `epsilon`-complexity.  There is a deterministic encoder which
reproduces every `gamma(t)` within `epsilon+delta`, uses at most

\[
 N\le\left\lceil{vW\over\delta}\right\rceil+1                          \tag{19}

distinct circuit words, and obeys

\[
 \boxed{I(T;W)\le\log N,}                                               \tag{20}
\]

but

\[
 \boxed{
 D(q\|\pi_a)
 \ge S\log(M/a)-\log N-\log(1-a).}                                    \tag{21}
\]

Here `T` may have any probability law on `[0,W]`, and the encoder is obtained from one fixed time
mesh independent of that law.

### Proof

Choose a time mesh of spacing at most `delta/v`, with the constant-curve case treated by one point.
For each mesh point `t_i`, choose a shortest `epsilon`-word `w_i`.  Every time lies within state
distance `delta` of one mesh state, so the corresponding `w_i` reproduces it within
`epsilon+delta`.  The output has at most `N` values, proving `(19)--(20)`.

Because `C_epsilon>=C_(epsilon+delta)`, every selected word has length at least `S`.  Hence
`E|W|>=S`.  For this deterministic encoder, `(5)` gives

\[
 D(q\|\pi_a)
 =-\log(1-a)+\log(M/a)\mathbb E|W|-H(W).
\]

Use `H(W)=I(T;W)<=log N` to prove `(21)`. `square`

The theorem proves more than “description length differs from circuit complexity.”  It identifies
the exact missing term and forces it to be large: when few index bits select only hard
reproductions, their marginal law must be exponentially atypical under local gate production.

## 6. Ordinary static-local plateau and recurrence

Apply Theorem D to the full-scale continuous plateau in
`cubic-phase-seeded-static-local-full-scale-plateau-law.md`.  For every sufficiently large `n`, its
paper theorem supplies:

- `D=2^n`;
- one bounded nearest-neighbour time-independent two-local Hamiltonian and one polynomially
  preparable seed;
- a one-unit interval `[A,A+1]` on which every state has
  `epsilon_-`-complexity greater than

\[
 s_n=\Omega(D/\log M_n);                                                \tag{22}
\]

- orbit speed at most `v_n=sqrt(12n-9)`;
- arbitrarily accurate later recurrence to the polynomially preparable seed.

Fix `0<delta<epsilon_-`, put `epsilon=epsilon_--delta`, and choose `a=1/M_n`.  Theorem D gives one
encoder for the entire plateau segment with

\[
 \boxed{I(T;W)=O(\log n),}                                               \tag{23}
\]

because `N<=ceil(sqrt(12n-9)/delta)+1`, while

\[
 \boxed{D(q\|\pi_{1/M_n})=\Omega(D)=\Omega(2^n).}                       \tag{24}
\]

At a later recurrence, one fixed word of length `b_n=O(n^3)` preparing the seed reproduces the
returned state at the enlarged recurrence tolerance.  Its selector information is zero and its
synthesis divergence is

\[
 \boxed{
 D(\delta_{w_0}\|\pi_{1/M_n})
 =-\log(1-1/M_n)+2b_n\log M_n
 =\operatorname{poly}(n).}                                             \tag{25}
\]

Therefore one ordinary autonomous trajectory has an exact information--preparation separation:

\[
 \boxed{
 \begin{array}{c|c|c}
 &\text{selection information}&\text{synthesis divergence}\\ \hline
 \text{full plateau segment}&O(\log n)&\Omega(2^n)\\
 \text{later recurrence}&0&\operatorname{poly}(n).
 \end{array}}                                                          \tag{26}
\]

The plateau theorem used here is presently paper-proved, not Lean-proved.  Accordingly `(22)--(26)`
remain Stage 2 and are barred from a final manuscript until that parent and this composition pass
the formal gate.

## 7. Conjecturing / failure / replacement loop

### C0 -- Brown complexity is the information needed to specify the state

**Verdict:** `[FALSIFIED]` by the phase-graph cover law and Theorem D.

A polynomial-size index can select approximants to a whole short orbit segment whose every point
has near-maximal circuit complexity.

### C1 -- charge ordinary rate--distortion codebook size instead

**Verdict:** `[FALSIFIED AS THE PHYSICAL COST]`.

An arbitrary reproduction centre may itself require exponentially many gates.  Codebook
cardinality charges selection but not synthesis.

### C2 -- use preparation-weighted rate--distortion

**Verdict:** `[REDISCOVERED AS GENERAL INFORMATION THEORY; EXACT CIRCUIT SPECIALIZATION PROVED]`.

Relative-entropy coding with a reproduction prior and Gibbs variational formulas are classical.
Theorems A--C specialize them to the actual killed local-gate process and identify the hard Green
surprisal as exact preparation-relative distortion cost.

### C3 -- complexity has two operational currencies

**Verdict:** `[PAPER-PROVED AS AN IDENTITY; PHYSICAL UNIVERSALITY CLAIM OPEN]`.

Equation `(10)` proves the split for every integrable approximate-complexity source.  Equations
`(23)--(26)` show that autonomous static complexity can reside almost entirely in synthesis
divergence.  By contrast, the generating encoder for a source sampled from the same gate prior has
word marginal `pi_a` and hence zero synthesis divergence; endpoint collisions merely move cost
between conditional randomness and selection information.

The corrected live conjecture is frozen, with its exact quantifiers and falsifiers, in
`../1-in-progress/synthesis-divergence-brown-law.md`:

> **First-entrance synthesis-divergence Brown law.**  Before saturation and outside one common
> recurrence/carrier filtration, ordinary chaotic fixed-local Hamiltonians increase the
> first-arrival surprisal under the local gate prior at a rate proportional to physical time; the
> plateau is sustained first-arrival rarity and recurrence is its exact collapse.

This is not counted as proved.  Raw endpoint Green mass is now retired as the final primitive
because it mixes first preparation with post-hit returns.  The exact `[OPEN CORE]` is a Brown-scale
directional estimate for the first-entrance equilibrium potential on the geometric time skeleton.
Unlike global Haar distance, source entropy, or a positive global moment, this primitive retains
local preparation geometry while permitting permanent non-Haar locality.

## 8. Universal shadow map

| Existing fact or obstruction | Shadow of the selection--synthesis law |
|---|---|
| Random-circuit linear growth | The generating encoder has matched word marginal and `D=0`; its gate cost lies in `H(W|X)+I(X;W)`. |
| Static Hamiltonian low parameter entropy | A short orbit segment admits a deterministic selector with `I=O(log n)` by Theorem D. |
| Static full-complexity plateau | Synthesis divergence becomes `Omega(D)` by `(24)`. |
| Permanent non-Haar locality | Large marginal divergence is compatible with maximal preparation cost; Haar convergence is unnecessary. |
| Gate-walk Green/Bellman law | Raw `-log G` is a preparation-relative endpoint rate, but the entrance--return law splits off its post-hit recurrence resolvent. |
| First-entrance capacity law | Loop-free surprisal is a prefix-free KL cost; its expectation is capacity plus one directional non-Haar discrepancy. |
| Positive-replica entropy price | Averaging over words measures cross-entropy and necessarily pays gate-prior rarity. |
| Two-memory orthogonality | Static--circuit alignment is a moment-level diagnostic for gate collision; it is not by itself equivalent to synthesis divergence. |
| Quantum recurrence | One short witness collapses preparation surprisal by `(17)` and `(25)`. |
| Black-hole interior/complexity proposal | If the holographic complexity dictionary is valid, continued interior growth tracks synthesis cost after ordinary state information has saturated. This is an interpretation, not a proved gravity theorem. |

## 9. Hostile audit

1. **The information identity is classical.**  Cross-entropy decomposition, KL chain rules and
   conditioned-prior minimization are standard.  No abstract information-theory novelty is claimed.
2. **The circuit application is exact but priority is provisional.**  Targeted searches found no
   source stating `(10)`, `(12)`, and the static plateau separation `(26)` for a local gate-word
   prior.  Negative search is not proof of priority.
3. **This does not prove the Brown ramp.**  It replaces the wrong entropy primitive and isolates the
   required lower-tail object.  The conjectural linear rate remains open.
4. **The split depends on the physical gate prior.**  Changing alphabet, gate costs, ancillas,
   measurements, or postselection changes `pi`.  That dependence is operationally required, not a
   universality defect.
5. **Minimal-word measurability is explicit.**  Countability and Borel endpoint tubes give the
   selector in Theorem B.  No hidden measurable-choice theorem is used.
6. **Continuous source entropy is not used.**  Theorem D bounds the discrete word-selector
   information directly by its finite image.
7. **Black-hole statement is conditional.**  Complexity--volume/action remains a holographic
   proposal.  The proved theorem concerns finite quantum systems and local gate processes only.
8. **Lean status.**  The exact finite/countable probability identities and plateau composition must
   be formalized after the active corpus refactor before any final paper uses them as AI proof.
9. **Free energy does not make the ramp easy.**  First-entrance surprisal is bilipschitz-equivalent
   to complexity at fixed fugacity.  Renaming the lower bound is not novelty.  The advance is the
   exact separation of first preparation from recurrence and of directional capacity matching from
   global Haar convergence; the static Brown directional estimate remains the hard theorem.

## 10. External boundary checked

- Classical entropy-constrained vector quantization and rate--distortion with reproduction costs
  already distinguish index entropy from reproduction penalties; see, for example,
  arXiv:1507.08349.  The general KL algebra in Theorems A--C is a `[BRIDGE]`, not a priority claim.
- Brown and Susskind, *Second law of quantum complexity*, relate circuit complexity to an auxiliary
  positional entropy and black-hole uncomplexity (arXiv:1701.01107).  Their proposal does not give the local-word
  prior decomposition `(10)` or the static low-information/high-synthesis separation `(26)`.
- Haferkamp et al., *Linear growth of quantum circuit complexity*, prove the random-circuit growth
  law (arXiv:2106.05305).  Their evolving source is generated by fresh random gates; they do not prove the autonomous
  static synthesis-divergence law conjectured above.
- Guo, Sasieta and Swingle, *Complexity is not Enough for Randomness*, separate complexity and
  design generation in Brownian systems (arXiv:2405.17546).  The present exact split is compatible with that result
  but concerns preparation-prior divergence for static dynamics.

## 11. Lean plan after refactor

1. geometric word prior normalization `(1)--(2)` on finite words;
2. finite/countable cross-entropy identity `(4)--(10)`;
3. conditioned-prior KL minimization `(12)--(15)`;
4. Green tail and one-witness bounds `(16)--(17)`;
5. finite-mesh curve encoder and divergence lower bound `(18)--(21)`;
6. composition with the eventual Lean version of the cubic static-local plateau.
