# Inverse-square static-local laboratory complexity growth law

- **ID:** `inverse-square-static-local-laboratory-complexity-growth-law`
- **Stage:** 2 -- fully proven on paper
- **Type:** theorem / deterministic fixed-error static-Hamiltonian ramp
- **Status:** `[PAPER-PROVED] [LEAN IN PROGRESS] [NOVELTY UNVERIFIED]`
- **Parent:** `../3-formalized/geometric-skeleton-brown-ramp-transfer-law.md`
- **External boundary:** Zlokapa--Allen--Harrow, arXiv:2607.19852
- **Date:** 2026-08-14

## Public sentence

A single unchanging, integrable local Hamiltonian can force quantum circuit complexity to grow
linearly in laboratory time at fixed observational error; neither refreshed randomness nor chaos
is necessary for the first robust ramp.

## Frozen conjecture

For `L >= 1`, place `2L` qubits in disjoint labelled pairs `(A_j,B_j)`, `1 <= j <= L`, and put

\[
 H_L=\sum_{j=1}^L {1\over j^2}|11\rangle\!\langle11|_{A_jB_j}.       \tag{1}
\]

Let `C_epsilon^op(U)` be ancilla-free unitary circuit complexity: minimum number of arbitrary
two-qubit gates, with arbitrary one-qubit gates free, required to produce a unitary `W` satisfying
`||W-U||_op <= epsilon`.

There are absolute explicit constants `epsilon_0,c_0,c_1,c_2>0` such that for every
`0<epsilon<=epsilon_0`, every sufficiently large `L`, and every laboratory time

\[
 c_0\epsilon\le t\le c_1\epsilon L,                              \tag{2}
\]

one has

\[
 \boxed{
 c_2{t\over\epsilon}-1
 \le C_\epsilon^{\rm op}(e^{-itH_L})
 \le \left\lceil {2t\over\epsilon}\right\rceil .}               \tag{3}
\]

The Hamiltonian in `(1)` is positive, diagonal, commuting, time independent, two-local,
degree one, and has operator norm below `2`, uniformly in `L`. The same `H_L` is used at every
time in `(2)`.

## Frontier audit

### Internal

- `[CORPUS]` `GeometricSkeletonBrownRamp.lean` transfers hard endpoint skeletons to continuous
  ramps but does not supply one hard endpoint for an ordinary static Hamiltonian.
- `[LOCAL-RESEARCH]` `computable-static-local-exponential-state-complexity-law.md` supplies
  autonomous hard states at uncontrolled times, not first onset or a laboratory-time ramp.
- `[LOCAL-RESEARCH]` `resolution-time-noncommutativity-static-local-complexity-law.md` proves fixed
  resolution is load-bearing but supplies no rate.
- `[CORPUS]` `StaticOrbitNetBellmanLaw.lean` and `ExactPenaltyCircuitBellman.lean` prove that source
  smoothness and target count cannot establish growth; actual gate locality must enter.

### External

- `[LITERATURE]` Haferkamp et al., arXiv:2106.05305, prove exact linear growth for refreshed random
  circuits, not a robust ramp for one static Hamiltonian.
- `[LITERATURE]` Haferkamp, arXiv:2303.16944, proves constant-error square-root growth and
  exponentially fine-error linear growth for refreshed random circuits.
- `[LITERATURE]` Bohdanowicz--Brandao, arXiv:1710.02625, obtain steady growth for an engineered
  universal static Hamiltonian under computational-complexity assumptions.
- `[LITERATURE]` Zlokapa--Allen--Harrow, arXiv:2607.19852, prove unconditional fixed-error gate and
  query lower bounds. Their static hard instance is a disjoint-pair commuting Hamiltonian at unit
  time; asymptotically late growth in their headline theorem uses fresh blocks through piecewise
  time dependence. Rescaling their static theorem is a useful bridge, not novelty.
- Targeted searches found no two-sided fixed-H inverse-square tail ramp `(3)`. This is evidence of
  separation, not a completed priority audit.

## Conjecture attack

### C0 -- rescaling the 2026 unit-time theorem is the desired result

**Verdict:** `[REDISCOVERED] [BRIDGE]`.

Applying the unit-time theorem to coefficients `t a_j` is immediate. It does not originate a new
mechanism and its trace-distance channel lower bound for `a_j proportional to j^-2` optimizes at a
sublinear power. It cannot headline this route.

### C1 -- inverse-square tails force a deterministic operator-norm ramp

**Verdict:** `[CONJECTURE] [SURVIVES PRELIMINARY ATTACK]`.

The upper and lower mechanisms use the same tail at different logical levels:

1. truncating after `K` pairs costs `K` gates and leaves operator error at most
   `t sum_(j>K)j^-2 <= t/K`;
2. if a `G`-gate circuit leaves many tail pairs wholly untouched by two-qubit gates, a four-state
   mixed phase difference detects a subset whose accumulated phase exceeds the error budget;
3. one two-qubit gate touches at most two labelled pairs, so suppressing every such witness costs
   `Omega(t/epsilon)` gates.

The mechanism survives phase wrapping because the lower witness is selected from a moving tail
block where every individual phase is small; no condition is imposed on the wrapped head.

## Exact open core

`[OPEN CORE]` Close the four-state witness with explicit constants, including:

1. factorization of a circuit's diagonal amplitudes on every pair untouched by all two-qubit gates;
2. operator-norm-to-entrywise transfer;
3. a finite greedy subset with accumulated phase in a non-wrapping interval;
4. the inverse-square block count and tail truncation upper bound.

No probability, ensemble, spectral gap, asymptotic computation, or complexity assumption may enter.

## Stronger connected conjecture selected after attack

The disconnected-pair statement is mathematically sufficient but physically weaker than necessary. Put the
`2L` qubits on one path. Write `P_(r,r+1)=|11><11|` on adjacent sites and define

\[
 \widehat H_L=
 \sum_{j=1}^L {1\over j^2}P_{2j-1,2j}
 +{1\over L^3}\sum_{j=1}^{L-1}P_{2j,2j+1}.                       \tag{4}
\]

The second sum connects consecutive labelled pairs. All terms remain positive, diagonal and commuting. The
interaction graph is the full path, locality is nearest-neighbour, and

\[
 \|\widehat H_L\|_{\rm op}
 =\sum_{j=1}^L j^{-2}+{L-1\over L^3}<3.                         \tag{5}
\]

The strengthened frozen claim is: for `0<epsilon<=1/100`, `L>=2`, and

\[
 1024\pi\epsilon\le t\le {\epsilon L\over2},                   \tag{6}
\]

one has

\[
 \boxed{
 \left\lfloor{t\over128\pi\epsilon}\right\rfloor
 \le C_\epsilon^{\rm op}(e^{-it\widehat H_L})
 \le \left\lceil{2t\over\epsilon}\right\rceil .}              \tag{7}
\]

This is the claim sent through the proof gate. Equation `(3)` is retired in favour of `(7)`.

## Complete paper proof

### Lemma 1 -- inverse-square tail

For every integer `K>=1`,

\[
 \sum_{j=K+1}^L{1\over j^2}
 \le\sum_{j=K+1}^L{1\over j(j-1)}
 ={1\over K}-{1\over L}\le {1\over K}.                          \tag{8}
\]

The first inequality uses `j(j-1)<=j^2`; the equality telescopes. Taking `K=1` and adding the first
term gives `sum_(j=1)^L j^-2<2`, which proves `(5)`.

### Lemma 2 -- upper ramp

Put `K_+=ceil(2t/epsilon)`. Condition `(6)` gives `K_+<=L`. Implement exactly the first `K_+`
matching-edge phase gates and omit every later matching edge and every bridge edge. Since all terms commute,
the omitted Hamiltonian `R` is positive diagonal and

\[
 \|R\|_{\rm op}
 \le {1\over K_+}+{L-1\over L^3}.                               \tag{9}
\]

For self-adjoint `R`,

\[
 \|e^{-itR}-I\|_{\rm op}\le t\|R\|_{\rm op}.                   \tag{10}
\]

Because `K_+>=2t/epsilon` and `t<=epsilon L/2`, equations `(9)--(10)` give

\[
 t\|R\|_{\rm op}
 \le {\epsilon\over2}+{t\over L^2}
 \le {\epsilon\over2}+{\epsilon\over2L}<\epsilon.             \tag{11}
\]

Each retained exponential is one arbitrary two-qubit gate. Thus the right inequality in `(7)` holds.

### Lemma 3 -- four-amplitude phase witness

Let `U,W` be unitaries and suppose `||W-U||_op<=epsilon`. Every matrix entry then differs by at most
`epsilon`, while every diagonal entry of either unitary has modulus at most one.

Suppose four basis configurations `x_(ab)`, `a,b in {0,1}`, obey

\[
 U_{00,00}=U_{01,01}=U_{10,10}=1,
 \qquad U_{11,11}=e^{-i\phi},                                  \tag{12}
\]

and the approximant obeys the factorization identity

\[
 W_{00,00}W_{11,11}=W_{01,01}W_{10,10}.                        \tag{13}
\]

Insert and subtract the two products in `(13)`. The product rule and the unit diagonal-entry bounds give

\[
 |e^{-i\phi}-1|\le4\epsilon.                                  \tag{14}
\]

For `0<=phi<=pi`, chord length and concavity of sine give

\[
 |e^{-i\phi}-1|=2\sin(\phi/2)\ge {2\phi\over\pi}.              \tag{15}
\]

Hence `(12)--(13)` are impossible whenever `3pi epsilon<=phi<=pi`, because `(15)` is at least
`6epsilon>4epsilon`.

### Lemma 4 -- untouched pairs factor

Consider an ancilla-free circuit with arbitrary one-qubit gates and `G` arbitrary two-qubit gates. Call a
labelled pair `j` touched when at least one of its two qubits participates in a two-qubit gate. One gate touches
at most two labelled pairs, hence at most `2G` pairs are touched.

If `S` is a set of untouched pairs, every gate on a qubit belonging to `S` is one-qubit. Gates on disjoint
supports commute, so the circuit unitary, after regrouping tensor factors, has the form

\[
 W=\left(\bigotimes_{j\in S}A_j\otimes B_j\right)\otimes W_{S^c}. \tag{16}
\]

Let `x_(ab)` put value `a` on every first qubit of a pair in `S`, value `b` on every second qubit, and zero
elsewhere. Expanding the four diagonal amplitudes of `(16)` proves `(13)` exactly, including when some
diagonal factor vanishes.

### Lemma 5 -- a moving tail block contains a detected subset

Put

\[
 K=\left\lfloor{t\over128\pi\epsilon}\right\rfloor.            \tag{17}
\]

The lower bound in `(6)` gives `K>=8`. The upper bound gives `8K<=L`. Suppose for contradiction that
`G<K`. In the block

\[
 B_K=\{j:4K<j\le8K\},                                         \tag{18}
\]

there are `4K` labelled pairs, fewer than `2K` of which are touched. Thus the untouched subset `T` has more
than `2K` elements. Its total matching-edge phase obeys

\[
 t\sum_{j\in T}{1\over j^2}
 > {2Kt\over(8K)^2}
 ={t\over32K}\ge4\pi\epsilon.                                 \tag{19}
\]

Every individual phase in this block obeys

\[
 {t\over j^2}<{t\over16K^2}
 <8\pi\epsilon{K+1\over K^2}
 \le2\pi\epsilon,                                            \tag{20}
\]

where `(17)` gives `t<128pi epsilon(K+1)` and `K>=8` gives the last inequality.

Add untouched elements greedily until their matching phase first reaches `3pi epsilon`. Equations
`(19)--(20)` produce a subset `S subset T` with

\[
 3\pi\epsilon\le
 t\sum_{j\in S}j^{-2}\le5\pi\epsilon.                         \tag{21}
\]

For the four configurations from Lemma 4, the bridge terms vanish except possibly on the `11`
configuration. Their total added phase is nonnegative and at most

\[
 t{L-1\over L^3}\le{\epsilon\over2L}\le{\epsilon\over4}.      \tag{22}
\]

Consequently the complete phase `phi` in `(12)` satisfies

\[
 3\pi\epsilon\le\phi\le5\pi\epsilon+\epsilon/4<\pi            \tag{23}
\]

for `epsilon<=1/100`. Lemma 4 gives `(13)`, while Lemma 3 makes `(23)` impossible. Therefore `G>=K`,
proving the left inequality in `(7)`.

### Theorem

Lemmas 1--5 prove `(5)` and `(7)` for the single explicit Hamiltonian `(4)` at every time in the full
laboratory window `(6)`. No Hamiltonian redraw, fresh gate randomness, computational-complexity assumption,
spectral genericity, or asymptotic time average occurs.

## Hostile mathematical audit

1. **Does complexity genuinely grow?** Yes in the operational theorem sense: the same fixed-error complexity
   is trapped between two positive linear functions of the same laboratory time throughout `(6)`. This is not
   a lower envelope placed beneath an already uncontrolled plateau.
2. **Is growth imported as a premise?** No. Circuit locality supplies only `(16)`; inverse-square tail geometry
   and operator error force the rate.
3. **Does phase wrapping kill monotonicity?** No. Head phases may wrap arbitrarily. The witness moves to the
   block `(18)`, whose individual phases satisfy the non-wrapping estimate `(20)`.
4. **Is Hamiltonian ordinary?** It is a connected nearest-neighbour two-local spin-chain Hamiltonian with no
   clock, time dependence, disorder redraw, nonlocal term, or oracle. It is inhomogeneous and integrable; both
   limitations must be explicit.
5. **Does theorem prove Brown-scale growth?** No. Window and attained complexity are linear in `L`, not
   exponential in qubit number. This is a first unconditional static-H laboratory ramp and a counterexample to
   necessity of chaos, not Brown--Susskind closure.
6. **Metric dependence?** Essential. Result uses global operator norm and ancilla-free unitary circuits. State
   complexity, local-observable error, diamond-norm channels with discarded ancillas, and fault-tolerant gate
   sets require separate transfer theorems.
7. **Weak bridges?** Bridge strength `L^-3` establishes connected locality while staying below fixed resolution
   on the proved window. The ramp is carried by matching interactions, not by bridge transport. Claim must not
   be described as ballistic information propagation on the chain.
8. **Priority?** Exact parent mechanisms overlap recent Hamiltonian-simulation lower bounds. Candidate new
   content is the one-draw continuous inverse-square tail ramp, moving non-wrapping witness, and connected
   fixed-H two-sided law. Priority remains unverified pending a full citation graph and expert review.

## Proof status after hostile audit

`[PAPER-PROVED] [NOVELTY UNVERIFIED]`. The dependency-closed proof above closes the former open core. Move the
exact theorem to Stage 2 before Lean formalization; no stronger physical interpretation is authorized.
