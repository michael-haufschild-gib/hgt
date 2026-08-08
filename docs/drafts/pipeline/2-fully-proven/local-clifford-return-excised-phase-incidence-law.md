# Local-Clifford return-excised phase-incidence law

- **ID:** `local-clifford-return-excised-phase-incidence-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** quenched growing-replica theorem / ordinary static-local complexity plateau
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, O3--O4 interface
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED] [LEAN DEFERRED]`
- **Date:** 2026-08-08

## Public sentence

For a typical fixed nearest-neighbour Gaussian spin Hamiltonian and any fixed finite local gate
alphabet, one product state spends all but an exponentially small fraction of completed time
beyond every circuit family of depth
`Omega((3/2)^n / log n)`; earlier returns are charged once, not once per circuit.

This is a rigorous plateau-occupation theorem. It is not a first-hard-time or linear-growth theorem.

## Frontier closed by this card

The return-excised incidence laws reduce complete target capture to an occupied replica image, but
leave its quenched growing-replica moment unbounded. Minimum spectral-gap anti-concentration and raw
observer-Jacobian determinants are already retired. The missing bound must:

1. hold after one Hamiltonian is drawn and then kept fixed;
2. absorb every target before estimating probability;
3. retain distinct source sheets rather than quotienting equal endpoints;
4. depend on actual occupied replica image, not circuit-description count; and
5. pay a permitted return set once.

This card proves that theorem on the completed spectral phase orbit. It then supplies an explicit
ordinary bounded-degree static-local ensemble for which the controlling spectral collision is
exponentially small with high probability. The remaining Brown--Susskind obstruction is effective
finite-time growth: this theorem gives no bound on the first time at which the plateau is reached.

## Abstract quenched theorem

Let `H` be self-adjoint on `C^D`, with a simple orthonormal eigenbasis
`e_1,...,e_D`. Fix a unit input `psi`, put

\[
 p_j=|\langle e_j,\psi\rangle|^2,
 \qquad
 C_H(\psi)=\sum_{j=1}^D p_j^2,                       \tag{1}
\]

and absorb the fixed coefficient phases into the phase variables. On the full spectral phase torus
`T^D` define

\[
 \Phi_H(\zeta)=\sum_{j=1}^D\sqrt{p_j}\,\zeta_j e_j,
 \qquad |\zeta_j|=1,                                 \tag{2}
\]

with normalized Haar measure `m_H`.

Let `Z` be any finite family in the closed unit ball containing at least one nonzero vector, let
`r>=1`, and let

\[
 h_r(Z)=\dim_{\mathbb C}\operatorname{span}
 \{z^{\otimes r}:z\in Z,\ z\ne0\}.                  \tag{3}
\]

For `0<a<=1`, put

\[
 E_a(Z)=\{\zeta:\exists z\in Z,
          |\langle\Phi_H(\zeta),z\rangle|^2\ge a\}. \tag{4}
\]

Let `Q` be any measurable original shortcut event and let `R subset T^D` be any measurable,
independently fixed return set such that

\[
 Q\setminus R\subseteq E_a(Z).                        \tag{4a}
\]

Thus every original shortcut which is not charged as a return is captured by one of the actual
return-removed residual targets in `Z`. With `Phi_L` defined below, let `S_r(Z)` be the span in
`(3)` and define the surviving light-source incidence carrier

\[
 U_{r,R}^{L}(Z)=\operatorname{span}
 \{P_{S_r(Z)}\Phi_L(\zeta)^{\otimes r}:\zeta\notin R\},
 \qquad
 \iota_{r,R}^{L}(Z)=\dim_{\mathbb C}U_{r,R}^{L}(Z).   \tag{4b}
\]

Then

\[
 \boxed{
 m_H(Q)
 \le m_H(R)+\iota_{r,R}^{L}(Z)\,r!
       \left({16C_H(\psi)\over a^2}\right)^r .}
                                                               \tag{5}
\]

The same statement holds for an `H`-dependent target family `Z_H`, pointwise for every fixed `H`.
No measurability of the selector `H -> Z_H` is used. In applications `R` must be selected by a
target-independent recurrence rule; choosing `R=E_a(Z)` is circular and conveys no information.

### Exact heavy-sector form

Set

\[
 \tau={4C_H(\psi)\over a},\qquad
 A=\{j:p_j>\tau\},                                   \tag{6}
\]

and split `Phi_H=Phi_A+Phi_L` into the spectral coordinates in `A` and its complement. Then

\[
 \|\Phi_A\|^2\le {a\over4},                           \tag{7}
\]

and every capture in `(4)` forces

\[
 |\langle\Phi_L(\zeta),z\rangle|^2\ge {a\over4}      \tag{8}
\]

for at least one actual occupied target `z`. Equation `(5)` is obtained by projecting the occupied
vectors `z^(tensor r)` into the least surviving light-source carrier `(4b)`, then applying one
determinant-optimal design there. Thus

\[
 \iota_{r,R}^{L}(Z)\le h_r(Z),                        \tag{8a}
\]

and the heavy spectral sector is removed once before the exact source--target incidence is
estimated.

## Dependency-closed proof of the abstract theorem

### Step 1 -- one common heavy spectral sector

From `(6)`,

\[
 \sum_{j\in A}p_j
 \le {1\over\tau}\sum_{j\in A}p_j^2
 \le {C_H(\psi)\over\tau}={a\over4},                 \tag{9}
\]

which proves `(7)`. If `z` is in the unit ball and
`|<Phi_H,z>|>=sqrt(a)`, then

\[
 |\langle\Phi_L,z\rangle|
 \ge \sqrt a-\|\Phi_A\|\,\|z\|
 \ge {\sqrt a\over2},                                \tag{10}
\]

proving `(8)`. The set `A` depends on the fixed Hamiltonian and input, never on a target.

### Step 2 -- exact general-tensor Steinhaus bound

Let `Sym^r(C^D)` carry the normalized occupation basis `e_alpha`, indexed by multi-indices
`alpha` with `|alpha|=r`. Put `tilde p_j=p_j` for `j notin A` and `tilde p_j=0` for `j in A`.
For every `w=sum_alpha w_alpha e_alpha`,

\[
 \langle\Phi_L(\zeta)^{\otimes r},w\rangle
 =\sum_{|\alpha|=r}
   \sqrt{{r!\over\alpha!}}
   \prod_j(\sqrt{\widetilde p_j}\zeta_j)^{\alpha_j}
   \overline{w_\alpha}.                              \tag{11}
\]

Distinct multi-indices are distinct torus characters. Haar orthogonality therefore gives the exact
identity

\[
 \int_{\mathbb T^D}
 |\langle\Phi_L(\zeta)^{\otimes r},w\rangle|^2dm_H
 =\sum_{|\alpha|=r}{r!\over\alpha!}
   \prod_j \widetilde p_j^{\alpha_j}|w_\alpha|^2.    \tag{12}
\]

Every surviving coordinate has `p_j<=tau`; hence

\[
 \boxed{
 \int|\langle\Phi_L(\zeta)^{\otimes r},w\rangle|^2dm_H
 \le r!\tau^r\|w\|^2.}                              \tag{13}
\]

Unlike a fixed-target moment bound, `(13)` survives projection of target tensors into an arbitrary
incidence carrier. For `w=z^(tensor r)`, it contains the usual estimate
`int |<Phi_L,z>|^(2r) <= r! tau^r`. The naive inequality
`max_j p_j <= sqrt(C_H)` gives only `r! C_H^(r/2)`; removing one common heavy sector upgrades the
scale to `r! C_H^r`.

### Step 3 -- minimal incidence projection before optimal design

Write `S=S_r(Z)`, `U=U_(r,R)^L(Z)`, and let `P_S,P_U` be their orthogonal projections. By
construction `U subset S`, proving `(8a)`. For every `zeta notin R`, `P_S Phi_L(zeta)^(tensor r)`
is itself a spanning generator of `U`; nested projection therefore gives

\[
 P_U\Phi_L(\zeta)^{\otimes r}
 =P_S\Phi_L(\zeta)^{\otimes r}.                      \tag{14}
\]

For every target `z`, put `w_z=P_U z^(tensor r)`. Since `z^(tensor r) in S`, `(14)` gives exact
off-return incidence preservation:

\[
 \langle\Phi_L(\zeta)^{\otimes r},w_z\rangle
 =\langle\Phi_L(\zeta)^{\otimes r},z^{\otimes r}\rangle.
                                                               \tag{15}
\]

The family `{w_z:z in Z}` spans `U`, because the unprojected targets span `S` and `P_U S=U`. If
`iota=dim U=0`, `(15)` makes positive-threshold capture outside `R` impossible and `(5)` is
immediate. Assume `iota>0`.

The finite D/G-optimal-design law supplies weights `lambda_z>=0`, supported on actual nonzero
projected endpoints `w_z`, summing to one, such that for every tensor `u` and every `z in Z`,

\[
 |\langle u,w_z\rangle|^2
 \le\iota\sum_{v\in Z}\lambda_v|\langle u,w_v\rangle|^2.
                                                               \tag{16}
\]

Apply `(16)` to `u=Phi_L(zeta)^(tensor r)`. Equations `(8)` and `(15)` imply on `Q setminus R`

\[
 \left({a\over4}\right)^r
 \le\iota\sum_{v\in Z}\lambda_v
       |\langle\Phi_L(\zeta)^{\otimes r},w_v\rangle|^2.       \tag{17}
\]

Every `w_v` has norm at most `||v^(tensor r)||<=1`. Integrate `(17)`, enlarge each nonnegative
integral to the full torus, and use `(13)`:

\[
 \left({a\over4}\right)^r m_H(Q\setminus R)
 \le\iota r!\tau^r.                                  \tag{18}
\]

Substituting `tau=4C_H/a` gives

\[
 m_H(Q\setminus R)
 \le\iota_{r,R}^{L}(Z)r!
       \left({16C_H(\psi)\over a^2}\right)^r.        \tag{19}
\]

Finally `Q subset R union (Q setminus R)` proves `(5)`. Taking `Q=E_a(Z)` recovers the direct
complete-target bound as a special case.

No source point is identified with another. Equal physical endpoints reached by distinct phase
points remain distinct terms of every integral and every generator used in `(4b)`. Only reporter
space is compressed. Duplicate target labels do not alter `S`, `U`, or the optimal design, and
exact-zero residuals contribute no tensor direction.

## Ordinary bounded-degree static-local ensemble

Fix `n>=2`. Let `G` be an interaction graph containing a spanning path; the nearest-neighbour open
chain is the basic example. For every allowed nonempty support `S` of bounded size, include every
Pauli orientation on `S`, and set

\[
 H(J)=\sum_{S}\ \sum_{\alpha\in\{X,Y,Z\}^S}
       \sigma_S J_{S,\alpha}P_{S,\alpha},             \tag{20}
\]

where the `J_(S,alpha)` are independent standard real Gaussians and `sigma_S>0` depends on the
support but not its Pauli orientation. Assume all one-site and spanning-path edge blocks occur.
This is a time-independent, bounded-degree, two-local Gaussian spin Hamiltonian when only path
vertices and edges are used.

Take the fixed product input `Omega=|0>^(tensor n)`. For every `L>=1`,

\[
 \boxed{
 \Pr_H\left\{C_H(\Omega)>L\left({2\over3}\right)^n\right\}
 \le {1\over L}.}                                    \tag{21}
\]

Moreover, almost every `H` in `(20)` has simple spectrum, maximal projective rational spectral
rank `2^n-1`, and nonzero overlap between `Omega` and every eigenvector. Hence every Hamiltonian
outside one null set and the exceptional set in `(21)` obeys

\[
 \boxed{
 m_H(Q)
 \le m_H(R)+\iota_{r,R}^{L}(Z)r!
 \left({16L(2/3)^n\over a^2}\right)^r}               \tag{22}
\]

for every finite occupied residual-target family, every positive replica order, and every
independently fixed return decomposition satisfying `(4a)`.

### Proof of the local-Clifford collision law

The law `(20)` is invariant under conjugation by every product of one-qubit Clifford unitaries:
such conjugation only permutes, and possibly changes signs of, the Pauli orientations on each fixed
support. Product-Clifford conjugation acts transitively on the `6^n` product stabilizer states.
Therefore `E_H C_H(phi)` has the same value for every product stabilizer input `phi`, and

\[
 \mathbb E_H C_H(\Omega)
 ={1\over6^n}\sum_{\phi\in\mathrm{ProdStab}_n}
   \mathbb E_H C_H(\phi).                             \tag{23}
\]

For one qubit, the six stabilizer states obey the exact second-moment identity

\[
 {1\over6}\sum_{\phi}|\phi\rangle\langle\phi|^{\otimes2}
 ={I+F\over6}.                                       \tag{24}
\]

For a fixed `n`-qubit unit vector `e`, tensoring `(24)` and expanding the local swaps gives

\[
 {1\over6^n}\sum_{\phi\in\mathrm{ProdStab}_n}
 |\langle e,\phi\rangle|^4
 ={1\over6^n}\sum_{A\subseteq[n]}\operatorname{Tr}(\rho_A^2)
 \le {2^n\over6^n}=3^{-n},                           \tag{25}
\]

where `rho_A` is the reduced state of `|e><e|` on `A`. Summing `(25)` over the `D=2^n`
eigenvectors of a fixed simple Hamiltonian and using `(23)` proves

\[
 \mathbb E_H C_H(\Omega)\le (2/3)^n.                 \tag{26}
\]

Markov's inequality proves `(21)`.

The projective-rank statement is the paper-proved nearest-neighbour spectral-maximality theorem:
all one- and two-site Hermitian terms on a spanning path admit no generic rational affine spectral
relation beyond trace. The Gaussian law is full-density on that family. Full spectral support at
`Omega` is also generic: the Krylov determinant

\[
 \det[\Omega,H\Omega,\ldots,H^{2^n-1}\Omega]          \tag{27}
\]

is a polynomial in the coefficients and is nonzero at
`H_0=sum_(j=0)^(n-1) 3^j X_j`; balanced ternary makes the `X`-basis energies distinct, while
`Omega` has equal nonzero overlap with every `X`-basis vector. Thus `(27)=0` is a Gaussian-null
algebraic set.

## Physical-time consequence

For every Hamiltonian with maximal projective rank, Kronecker--Weyl equidistribution identifies
the long-time projective phase closure of `exp(-itH)Omega` with projective Haar measure. The target
event is invariant under common phase, so its projective measure equals its full-torus measure in
`(2)`. Therefore,
for every closed target tube `(4)`,

\[
 \limsup_{T\to\infty}{1\over2T}
 \left|\left\{t\in[-T,T]:
   \exists z\in Z,\ |\langle e^{-itH}\Omega,z\rangle|^2\ge a
 \right\}\right|
 \le \iota_{r,\varnothing}^{L}(Z)r!
       \left({16C_H(\Omega)\over a^2}\right)^r
 \le h_r(Z)r!\left({16C_H(\Omega)\over a^2}\right)^r. \tag{28}
\]

For a phase-defined return set whose boundary has Haar measure zero, `(5)` gives the same bound
with its long-time density added once. Anchor time translation changes only the phases of the
spectral coefficients, not the probabilities `p_j` or collision `(1)`, so the estimate is unchanged
after lag-resolved anchor rephasing.

Equation `(28)` is quenched: draw one Hamiltonian, keep it fixed, and take physical time density.
It is not an annealed random-circuit statement.

## Complete circuit consequence

Let a finite gate dictionary on `n` qubits have at most `M_n^(s+1)` words of length at most `s`,
and let `Z_s` be their occupied output states. For trace-distance error `epsilon<1`, put

\[
 a=1-\epsilon^2,
 \qquad
 r_n=\left\lfloor {a^2\over32L}\left({3\over2}\right)^n\right\rfloor. \tag{29}
\]

When `r_n>=1`, `r_n!<=r_n^(r_n)` and `(22)` give

\[
 m_H(E_a(Z_s))
 \le m_H(R)+\iota_{r_n,R}^{L}(Z_s)2^{-r_n}
 \le m_H(R)+h_{r_n}(Z_s)2^{-r_n}
 \le m_H(R)+M_n^{s+1}2^{-r_n}.                        \tag{30}
\]

Hence, if

\[
 s+1\le {r_n\log2\over2\log M_n},                    \tag{31}
\]

then

\[
 m_H(E_a(Z_s))\le m_H(R)+2^{-r_n/2}.                 \tag{32}
\]

For a standard finite two-qubit gate alphabet with arbitrary gate locations,
`log M_n=O(log n)`. Thus, with Hamiltonian probability at least `1-1/L`, the fixed product-state
orbit has completed-time approximate state complexity

\[
 \boxed{
 \Omega\!\left({(3/2)^n\over L\log n}\right)}        \tag{33}
\]

outside return density plus `exp(-Omega((3/2)^n/L))` phase density.

This is exponential but not near-maximal: the unrestricted `n`-qubit state scale is `2^n` up to
polynomial factors.

## Conjecturing protocol

### C0 -- raw coarea mass is the missing estimate

**Verdict:** `[CIRCULAR]`. Coarea disintegration rewrites capture probability and retains sheets;
it does not reduce it.

### C1 -- a growing raw observer pseudodeterminant closes the union

**Verdict:** `[FALSIFIED BY CORPUS]`. Reporter duplication changes the determinant without changing
the event. Physical tensor copies have the same exact metric/tube compensation.

### C2 -- a positive Pauli Casimir forces a linear Wegner bound

**Verdict:** `[FALSIFIED]`. The pencil

\[
 g_1\begin{pmatrix}1&0\\0&0\end{pmatrix}
 +g_2\begin{pmatrix}0&1\\1&0\end{pmatrix}
\]

has `A_1^2+A_2^2>=I`, but its small eigenvalue is quadratic in `g_2` when `g_1` stays away from
zero. Its lower tail is of order `sqrt(delta)`, not `delta`. Casimir/Hall control alone cannot
supply the required spectral anti-concentration.

### C3 -- couple flat eigenvalues to eigenvector orientation

**Verdict:** `[TRUE IDENTITY, INSUFFICIENT]`. For a simple eigenbranch of a Hermitian pencil,

\[
 \sum_i\|A_i u\|^2
 =|\nabla\lambda|^2+
   \sum_i\|(A-\lambda)\partial_i u\|^2.               \tag{34}
\]

This gap-free spectral--orientation decomposition explains the C2 counterexample, but a target
reporter may miss the transverse orientation. No target-uniform coarea decay follows without an
additional occupied-image argument.

### C4 -- bound every target by `max_j p_j`

**Verdict:** `[PROVED BUT TOO WEAK]`. The Steinhaus moment gives
`r! max_j(p_j)^r <= r! C_H^(r/2)`. This reaches only the inverse-square-root collision scale and
loses an exponential factor in the attainable circuit depth.

### C5 -- remove the common heavy spectral sector before incidence

**Verdict:** `[PAPER-PROVED SURVIVOR]`. Equations `(6)--(19)` upgrade `C_H^(r/2)` to `C_H^r`,
retain every source sheet, and absorb the complete target union through exact minimal surviving
source--target incidence rank. General-tensor Haar orthogonality is load-bearing: it preserves the
same replica ceiling after actual endpoint tensors are projected into that carrier. Optimizing the
split gives the constant `16` within this hard-threshold proof: writing the heavy norm as
`x sqrt(a)` yields the factor
`C_H/[a^2 x^2(1-x)^2]`, minimized at `x=1/2`.

### C6 -- ordinary local Hamiltonians need eigenvector universality

**Verdict:** `[FALSIFIED AS NECESSITY]`. Exact local-Clifford invariance and the product-stabilizer
second moment prove `(21)` for a fixed product input. No Wigner approximation, ETH premise,
eigenvector universality, minimum spectral gap, or numerical computation occurs.

## Sharpness and hostile audit

1. **Collision scale is sharp for the symmetry class.** Product eigenbases attain equality in
   `(25)`. One-local support-isotropic ensembles attain `(26)`, and ensembles with arbitrarily weak
   but positive two-local variance approach that value. Improving `(2/3)^n` uniformly requires
   quantitative interaction or entanglement input absent from local-Clifford symmetry.
2. **Constant 16 is method-sharp, not claimed theorem-sharp.** A smoother truncation or sharper
   Steinhaus inequality may improve constants; it cannot change the proved exponential scale.
3. **Completed-time, not Brown growth.** Maximal projective rank is qualitative. It gives no
   effective equidistribution time, first hard time, linear ramp, plateau onset, or first recurrence
   time. O4 remains open.
4. **Finite target family.** A continuous adjustable gate set needs a proved finite metric net and
   its entropy. The finite-alphabet consequence `(29)--(33)` is unconditional as stated.
5. **Support-isotropic disorder.** Anisotropic or deterministic local Hamiltonians are not covered
   by `(21)`. The abstract theorem `(5)` remains valid for every fixed Hamiltonian, with its actual
   collision.
6. **Return set cannot be optimized against the event.** The theorem preserves any independent
   physical return filtration, but does not manufacture one with small density.
7. **Not near-maximal.** The exponent base `3/2` is strictly below Hilbert dimension base `2`.
   The result is a genuine exponential product-input plateau, not the full Brown--Susskind plateau.
8. **Fibre-sheet claim is literal but phase-level.** The source is the completed spectral torus.
   Every phase sheet is integrated separately. A finite-time Gaussian coefficient-space coarea
   rate still requires effective ensemble transfer.
9. **Novelty remains unverified.** Product-state 2-design identities, Steinhaus moments,
   D/G-optimal design, Markov, and Kronecker--Weyl are classical. The candidate new knowledge is
   their exact quenched composition yielding `(5)`, `(21)`, and the bounded-degree static-local
   circuit consequence `(33)`. No priority claim is authorized yet.

## External comparison

- Kueng and Gross prove that stabilizer states form a projective 3-design; the present proof uses
  only the elementary tensor product of the six-state one-qubit 2-design:
  <https://arxiv.org/abs/1510.02767>.
- Kiefer--Wolfowitz D/G equivalence supplies the classical finite optimal-design leverage theorem.
  It does not state the return-excised replica-incidence or local-Hamiltonian consequence.
- Oszmaniec, Kotowski, Horodecki, and Hunter-Jones prove saturation and recurrence for random local
  circuits and stochastic local Hamiltonian evolution, not one quenched ordinary time-independent
  nearest-neighbour Hamiltonian: <https://arxiv.org/abs/2205.09734>.
- Brown, Freedman, Lin, and Susskind study universality of complexity geometry and motivate the
  static-local growth law; they do not prove `(5)`, `(21)`, or `(33)`:
  <https://arxiv.org/abs/2111.12700>.
- The targeted searches found no prior theorem combining support-isotropic local-Clifford disorder,
  fixed product-input spectral collision, heavy-sector replica truncation, occupied endpoint
  incidence, return excision, and the exponential static-local plateau `(33)`. This is separation
  evidence, not proof of priority.

## Lean status and future formalization map

Per explicit user instruction during the corpus refactor, no Lean file is created or modified.
Lean corpus was used read-only to identify reusable interfaces:

- replica target-span capture and duplicate/zero invariance;
- return-excised minimal incidence rank;
- projective spectral completion and Kronecker--Weyl transfer;
- support-isotropic Pauli families and local spectral maximality;
- finite Steinhaus/replica collision expansions.

Future dependency order after refactor:

1. finite general-symmetric-tensor torus-character bound `(11)--(13)`;
2. common heavy-sector decomposition `(6)--(10)`;
3. minimal light-incidence projection and composition with the optimal projected-endpoint design
   `(14)--(19)`;
4. product-stabilizer local-purity identity `(24)--(26)`;
5. support-isotropic local-Clifford conjugation transfer and Markov `(21)`;
6. physical-time and finite-circuit capstones `(28)--(33)`.

Until those statements are formalized and axiom-audited, this card authorizes paper mathematics and
frontier planning only, not a final manuscript claim under the project's Lean-only publication rule.
