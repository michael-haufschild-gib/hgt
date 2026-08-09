# Weak cuts separate static-local complexity onset from plateau capacity

- **ID:** `weak-cut-complexity-onset-capacity-separation-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / Brown-onset obstruction / nearest-neighbour static-local dynamics
- **Parents:** `cubic-phase-seeded-static-local-full-scale-plateau-law.md`,
  `../3-formalized/weak-interaction-recurrence-singularity-law.md`,
  `../3-formalized/fast-forwardable-stratum-codimension-obstruction.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED] [LEAN DEFERRED]`
- **Date:** 2026-08-09

## Public sentence

An arbitrarily weak bond can leave a finite quantum system's eventual complexity capacity maximal
while postponing the first full-complexity epoch for an arbitrarily long time.  Plateau height and
onset time are therefore different physical data: the first is spectral capacity, while the second
also sees interaction conductance.

## Setup

Let

\[
 \mathcal H=\mathcal H_A\otimes\mathcal H_B,
 \qquad
 H=H_A\otimes I+I\otimes H_B+V,                                \tag{1}
\]

where `V` is the interaction crossing the cut.  Start from a product state
`chi=chi_A tensor chi_B`.  Circuit complexity is measured from a product reference using an
inverse-closed finite universal one- and two-qubit alphabet and pure-state trace distance.

For `k` qubits and `eta>0`, let `S_k(eta)` be a uniform state-synthesis cap: every `k`-qubit pure
state has an `eta`-approximation using at most `S_k(eta)` gates.  Standard recursive state
preparation followed by finite-alphabet compilation gives, at every fixed `eta`,

\[
 S_k(eta)\le 2^k\,\operatorname{poly}(k,\log(1/eta)).            \tag{2}
\]

Only finiteness of `S_k(eta)` is needed for the exact finite-size theorem; `(2)` gives its
large-system scale.

## Theorem A -- cut-conductance delay law

This theorem is the balanced-cut specialization of the already
`[LOCAL-RESEARCH] [LEAN-PROVED]` fast-forwardable-stratum Duhamel law. It is retained here as the
physical bridge to spatial conductance, not claimed as a new continuity mechanism.

For `eta_A,eta_B>=0` and `epsilon>eta_A+eta_B`, every time satisfying

\[
 |t|\,\|V\|_{\rm op}\le\epsilon-eta_A-eta_B                   \tag{3}
\]

obeys

\[
 \boxed{
 C_\epsilon(e^{-itH}\chi)
 \le S_{n_A}(eta_A)+S_{n_B}(eta_B).}                           \tag{4}
\]

For a balanced cut and fixed positive errors, the right side is

\[
 2^{n/2}\operatorname{poly}(n)=o(2^n/\log n).                 \tag{5}
\]

Consequently the first time at which complexity can exceed the split-system synthesis cap obeys

\[
 \boxed{
 T_{\rm full}(H,\epsilon)
 \ge {\epsilon-eta_A-eta_B\over\|V\|_{\rm op}}.}              \tag{6}
\]

### Proof

Put `H_0=H_A tensor I+I tensor H_B`.  Duhamel's formula and unitarity give

\[
 \|e^{-itH}-e^{-itH_0}\|_{\rm op}\le |t|\,\|V\|_{\rm op}.    \tag{7}
\]

The decoupled state factors exactly:

\[
 e^{-itH_0}\chi
 =(e^{-itH_A}\chi_A)\otimes(e^{-itH_B}\chi_B).                \tag{8}
\]

Prepare the two factors with errors `eta_A,eta_B` and concatenate their disjoint circuits.  Tensor
stability and the triangle inequality give total trace-distance error at most

`eta_A+eta_B+|t| ||V||_op`.  Equations `(3)--(4)` follow.  Equation `(2)` on a balanced cut proves
`(5)`, and `(6)` is the contrapositive of `(4)`.

No spectral gap, perturbation expansion, or long-time approximation is used.  The estimate is
uniform on the complete interval `(3)`.

## Theorem B -- product cubic-phase seeds retain full spectral capacity

Split the qubits into nonempty sets `A,B`, with dimensions `d_A,d_B` and `D=d_A d_B`.  Independently
sample the degree-at-most-three `Z/8Z` cubic-phase seeds `chi_(h_A)` and `chi_(h_B)` on the two
factors.  For every orthonormal basis `(e_j)_(j=1)^D` of the full, possibly entangled, bipartite
space,

\[
 \boxed{
 \mathbb E_{h_A,h_B}
 \sum_{j=1}^D
 |\langle e_j,\chi_{h_A}\otimes\chi_{h_B}\rangle|^4
 \le {4\over D}.}                                             \tag{9}
\]

Hence at least one exactly `O(n^3)`-preparable product cubic seed has spectral collision at most
`4/D` in that basis.

### Proof

It is enough to compute with independent Steinhaus coordinate phases; four-wise independence of
each cubic-phase family transfers every moment used below exactly.  Fix a unit vector
`e in H_A tensor H_B`.  For a phase state `a` on `A`, let

\[
 v_a=(\langle a|\otimes I)e,
 \qquad q(a)=\|v_a\|^2.                                       \tag{10}
\]

Phase pairing on `B` gives

\[
 \mathbb E_b|\langle e,a\otimes b\rangle|^4
 \le {2q(a)^2\over d_B^2}.                                    \tag{11}
\]

Writing `rho_A=Tr_B |e><e|`, a second phase pairing gives

\[
 \mathbb E_a q(a)^2
 ={(Tr\,rho_A)^2+Tr(rho_A^2)-\sum_x(rho_A)_{xx}^2\over d_A^2}
 \le {2\over d_A^2}.                                         \tag{12}
\]

Thus the fourth moment for one `e` is at most `4/D^2`.  Sum over the `D` basis vectors to obtain
`(9)`.  Averaging then supplies one seed pair below the mean.  Each factor has the exact cubic
controlled-phase preparation from the parent theorem, so their product costs `O(n^3)` gates.

## Theorem C -- arbitrary onset delay with a full later plateau

Fix constant resolution budgets

\[
 0<eta_A+eta_B<epsilon_-<epsilon_+<1                           \tag{13}
\]

and any prescribed finite delay `L>0`.  For every sufficiently large `n`, there exist

1. one unit-coefficient-shell, time-independent nearest-neighbour Pauli Hamiltonian `H_n`;
2. one product cubic-phase seed `chi_n` of exact complexity `O(n^3)`;

such that all of the following hold for the same fixed pair:

\[
\begin{array}{ll}
\text{delayed full onset:}&
 C_{\epsilon_-}(e^{-itH_n}\chi_n)
 \le 2^{n/2}\operatorname{poly}(n)\quad(0\le t\le L),\\[2mm]
\text{full later plateau:}&
 C_{\epsilon_-}(e^{-itH_n}\chi_n)
 \ge c\,2^n/\log M_n
 \quad\text{through one interval of length }\exp(c2^n),\\[2mm]
\text{later recurrence:}&
 e^{-itH_n}\chi_n\text{ later returns within any prescribed positive error of }\chi_n,\\[1mm]
\text{permanent non-Haar locality:}&
 e^{-itH_n}\text{ remains separated from Haar randomness by the fixed local two-query protocol}
 \text{ for every real }t.
\end{array}                                                    \tag{14}
\]

Here `c>0` depends only on the fixed errors and gate alphabet, not on `L`.

### Proof

Choose a balanced spatial cut, a decoupled path-local coefficient-shell point `H_0`, and a
positive-volume shell neighbourhood `U` on which

\[
 \|H-H_0\|_{\rm op}
 \le {\epsilon_- -eta_A-eta_B\over L}.                         \tag{15}
\]

The path-local simple-spectrum, cyclicity, and maximal-projective-rank loci are conull; cyclicity
may be imposed simultaneously for the finite set of all product cubic seeds.  For every
`H in U`, Theorem B says that at least one seed in this finite set has collision at most `4/D` in
the eigenbasis of `H`.  The corresponding finitely many collision-good subsets cover `U`.
Therefore one fixed seed has a positive-measure collision-good subset of `U`; choose `H_n` from
its intersection with the preceding conull locus, and call that seed `chi_n`.  Thus the seed is
fixed for the resulting evolution rather than resampled in time.  Theorem A and `(15)` prove the
first line of `(14)`.

The collision-to-capacity theorem on the completed phase torus gives a depth
`cD/log M_n` easy-circuit complement whose bad Haar-phase measure is `exp(-cD)`.  Maximal
projective rank makes the one fixed orbit equidistributed on that torus.  A speed mesh and the same
complete-union estimate select a continuous hard block of length `exp(cD)`; reducing `c` once
absorbs the mesh.  Projective recurrence gives the later return.  The already proved bounded-weight
Pauli two-query separator applies at every time.  These are exactly the remaining three lines of
`(14)`.

Since `L` was arbitrary while the plateau constants are independent of it, eventual plateau
capacity does not bound first onset.

## Theorem D -- the ordinary shell has an unavoidable polynomial delay tail

For the full one-site plus nearest-neighbour two-site Pauli coefficient shell, the coefficient
dimension is

\[
 m=3n+9(n-1)=12n-9.                                           \tag{16}
\]

Across any fixed edge, the genuinely coupling Pauli block has dimension `p=9`.  For a uniform shell
point, let `rho` be the Euclidean norm of those nine coefficients.  Then

\[
 \rho^2\sim\operatorname{Beta}\left({9\over2},{m-9\over2}\right),              \tag{17}
\]

and therefore, for `0<x<1`,

\[
 \boxed{
 \Pr\{\rho\le x\}
 ={B_{x^2}(9/2,(m-9)/2)\over B(9/2,(m-9)/2)}
 =\Theta_n(x^9)\quad(x\downarrow0).}                           \tag{18}
\]

Deleting this edge decouples the chain, while

\[
 \|V\|_{\rm op}\le\sum_{a,b=1}^3|J_{ab}|\le3\rho.           \tag{19}
\]

For every fixed product seed, Theorem A and `(18)--(19)` imply the lower failure floor

\[
 \boxed{
 \Pr\{T_{\rm full}>L\}
 \ge c_n L^{-9}}                                               \tag{20}
\]

for all sufficiently large `L`, with an explicit positive finite-size constant `c_n` determined
by `(18)` and the fixed error margin.  A quenched Brown theorem for this unconditioned shell can
therefore never have a uniformly smaller delay tail.  At Brown time `L=2^n/poly(n)`, the floor is
`exp(-Theta(n))`, not doubly exponentially small: the beta normalization in `(18)` contributes
only a polynomial factor in `n` when `p=9` is fixed.

### Proof

Orthogonal projection of a uniform sphere point onto a fixed `p`-dimensional coordinate subspace
has the beta law `(17)`.  Its distribution function is `(18)`.  Equation `(19)` is Cauchy--Schwarz
for the nine unitary Pauli words.  Substitute

\[
 x={\epsilon-eta_A-eta_B\over3L}
\]

in `(18)` and apply `(6)`.

## Theorem E -- the complete path bottleneck can be paid once

For edge `e`, write `rho_e` for its nine-coefficient Euclidean norm and `V_e` for its two-site
interaction.  Pauli orthogonality on the four-dimensional edge Hilbert space gives

\[
 \|V_e\|_{\rm HS}=2\rho_e,
 \qquad
 \boxed{\rho_e\le\|V_e\|_{\rm op}\le3\rho_e}.                 \tag{21}
\]

Define the contiguous-cut conductance

\[
 \mathfrak g_{\rm path}(H)=\min_{1\le e<n}\|V_e\|_{\rm op}.  \tag{22}
\]

If `F_(m,9)(x)` denotes the beta distribution function in `(18)`, then no independence between
different edges is required for

\[
 \boxed{
 F_{m,9}(x/3)
 \le \Pr\{\mathfrak g_{\rm path}(H)\le x\}
 \le(n-1)F_{m,9}(x).}                                         \tag{23}
\]

Thus the whole weak-cut sector has the same ninth-power small-`x` exponent, up to the explicit
linear edge union.  At inverse Brown scale `x=poly(n)/2^n`, its probability is
`exp(-Theta(n))`.  Conditioning on

\[
 \mathfrak g_{\rm path}(H)>x                                  \tag{24}
\]

excludes the norm-small single-edge mechanism of Theorem A from certifying a delay longer than a
constant multiple of `1/x`, while costing only the tail `(23)` once.  It does not exclude other
fast-forwarding or onset-delay mechanisms.

### Proof

The nine two-site Pauli words are Hilbert--Schmidt orthogonal with squared norm four, so
`||V_e||_HS=2rho_e`.  Since `V_e` has matrix rank at most four,
`||V_e||_op>=||V_e||_HS/2=rho_e`; the upper estimate is `(19)`.  If one fixed edge has
`rho_e<=x/3`, then `mathfrak g_path<=x`, proving the lower bound in `(23)`.  Conversely,
`mathfrak g_path<=x` forces `rho_e<=x` for at least one edge; the union bound proves the upper
bound.  Equation `(18)` supplies both endpoint probabilities.

## What this changes in the Brown frontier

The conjecture

> collision `O(1/D)` plus maximal projective rank forces Brown-time onset

is false.  Theorem C keeps both properties and every already proved late-time clause while making
the onset delay arbitrarily large.  Spectral capacity and physical clock speed are independent.

The missing invariant is not a minimum spectral gap.  Every valid onset theorem must include the
interaction cut profile

\[
 \mathfrak g(H)=\min_{A|B\ {\rm nontrivial}}\|V_{A|B}\|_{\rm op}             \tag{25}
\]

as one necessary clock, but this profile is not sufficient.  For seeds product across the
minimizing cut, Theorem A proves the universal necessary clock `1/mathfrak g(H)`.  Theorems D--E
fix the sharp small-cut exponent for one edge and for the complete contiguous-cut profile of the
ordinary path-local shell.

This does not prove that a lower bound on `mathfrak g(H)` is sufficient for Brown growth.  Typical
fixed-shell Hamiltonians may still possess circuit shortcuts unrelated to a weak spatial cut.
The later capacity-compatible fast-forwardable incubation law gives fully coupled diagonal
carriers with arbitrarily long delay, so the sharpened target is:

> name concrete shortcut-carrier tubes, pay both their codimension tails and the explicit
> `L^{-9}` cut-bad sector, then attack geometric-skeleton Bellman escape on the complement.

This is a research programme, not a sufficiency theorem or an inverse classification.

## Conjecturing and falsification ledger

### C0 -- full collision capacity fixes the first plateau time

`[FALSIFIED]`.  Theorem C preserves collision `O(1/D)`, maximal projective rank, full plateau
height, exponential-in-`D` duration, recurrence, and the locality separator while delaying onset
past arbitrary `L`.

### C1 -- fixed coefficient-shell norm removes weak-interaction delay

`[FALSIFIED]`.  The global shell norm remains one while a single nine-dimensional edge block tends
to zero.

### C2 -- weak cuts are negligible enough to demand superexponential quenched tails

`[FALSIFIED]`.  The exact beta law gives the `L^{-9}` floor.

### C3 -- condition on cut conductance and run Bellman escape

`[FALSIFIED]`.  The fully coupled diagonal carrier in
`capacity-compatible-fast-forwardable-incubation-law.md` has
`mathfrak g_path(H)=Omega(n^(-1/2))`, optimal collision, and generic maximal projective rank after
transverse perturbation, yet remains easy through any prescribed `L`.

## Hostile audit

1. This theorem is a no-go and frontier correction, not Brown growth.
2. The delayed family is fine-tuned through one weak edge; Theorem D states exactly how much shell
   probability that tuning costs.
3. The product seed in Theorem C may depend on `n` and the prescribed delay `L`.  It is fixed for
   the resulting evolution, but the argument does not provide one explicit seed with a
   high-probability theorem over the whole shell.
4. State-synthesis bound `(2)` is standard infrastructure and carries no novelty claim.
5. Duhamel delay and its codimension mechanism are internally prior. Candidate novelty is limited
   to the product-cubic capacity composition, its delayed-yet-late-full plateau/recurrence/locality
   conclusion, and exact nine-dimensional path-edge refinement. External priority remains
   unaudited.
6. No final manuscript claim is authorized before Lean formalization and axiom audit.

## Lean realization after corpus refactor

1. bipartite decoupled exponential factorization and Duhamel trace-distance bound;
2. tensor preparation and approximate-complexity upper transfer `(4)`;
3. product phase-state fourth-moment bound `(9)`;
4. beta projection law or a sufficient explicit sphere-tube lower bound;
5. Pauli Hilbert--Schmidt/operator-norm comparison and the path-edge union `(23)`;
6. compose only after the existing plateau, recurrence, and locality parents are formalized.

No Lean source or process was touched while the corpus refactor was active.
