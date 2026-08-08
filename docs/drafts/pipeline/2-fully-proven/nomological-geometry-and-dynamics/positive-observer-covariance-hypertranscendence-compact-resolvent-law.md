# Positive observer covariance, relative jet freedom, and compact-resolvent completeness

- **ID:** `clg-positive-observer-covariance-compact-resolvent`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / FIVE-SECTOR BRIDGE / COMPACTNESS CRITERION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [RELATIVE-JET-FREEDOM/POSITIVITY/RECURRENCE/COMPLETION]`
  `[CONNECTED-FILTER DEFECT] [NOT RH] [NO LEAN WRITTEN OR BUILT]`
- **Statement:** For a faithful differential conditional observer, relative jet-freedom forces
  infinite positive covariance rank; its canonical norm is noncoercive, and compact resolvent is
  exactly the additional datum needed for compact action sublevels.

## Goal

Find a dynamical admissibility criterion above individual routes. The theorem must explain why an
admitted relatively jet-free tower creates hidden observer
rank, why positivity does not repair noncompactness, how recurrence can close after observation
while lifted history escapes, and which exact extra structure produces completeness.

## 1. Differential positive observer

Let `A superset B` be unital `C^*`-algebras and let `E:A->B` be a faithful conditional
expectation. Let `A_0 subset A` and `B_0 subset B` be dense unital star subalgebras with
`B_0 subset A_0`, and let `delta:A_0->A_0` be a derivation preserving `B_0`. Assume

\[
 E(A_0)\subseteq B_0,
 \qquad E\delta=\delta E\quad\text{on }A_0.
\tag{1}
\]

Let `phi:B->C` be a positive state such that

\[
 \psi=\phi\circ E
\tag{2}
\]

is faithful on `A`. Define

\[
 H_E=\overline{\ker(E)\cap A_0}^{\,L^2(A,\psi)}.
\tag{2a}
\]

For `a in A_0`, define its hidden component and covariance kernel by

\[
 c(a)=a-E(a),\qquad
 \Gamma_E(a,b)=\psi(c(a)^*c(b)).
\tag{3}
\]

## 2. Positive observer-defect theorem

### Theorem 2.1

For all `a,b in A_0`,

\[
 \boxed{
 \Gamma_E(a,b)=
 \phi\!\left(E(a^*b)-E(a^*)E(b)\right).}
\tag{4}
\]

Consequently `Gamma_E` is a positive-semidefinite Hermitian kernel.

### Proof

Expand `(3)`. Bimodularity and idempotence give

\[
 E(a^*E(b))=E(a^*)E(b),\quad
 E(E(a)^*b)=E(a^*)E(b),\quad
 E(E(a)^*E(b))=E(a^*)E(b).
\]

After applying `phi`, one negative copy survives, which proves `(4)`. Positivity follows directly
from `(3)`: for finite scalars `z_i`,

\[
 \sum_{i,j}\bar z_i z_j\Gamma_E(a_i,a_j)
 =\psi\!\left(\left(\sum_i z_i c(a_i)\right)^*
                    \left(\sum_j z_j c(a_j)\right)\right)\ge0.
\]

QED.

## 3. Relative jet freedom forces infinite covariance rank

Call `f in A_0` **relatively jet-free over `B_0`** when, for every `N`,

\[
 b+\sum_{j=0}^{N}z_j\delta^jf=0,\qquad
 b\in B_0, z_j\in\mathbb C
\quad\Longrightarrow\quad
 b=z_0=\cdots=z_N=0.
\tag{5}
\]

If `B_0 subset K subset Z(A_0)` for a central differential field `K`, differential
transcendence over `K` implies this linear condition. For general noncommutative `B_0`, only the
explicit relative jet-freeness hypothesis `(5)` is used.

### Theorem 3.1

Set

\[
 h_j=c(\delta^jf)=\delta^jc(f).
\tag{6}
\]

For every `N`, the Gram matrix

\[
 G_N=\left(\Gamma_E(\delta^if,\delta^jf)\right)_{0\le i,j\le N}
\tag{7}
\]

is positive definite. Hence

\[
 \boxed{\operatorname{rank}G_N=N+1.}
\tag{8}
\]

The covariance completion `H_E` in `(2a)` is infinite-dimensional.

### Proof

If `sum_(j<=N)z_jh_j=0`, then

\[
 \sum_jz_j\delta^jf-
 \sum_jz_jE(\delta^jf)=0.
\]

The second sum lies in `B_0`, so relative jet-freeness `(5)` gives every `z_j=0`. Thus the `h_j`
are linearly independent. For nonzero `z=(z_j)`, faithfulness of `psi` gives

\[
 z^*G_Nz=\psi\!\left((\sum_jz_jh_j)^*(\sum_jz_jh_j)\right)>0.
\]

This proves positive definiteness, `(8)`, and infinite dimension. QED.

## 4. Positivity is not completeness

Gram--Schmidt uses only finite algebraic spans of the `h_j`, so it gives an orthonormal sequence
`e_n in ker(E) cap A_0 subset H_E`. Hence the displayed use of `E(e_n)` remains algebraic:

\[
 E(e_n)=0,\qquad \Gamma_E(e_n,e_n)=1,
\tag{9}
\]

and `(e_n)` has no convergent subsequence. The canonical positive action

\[
 A_0(\xi)=\|\xi\|_{H_E}^2
\tag{10}
\]

therefore has noncompact sublevels. Relative jet freedom makes the hidden positive unit shell
noncompact; Hilbert completeness remains, but positivity alone does not supply proper dynamics.

## 5. Compact-resolvent classification

Let `L` be a positive self-adjoint operator on `H_E`. Define the extended action

\[
 A_L(\xi)=
 \begin{cases}
 \|\xi\|^2+\|L^{1/2}\xi\|^2,
   &\xi\in\operatorname{Dom}(L^{1/2}),\\
 +\infty,&\text{otherwise}.
 \end{cases}
\tag{11}
\]

### Theorem 5.1

\[
 \boxed{
 \{\xi:A_L(\xi)\le R\}\text{ is compact for every }R
 \quad\Longleftrightarrow\quad
 (I+L)^{-1}\text{ is compact}.}
\tag{12}
\]

### Proof

The unit action ball is the image of the Hilbert unit ball under `(I+L)^(-1/2)`. It is relatively
compact exactly when this operator is compact. For a positive self-adjoint `L`, compactness of
`(I+L)^(-1/2)` is equivalent by functional calculus to compactness of `(I+L)^(-1)`. Rescaling
handles every `R`. The closed quadratic form of `L` is lower semicontinuous, so each action ball
is norm closed; relative compactness is therefore compactness. QED.

Thus, on infinite-dimensional `H_E`, compact resolvent is necessary and sufficient for compact
sublevels of graph actions exactly of the form `(11)`. Choosing `L` after seeing the desired tower
is not a field law; a valid chart must derive it from source constitution.

## 6. Closed observer, open lift

In the GNS Hilbert space, bimodularity gives the orthogonal decomposition

\[
 L^2(A,\psi)=\overline{B_0}\oplus H_E.
\tag{12a}
\]

Indeed every algebraic vector decomposes as `E(a)+c(a)`, and the two pieces are orthogonal. Let
`P_B` be the corresponding observer projection. Assume `L` has compact resolvent and
infinite-dimensional `H_E`, and let `u_n` be orthonormal eigenvectors with eigenvalues
`lambda_n->infinity`. For any periodic observer history `o_n in overline(B_0)` with
`o_(n+T)=o_n`, define the internal lift

\[
 x_n=o_n+u_n.
\tag{13}
\]

Its observer projection `P_Bx_n=o_n` is exactly periodic, its hidden component has no recurrent subsequence,
and

\[
 A_L(u_n)=1+\lambda_n\longrightarrow\infty.
\tag{14}
\]

Moreover

\[
 A_L(e^{i\theta}\xi)=A_L(\xi),
\tag{15}
\]

so positive action forgets global phase. This is an exact model of closed observation with open,
costly lifted history. It proves existence of escaping lifts; it does not say every recurrent
observer path must escape.

## 7. Connected filtered-product defect

Define

\[
 \kappa_E(a,b)=\phi\!\left(E(ab)-E(a)E(b)\right).
\tag{16}
\]

Then

\[
 \boxed{\kappa_E(a,b)=\Gamma_E(a^*,b).}
\tag{17}
\]

Therefore every matrix `(kappa_E(a_i^*,a_j))` is positive semidefinite and obeys all Gram
inequalities, including Cauchy--Schwarz.

If `E` is multiplicative, `(4)` gives `Gamma_E=0`. For `a in ker E`, faithfulness then gives
`psi(a^*a)=0`, hence `a=0`; thus `ker E=0` and `A_0=B_0`. Therefore

\[
 \boxed{
 \text{a faithful multiplicative observer has no nonzero relative hidden modes}.}
\tag{18}
\]

Nonmultiplicativity is not an error here. It is the observer covariance defect measuring failure
of products to pass through observation. Calling it physical interaction requires a separate
realization theorem.

## 8. Five-sector interpretation

| Sector | Exact shadow |
|---|---|
| relative prolongation | relative jet freedom forces `rank G_N=N+1` |
| positivity/Stokes-type coarea | covariance is a positive Gram kernel; identifying a literal Stokes form with it remains open |
| recurrence/history | periodic observer projection coexists with escaping compact-resolvent lift |
| completion/properness | positivity is noncoercive; compact resolvent is exactly the repair criterion |
| conditional filtered observables | admitted star-paired connected products are covariance defects; multiplicative filters cannot produce them |

This motivates, but does not construct, a candidate higher primitive for positive charts: a stack of completely positive
observer correspondences, with covariance tensors and compact-resolvent generators transported by
bimodules. A single chosen GNS space is only a local frame.

## 9. Hostile boundaries

1. HT is not local holonomy noncompactness; `(8)` concerns hidden covariance rank.
2. Positivity is not universally a phase quotient; `(4)` is broader covariance positivity.
3. Observer recurrence does not force every lift to escape; `(13)` constructs escaping lifts.
4. Compact resolvent is necessary and sufficient only in the Hilbert action model `(11)`; other
   categories need their own properness notion.
5. No source-native conditional expectation `E` is yet proved to realize both a genuine HT family
   and a nonisomorphic Stokes/recurrence source.
6. No source theorem currently derives `L`; appending it would be theatre.
7. No wormhole length, horizon algebra, or RH selector follows from covariance alone.

## 10. Conditional consequences and falsifiers

1. Every packet admitted into the hypotheses of `(5)` has `det G_N>0` for all `N`.
2. Every admitted star-paired filter matrix of the form `(17)` is positive semidefinite and obeys
   Cauchy--Schwarz.
3. A bounded generator on infinite-dimensional `H_E`, or any generator lacking compact resolvent,
   cannot give compact sublevels for a graph action `(11)`.
4. A graph action `(11)` has compact sublevels exactly under the compact-resolvent condition
   `(12)`.
5. A faithful multiplicative quotient cannot be the universal observer for a nontrivial relative
   jet tower satisfying `(5)`.
6. If concrete HT, Stokes, and recurrence charts require incompatible positive observers, the
   field must pivot from one GNS geometry to a stack of CP correspondences.

## 11. Literature and physics boundary

- Brown--Freedman--Lin--Susskind, effective complexity geometry:
  <https://arxiv.org/abs/2111.12700>.
- Susskind, cut locus and exponential-time transition:
  <https://arxiv.org/abs/2006.01280>.
- Miyaji--Ruan--Shibuya--Yano, spectral conditions for complexity growth and plateau:
  <https://arxiv.org/abs/2507.23667>.
- Liu, 2026 positive filters and wormhole terms as products of filtered fluctuations:
  <https://arxiv.org/abs/2608.02743>.

These papers motivate but do not prove the HGT realization. In particular, star-paired connected
terms in an admitted conditional-expectation chart are covariance defects, but gravitational
wormhole terms require a source-derived filter, horizon algebra, and bulk reconstruction;
covariance identities alone are not gravity.

## Gates

- [x] positive covariance identity
- [x] relative-jet-freedom infinite-rank theorem
- [x] positivity/noncompactness theorem
- [x] compact-resolvent iff classification
- [x] recurrent observer/escaping lift construction
- [x] connected-product and multiplicative-observer no-go
- [ ] source-native `E` realizing two nonisomorphic corpus sectors
- [ ] source-derived compact-resolvent `L`
- [ ] CP-correspondence transition theorem
- [ ] formalize only after field-level target stabilizes

## Lean-return note

No Lean code was written or built. A later formalization should separate finite Gram positivity,
jet-independence, compact-operator equivalence, and the conditional-expectation identities.

## Log

- 2026-08-09 — higher pivot from quotient geometry to positive observer correspondences.
