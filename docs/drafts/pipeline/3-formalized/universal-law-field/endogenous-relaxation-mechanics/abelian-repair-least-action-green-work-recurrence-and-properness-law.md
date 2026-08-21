# Abelian repair, least action, Green work, recurrence, and properness law

- **ID:** ULF-EARM-1
- **Stage:** 3-formalized
- **Type:** THEOREM / THIRD ENDOGENOUS-COMPLETION LABORATORY
- **Source:** Endogenous Abelian Relaxation Mechanics
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL FINITE THEOREM]
  [CLASSICAL SANDPILE INGREDIENTS] [BRIDGE / NEW-TO-CORPUS FUSION]
  [FULLY LEAN-FORMALIZED] [NOT RH]

## 1. Setup

Let `G` be a finite connected undirected multigraph without self-loops and with a distinguished
sink `s`.  Write `V` for the non-sink vertices and assume `V` is nonempty.  Multiple edges are
allowed.  Put

\[
 d_v=\deg_G(v),
 \qquad
 a_{vw}=\#\{\text{edges joining }v\text{ and }w\}.
\]

The reduced Laplacian is the integer matrix

\[
 \Delta_{vv}=d_v,
 \qquad
 \Delta_{vw}=-a_{vw}\quad(v\ne w).
 \tag{AR.1}
\]

A configuration is `eta in Z_{>=0}^V`.  It is stable when

\[
 0\le\eta_v<d_v\qquad(v\in V).
 \tag{AR.2}
\]

Vertex `v` is unstable when `eta_v>=d_v`.  Its legal repair, or toppling, is

\[
 \eta\longmapsto\eta-\Delta e_v.
 \tag{AR.3}
\]

The repair consumes `d_v` units at `v`, transports one unit along every edge from `v` to another
non-sink vertex, and sends the remaining units to the sink.  Thus legality and transport are both
fixed by `Delta` before any execution.

## 2. Positive source geometry

### Lemma 2.1 -- reduced-Laplacian positivity

For every real vector `x in R^V`,

\[
 x^T\Delta x
 =\sum_{\{v,w\}\subseteq V}a_{vw}(x_v-x_w)^2
  +\sum_{v\in V}a_{vs}x_v^2.
 \tag{AR.4}
\]

Consequently `Delta` is symmetric positive definite.  Its inverse is entrywise nonnegative, and

\[
 g=\Delta^{-1}{\bf 1}
 \tag{AR.5}
\]

has strictly positive coordinates.

#### Proof

Expanding the right side of (AR.4) gives the diagonal degree terms and twice the off-diagonal
terms of `x^T Delta x`.  If the right side vanishes, `x` is constant along every non-sink edge and
zero at every vertex adjacent to the sink.  Connectedness propagates zero to all of `V`; hence
`Delta` is positive definite.

For inverse positivity, let `b>=0` and solve `Delta h=b`.  If `h` had a negative minimum at `v`,
then

\[
 (\Delta h)_v
 =\sum_{w\in V}a_{vw}(h_v-h_w)+a_{vs}h_v\le0.
\]

Because `b_v>=0`, equality would be forced.  It can persist only when every non-sink neighbour of
`v` with positive edge multiplicity has the same minimum and `a_vs=0`.  Propagating these two
conditions along a graph path from `v` to the sink reaches a non-sink vertex adjacent to the sink;
there the sink term is strictly negative, a contradiction.  Therefore `h>=0`.  Applying this to
each coordinate vector proves `Delta^{-1}>=0`.  For `b=1`, the same strong-minimum argument excludes
a zero coordinate, proving `g>0`. `square`

## 3. Termination and least action

For a legal execution, let `u_v` count the number of topplings of `v`; call

\[
 u\in\mathbb Z_{\ge0}^V
 \tag{AR.6}
\]

its odometer.  The resulting configuration is `eta-Delta u`.

### Theorem 3.1 -- endogenous termination and least lineage

Every legal execution terminates.  Every maximal legal execution ends in a stable configuration.
Its stable endpoint and odometer are independent of the repair schedule.

More sharply, if `u` is the odometer of any legal prefix and `v>=0` is any integer vector for
which `eta-Delta v` is stable, then

\[
 \boxed{u\le v\text{ coordinatewise}.}
 \tag{AR.7}
\]

Thus the completed legal odometer is the unique coordinatewise least nonnegative stabilizing
history.

#### Proof

Each legal toppling preserves nonnegativity.  By (AR.5), one toppling at `v` changes the positive
potential `g^T eta` by

\[
 g^T(\eta-\Delta e_v)-g^T\eta
 =-(\Delta g)_v=-1.
 \tag{AR.8}
\]

The potential remains nonnegative, so no legal execution can be infinite.  A maximal execution has
no unstable vertex and is stable.

For least action, suppose a legal prefix first tries to topple some vertex `i` more often than a
stabilizing vector `v`.  Immediately before that toppling its count vector `u'` satisfies

\[
 u'\le v,
 \qquad u'_i=v_i.
\]

Since off-diagonal entries of `Delta` are nonpositive,

\[
 \begin{aligned}
 (\eta-\Delta u')_i
 &=\eta_i-d_i u'_i+\sum_{j\ne i}a_{ij}u'_j\\
 &\le\eta_i-d_i v_i+\sum_{j\ne i}a_{ij}v_j
 =(\eta-\Delta v)_i<d_i.
 \end{aligned}
 \tag{AR.9}
\]

This contradicts legality of the proposed toppling.  Hence (AR.7).  Applying it in both directions
to two completed legal executions gives equality of odometers and endpoints. `square`

Write

\[
 \operatorname{stab}(\eta)=\eta-\Delta u(\eta)
 \tag{AR.10}
\]

for the canonical stable endpoint.

### Corollary 3.2 -- conservative exactification

Stabilization has the exact source/observer/history decomposition

\[
 \boxed{\eta=\operatorname{stab}(\eta)+\Delta u(\eta).}
 \tag{AR.11}
\]

Toppling changes which vertices are unstable and hence which later repairs are legal, but every
repair is invisible in the finite quotient

\[
 K_G=\mathbb Z^V/\Delta\mathbb Z^V.
 \tag{AR.12}
\]

The quotient is finite because `Delta` is a nonsingular integer matrix.

## 4. Source addition and serial composition

Fix a stable configuration `eta` and a source formation

\[
 a\in\mathbb Z_{\ge0}^V.
 \tag{AR.13}
\]

For `n>=0`, define

\[
 \eta_n=\operatorname{stab}(\eta+n a),
 \qquad
 u_n=u(\eta+n a).
 \tag{AR.14}
\]

### Lemma 4.1 -- formation/stabilization exchange

For all nonnegative configurations `x,y`,

\[
 \boxed{
 \operatorname{stab}(\operatorname{stab}(x)+y)
 =\operatorname{stab}(x+y).}
 \tag{AR.15}
\]

Consequently, with `A_a(z)=stab(z+a)` on the finite set of stable configurations,

\[
 \eta_{n+1}=A_a(\eta_n),
 \qquad
 \eta_n=A_a^n(\eta).
 \tag{AR.16}
\]

#### Proof

Take a legal stabilization of `x`.  Adding `y>=0` cannot make any toppling in that execution
illegal, so the same topplings form a legal prefix for `x+y`.  Completing that prefix produces the
left side of (AR.15).  Schedule independence from Theorem 3.1 identifies it with the direct
stabilization on the right.  Equation (AR.16) follows by induction. `square`

## 5. Exact work and recurrent-observer/open-lineage law

The Green vector and Green quadratic form associated with the same source operator are

\[
 G=\Delta^{-1},
 \qquad
 \mathcal E_G(b)=b^TG b.
 \tag{AR.17}
\]

Define full lineage work

\[
 W_n=u_n^T\Delta u_n.
 \tag{AR.18}
\]

### Theorem 5.1 -- Green conservation, recurrence, and open lineage

For every `n>=0`:

1. **Exact balance**
   \[
   \boxed{\Delta u_n=\eta+n a-\eta_n.}
   \tag{AR.19}
   \]

2. **Total-repair conservation**
   \[
   \boxed{
   {\bf1}^Tu_n=g^T(\eta+n a-\eta_n).}
   \tag{AR.20}
   \]

3. **Exact Green work**
   \[
   \boxed{
   W_n=\mathcal E_G(\eta+n a-\eta_n).}
   \tag{AR.21}
   \]

4. **Cofinal lineage law**
   \[
   \boxed{
   \frac{u_n}{n}\longrightarrow G a,
   \qquad
   \frac{W_n}{n^2}\longrightarrow a^TGa.}
   \tag{AR.22}
   \]

5. **Finite recurrent observation.**  The stable orbit `(eta_n)` is eventually periodic.  The
   quotient observer
   \[
   [\eta_n]=[\eta]+n[a]\in K_G
   \tag{AR.23}
   \]
   is periodic from the start, with period equal to the order of `[a]` in `K_G`.

6. **Exact return holonomy.**  If a stable state on the eventual cycle returns after `P>=1`
   additions, then its odometer over one cycle is
   \[
   \boxed{q_P=P\,G a\in\mathbb Z_{\ge0}^V,}
   \tag{AR.24}
   \]
   and its closed-loop lineage work is
   \[
   \boxed{
   q_P^T\Delta q_P=P^2a^TGa.}
   \tag{AR.25}
   \]
   After `k` observer cycles the stable state is unchanged, the lifted odometer is `k q_P`, and
   the full work is `k^2P^2a^TGa`.

#### Proof

Equation (AR.19) is (AR.11) applied to `eta+n a`.  Multiplying it by `g^T` and using
`g^T Delta=1^T` proves (AR.20).  Substituting `Delta u_n` into (AR.18) gives

\[
 u_n^T\Delta u_n
 =(\Delta u_n)^TG(\Delta u_n),
\]

which is (AR.21).

The stable set is finite and hence bounded.  Solving (AR.19) gives

\[
 u_n=nGa+G(\eta-\eta_n).
 \tag{AR.26}
\]

The second term is bounded, proving both limits in (AR.22).  Finiteness of the stable set and
(AR.16) give eventual periodicity.  Equation (AR.23) follows from (AR.19); translation by `[a]` on
the finite group `K_G` has the asserted period.

Choose a stable state `z` on the eventual cycle and suppose `A_a^P(z)=z`.  By Lemma 4.1, direct
stabilization of `z+P a` returns to `z`.  If `q_P` is its odometer, exact balance gives

\[
 \Delta q_P=P a.
\]

Invertibility of `Delta` proves (AR.24), and positivity of an odometer gives its nonnegativity.
Equation (AR.25) follows by substitution.  Repeating the cycle and using least-action uniqueness
makes the odometers add, proving the final assertion. `square`

## 6. Global properness and selection

### Theorem 6.1 -- bounded lineage work selects neutral formation

For a nonnegative source `a`, the following are equivalent:

1. `a=0`;
2. `(u_n)` is bounded;
3. `(W_n)` is bounded;
4. the lifted odometer of one eventual observer cycle is zero;
5. some infinite subsequence of source times has bounded full lineage work.

Equivalently,

\[
 \boxed{
 \sup_n W_n<\infty\iff a=0.}
 \tag{AR.27}
\]

#### Proof

If `a=0`, the stable starting state never topples, so every odometer and work vanishes.  If
`a!=0`, positive definiteness gives

\[
 a^TGa>0.
\]

The limits in (AR.22) imply `W_n` grows quadratically and `u_n` grows linearly.  The exact cycle
formula (AR.25) makes every nonzero cycle holonomy positive.  Hence none of clauses 2--5 can hold.
`square`

This is a selection theorem internal to the repair mechanism.  No external compactness functional
or target endpoint is supplied: `Delta` generates legality, transport, Green work, and properness.

## 7. Withheld two-vertex prediction

Take two non-sink vertices joined by one edge, each also joined once to the sink.  Then

\[
 \Delta=
 \begin{pmatrix}2&-1\\-1&2\end{pmatrix},
 \qquad
 G=\frac13
 \begin{pmatrix}2&1\\1&2\end{pmatrix}.
 \tag{AR.28}
\]

For source `a=e_1`, the quotient class `[a]` has order three because

\[
 3e_1=\Delta(2,1)^T.
 \tag{AR.29}
\]

Starting from the stable state `(1,1)`, three additions return the stable observer to `(1,1)`, but
the odometer holonomy is

\[
 q_3=(2,1)^T.
 \tag{AR.30}
\]

The work was not used to determine the period or holonomy.  The theorem predicts it afterward:

\[
 \boxed{
 q_3^T\Delta q_3
 =3^2e_1^TGe_1
 =6.}
 \tag{AR.31}
\]

Thus a period-three observer hides a linearly open history.  Its fundamental-loop quadratic work
is six; the accumulated lineage after `k` repeated loops has work `6k^2`.

## 8. Cross-organ mechanism and fourth-organ prediction

The theorem fuses five structurally different organs generated by one source matrix:

| Organ | Exact source-generated output |
|---|---|
| executable relation | unstable-site toppling and state-dependent future legality |
| completion/confluence | least-action odometer and schedule-independent stabilization |
| topology/quotient | finite critical group `coker Delta` |
| recurrence/history | periodic stable or quotient observation with open odometer lift |
| positivity/properness | Green energy and bounded-work neutral selection |

The fourth-organ prediction is (AR.25): recurrence data and the source boundary determine the
hidden positive work exactly.  Neither recurrence nor Green work was used to define the other.

Compared with the word and Arens laboratories, this proves a strictly stronger common mechanism:

\[
 \boxed{
 \text{conservative observer return}
 +\text{least endogenous repair}
 \Longrightarrow
 \text{reconstructible open lineage and proper work}.}
 \tag{AR.32}
\]

## 9. Hostile boundaries

1. **Classical ingredients.**  Least action, stabilization, critical groups, and Green functions
   are standard sandpile/abelian-network mathematics.  The ULF contribution is their exact role as
   the third endogenous-completion laboratory and the combined return-work law.
2. **Dissipation is load-bearing.**  Without a sink, the reduced Laplacian is singular, legal
   execution need not terminate, and Green properness fails.
3. **Abelianity is load-bearing.**  Noncommuting repairs need higher history data; a scalar odometer
   cannot classify them.
4. **Nonnegative source is load-bearing.**  Signed forcing can cancel and requires a different
   admissibility theorem.
5. **Finite graph is load-bearing.**  Infinite-volume stabilization, recurrence, and Green
   admission are separate problems.
6. **No RH consequence.**  No arithmetic source has been realized as this Laplacian relaxation.
   Such a realization must be predicted by the mechanism, not fitted from an RH endpoint.
7. **No universal hypertranscendence claim.**  Open lineage here is caused by repeated positive
   formation, not differential transcendence.

## 10. Parent literature

- Bond--Levine prove the least-action mechanism for general abelian networks:
  [arXiv:1309.3445](https://arxiv.org/abs/1309.3445).
- Holroyd--Levine--Meszaros--Peres--Propp--Wilson give the finite directed-graph sandpile and
  rotor-routing foundations: [arXiv:0801.3306](https://arxiv.org/abs/0801.3306).
- Jarai surveys stabilization, recurrence, and infinite-volume boundaries:
  [arXiv:1401.0354](https://arxiv.org/abs/1401.0354).
- Dhar--Ruelle--Sen--Verma describe the finite abelian group and toppling invariants:
  [arXiv:cond-mat/9408022](https://arxiv.org/abs/cond-mat/9408022).
- Chan--Levine separate recurrent finite observation from nonhalting dynamics in general abelian
  networks: [arXiv:1804.03322](https://arxiv.org/abs/1804.03322).

## 11. Lean boundary

Every displayed theorem of this card is Lean-certified in
`GaloisForLFunctions.HTGeometry.AbelianRepairLeastAction`, unconditionally and without added
hypotheses beyond the card's own standing assumptions (nonnegative configurations, nonnegative
source, stable start).  See the companion record for the statement-by-statement map.

The original Stage-2 note read: this theorem is dependency-closed on paper; no Lean file was written or built in that research
turn.  Formalization should proceed only after the read-only audit chooses between:

1. a general finite-graph reduced-Laplacian development; or
2. an abstract symmetric integral `M`-matrix theorem with the graph as a corollary.

The capstone to certify is the conjunction of least action, exact return holonomy (AR.24), Green
work (AR.25), and bounded-work selection (AR.27).  Formalizing only stabilization would miss the
new field-level fusion.

## Log

- 2026-08-12 -- conjecture frozen after corpus audit killed likelihood/Krylov refinement and found
  the Arens non-rewriting validation already closed.
- 2026-08-12 -- dependency-closed proof completed; exact two-vertex withheld prediction and
  properness selector survived hostile review; promoted to Stage 2 with Lean intentionally open.
