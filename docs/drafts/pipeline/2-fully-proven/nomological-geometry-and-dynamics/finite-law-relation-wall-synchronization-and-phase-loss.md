# Finite law-relation wall synchronization and phase loss

- **ID:** `ltg-finite-law-relation-wall-synchronization-phase-loss`
- **Stage:** 2 — fully proved on paper
- **Status:** `[PAPER-PROVED] [ROUTE-INDEPENDENT CALIBRATION] [NOT RH]`
  `[NO LEAN WRITTEN]`
- **Purpose:** prove that one degenerating law relation forces simultaneous algebraic, positive,
  topological-relation, determinant, and operational-cost shadows, while positivity loses phase.

## 1. Setup

Let `V` and `W` be complex Hilbert spaces of equal finite dimension `n`. Let

\[
 A_t:V\longrightarrow W
\]

be a norm-continuous family for `0<=t<epsilon`, invertible for `t>0`. Put

\[
 r=\dim\ker A_0>0,
 \qquad G_t=A_t^*A_t,
 \qquad \Gamma_t=\{(x,A_tx):x\in V\}\subset V\oplus W.
\tag{1}
\]

Let `R_t=Gamma_t^(-1) subset W direct-sum V` be the inverse linear relation:

\[
 R_t=\{(A_tx,x):x\in V\}.
\tag{2}
\]

For `t>0` and `y in W`, define minimal inverse-lift cost

\[
 C_t(y)=\|A_t^{-1}y\|^2.
\tag{3}
\]

## 2. Synchronization theorem

### Theorem 2.1 — five shadows of one wall

As `t->0`:

1. `ker A_0` has dimension `r`;
2. `G_0` is positive semidefinite with nullity `r`;
3. `det G_t=|det A_t|^2` for all `t`, and both determinant shadows vanish at the wall;
4. the inverse graphs `R_t` converge in the finite Grassmannian to the closed relation

   \[
    R_0=\{(A_0x,x):x\in V\},
   \tag{4}
   \]

   whose domain is `ran A_0` and whose multivalued part is

   \[
    \operatorname{mul}R_0
    =\{x:(0,x)\in R_0\}=\ker A_0;
   \tag{5}
   \]

5. for every `y notin ran A_0`,

   \[
    C_t(y)\longrightarrow\infty.
   \tag{6}
   \]

Thus kernel, positive nullity, determinant wall, multivalued inverse, and lift-cost divergence are
forced by one relation degeneration.

#### Proof

For every `x`,

\[
 \langle G_0x,x\rangle=\|A_0x\|^2,
\]

so `ker G_0=ker A_0`, proving Items 1--2. Multiplicativity of determinant and
`det(A_t^*)=overline(det A_t)` give Item 3.

The map `A -> Gamma_A` from finite-dimensional operator space to the Grassmannian is continuous.
The coordinate flip `V direct-sum W -> W direct-sum V` is unitary, so it sends
`Gamma_t` continuously to `R_t`; hence `R_t->R_0`. Formula `(4)` immediately gives
`dom R_0=ran A_0`, and `(0,x) in R_0` exactly when `A_0x=0`, proving Items 4--5 except for cost.

Suppose `(6)` fails for `y notin ran A_0`. Then some sequence `t_j->0` has
`x_j=A_(t_j)^(-1)y` bounded. Passing to a subsequence in finite dimension gives `x_j->x`. Norm
continuity yields

\[
 A_0x=\lim_j A_{t_j}x_j=y,
\]

contradicting `y notin ran A_0`. Therefore `C_t(y)->infinity`. ∎

## 3. Phase-loss theorem

### Theorem 3.1 — positive Gram shadow is nonconservative

For every unitary `U:W->W`,

\[
 (UA)^*(UA)=A^*A.
\tag{7}
\]

If `V=W` and `A` is invertible, then

\[
 \det(UA)=\det(U)\det(A).
\tag{8}
\]

Consequently the positive Gram shadow retains `|det A|` but loses the determinant phase and the
left-unitary orientation of the law relation.

#### Proof

Equation `(7)` is `A^*U^*UA=A^*A`; `(8)` is determinant multiplicativity. Choosing scalar
unitaries `U=e^(i theta)id` varies determinant phase while fixing the entire Gram operator. ∎

### Corollary 3.2 — corrected complementarity statement

The pair `(A,A^*A)` contains exactly the information of `A`, because first projection recovers
`A`. The genuine theorem is one-way: `A -> A^*A` is nonconservative. No symmetric uncertainty
claim follows without an additional incompatibility of global frames.

## 4. Exactification torsor

For fixed `t>0` and `y`, the lift set

\[
 \mathcal P_t(y)=\{x:A_tx=y\}
\]

is a singleton. At the wall, for `y in ran A_0`,

\[
 \mathcal P_0(y)=x_0+\ker A_0
\tag{9}
\]

is a torsor under the new multivalued fibre. For `y notin ran A_0` it is empty while the pre-wall
cost diverges by `(6)`. Thus exactification changes from unique, to torsorial or impossible, at the
same relation wall.

### Example 4.1 — sharp one-port normal form

For `V=W=C^n` and

\[
 A_t=\operatorname{diag}(t,1,\ldots,1),
\]

the wall has `r=1`,

\[
 G_t=\operatorname{diag}(t^2,1,\ldots,1),
 \qquad |\det A_t|=|t|,
 \qquad C_t(e_1)=|t|^{-2}.
\]

The limiting inverse relation has multivalued part `C e_1`. All exponents are sharp, and one lost
law direction becomes one positive null port, one determinant zero, one multivalued inverse port,
and one quadratic cost divergence.

## 5. Lawspace interpretation

This theorem supplies the finite normal form of an LTG discriminant wall:

| Functor of source relation | Forced wall shadow |
|---|---|
| kernel | lost exactification directions |
| positive polar square `A^*A` | zero-mode/nullity `r` |
| determinant | wall support, phase forgotten after squaring |
| inverse relation | multivalued fibre of dimension `r` |
| minimal lift cost | divergence transverse to `ran A_0` |
| lift space | singleton becomes torsor or empty |

The theorem does not show that any two corpus routes arise from one `A_t`. It makes a falsifiable
prediction: once a common source relation is constructed, these shadows must synchronize over its
same discriminant wall.

## 6. Hostile boundaries

1. Infinite algebraic rank alone does not imply cost blow-up; finite-dimensional compactness and
   a fixed transverse target `y` are used.
2. Cost need not diverge for `y in ran A_0`; some admitted lifts may remain bounded.
3. Gram data do not recover phase or left-unitary frame.
4. Forward graphs stay continuous; singularity appears in inverse solvability and multivaluedness,
   not as arbitrary topological discontinuity.
5. No source current, stability equation, hypertranscendence, or RH statement is proved.

## 7. Lean boundary

No Lean was written or built. Later formalization could use finite-dimensional kernels, adjoints,
determinants, Grassmannian graphs, and compactness. Do not formalize until a paper-level corpus
instantiation is selected.
