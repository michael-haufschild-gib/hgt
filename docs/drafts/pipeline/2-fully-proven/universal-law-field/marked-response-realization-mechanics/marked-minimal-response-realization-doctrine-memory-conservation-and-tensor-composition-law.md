# Marked minimal response realization, doctrine-memory conservation, and tensor composition law

- **ID:** ULF-MRRM-1
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / GENERAL MARKED PRESENTATION-INVARIANCE GATE
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL]`
  `[MINIMAL-PRESENTATION UNIQUENESS] [EXACT MEMORY CONSERVATION]`
  `[HIGHER-SLOT TENSOR COMPOSITION] [POSITIVE GNS SHADOW] [NOT RH]`

## 1. Linear response laws

Let `k` be a field and `A` a set. Write `A*` for the free monoid of finite words, with empty word
`epsilon`. A finite linear marked presentation is

\[
 \mathcal P=(V,i,o,(T_a)_{a\in A}),
\]

where `V` is a finite-dimensional `k`-vector space, `i in V`, `o in V*`, and `T_a in End(V)`.
For a word `w=a_1...a_n`, put

\[
 T_w=T_{a_n}\cdots T_{a_1},\qquad T_\epsilon=1,
\]

and define its complete response law

\[
 r_\mathcal P(w)=o(T_wi).
\tag{MR.1}
\]

The presentation is **reachable** when

\[
 \operatorname{span}\{T_wi:w\in A^*\}=V,
\tag{MR.2}
\]

and **observable** when

\[
 \bigcap_{w\in A^*}\ker(oT_w)=0.
\tag{MR.3}
\]

It is **minimal** when both hold.

## 2. Marked presentation invariance

### Theorem 2.1 — unique minimal marked realization

Let

\[
 \mathcal P=(V,i,o,T),\qquad
 \mathcal Q=(W,j,p,U)
\]

be minimal presentations on the same alphabet. If

\[
 r_\mathcal P(w)=r_\mathcal Q(w)
 \qquad(w\in A^*),
\tag{MR.4}
\]

then there is a unique linear isomorphism `S:V -> W` such that

\[
 \boxed{
 Si=j,\qquad ST_a=U_aS\ (a\in A),\qquad pS=o.}
\tag{MR.5}
\]

### Proof

Reachability suggests

\[
 S\left(\sum_c\alpha_cT_{w_c}i\right)
 =\sum_c\alpha_cU_{w_c}j.
\tag{MR.6}
\]

To prove well-definedness, assume the vector on the left of `(MR.6)` is zero. For every word `v`,

\[
 pU_v\left(\sum_c\alpha_cU_{w_c}j\right)
 =\sum_c\alpha_c r_\mathcal Q(w_cv)
 =\sum_c\alpha_c r_\mathcal P(w_cv)
 =oT_v\left(\sum_c\alpha_cT_{w_c}i\right)=0,
\]

where the word order is read according to the convention in `(MR.1)`. Observability of `Q` makes
the target vector zero. Thus `S` is well-defined. The same construction with `P,Q` exchanged gives
an inverse. Empty and one-letter word calculations give `Si=j`, `ST_a=U_aS`, and `pS=o`.
Reachability makes any map with these properties agree with `(MR.6)`, proving uniqueness. QED.

This is the exact finite-linear marked-presentation law: complete response, not carrier resemblance, determines
the minimal presentation up to unique marked isomorphism.

## 3. Doctrine restriction and the exact two-term memory law

Fix a minimal `A`-presentation `P` and let `B subset A`. Define the restricted reachable space

\[
 R_B=\operatorname{span}\{T_wi:w\in B^*\}\subseteq V
\tag{MR.7}
\]

and its restricted invisible space

\[
 N_B=\{x\in R_B:oT_wx=0\text{ for every }w\in B^*\}.
\tag{MR.8}
\]

Every `T_b`, `b in B`, preserves both `R_B` and `N_B`. Hence the quotient

\[
 V_B^{min}=R_B/N_B
\tag{MR.9}
\]

inherits a marked `B`-presentation.

### Theorem 3.1 — restricted minimal realization

The quotient presentation `(MR.9)` is reachable and observable and realizes exactly the restricted
response `r_P|_(B*)`. Consequently every minimal realization of that restricted law has dimension

\[
 \boxed{m_B=\dim R_B-\dim N_B.}
\tag{MR.10}
\]

### Proof

Reachability is immediate from the definition of `R_B`. The output descends because `N_B` is
contained in the kernel of `o` by taking the empty future word. If a class `[x]` is invisible to
every future `B`-word, then `x` lies in `N_B`, so `[x]=0`; hence the quotient is observable. The
response of `[i]` is unchanged because quotient maps intertwine every `T_b` and the output.
Theorem 2.1 gives uniqueness and therefore the dimension formula. QED.

### Theorem 3.2 — reachability/observability memory conservation

Let `m_A=dim V` be the full minimal memory. Then

\[
 \boxed{
 m_A-m_B
 =\operatorname{codim}_V R_B+\dim N_B.}
\tag{MR.11}
\]

### Proof

By `(MR.10)`,

\[
 \dim V-m_B
 =\dim V-\dim R_B+\dim N_B.
\]

This is `(MR.11)`. QED.

The first summand is **reachability birth** under doctrine enlargement. The second is
**observability repair**. The two terms are nonnegative and presentation-invariant because both
sides of `(MR.11)` are determined by the full and restricted response laws.

### Corollary 3.3 — exact no-go classification

The restricted doctrine has full memory, `m_B=m_A`, exactly when

\[
 \boxed{R_B=V\quad\text{and}\quad N_B=0.}
\tag{MR.12}
\]

Thus finite-linear reconstruction fails only by missing production, missing tests, or both.

## 4. Higher-slot tensor composition

Let `P_l=(V_l,i_l,o_l,T^(l))`, `1<=l<=q`, be presentations on one alphabet `A`. Their tensor
presentation has state space

\[
 V_1\otimes\cdots\otimes V_q,
\]

source mark `i_1 tensor ... tensor i_q`, output `o_1 tensor ... tensor o_q`, and letter action

\[
 T_a^{(1)}\otimes\cdots\otimes T_a^{(q)}.
\tag{MR.13}
\]

### Theorem 4.1 — exact higher-slot response and memory bound

The tensor presentation realizes the pointwise product law

\[
 \boxed{r(w)=\prod_{l=1}^q r_l(w).}
\tag{MR.14}
\]

If `m_l` is the minimal memory of `r_l`, then

\[
 \boxed{m_r\le\prod_{l=1}^q m_l.}
\tag{MR.15}
\]

Equality holds exactly when the tensor presentation of minimal factors is reachable and observable.
Marked isomorphisms of the factors tensor to a marked isomorphism of the composite. These tensor
comparisons satisfy the usual associativity and permutation coherence because tensor products do.

### Proof

For every word `w`, the word action of `(MR.13)` is the tensor of the word actions. Evaluation on
the tensor source/output gives `(MR.14)`. The displayed tensor presentation has dimension the
right side of `(MR.15)`; minimal memory cannot exceed the dimension of a presentation. It attains
that dimension exactly when the presentation is already minimal. Tensoring the intertwining
identities `(MR.5)` proves presentation invariance; canonical tensor associators and symmetries give
coherence. QED.

## 5. Positive `*`-response and GNS realization

Assume `A` has an involution and words carry reversal-star. Let `r:A* -> C` satisfy

\[
 \sum_{u,v}\overline{c_u}c_v r(u^*v)\ge0
\tag{MR.16}
\]

for every finitely supported coefficient family. On the free word space define

\[
 \langle e_u,e_v\rangle_r=r(u^*v).
\tag{MR.17}
\]

Let `H_r^alg` be the algebraic quotient by its radical and let `H_r` be its Hilbert completion when
needed. In finite rank the two coincide as a finite-dimensional Hilbert space.

### Theorem 5.1 — complete positive response is presentation-complete

The left word action, empty-word mark, and cyclic output make `H_r^alg` a cyclic marked realization of
the complete `*`-response. Its dimension is the rank of the Gram/Hankel kernel `(MR.17)`. Any other
minimal cyclic `*`-realization with the same complete response is uniquely unitarily equivalent.

For `B subset A` closed under involution, the `B`-GNS space is the closure of the restricted
reachable word span modulo its Gram radical. Thus the positive memory loss is the same
reachability/radical loss in `(MR.11)`.

### Proof

Positivity makes `(MR.17)` a positive semidefinite sesquilinear form. Its radical is invariant under
left word multiplication because

\[
 \langle e_{au},e_v\rangle_r=r((au)^*v)
\]

is another word-context pairing. Hence the action descends. The empty word is cyclic by
construction, and its matrix coefficients recover `r`. Kernel rank equals quotient dimension.
For two minimal cyclic realizations, Theorem 2.1 supplies the unique marked intertwiner; equality of
all Gram coefficients makes it isometric, hence unitary. Restriction to `B` gives the final claim.
QED.

This proves that positivity itself is not phase erasure. The complete positive response retains the
cyclic law. Erasure occurs only after replacing the complete kernel by norms, diagonal values,
determinants, or another nonfaithful scalarization.

## 6. Cofinal doctrine consequence

Let `B_1 subset B_2 subset ... subset A` and assume every word uses letters from some `B_n`.
Then the minimal memories `m_(B_n)` are nondecreasing. If they are bounded, they eventually
stabilize. If the full response has no finite-dimensional linear realization, then

\[
 \boxed{m_{B_n}\longrightarrow\infty.}
\tag{MR.18}
\]

### Proof

Each restricted Hankel matrix is a submatrix of the next, so ranks are nondecreasing. A bounded
nondecreasing integer sequence stabilizes. If it stabilized at `M`, every finite response block
would have rank at most `M`; the full Hankel kernel would then have rank at most `M`, producing an
`M`-dimensional realization by the standard row-space construction, contradiction. QED.

Equation `(MR.18)` is a linear-memory statement only. Differential hypertranscendence requires the
stronger nonlinear prolongation doctrine and is not inferred from it.

## 7. Field consequence and RH boundary

The theorem closes the general finite-linear marked-presentation gate for Constitutive Process
Mathematics:

1. complete response equality makes minimal routes genuine gauges;
2. doctrine growth has an exact two-term conservation law;
3. parallel higher-slot composition is coherent and presentation-independent;
4. complete positive realization carries the same memory invariant;
5. unbounded cofinal response rank cannot hide in one finite chart.

It does not prove that the HGT routes share one response law. It does not supply source
anti-equivariance, global properness, or an RH annihilator. Those are now sharply typed source
tasks. A proposed final architecture must construct the common response before zero specialization
and show that the RH-bearing odd direction is removed by source law rather than by observer
scalarization.

## 8. Hostile scope

1. Minimal linear realization and Hankel-rank theory are classical parents.
2. The theorem applies to complete word responses; finite moment agreement is insufficient.
3. Partial, unbounded, nonlinear, and derived processes need larger doctrines.
4. Tensor-product memory can be strictly smaller than the product bound.
5. Positive GNS uniqueness requires the full cyclic `*`-response, not a diagonal probability law.
6. No claim of RH, route identification, or scientific novelty is made.
7. Theorem 2.1 proves similarity of minimal finite-linear presentations, not general categorical
   Morita invariance. Extending the response law to bimodules/process categories remains open.

## 9. Parent literature

Theorems 2.1 and 6 are in the classical Schützenberger--Fliess theory of recognizable
noncommutative formal series and Hankel rank. A modern reference is Berstel--Reutenauer,
*Noncommutative Rational Series with Applications*, Chapter 2, where minimal representations are
proved similar. The positive realization is the usual cyclic GNS construction. The exact
reachability/observability debt decomposition is recorded here because it is the load-bearing field
interpretation, not as a priority claim for realization theory.
