# Product primitive saturation, resolvent current, and formation-depth properness law

- **ID:** ULF-PFRM-2
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT COMPLETION CLASSIFICATION + GLOBAL FORMATION-PROPERNESS THEOREM
- **Parent:** `two-packet-rational-primitive-rigidity-and-finite-formation-no-new-current-law.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [PRODUCT COMPLETION CLASSIFIED]`
  `[EXACT FINITE INTERPOLATION] [RESOLVENT CURRENT] [DIVIDED-DIFFERENCE CONSERVATION]`
  `[FORMATION DEPTH PROPER] [TOPOLOGICAL GENERATION NO-GO] [LEAN-FORMALIZED CORE] [NOT RH]`

## 1. Mathematical delta

Finite rational formation is rigid: an additive output is already a finite linear jet current.
The obvious survivor was to complete the jet span. This theorem computes that completion exactly.

The answer is hostile to naive generation claims. In the product topology, finite jets are dense
in **every** current on the source-active coordinates. Completion therefore does not distinguish a
new law. What remains nontrivial is the least formation depth required to reproduce larger finite
observer packets. A single resolvent current has a nonzero divided difference on every packet and
forces this depth to grow exactly with packet size.

The mechanism is

\[
 \boxed{
 \text{injective clock}+\text{active sources}
 \Longrightarrow \text{product saturation},
 \qquad
 \text{nonzero divided differences}
 \Longrightarrow \text{formation-depth escape}.}
 \tag{PPS.1}
\]

Thus **closure membership is not generation**. Generation is a lift-complexity law.

## 2. Abstract weighted-orbit saturation

Let \(I\) be a set, let \(\lambda:I\to\mathbb C\) be injective, and let
\(V\le\mathbb C^I\) be a complex vector subspace. Define the active coordinate set

\[
 A_V=\{i\in I:\exists v\in V,\ v(i)\ne0\}.
 \tag{PPS.2}
\]

For \(n\ge0\), write \(\lambda^nv\) for pointwise multiplication and put

\[
 \mathcal H(V,\lambda)
 =\operatorname{span}_{\mathbb C}
   \{\lambda^nv:v\in V,n\ge0\}\subseteq\mathbb C^I.
 \tag{PPS.3}
\]

Give \(\mathbb C^I\) the product topology.

### Theorem 2.1 -- exact finite interpolation and product-closure classification

For every finite \(F\subseteq A_V\) and every target \(y:F\to\mathbb C\), there is
\(h\in\mathcal H(V,\lambda)\) with

\[
 h|_F=y.
 \tag{PPS.4}
\]

Consequently

\[
 \boxed{
 \overline{\mathcal H(V,\lambda)}^{\mathrm{prod}}
 =\{y\in\mathbb C^I:y(i)=0\text{ for }i\notin A_V\}.}
 \tag{PPS.5}
\]

### Proof

For each \(i\in F\), choose \(v_i\in V\) with \(v_i(i)\ne0\). Since \(\lambda\) is
injective, Lagrange interpolation gives \(L_i\in\mathbb C[X]\) such that

\[
 L_i(\lambda(j))=
 \begin{cases}
 y(i)/v_i(i),&j=i,\\
 0,&j\in F\setminus\{i\}.
 \end{cases}
 \tag{PPS.6}
\]

Then \(h=\sum_{i\in F}L_i(\lambda)v_i\) belongs to
\(\mathcal H(V,\lambda)\) and restricts to \(y\) on \(F\). Basic product
neighbourhoods constrain only finitely many coordinates, so `(PPS.4)` proves density on the active
coordinate product. Every generator vanishes off \(A_V\), and each inactive coordinate
evaluation is continuous; hence the closure also vanishes there. QED.

## 3. Divided-difference conservation and exact depth

Assume one cyclic source \(v\in\mathbb C^I\) is nowhere zero and \(I\) is infinite. Define

\[
 \mathcal H_d(v,\lambda)
 =\{vP(\lambda):P\in\mathbb C[X],\ \deg P\le d\}.
 \tag{PPS.7}
\]

Choose \(c\in\mathbb C\setminus\lambda(I)\), and define the completed resolvent current

\[
 R_c(i)=\frac{v(i)}{c-\lambda(i)}.
 \tag{PPS.8}
\]

For a finite nonempty \(F\subset I\), define the normalized packet divided difference

\[
 \delta_F(y)=
 \sum_{i\in F}
 \frac{y(i)/v(i)}
      {\prod_{j\in F\setminus\{i\}}(\lambda(i)-\lambda(j))}.
 \tag{PPS.9}
\]

### Theorem 3.1 -- exact conservation witness

If \(|F|=N\), then:

1. for \(N\ge2\), \(\delta_F(vP(\lambda))=0\) for every polynomial \(P\) of
   degree at most \(N-2\);
2. the resolvent current satisfies
   \[
   \boxed{
   \delta_F(R_c)=\prod_{i\in F}(c-\lambda(i))^{-1}\ne0;}
   \tag{PPS.10}
   \]
3. the least polynomial formation depth reproducing \(R_c\) on \(F\) is exactly
   \[
   \boxed{N-1.}
   \tag{PPS.11}
   \]

### Proof

Formula `(PPS.9)` is the order-\((N-1)\) divided difference of the normalized values
\(y/v\). It annihilates every polynomial of degree at most \(N-2\).

For \(f(X)=(c-X)^{-1}\), the divided-difference recursion gives

\[
 f[\lambda(i):i\in F]
 =\prod_{i\in F}(c-\lambda(i))^{-1},
\]

proving `(PPS.10)`. Thus no polynomial of degree at most \(N-2\) reproduces the resolvent
values on \(F\). Lagrange interpolation supplies one of degree at most \(N-1\), proving
`(PPS.11)` for \(N\ge2\). For \(N=1\), a constant polynomial is necessary and
sufficient, so the least depth is \(0=N-1\). QED.

### Corollary 3.2 -- global formation properness

Let \(F_1\subset F_2\subset\cdots\) with \(|F_N|=N\). The exact-head formation cost of
\(R_c\) is \(N-1\), hence tends to infinity. Moreover every product-convergent net

\[
 vP_\alpha(\lambda)\longrightarrow R_c
 \tag{PPS.12}
\]

has cofinally escaping polynomial degrees.

Indeed, each \(\mathcal H_d(v,\lambda)\) is product-closed: values on any \(d+1\) coordinates
recover the polynomial coefficients through an invertible Vandermonde matrix, and every remaining
coordinate is a fixed linear function of those values. Since `(PPS.10)` puts
\(R_c\notin\mathcal H_d\), no subnet eventually contained in \(\mathcal H_d\) can converge to
\(R_c\). Every fixed depth is eventually left.

## 4. Arithmetic primitive realization

Let \(\mathcal P_0\) be the positive-prime-power additive sector from ULF-PFRM-1. Let
\(W\le t\mathbb C[[t]]\) and define

\[
 E(W)=\{n\ge1:\exists u\in W,\ u_n\ne0\}.
 \tag{PPS.13}
\]

Index active coordinates by

\[
 I_W=\{(p,n):p\text{ prime},\ n\in E(W)\},
\qquad
 \lambda(p,n)=i\log(p^n)=in\log p.
 \tag{PPS.14}
\]

Unique factorization makes \(\lambda\) injective, and the rotated logarithmic derivation obeys

\[
 (D^ka_u)(p^n)=\lambda(p,n)^ku_n.
 \tag{PPS.15}
\]

Theorem 2.1 gives the exact completion law

\[
 \boxed{
 \overline{\mathbb C[D]a_W}^{\mathrm{coeff}}
 =\{z\in\mathcal P_0:z(p^n)=0\text{ for }n\notin E(W)\}.}
 \tag{PPS.16}
\]

As soon as one profile is nonzero on a valuation layer, finite jet formations are coefficientwise
dense in **all prime-dependent currents on that layer**.

If one profile \(u\) has \(u_n\ne0\) for every \(n\ge1\), define

\[
 \boxed{
 J_u=(1-D)^{-1}a_u,
 \qquad
 J_u(p^n)=\frac{u_n}{1-in\log p}.}
 \tag{PPS.17}
\]

This is a source-defined coefficientwise resolvent, not a fitted target current. It belongs to the
closure in `(PPS.16)` but to no finite jet span. On every \(N\)-element prime-power packet its
least exact formation depth is \(N-1\), and

\[
 \boxed{
 \delta_F(J_u)=\prod_{p^n\in F}(1-in\log p)^{-1}.}
 \tag{PPS.18}
\]

## 5. Field-level correction

ULF-PFRM-1 showed that finite rational formation cannot create a new additive current. The present
theorem shows that raw coefficientwise completion is too weak to identify one: it admits every
current on active coordinates.

The surviving field variable is the cofinal lift profile

\[
 \boxed{
 F\longmapsto
 \min\{d:\text{a depth-}d\text{ formation reproduces the target on }F\}.}
 \tag{PPS.19}
\]

For the resolvent this profile is exactly \(|F|-1\). Formation completion and formation
properness are complementary:

\[
 \text{every finite observer packet is reachable},
 \qquad
 \text{required source history escapes to infinite depth}.
 \tag{PPS.20}
\]

## 6. Fusion across four organs

| organ | exact shadow |
|---|---|
| primitive/source | packet-additive prime-power current \(a_u\) |
| differential/prolongation | clock jets \(D^ka_u\) and injective prime-power spectrum |
| topology/admission | product completion equals the full active primitive product |
| formation/properness | divided difference forces exact depth \(|F|-1\) |

Finite packet restriction is the common recovery kernel. Theorem 2.1 gives joint reconstruction on
every packet; Theorem 3.1 gives the conserved obstruction to doing so at bounded depth.

### Fourth-organ prediction

Any receiver preserving normalized clock values and packet restriction must preserve `(PPS.10)`.
Therefore a claimed depth-\(d\) realization of the resolvent packet in a spectral, moment,
recurrence, or positive receiver is impossible once it sees \(N>d+1\) distinct clock coordinates.
If the receiver misses this obstruction, it has quotiented out order-\((N-1)\) divided differences.

This prediction precedes any fourth-route choice. An instantiation must derive its clock and
restriction map from its source; it may not fit the nodes after seeing the endpoint.

## 7. Hostile boundaries

1. **Product topology is load-bearing.** Stronger norm or analytic topologies can give a smaller
   closure.
2. **Injective clock is load-bearing.** Clock collisions impose partition-diagonal constraints.
3. **Active support is exact.** No completion creates coefficients on a layer killed by all source
   profiles.
4. **Closure is not canonical generation.** `(PPS.16)` proves approximability, not naturality.
5. **The resolvent uses functional calculus.** It is canonical only after \(1-D\) and
   coefficientwise inversion are declared source operations.
6. **Exact-head cost differs from norm cost.** Stronger receivers need quantitative stability.
7. **No RH statement.** This changes the completion question but supplies no divisor selection.

## 8. Parent boundary

Lagrange interpolation, divided differences, product-topology density from finite interpolation,
and finite-dimensional Vandermonde closure are classical. The exact arithmetic coupling of
prime-power logarithmic jets, maximal primitive saturation, and resolvent formation-depth profile
is the corpus-specific theorem. No external priority claim is made.

## 9. Conjecture loops closed

1. **Product completion adds a small distinguished primitive sector. -- False.** It saturates the
   full source-active primitive product.
2. **Dense reachability makes formation depth irrelevant. -- False.** The resolvent packet has
   exact cost \(|F|-1\).
3. **A new completed current gives a nonzero quotient-by-closure fracture. -- False here.** Every
   active current has zero such class. The survivor is the cofinal depth profile.
4. **Hypertranscendence alone supplies properness. -- False.** Algebraic freeness gives finite
   reconstruction; the divided difference supplies depth escape.
5. **One finite observer detects completion. -- False.** Only cofinal growth detects it.

## 10. Gates

- [x] abstract product-closure classification
- [x] exact finite interpolation
- [x] divided-difference conservation identity
- [x] exact minimal-depth theorem
- [x] cofinal formation properness
- [x] arithmetic prime-power specialization
- [x] source-defined resolvent witness
- [x] four-organ fusion and fourth-organ prediction
- [ ] hostile independent proof audit
- [x] Lean formalization and universal-law-field umbrella wiring
- [ ] stronger analytic-scale completion classification

## Log

- 2026-08-12 -- product-completion escape computed exactly; naive strict-fracture conjecture
  falsified; maximal primitive saturation and exact resolvent depth profile proved.
