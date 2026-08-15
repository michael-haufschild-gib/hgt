# Event topology is conserved as source--target debt

- **ID:** `event-topological-debt-conservation`
- **Stage:** 3-formalized
- **Formalized companion:** `event-topological-debt-conservation-formalized.md`
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [LEAN-PROVEN] [REDISCOVERED] [BRIDGE]`
- **Parent conjectures:**
  `../../1-in-progress/actuality-fracture-weak-gravity-law.md`,
  `../../1-in-progress/four-dimensional-higgs-event-fracture-law.md`
- **Statement:** Every additive invariant of a constant-rank event satisfies
  \[
  [\ker T]-[\operatorname{coker}T]=[E]-[F].
  \]
  Event debts telescope along composable histories. Hence a same-parent event has equal stable
  kernel and cokernel classes, and a closed finite event history has zero total absolute debt.

## Exact theorem

Let \(A\) be an abelian group. An additive event in \(A\) consists of five classes
\[
s,\quad k,\quad i,\quad t,\quad c\in A
\]
such that
\[
s=k+i,\qquad t=i+c.
\tag{1}
\]
Think of these as source, kernel, transmitted image, target, and cokernel classes. Define the
event debt
\[
\delta=k-c.
\tag{2}
\]
Then:

1. **One-event conservation**
   \[
   \delta=s-t.
   \tag{3}
   \]
2. **Same-parent rigidity**
   \[
   k=c\quad\Longleftrightarrow\quad s=t.
   \tag{4}
   \]
3. **History telescope.** Let \(x_0,\ldots,x_n\in A\). For each \(0\leq j<n\), suppose
   \[
   x_j=k_j+i_j,\qquad x_{j+1}=i_j+c_j.
   \tag{5}
   \]
   Then
   \[
   \sum_{j=0}^{n-1}(k_j-c_j)=x_0-x_n.
   \tag{6}
   \]
4. **Closed-history conservation.** If \(x_n=x_0\), then
   \[
   \sum_{j=0}^{n-1}(k_j-c_j)=0.
   \tag{7}
   \]

These statements hold for every additive invariant at once because \(A\) is arbitrary.

## Proof

Subtract the two equations in (1):
\[
\begin{aligned}
s-t
  &=(k+i)-(i+c)\\
  &=k-c\\
  &=\delta.
\end{aligned}
\]
This proves (3). Equation (4) follows because \(k-c=s-t\), so either difference vanishes exactly
when the other does.

Applying (3) to (5) gives
\[
k_j-c_j=x_j-x_{j+1}.
\]
Therefore
\[
\begin{aligned}
\sum_{j=0}^{n-1}(k_j-c_j)
 &=\sum_{j=0}^{n-1}(x_j-x_{j+1})\\
 &=(x_0-x_1)+(x_1-x_2)+\cdots+(x_{n-1}-x_n)\\
 &=x_0-x_n,
\end{aligned}
\]
which proves (6). Substituting \(x_n=x_0\) proves (7). \(\square\)

## Vector-bundle realization

Let \(T:E\to F\) be a constant-rank morphism of finite-rank vector bundles over a compact base
\(X\). Then \(K=\ker T\), \(I=\operatorname{im}T\), and \(C=\operatorname{coker}T\) are vector
bundles, and there are exact sequences
\[
0\longrightarrow K\longrightarrow E\longrightarrow I\longrightarrow0,
\qquad
0\longrightarrow I\longrightarrow F\longrightarrow C\longrightarrow0.
\tag{8}
\]
In \(K^0(X)\), exact-sequence additivity gives
\[
[E]=[K]+[I],\qquad [F]=[I]+[C].
\tag{9}
\]
The abstract theorem therefore becomes
\[
[\ker T]-[\operatorname{coker}T]=[E]-[F].
\tag{10}
\]

Consequences:

1. If \([E]=[F]\), then \([\ker T]=[\operatorname{coker}T]\). The two bundles are stably
   equivalent and have the same stable characteristic data.
2. If an additive observer distinguishes the kernel and cokernel, then it must already
   distinguish the source and target.
3. Pointwise equality of source and target dimensions is irrelevant. What matters is their
   global virtual bundle class.
4. For a chain whose target bundle is the next source bundle, the event index classes telescope
   exactly as in (6).

The numerical rank identity is only the degree-zero shadow:
\[
\dim\ker T-\dim\operatorname{coker}T
=\operatorname{rank}E-\operatorname{rank}F.
\tag{11}
\]

## Rank-changing and localized defects

Rank change does not contradict the theorem. It changes which version is well typed.

If the rank of \(T\) jumps, its pointwise kernels and cokernels need not form vector bundles.
The two-term complex
\[
E\xrightarrow{T}F
\tag{12}
\]
still has absolute virtual class \([E]-[F]\). If \(T\) is invertible away from a defect set
\(Z\), the map itself can additionally define a relative or compactly supported \(K\)-class
localized on \(Z\). That localized class depends on the clutching/homotopy data of \(T\), not on
the sentence “the rank changes.”

Thus there are three distinct mechanisms:

1. **constant-rank absolute debt:** equation (10);
2. **nonzero parent debt:** \([E]-[F]\neq0\);
3. **localized relative debt:** extra homotopy data of \(T\) off its singular set.

Conflating them would falsely make noninvertibility appear to create topology for free.

## Hostile novelty audit

`[NOT NEW MATHEMATICS]`

Equation (10) is standard Grothendieck-group additivity. Atiyah and Singer define the family
Fredholm index by
\[
\operatorname{ind}T=[\ker T]-[\operatorname{coker}T]\in K(X)
\]
when kernel and cokernel bundles are available:
<https://numdam.org/item/10.1007/BF02684885.pdf>.

The physical use of bundle maps, complexes, and localized \(K\)-classes is also occupied.
Witten identifies D-brane charge with spacetime \(K\)-theory:
<https://arxiv.org/abs/hep-th/9810188>.
Brane--antibrane systems are described by triples \((E_1,E_2,T)\):
<https://arxiv.org/abs/hep-th/0009112>.
Modern family-index constructions explicitly handle rank-jumping kernels by index-bundle and
superconnection data:
<https://arxiv.org/abs/2303.09091>.

No novelty claim may be made for the conservation equation, its telescope, the family index, or
localized defect classes.

## Positive survivor for the event--spacetime program

The theorem closes a loophole in the current continuum mechanism.

The local exceptional interface uses two ten-dimensional carriers and a rank-six map with a
four-dimensional kernel and four-dimensional cokernel. Calling the source and target “the same
underlying \(\operatorname{Spin}(10)\) ten-bundle” would force
\[
[\text{weak kernel}]=[\text{spacetime cokernel}]
\tag{13}
\]
in \(K^0(X)\). Noninvertibility alone therefore does not repair the already-proved obstruction to
a universal weak-bundle/tangent-bundle identification.

Any viable continuum realization must derive at least one of:

1. a nontrivial global parent class \([E_{\rm mat}]-[E_{\rm obs}]\) whose value is exactly the
   weak--spacetime topological mismatch;
2. a localized relative event class, including the map's required clutching data;
3. a base-free event category with an index theory from which the continuum base and its tangent
   class are reconstructed rather than assumed.

The third condition is essential to an emergence claim. Writing (10) for bundles over a
pre-existing manifold \(X\) cannot by itself explain why \(X\) exists.

This bridge does not prove that spacetime is an event cokernel, that gravity is an event curvature,
or that Hypertranscendence supplies the missing index. It identifies the exact topological bill
that any such theory must pay.

Public summary:

> **An event cannot create spacetime topology for free.**

## Formalization

The arbitrary-abelian-group content is unconditionally Lean-proven in
`../../../../../formal/GaloisForLFunctions/HTGeometry/EventTopologicalDebt.lean`:

1. `eventDebt_eq_source_sub_target` — one-event debt conservation;
2. `kernel_eq_cokernel_iff_source_eq_target` — same-parent equivalence;
3. `eventDebt_history_telescope` — finite-history telescoping;
4. `eventDebt_closed_history_eq_zero` — closed-history zero debt.

The bundle interpretation remains paper mathematics until the required topological \(K\)-theory
infrastructure exists in this Lean toolchain.

## Gates

- [x] exact statement and dependency-closed paper proof
- [x] rank-changing caveat separated from constant-rank bundle theorem
- [x] hostile novelty audit: standard index/Grothendieck mathematics
- [x] positive survivor changes the event-continuum open core
- [x] exact abelian-group theorem formalized unconditionally in Lean
- [ ] physical theory derives a parent or relative index without assuming spacetime

## Log

- 2026-07-29 — extracted the additive event identity from the constant-rank kernel/image/cokernel
  sequences.
- 2026-07-29 — proved finite-history telescoping and same-parent rigidity; separated absolute
  debt from localized relative defect classes.
- 2026-07-29 — hostile audit identified the result as standard family-index/Grothendieck
  mathematics and used it only as a boundary theorem for the frozen physical conjectures.
- 2026-07-29 — formalized the exact arbitrary-additive-group theorem and finite telescope. Focused
  build `GaloisForLFunctions.HTGeometry.EventTopologicalDebt` passed 8475/8475 jobs. Axiom audit
  found only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-15 — re-audited from source with `lake env lean` and focused leaf build; all five
  capstones remain closed with only `propext`, `Classical.choice`, and `Quot.sound`.
