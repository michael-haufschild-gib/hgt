# Clock-coframe conservation budget law

- **ID:** `clock-coframe-conservation-budget-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONSERVATION / RELATIONAL CLOCKS / ACTIVE GRAVITY
- **Novelty:** adaptive-source mechanism `[REDISCOVERED]`; integration into clock-only gravity
  program `[DEPENDENCY-CLOSURE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ChronometricCausalSusceptibility.lean`

## Headline

> **The clocks that label spacetime can also pay gravity's conservation debt.**

In \(d\) spacetime dimensions, \(d\) scalar clock gradients forming a coframe are enough to absorb
the \(d\) local stress-conservation constraints. Any additional clock-source channel remains free
for an independently prescribed signal.

## Exact theorem

Let \(V\) be the module of covector-valued conservation defects and \(C\) the module of adaptive
clock-source coefficients. Suppose the scalar clock gradients define a linear equivalence

\[
  \Theta:C\overset{\sim}{\longrightarrow}V,\qquad
  \Theta(a)=\sum_\ell a_\ell\,d\phi_\ell.                    \tag{1}
\]

For any stress divergence \(b\in V\), define

\[
  a_b=\Theta^{-1}(-b).                                       \tag{2}
\]

Then

\[
  b+\sum_\ell (a_b)_\ell\,d\phi_\ell
  =b+\Theta(a_b)=0.                                          \tag{3}
\]

Thus the linearized Einstein--scalar compatibility condition

\[
  \operatorname{div}_{\hat g}f^1+
  \sum_\ell f_\ell^2\,d\hat\phi_\ell=0                       \tag{4}
\]

is solved exactly by taking \(f^2=a_{\operatorname{div}f^1}\).

Now let \(S\) be any independent signal module. Define the full clock source

\[
  \mathcal A(b,s)=(\Theta^{-1}(-b),s)\in C\times S.           \tag{5}
\]

Its first component satisfies conservation, its second component is exactly \(s\), and
\(\mathcal A\) is injective. Hence conservation consumes precisely the coframe component and does
not erase an explicitly separated signal channel.

## Proof

By the inverse law for \(\Theta\),

\[
  \Theta(\Theta^{-1}(-b))=-b.
\]

Adding \(b\) proves `(3)`. Projection of `(5)` onto \(S\) is the identity. If
\(\mathcal A(b_1,s_1)=\mathcal A(b_2,s_2)\), second projection gives \(s_1=s_2\); applying
\(\Theta\) to equality of first components gives \(-b_1=-b_2\), hence \(b_1=b_2\).
\(\square\)

## Four-dimensional interpretation

In four dimensions, four scalar clocks with independent gradients form a local coframe. The same
condition already needed for relational event coordinates therefore supplies the adaptive source
needed by the conservation law. An additional source channel can carry an independently chosen
probe signal without being consumed by conservation.

This matches the exact mechanism in Kurylev--Lassas--Uhlmann's Einstein--scalar active-measurement
work: their later formulation assumes four independent background scalar gradients and constructs
bundle maps \(A_\phi^1,A_\phi^2\) that respectively right-invert contraction with \(d\phi\) and
project onto its kernel:
<https://arxiv.org/abs/1406.4776>. Their earlier five-field condition also included a field-value
row in a \(5\times5\) adaptive-source matrix:
<https://arxiv.org/abs/1405.3384>.

## Hostile boundary

1. The adaptive-source theorem and the four-gradient nondegeneracy mechanism are prior art.
2. This result does not prove a global clock coframe exists.
3. It does not prove physical apparatus can independently actuate every algebraic source channel.
4. It does not remove nonlinear gauge constraints; it closes only the pointwise linear
   conservation budget used by the active-measurement theorem.
5. Degenerate clock gradients destroy the construction. Such degeneracy is an operational
   boundary of the proposed gravity reconstruction, not a removable technicality.
