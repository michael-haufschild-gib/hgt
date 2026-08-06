# Clock-coframe conservation budget law

- **ID:** `clock-coframe-conservation-budget-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONSERVATION / RELATIONAL CLOCKS / ACTIVE GRAVITY
- **Novelty:** adaptive-source mechanism `[REDISCOVERED]`; integration into clock-only gravity
  program `[DEPENDENCY-CLOSURE]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/ChronometricCausalSusceptibility.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockCoframeDegeneracy.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockConservationConstrainedDrives.lean`

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
   boundary of the proposed gravity reconstruction, not a removable technicality. This is now
   proved sharp in both halves — see below.

## Exact degeneracy boundary

Drop the assumption that `(1)` is an equivalence and keep only a linear map \(\Theta:C\to V\). Call
a defect \(b\) *absorbable* when some adaptive source cancels it, \(\exists a,\;b+\Theta(a)=0\).
Then

\[
  \text{every defect absorbable}
  \iff\Theta\ \text{surjective}
  \iff\operatorname{span}\{d\phi_\ell\}=V,
\]
\[
  \text{absorbing source unique}
  \iff\Theta\ \text{injective}
  \iff\{d\phi_\ell\}\ \text{linearly independent}.
\]

Each half of the coframe hypothesis is therefore equivalent to one half of the conservation budget,
not merely sufficient for it. If there are fewer clock channels than defect dimensions then
\(\operatorname{rank}\Theta<\dim V\) and some conservation defect survives every adaptive source. If
the gradients are dependent, one defect is absorbed by many sources, so the adaptive source is not a
datum and the separated signal channel of `(5)` is not well posed.

### The constrained sources exhaust the source space

`formal/GaloisForLFunctions/HTGeometry/ClockConservationConstrainedDrives.lean` completes `(5)`:

- `conservationBalancedClockSourceWithSignal_surjective`,
  `conservationBalancedClockSourceWithSignal_bijective` — every clock source is
  conservation-balanced, for exactly one defect, so the adaptive construction is a bijection and not
  merely an injection;
- **`responseOperator_eq_of_conservationBalanced_data`** — consequently the conservation constraint
  removes no drive: two probe responses agreeing on every conservation-balanced source are equal.
  This is the form the active-measurement programme needs, where the drives must satisfy the
  linearized conservation condition.

Axioms: `[propext, Classical.choice, Quot.sound]`; the bijection needs no choice.

### Lean status of the degeneracy boundary

`formal/GaloisForLFunctions/HTGeometry/ClockCoframeDegeneracy.lean`:

- `AbsorbsDefect`, `absorbsDefect_iff_mem_range` — absorbability is membership of the range;
- `forall_absorbsDefect_iff_surjective` — every defect absorbable iff `Θ` is surjective;
- `absorbing_source_unique_iff_injective` — uniqueness of the absorbing source iff `Θ` is injective;
- `clockGradientMap`, `forall_absorbsDefect_iff_span_eq_top`,
  `absorbing_source_unique_iff_linearIndependent` — the same two criteria stated directly on the
  family of clock gradients, as spanning and as linear independence;
- `exists_two_absorbing_sources_of_not_injective` — degenerate gradients give many absorbing
  sources for one defect;
- `exists_unabsorbable_defect_of_finrank_lt` — fewer clock channels than defect dimensions leaves
  an unabsorbable defect;
- `exists_unabsorbable_defect_single_clock` — an explicit witness.

All depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Gates

- [x] 0 → 1  in-progress: statement well posed and source-pure
- [x] 1 → 2  fully-proven: complete paper proof with no open dependency
- [x] 2 → 3  formalized: `responseOperator_eq_of_conservationBalanced_data`, `forall_absorbsDefect_iff_span_eq_top`; `lake build GaloisForLFunctions.HTGeometry` green; axioms
  `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready: standalone paper and external priority audit

## Log

- 2026-08-06 — moved to `3-formalized`: every theorem stated and proved on this card is unconditional in Lean, all named modules build under the `GaloisForLFunctions.HTGeometry` umbrella, and every declaration is axiom-audited to `[propext, Classical.choice, Quot.sound]`.
