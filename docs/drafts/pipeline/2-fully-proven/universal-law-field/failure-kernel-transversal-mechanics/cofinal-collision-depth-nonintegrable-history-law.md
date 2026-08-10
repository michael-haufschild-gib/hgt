# Cofinal collision-depth and nonintegrable-history law

- **ID:** ULF-FKT-CCD-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** cofinal extension of ULF-FKT-HMCF-1
- **Statement:** bounded normalized observer-loss can encode an almost-surely finite collision depth
  whose expected lifted history is infinite.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [MECHANISM NOT ROUTE]
  [EXPLICIT COFINAL MODEL] [ANALYTIC CORE LEAN-PROVED]
  [COUNTABLE COUPLING REALIZATION LEAN-PENDING] [NOT RH]

## 1. Setup

Let

\[
 X=\{(j,b):j\ge1,\ b\in\{0,1\}\},
 \qquad d_j=\frac1{j(j+1)}.
\]

Define probability profiles

\[
 \mu(j,0)=d_j,\quad \mu(j,1)=0,
 \qquad
 \nu(j,1)=d_j,\quad \nu(j,0)=0.
\tag{CCD.1}
\]

They are probabilities because

\[
 d_j=\frac1j-\frac1{j+1},
 \qquad \sum_{j=1}^{\infty}d_j=1.
\tag{CCD.2}
\]

At observer level `n`, merge the pair `(j,0),(j,1)` exactly for `j<=n`; leave all pairs with
`j>n` separated.  These partitions form a nested cofinal chain.

## 2. The theorem

### Theorem 2.1 (bounded defect, infinite weighted history)

The maximal agreement capacity at level `n` is

\[
 A_n=\sum_{j=1}^n d_j=1-\frac1{n+1}.
\tag{CCD.3}
\]

The observed total variation is

\[
 \operatorname{TV}_n=1-A_n=\frac1{n+1},
\tag{CCD.4}
\]

and the new collision mass born at stage `n` is

\[
 A_n-A_{n-1}=d_n=\frac1{n(n+1)}.
\tag{CCD.5}
\]

There is a unique coupling simultaneously maximal at every finite stage:

\[
 \gamma_*((j,0),(j,1))=d_j
\]

and zero elsewhere.  Under `gamma_*`, let `tau` be the first observer level at which the coupled
pair becomes observationally equal.  Then

\[
 \mathbb P(\tau=j)=d_j,
 \qquad \mathbb P(\tau<\infty)=1,
 \qquad \mathbb E\tau=\infty.
\tag{CCD.6}
\]

Therefore a normalized positive defect chain can have total mass one and vanish in the observer
limit while its scale-weighted lifted history diverges.

## 3. Proof

At level `n`, the only blocks supporting both marginals are the merged `j`-pairs for `j<=n`.
Each contributes `d_j`, proving `(CCD.3)`.  The finite telescoping identity gives `(CCD.3)` and
`(CCD.5)`; the probability overlap identity gives `(CCD.4)`.

Any coupling attaining agreement `A_n` must put all mass `d_j` from `(j,0)` onto `(j,1)` for every
`j<=n`, because that merged block contains exactly one `mu` atom and one `nu` atom of the same mass.
Simultaneous maximality for all `n` therefore forces `gamma_*`, and `gamma_*` plainly has the stated
marginals.

The collision time of the `j`th pair is exactly `j`, so its law is `d_j`.  Equation `(CCD.2)` gives
almost-sure finiteness.  But

\[
 \mathbb E\tau
 =\sum_{j=1}^{\infty}j d_j
 =\sum_{j=1}^{\infty}\frac1{j+1}
 =\infty.
\]

This proves `(CCD.6)`.

## 4. Exact correction to the bounded-budget slogan

The binary overlap theorem bounds the **unweighted total defect mass** of normalized profiles by
one.  It does not bound a cost that weights defect by collision depth, aperture, formation time, or
any other unbounded source scale.  The correct separation is

\[
 \text{finite total loss}\quad\not\Rightarrow\quad
 \text{uniformly integrable lifted history}.
\]

Thus unbounded history need not require radial mass growth, signed phase, or increasing arity.  A
positive normalized collision law already suffices when its birth-depth distribution has a heavy
tail.  What must be supplied independently is a scale/cost law and its uniform-integrability
criterion.

## 5. Hostile scope

- This is an explicit countable model, not a theorem that every observer tower has infinite
  history.
- Collision depth depends on the marked nested tower; endpoint overlap alone does not determine it.
- Reweighting level `j` by a bounded cost makes the expectation finite.
- Finite total variation, almost-sure collision, and finite expected collision depth are three
  different properties.
- The construction supplies no physical clock, complexity, recurrence theorem, source selector,
  or RH implication.

## 6. Field consequence

The finite consensus face extends to a persistent **collision-depth measure**.  Observer topology
records whether distinctions eventually disappear; the measure records when; a cost law tests
integrability.  This is a three-layer mechanism:

\[
 \text{positive witness}\longrightarrow
 \text{collision filtration}\longrightarrow
 \text{costed history}.
\]

None of the three layers can be reconstructed from the terminal observer alone.

## 7. Lean target

`HTGeometry.ConstitutiveCofinalCollisionHistory` now certifies:

- telescoping defect profile and finite partial capacities;
- divergence of weighted partial sums;
- exact distinction among bounded total mass, vanishing tail, and divergent first moment.

The explicit countable source profiles and their unique simultaneous coupling remain paper-only.
They do not count as Lean-certified results.

## Log

- 2026-08-10 — explicit heavy-tail mechanism closed on paper; Lean pending.
- 2026-08-10 — telescoping-capacity, vanishing-tail, and divergent-history core elaborates cleanly in
  Lean; countable coupling realization remains paper-only.
