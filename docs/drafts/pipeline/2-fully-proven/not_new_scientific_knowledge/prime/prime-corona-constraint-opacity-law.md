# Prime-corona constraint opacity and anchored maximal HT freedom

- **ID:** `prime-corona-constraint-opacity-law`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM / GENERAL HT LANDSCAPE BRIDGE / RH ROUTE CONSTRAINT
- **Scientific status:** `[PROVED ON PAPER] [FORMAL CORE COMPLETE] [BRIDGE]`
- **Parents:**
  `../2-fully-proven/needs-audit/prime-dirichlet-tail-differential-matroid.md`,
  `../2-fully-proven/needs-audit/maximal-isodivisorial-ht-free-frame.md`

## Constraint

Let `J` be countable, enumerate the primes as `p_0,p_1,...`, and let

```text
theta_n = (epsilon_j(p_n))_(j in J) in {+1,-1}^J
```

be the prime-orientation pattern of a countable family of signed prime-zeta carriers.  Define its
tail-cluster constraint

```text
K_epsilon = intersection_N closure {theta_n : n >= N} subset {+1,-1}^J.
```

This is a nonempty compact set.  The law identifies how `K_epsilon`, rather than a flow or one
selected carrier, controls the differential matroid.

## Theorem: corona-span law

For every finite `I subset J`, every finite nonempty integer-shift set `A`, and the
finite-prime Dirichlet differential field `E_fin`, put

```text
F_(I,A) = E_fin < P_(epsilon_j)(s+a) : j in I, a in A >.
```

Then

```text
dtrdeg_(E_fin) F_(I,A)
  = card(A) * dim_C Span(pi_I(K_epsilon)).                 (1)
```

Equivalently, a finitely supported coefficient vector `c` gives a tail relation

```text
sum_j c_j epsilon_j(p) = 0 for all but finitely many p
```

if and only if the continuous cylinder-linear functional

```text
x |-> sum_j c_j x_j
```

vanishes identically on `K_epsilon`.

Conversely, every nonempty closed `K subset {+1,-1}^J` occurs as `K_epsilon` for a countable
orientation family.  Thus compact Boolean constraints, not trajectories, classify all possible
prime-tail differential-rank profiles.

## Theorem: anchored opacity interval

Fix `j_0 in J` and let

```text
H_(j_0) = {x : x_(j_0)=+1},
S_(j_0) = {all-positive pattern}
          union {the pattern with exactly coordinate j negative : j != j_0}.
```

The set `S_(j_0)` is compact and lies in `H_(j_0)`: its complement is open, because a point outside
it either is negative at the anchor or has two distinct negative coordinates, each condition being
witnessed in a finite cylinder.  For every closed constraint satisfying

```text
S_(j_0) subset K subset H_(j_0),                           (2)
```

the coordinate functions on `K` are linearly independent.  Hence the realization in the first
theorem has all of the following simultaneously:

1. the distinguished coordinate is exactly the all-positive prime-zeta source `P_+`;
2. every finite family of carriers and every finite shift rectangle is differentially
   algebraically independent over `E_fin`;
3. the exact nonlinear prime-tail constraint can be any closed `K` in the interval `(2)`.

Therefore the complete finitary differential matroid is constant on the entire closed-constraint
interval `[S_(j_0),H_(j_0)]`.  Maximal hypertranscendental freedom is compatible with, and blind to,
arbitrary nonlinear compact tail constraints even after the zeta prime orientation is fixed.

## Proof route

### 1. Tail relations are exactly corona annihilators

Let `c` have finite support `I`.  The functional `ell_c(x)=sum_(j in I)c_j x_j` takes only finitely
many values on the Boolean cube.  If `ell_c(theta_n)=0` eventually, continuity makes it vanish on
every tail cluster point.  Conversely, if it is nonzero for infinitely many `n`, one nonzero
finite `I`-pattern occurs infinitely often and yields a point of `K_epsilon` where `ell_c` is
nonzero.  This proves the kernel identity and the finite-projection rank formula.

### 2. Differential rank transfer

The established prime-Dirichlet tail theorem identifies differential independence over `E_fin`
with tail linear independence, uniformly across finite integer-shift rectangles.  Choose a basis of
`Span(pi_I(K_epsilon))`.  The kernel identity makes the corresponding tail classes independent and
expresses all remaining classes modulo finite support in their span.  The independent coordinates
contribute `card(A)` differential generators per basis vector; the dependent coordinates differ
from their linear combinations by finite Dirichlet polynomials.  This gives `(1)`.

### 3. Every compact constraint occurs

The Cantor cube on countable `J` is compact metrizable.  Every nonempty closed `K` has a countable
dense subset.  Repeat every point of this dense subset infinitely often in one sequence
`theta_n`.  Every subsequential limit belongs to `K`, while density and repetition make every point
of `K` a subsequential limit.  Hence the tail-cluster set is exactly `K`; reading coordinate `j`
along the prime enumeration defines the required orientation `epsilon_j`.

### 4. Anchored maximal rank

Suppose a finite cylinder-linear form vanishes on `S_(j_0)`.  Evaluation at the all-positive
pattern gives `sum_j c_j=0`.  Evaluation at the single-negative pattern for `j != j_0` gives
`sum_j c_j-2c_j=0`, hence every `c_j=0` off the anchor.  The first equation then gives
`c_(j_0)=0`.  Thus the coordinate functions are independent on the skeleton and therefore on every
larger `K`.  The corona-span law supplies the analytic conclusion.

## Attacks

1. **Rational-field attack.**  The associated lattice of generated fields is standard rational
   function-field geometry once a tail basis is chosen.  It is infrastructure, not the candidate
   novelty.
2. **Almost-disjoint attack.**  `S_(j_0)` recovers the existing exclusive-block/almost-disjoint
   free frame.  The possible residue is not that skeleton, but the full compact-constraint
   classification and the opacity of the entire interval above it.
3. **Symbolic-dynamics attack.**  Realizing a closed set as the limit set of a sequence is standard.
   The candidate contribution must be the exact differential-transcendence rank formula and the
   anchored nonfaithfulness theorem, not the topological realization alone.
4. **Stone--Cech attack.**  Tail relations of finite-range sequences can be read on the remainder
   of a discrete space.  This is parent infrastructure.  The new claim, if any, is the complete
   source-specific identification with signed prime-Dirichlet differential fields.
5. **Significance attack.**  A short combination of known parents does not pass automatically.
   The result clears significance only if the anchored opacity interval excludes a live class of
   HT/RH proof architectures rather than merely redescribing tail independence.

## Dual-gate verdict

The theorem is correct and useful, but it does not pass the dual gate as standalone new scientific
knowledge.  Its kernel identity is the topological form of the already proved recurring-pattern
characterization, the arbitrary closed-set realization is classical compact-metric topology, and
the anchored skeleton is the finite-pattern form of the existing almost-disjoint free frame.  The
maximal-isodivisorial theorem already excludes the same linear differential-matroid route at a
stronger fixed-divisor level.

The positive residue is decisive: the differential matroid is only the degree-one shadow of the
compact constraint.  The stronger `prime-walsh-stone-tail-reconstruction-law` adds every finite
nonlinear primewise observable and reconstructs the whole constraint.  That is the candidate new
mechanism; this card is its proved bridge.

## Positive RH necessity

The all-positive prime-zeta source can be held fixed as one coordinate of a maximally free HT
family while the nonlinear compact constraint on every auxiliary prime orientation varies through
the entire interval `[S_(j_0),H_(j_0)]` without changing one finite differential-rank datum.
Therefore a route to RH cannot obtain source rigidity from:

- hypertranscendence of the zeta prime layer;
- joint differential algebraic independence from arbitrarily many HT probes;
- the complete finitary differential matroid of those probes;
- finite Euler chambers together with any of the preceding data.

> **Nonlinear-corona incidence law.**  An RH-capable HT carrier must read a nonlinear tail
> constraint coupled to the scale-one functional equation or the continued divisor.  Differential
> rank, even at maximal countable width and with the positive Euler source anchored, cannot supply
> that incidence.

## Gates

- [x] exact compact constraint object and rank formula stated
- [x] anchored skeleton and degenerate cases isolated
- [x] complete candidate paper proof written
- [x] compare against all prior project constraint-saturation and almost-disjoint results
- [x] primary literature audit across symbolic dynamics, Stone--Cech remainders, algebraic
  matroids, and differential algebra of Dirichlet series
- [x] formalize the finite-pattern annihilator and anchored skeleton theorems
- [x] formalize exact realization of arbitrary finite recurring-pattern constraints
- [x] isolate arbitrary compact-cluster realization as a classical compact-metric boundary
- [x] significance and novelty verdict: bridge; promoted residue transferred to the Prime-Walsh law

## Status

`[CLOSED AS BRIDGE]` The theorem is proved.  It supplies the exact linear shadow and opacity
statement used by the stronger Prime-Walsh Stone reconstruction candidate, but is not itself new
scientific knowledge.
