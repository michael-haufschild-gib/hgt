# Xi moment landing forces root-budget escape

Status: Lean kernel checks and axiom audit passed; wired. `[BRIDGE]`, not a new RH architecture.

## Exact statement

Let `a_N : ℕ → ℝ` be nonnegative decreasing summable sequences. If, for every `r ≥ 0`,
`Σ_k a_N(k)^(2r+2) → normalizedPrimeArchMoment r`, then `Σ_k a_N(k) → +∞`.
Consequently no uniformly root-nuclear family, even with changing aperture, dimension,
carrier or mixing, can land on all completed Xi moments. Operator half-normalization uses
the sequence repeating each singular value twice; no reflection copy or multiplicity is lost.

Checked locks: `GammaSewnPluckerGlobalMeanMomentNoGo` excludes exact fixed-carrier landing;
`SoninRegularizedMomentWeldNoGo` handles its literal regularized cofinal family.
Surviving edge addressed here: approximate moment landing with a uniformly bounded root budget.
This does not exclude families with diverging root budget or prove an arithmetic selector.

## Proof

1. Suppose root budgets do not tend to infinity. Pass to a cofinal subsequence with
   `Σ a_N ≤ C`. Nonnegativity implies `C ≥ 0` and monotonicity gives
   `a_N(k) ≤ C/(k+1)`.
2. Product compactness of `[0,C]^ℕ` gives a pointwise convergent sub-subsequence `a_N → b`.
   Finite sums pass to the limit: `b ≥ 0`, `b` decreases, and `Σ b ≤ C`.
3. For every `r`, the common summable majorant
   `C^(2r) * (C/(k+1))²` dominates `a_N(k)^(2r+2)`.
   Dominated convergence therefore gives exact squared-power moments for `b`.
4. Its positive Hankel representation implies RH via the existing complete prime--Gamma
   moment criterion. Under this internally derived RH, existing Xi moment identification
   and ordered moment determinacy identify `b` with the full multiplicity-exact ordered Xi
   reciprocal sequence. That sequence is not summable. Contradiction.

Positive survivor: accurate cofinal moment landing must pay an unbounded, eventually
arbitrarily large root budget, not merely change aperture. No rate claimed.

Finite consequence: for each budget `C`, some degree `n` separates every admissible
sequence from the Xi moments by at least `1/(n+1)` in one of its first `n+1` moments.
Otherwise choose a sequence for each `n` approximating those moments more closely;
every fixed moment then converges and steps 1--4 contradict the common budget.
The degree is existential; this is not a computed numerical certificate.

Fixed-source consequence: if `A_N = B_N A C_N` with nuclear `A`, then
`Σ s_k(A_N) ≤ ||B_N|| ||C_N|| Σ s_k(A)`. Exact asymptotic half-normalized Xi
energy moments therefore force `||B_N|| ||C_N|| → ∞`. In particular bounded
stage-dependent mixing of the actual C1 root cannot evade the firewall.

## Prior art / scope

The compact spectral moment method is classical, not a new discovery:
[Collins--Hasebe--Sakuma (2018), Propositions 2.8--2.10](https://www.jstage.jst.go.jp/article/jmath/70/3/70_1111/_pdf)
develops convergence/reconstruction from nonnormalized Schatten moments. Remark 2.11
warns that the first controlled moment can lose mass at zero. Our stronger root budget
gives a summable square-moment majorant and prevents precisely that loss. A mere
uniform energy trace bound is not enough and is not claimed to be enough.
Here the application is to the corpus's exact Xi normalization and source budget firewall.
No literature-priority claim and no new primitive claimed.

## Lean

- `HTGeometry/OrderedRootBudgetMomentCompactness`: compact receiver, divergent-cost
  theorem, and finite moment-gap certificate.
- `RHTower/GammaSewnPluckerGlobalMeanMomentNoGo`: extracted sequence-level exclusion;
  existing operator theorem reuses it without changing its statement.
- `RHTower/PrimeArchMomentRootBudgetEscape`: full and half-normalized Xi landing,
  arbitrary changing Hilbert carriers, and actual C1 cofinal mixing-cost escape.
- Exact final leaf checked in canonical-module scratch, then installed unchanged.
  Needed oleans only; no full or umbrella build. Formal lint passed.
- `/tmp/HgtMomentRootEscapeAudit.lean`: all eight audited results depend only on
  `propext`, `Classical.choice`, `Quot.sound`. No owned Lean process remains; no RH claim.
