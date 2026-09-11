# Linear completion of deletion prefixes: classical-route audit

**Stage:** 3-formalized. **Type:** exact identification [PROVED HERE].
**RH implication:** none newly proved. This tests and excludes a proposed reformulation,
not the general possibility of nonlinear chronological information.

The proposed escape was to use a growing family of arithmetic deletion prefixes and
its linear completion as new source data. The current corpus and primary literature
identify that formulation with the classical Nyman–Beurling/Báez-Duarte family.

For `p>=1`, the literal prefix is
`D_p(N)=sum_(1<=n<=N)(1-p*[p|n])=N mod p`.
Thus `D_p(N)/p={N/p}`. On the continuous tail cell `N<u<N+1`,

```
D_p(N)/u = p*({u/p}-{u}/p)/u.
```

The right side is exactly `p` times the existing tail-coordinate Báez-Duarte
generator. Finite rescaling of each generator by its nonzero label leaves its
linear span unchanged, hence also its closure in any fixed topology on that
same carrier. The weighted sequence space with weight `1/(N*(N+1))` is already
Bagchi's 2005 formulation of the classical criterion.

## Complete proof and formal scope

The finite sum counts `N` unit contributions and subtracts `p` for each of the
`floor(N/p)` multiples, giving `N-p*floor(N/p)=N mod p`. Division by `p` is
the elementary fractional-part formula. Therefore a finite combination of the
prefix vectors with coefficients `c_p` equals the combination of fractional-part
vectors with coefficients `p*c_p`. Conversely the coefficient change `c_p/p`
recovers every finite fractional-part combination. These maps are inverse because
every label is positive. The two spans are equal as sets of complex sequences;
applying closure in any single chosen topology preserves equality.

On `N<u<N+1`, the two floors are `floor(u)=N` and
`floor(u/p)=floor(N/p)`. Substitution into the fractional parts gives
`{u/p}-{u}/p=(N mod p)/p`, proving the tail-cell formula above. This is
the existing corpus generator `bdGenFun(1/p,u)` times `p`. The published
weighted sequence criterion uses positive integer coordinates; our formal
sequence includes the additional, identically zero coordinate at `N=0`.

Lean proves the actual finite-prefix dictionary, arbitrary finite combinations,
both span inclusions, closure equality for any topology on the whole sequence
carrier, and the pointwise tail-cell identity. No new weighted `L²` density
theorem or converse RH criterion is exported. The known weighted-space criterion
is cited for the architecture audit; its open approximation requirement is never
assumed or proved here.

## No-go scope and second pass

This excludes novelty of the proposed linear completion. Passing to growing
families still takes closures of the same union of finite spans. Modulus-dependent
nonzero rescaling changes no span. Bagchi also explicitly allows comparable
positive weights in the sequence norm. These variants therefore do not rescue
the claimed new architecture.

**NO POSITIVE SALVAGE FOUND** for a new architecture from that linear completion.
The exact dictionary is useful audit evidence, but it identifies published
mathematics and is not counted as a new positive survivor. Nonlinear chronological
words are outside the identification; their existence was proved previously and
is not new salvage from this audit. Any future use requires an explicit additional
operation and an independently proved zero-specific consequence.

## Sources and validation

Sources checked: `EulerDeletionQuasiShuffleConvergence`,
`BaezDuarteGramDiscrete`, `BaezDuarteL2Carrier`, and the actual sufficient-direction
statement in `NymanBeurlingCriterion`. Primary papers opened:
[Báez-Duarte (2002)](https://arxiv.org/abs/math/0205003) and
[Bagchi (2005)](https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf),
Theorem 1 and its stated weighted-sequence formulation. Novelty is rejected for
this linear completion, not inferred from search misses.

Module `EulerDeletionLinearSpanAudit`, namespace `RHTower.DeletionLinearSpanAudit`.
the Lean certificate below.

## Lean certificate

**Stage:** 3-formalized. **RH implication:** none. **Novelty verdict:** the
proposed linear completion identifies a published classical family.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionLinearSpanAudit.lean`.
Namespace: `RHTower.DeletionLinearSpanAudit`.

`prefixVector` is defined from the existing literal integer-coefficient sum.
`fractionVector` is independently defined as the complex-valued sequence
`fract(N/(q+1))`. `prefixVector_eq_mul_fraction` proves equality after multiplication
by `q+1`. `finiteCombination_eq` gives the explicit coefficient change for every
finite combination. `span_prefixVector_eq_fractionVector` proves both span
inclusions, and `closure_span_eq` applies in any chosen topology on the whole
sequence carrier. `tail_cell_eq_bdGenFun` identifies the normalized prefix with
the actual existing Báez-Duarte generator on every open integer cell.

The premise-free `literal_prefix_classical_linear_dictionary` packages the exact
source identity and equality of spans. It has no density, zero, or RH premise.

`lake env lean /tmp/hgt-deletion-linear-audit-9rjQNq/Audit.lean` passed six axiom
audits, covering the source dictionary, finite combinations, span, closure, cell
identity, and capstone. Dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. Production matches the audited scratch body. Narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionLinearSpanAudit` passed;
umbrella import is wired. No full or umbrella build ran. Repository-wide
`scripts/formal_tools.py lint` failed solely on concurrent work outside this module:
`RHTower/ThetaTiltLogDensity.lean` was unreachable from its theorem-area umbrella.
No lint error named this audit module. Output:
`/tmp/hgt-deletion-linear-audit-9rjQNq/lint.log`. The earlier compatible-curvature audit passed global lint. Repository-wide `scripts/formal_tools.py lint` passed with every module of this card wired into the `RHTower` umbrella; a later rerun failed only on another session's unwired module `RHTower.Sieve.MenonHarmonicBlockLevelSplitHM`, which names none of this card's modules.
No mathematical computation or external proof certificate was used.

The the paper proof above
states the precise limits. This proves an identification with classical
mathematics, not a new RH mechanism. No new positive architectural salvage was
found in the linear completion. Higher chronological operations remain a separate
unfulfilled research obligation.
