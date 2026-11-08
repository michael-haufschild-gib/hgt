# Two-sided oscillation of every averaged Narain remainder

- **ID:** W11-NO
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Pole-forced decay boundary](../3-formalized/ads3-narain-average-pole-decay-boundary.md)

## Conjecture

For every positive target-height pair, let
`R(y)=yA_YZ(y)+(3/π)log y−B_YZ`. For every actual xi zero `ρ`, every
`α>1−Re ρ/2`, every `K>0` and every `ε>0`, there are `y₊,y₋∈(0,ε)` with

`R(y₊)>K y₊^α` and `R(y₋)<−K y₋^α`.

In particular every fixed averaged remainder changes sign arbitrarily
near zero. Exceptional central heights do not suppress this oscillation.
The strict exponent loss avoids claims about exact boundary amplitudes.

## Corpus mechanism

Every arithmetic pole survives in the actual fixed mean with full
multiplicity. The proved finite-part Mellin identity removes the real
main pole. Xi has no real zeros. Landau's theorem should therefore
exclude either eventual sign of `R(y)±K y^α`: its comparison term adds
only a real pole at `s=1−α`, strictly left of the surviving pole
`s=ρ/2`.

The exact small-height continuation is
`F(s)=narainMellinMeanRegularPart Y Z (s−1/2)−∫₁∞ y^(s−1)A_YZ(y)dy`.
The tail integral is entire by exponential large-height decay. On `Re s>1`,
`F(s)=∫₀¹ y^(s−2)R(y)dy`; at every real `s>0` the principal-part
regularization is analytic. Subtracting this entire tail preserves every
arithmetic pole and its multiplicity.

`RHTower.no_oneSign_tail_of_meromorphic_pole` in
`MobiusDivisorCompactClockTailSeparation.lean` already allows arbitrary
negative pole order and a meromorphic continuation with no real pole
right of `1/4`. Meromorphic identity propagation handles the entire
divisor without deleting or truncating its zeros. Its transitive axiom
audit contains only `propext`, `Classical.choice`, `Quot.sound`.
`RHTower.exists_xiZeroCopy` in `XiWallLogDerivativeCones.lean` supplies an
actual zero from the corpus's Hardy theorem, so the final sign-change
corollary needs no zero-existence assumption. Its axiom audit also contains
only the standard three axioms.

For `1−Re ρ/2<α<1`, the reference abscissa can remain `1/4`.
Put `β=1−α>0` and rescale the
comparison carriers to
`g_±(L)=±e^((5/4−β)L)R(e^(−L))+K e^(L/4)`.
Its transform uses physical variable `s=z+β−1/4`; the comparison pole is
`z=1/4`, while each relevant arithmetic pole lies strictly to its right.
The divisor is `ξ(2z+2β−1/2)`. Initial convergence at `Re z>3/2` follows
from the established Euler-region identity. These are the proposed inputs for the existing fixed-reference tail
measure and meromorphic Landau theorem; their concrete application remains
open. Larger exponents would follow by comparison with an intermediate
exponent below one.

Reality of the actual remainder and continuity in logarithmic coordinates
are formalized in `NarainSourceReality`. `NarainMeanMellinTail` proves
absolute convergence at every parameter and entireness of the actual
large-height Mellin tail. `NarainMeanSmallSource` identifies the source
with `R(y)/y` on `0<y≤1`, zero above one, and proves its Mellin identity
on `Re s>1` and absolute convergence on `Re s>1/2`.
`NarainMeanRegularity` and `NarainMeanSmallRegularity` prove global
meromorphy, positive-real analyticity and preservation of every arithmetic
pole with full multiplicity. Five modules passed direct Lean checks and
14 endpoint axiom audits, using only the standard three axioms.

Both concrete Landau instantiations remain unproved. The displayed
rescaled carriers still require exact Laplace identities and the full
hypotheses of the one-sign theorem before either oscillation conclusion
can be claimed.

The logarithmic-coordinate identity is already public as
`RHTower.mellin_eq_integral_exp_neg_mul_log` in
`MobiusLaplaceMellinPlancherelBridge.lean`; its transitive axiom audit
contains only `propext`, `Classical.choice`, `Quot.sound`.
Cutting the source off at `y=1`
restricts the transformed integral to `L≥0`. The proved actual boundary
rate gives `R(exp(−L))=o(exp(−L/2))`, so the comparison function above
has exponential growth at most `exp((3/4−β)L)+exp(L/4)` at infinity.
Its continuity handles compact intervals. Thus the initial Laplace
integrability obligation needs no new small-height estimate.

## Gates

- [x] Source reality, cutoff transform, pole preservation and Landau inputs audited.
- [ ] 0 → 1: exact rescaled Laplace identities and concrete Landau hypotheses.
- [ ] 1 → 2: both one-sign contradictions proved without lost poles.
- [ ] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
