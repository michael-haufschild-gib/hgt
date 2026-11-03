# Joint cubic-moment and prime-2 payment

- **ID:** F1-JP
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [F1 assembly](f1-window-tower-assembly.md)
- **Statement:** Every real odd C² test supported in `[-1/2,1/2]` has nonnegative complete Weil form.

## Remaining inequality

Write `E=∫F²`, `M=∫F(x)x(1−16x²/5)dx`, `L=log2`, `S=[L−1/2,1/2]`,
`F₊(x)=(F(x)+F(L−x))/2`, `F₋(x)=(F(x)−F(L−x))/2`.
The complete form is

`Q(F)=Q₁(F)+(√2 log2)∫_S(F₊²−F₋²)`.

The proved frozen bound `Q₁+20M²≥E/125` isolates one moment but does not pay this
signed strip term. Retaining the cubic ground-state variance and its variable potential,
instead of their constant lower bound, may pay `F₋` while `F₊` pays the moment.
Both charges must use disjoint shares of the same jump energy.

## Existing inputs and limits

- WTZ: frozen odd coercivity on `M=0`, margin `1/125`.
- AIP: exact reflected even/odd strip decomposition; microfold estimates pay strip fluctuations.
- AIP: joint prime-only Harnack reaches half-aperture `23/40`, with the pole unpaid.
- Complete all-test positivity reaches `a*=enlargedWeilFloorAperture>181/500`, with floor
  `1/8000`; `a*<1/2`. The unit odd window remains beyond that all-test result.

## Gates

- [ ] Prove a joint lower bound retaining the cubic moment, reflected even gain and odd cost.
- [ ] Check all energy allocations; no jump contribution counted twice.
- [ ] Formalize the resulting complete-form inequality without an assumed positivity input.

[Two-moment complement](../3-formalized/f1-complete-odd-two-moment-complement.md) proves
`Q(F)≥∫F²/100` on `∫xF=∫x³F=0`, using the regional logarithmic spectrum. Individual Lean
checks and standard-only axiom audits pass. The two low moments and their cross terms remain
open. [Regional reflection payment](f1-regional-reflection-payment.md) retains the exterior
potential and signed reflection as a candidate joint bound; its sign is unproved.

[Exact second lag moment](../3-formalized/f1-odd-second-lag-moment.md) gives
`M₂=E/3+(∫xF)²`. The retained Gamma comparison now charges `M₁/24+(∫xF)²/16`
instead of a uniform error, with uniform loss improved from `5/96` to `7/192`.
The [first lag identity](../3-formalized/f1-first-lag-moment-primitive.md) gives
`M₁=E/2+∫H²`, `H(x)=∫_{−1}ˣF`, and places the position and sinh charges on the same primitive.
All these identities and the resulting Gamma/pole bound pass individual Lean and
standard-only transitive axiom audits.

## Primitive candidate

With `C(t)=∫F(x)F(x+t)dx`, the retained bound suggests the sufficient lower form

`P(F)=∫₀¹(E−C(t))/t dt−(γ+logπ+log2+1/48)E−(∫H²)/24−(∫H)²/16
 −½(∫H cosh(x/2))²−(√2 log2)C(log2)`.

Conjecture: `P(F)≥0` for every real odd C² unit-window test. A quintic obstruction is
under audit. For `F(x)=g(2x)`, with `g` from the regional card, the correction from
the old lower form is exactly `E/32−(∫H²)/24−(∫xF)²/16`. The same rational upper
certificate stays strictly negative after adding this correction; its sign is kernel
checked. The integral identities and support-preserving C² approximation still need
their Lean proofs. No C² counterexample is claimed before those checks.

The two primitive moment squares, primitive mass and signed prime reflection must be
paid together. If the obstruction closes, the discarded Gamma remainder must be
retained; failure of this lower form would not refute positivity of the complete Weil form.
