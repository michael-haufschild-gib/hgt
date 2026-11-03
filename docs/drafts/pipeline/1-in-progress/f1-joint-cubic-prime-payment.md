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

- [x] Prove and formalize the joint two-moment lower form with signed reflection.
- [x] Pay the third-moment charge with a positive reserve; audit all energy allocations.
- [ ] Pay the remaining first-moment charge and mixed terms.
- [ ] Formalize complete odd unit-window positivity.

[Two-moment complement](../3-formalized/f1-complete-odd-two-moment-complement.md) proves
`Q(F)≥∫F²/100` on `∫xF=∫x³F=0`, using the regional logarithmic spectrum. Individual Lean
checks and standard-only axiom audits pass. The
[joint low-moment payment](../3-formalized/f1-joint-low-moment-chord-payment.md) strengthens
the domain and reduces the charge: `Q(F)+(3203/320)(∫xF)²≥E/1000` for every odd C² unit test.
Thus only `∫xF=0` is needed for a positive floor. The remaining first-moment payment
and its cross terms remain open.

[Exact second lag moment](../3-formalized/f1-odd-second-lag-moment.md) gives
`M₂=E/3+(∫xF)²`. The retained Gamma comparison now charges `M₁/24+(∫xF)²/16`
instead of a uniform error, with uniform loss improved from `5/96` to `7/192`.
The [first lag identity](../3-formalized/f1-first-lag-moment-primitive.md) gives
`M₁=E/2+∫H²`, `H(x)=∫_{−1}ˣF`, and places the position and sinh charges on the same primitive.
All these identities and the resulting Gamma/pole bound pass individual Lean and
standard-only transitive axiom audits.

## Refuted primitive lower form

With `C(t)=∫F(x)F(x+t)dx`, the retained bound suggests the sufficient lower form

`P(F)=∫₀¹(E−C(t))/t dt−(γ+logπ+log2+1/48)E−(∫H²)/24−(∫H)²/16
 −½(∫H cosh(x/2))²−(√2 log2)C(log2)`.

The conjecture `P(F)≥0` is refuted by the
[quintic obstruction](../5-failed/f1-quintic-retained-gamma-obstruction.md).
`exists_odd_unit_retainedGamma_neg` proves a real odd C² counterexample with the exact
unit support, by smoothing `F(x)=2x(1−4x²)(1−2x²)`. Exact integral identities, signed
prime/pole bounds and support-preserving transfer pass individual Lean source audits,
with standard-only transitive axioms.

The two primitive moment squares, primitive mass and signed prime reflection must be
paid together with the discarded Gamma remainder. The complete Weil-form conjecture
remains open.

The exact terms omitted from `P` are
`∫₀¹r(t)(E−C(t))dt+2δE`, with
`r(t)=e^(t/2)/sinh t−1/t−1/2+t/24+t²/16` and
`δ=archLevyAntideriv(1)−log2−π/4+1/4−1/96`.
Both are nonnegative by the proved Gamma kernel and tail bounds. Splitting the exact
Gamma integral and substituting `M₂=E/3+(∫xF)²` gives `Q=P+∫r(E−C)+2δE` on this
odd unit window. This equality is a paper identity; the joint sign with these terms
retained remains the target.

The [three-mode exterior reserve](../3-formalized/f1-gamma-remainder-reserve.md)
proves `Q≥P+E/64` in Lean with standard-only transitive axioms. The next sufficient joint
inequality is `P≥−E/64`, with both low moments, their cross terms, prime and pole retained.
This floor is unproved. The same reserve repairs a C² quintic approximation:
`exists_odd_unit_retainedGamma_neg_weil_pos` proves `P<0<Q` on one unit-window test,
with an individual source and standard-only transitive-axiom audit.

The [primitive variance reduction](../3-formalized/f1-primitive-variance-reduction.md)
proves `∫H²−(∫H)²≤E/(4π²)` and combines the primitive and sinh costs into a single
first-moment charge, retaining the signed prime correlation. Individual Lean and
standard-only transitive axiom audits pass. The
[exact regional assembly](../3-formalized/f1-regional-exterior-identity.md) now proves
`D(G)≤P(F)+E/64≤Q(F)` with the exterior potential, both low moments and signed reflection
retained. Individual Lean and standard-only axiom audits pass. The
[sign of D](f1-primitive-variance-joint-payment.md) remains open. The audited joint payment
proves `D(G)+(3203/1280)(∫₀¹uG)²≥E/1000`. It pays the entire third charge and `3/2`
of the first charge; the current linear inverse chord provably cannot pay the full first charge.
