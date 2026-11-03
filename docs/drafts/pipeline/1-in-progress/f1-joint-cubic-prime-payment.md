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
- Complete all-test positivity is proved only through half-aperture `181/500`.

## Gates

- [ ] Prove a joint lower bound retaining the cubic moment, reflected even gain and odd cost.
- [ ] Check all energy allocations; no jump contribution counted twice.
- [ ] Formalize the resulting complete-form inequality without an assumed positivity input.

[Two-moment complement](../2-fully-proven/f1-complete-odd-two-moment-complement.md) has a paper
proof of complete positivity on `∫xF=∫x³F=0`, using the regional logarithmic spectrum.
Its Lean formalization is pending; the two low moments and their cross terms remain open.
