# Localized energy-gap collision frequency law

- **Status:** in progress
- **Target module:** `GaloisForLFunctions.RHTower.LocalizedEnergyGapCollisionFrequencyLaw`
- **Claim class:** `[CONJECTURE] [ANDERSON-LOCALITY BRIDGE]`

## Proposed law

Let a normalized spectral measure contain distinct atoms \(E_i\), indexed by
a nonempty finite set \(S\), with masses \(p_i\ge 0\). If
\[
  \sum_{i\in S}p_i\ge 1-\alpha,
  \qquad |S|\le M,
\]
then its energy-gap law \(\Delta\mu\) obeys
\[
  \Delta\mu(\{0\})\ge
  \sum_{i\in S}p_i^2\ge \frac{(1-\alpha)^2}{M}.
\]
Consequently, for every \(n\in\mathbb N\),
\[
 ((\Delta\mu)^{*n})(\{0\})
 \ge
 \left(\frac{(1-\alpha)^2}{M}\right)^n.
\]

Combined with the localized escape--return theorem, one localization
certificate would therefore control both:

1. the finite-resolution post-exit deadline through exponent \(M-1\);
2. every long-time survival moment through the inverse-volume collision
   floor above.

## Paper proof

Distinct diagonal pairs \((E_i,E_i)\) are disjoint and each contributes
\(p_i^2\) to the zero atom of the gap law. Cauchy--Schwarz gives
\((\sum_i p_i)^2\le |S|\sum_i p_i^2\). In every \(n\)-fold gap
convolution, the event that all \(n\) gaps equal zero contributes
\(\Delta\mu(\{0\})^n\).

## Kill tests

- A counterexample to the convolution atom lower bound.
- Failure to group degeneracies into distinct energy sectors.
- A claimed countably infinite extension that silently truncates the
  spectral measure rather than lower-bounding its existing atoms.
- Prior literature already joining this inverse-volume collision floor to a
  deterministic strictly post-exit localization-volume deadline.

## Boundaries

- The inverse-volume floor is not a lower bound on the first return time.
- Localization must supply the retained mass and visible-volume certificate.
- The theorem does not prove Anderson localization for a named ensemble.
- Scientific novelty is separate from mathematical truth.
