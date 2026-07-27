# Sigma-compactness of rational finite adeles

- **ID:** `field-one-finite-adele-sigma-compact`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-finite-adele-l2-weyl-multiplier`
- **Statement:** rational finite adeles are covered by countably many compact denominator
  dilates of integral finite adeles; consequently finite-adele additive Haar measure is
  sigma-finite.

## Theorem

For \(x=(x_v)_v\in\mathbb A_f\), only finitely many coordinates are nonintegral. The local
adic-completion denominator theorem gives, for each bad \(v\), a nonzero integer \(b_v\) such
that \(b_vx_v\) is integral. Their finite product \(d\ne0\) clears every coordinate:
\[
  dx\in\widehat{\mathbb Z}.
\]
Therefore
\[
  \mathbb A_f=\bigcup_{d\in\mathbb Z}d^{-1}\widehat{\mathbb Z}.
\]
Each member is the continuous image of compact \(\widehat{\mathbb Z}\), and the integer index is
countable. Hence \(\mathbb A_f\) is sigma-compact. Additive Haar measure on a sigma-compact
locally compact group is sigma-finite.

The proof avoids strong approximation and does not enumerate primes.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleSigmaCompact`
- **Core theorems:**
  `fieldOneFiniteAdele_exists_integral_denominator_coordinates`,
  `fieldOneFiniteAdele_exists_integral_denominator`,
  `fieldOneFiniteAdeleDenominatorCompact_isCompact`,
  `fieldOneFiniteAdele_mem_denominatorCompact`
- **Instances:** `fieldOneFiniteAdeleSigmaCompactSpace`,
  `fieldOneFiniteAdeleAddHaarSigmaFinite`
- **Audit:** direct cached `lake env lean` passed. Scratch `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved
  for final audit.

## Gates

- [x] 0 → 1: finite bad-coordinate denominator law
- [x] 1 → 2: countable compact covering and Haar sigma-finiteness
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
