# Archimedean obstructions to integrality anchors for the Riemann zeta function

- **ID:** `archimedean-integrality-obstructions`
- **Stage:** 4-publication-ready
- **Type:** theorem package (six theorems) with a classification
- **Knowledge label:** `[NEW THEOREMS] [NEW LEAN FORMALISATION] [FORMALISED] [PUBLICATION READY]`
- **Source boundary:** Kronecker's theorem, the six exponentials theorem (Lang–Ramachandra),
  Hardy's theorem, Li's criterion, Weil's and Deligne's proofs of RH over finite fields, and
  Ferrero–Washington's `μ = 0` are literature; every statement below about ξ is proved here and
  certified in Lean. The manuscript is `archimedean-integrality-obstructions-manuscript.md`.

## Closed claim

Let ξ be the completed Riemann zeta function, `w(ρ) = 1 − 1/ρ` the Arakelov coordinate of a zero.

1. **Twin rigidity.** Every factorization `ξ = a·d` on `Re s > ½` by analytic factors with equal
   vanishing orders is `(g v, g/v)` for an analytic square root `g` of ξ and an analytic unit `v`.
2. **Global parity wall.** `Ξ` takes both strict signs above every height; ξ has critical-line
   zeros of odd order above every height; not every order of ξ is even. For `f^e·u` with `u`
   nonvanishing, parity of the order is void when `e` is even and preserved when `e` is odd.
3. **Frobenius torsion law.** If every `w(ρ)` is an algebraic integer and Galois conjugates of
   coordinates are coordinates of zeros, then RH is false; with contractive conjugate packets this
   is contradictory. Consequently no Frobenius with the zeros as eigenvalues carries Weil–Deligne
   integrality in the normalised coordinate.
4. **Per-prime integrality.** For nonreal `ρ`, `p^ρ` algebraic for one `p ≥ 2` makes `ρ` and
   `w(ρ)` transcendental; for three distinct primes not all of `p^ρ, q^ρ, r^ρ` are algebraic.
   Six exponentials theorem, formalised (new to Lean).
5. **Off-line indicator.** The escape multiplicity of the corpus's direct sub-unit anchor equals
   the off-line indicator; its sub-unit gap is the off-line condition; its vanishing everywhere is RH.
6. **Li sign oscillation.** Off the line the paired Li coefficients are positive for arbitrarily
   large `n`; unconditionally they are never eventually negative.

**Classification.** Every producer shape for RH in the corpus or the literature is one of four
theorem-closed kinds (fixed functionals; convergence in the strip; symmetries relating `s` to
`σ(s)`; two-factor presentations of ξ). The two remaining shapes, an amplified discrete anchor
and a direct sub-unit anchor, are refuted in their Weil–Deligne and Ferrero–Washington forms by
(3)–(4) and (5)–(6): normalised integrality is incompatible with RH, per-prime integrality fails
at three primes, and the negation of RH never yields a universal arithmetic statement, only
mean-zero oscillations.

## Gates

- [x] 0 → 1: routes stated with falsifiers (ULF-PIO/SLC/IND/ANC/INT/SYMP/META/F1-002, MUST-130)
- [x] 1 → 2: complete paper proofs on the cards named in the manuscript
- [x] 2 → 3: Lean modules `TwinRigidity`, `GlobalParityWall`, `FrobeniusTorsionLaw`,
  `SixExponentials.*`, `EscapeMultiplicityOffLineIndicator`, `LiSignOscillation`,
  `SymplecticDoublingFree`, `ZeroLedgerPairParity`, `MoebiusConvergenceZeroFree`,
  `XiLaguerreZeroSumIdentity`, `LaguerreKernelCounterexample`, `MertensOddWindowKnapsack`; all
  built, wired, axioms `propext, Classical.choice, Quot.sound`
- [x] 3 → 4: manuscript written; dependency closure listed per theorem

## Anti-theatre closure

- The torsion law's hypotheses are the exact transport of Weil–Deligne integrality (algebraic
  integers, Galois-closed eigenvalue set, unit-modulus conjugates); no hypothesis names a zero.
- The six exponentials theorem is proved from Siegel's lemma, the multipoint Schwarz lemma and
  Liouville's inequality only; no zero-density or Tijdeman estimate is assumed.
- The Li oscillation theorem is proved for arbitrary symmetric families; the mean value on the
  torus uses recurrence and the geometric sum, no equidistribution theorem.
- The indicator theorem is an identity of definitions, exhibited rather than assumed.
- No statement is RH-conditional except where RH appears as an explicit iff.

## Log
- 2026-09-02 — created at stage 4 with the manuscript.
