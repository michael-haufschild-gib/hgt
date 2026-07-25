# Global Hurwitz differential independence over the whole Xi divisor

**Stage:** 3 — formalized, unconditional.
**Module:** `formal/GaloisForLFunctions/RHTower/XiDivisorHurwitzGlobalIndependence.lean`
**Axioms:** `propext, Classical.choice, Quot.sound`. Lint gate: passed.

## Statement

```lean
theorem xi_divisor_hurwitz_differentialIndependent :
    DifferentialIndependent (RatFunc ℂ)
      (fun ρ : XiDivisorSupport => continuedHzetaUpperEndMero ((ρ : XiDivisorSupport) : ℂ))
```

In words: **the analytically continued Hurwitz functions `H(ρ, ·)` indexed by *all* nontrivial zeros
of the Riemann zeta function, simultaneously, satisfy no algebraic differential relation over `ℂ(a)`
whatsoever.** No finite combination of them and their derivatives, with rational-function
coefficients, vanishes identically unless it is trivial.

Unconditional. No Riemann Hypothesis, no simplicity of zeros, no correlation or linear-independence
hypothesis.

## Mechanism

The Hurwitz monodromy character is `mu(s) = exp(2 pi i s)`, and `mu(s) = mu(t) ⟺ s - t ∈ ℤ`. The
open critical strip has width **exactly one**, which is exactly the period of `mu`. Hence distinct
nontrivial zeros are automatically monodromy-separated, and `0 < Re rho < 1` automatically gives
`mu(rho) ≠ 1`. Nothing about the *location* of the zeros is used — only that they inhabit a strip
whose width matches the character's period.

So an object about which almost nothing is known unconditionally (the placement of the zeros) yields
a complete structural certainty about the family of classical functions it indexes.

## Relation to what already existed

- **Corpus:** `RHTower.xi_zero_hurwitz_differentialIndependent` gives the same conclusion for every
  *finite* injective family. The global statement was absent, and could not be derived in place: the
  finitary interface `differentialIndependent_of_forall_finite_subfamily` requires
  `DifferentialAlgebra (RatFunc ℂ) upperEndMeroField`, an instance the corpus did not contain.
- **New infrastructure proved here:** `globalXiRatFuncDifferentialAlgebra` — the rational coordinate
  field `ℂ(z)` embeds into the upper-end meromorphic field as a *differential* subfield, i.e. the
  embedding intertwines the formal derivative with the analytic one. Proved by `RatFunc.induction_on`
  with the quotient rule on both sides, reducing to `upperEndMero_deriv_polyEval` and
  `ratFuncCoordinateDerivation_algebraMap`. Also supplied: `CharZero upperEndMeroField` and
  `Differential (RatFunc ℂ)` in this context.
- **Literature audit (recorded in `0-backlog/xi-zero-hurwitz-novelty-audit.md`):** the published work
  on Hurwitz functions indexed by zeta zeros concerns *joint universality* (Lith. Math. J. 2019) and
  is **conditional** on weak Montgomery pair correlation plus `ℚ`-linear independence. Differential
  independence of that family appears nowhere I could find, in either the finite or the global form.

## Honest assessment

**Novelty:** `[NOVELTY UNVERIFIED]` in the strict sense — absence from all literature cannot be
proved by search. What was done: corpus grep (finite version present, global absent) and targeted
literature search (nothing on differential independence for this index set; the one nearby result is
about a different property and is conditional).

**Significance:** the honest case is that this is an *infinite* explicitly-indexed family of
classical special functions proved completely differentially independent with no hypotheses, where
the index set is arithmetically opaque. The honest counter-case is that the finite version already
existed and the upgrade is finitary; the genuinely new mathematical content is the differential
subfield instance, and the genuinely new *statement* is the global one. Both are real; neither is
revolutionary. Recorded at that level and no higher.

## Next

The same argument applies verbatim to any set of points in an open strip of width one. The natural
extension is the union of nontrivial zeros of *any* family of Dirichlet `L`-functions — all lie in
the same strip — giving one differentially independent Hurwitz family indexed by the zeros of the
whole family at once, again unconditionally. That is the next statement to formalize, and it is a
strictly stronger fact that no longer mentions zeta alone.
