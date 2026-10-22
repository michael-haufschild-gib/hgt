# Novelty audit: Xi-zero Hurwitz differential independence

**Stage:** 0 — audit record, no new theorem.
**Procedure note:** this is the first item on which Gate 1 (literature + corpus audit) was run
*before* any construction, per the rule adopted in `euler-defect-controls-displacement.md`.

## What I intended to prove

> For any finite set of distinct nontrivial zeros `rho_1, ..., rho_n` of zeta, the analytically
> continued Hurwitz functions `H(rho_1, ·), ..., H(rho_n, ·)` are differentially independent over
> `ℂ(a)`.

Mechanism: the Hurwitz monodromy character is `mu(s) = exp(2 pi i s)`, and
`mu(s) = mu(t) ⟺ s - t ∈ ℤ`. The open critical strip has width **exactly 1**, which is exactly the
period of `mu`. So distinct nontrivial zeros are automatically monodromy-separated, with no
hypothesis. Non-integrality (`mu ≠ 1`) is likewise automatic since `0 < Re rho < 1`.

## Corpus audit — ALREADY PRESENT

`RHTower/XiZeroHurwitzDifferentialIndependence.lean`:

```lean
theorem xi_zero_hurwitz_differentialIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ) :
    DifferentialIndependent (RatFunc ℂ)
      (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ))
```

Verified unconditional: axioms `propext, Classical.choice, Quot.sound`. The proof is exactly the
mechanism above. **Claiming this would have been duplication presented as discovery.** The check
cost one grep.

## Literature audit

Closest published work on this index set: *Joint universality of Hurwitz zeta-functions and
nontrivial zeros of the Riemann zeta-function* (Lithuanian Math. J., 2019) — shifts of Hurwitz zeta
indexed by the **imaginary parts** of zeta zeros approximate arbitrary analytic functions. That
result is **conditional** on a weak form of the Montgomery pair correlation conjecture together with
`ℚ`-linear independence of `{log(m + α_j)}`.

**Do not overclaim from this.** Joint universality and differential independence are different
properties; the conditionality of the former says nothing directly about the novelty of the latter.
What the comparison does establish is that the *index set* "Hurwitz functions labelled by zeta
zeros" is a studied object, and that the studied results on it are conditional while the corpus's is
not. Whether `xi_zero_hurwitz_differentialIndependent` is novel **remains unverified** and would need
a specialist in differential Galois theory to settle.

## Gap actually identified

The corpus has only the **finite** law. The global form — no relation among the Hurwitz functions
indexed by *all* nontrivial zeros simultaneously — is not present. It follows from
`differentialIndependent_of_forall_finite_subfamily` (`HTGeometry/DifferentialPointedCollisionMatroid.lean`),
but that lemma requires `[Differential (RatFunc ℂ)]`, `[DifferentialAlgebra (RatFunc ℂ) upperEndMeroField]`
and `[CharZero upperEndMeroField]`, which are assembled ad hoc per file in this corpus and are not
available in the `XiZeroHurwitz...` instance context. Supplying them is the concrete blocked step.

**Honest assessment of that increment:** it is a routine finitary upgrade of an existing theorem, not
a significant new fact. Recorded as a gap, not as a discovery.

## Outcome

No novel significant fact produced. What the turn produced is procedural: audit-before-build worked
and prevented a false novelty claim.

## Second candidate, audited and rejected: the trivial/nontrivial dichotomy

> For a zero `s` of zeta, `H(s, ·)` is differentially algebraic over `ℂ(a)` **iff** `s` is a trivial
> zero — so the classical trivial/nontrivial bookkeeping distinction coincides exactly with a
> differential-algebraic dichotomy (degenerate versus hypertranscendental).

**Rejected as insignificant.** It decomposes into:

- trivial zero `s = -2k` ⟹ `ζ(-n, a) = -B_{n+1}(a)/(n+1)`, a Bernoulli polynomial, hence in `ℂ(a)`.
  Textbook.
- nontrivial zero ⟹ hypertranscendental. This is `xi_zero_hurwitz_differentialIndependent`
  specialised to a singleton — already in the corpus.

So it is a **combination of a classical evaluation with an existing corpus theorem**, and the only new
content is the framing. Framing is not a fact. Literature search around Hurwitz hypertranscendence in
the second variable returned nothing decisive either way (it returned Hilbert 1900 on `zeta` in `s`,
and Van Gorder / Prado--Klinger-Logan on infinite-order operators), so novelty is unresolved — but
significance fails independently of novelty, which settles it.

## Third candidate: global independence — blocked, and routine anyway

`differentialIndependent_of_forall_finite_subfamily` requires
`[Differential (RatFunc ℂ)]`, `[DifferentialAlgebra (RatFunc ℂ) upperEndMeroField]`,
`[CharZero upperEndMeroField]`. The first and third are constructible
(`ratFuncCoordinateDifferential` in `MeromorphicGammaOrbit`; `charZero_of_injective_ringHom
upperEndComplexToMero.injective`). The second **does not exist in the corpus**: the available
instances are `DifferentialAlgebra (RatFunc ℂ) (meroField U)` and
`DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField`, neither of which is the
needed pair. Building it means proving the coordinate map `ℂ(z) → upperEndMeroField` intertwines the
derivations — plumbing, not mathematics.

And by the standard applied above, a finitary upgrade of an existing theorem is not a significant new
fact regardless.

## Turn outcome

**No novel significant fact produced.** Three candidates generated, three rejected on audit:
duplication, insignificance-by-decomposition, and routine-upgrade-plus-missing-plumbing. Recorded so
none is re-attempted.

What is actually needed, stated plainly: a question whose answer is not a recombination of (i) the
width-one strip, (ii) the monodromy character, (iii) classical special-value evaluations. Every
candidate above is such a recombination. The corpus's Hurwitz layer appears to be *saturated* at this
level — its content is exhausted by "`mu` is injective on a width-one strip" — and further mining of
it will keep producing recombinations. The next attempt must start from a different corpus layer.
