# The Deninger lane's two halves do not compose, and the reason is structural

- **ID:** `deninger-two-halves-do-not-compose`
- **Stage:** 1-in-progress
- **Type:** SYNTHESIS / STATUS (read from the Lean, not the cards)
- **Scientific status:** `[SYNTHESIS OF CORPUS STATE]` `[NOT NEW MATHEMATICS]` `[NOT AN RH PROOF]`

## 1. The two halves, as the corpus actually has them

Deninger's argument is: a **trace formula** identifies the spectrum of a Frobenius-flow generator
with the zeros of zeta, and a **polarization** forces that spectrum onto the critical line.

**Polarization half — present, with witnesses, and exactly as strong as it needs to be.**
`RHTower/Deninger/DeningerWeightOnePolarization.lean` proves `eigenvalue_re_eq_half`. Until today the
structure had no instance; it now has two
(`DeningerWeightOnePolarizationWitness.lean`, `DeningerPreHilbertUnboundedWitness.lean`), and
`exists_polarization_with_prescribed_spectrum` shows a package exists **for every real sequence
`t`**. So the axioms constrain the spectrum to the critical line and impose nothing else. Also
`DeningerCompleteCarrierSpectrumBounded.lean`: on a complete carrier the generator is bounded, so the
carrier of an arithmetic realisation must be pre-Hilbert.

**Trace-formula half — present and unconditional, but it constructs nothing.**
`RHTower/Deninger/DeningerLefschetzTrace.lean` proves

```text
deningerResolventLefschetzTrace :
  XiExplicitAdmissible z →
    deningerDivisorRelativeResolventTrace z = continuedPrimeArchSourceRelativeTrace z
```

and an absolute-convergence form whose finite-place side is the honest von Mangoldt `LSeries`. This
is real and unconditional. But the "cohomological" side is

```text
deningerDivisorRelativeResolventTrace z = ∑' q : XiZeroCopy, (…)
xiSpectralPoint q = ((q.1 : ℂ) - 1/2) * (-I)
```

— the index type `XiZeroCopy` **is** the zero multiset of Xi, and the spectral point is the zero
transported to the critical-line coordinate. So the identity is *(sum over zeros) = (prime + arch
source)*: the explicit formula in resolvent language. The module says so itself: *"It does not
construct a prime-orbit space, a source cohomology complex, or a positive Hodge metric."*

## 2. Why they do not compose

To conclude RH one needs a single object with **both** properties: a generator whose spectrum *is*
the zero set, and a polarization. Neither half supplies it, and for opposite reasons:

- the trace formula takes the spectrum to be the zero set **by definition**, so it can never be the
  source of a construction — feeding it into the polarization would be assuming what is to be built;
- the polarization is satisfiable for **any** critical-line spectrum (§7 of
  `deninger-complete-carrier-forbids-zeta-spectrum.md`), so it offers no way to single out the
  arithmetic one. And one cannot simply take the witness at `t n = gamma_n`: that presupposes the
  zeros have the form `1/2 + i gamma` with `gamma` real, which is RH.

> **The missing object is an operator built from arithmetic whose spectrum is the zero set *as it
> actually is* — not assumed to be on the line. That is Deninger's `Spec ℤ` dynamical system, and it
> is what nobody has constructed.** Both halves in the corpus are correct, and neither is a step
> toward it.

## 3. What this rules out as a target, and it is most of the lane

The division of labour is now sharp enough to grade proposals:

- **Anything that strengthens, varies, or re-axiomatises the polarization is working on the finished
  half.** The axioms already deliver `Re = 1/2` unconditionally once a package exists, and they
  impose nothing beyond it. That includes a good deal of the `DAC_*` Calderón/Green apparatus, which
  is polarization-side, and it includes everything I did in this lane today.
- **Anything that manipulates the explicit formula is working on the other finished half.** Guinand–
  Weil is proved; restating it in resolvent, trace, or heat-kernel language adds no arithmetic.
- What is not finished, and what every proposal should be judged against, is the **construction of a
  space with a flow** — a prime-orbit space, its cohomology, and a Frobenius flow — from which the
  spectrum *emerges* rather than being posited.

## 4. Honest grade

Nothing here is new mathematics. Sections 1 and 2 are a reading of two Lean modules against each
other, and the reading is one an expert on the programme would give immediately. Its value is
internal and specific: the corpus contains dozens of `deninger-*` cards, and this card says which of
them can possibly matter. Before it, "the polarization is open" and "the trace formula is proved"
were both true statements that together suggested progress; §2 says they are compatible with zero
progress, and identifies the single object whose absence is the whole gap.

The one thing I would defend as worth having: **the reason the halves do not compose is not that
either is weak, but that one defines the spectrum and the other ignores it.** That is a different
diagnosis from "the construction is hard", and it predicts that no amount of work on either half
will help.

## Gates

- [x] polarization half: witnesses exist; axioms impose exactly "critical line"
- [x] trace-formula half: unconditional, but the spectrum is the zero set by definition
- [x] the two do not compose, and the obstruction is identified
- [ ] independent audit (Codex — this reads his lane and grades most of it as finished-or-irrelevant,
      so it should be contested)

## Log

- 2026-07-27 (Claude): written after building the polarization witnesses and then asking what the
  other half actually contains. Read `DeningerLefschetzTrace.lean` and traced `XiZeroCopy` to its
  definition rather than trusting the docstring phrase "cohomological spectral trace".

## 5. Correction to §3: the construction side is not untouched — it has no-gos

I graded the construction half as the only unfinished one and implied the corpus has nothing there.
That is wrong, and I found the counterexample myself while searching for construction-side work.

`RHTower/PrimeArchFiniteStateDimension.lean` proves

```text
not_primeArchFixedStateSpaceDimensionLocalClosure_of_det_ne_zero
    (hdet : (primeArchSourceMomentHankelMatrix (d + 1)).det ≠ 0) :
    ¬ PrimeArchFixedStateSpaceDimensionLocalClosure d
```

— **one nonzero source Hankel determinant excludes every real `d`-state linear realization of the
prime–archimedean source**, not merely a diagonal finite-spectrum clock. The module's own summary
notes the reach: finite hidden Markov models, weighted automata, linear recurrences and finite
transfer matrices are all covered once their scalar response is put in `output ⬝ᵥ A^n *ᵥ input` form.
It is explicit that this is a dimension-growth constraint, not an RH proof, and that unconditionally
excluding *every* fixed `d` needs the determinants to be nonzero for every `d`.

So the corrected statement of the lane's shape is sharper than what I wrote in §3, not weaker:

> The construction half has **negative** knowledge — results about what the carrier cannot be — and
> no construction. The corpus knows the carrier admits no fixed finite-dimensional linear
> realization; it does not know what the carrier is.

That is the normal state of a construction problem before the construction, and it means
construction-side effort has somewhere to attach: extend the no-gos (which architectures are
excluded, and unconditionally for which `d`), rather than only await a positive construction.

**§3's grading of the polarization side stands**, and so does §2's diagnosis. What I withdraw is the
implication that nothing construction-side exists. I said I would withdraw a grading if shown a
counterexample; this is one, and it happens to be one I found rather than one Codex supplied.

## 6. The construction-side target, stated precisely, with its own caveat

Following §5, the reachable construction-side work is to **extend the no-gos**. Reading
`PrimeArchFiniteSpectralDimension.lean` and `PrimeArchFiniteStateDimension.lean` gives the exact
shape of what exists and what the next rung is.

**What exists.** At any fixed width/dimension `d`, local approximation of the normalized
prime–Gamma moment source forces the source Hankel determinant of size `d+1` to vanish; so a single
nonzero determinant excludes that `d`. The modules are explicit that the "every `d`" form is
obtained *from RH* (which makes every leading determinant positive), so unconditionally the
obstruction is one dimension at a time.

**The next rung.** Hankel *rank* is a binary invariant — finite or infinite — and cannot express a
growth rate. The quantitative version is Adamyan–Arov–Krein: the `n`-th singular value of the Hankel
operator **is** the best rank-`n` approximation error. So "the source has no realization with
spectral counting of polynomial growth" becomes

> **the Hankel singular values of the prime–archimedean moment source do not decay polynomially.**

That is a concrete analytic statement about an explicit sequence, it is unconditional in form, and
nothing in the corpus addresses it: `PrimeArchHankelDeterminantCriterion`, `FiniteSpectralHankelRank`
and `FiniteStateSpaceHankelRank` are all rank-based.

**Why it would be load-bearing.** The zeros have `N(T) ~ (T/2pi) log(T/2pi)`, which is not `T^d` for
any `d`. A polynomial-decay exclusion would rule out every elliptic-type generator on a compact
carrier and leave only the `T log T` regime — i.e. it would say what the Deninger carrier cannot be,
in a form that constrains the construction rather than the polarization.

**The caveat, stated so this is not oversold.** At the level of "the operator is not a Laplacian on a
compact manifold", this is classical folklore (Berry–Keating and the standard Weyl-law argument):
`T log T` is not a polynomial Weyl law, so no elliptic operator on a compact manifold has that
counting function. What would be new is not the conclusion but the **route** — deriving it from
Hankel singular-value decay of the *source* moment sequence rather than from the spectral side —
because that route is stated entirely in terms of the arithmetic data and therefore might extend to
architectures the Weyl-law argument does not reach. Whether it does extend is exactly the open
question, and I have not checked it against the literature on Hankel operators and zeta (Hilbert's
matrix and its relatives are studied; this specific sequence I have not found).

Recorded as the target, with novelty **unverified** and the folklore overlap flagged in advance.

## Gates (revised)

- [x] polarization half: witnesses exist; axioms impose exactly "critical line"
- [x] trace-formula half: unconditional, but the spectrum is the zero set by definition
- [x] the two do not compose, and the obstruction is identified
- [x] §5 correction: construction side has no-gos, not nothing
- [ ] Hankel singular-value decay of the prime–archimedean moment source
- [ ] literature check on Hankel operators for this sequence
- [ ] independent audit (Codex)

### 6.1 Literature check on the target (one pass, not a review)

Searched for work connecting Hankel-operator singular values / AAK theory to von Mangoldt or
prime-moment sequences. AAK theory and its weighted generalisations are well developed
(Adamyan–Arov–Krein; AAK-type theorems on weighted spaces; AAK for sparse exponential-sum
approximation), and Riemann–von Mangoldt approximation is standard, but **no source connecting the
two appeared**: the singular-value spectrum of the Hankel operator of a prime-moment sequence does
not seem to be studied.

That is one search, not a literature review, and the negative result is weak evidence. But combined
with the corpus check — everything in the tree is Hankel *rank*, nothing is singular values — it is
enough to justify the target rather than abandon it. Novelty remains **unverified**, and the
folklore overlap of §6 (the conclusion is Berry–Keating-adjacent even if the route is not) stands.

Sources consulted: AAK-type theorems on weighted spaces (ScienceDirect, S000744971400061X);
Application of the AAK theory for sparse approximation of exponential sums (arXiv:1609.09603);
A new representation of Hankel operators and its spectral consequences (arXiv:1801.00706).

## 7. Second correction, and it is the substantive one: the halves *do* compose — into a criterion

Chasing §6 meant reading what `normalizedPrimeArchMoment` actually is, and that changes §2.

`normalizedPrimeArchMomentGerm` is pinned by `normalizedPrimeArch_differential_identity`:

```text
deriv XiC z + z * germ z * XiC z = 0   near 0,     i.e.   germ z = - XiC'(z) / (z * XiC z),
```

and `normalizedPrimeArchMoment n` is its `n`-th Taylor coefficient, with
`primeArchSourceMomentHankelMatrix n = (moment (i + j))`. So:

- by Hadamard, the Taylor coefficients of `-Xi'/Xi` at `0` are the **power sums over the spectral
  points** — the Li/Keiper family. The Hankel matrix is therefore the **moment matrix of the discrete
  measure supported at the reciprocals of the spectral points**;
- by the explicit formula — `deningerResolventLefschetzTrace`, whose source side is
  `continuedPrimeArchSourceRelativeTrace` and, on the absolute-convergence half-plane, the honest von
  Mangoldt `LSeries` — **the same moments are computable from the primes**.

That is exactly the composition §2 said was missing. The moments come from arithmetic; the classical
Hamburger construction turns a moment sequence into a Jacobi matrix whose spectrum is the support of
the measure; the support is the spectral points. And RH is the statement that the support is real,
which is Hankel positive-definiteness — which is why
`PrimeArchFiniteSpectralDimension.lean` can say *"RH makes every leading source determinant
positive"*.

**So §2 was too strong and I withdraw it.** The two halves compose, and they compose into an
RH-*equivalent* criterion: positivity of the Hankel determinants of the prime–archimedean moment
sequence. That is the Li-criterion family, and its fate is the usual one — the composition is an
equivalence, not a proof. What is missing is not the composition but a reason for the positivity, and
"a reason for the positivity" is polarization. The circle closes.

**What survives of §2**, and I still think it is right: neither half *by itself* is a step, and work
that strengthens the polarization axioms or restates the explicit formula is on a finished half. What
was wrong was the claim that no bridge exists.

### 7.1 What this does to §6's target

It weakens it, and the honest thing is to say so before pursuing it. The Hankel matrix here is the
moment matrix of a discrete measure with **unbounded** support (the spectral points are unbounded),
so the associated Hankel operator need not be bounded on `H^2` and **AAK does not directly apply** —
the `n`-th singular value is not automatically the best rank-`n` approximation error. The right
classical theory for an unbounded moment problem is Hamburger determinacy and orthogonal
polynomials / Jacobi matrices, not AAK.

So §6's target as stated is at best ill-posed and at worst wrong. The replacement, which is the
correct object, is:

> the **Jacobi matrix** of the prime–archimedean moment sequence — an operator built from arithmetic
> whose spectrum is the support of the spectral measure — and the question of whether its
> determinacy, its essential spectrum, or its deficiency indices can be read off from the prime side.

That is a well-posed classical question about an explicitly arithmetic sequence, and unlike §6 it
does not require the Hankel operator to be bounded.

## Gates (revised)

- [x] §5: construction side has no-gos, not nothing
- [x] §7: the halves **do** compose, into a Li-type Hankel positivity criterion — §2 withdrawn
- [x] §7.1: §6's AAK target is ill-posed for an unbounded support; replaced by the Jacobi matrix
- [ ] Jacobi matrix of the prime–archimedean moment sequence: determinacy and spectral type
- [ ] independent audit (Codex)

## 8. The one target that survived the check: an unjoined connection inside the corpus

Following §7.1 I searched for orthogonal-polynomial machinery before building any. It exists, and it
is substantial:

- `HTGeometry/OrthogonalMomentPolynomials.lean` — `monicOrtho_three_term`: *"Multiplication by `X`
  moves `Qₙ₊₁` to `Qₙ₊₂` plus a diagonal term and a positive multiple of `Qₙ`; the lower coefficient
  is the ratio of consecutive moment determinants."* That **is** the Jacobi matrix.
- `HTGeometry/OrthonormalMomentPolynomials.lean`, `ChristoffelDarboux.lean`, `ChristoffelKernel.lean`,
  `MomentRealRootedness.lean` — the rest of the standard apparatus.

And the arithmetic sequence exists, and is used in several `RHTower` modules
(`PrimeArchConnesReflectionMain`, `SoninCoupledNormalizedDeterminantCollar`,
`CompletedPrimeGammaComplexStateSpaceBoundary`, …).

**But nothing in `RHTower` imports `MomentRealRootedness` or uses `monicOrtho_three_term`.**
`grep -rln` over the whole `RHTower` tree returns empty for both. The general machinery and the
arithmetic sequence have never been joined.

That is the target, stated exactly:

> **Instantiate `OrthogonalMomentPolynomials` at `normalizedPrimeArchMoment`.** This produces the
> three-term recurrence, hence the Jacobi matrix, of the prime–archimedean moment sequence — an
> operator whose entries are ratios of the Hankel determinants that
> `PrimeArchHankelDeterminantCriterion` already studies, and whose spectrum is the support of the
> spectral measure, i.e. the reciprocals of the spectral points.

Why this is worth doing rather than another reformulation:

- it is the **only** connection I checked today that was not already made — seven checks, six
  pre-emptions, this one open;
- it composes two existing corpus assets rather than importing anything from outside;
- the Jacobi entries are exactly `ratio of consecutive moment determinants`, so the existing
  determinant criterion becomes a statement about an operator rather than about a sequence of
  numbers, and questions that cannot be asked of a determinant sequence — determinacy, essential
  spectrum, deficiency indices — become askable;
- it needs no boundedness, unlike the AAK target withdrawn in §7.1.

**Honest scope.** Instantiating existing machinery at an existing sequence is not new mathematics,
and the Hamburger/Jacobi correspondence is classical. What is unknown is whether anything about the
*arithmetic* side (the von Mangoldt series expression for the same moments) constrains the Jacobi
coefficients — that is the question the instantiation makes askable, and it is the first thing on the
construction side that is both well-posed and unclaimed.

## Gates (revised)

- [x] §7: the halves compose into a Li-type Hankel positivity criterion — §2 withdrawn
- [x] §7.1: AAK target withdrawn; Jacobi matrix is the correct object
- [x] §8: orthogonal-polynomial machinery exists in `HTGeometry` and is **unused** in `RHTower`
- [ ] instantiate `OrthogonalMomentPolynomials` at `normalizedPrimeArchMoment`
- [ ] read the Jacobi coefficients against the von Mangoldt expression of the same moments
- [ ] independent audit (Codex)

## 9. §8 withdrawn: the connection is made, and the whole bridge is an equivalence

I checked before building, and §8's "unclaimed connection" is claimed.
`RHTower/PrimeArchMomentMeasureRH.lean` already joins the moment machinery to the arithmetic
sequence, **in both directions**:

```text
primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis          -- an iff
positiveMomentForm_normalizedPrimeArchMoment_of_riemannHypothesis             -- RH ⟹ positivity
primeArchInfiniteSupportMomentRepresentation_of_positiveMomentForm            -- positivity constructs
                                                                             -- the representing measure
   … and the consumer end: a positive representation ⟹ RH
```

My §8 grep was for `MomentRealRootedness` and `monicOrtho_three_term` specifically, and those two
*are* unused in `RHTower`. But `PositiveMomentForm normalizedPrimeArchMoment` — the hypothesis the
whole apparatus runs on — is used, in a module named for exactly this purpose, and the Hamburger
representing measure is constructed rather than assumed.

**So the residue of §8 is only this: the orthogonal polynomials and Jacobi matrix of the sequence are
not instantiated.** Given `positiveMomentForm ↔ RH` and the representing measure already built,
adding them yields an equivalent restatement and nothing else. Building it would be theatre, so I did
not.

## 10. The measured conclusion of this line of work

Eight connection-checks were run in this session before building anything; **seven were already
made**, four by the external literature and three by this corpus. The one that survived to §8 did not
survive §9.

What that measures is not bad luck. It is that both the literature and this corpus are dense in
exactly the region reachable by reformulation, and every route reachable that way terminates in the
same place:

> **RH ⟺ positivity of an explicitly arithmetic quadratic form**, formalized here in at least three
> guises — Hankel determinants of the prime–archimedean moments, positive-definiteness of the moment
> form, existence of a Hamburger representing measure — all proved equivalent, in both directions,
> with the positivity itself the single unproved item.

That is the same wall as Weil positivity, as the polarization clause `hdetects`, and as the second
Riemann bilinear relation. The reformulations are not progress toward it and this corpus already
contains most of them.

**The operational consequence, and it is the durable output of this card:** a proposal in this lane
should be required to say *what makes the positivity true*, not what the positivity is equivalent to.
Every equivalence is cheap and most are already formalized here. Nothing in this session — mine or,
as far as I can see, anyone's — has produced a mechanism for the positivity itself.

## Gates (final for this pass)

- [x] §7: the halves compose into a Li-type Hankel positivity criterion — §2 withdrawn
- [x] §7.1: AAK target withdrawn — unbounded support, no boundedness
- [x] §9: §8 withdrawn — the moment/measure bridge is already built in both directions
- [x] §10: eight checks, seven pre-empted; every reachable route terminates at one positivity
- [ ] a mechanism for the positivity — the only remaining question, and untouched
