# A complete carrier forbids the zeta spectrum: the "nuclear before Hilbert" rule is Hellinger–Toeplitz

- **ID:** `deninger-complete-carrier-forbids-zeta-spectrum`
- **Stage:** 1-in-progress
- **Type:** STRUCTURAL NO-GO (formalized)
- **Scientific status:** `[LEAN-PROVED, AXIOM-CLEAN]` `[MATHEMATICS IS CLASSICAL — see §5]`
  `[NOT AN RH PROOF]`
- **Module:** `formal/GaloisForLFunctions/RHTower/Deninger/DeningerCompleteCarrierSpectrumBounded.lean`

## 1. The observation

`DeningerWeightOnePolarization` declares

```text
theta : Module.End ℂ H
```

— an **everywhere-defined** linear endomorphism — and the module proves
`shiftedTheta_skewSymmetric`: `⟪(theta − 1/2) x, y⟫ = − ⟪x, (theta − 1/2) y⟫`.

Multiplying a skew-symmetric operator by `I` makes it symmetric. The **Hellinger–Toeplitz theorem**
(mathlib: `LinearMap.IsSymmetric.continuous`) says an everywhere-defined symmetric operator on a
**complete** inner-product space is continuous. Therefore, on a complete carrier:

```text
isSymmetric_I_smul_shiftedTheta      I · (theta − 1/2) is symmetric
theta_continuous                     [CompleteSpace H] → Continuous theta
exists_eigenvalue_norm_bound         [CompleteSpace H] → ∃ C, every eigenvalue has ‖rho‖ ≤ C
not_completeSpace_of_unbounded_spectrum
                                     unbounded spectrum → ¬ CompleteSpace H
```

All axiom-clean `[propext, Classical.choice, Quot.sound]`.

## 2. What it says about the arithmetic case

The arithmetic realisation must have the eigenvalues of `theta` be `1/2 + i·gamma` over **all** zeros
of zeta, and the `gamma` are unbounded. By `exists_eigenvalue_norm_bound` that is impossible on a
complete carrier. Hence:

> **No arithmetic realisation of Deninger's polarized weight-one package exists on a Hilbert space.
> The carrier must be an incomplete pre-Hilbert space.**

This is not a defect of the package and it does not kill the lane. It identifies, with a classical
theorem, exactly why the corpus's own prescription is mandatory.

## 3. It derives the corpus's prescription instead of assuming it

`deninger-source-native-arithmetic-cohomology-roadmap.md` prescribes *"Smooth suspension and unit
augmentation must therefore precede Hilbert completion … Nuclear cohomology must be formed first"*,
and `deninger-arithmetic-calderon-green-intermediate-extension.md` lists as a falsifier *"Orthogonal
Hilbert completion before incidence makes the scalar quotient seminorm zero."* Both were stated as
design rules learned from failures.

§1 turns the rule into a consequence: **completion forces the generator bounded, and a bounded
generator cannot carry the zeta spectrum.** The prescription is not stylistic and not a workaround —
it is forced, and the forcing theorem is from 1927.

This also corrects the emphasis of my own earlier work in this lane. In
`deninger-lane-reduces-to-one-hypothesis.md` §4 I showed that a *weighted* completion can support the
invariant object when an unweighted one cannot, and treated that as the repair. It is a repair for
existence of invariant vectors; it does **not** repair this, because Hellinger–Toeplitz applies to
any complete carrier whatever the weight. Weighting the completion does not make the generator
unbounded. The two obstructions are independent and this one is the more basic.

## 4. Consequence for what to build next

I proposed to Codex an infinite-dimensional witness with unbounded spectrum as the next rung. **That
is impossible on a Hilbert space** — §1 forbids it. The correct next rung is therefore:

- a **pre-Hilbert** (incomplete) carrier with an everywhere-defined `theta` whose eigenvalues are
  `1/2 ± i t_n` with `t_n → ∞`, satisfying all the polarization axioms.

Such a carrier is easy to describe informally — take the algebraic direct sum `⊕_n ℂ²` of the
finite-dimensional witnesses of `deninger-weight-one-polarization-witness.md` at parameters
`t_n → ∞`, which is dense in the `ℓ²` sum and incomplete, with `theta` diagonal and unbounded. That
is the honest shape of the arithmetic carrier: **algebraic direct sum, not Hilbert sum**, and it
matches "nuclear cohomology must be formed first" exactly.

Formalising it is the next task and it is well defined.

## 5. Novelty, stated hostilely

- **Hellinger–Toeplitz is 1927 and the corollary is folklore.** In the Hilbert–Pólya literature it is
  standard that the sought operator must be unbounded and therefore not everywhere defined; that is
  why one works with self-adjoint extensions of densely defined operators. I claim no novelty for the
  mathematics.
- **What is new is local and worth having**: the corpus's formalized package declares `theta` as a
  total `Module.End`, and nobody had noticed that this plus completeness plus the proved skewness
  bounds the spectrum. The package as stated is therefore only realisable pre-Hilbert, and the design
  rule the corpus arrived at empirically is a theorem.
- Grade: `[BRIDGE]` as mathematics, `[useful]` as corpus knowledge, because it converts a rule of
  thumb into a proof and redirects the next construction from an impossible target to a possible one.

## Gates

- [x] `I · shiftedTheta` symmetric — Lean
- [x] Hellinger–Toeplitz applied: `theta` continuous on complete carriers — Lean
- [x] eigenvalue modulus bounded by the operator norm — Lean
- [x] unbounded spectrum ⟹ carrier incomplete — Lean
- [ ] pre-Hilbert witness with `t_n → ∞` (algebraic direct sum of the 2-dimensional witnesses)
- [ ] independent audit (Codex)

## Log

- 2026-07-27 (Claude): found while asking what an infinite-dimensional witness for
  `DeningerWeightOnePolarization` would look like. The answer is that on a Hilbert space it cannot
  exist, which is more informative than the witness would have been.

## 6. The redirect is executed: a pre-Hilbert witness with unbounded spectrum

§4 said the correct next rung is a **pre-Hilbert** carrier with unbounded spectrum on the critical
line, and that it is well defined. It is now built:
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerPreHilbertUnboundedWitness.lean`, axiom-clean.

**Carrier.** The *algebraic* direct sum `⨁_(n : ℕ) ℂ²`, realised as `(ℕ × Fin 2) →₀ ℂ`, with an
inner product built by hand as an `InnerProductSpace.Core`:

```text
innerF x y = ∑_(p ∈ y.support) conj (x p) * y p
```

Hermitian symmetry needs the one support-union argument (`innerF_eq_sum_of_subset`); additivity and
conjugate-linearity in the first slot are free because the index set is `y.support` on both sides;
definiteness comes from the finite sum of squared norms.

**Hodge star.** `sigmaMap x q = eps q * conj (x (sw q))` with `sw` the blockwise coordinate swap and
`eps` the blockwise sign, giving `sigmaMap_sq : sigma (sigma x) = -x` — the odd `K`-real structure.

**Generator.** `thetaMap x q = lam q * x q` with `lam (n,0) = 1/2 + i n`, `lam (n,1) = 1/2 - i n`.
The two facts that make every axiom work are `conj (lam (sw p)) = lam p` and
`conj (lam p) + lam p = 1`.

**Cup trace, for free.** Rather than defining the symplectic form separately, take

```text
cupForm a b = - ⟪sigma b, a⟫ .
```

Then `inner_eq_cup_star` is immediate from `sigma^2 = -1`, and bilinearity holds because `sigma` and
the first inner-product slot are each conjugate-linear, so their composite is linear. This removes
the whole symplectic-form construction from the file; it is determined by the star and the metric.

**Result.** `polarization : DeningerWeightOnePolarization Carrier` verifies every axiom, and

```text
thetaMap_eigen n : theta (single (n,0) 1) = (1/2 + i n) • single (n,0) 1
```

so the spectrum contains `1/2 + i n` for every `n` — **unbounded, and on the critical line**.
Feeding this to `eigenvalue_re_eq_half` returns `Re = 1/2`, as it must.

**And the incompleteness is derived, not assumed.**

```text
not_completeSpace_carrier : ¬ CompleteSpace Carrier
```

is proved by applying `not_completeSpace_of_unbounded_spectrum` of §1 to this very package. The
carrier is not complete *because* its spectrum is unbounded — the no-go is used constructively.

### 6.1 What this settles

- The polarization axioms are **consistent with an unbounded spectrum on the critical line**. Before
  this, the only witness was two-dimensional with a two-point spectrum, and one could have suspected
  the axioms collapse in the regime the arithmetic case needs.
- The two obstructions are now cleanly separated and both are exhibited: completeness bounds the
  spectrum (§1), and dropping completeness removes that bound (§6).
- **It is still not the arithmetic cohomology.** The spectrum here is `{1/2 ± i n : n ∈ ℕ}`, chosen
  by hand; the arithmetic case requires it to be the zeta zeros, which is RH. What the witness shows
  is that the *shape* of the requirement is satisfiable, so the lane is not obstructed at this level.

## Gates (revised)

- [x] `I · shiftedTheta` symmetric — Lean
- [x] Hellinger–Toeplitz: `theta` continuous on complete carriers — Lean
- [x] eigenvalue modulus bounded by the operator norm — Lean
- [x] unbounded spectrum ⟹ carrier incomplete — Lean
- [x] pre-Hilbert witness with unbounded spectrum on the critical line — Lean, axiom-clean
- [x] its incompleteness derived from the no-go rather than assumed — Lean
- [ ] independent audit (Codex)

## 7. How strong are the polarization axioms? Exactly "critical line", and nothing more

The witness of §6 was built with the specific spectrum `1/2 ± i n`. It generalises for free, and the
generalisation is the more informative statement. `exists_polarization_with_prescribed_spectrum`,
axiom-clean:

```text
for every  t : ℕ → ℝ  and every n,
  (polarization t).theta (single (n,0) 1) = (1/2 + i·t n) • single (n,0) 1
```

Every proof in §6 used only two facts about the eigenvalue family — `conj (lam (sw p)) = lam p` and
`conj (lam p) + lam p = 1` — and both hold for an arbitrary real `t`. Therefore:

> **The polarized weight-one axioms constrain the spectrum to lie on the critical line, closed under
> conjugation, and impose nothing else.** No density, no growth rate, no arithmetic property of the
> eigenvalue family is forced by the polarization.

`not_completeSpace_carrier` is correspondingly stated for any unbounded `t`.

### 7.1 Why this matters for the programme

Deninger's argument has two halves: a **trace formula** identifying the spectrum of the
Frobenius-flow generator with the zeros of zeta, and a **polarization** forcing that spectrum onto
the critical line. §7 says the second half is *exactly* strong enough to do its job and no stronger:
it is a purity mechanism, not a source of arithmetic.

The practical consequence is a division of labour that can be stated without hedging:

- anything about *which* points are in the spectrum — their density `N(T) ~ (T/2π) log(T/2π)`, their
  arithmetic, their relation to primes — must come entirely from the trace formula;
- the polarization contributes one thing, `Re = 1/2`, and contributes it unconditionally once the
  package exists.

So a proposal in this lane should be judged by what it does for the trace-formula half. A proposal
that strengthens or varies the polarization axioms is working on the half that is already finished.

### 7.2 Honest grade

The generalisation is a parameter substitution in an existing proof; it took ten minutes and no new
idea. Its value is entirely in what it rules out as a target, and in making "the polarization is not
where the arithmetic lives" a theorem rather than an impression.

## Gates (revised)

- [x] pre-Hilbert witness with unbounded spectrum — Lean, axiom-clean
- [x] incompleteness derived from the no-go — Lean
- [x] spectrum arbitrary on the critical line: the axioms impose nothing further — Lean
- [ ] independent audit (Codex)
