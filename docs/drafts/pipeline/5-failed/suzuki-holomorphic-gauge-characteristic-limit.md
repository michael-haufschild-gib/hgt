# Suzuki holomorphic-gauge characteristic limit no-go

- **ID:** `suzuki-holomorphic-gauge-characteristic-limit`
- **Stage:** 5-failed / Route G terminal result
- **Type:** SOURCE-COMPLETE NO-GO / POSITIVE MEROMORPHIC SURVIVOR
- **Scientific status:** `[THEOREM] [PAPER-PROVED] [LEAN TARGET IDENTIFIED]`
  `[ROUTE G RETIRED] [NOT AN RH PROOF] [NO COMPUTATION]`
- **Primary source under audit:** Masatoshi Suzuki, *Weil's quadratic form via the screw
  function*, arXiv:2606.09096v1 (2026), Theorem 1.5, Corollary 1.6, and Sections 7--8
- **Prior formal core:** `SuzukiCharacteristicEntireLimitNoGo.lean`

## Terminal verdict

`[THEOREM] [SUZUKI-HOLOMORPHIC-GAUGE-CHARACTERISTIC-LIMIT-NO-GO]`

Suzuki's displayed one-angle limit program is impossible in its analytic characteristic-function
category.  The obstruction is independent of source operator, aperture schedule, form shift,
extension angle, and normalization:

> No locally uniform sequence on `C` of finite holomorphic exponential gauges times entire
> real-zero characteristic functions can converge to
> `z^2 XiC(z) / XiC'(z)`.

This closes Route G when Route G means Suzuki's published source-to-characteristic limit.  The
finite-aperture self-adjoint and all-angle theorems remain valid.  They do not rescue the displayed
limit: they expose a different, meromorphic two-angle problem recorded below as positive survivor.

## [CORPUS]

Internal corpus already contained two parts of the terminal argument, but not their exact
holomorphic-gauge closure as Suzuki states it.

1. `SuzukiCharacteristicEntireLimitNoGo.lean` proves that the legacy ordinary-entire compact-limit
   wall is false.  It supplies positive real consecutive centered-Xi zeros under the RH conclusion,
   Rolle's critical point between them, and the negative meromorphic order of the target there.
2. `SuzukiFiniteApertureHermiteBiehler.lean` proves the all-angle positive survivor: the ratio of
   two characteristic coordinates is Schur/Livšic and can be reconstructed from two extension
   angles; a common nonvanishing entire gauge cancels.
3. `suzuki-finite-aperture-hermite-biehler-normal-family.md` already identifies a two-angle
   meromorphic quotient as the pole-compatible replacement.
4. Route-G wall-field, chord-mass, Pick, and Ward cards continue that replacement.  They do not
   prove Suzuki's displayed one-angle limit and must not be used to relabel the failed conjecture
   as open.

## [LITERATURE]

Suzuki proves unconditionally that, for every fixed aperture and admissible shift, each
`W(a,theta;z)` is entire and has only real zeros.  Corollary 1.6 then asks for `theta(a)` and a
finite exponential correction `exp(phi(a,z))` such that

```text
exp(phi(a,z)) W(a,theta(a);z)
  -> z^2 xi(1/2-i z) / xi'(1/2-i z)                    (1)
```

uniformly on every compact subset of `C`.  The paper describes the exponential as a normalization
and says the convergence is an identity of complex functions.  The analytic reading therefore
requires the gauge to be holomorphic.  If no regularity is imposed on `phi`, the displayed premise
is not a characteristic-function convergence theorem: an arbitrary pointwise multiplier can
destroy holomorphy, while the right side is not finite at its poles.  Neither reading supplies a
viable ordinary compact-open limit on all of `C`.

The 2026 numerical follow-up arXiv:2607.24830 explicitly says it does not prove or approach RH and
does not repair this target-category mismatch.  Its finite-element evidence is excluded here.

## [LOCAL-RESEARCH] Exact theorem

Let `W_n, Phi_n : C -> C` be entire.  Assume every zero of `W_n` is real and put

```text
F_n(z) = exp(Phi_n(z)) W_n(z).                           (2)
```

Suppose `F_n` converges locally uniformly on `C` to the totalized centered Suzuki target

```text
T(z) = z^2 XiC(z) / XiC'(z),                             (3)
```

and `T` is nonzero somewhere.  Then contradiction.

This theorem strictly contains the source-defined family in Corollary 1.6: it allows arbitrary
entire real-zero `W_n`, arbitrary entire gauges, arbitrary subsequences, and forgets every
operator-specific restriction.  Failure of this larger class is therefore source-complete for
the published one-angle program.

### Proof

1. `exp(Phi_n)` is entire and nowhere zero.  Hence `F_n` is entire and has exactly the zero set of
   `W_n`; all zeros of `F_n` are real.
2. By the Weierstrass theorem, a locally uniform limit of the entire `F_n` is entire.  Thus `T` is
   analytic on all of `C`.
3. Hurwitz/closed-zero transfer applied to the nonzero limit says every zero of `T` is real.  Every
   centered Xi zero is a zero of the meromorphically reduced quotient: if `XiC` has order `m`, its
   derivative has order `m-1`, so the quotient retains one zero.  Therefore all centered Xi zeros
   are real, which is RH.
4. Under RH, the infinite Xi divisor supplies two distinct positive real centered zeros.  Compact
   zero finiteness selects consecutive zeros `0 < p < q`.
5. Rolle's theorem gives `c in (p,q)` with `XiC'(c)=0`.  Consecutivity gives `XiC(c) != 0`, and
   positivity gives `c != 0`.
6. Therefore the numerator `c^2 XiC(c)` is nonzero while the denominator vanishes to positive
   finite order.  The meromorphic order of `T` at `c` is negative: `T` has a genuine pole.
7. This contradicts Step 2.

No zero simplicity, RH premise, numerical zero, asymptotic computation, or property of a selected
Suzuki source was assumed.

## [CONJECTURE] Hostile alternatives and disposition

### C1. Singular or nonholomorphic gauges evade the pole

`[REFUTED AS A ROUTE-G REPAIR]` A finite exponential never vanishes.  A holomorphic exponential
cannot cancel a pole.  A nonholomorphic or singular multiplier leaves the analytic
characteristic-function category and invalidates the real-zero/Hurwitz implication advertised by
Corollary 1.6.  Ordinary complex uniform convergence on a compact containing a pole is not defined
as convergence to a finite complex function.  Spherical convergence would be a different theorem.

### C2. A special source, shift, or angle removes the obstruction

`[REFUTED]` The theorem quantifies over every entire real-zero family and every entire exponential
gauge.  It is stronger than any source-specific choice.  Source structure cannot alter the target's
interlacing critical-point poles.

### C3. Use two extension angles and retain poles

`[SURVIVES, BUT IS NOT COROLLARY 1.6]` For distinct unit phases `u_0,u_1`,

```text
W_j = A + u_j E,
W_0/W_1 = (Theta+u_0)/(Theta+u_1),
Theta = (u_0-u_1 W_0/W_1)/(W_0/W_1-1).                  (4)
```

This is meromorphic, common entire gauges cancel, and real poles are retained.  It is the sharp
positive survivor.  Proving its source-selected limit would be a new pole-compatible Livšic route,
not a proof of Suzuki's false one-angle compact-limit conjecture.

## Strongest positive survivor

`[THEOREM] [POSITIVE SURVIVOR]`

The exact boundary is categorical:

```text
one holomorphically gauged entire characteristic
  --ordinary compact-open on C--> z^2 XiC/XiC'          impossible;

two-angle characteristic quotient
  --meromorphic/spherical compactness--> Livsic carrier  structurally admissible.  (5)
```

Any successor must name:

- two actual Suzuki extension angles or an equivalent all-angle Hermite--Biehler pair;
- meromorphic convergence, or holomorphic convergence only away from the limiting pole divisor;
- source-selected nondegeneration and uniqueness;
- exact identification of the resulting Livšic/Donoghue carrier with a global Xi/de Branges
  carrier.

Those requirements constitute a new repaired route.  They are not missing lemmas inside retired
Route G.

## Anti-theatre audit

- New knowledge is the gauge-complete quantifier: the obstruction covers every finite holomorphic
  exponential normalization, not merely the ungauged legacy predicate.
- Proof attacks target type, the hard invariant no source manipulation changes.
- Finite Suzuki theorems are preserved exactly; only impossible global conclusion is retired.
- Meromorphic survivor is retained and sharply delimited rather than declared dead.
- No RH claim follows.  Result says Suzuki's displayed strategy cannot prove RH as written.

## Formalization target

Extend `SuzukiCharacteristicEntireLimitNoGo.lean` with:

```text
SuzukiHolomorphicGaugeCharacteristicLimitWall
not_suzukiHolomorphicGaugeCharacteristicLimitWall
```

The proof must derive target holomorphy from locally uniform convergence using mathlib's
Weierstrass theorem, transfer real zeros through the nowhere-zero exponential gauge, and invoke the
existing unconditional target-pole no-go.  No new axiom or conditional Lean declaration is
permitted.

## Gates

- [x] primary Suzuki statement checked
- [x] exact target-category mismatch isolated
- [x] gauge-complete paper theorem proved
- [x] source/operator/angle independence audited
- [x] nonholomorphic and spherical readings separated
- [x] strongest pole-compatible survivor extracted
- [ ] exact unconditional Lean theorem
- [ ] umbrella wiring audit
- [ ] targeted module build
- [ ] route/frontier ledgers retired consistently

