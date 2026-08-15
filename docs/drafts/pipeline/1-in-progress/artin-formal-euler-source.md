# Coefficientwise Artin Euler source at number-field finite places

- **ID:** `artin-formal-euler-source`
- **Stage:** 1-in-progress
- **Type:** THEOREM (literature infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** from the canonical finite-place polynomials \(P_v(T)\), construct the
  coefficientwise arithmetic Euler source whose local factor is \(P_v(T)^{-1}\) placed at powers
  of \(N(v)\), and prove every coefficient is eventually equal to the corresponding finite Euler
  product coefficient.

## Goal

Build the first genuinely global Artin object without smuggling in an analytic product.  The
carrier is `ArithmeticFunction ℂ`; local factors arise from actual inverse power series and the
global value is Mathlib's coefficientwise `ArithmeticFunction.eulerProduct`.  This is prerequisite
infrastructure for the `Re(s) > 1` convergence theorem, not an Artin `L`-function continuation.

## Paper proof

For every finite base prime \(v\), the already formalized local polynomial satisfies
\(P_v(0)=1\).  Hence its image in \(\mathbb C[[T]]\) is a unit and has a uniquely defined inverse
\(U_v=P_v^{-1}\) with constant coefficient one.  Put the coefficient of \(T^m\) in `U_v` at the
arithmetic-function input \(N(v)^m\) via `ArithmeticFunction.ofPowerSeries`, and take the
coefficientwise Euler product over finite primes.  Northcott finiteness for ideal norms makes only
finitely many local data contribute to any fixed coefficient.  Consequently the net of finite
products is eventually constant at that coefficient, exactly as
`ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries` states.

Every step depends only on the finite-place polynomial, its proved constant term, finite ideal-norm
fibres, and the existing arithmetic-function Euler-product theorem.  No analytic convergence or
continuation is used.

## Exact Lean target

```text
artinFormalEulerSource_coefficient_eventually_eq:
  ∀ rho n,
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      (∏ v ∈ S, artinLocalEulerArithmeticFactor v rho) n =
        artinFormalEulerSource rho n.
```

## Hostile non-circularity audit

- `ArithmeticFunction.eulerProduct` is coefficientwise, not an analytic `tprod`; calling it a
  convergent Euler product would be false.
- Northcott supplies finite coefficient support, not the norm summability required for
  \(\Re(s)>1\).
- No `Multipliable`, `Meromorphic`, or `ArtinLFunction` proposition is introduced.  Such an
  interface would hide the next theorem rather than prove it.
- This result cannot cross the C2 source-to-divisor obstruction: it has no continuation and hence
  no order character.

## Open successor

The actual locally uniform reciprocal product on `\{s : ℂ | 1 < s.re\}` is now separately
formalized and holomorphic.  The remaining bridge is equality between that analytic tprod and
the `LSeries` of this coefficientwise source.  Its indispensable ingredients are an explicit
complex analytic evaluation theorem for the finite-root local inverse series and an absolutely
summable Fubini/reindexing theorem over finite places and norm coefficients.

Mathlib's generic `PowerSeries.eval₂Hom` is adic: it requires an `IsLinearTopology` target and
cannot evaluate an arbitrary formal complex power series at `|z|<1`.  Treating it as the desired
analytic evaluation would be false.  The local bridge must therefore use the actual finite root
factorization and geometric series, followed by a separate global rearrangement proof.

## Sharp positive survivor: the ideal-tuple `ℓ¹` envelope

The first attempted global shortcut was rejected: a uniform bound on the total `ℓ¹` norm of the
finite Euler products does **not** imply coefficientwise dominated convergence (mass can escape,
as for the sequence of point masses at increasing integers).  The exact replacement is a fixed
positive majorant.

Let `D := Module.finrank ℂ V`, let `c_K(n)` count nonzero integral ideals of `𝓞 K` of absolute
norm `n` (and put `c_K(0)=0`), and let

```text
B_K,D := c_K ^ D
```

be its `D`-fold Dirichlet convolution.  Thus `B_K,D(n)` counts ordered `D`-tuples of nonzero
ideals with product norm `n`.  For every finite set `F` of finite primes, write `A_F` for the
corresponding finite product of actual Artin local arithmetic factors.  The sharp paper target is

```text
∀ F n, ‖A_F n‖ ≤ B_K,D n.
```

Its proof labels the at-most-`D` unit roots of every local Frobenius polynomial.  A monomial in a
coefficient expansion gives one exponent for each labelled root at each `v ∈ F`.  Inject those
labels into `Fin D`, and collect the exponents of colour `j` into the ideal
`J_j = ∏ v, v ^ exponent(v,j)`.  Ideal multiplicities recover every original exponent, so this
is an injection into ordered `D`-tuples of ideals of the required product norm.  Each monomial has
norm one, hence the triangle inequality gives the displayed bound.  This handles `D=0` as the
arithmetic delta at `1`.

The summability is sharp and uses no continuation:

```text
L(B_K,D, s) = L(c_K, s)^D = ζ_K(s)^D,     Re(s) > 1.
```

The base ideal-count convergence already has a proof inside
`NumberFieldFinitePlaceNormSummability.lean`; it must be exported.  Repeated
`ArithmeticFunction.LSeriesSummable_mul` then supplies the right-hand summability.  Together with
coefficient stabilization, `LSeries.norm_term_le`, and
`tendsto_tsum_of_dominated_convergence`, this proves convergence of finite source products to the
formal-source `LSeries`.  The separately required local finite-root geometric evaluation and
finite arithmetic-product identity then identify that limit with the existing analytic tproduct.

Relevant existing finite-factor infrastructure is
`HTGeometry/PowerSeriesAbsoluteEvaluation.lean`,
`HTGeometry/ArithmeticFunctionLSeriesDeterminant.lean`, and
`Ideal.finprod_heightOneSpectrum_pow_multiplicity`.  It has not yet been assembled into an Artin
leaf: the outstanding Lean work is root-label expansion, the root-colour-to-ideal-tuple injection,
the convolution/cardinality equivalence, and an exported ideal-count `LSeries` theorem.  This is a
`[LITERATURE] [BRIDGE] [NOT NEW]` route, not a continuation or holomorphy result.

## Exact formal result

`formal/GaloisForLFunctions/RHTower/ArtinFormalEulerSource.lean` now defines

```text
artinLocalEulerPowerSeries,
artinLocalEulerArithmeticFactor,
artinFormalEulerSource,
```

and proves

```text
numberFieldFinitePlaceLocalEulerPolynomial_eval_zero,
numberFieldFinitePlaceLocalEulerPolynomial_mul_artinLocalEulerPowerSeries,
artinFormalEulerSource_coefficient_eventually_eq.
```

The first theorem transports the previously proved `P_Q(0)=1` through the canonical
finite-place choice.  The second is the actual power-series inverse identity.  The last is the
exact coefficientwise finite-product stabilization theorem.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ArtinFormalEulerSource.lean` passed.
- `lake build GaloisForLFunctions.RHTower.ArtinFormalEulerSource` passed; targeted leaf only.
- `/tmp/ArtinFormalEulerSourceAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for all exported results.
- The leaf is wired into `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build was run.
- The most recent repository-wide lint remains blocked by unrelated concurrent modules, so this
  card stays Stage 1 rather than claiming a whole-tree formal-gate pass.

## Log

- 2026-08-15 — opened after source-verified Mathlib audit found the exact number-field
  `ArithmeticFunction.eulerProduct` route and a compiler-checked scratch prototype.  The paper
  proof closes at the coefficientwise level; the analytic successor remains separate.
- 2026-08-15 — formalized the reciprocal local factors and coefficientwise global Euler source,
  then source-checked, target-built, axiom-audited, and wired the leaf.  The result remains a
  formal source only; it makes no `Re(s)>1` convergence claim.
- 2026-08-15 — the canonical analytic tprod on `Re(s)>1` is now formalized in the separate
  `ArtinNumberFieldEulerProductAnalytic.lean` leaf.  A source audit ruled out a tempting but
  invalid shortcut: generic formal power-series evaluation is adic, not complex-radius
  evaluation.  The remaining analytic/source equality is isolated as explicit local
  root-geometric summation plus global absolute Fubini/reindexing infrastructure.
- 2026-08-15 — completed the sharp paper audit for the source/tprod bridge.  The fixed
  `D`-tuple-of-ideals majorant, rather than a merely uniform finite-product norm bound, is the
  correct Tannery input; it retains norm collisions and is summable at the sharp threshold
  `Re(s)>1`.  Lean implementation order is now fixed: export ideal-norm-count summability;
  add a dependency-light absolute-power-series core; prove local finite-root evaluation; prove
  sparse `ofPowerSeries` L-series reindexing; then formalize the root-occurrence-to-ideal-tuple
  injection and the dominated-convergence wrapper.  Repeated roots must be labelled by the
  `Multiset` coercion type, not by the membership subtype, which would collapse multiplicities.
  The existing HTGeometry absolute-evaluation leaf is deliberately not imported: it pulls an
  unrelated 53-module dependency cone.  None of these items is claimed formalized until its
  foreground source check, target build, and axiom audit pass.
