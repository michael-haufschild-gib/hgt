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

Prove the actual locally uniform product on `\{s : ℂ | 1 < s.re\}` equals this source and is
holomorphic there.  Its indispensable new input is ideal-norm summability, not further local
algebra.

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
