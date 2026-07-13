# Xi Arakelov Kronecker chamber

- **ID:** `xi-arakelov-kronecker-chamber`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN ARITHMETIC × ORIENTATION COLLISION
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiArakelovKroneckerChamber.lean`

## Statement

For an Xi zero `rho`, write

\[
w_\rho=1-\rho^{-1}.
\]

The Arakelov coordinate sends the critical line to the unit circle:

\[
|w_\rho|=1\quad\Longleftrightarrow\quad \operatorname{Re}\rho=\tfrac12.
\]

Lean proves the following arithmetic top-down chain:

```text
every Xi-zero Arakelov coordinate is an algebraic integer
  +
every complex root of its integral minimal polynomial has norm at most one
  -> every Xi-zero Arakelov coordinate has norm one
  -> every Xi zero lies on the critical line
  -> RH.
```

Equivalently, with the two global predicates formalized in the module,

\[
\mathrm{XiArakelovCoordinatesIntegral}
\quad+\quad
\mathrm{XiArakelovConjugateRootsContractive}
\quad\Longrightarrow\quad RH.
\]

## Mechanism

Let `P` be the monic integral minimal polynomial of a nonzero algebraic integer `w`.  Its constant
coefficient is a nonzero integer, so

\[
1\le |P(0)|=\prod_{P(\beta)=0}|\beta|.
\]

If every complex conjugate satisfies `|beta| <= 1`, the same product is at most one.  Hence the
product equals one.  Removing the distinguished factor `w` shows `1 <= |w|`, while contractivity
gives `|w| <= 1`; therefore `|w|=1`.

At an Xi zero, `w_rho` is nonzero because every Xi zero lies strictly inside `0 < Re rho < 1`.
The Arakelov unit-circle equivalence then supplies `Re rho = 1/2`.

## Anti-redressing attack

The two premises have different blind spots.

- Algebraic integrality alone carries no Archimedean orientation.  An algebraic integer may have a
  distinguished embedding strictly inside or outside the unit disk while another conjugate
  compensates in the product.
- Conjugate-root contractivity alone does not force algebraicity.  Lean's integral minimal
  polynomial is zero for a nonintegral value, so its root condition is empty in precisely that
  case.

Thus neither predicate is an RH formulation.  The critical-line conclusion appears only when the
arithmetic nonvanishing of the conjugate product collides with the Archimedean contraction chamber.

This remains a strong and presently unsupported sufficient condition.  It should not be confused
with evidence that Xi-zero coordinates are algebraic.

## Open core

`[OPEN CORE]` Construct a source-natural arithmetic realization of every `w_rho` as an eigenvalue
of a monic integral finite-rank object, and prove that every conjugate eigenvalue is contractive.
Neither input may be obtained by assuming `|w_rho|=1`, self-adjointness, unitarity, or an
RH-equivalent zero-location statement.

A viable provider would be an integral source complex whose characteristic polynomial contains the
Arakelov coordinate and whose complete complex spectrum is bounded by one for a reason independent
of the Xi divisor.  No such provider is present in the current corpus.  Expected transcendence of
zeta zeros makes the integrality premise a serious plausibility risk, so this is a fringe route
rather than a primary target.

## Formal verification

Lean proves:

- `minpolyInt_coeff_zero_ne_zero`;
- `multiset_norm_prod_le_one`;
- `norm_eq_one_of_integral_conjugates_contractive`;
- `riemannHypothesis_of_xiArakelovCoordinatesIntegral_of_conjugateRootsContractive`;
- `riemannHypothesis_of_xiArakelovIntegralConjugateChamber`.

The named module build passes in the repository toolchain.
