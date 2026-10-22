# Dense-resolvent transpose purity

- **ID:** `deninger-dense-resolvent-transpose-purity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY`
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Statement:** a nonzero continuous transpose eigenfunctional on
  source cohomology forces failure of the corresponding resolvent on
  every dense invariant core; hence a Hodge core with off-axis
  resolvent stability forces weight-one purity without Riesz
  boundedness of the eigenfunctional.

## Goal

Replace pointwise Hilbert boundedness of Meyer evaluation functionals
by the natural rigged-Hilbert regularity condition: the Hodge
resolvent preserves a dense source core.  This is weaker, sees the
strong dual where Meyer's eigenvectors actually live, and reduces the
RH gate to a source elliptic-regularity theorem.

## Algebraic theorem

Let \(D\) be a complex vector space, let \(T:D\to D\) be linear, and
let \(\ell:D\to\mathbb C\) satisfy
\[
  \ell(Tx)=\lambda\ell(x) \qquad (x\in D).                 \tag{1}
\]
If
\[
  T-\lambda:D\longrightarrow D                            \tag{2}
\]
is surjective, then \(\ell=0\).

### Proof

`[PROVED HERE]`

For \(y\in D\), choose \(x\in D\) with
\((T-\lambda)x=y\).  Equation `(1)` gives
\[
  \ell(y)=\ell(Tx)-\lambda\ell(x)=0.
\]
Since \(y\) was arbitrary, \(\ell=0\).

## Dense-source theorem

Let \(E\) be a Hausdorff locally convex source cohomology space,
\(D\subset E\) a dense invariant vector subspace, and
\(\ell\in E'\) nonzero.  Continuity and density imply
\(\ell|_D\ne0\).  Therefore:

1. if \(\ell(Tx)=\lambda\ell(x)\) on \(D\), then
   \(T-\lambda\) is not surjective on \(D\);
2. if \(V:D\to D\) and
   \(\ell(Vx)=c\ell(x)\), then \(V-c\) is not surjective on \(D\).

Consequently, suppose a weight-one arithmetic Hodge realization has
centered generator
\[
  A=\Theta-\tfrac12
\]
and a dense source core \(D_{\mathrm{Hdg}}\) such that
\[
  A-z:D_{\mathrm{Hdg}}\longrightarrow D_{\mathrm{Hdg}}
  \quad\text{is surjective whenever }\operatorname{Re}z\ne0. \tag{3}
\]
Every nonzero continuous transpose eigenfunctional of \(\Theta\) has
eigenvalue \(\rho\) with
\[
  \operatorname{Re}\rho=\tfrac12.                         \tag{4}
\]

Alternatively, for the centered time-one flow \(V=e^A\), it is enough
to prove
\[
  V-c:D_{\mathrm{Hdg}}\longrightarrow D_{\mathrm{Hdg}}
  \quad\text{is surjective whenever }|c|\ne1.              \tag{5}
\]
Then every nonzero transpose eigencharacter has modulus one.  For
\(c=e^{\rho-1/2}\), this again gives `(4)`.

## Why this improves the RH gate

Meyer's generalized zero states are continuous functionals on the
strong dual of the nuclear quotient; they need not be vectors in the
Hodge Hilbert space.  The earlier Riesz criterion requires each
order-zero state to extend boundedly to the Hilbert completion.  The
dense-resolvent criterion requires only:

1. a source-defined dense smooth Hodge core;
2. invariance of that core under the centered flow;
3. source regularity of the off-axis Hodge resolvent.

These conditions are standard outputs of elliptic Hodge theory.  In
the arithmetic setting they must be proved for the global
Calderón--Green intermediate extension and its strict nuclear limit.
No zeta zero is used to define the core or resolvent.

## Generalized jets

The same argument handles a finite Jordan chain.  If
\((T'-\lambda)^m\ell=0\) and \(T-\lambda\) is surjective on the core,
then every power \((T-\lambda)^m\) is surjective.  Applying the
algebraic theorem inductively forces \(\ell=0\).  Thus dense resolvent
stability excludes every off-axis generalized Meyer block, not only
order-zero states.

## Lean status

The order-zero algebraic kernel, finite generalized-jet kernel,
centered weight-one purity theorem, source-resolvent Xi spectrum
package, and RH corollary are formalized in
`GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticDenseResolventPurity`.
Checked against the card statement by statement:

- `deningerTransposeEigenfunctional_eq_zero_of_sub_surjective` is the
  algebraic theorem `(1)`--`(2)`: a transpose eigenfunctional vanishes
  when `T - λ` is surjective, proved exactly as on the card by
  choosing a preimage;
- `deningerLinearMap_pow_surjective` is the generalized-jet step:
  every power of a surjective endomorphism is surjective, so a finite
  Jordan chain is excluded as well;
- `deningerSourceResolvent_transposeEigenvalue_re_eq_zero` and
  `deningerSourceResolvent_transposeEigenvalue_re_eq_half` are `(3)`
  and `(4)`: off-axis surjectivity of every difference forces the
  centered eigenvalue onto the imaginary axis, i.e. `Re ρ = 1/2`;
- `DeningerHodgeSchwartzResolventXiSpectrum` and
  `riemannHypothesis_of_hodgeSchwartzResolventXiSpectrum` package the
  hypothesis and the criterion, with dense-range variants
  `deningerSourceDenseRange_transposeEigenvalue_re_eq_half` and
  `riemannHypothesis_of_hodgeSchwartzDenseRangeXiSpectrum` for the
  weaker form `(5)`.

### Verification

- Direct command: `lake env lean` on the module — passes with no
  errors and no warnings.
- Cached module build: `lake build` of the module completes.
- Scratch `#print axioms` on every headline declaration: only
  `propext`, `Classical.choice`, `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and attack
- [x] 1 → 2 fully-proven: complete algebraic and dense-core proofs
- [x] 2 → 3 formalized: algebraic kernel, generalized-jet kernel,
      weight-one purity, the Xi-spectrum package and the RH criterion,
      with cached build and axiom audit
- [ ] 3 → 4 publication-ready: the criterion's hypothesis — a dense
      source Hodge core with off-axis resolvent surjectivity — is the
      open arithmetic input, not part of this theorem

## Log

- 2026-07-27 — Proved dense-resolvent form and identified source
  elliptic regularity, rather than Riesz representability, as the
  minimal strong-dual spectral-faithfulness gate.
- 2026-07-27 — Formalized surjectivity of every power and exclusion of
  finite generalized transpose eigenjets; direct Lean check passes.
- 2026-08-01 — Closed the stage-3 gate: verified the module states the
  card's theorems clause by clause, then ran the cached build and the
  declaration-axiom audit.  No new Lean was needed.
