# Riesz-eigenfunctional Hodge purity

- **ID:** `deninger-riesz-eigenfunctional-hodge-purity`
- **Stage:** 3-formalized
- **Type:** ABSTRACT HILBERT--HODGE THEOREM
- **Label:** `DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY`
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Statement:** a Meyer eigenfunctional represented by a nonzero
  vector in the Hodge-generator domain has weight-one real part
  \(1/2\); for RH it is enough to represent the order-zero functional
  at each zeta zero.

## Theorem

Let \(\mathcal H\) be a complex Hilbert space and let
\(\Theta\) be a densely defined operator on a domain
\(\mathcal D\subseteq\mathcal H\).  Assume the weight-one adjoint law
\[
 \langle\Theta x,y\rangle
 +
 \langle x,\Theta y\rangle
 =
 \langle x,y\rangle
 \qquad(x,y\in\mathcal D).                                     \tag{1}
\]
The inner product is conjugate-linear in the first variable.

Let \(0\ne y\in\mathcal D\), and suppose its Riesz functional is a
transpose eigenfunctional:
\[
 \langle y,\Theta x\rangle
 =
 \rho\,\langle y,x\rangle
 \qquad(x\in\mathcal D).                                       \tag{2}
\]

`[PROVED HERE] [DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY]`

Then
\[
 \operatorname{Re}\rho=\frac12.                               \tag{3}
\]

### Proof

Put \(x=y\) in `(1)` and use conjugate symmetry:
\[
\begin{aligned}
 \|y\|^2
 &=
 \langle\Theta y,y\rangle
 +\langle y,\Theta y\rangle\\
 &=
 \overline{\langle y,\Theta y\rangle}
 +\langle y,\Theta y\rangle.
\end{aligned}
\]
Equation `(2)` gives
\[
 \langle y,\Theta y\rangle=\rho\|y\|^2.
\]
Since \(\|y\|^2>0\),
\[
 (\overline\rho+\rho)\|y\|^2=\|y\|^2,
\]
so \(\overline\rho+\rho=1\), proving `(3)`.

## Meyer specialization

Meyer's literal generalized spectral vectors live in the strong dual
\(M_\zeta'\), not generally in \(M_\zeta\).  A Hodge completion of
\(M_\zeta\) therefore proves RH only if the order-zero evaluation
functional at every nontrivial zero \(\rho\) is represented by a
nonzero vector
\[
 y_\rho\in\operatorname{Dom}\Theta_{\mathcal H}                \tag{4}
\]
and its transpose action is `(2)`.

This requirement is Hodge-norm boundedness plus domain compatibility:
\[
 |\ell_\rho(x)|
 \le C_\rho\|x\|_{\mathcal H}
\quad\text{on the nuclear core},                               \tag{5}
\]
with the Riesz representative lying in `(4)`.

For RH, `(5)` is needed only for the order-zero functional at each
zero.  Representing every higher Mellin jet preserves the full
generalized block and is needed for the stronger multiplicity/Jordan
comparison, not for critical-line location alone.

## Hostile audit

- Merely placing \(\ell_\rho\) in the nuclear distribution dual is
  insufficient; that holds before Hodge completion.
- Density of the nuclear core in \(\mathcal H\) does not make every
  nuclear functional Hilbert-bounded.
- A Hilbert-bounded functional whose Riesz vector is outside
  \(\operatorname{Dom}\Theta\) does not satisfy the displayed proof
  without an additional form-domain argument.
- No zero is used to define the Hodge norm; zeros enter only in the
  final, one-way spectral comparison.
- No RH premise, CCM object, or numerical computation enters.

## Lean status

Formalized as
`RHTower.deningerClosedWeightOne_rieszEigenfunctional_re_eq_half` in
`GaloisForLFunctions.RHTower.DeningerArithmeticRieszEigenfunctionalPurity`.
The same module defines
`DeningerClosedWeightOneRieszXiSpectrum` and proves
`riemannHypothesis_of_closedWeightOne_rieszXiSpectrum`.

`deningerClosedWeightOne_rieszEigenfunctional_re_eq_half` states the
card's theorem exactly: the weight-one adjoint law `(1)` is carried by
`DeningerClosedWeightOnePolarization`, hypothesis `(2)` is the
transpose-eigenfunctional condition on the generator domain, and the
conclusion is `(3)`.  The proof is the card's: conjugate symmetry turns
`⟨Θy, y⟩` into `conj ρ ‖y‖²`, the adjoint law gives
`(conj ρ + ρ)‖y‖² = ‖y‖²`, and `‖y‖² ≠ 0` cancels.

### Verification

- Direct command: `lake env lean` on the module — passes with no
  errors and no warnings.
- Cached module build: completes.
- Scratch `#print axioms` on
  `deningerClosedWeightOne_rieszEigenfunctional_re_eq_half` and
  `riemannHypothesis_of_closedWeightOne_rieszXiSpectrum`: only
  `propext`, `Classical.choice`, `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: statement isolated
- [x] 1 → 2 fully-proven: `(3)` proved from `(1)` and `(2)`
- [x] 2 → 3 formalized: the purity theorem, the Xi-spectrum package
      and the RH criterion, with cached build and axiom audit
- [ ] 3 → 4 publication-ready: condition `(5)` — Hodge-boundedness of
      the order-zero Meyer functionals with Riesz representatives in
      the generator domain — is the open arithmetic input

## References

- `DAC_SOURCE_THREE_TERM_HODGE_PURITY`.
- `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`.
- Standard Riesz representation and skew-adjoint spectral theory.

## Log

- 2026-07-27 — Replaced vague generalized-jet faithfulness by the
  exact RH-useful condition: order-zero Meyer eigenfunctionals must be
  Hodge-bounded with Riesz representatives in the generator domain.
- 2026-08-01 — Closed the stage-3 gate: verified the module states the
  card's theorem, then ran the cached build and the declaration-axiom
  audit.  No new Lean was needed.
