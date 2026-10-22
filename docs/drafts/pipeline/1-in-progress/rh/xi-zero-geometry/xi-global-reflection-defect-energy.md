# Xi global reflection-defect energy

## Status

**In progress.** The divisor-side identity is unconditional and is being formalized. The source-side upper estimate is the open RH-bearing core.

## Claim

Let `q` range over the multiplicity copies of the nontrivial Xi divisor and put
\[
  \lambda_q=\xi_q^{-1},
  \qquad
  \xi_q=-i\bigl(\rho_q-\tfrac12\bigr).
\]
The inverse-square summability of the Xi divisor makes the following global quantity finite:
\[
  \mathcal E_{\mathrm{ref}}
   :=\sum_q |\lambda_q-\overline{\lambda_q}|^2.
\]
It is the squared Hilbert--Schmidt distance between the reciprocal Xi divisor operator and its adjoint. If
\[
  H_\Xi:=\sum_q|\lambda_q|^2,
  \qquad
  M_\Xi:=\sum_q\lambda_q^2,
\]
then
\[
  \boxed{\mathcal E_{\mathrm{ref}}=2H_\Xi-2\operatorname{Re}M_\Xi.}
\]
The functional-equation and Schwarz symmetries make `M_Xi` real. Hence
\[
  H_\Xi\ge M_\Xi,
\]
with equality exactly when every Xi zero lies on the critical line. Equivalently,
\[
  \boxed{\mathrm{RH}\iff \mathcal E_{\mathrm{ref}}=0
  \iff H_\Xi=M_\Xi.}
\]

The holomorphic term is an exact completed-source value:
\[
  M_\Xi=-\frac{\Xi_C''(0)}{\Xi_C(0)}

\]
because `Xi_C` is even and its multiplicity-exact genus-one product has centered spectral locations `xi_q`.

## Positive carrier interpretation

The theorem separates two global channels without discarding either:

1. `M_Xi` is the holomorphic completed-source channel, determined by the central two-jet of Xi.
2. `H_Xi` is the Hermitian divisor-orientation channel, the Hilbert--Schmidt mass of the reciprocal divisor.

A successful Connes realization must couple them by the sharp source inequality
\[
  H_\Xi\le M_\Xi.
\]
The opposite inequality is automatic from the reflection-defect square, so this source inequality forces equality and RH.

## Open core

`[CONJECTURE]` The continued prime--Gamma Guinand--Weil source admits a cofinal positive realization whose source norm is `H_Xi` and whose completed central value is `M_Xi`; contractivity of that realization gives
\[
  H_\Xi\le M_\Xi.
\]

The conjecture is not promoted by the divisor identity. The research task is to construct this source realization or derive the same upper estimate directly from the prime--Gamma trace formula.

## Verification obligations

- Prove summability of the reflection-defect series from inverse-square summability.
- Prove the exact square expansion and the equality characterization.
- Connect equality with the existing multiplicity-exact RH criterion.
- Prove the central two-jet identity from the exact Xi canonical product.
- Identify a source-side positive form whose norm is `H_Xi`; do not replace this by a divisor-indexed definition.

## Novelty and significance gate

- **Novelty:** pending literature audit after the theorem is complete; the abstract Hilbert--Schmidt identity is classical, while the exact Xi/source coupling may be new.
- **Significance:** the divisor identity alone is a sharp global RH criterion, not an RH estimate. Significance requires a nontrivial prime--Gamma upper bound or a source construction yielding it.
