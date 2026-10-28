# A simultaneous Gram budget for growing Ramanujan families

## Statement

For positive conductors, let

\[
u_m(n)=c_m(n)/\sqrt{\phi(m)},\qquad v_m(n)=u_m(n)/\sqrt n,
\qquad H_N=\sum_{n=1}^N1/n.
\]

Every finite conductor set \(S\), real coefficient family \(a\), and natural horizon \(N\) satisfy

\[
\left|\sum_{n=1}^N\left(\sum_{m\in S}a_m v_m(n)\right)^2
-H_N\sum_{m\in S}a_m^2\right|
\le 2\left(\sum_{m\in S}m^2\right)\left(\sum_{m\in S}a_m^2\right).
\]

Replacing \(H_N\) by \(\log N\) changes the constant to \(1+2\sum_{m\in S}m^2\).
These are the literal Ramanujan profiles of the prime matrix. No fixed-family asymptotic
premise or externally supplied small Gram error occurs in the statements.

## Mathematical proof

For conductors \(m,l\), use the common period \(q=ml\). Complete-period Ramanujan
orthogonality gives mean \(\delta_{ml}\) for \(u_mu_l\) and mean one for both squares.
The inequality \(2|uv|\le u^2+v^2\) therefore gives

\[
\sum_{j<q}|u_m(j+1)u_l(j+1)-\delta_{ml}|\le2q.
\]

Every partial sum of this mean-zero periodic sequence is bounded by its complete-period
absolute sum. Abel summation with reciprocal weights preserves that bound: its terminal
weight and weight increments have total mass one. Consequently

\[
\left|\sum_{n=1}^N v_m(n)v_l(n)-\delta_{ml}H_N\right|\le2ml.
\]

Expand the family square and sum the entry costs before applying Cauchy–Schwarz:

\[
\left|\sum_{m,l\in S}a_ma_l\,\mathrm{error}_{ml}\right|
\le2\left(\sum_{m\in S}m|a_m|\right)^2
\le2\left(\sum_{m\in S}m^2\right)\left(\sum_{m\in S}a_m^2\right).
\]

The classical bound \(|H_N-\log N|\le1\), including Lean's zero-horizon convention,
pays the final diagonal term. All arithmetic and analytic inputs are existing proved
results; none is an assumption about a growing family.

## Formal closure

Module:
`formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/GrowingRamanujanFamiliesHaveAUniformGramBudget.lean`

Public declarations:

- `ramanujanPoleProfile_gram_error_le`
- `ramanujanPoleProfile_family_gram_error_le`
- `ramanujanPoleProfile_family_log_gram_error_le`

The complete module passes `lake --old env lean`. All three capstones have only
`propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom lists.
The programme umbrella imports the module; the umbrella is not built.

## Scope

The result pays the entire Gram matrix with one coefficient-space bound. It does not pay
prime-matrix residuals, adjunction-energy separation, the modal complement, Gamma, or the two
continuous pole coordinates. A controlled Gram family alone is not a complete arithmetic source.
