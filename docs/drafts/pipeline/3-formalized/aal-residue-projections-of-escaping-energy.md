# Uniform residue energy and projection leakage

- **ID:** aal-residue-projections-of-escaping-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual damped Möbius receiver has a uniform residue-energy discrepancy bound; on energy escape, residue projection leaves a precisely determined mass outside the receiver line.

## Statements

For $0<\varepsilon<1/2$, let $A_n$ be the centered divisor prefix,
$e_n=A_n^2/[n(n+1)]$, $E_T=\sum_{n=1}^T e_n$, and
$R_{q,r}(T)=\sum_{1\le n\le T,\ n\equiv r\pmod q}e_n$.

The unconditional finite-horizon bounds are

\[
\sum_{n=1}^{T}|e_{n+1}-e_n|\le4\sqrt{E_T}+1,
\qquad
|R_{q,r}(T)-E_T/q|\le8\sqrt{E_T}+4.
\]

The second bound is uniform in $q$ and $r$. Thus either $E_T$ is bounded, or
$R_{q_T,r_T}(T)/E_T-1/q_T\to0$ for every moving modulus and residue.

For fixed $q,r$, the best scalar approximation to the masked receiver has coefficient
$a_T=R_{q,r}(T)/E_T$. Its normalized squared error is exactly $a_T(1-a_T)$.
On escape this tends to $q^{-1}(1-q^{-1})$; parity leaves mass $1/4$ outside the receiver line.

## Proof

The actual source gives $|A_{n+1}-A_n|\le1$ and $|A_n|\le n$.
Expanding the change of denominator gives
$|e_{n+1}-e_n|\le(4|A_n|+1)/[n(n+1)]$.
Pronic Cauchy–Schwarz bounds the sum of $|A_n|/[n(n+1)]$ by $\sqrt{E_T}$;
the reciprocal weights sum to at most one. This proves the variation bound.

The centered residue indicator has partial sums bounded by two, uniformly in the modulus.
Summation by parts, the variation bound, and $e_n\le1$ give the discrepancy estimate.
Monotonicity of $E_T$ supplies the bounded-or-escaping alternative. Expanding the masked
squared distance gives $c^2E_T+(1-2c)R_{q,r}(T)$; completing the square gives the minimizer
and the exact normalized leakage.

## Lean

Module: `GaloisForLFunctions/ArithmeticDefectRigidity/EscapingEnergyErasesPeriodicMasks.lean`.

- `sum_abs_receiverEnergyCell_diff_le`
- `abs_receiverResidueEnergy_sub_mean_le`
- `admits_or_moving_residue_energies_equidistribute`
- `receiverResidueProjectionError_min`
- `normalized_receiverResidueProjectionError_eq`
- `admits_or_residue_projection_leakage`

Direct Lean check passed. All eleven public theorems have axiom closure
`propext`, `Classical.choice`, `Quot.sound`. Imported by the programme umbrella.

## AAL boundary

The result concerns the receiver line. Compression to the full cofactor space would require
mixed residue-covariance limits. Neither closure of a finite spectral space under residue
projections nor a contradiction to an actual finite exceptional zero layer has been proved.
AAL remains unresolved.
