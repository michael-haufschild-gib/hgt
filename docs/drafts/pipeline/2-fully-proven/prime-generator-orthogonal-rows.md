# Prime-generator orthogonal rows

- **ID:** critical-rigidity-prime-generator-orthogonal-rows
- **Stage:** 2-fully-proven
- **Type:** THEOREM; Lean verification pending
- **Statement:** Separate coherent pole transport from the dissipative prime rows and determine the sharp cost after removing the output constant row.

## Exact decomposition

For prime-supported normalized input `F_a=Σ_(p≤Q)a_p e_p`, write `τ_p=log p/(p−1)` and `P_Q(a)=Σ log p/sqrt(p−1)·a_p`. The prime divisor-jet identity gives

`G F_a=P_Q(a)−Σ_(p≤Q)τ_p a_p e_p`.

The two output terms are orthogonal over a complete period. Orthogonality of the normalized conductor modes therefore yields

`mean (G F_a)²=P_Q(a)²+Στ_p²a_p²`,

`mean F_a·G F_a=−Στ_p a_p²≤0`.

Thus large coherent output and dissipative self-pairing coexist. A norm obstruction is not a sign obstruction.

## Sharp positive survivor

The centered output has exact relative squared norm

`sup_a mean (G F_a−P_Q(a))²/L_Q(a)=log 2/2`, for every `Q≥2`.

Indeed `τ_p²/(log p+τ_p)=log p/[p(p−1)]`. The elementary integer estimate `log p≤(p−1)log 2` follows inductively from `n+1≤2n` for `n≥1`. Hence the ratio is at most `log 2/p≤log 2/2`. Conductor two attains equality.

This resolves output pole removal on prime-supported input. It makes no claim for composite conductor packets: coherent transfer into nonconstant divisor rows is a separate candidate.

## Lean

`CriticalScaleArithmeticRigidity/PrimeGeneratorOrthogonalRows.lean`. The input is the literal convergent prime generator; the output projection is complete-period centering.
