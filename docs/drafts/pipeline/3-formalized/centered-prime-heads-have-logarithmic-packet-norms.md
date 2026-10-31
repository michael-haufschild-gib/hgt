# Centered prime heads have logarithmic packet norms

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md);
  [affine selection](affine-shell-correlations-select-conductor-quotients.md);
  [head boundary](prime-conductor-heads-and-tails-have-opposite-torsion-limits.md).

Let `D_ml(k)` be the normalized complete-period mean of `c_m(n)c_l(kn)`
and set

`S_K(m,l)=sum_(k<K)Lambda(k)/k [D_ml(k)+D_lm(k)−2delta_ml]`.

For every `Q,K` and real coefficients, the uniform bound is

`|sum_(1≤m,l≤Q) a_m a_l S_K(m,l)|`
`≤[6log Q+log4+4] sum_(1≤m≤Q)a_m²`.

Affine selection makes each `D_ml(k)` nonnegative and each diagonal entry
either zero or one. For distinct conductors, partial head means therefore
increase from zero to `I(m,l)/sqrt(phi(m)phi(l))`. Centered diagonal means
decrease from zero to `−2tameDifferent(m)`.

These entrywise intervals bound the absolute packet form by the torsion
pairing on absolute coefficients plus `2sum tameDifferent(m)a_m²`.
The proved torsion bound costs `4log Q+log4+4`; the tame term costs `2log Q`.
The assertion concerns complete-period means. Transfer to moving finite
horizons remains separate.

The pointwise dilation refinement is
`phi(q)c_l(kn)=phi(l)c_q(n)`, `q=l/gcd(l,k)`.
It follows from the totient-quotient formula and the exact identity
`l/gcd(l,kn)=q/gcd(q,n)`; no period averaging is needed.
Consequently, with `q_l(k)=l/gcd(l,k)` and
`G_ml(Y)=sum_(n≤Y)u_m(n)u_l(n)/n`, the literal finite head has the exact formula

`H_K,N(m,l)=sum_(k<K)Lambda(k)/(k log N)`
`[sqrt(phi(l)/phi(q_l(k))) G_m,q_l(k)(N/k)`
`+sqrt(phi(m)/phi(q_m(k))) G_l,q_m(k)(N/k)]`.

## Lean

`SuccessorShellArithmetic/Conductor/PrimeConductorHeadNorm.lean` proves:

- Exact dilation and Gram reduction:
  `ramanujanLagCoefficient_dilate_reduced`,
  `normalizedRamanujanMode_dilate_reduced`,
  `primeConductorHeadPairing_eq_reducedGram`.
- Closed period means and their signs:
  `primeConductorDilationMean_eq_reduced`,
  `primeConductorDilationMean_nonneg`,
  `primeConductorDilationMean_self_le_one`.
- Sharp entrywise intervals and the uniform packet bound:
  `centeredPrimeConductorHead_offDiagonal_bounds`,
  `centeredPrimeConductorHead_diagonal_bounds`,
  `abs_centeredPrimeConductorHeadPacket_le_log`.

Final direct `lake --old env lean` check passed. All nine transitive axiom
sets are exactly `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import present. The full Weil comparison remains open.
