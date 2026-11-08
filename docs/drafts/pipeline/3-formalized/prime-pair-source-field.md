# Prime-pair source field

- **ID:** prime-pair-source-field
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The distinct-prime pair source determines the transverse field of every actual zeta zero to the right of the critical line, with an explicit proper-prime-power correction.

Write $P=-\zeta'/\zeta-H$, where $H(s)=\sum_{p,k\ge2}(\log p)p^{-ks}$ is holomorphic on $\Re s>1/2$. Put $D(s)=\sum_p(\log p)^2p^{-2s}$ and $S=P^2-D$. On $\Re s>1$, $S$ is the ordered distinct-prime pair series.

At an actual zero $\rho$ of multiplicity $m$, write $\zeta'/\zeta=m/(s-\rho)+B(s)$. Then
\[
[S]_{\rho,-2}=m^2,\qquad [S]_{\rho,-1}=2m(B(\rho)+H(\rho)),
\]
\[
\mathcal F(\rho)=\Re\frac{[S]_{\rho,-1}}{2m}-\Re H(\rho)+\Re\frac{A'}A(\rho).
\]
Here $A$ is the archimedean factor and $\mathcal F$ is the absolutely convergent transverse zero field. The diagonal $D$ is holomorphic at $\rho$ and contributes no negative Laurent coefficient.

At a center $\rho+d$, $d>0$, the existing `tendsto_normalized_higher_prime_power_jets` makes the jets of $H$ normalized by $d^{k+1}/((-1)^k k!)$ tend to zero: $d<\Re(\rho+d)-1/2$. Nevertheless, $H(\rho)$ remains in the simple Laurent coefficient after squaring. Its mixed term cannot be discarded. No sign of the prime-pair residue, and no AAL conclusion, follows from this identity alone.

## Proof

1. Absolute convergence of the prime-log series on $\Re s>1$ permits multiplication and diagonal removal. Thus $S(s)=\sum_p\sum_{q\ne p}(\log p)(\log q)p^{-s}q^{-s}$.
2. The corpus proves $H$ holomorphic on $\Re s>1/2$. Also $D(s)=-P'(2s)$ there, so $D$ is holomorphic because $\Re(2s)>1$.
3. The actual zero factorization gives $P(s)=-m/(s-\rho)-B(s)-H(s)$. Squaring gives double coefficient $m^2$ and simple coefficient $2m(B(\rho)+H(\rho))$. Subtracting $D$ changes neither coefficient.
4. The existing actual source-field identity is $\mathcal F(\rho)=\Re B(\rho)+\Re(A'/A)(\rho)$. Substitution gives the stated prime-pair formula. The multiplicity is positive because the zero has a multiplicity copy, so division by $2m$ is valid.

No simplicity, extremality, finite-layer, or unproved analytic assumption is required. The statements hold at every actual zero with $\Re\rho>1/2$.

## Lean

Module: `ArithmeticCorrespondencePositivity/PrimePairsRetainThePrimePowerField.lean`.

- `primePairSource_eq_tsum`: actual ordered distinct-prime series.
- `analyticAt_primePowerTail`, `primePairDiagonal_eq`, `analyticAt_primePairDiagonal`: analytic corrections.
- `laurentCoeff_primeLogContinuation_sq`: exact nonlinear prime-power correction.
- `laurentCoeff_primePairSource`, `laurentCoeff_primePairSource_leading`: both polar coefficients.
- `xiTransverseField_eq_primePairSource`: actual transverse-field identity.

Direct `lake --old env lean GaloisForLFunctions/ArithmeticCorrespondencePositivity/PrimePairsRetainThePrimePowerField.lean` passed without warnings. All eight public theorems have exactly `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closure. Imported by the umbrella; no umbrella build.
