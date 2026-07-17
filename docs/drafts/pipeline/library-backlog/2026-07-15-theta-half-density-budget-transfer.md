# Formalize the theta half-density Ward--Laplace budget transfer

- **Source card:**
  `../3-formalized/not_new_scientific_knowledge/theta-cusp-half-density-ward-laplace-budget-transfer.md`;
  `../3-formalized/not_new_scientific_knowledge/theta-cusp-half-density-damped-tail-domination.md`
- **Destination:** `formal/GaloisForLFunctions/RHTower/`
- **Suggested imports:** `PrimeArchThetaGibbsEquipartition.lean`;
  `PrimeArchThetaAtomLikelihoodRatio.lean`; `ThetaCuspFourierLaplace.lean`;
  `XiEndpointCompletedValue.lean`
- **Constraint:** This ticket was written under a no-computation/no-build instruction.  Reuse the
  existing integrability, Ward, strip, endpoint, and likelihood declarations; do not add a new
  analytic interface when an existing theorem suffices.

## Requested theorem surface

1. Define the real Laplace transforms of `thetaCuspLiouvilleGibbsAtom n` and
   `thetaCuspSourceTerm · n` on the half-line.
2. Prove

   ```text
   2*pi*n^2*B_n(z+2)=b_n(0)+(z+5/2)*B_n(z),
   A_n(z)=2*pi*(b_n(0)+(z-1/2)*B_n(z)).
   ```

3. Prove the values at `z=1/2` and `z=-1/2`, then the nonnegative exponential-generating identity

   ```text
   sum_j thetaCuspAtomRawEvenMoment j n /(4^j*(2*j)!)
     =(4*pi*n^2-1)*exp(-pi*n^2).
   ```

4. Use `thetaCuspFourierLaplace_eq_XiC_on_strip`, `thetaCuspFullSource_neg`, and
   `XiC_I_half_eq` to prove the full-source budget `sum_j m_j/(4^j*(2*j)!)=1/2`.
5. Combine the exact higher-tail budget with
   `thetaCuspHigherFirst_rawEvenMoment_cross_le` to prove the
   cumulative likelihood-budget estimate `t_k*W_k<=H` without division where possible.
6. Formalize the exponentially damped domination

   ```text
   f_n(x)<=C_n*exp(-2*pi*(n^2-1)*x)*f_1(x)
   ```

   and use `cosh(x/2)*exp(-2*pi*(n^2-1)*x)<=1` to prove
   `H<(8/2997)*a_0`.  Then add direct consumers for

   ```text
   14*(a_0+a_1/8+H)*a_2^2 <= 9*(a_0+a_1/8)*a_1*a_3,
   16*(a_0+H)*a_2 <= 45*a_1^2.
   ```

7. Wire the new module through `RHTower.lean` and update the formalized card only after narrow
   verification is authorized and passes.

## Antisymmetric reflection / Turan-curvature successor

8. Formalize the difference of the half-density anchors as the odd-moment budget
   `sum M_(2*j+1)/(4^j*(2*j+1)!)=exp(-pi*n^2)`.
9. Add a general HTGeometry half-line slope-curvature identity for
   `D_m=M_(2*m)^2-(2*m-1)/(2*m+1)*M_(2*m-2)*M_(2*m+2)` under explicit integrability and boundary
   hypotheses.
10. Specialize it to the first theta atom, split
    `E=s_0/x^2+E_reg`, prove the one-sign-change law for `E_reg`, and expose the boundary determinant,
    positive unimodal crossing windows, and two regular-curvature consumers.
    The paper theorem is
    `../2-fully-proven/not_new_scientific_knowledge/theta-cusp-antisymmetric-half-density-turan-curvature-transfer.md`.

## Continuous residual-tail successor

11. Define the two cutoff transforms of the first atom and formalize their elementary antiderivatives:
    `T_+(a)=2*pi*exp(3*a)*exp(-pi*exp(2*a))` and
    `T_-(a)=(2*pi*exp(2*a)-1)*exp(-pi*exp(2*a))`.
12. Derive the all-cutoff even/odd residual moment budgets, the ordinary survival corridor, and the
    binomial reconstruction of upper incomplete moments.
13. Formalize the source-specific seam localization `c<log 2` only after the generic slope-curvature
    and one-seam interfaces exist.  The paper source is
    `../2-fully-proven/not_new_scientific_knowledge/theta-cusp-continuous-half-density-residual-tail-chart.md`.
