# HB native angular current at the cusp

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target is cancellation of the complete original physical current. This attack evaluates its angular Green boundary before causal integration, using the actual full-source circle mean. Native/causal equality is already formalized in `ThetaCuspHawkingBMNativeCausalEquality`; uniqueness is not a new obligation here.

Write `k=log Y`, `F_d(X,k)=mean q d X k`, and
`P_d(k)=sum_i A_i exp(alpha_i k) powerCircle alpha_i d`, with the three original exponents `2q,1,2-2q` and completed amplitudes from `ThetaCuspHawkingBMJointSourcePrincipalData`. The exact vertical angular Green density of coexact potentials is

```text
H(F,G) = exp(k)(F_k G_XX - G_k F_XX)
       + exp(-k)(F_k G_kk - G_k F_kk).
```

Proved boundary statement: for fixed nonnegative native radii, `H(F_d,F_e)-H(P_d,P_e)` tends to zero at the cusp after every complex height weight, retaining every source mode. The surviving principal flux is

```text
sum_{i<j} A_i A_j alpha_i alpha_j (alpha_j-alpha_i)
  [powerCircle alpha_i d powerCircle alpha_j e
   -powerCircle alpha_j d powerCircle alpha_i e]
  exp((alpha_i+alpha_j-1)k).
```

The existing native cusp-jet theorem controls all derivatives of `F-P`, uniformly in horizontal position and compact radius. No principal term, finite boundary value or original measure is discarded. This is an asymptotic boundary evaluation, not a finite-part definition or an extinction theorem.

The analytical proof is closed. The circle-power/Legendre identity and positive-chart kernel smoothness give smooth principal coefficients, including radius zero. Differentiating the finite sum gives `P_k=sum alpha_i A_i C_i exp(alpha_i k)`, `P_kk=sum alpha_i^2 A_i C_i exp(alpha_i k)`, and `P_XX=0`. Substitution into `H` cancels the diagonal terms and pairs the two orientations of every off-diagonal term. The resulting exponents are exactly `2q,1,2-2q`.

For any complex weight `w`, choose a natural decay order `N>Re(w)`. The native remainder-jet bound gives a constant times `exp((Re(w)-N)k)` after weighting; hence every weighted remainder jet tends to zero. Mixed principal/remainder terms use this estimate with weight shifted by the corresponding principal exponent. Products of two remainder jets use the weighted estimate for one factor and the unweighted estimate for the other. Expanding the bilinear current proves `exp(w k)(H(F_d,F_e)-H(P_d,P_e))→0` along every horizontal path, for each pair of nonnegative radii.

Finally, for the actual field `f(X,log Y)`, `partial_Y=Y^(-1) partial_k` and `Y^2 partial_YY=partial_kk-partial_k`. Substitution in `F_Y Delta G-G_Y Delta F` gives the displayed density `H` with both Jacobian factors. Six statements pass the Lean scratch check. See the [exact result, source owner and validation](../3-formalized/hb-native-angular-current-cusp.md).

Remaining physical obligations: transport this boundary formula through the original causal integrals and reconstruction, combine temporal/radial/cusp faces and source contacts, and establish the independent SS/SV/VV cancellations. RH remains unproved.

Search evidence: deep corpus searches for reciprocal concomitants and Lagrange identities returned source-only candidates requiring unrelated premises; none supplies this boundary evaluation. Broad recent arXiv searches found [A Superconducting Peierls Instability](https://arxiv.org/abs/2609.04164) and [Anomalous dynamical energy flows via nonlinear phononics in spin-Peierls chains](https://arxiv.org/abs/2608.22517). Their inspected abstracts concern different coupled systems and supply no proof premise here.
