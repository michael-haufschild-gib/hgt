# HB causal response cusp current

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Hard target: the complete physical-current cancellation, with original source contacts and all boundary faces. The [native angular cusp current](../3-formalized/hb-native-angular-current-cusp.md) is proved for the source kernel. This attack carries its full asymptotic data through the original causal response and the derivatives appearing in reconstruction. The frontier map remains read only.

Let `U=fullNullResponse q s a p r X k` and let `c_i=principalNullResponse q s a i p r` be the existing original radial response coefficients. On the nonnegative causal quadrant, define the exact uncut remainder

```text
R = U - sum_i c_i exp(alpha_i k),    alpha=[2q,1,2-2q].
```

The first conjecture is now [formalized](../3-formalized/hb-causal-response-cusp-current.md): every actual angular derivative of R equals the original signed double source integral of the corresponding native cusp-remainder derivative, including the null Jacobian 1/4. All these derivatives decay faster than any height power, uniformly on compact causal rectangles and in horizontal position. The principal coefficients are the existing physical radial responses. Eight new public theorems passed the exact leaf build and the axiom audit.

Analytical proof mechanism: the original circle-power/Legendre identity identifies each integrated principal channel with `principalNullResponse`. Subtract the admitted finite principal sum from the complete source integral. The native cusp-remainder jets are jointly smooth in radius and angular variables; the characteristic radius need only be continuous when differentiating angular variables. Differentiate the original compact source integrals, retaining their actual weight. On a bounded causal rectangle the native radius and the original source weight have common bounds. The existing arbitrary-order native cusp-jet estimate then passes through both integrals. This controls every retained source mode, not just an angular mean or a finite principal projection.

Second conjecture: first null derivatives and their angular jets satisfy the same rapid cusp bounds. The existing scalar `radialResponse_goursat` equation applies to all three original principal coefficients. Subtract these equations from `fullNullResponse_goursat`: the spectral factor `(-alpha_i)(1-alpha_i)=alpha_i(alpha_i-1)` is exactly the angular Laplacian of its principal power. This gives the uncut remainder's Goursat equation at every positive height, without a cutoff-region assumption. FTC turns its double primitive into the actual first-null derivative. Its integrand consists of the original source remainder and the actual angular Laplacian of R, which the first conjecture controls at every derivative order. Both zero-length characteristic edges must be retained. This uses the field equation instead of imposing a derivative of the arcosh radius at a characteristic edge.

The exact forcing is

```text
F_R(p,r,X,k) = R_source(X,k) sourceWeight(p,r)/4
              + (exp(2k) R_XX + R_kk - R_k)/(4 cosh((p-r)/2)^2),
R_source(X,k) = nativeRemainder q [0,X,k].
```

Thus `R = integral_0^p integral_0^r F_R`, `R_p = integral_0^r F_R(p,b) db` and `R_r = integral_0^p F_R(a,r) da`. These formulas retain the original source, rather than replacing it by arbitrary forcing data. For canonical angular derivatives `D_X^u D_k^v`, the differentiated exponential term is exactly

```text
exp(2k) sum_(j=0)^v binom(v,j) 2^(v-j) D_X^(u+2) D_k^j R.
```

Every term has arbitrary cusp decay by choosing the input decay order two larger. Angular differentiation of the double primitive, followed by FTC, proves the null/angular trace claim analytically without assuming that mixed orbit derivatives already commute. The exact integral, jet, Goursat, and both first-null derivative formulas are now formalized; higher angular null-trace estimates remain to be formalized. These bounds are on compact causal rectangles and do not by themselves supply an infinite-radius horizon limit or the complete current cancellation.

The resulting actual response/current coefficients should be tested in the original physical action. For two responses with coefficients c_i and d_i, the angular principal interactions have coefficients `alpha_i alpha_j (alpha_j-alpha_i)(c_i d_j-c_j d_i)` and powers `2q,1,2-2q`. Reconstruction requires the corresponding derivatives of the original c_i,d_i and the matching remainder estimates. No vanishing of these coefficients, finite-part prescription, physical-current cancellation or RH is assumed.

Corpus evidence: `fullNullResponse_goursat`, `fullNullResidual_goursat`, `fullNullResidual_eq_nativeResidualIntegral`, `principalNullResponse_physical_ae`, native/physical causal equality, the native all-order cusp-jet bound, and the new original-height angular current expansion. Deep polyhomogeneous and integral-transport searches returned partial/source-only results; the proposed polarized-heat ingredient group does not provide the required causal source identity.

Broad arXiv searches inspected the abstracts of [nonlinear wave expansions without corner conditions](https://arxiv.org/abs/math/0506423) and [inverse Vlasov–Poisson scattering expansions](https://arxiv.org/abs/2404.15885). These suggest using the field equation to transfer asymptotics through characteristic corners; neither is a Lean premise or a verified theorem about this source. Searches preferring June–September 2026 did not return a directly usable mathematical result.

Broader Peierls and Darboux searches were inspected through declarations, candidate statements, source methods and proposed ingredient groups. Their results were partial and largely source-only. The constructive source-lift calculation matches the existing [full source onset decomposition](../3-formalized/hb-full-source-onset-reduction.md), which must be reused: the original source is two specified wave images plus its fixed onset pulse. Its incoming profile is `H-s(s-1)Q/4`; pairing that profile and the actual causal pulse response remains required. Searches on symplectic structure and isotropy also inspected the abstracts of [SINFONIA, 3 September 2026](https://arxiv.org/abs/2609.03329) and [quadratic spacetime intervals, June 2026](https://arxiv.org/abs/2606.25993). Neither supplies a theorem about the original theta-source pairing; no numerical results or external premises enter the proof.
