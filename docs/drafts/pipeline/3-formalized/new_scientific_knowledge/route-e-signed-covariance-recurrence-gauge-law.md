# Route E signed covariance recurrence and gauge law

- **ID:** ROUTE-E-SIGNED-COVARIANCE-RECURRENCE-GAUGE-001
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT SOURCE REDUCTION / CIRCULARITY NO-GO / POSITIVE ENERGY SURVIVOR
- **Parent:** ../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md
- **RH used:** no
- **Computation used:** no
- **External audit:** intentionally omitted; no external priority claim

## Theorem

For distinct insertions \(p_1,\ldots,p_k\), let \(S_0=\varnothing\),
\(S_j=S_{j-1}\cup\{p_j\}\), and define

\[
 \alpha_j=
 \frac{Z_{j-1}(x)-Z_{j-1}(p_jx)}
      {Z_{j-1}(x)+Z_{j-1}(p_jx)},\qquad
 \beta_j=
 \frac{Z_{j-1}(p_jx)}
      {Z_{j-1}(x)+Z_{j-1}(p_jx)},
\]
\[
 d_j=\int_x^{p_jx}-\operatorname{Cov}_{S_{j-1},t}
       ((-1)^{|T|},E(T))\,dt .
\]

Then
\[
 \psi_j(x)=\alpha_j\psi_{j-1}(x)-\beta_jd_j,
\]
and, with \(A_{a:b}=\prod_{\ell=a}^b\alpha_\ell\),
\[
 \boxed{\psi_k(x)=A_{1:k}-\sum_{j=1}^k\beta_jA_{j+1:k}d_j.} \tag{1}
\]

The recurrence weights are positive, \(\alpha_j=1-2\beta_j\), and
\[
 \boxed{\sum_{j=1}^k\beta_jA_{j+1:k}=\frac{1-A_{1:k}}2<\frac12.} \tag{2}
\]

If \(W_k=\sum_j\beta_jA_{j+1:k}d_j\), then
\[
 \boxed{|W_k-A_{1:k}|\le\eta\iff|\psi_k|\le\eta.}        \tag{3}
\]
For two insertion orders \(\sigma,\tau\) with the same final aperture,
\[
 \boxed{W_k^\sigma-W_k^\tau=A_{1:k}^\sigma-A_{1:k}^\tau.} \tag{4}
\]

Finally define
\[
 \mathcal Q_S(x)=J_S(x)^2/Z_S(x)
\]
and
\[
 \mathcal D_{S,p}(x)=
 \frac{Z_S(x)Z_S(px)}{Z_S(x)+Z_S(px)}
   (\psi_S(x)+\psi_S(px))^2.
\]
Then
\[
 \boxed{\mathcal Q_{S\cup p}(x)+\mathcal D_{S,p}(x)
       =\mathcal Q_S(x)+\mathcal Q_S(px),\qquad
       \mathcal D_{S,p}(x)\ge0.}                         \tag{5}
\]

## Proof

Divide the exact current and partition insertion laws
\[
 J_{S\cup p}(x)=J_S(x)-J_S(px),\qquad
 Z_{S\cup p}(x)=Z_S(x)+Z_S(px)
\]
by \(Z_S(x)>0\), and use the integrated covariance identity
\[
 \psi_S(px)-\psi_S(x)=
 \int_x^{px}-\operatorname{Cov}_{S,t}((-1)^{|T|},E(T))\,dt.
\]
This gives the one-step recurrence.  Induction gives (1).

The identity \(\alpha_j=1-2\beta_j\) implies
\[
 \beta_jA_{j+1:k}=\tfrac12(A_{j+1:k}-A_{j:k}),
\]
so (2) telescopes.  Equation (3) is (1) with the terms moved across the equality.
The endpoint is independent of insertion order; subtracting the two copies of (1) gives (4).

For (5), substitute \(J_S=Z_S\psi_S\), clear the three positive partition denominators,
and expand.  It is the two-point weighted polarization identity
\[
 \frac{(a-b)^2}{u+v}
 +\frac{uv}{u+v}\left(\frac au+\frac bv\right)^2
 =\frac{a^2}{u}+\frac{b^2}{v}.
\]
Nonnegativity follows from \(u,v>0\).

## Scientific content

Equation (1) is the fully weighted parity--energy covariance accumulation requested by the Route E
frontier: recurrence weights, physical dilation intervals, partition masses, and finite-volume
signs are all retained.

Equations (3)--(4) close two false shortcuts.  Bounding the accumulated covariance minus its
baseline is exactly bounding the endpoint, and averaging insertion orders only transfers the same
order dependence between baseline and accumulation.  Neither is an independent RH producer.

Equation (5) is the strongest positive survivor.  Taking a norm only after signed insertion
produces an exact nonnegative loss measuring same-sign scale coherence.  Any successful quadratic
route must prove cofinal saturation of this dissipation; antiscale coherence
\(\psi_S(px)\approx-\psi_S(x)\) is its exact escape mode.

## Lean certificate

Module:
formal/GaloisForLFunctions/RHTower/GibbsSignedCovarianceAccumulation.lean.

Principal declarations:

- normalized_current_insert_covariance_recurrence
- signedRecurrenceEndpoint_eq
- signedRecurrenceRetainedMass_eq
- normalizedGibbsCurrent_insert_list_eq_baseline_sub_accumulation
- gibbsPrimeInsertion_accumulation_bound_iff_current_bound
- gibbsPrimeInsertion_order_gauge
- gibbsNormalizedCurrentEnergy_insert_add_dissipation
- gibbsSameSignDissipation_nonneg
- gibbsNormalizedCurrentEnergy_insert_le

The module is wired into GaloisForLFunctions.RHTower.

## Audit

- lake env lean GaloisForLFunctions/RHTower/GibbsSignedCovarianceAccumulation.lean — pass.
- lake build GaloisForLFunctions.RHTower.GibbsSignedCovarianceAccumulation — pass,
  8659/8659 targeted jobs.
- Axiom audit — every principal theorem uses only propext, Classical.choice, and Quot.sound.
- No sorry, admit, axiom, opaque, or unsafe declaration.
- Full build not run.

Static corpus lint reached unrelated concurrent state:
GaloisForLFunctions.HTGeometry.ObserverBoundaryBuilding was not yet wired into its umbrella, and
generated indexes changed again while lint ran.  No lint error named this module or its
declarations.

## Status

[PAPER-PROVED] [LEAN-CERTIFIED] [NOT AN RH PROOF].

The strict-half bound remains open.  This card proves its exact finite source reduction and
prevents that reduction from being presented as the missing estimate.
