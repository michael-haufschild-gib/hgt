# Xi off-line endpoint-charge self-cubic law

- **ID:** \`xi-offline-endpoint-charge-self-cubic-law\`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH ESTIMATE
- **Scientific status:** \`[PROVEN] [FORMALIZED] [NOVELTY UNVERIFIED] [RH ESTIMATE PROGRESS]\`

## Carrier

For a multiplicity copy \(q\) of the Xi divisor, let

\[
w_q=\Re\!\left(r_q\overline{r_{q^\dagger}}\right)>0
\]

be its endpoint cross charge and define the off-line endpoint charge

\[
C_\perp=\sum_{\Re q\ne1/2}w_q.
\]

Then

\[
0\le C_\perp\le C,\qquad C=2+\gamma_E-\log(4\pi).
\]

## Theorem

The FE--Schwarz quartet of every off-line copy lies entirely in the off-line sector. Hence

\[
4w_q\le C_\perp,
\qquad
4\le C_\perp(\gamma_q^2+1).
\]

Consequently the transverse thermal defect satisfies the self-localized cubic estimate

\[
\mathcal E_\perp
\le
4\left(\frac{C_\perp}{4-C_\perp}\right)^3
\le
4\left(\frac{C}{4-C}\right)^3.
\]

Moreover,

\[
C_\perp=0\Longleftrightarrow\mathcal E_\perp=0
\Longleftrightarrow\mathrm{RH}.
\]

## Exact remaining coercivity

The displayed inequality is not by itself a contraction in \(\mathcal E_\perp\): an off-line
quartet can approach the critical line while retaining endpoint charge of order
\(\gamma^{-2}\), whereas its transverse energy has the additional factor
\((\Re\rho-1/2)^2\). A proof of RH through this carrier therefore requires a source-side
coercivity law relating \(C_\perp\) back to \(\mathcal E_\perp\), or a quantized lower bound for
one of these two carriers. The self-cubic law is a strict improvement of the completed-curvature
budget because it vanishes on the RH fibre, but it is not an iteratable contraction: the missing
horizontal factor can tend continuously to zero.

## Gates

- [x] Formalize summability and positivity of the off-line charge.
- [x] Prove \(4w_q\le C_\perp\) for every off-line copy.
- [x] Prove the self-localized cubic inequality.
- [x] Prove \(C_\perp=0\iff\mathrm{RH}\).
- [x] Integrate the theorem into the exact Connes--Born/Witten--KMS master theorem.
- [ ] Prove a source identity controlling \(C_\perp\) without divisor input, or a source-side
  coercivity law that forces its zero endpoint.

## Formal artifact

\`formal/GaloisForLFunctions/RHTower/XiThermalOffLineChargeSelfCubicBound.lean\`

Principal declarations:

- \`xiEndpointOffLineCharge_nonneg\`;
- \`xiEndpointOffLineCharge_le_curvature\`;
- \`four_mul_xiEndpointCrossCharge_le_offLineCharge\`;
- \`four_le_offLineCharge_mul_one_add_im_sq\`;
- \`xiEndpointOffLineCharge_eq_zero_iff_rh\`;
- \`xiThermalOrientationTerm_le_offLineCharge_endpointCrossCharge_cube\`;
- \`xiThermalOrientationEnergy_le_offLineChargeCubicBudget\`;
- \`xiThermalOffLineChargeCubicBudget_le_exactCubicEndpointBudget\`;
- \`xiThermal_offLineCharge_budget_energy_zero_tfae\`.

The module and strengthened master theorem compile without placeholders. Axiom inspection reports
only \`propext\`, \`Classical.choice\`, and \`Quot.sound\`.
