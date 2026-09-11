# HB: incoming fixed-clock balance and literal source work

Status: ten new public source theorems passed scratch checks and the exact leaf build. Fixed Hawking-clock extinction and RH remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact source laws

For every actual Xi occurrence, the four original incoming horizon-current components have the form

    J_j(v)=exp(-6v)[C_j0 chi(v)²+C_j1 chi(v)chi'(v)+C_j2 chi'(v)²],

where chi is the original smooth transition. All three profiles are retained. The unchanged common clock gives

    M_h^(-6)(J_j)=h exp(-6h) C_j0,
    integral_(1+T)^(1+T+h) J_j
      = C_j0 exp(-6(1+T))[1-exp(-6h)]/6,

for nonnegative h,T. The first identity also holds for the original incoming Einstein action evaluated at the horizon. In the original time measure, finite translation adds the outgoing slab and subtracts the incoming slab; both caps remain explicit.

For the actual forced angular fields H_s,H_t, write Q for the literal half-square, U=coexact H_s, V=coexact H_t, W=coexact Q, and s+t=-3. Put alpha_i=(2i+1)(2i+2), d_i=i(i-1)/4. Define

    G_j=alpha_t partial_j H_s (H_t+Q)
          -alpha_s partial_j H_t (H_s+Q),
    r_s=-2s d_t[(t+1)²-st]+st alpha_t/3,
    r_t= 2t d_s[(s+1)²-st]-st alpha_s/3,
    r_Q=2d_s d_t(s-t)(1-st),
    Z=r_s H_s+r_t H_t+r_Q Q,
    B=-(st/3)G+Z grad Q,    c=a²b²/64.

The exact incoming radial mass balance is

    y² C_10=4c[y² div B-Z(2(s+1)(s+2)Q+fullGradientEnergy)].

No source-response or gradient-energy term is removed. The formal statement keeps the two divergences separately; the displayed combined current is their linear combination. The identity is multiplied by y² and 4c, with no division by amplitude or spectral difference.

## Proof and boundary meaning

Product differentiation of G uses the actual smooth angular responses. Their equations Delta H_i=alpha_i(H_i+Q) cancel the two second-derivative products, leaving the full covector operator exchange. Expanding the already identified original trace/normal jets produces the three r coefficients. Differentiating Z grad Q then uses the actual source equation Delta Q=2(s+1)(s+2)Q+fullGradientEnergy. These steps prove the displayed source balance, rather than imposing a conservation hypothesis.

For a finite positive-height rectangle, the associated angular boundary is

    integral_y0^y1 [B_0(x1,y)-B_0(x0,y)]dy
      +integral_x0^x1 [B_1(x,y1)-B_1(x,y0)]dx.

This follows on paper by the one-dimensional FTC in each coordinate. The leaf formalizes the pointwise angular identities and finite time integrals; it does not claim an admitted infinite cusp integral or a completed spacetime Stokes theorem. The lower radial face also requires its outward minus sign when these coordinate-current formulas enter the physical action.

The literal scalar pulse has the exact radial factorization

    Pulse_s=2 alpha_s A_s(u)(1-u)
      [-((2s+1)u+1)H_s+d_s u²((2s+3)u+3)Q] chi'(v)exp(2sv),
    A_s(u)=a²(1+u)^(2s),    u=1/r.

Consequently the scalar pulse's zero at u=1 cannot be used to discard its master-source contact: the original conversion divides by (1-u²)u. The normalized horizon transfer and its trace-minus-normal formula are a further paper calculation recorded in the active card; they are not asserted as Lean conclusions of this leaf.

## Scope and remaining producer

These are unconditional source identities for the incoming SV–SV piece. They retain its full trace/normal angular fields, the half-square lift, all four incoming current components and all three clock profiles. They do not assemble independent SS/SV/VV responses or their nine pairings, solve every quadratic correction, evaluate changing-weight terms in the full action, or identify these temporal tests with the actual left-QNM state.

The remaining source-level task is cancellation of the derived work and every physical boundary contribution against the actual causal pulse response, incoming/pulse cross terms and other channels. The reduced receiver K=-Sigma|D|², Sigma>0, remains only the receiver. Neither its vanishing nor a sufficient opposing physical sign is proved here. See the [active conjecture loop and complete interface](../1-in-progress/hb-fixed-clock-source-translation.md).

## Verification

Module: [ThetaCuspHawkingBMIncomingClockTranslation.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMIncomingClockTranslation.lean), namespace `RHTower.D4BMIncomingClockTranslation`, 459 lines, ten public theorems.

The current/source-work statements and the pulse factorization passed foreground `lake env lean` scratch checks. The assembled source passed `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingClockTranslation` in 132 seconds, with no warnings and only the new leaf compiled. Twelve existing cache roots were reused; no dependency, full or umbrella build ran. The leaf is imported once by `RHTower.lean`.

Source SHA256: `0c6ff170b19498571fc80765ef8c935eea2b09de46272530d40c9c057bfe612d`. Static indexing completed; all thirteen public declarations appear in `LEAN_API.md`. Global formal lint passed with existing large-file warnings. No numerical experiment was run. All owned Lean checks exited.
