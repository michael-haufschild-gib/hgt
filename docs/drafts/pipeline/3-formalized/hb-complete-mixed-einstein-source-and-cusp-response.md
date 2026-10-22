# HB complete mixed Einstein source and cusp response

Stage: formalized in Lean 4. Type: `[BRIDGE]`. RH is not closed.

Target chain: literal theta cusp → Xi occurrence → retained spin-two source →
physical causal response and left-QNM pairing → independent fixed-clock extinction → RH.

## Exact mixed source

Let f=r²-1 and lambda=(s+1)(s+2). The scalar and coexact-vector jets are the
complete corpus first-order Einstein solutions. The retained mixed correction
has only symmetric temporal-angular entries

`k_tA=f*B²*s*(s+1)/(2*r³)*S*(coexact dS)_A`.

Define

```
J = (S*Sy, -S*Sx)
K = (y*(Sx²+Sy²)+y²*(Sx*Sxy-Sy*Sxx)+lambda*S*Sy,
     -y²*(Sx*Sxx+Sy*Sxy)).
```

These are half the coexact derivatives of S² and y²(Sx²+Sy²). The full source
has only mixed entries and their symmetric partners:

```
E_tA = B²*(Pt*J_A+Qt*K_A)
E_rA = B²*(Pr*J_A+Qr*K_A)
Pt = s*[r²*(-s³+2s²+15s+8)+(s-1)*(s+1)*(s+2)²]/(2*r⁵)
Qt = s*(s-1)*(r²-s-1)/(2*r⁵)
Pr = s*[r²*(5s²+15s+4)+s*(s-1)*(s+2)²]/(2*r⁴*f)
Qr = -s²*(s-1)/(2*r⁴*f).
```

The Lean theorem `amplitudeCut_eq` identifies every entry with the literal amplitude
cut `EpsilonSquared(1,1)-EpsilonSquared(1,0)-EpsilonSquared(0,1)` of the original
corrected nonlinear Einstein path. Its proof differentiates the actual first
Einstein variation along an independent direction, evaluates the full Ricci
contraction, and retains the combined scalar contraction. The inverse--Ricci
cross terms and the correction's linear cosmological image are included.
Third angular derivatives cancel without being set to zero.

## Forced current and angular equation

The current is

```
W = B²*[(5s²+15s+4)/4+s*(s-1)*(s+2)²/(4*r²)]*J
    -B²*s*(s-1)/(4*r²)*K.
```

Its complete product jet includes the envelope derivatives. The component
identities are `r²*f*E_rA=partial_t W_A` and `r²*E_tA/f=partial_r W_A`.
Setting the existing full vector Einstein master to `X=2W` cancels this source. The exact remaining master defect gives

```
Omega = coexact d [B²*(H-s*(s-1)*S²/(8*r²))]
[Delta-(2s+1)*(2s+2)]*H = (s+1)*(2s+1)*S².
```

The defect is retained in the formal operator identity. No angular inverse or
physical response is inserted as a premise.

## Explicit response to the cusp principal part

For an actual Xi point rho, the physical rates are rho-2 and -rho-1. Their
angular parameters have imaginary parts `(8*Re rho-10)*Im rho` and
`(8*Re rho+2)*Im rho`. The corpus's strict strip and absence of real Xi zeros
make both nonreal, including critical-line points.

The square of both retained Weyl powers is exactly

`(A*y^rho+D*y^(1-rho))² = A²*y^(2*rho)+2*A*D*y+D²*y^(2-2*rho)`.

For either physical parameter L, an explicit response is

```
H_cusp = A²*y^(2*rho)/[(2*rho)*(2*rho-1)-L]
       + 2*A*D*y/(-L)
       + D²*y^(2-2*rho)/[(2-2*rho)*(1-2*rho)-L].
```

All three denominators are nonzero at every actual Xi point. The actual
hyperbolic Laplacian, not a formal eigenvalue substitution, verifies
`(Delta-L)*H_cusp=(A*y^rho+D*y^(1-rho))²`. Multiplying by the forcing amplitude
retains this identity. This supplies the explicit cusp principal-part response.

## Remaining proof obligations

Construct the actual global hyperbolic form domain, admit the cusp-subtracted
full forcing, establish the smooth angular response, and prove its physical
causal prescription. The corpus's `FriedrichsFormOperator` supplies the abstract
construction from a complete dense form embedding; that embedding still needs
construction for this geometry. Retain all nonconstant tails, global gluing and
boundary terms. The full SS/VV responses, original left-QNM pairing and independent
fixed-clock extinction remain open.

No experiment supplies Lean evidence. The earlier RunPod source calculation
provided guidance only. The frontier map remains read-only.

## Audit

Development checks used `lake env lean` on scratch files. Final audits used only
`lake build <module>` for these four exact-source new leaves, with existing
imports supplied from their caches. All passed without Lean warnings:

- `GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexMixedQuadratic`
- `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticMixedSource`
- `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticMixedAmplitude`
- `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticMixedCurrent`

The 27 new public theorems were checked once with `#print axioms` in a scratch
file. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`
appear; no added axiom or proof-debt declaration is used. These are proved
identities on the stated nondegenerate coordinate chart and quantified Xi
occurrences, not an unconditional RH theorem. Each leaf is wired once into its
theorem-area umbrella; no umbrella or dependency rebuild ran. The final
`formal_tools.py lint --check-generated` passed, with only existing large-file
warnings outside these modules. No numerical certificate is used.

Principal declarations: `einstein_eq_secondVariation`, `ricci_component`,
`scalar_cancel`, `einstein_component`, `correction_amplitude_cut`, `amplitudeCut_eq`,
`currentJet_components`, `radial_current`, `temporal_current`,
`square_coexact_laplacian`, `master_resolvent_defect`,
`xi_resolvent_parameter_nonreal`, `xi_cusp_denominators`,
`xi_cusp_response_equation`, and `xi_forced_cusp_response_equation`.
