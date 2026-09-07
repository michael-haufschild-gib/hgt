# HB quadratic correction and physical endpoints

Stage: in progress. Type: `[BRIDGE]`; no novelty or RH closure claim.

Target chain: literal theta cusp → Xi occurrence → retained spin-two source →
physical causal response and left-QNM pairing → fixed Hawking-clock extinction → RH.

The actual angular quadratic source and its particular correction are proved in
[the source card](../3-formalized/hb-quadratic-angular-source-and-correction.md).
The next obstacle is a correction admitted at the physical endpoints and satisfying
the complete forced equation. Angular cancellation alone does not supply that.

## Constructed angular correction

Write `f=r²-1`, `C=s²*((s+1)²-4r²)/(8r⁴)`, and let `B` be the actual fundamental
envelope. Keep the previous mixed correction
`k_tA=f*aS*aV*B²*s*(s+1)/(2r³)*S*(coexact S)_A`.
Replace its scalar orbit block by

```
k_tt = 0
k_tr = aS²*B²*C*S²
k_rr = 2*aS²*B²*C*S²/f.
```

The orbit trace agrees with that of the prior correction. In the ingoing chart
`t=v-(1/2)log((r-1)/(r+1))`, its scalar block is only `k_vr=aS²*B²*C*S²`.
The mixed entries become `k_vA=k_tA` and `k_rA=-k_tA/f`.
The envelope becomes `exp(s*v)*((r+1)/r)^s`, regular for positive real radius.
The replacement jet's actual angular cancellation, the differentiated coordinate
map, the original-envelope identity, and the explicit radial endpoint extension
have passed scratch and final leaf audits. The correction has every radial
smoothness order at the horizon and zero entrywise limit at physical radial
infinity. None of these identities assumes that the remaining forced Einstein
components vanish. Exact statements and limitations are in
[the audited proof card](../3-formalized/hb-ingoing-correction-and-vector-master.md).

## Actual constrained vector operator

All sixteen actual linearized Einstein components have passed scratch and final Lean checks
on the complete divergence-free vector-stream metric jet. With time rate w and
orbit stream H, set `h_tA=f*H_r*V_A`, `h_rA=w*H*V_A/f`. Let D be the coexact
derivative of the scalar hyperbolic Laplacian when V is a coexact scalar derivative.
The derived master expression and tensor source are

```
X_A = [r²*f*H_rr+2*r*H_r-(w²*r²/f+2)*H]*V_A + H*D_A
E_tA = -f*partial_r X_A/(2*r²)
E_rA = -w*X_A/(2*r²*f).
```

Only these entries and their symmetric partners survive. No homogeneous radial
equation or angular eigen-equation is assumed. The actual scalar contraction
vanishes and the cosmological term is retained. This supplies the operator needed
for a forced response. The nonlinear forcing is now identified below; the physical
inverse still needs construction.

Restoring an envelope with logarithmic radial rate `w/(r*f)` gives the remaining
factor F the master operator
`r²*f*F_rr+2*r*(w+1)*F_r+[Delta-(w+1)*(w+2)]*F`.
The constant factor exposes the shifted angular resolvent. The inverse-square
factor has exact image `6+[Delta-(w+3)*(w+4)]/r²`. These identities also passed
independent scratch checks.

## Complete nonlinear mixed source and angular response

The complete all-height scalar–vector source is now proved to equal the literal
mixed amplitude cut of the original corrected nonlinear Einstein path. Every
component, the inverse–Ricci cross terms and the correction's linear cosmological
image are retained. Third angular derivatives cancel symbolically. The exact
source tensor and audit are in
[the formalized source and response card](../3-formalized/hb-complete-mixed-einstein-source-and-cusp-response.md).

With `J=coexact d(S²)/2` and `K=coexact d[y²(Sx²+Sy²)]/2`, its current is

```
W = B²*[(5s²+15s+4)/4+s*(s-1)*(s+2)²/(4*r²)]*J
    -B²*s*(s-1)/(4*r²)*K.
```

The complete product jet proves `r²*f*E_rA=partial_t W_A` and
`r²*E_tA/f=partial_r W_A`. Setting the vector master to `X=2W` cancels this
source. The exact master defect yields the sufficient angular equation

```
Omega = coexact d [B²*(H-s*(s-1)*S²/(8*r²))]
[Delta-(2s+1)*(2s+2)]*H = (s+1)*(2s+1)*S².
```

Both physical Xi branches have a nonreal angular parameter, unconditionally.
The full square of both Weyl cusp powers, including `2*A*D*y`, has an explicit
response to the actual hyperbolic differential operator. All three response
denominators are proved nonzero at every actual Xi occurrence. The forcing
amplitude is retained. The actual cusp-subtracted full forcing now has a proved
L² vector under the invariant modular measure. Analytic continuation proves the
full scalar's modular inversion at every Xi occurrence, and the complete residual
matches the modular seams. The proof retains all infinite-tail interactions and
cutoff derivatives; see
[the full forcing and continuation card](../3-formalized/hb-global-angular-forcing-and-modular-continuation.md).
The actual modular energy domain now has a proved dense injective embedding,
with the full weighted derivative graph retained. Its constructed self-adjoint
operator gives a unique finite-energy weak response to the original full forcing
at every actual Xi occurrence on both branches; see
[the energy-domain and response card](../3-formalized/hb-modular-energy-domain-and-weak-response.md).
Smooth global reconstruction and physical causal admission remain open. No
fixed-clock extinction claim follows from weak solvability.

## Work required

1. Obtain the smooth global representative of the proved weak response and its
   literal hyperbolic equation across the modular charts. Construct the global
   cusp-cutoff extension and assemble the full angular response. Establish the
   physical causal prescription for the complete forced vector metric.
2. Construct the remaining SS and VV responses and the complete constrained
   physical response. Retain the correction's linear image in the original left
   pairing until the physical domain and its boundary terms justify annihilation.
3. Derive the independent fixed-clock extinction law and close the RH chain.

The completed experiment supplies guidance only. Known angular cancellation and
predicted coordinate regularity were validation checks, not discovery targets.
No computation supplies Lean proof evidence. The frontier map is read-only.
