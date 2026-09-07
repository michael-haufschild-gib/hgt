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
for a forced response; it does not identify the nonlinear forcing or select the
physical inverse.

Restoring an envelope with logarithmic radial rate `w/(r*f)` gives the remaining
factor F the master operator
`r²*f*F_rr+2*r*(w+1)*F_r+[Delta-(w+1)*(w+2)]*F`.
The constant factor exposes the shifted angular resolvent. The inverse-square
factor has exact image `6+[Delta-(w+3)*(w+4)]/r²`. These identities also passed
independent scratch checks.

## Nonlinear source and response candidate

The [39.63-second RunPod experiment](../2-fully-proven/computations/hb-quadratic-physical-source-2026-09-07/REPORT.md)
evaluates every corrected source component at y=1 after all derivatives. Third
angular derivatives cancel throughout. The SV source has only mixed components;
its candidate all-height current potential W is recorded in the report. The
all-height nonlinear source identity remains unproved.

The independently derived vector master normalization requires `X=2W` to cancel
that nonlinear source. Put `P=S²`, `w=2s`, `b=s*(s-1)/8`. Combining the candidate
source current with the exact inverse-square master identity suggests the stream

```
Omega = coexact d [B²*(H-b*P/r²)]
[Delta-(2s+1)*(2s+2)]*H = (s+1)*(2s+1)*P.
```

Thus the candidate SV response needs one specific angular resolvent of S², with
its domain, constant terms, continuum and endpoint conditions retained. This is
a derived response candidate, not an assumed solution or a replacement for the
fixed-clock extinction target. Its nonlinear-source identification, angular
resolvent realization and physical causal admission remain open.

## Work required

1. Prove the complete all-height nonlinear SV source identity, construct the actual
   angular resolvent and establish the physical forced vector response.
2. Construct the remaining SS and VV responses and the complete constrained
   physical response. Retain the correction's linear image in the original left
   pairing until the physical domain and its boundary terms justify annihilation.
3. Derive the independent fixed-clock extinction law and close the RH chain.

The completed experiment supplies guidance only. Known angular cancellation and
predicted coordinate regularity were validation checks, not discovery targets.
No computation supplies Lean proof evidence. The frontier map is read-only.
