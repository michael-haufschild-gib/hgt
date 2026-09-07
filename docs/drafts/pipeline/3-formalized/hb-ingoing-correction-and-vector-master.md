# Ingoing quadratic correction and complete vector Einstein operator

Stage: formalized; all four exact-source leaf and new-only axiom audits passed.
Type: `[BRIDGE]`; no novelty or RH closure claim.

Target chain: literal theta cusp → Xi occurrence → retained spin-two source →
physical causal response and left-QNM pairing → fixed Hawking-clock extinction → RH.

## A correction with regular radial endpoints

Let `f=r²-1`, `C=s²*((s+1)²-4r²)/(8r⁴)`, and let B be the corpus's original
fundamental envelope. The replacement correction has nonzero static entries

```
k_tr = aS²*B²*C*S²
k_rr = 2*aS²*B²*C*S²/f
k_tA = f*aS*aV*B²*s*(s+1)/(2r³)*S*(coexact S)_A,
```

and their symmetric partners. Its temporal--temporal entry vanishes.
`ThetaCuspHawkingBMQuadraticIngoingCorrection` constructs its complete two-jet
and evaluates the actual first Einstein variation. It cancels exactly the same
two angular Hessian channels as the previous temporal-only correction. Inserting
it into the actual nonlinear metric-jet path leaves angular source
`B²*(aV²*D-aS²*C)*(dS tensor dS)_TF`, with the already derived vector weight D.

`ThetaCuspHawkingBMIngoingCoordinates` differentiates the real map
`t=v-(log(r-1)-log(r+1))/2`. Its complexified differential gives the matrix used
to pull back the correction. The original principal envelope becomes exactly
`exp(s*(v+log(1+1/r)))` on the exterior; this is a proved branch identity.

In inverse radius `u=1/r`, write `E=exp(s*(v+log(1+u)))` and
`V=aS*aV*E²*s*(s+1)*S/2`. The pulled-back correction is

```
k_vr = aS²*E²*s²*u²*((s+1)²*u²-4)*S²/8
k_vx = V*u*(1-u²)*Sy       k_vy = -V*u*(1-u²)*Sx
k_rx = -V*u³*Sy           k_ry = V*u³*Sx.
```

Every other entry vanishes, apart from symmetric partners.
`ThetaCuspHawkingBMQuadraticIngoingEndpoints` proves this identity for the actual
correction metric values with the original envelope. Every entry is smooth to
every complex radial order wherever `1+u` lies in the logarithm chart. The horizon
u=1 and boundary u=0 are both in that domain. The exact finite horizon limits and
zero limits at physical real radius tending to infinity are proved separately.

These are radial endpoint statements at fixed angular data. They do not establish
the full correction field's angular domain, its complete spatial jet realization,
nonlinear gauge, the remaining forced equations, or time-retarded admission.

## The complete constrained vector operator

`ThetaCuspHawkingBMVectorStreamEinstein` evaluates all sixteen components of the
actual linearized Einstein contraction on a complete divergence-free covector
stream jet. The free time rate is w. The metric entries are
`h_tA=f*H_r*V_A` and `h_rA=w*H*V_A/f`, with all ordered second metric derivatives
retained, including the third radial derivative of H.

The angular covector jet retains both differentiated divergence identities. In
components its scalar-Laplacian intertwiner is
`D0=y²*(V0_xx+V0_yy)+2y*(V0_y-V1_x)` and
`D1=y²*(V1_xx+V1_yy)`. For a coexact scalar derivative this is the coexact derivative
of its scalar hyperbolic Laplacian. No angular eigen-equation is assumed.

The exact master expression is

`X_A=[r²*f*H_rr+2r*H_r-(w²*r²/f+2)*H]*V_A+H*D_A`.

The complete cosmological Einstein source has only

```
E_tA = -f*partial_r X_A/(2r²)
E_rA = -w*X_A/(2r²*f)
```

and their symmetric partners. The proof derives the radial derivative of X with
all coefficient derivatives, proves the actual scalar variation is zero, and
retains the cosmological term. Thus the normalization and sign belong to the
actual tensor equation, not an assigned master equation.

Restoring the fundamental envelope gives the remaining radial factor F the exact
operator

`r²*f*F_rr+2r*(w+1)*F_r+[Delta-(w+1)*(w+2)]*F`.

The constant factor has image `Delta-(w+1)*(w+2)`. The inverse-square factor has
image `6+[Delta-(w+3)*(w+4)]/r²`. Both identities are proved from the derived
master expression.

## What this changes in the open response problem

The [39.63-second RunPod experiment](../2-fully-proven/computations/hb-quadratic-physical-source-2026-09-07/REPORT.md)
evaluates the full corrected nonlinear source at y=1 after differentiating. It
finds cancellation of third angular derivatives in every component and a purely
mixed SV source. Its candidate all-height current W uses coexact derivatives of
S² and of `y²*(Sx²+Sy²)`. That full nonlinear identity is not yet proved in Lean.

Combining that candidate with the independently proved vector operator suggests
the specific response

```
w = 2s, P = S², b = s*(s-1)/8
Omega = coexact d [B²*(H-b*P/r²)]
[Delta-(2s+1)*(2s+2)]*H = (s+1)*(2s+1)*P.
```

This identifies a concrete angular resolvent target. Its source identity, angular
domain, constant terms, continuum and physical causal prescription remain to be
constructed. The SS and VV responses are also open. A radial endpoint extension
or an exact operator reduction does not permit dropping the correction's linear
image from the original left pairing; that requires the actual physical test
and every boundary term. Fixed-clock extinction remains independent and unproved.

RH is not proved or falsified. The frontier map is read-only.

## Validation

All four leaves' proofs passed foreground scratch `lake env lean` checks.
Exact-source cache-only final audits compiled only the requested new leaves:

- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticIngoingCorrection`: 26 seconds; 3 public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIngoingCoordinates`: 4.3 seconds; 7 public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticIngoingEndpoints`: 18 seconds; 6 public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorStreamEinstein`: 199 seconds; 6 public theorems.

The 22 new public theorems were axiom-audited once in scratch. Each uses only
`propext`, `Classical.choice`, and `Quot.sound`; there are no added axioms or
experimental certificates. Explicit chart conditions remain in these intermediate
theorems; no unconditional RH theorem is claimed. Main and audit source bytes
match. Each leaf is wired once, and only its new olean/ilean files were installed.
No old axiom audit, full build, umbrella build, or existing-dependency rebuild ran.
One owned foreground Lean/Lake check ran at a time.

The experiment used three workers, passed 96 background/first-order checks and
six known angular checks, and supplied no Lean proof evidence. Downloaded code and
outputs match their checksums. The exact eight-file remote scratch directory was
removed. Corpus index generation, exact-source comparisons, umbrella-import
checks, scoped whitespace checks and `scripts/formal_tools.py lint --check-generated`
passed. Lint reports only the 141 existing large-file warnings. All owned Lean/Lake
processes completed, and the exact local scratch tree was inventoried without
symlinks and removed; its absence is verified. Other tasks' files and processes
were preserved. The frontier map received no edits from this work.
