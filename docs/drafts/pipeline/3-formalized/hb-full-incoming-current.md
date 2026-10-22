# HB: complete incoming wave-image current

Status: formalized. This evaluates the entire explicit incoming wave image in the original full-source decomposition. The onset-pulse response, complete causal pairing, SS/VV coefficients and RH remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Owner: [ThetaCuspHawkingBMFullIncomingCurrent.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMFullIncomingCurrent.lean), namespace `RHTower.D4BMFullIncomingCurrent`.

## Exact result

The actual constructed angular responses on both branches remain in the wave-image stream:

```
Psi_s = a² (1+1/r)^(2s) chi(v) exp(2sv)
          [coexact H_s - s(s-1)/(4r²) coexact Q].
```

The source value identity retains the original `timeRadialLift`, `timeSourceSeed`, `parameter`, and compact-radius normalization. The radial, time and mixed angular derivatives used in the current are proved to be actual derivatives. The current is identified with all four components of the volume-weighted Einstein action after the ingoing coordinate transformation.

The original horizon trace and normal covectors are

```
U_s=coexact H_s-k_s coexact Q,
N_s=-s coexact H_s+k_s(s+2) coexact Q,
k_s=s(s-1)/4.
```

For complementary rates `t=-s-3`, the current has exact mass, mixed and derivative-energy coefficients `clockCoefficients`. The two angular components retain the Green cross currents between `N_s,U_t` and `U_s,N_t`. The [analytical card](../1-in-progress/hb-full-incoming-current.md#analytical-full-current-evaluation) lists every coefficient.

Each physical component has the proved exterior limit and finite-clock integral

```
C0 M(V)+C1[3M(V)+B(V)/2]+C2 E(V),
M(V)=integral_0^V exp(-6v) chi(v)²,
E(V)=integral_0^V exp(-6v) chi'(v)²,
B(V)=exp(-6V) chi(V)².
```

No amplitude, clock, angular-response or boundary-cancellation premise is supplied. The exterior and upper-half-plane arguments carry their ordinary geometric domains. This is a pointwise angular evaluation and finite clock integral; angular integration and the full onset-pulse comparison remain open.

## Public proof API

| Theorem | Content |
|---|---|
| `regular_current_is_action` | All four original action-current components in regular ingoing jets |
| `responseProfile_derivatives` | Actual first and second derivatives of the full-response radial factor |
| `incoming_value_original` | Original two-wave-image source normalization |
| `incoming_radial_jets` | Actual first and second radial derivatives |
| `incoming_time_jets` | Actual time and mixed time/radius derivatives |
| `incoming_angular_mixed_jets` | Actual angular derivatives entering both cusp-current components |
| `incoming_current_is_action` | Complete two-branch incoming Einstein-current identity |
| `incoming_current_horizon_value` | Exact four-component horizon evaluation |
| `incoming_horizon_finite_integral` | Fixed-clock integral retaining the onset endpoint |
| `incoming_current_horizon_limit` | Exterior-to-horizon limit of every component |

## Validation

Scratch `lake env lean` passed. Final `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullIncomingCurrent` passed in an isolated audit using only existing compiled dependencies: two jobs, 23 seconds. The audit froze 3,991 project dependency modules (19,940 artifact links) and used 12 local dependency stubs. No dependency or umbrella build ran. All ten new public theorems passed `#print axioms` in a separate scratch file, each with exactly `propext`, `Classical.choice`, and `Quot.sound`. Installed source and five build artifacts match the audited files byte for byte. The module is wired once into `RHTower.lean`; the umbrella was not built. The search index refreshed once (four changed files, zero removed). All 21 new public API rows, the unique umbrella import, and local document links were checked. Global `scripts/formal_tools.py lint` reported two unrelated unwired modules: `GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAbsoluteInstability` and `GaloisForLFunctions.HTGeometry.PathIndependenceCochain`. No lint error named this module.

## Next direct cancellation test

Use the original decomposition `F=L Phi+R` with the specified transition-supported pulse `R`. Compare the pulse-response current and both wave-image/pulse cross terms with the coefficients above, retaining the same angular, temporal, AdS and horizon faces. In particular, the radial derivative-clock coefficient is `2c(X-Y)` with `X=U_t dot N_s`, `Y=U_s dot N_t`, `c=a²b²/64`. The full response does not inherit the old same-covector angular zeros.
