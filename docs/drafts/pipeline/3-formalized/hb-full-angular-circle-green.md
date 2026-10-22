# HB: full angular and original onset-pulse Green transfer

Status: formalized. The complete physical causal pairing and RH remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Owner: [ThetaCuspHawkingBMFullAngularCircleGreen.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMFullAngularCircleGreen.lean), namespace `RHTower.D4BMFullAngularCircle`.

For either actual Xi branch let `s=physicalRate q branch`, `alpha=(2s+1)(2s+2)`, `p(d)=legendreKernel (2s+1) (cosh d)`, `h(d)` be the circular mean of the constructed full angular response, and `m(d)` the existing circular mean of the literal half-square source. The new closed identity is

```
sinh D [p(D) h′(D) - p′(D) h(D)]
  = alpha integral_0^D sinh d p(d) m(d) dd.
```

The derivatives are actual derivatives of the constructed functions. The proof derives the forced circular equation from the full angular field equation and the original hyperbolic chart. It retains `h(0)=H(z)`. Continuity at zero and the fundamental theorem of calculus with interior derivatives close every finite nonnegative radius. No nonvanishing premise on `p` is required.

For the original `fullSourceOnsetPulse`, its circular mean is exactly `C_H h + C_Q m`, with `C_H=onsetResponseCoefficient` and `C_Q=onsetSourceCoefficient` retaining the existing radial functions, transition derivative and exponential clock. Its actual Green current therefore equals

```
C_H alpha integral_0^D sinh d p(d) m(d) dd
  + C_Q sinh D [p(D) m′(D) - p′(D) m(D)].
```

This replaces the full-response channel in that pulse current by a literal-source integral. It preserves the half-square current. It does not yet evaluate the pulse's full causal convolution, its cross terms with the incoming wave image, or the complete SS/SV/VV physical action.

## Public proof API

| Theorem | Content |
|---|---|
| `angularMean_zero` | Actual full angular datum at radius zero |
| `angularMean_smooth` | Every actual radial derivative exists |
| `angularMean_forced` | Full forced Darboux equation with the original half-square mean |
| `greenCurrent_hasDerivAt` | Actual current derivative at nonzero radius |
| `greenCurrent_finite_integral` | Complete finite source-transfer identity |
| `onsetAngularMean_eq` | Exact original pulse mean and normalization |
| `onsetGreenCurrent_transfer` | Original pulse current expressed through the literal-source integral and current |

## Validation

Development used foreground `lake env lean` scratch checks. Final `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCircleGreen` passed: two jobs, 12 seconds, using an isolated cache-only audit with 3,986 project dependency modules and 12 local dependency stubs. No dependency or umbrella build ran. All seven new public theorem axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The installed source and five build artifacts match the audited files byte for byte. The module is wired once into `RHTower.lean`; that umbrella was not built. Source SHA-256: `f49eb04f7014f989b2f2a419354aaa2c56e3da756b55f4560f5aef89e44e595d`.

The separate mathlib-name scratch check passed. The corpus index refreshed once (three changed files, zero removed); all 14 new public API rows, the unique umbrella import, and local document links were verified. `scripts/formal_tools.py lint` passed, with existing large-file warnings. All owned Lean/Lake processes terminated; the isolated audit, scratch files and four search-result files were removed. The frontier map and universal `STATUS.md` were not edited.

The [analytical work card](../1-in-progress/hb-onset-pulse-green-action.md) contains the paper derivation, search applicability and the remaining causal-pairing target.
