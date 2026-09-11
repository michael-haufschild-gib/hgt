# HB: full angular circle action and physical wave kernel

Status: formalized. The physical pulse convolution, complete mixed action and RH remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Owner: [ThetaCuspHawkingBMFullAngularCircleAction.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularCircleAction.lean), namespace `RHTower.D4BMFullAngularCircleAction`.

Let `h(d,X,k)` be the actual circular mean of the constructed full angular field `H`, and let `m` be the original theta half-square mean. The proved base action is

```
exp(2k) partial_XX h + partial_kk h - partial_k h
  = average_theta [(Delta H)(logCircle)]
  = alpha (h + m).
```

The proof differentiates the actual compact circle average. The original circle-chart coefficient identities express the pointwise transport defect as `-2 exp(k) partial_theta(partial_X H(logCircle))`. Periodicity removes that term upon averaging. Full angular-field smoothness supplies every derivative and integral admission; commutation is derived rather than assumed.

Combined with the full mean's radial forced equation, this proves its actual radial/base Darboux equation. Therefore

```
K(h,x,y,X,k) = h_mean(arcosh(invariant(h,x,y)),X,k)
```

obeys the original time/tortoise wave equation inside the original characteristic cone:

```
partial_hh K - partial_xx K
  - [exp(2k) partial_XX K + partial_kk K - partial_k K] / cosh(x)^2 = 0.
```

All derivatives are actual derivatives. The characteristic value is the unchanged `H(X,exp k)`; the direct and reflected kernels agree at the original AdS boundary. Thus the full-angular circular kernel appearing in the [source-only reconstruction](hb-full-angular-circle-reconstruction.md) has its original angular wave action identified. The complete onset pulse still requires causal integral formation and its signed comparison with the incoming wave image, both cross terms and every physical face.

## Public proof API

| Theorem | Content |
|---|---|
| `angularMean_laplacian_commutes` | Actual base Laplacian equals the averaged full-field Laplacian |
| `angularMean_laplacian_equation` | Full response and literal half-square forcing both retained |
| `angularMean_darboux` | Actual radial/base Darboux equation |
| `fullAngularRiemannKernel_wave` | Original interior time/tortoise wave equation |
| `fullAngularRiemannKernel_characteristic` | Original full-field characteristic value |
| `fullAngularRiemannKernel_AdS` | Direct/image agreement at the AdS endpoint |

`fullAngularRiemannKernel` is the one new public definition.

## Validation

Foreground `lake env lean` scratch checks passed without warnings. Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleAction` passed without warnings: three jobs, 82 seconds, with only the new action module reported built. The isolated audit reused the existing dependency cache and the already audited reconstruction module. No dependency or umbrella build ran. Source and five installed build artifacts match the audited files byte for byte. The module is wired once into `RHTower.lean`.

Source SHA-256: `ec74c479f401a83d4fcf89bc20cc72786c966ab3c391d8b0d4c1e6785276d760`.

All six new public theorem axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The shared corpus index refresh ran once (10 changed files, zero removed); all seven new public API rows, the unique umbrella import, final local document links and installed artifacts were verified. Repository-wide `scripts/formal_tools.py lint` passed after unrelated concurrent umbrella additions settled; existing large-file warnings remain. All owned Lean/Lake processes terminated, and the isolated audit, scratch files and five search-result files were removed. The [analytical card](../1-in-progress/hb-onset-pulse-green-action.md) records the proof mechanism and remaining causal-pairing target. The frontier map and universal `STATUS.md` were not edited.
