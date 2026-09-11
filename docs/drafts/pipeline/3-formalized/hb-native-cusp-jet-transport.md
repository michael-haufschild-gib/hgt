# HB: native circle cusp-jet transport

Stage: 3-formalized for actual native-mean derivative interchange, uniform cusp bounds and weighted limits. Full physical-current cancellation and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Source admission: [actual source cusp jets](hb-angular-cusp-jet-admission.md) now have every complex height-weighted bound. The present theorem closes transport to the actual native remainder and its radius/base-coordinate jets, needed for the retained angular Green currents.

## Formalized result and proof mechanism

For every finite derivative word in radius, horizontal position and logarithmic height, and every compact nonnegative radius interval, the literal `cuspMeanRemainder` has arbitrary inverse-height decay uniformly in horizontal position and radius. Its three transported principal powers remain explicit.

At the integrand level, use all four coordinates `(d,theta,X,k)`. Every derivative of the pulled-back source remainder is a finite sum of `c(d,theta) exp(m k)` times an actual coordinate jet of the original source at `logCircle(d,theta,X,k)`. Here `m` is a nonnegative integer and `c` is smooth. The exact circle derivative formulas prove closure of this class. Compactness bounds `c`; the circle height lower bound and source estimate at a sufficiently high order absorb every `exp(m k)`.

Differentiate the actual compact angle integral, using its smooth local majorants, and apply this integrand bound. This retains the original infinite Fourier source and the original averaging measure. No packet regularity or decay premise is supplied by the caller.

## Literature and search

Own broad terms: spherical averaging, transmutation, intertwining. Deep corpus searches target derivative transport and parameter-integral methods. Recent arXiv search examined [Elber–Lheem, Intertwining Operators for Siegel Parabolics over Finite Fields](https://arxiv.org/abs/2608.01485) (August 2026) and [Frassek et al., Intertwining Markov Processes via Matrix Product Operators](https://arxiv.org/abs/2603.09928) (revised May 2026). Their exact intertwining constructions suggest tracking the transformed operator and boundary data explicitly; no theorem from either paper is used as a premise.

## Exact analytical closure

Let `p=(d,theta,X,k)`, `z=circleMap(p)`, and `J_w(p)` be the actual source derivative word `w` evaluated at `z`. For coordinate index `i`, write `delta(i,j)` for the Kronecker symbol and `sigma_i=(delta(i,0),delta(i,1))`. Put

```
a_i = delta(i,3) offset + derivative(offset)[sigma_i],
b_i = delta(i,3) height + derivative(height)[sigma_i].
```

The chain rule gives

```
D_i J_w = delta(i,2) J_(0::w)
          + exp(k) [a_i J_(0::w) + b_i J_(1::w)].
```

For `c(d,theta) exp(mk) J_w`, differentiating `c` and `exp(mk)` leaves the same form at exponent `m`; the final two terms raise `m` by one. All coefficients remain smooth because the original circle denominator is strictly positive. This proves the finite representation by induction on an arbitrary ordered derivative word.

For `0<=d<=D<=k`, original circle height is at least `exp(k-D)>=1`. Apply the actual source-jet estimate at order `N+m`. Multiplication by `exp(mk)` gives

```
exp(mk) exp((N+m)(D-k)) = exp(mD) exp(N(D-k)).
```

Every coefficient has a bound on the compact `(d,theta)` rectangle. Finite addition preserves the same decay envelope. Thus all four-coordinate integrand jets have arbitrary inverse-height decay uniformly in `X`.

A locally uniform compact majorant for the Fréchet derivative justifies differentiating the original angle integral. Evaluation of the resulting integral of continuous linear maps on a coordinate vector gives the integral of the corresponding coordinate derivative. Iterate this identity; no derivative is exchanged on the basis of pointwise decay alone. The original `cuspMeanRemainder_integral` identifies the admitted mean with the existing native remainder, including its factor `1/2`.

The estimate at order `N+1` gives decay after multiplication by `exp(Nk)` along every arbitrary horizontal path and every radius path valued in `[0,D]`. No regularity of either path is needed because the jets are taken before path evaluation.

## Remaining physical scope

All three principal powers remain in `transportedPrincipal`. The present theorem targets the remainder only. It does not yet evaluate the principal angular Green flux, integrate the full physical current, or prove uniform admission of derivatives in the causal invariant `Z=cosh(d)` at `Z=1`.

## Source-specific derivative transfer

The corpus already proves `argumentFirst_tendsto_characteristic` and `angularKernel_right_derivative` in `ThetaCuspHawkingBMNativeCharacteristicContact`, including `M_Z(1)=Delta Q/2`. The remaining transfer requires more than that first contact. The [native Darboux primitive](hb-native-darboux-primitive.md) derives a nonsingular integral for the original invariant derivative and its application to physical source-radius differentiation. Higher invariant/angular derivative transfer and full principal-current cancellation remain separate obligations.

## Corpus lead for the next bridge

The broad `Darboux Volterra` search found `D4BMSpinTwoKernel.primitive_volterra` in `ThetaCuspHawkingBMSpinTwoKernelPrimitive`. Its original-kernel fundamental-theorem argument retains two characteristic zero jets and the full spin-two factor. It applies to the complex-degree Legendre kernel. The reusable method is to integrate the native Darboux operator and prove its lower current from actual smoothness; applying a fixed scalar degree to the full angular source would not establish that bridge.

## Lean certificate

The new [ThetaCuspHawkingBMNativeCuspJets.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeCuspJets.lean) exposes `nativeJet`, `nativeIntegrandJet`, `circleRemainder`, and three unconditional source-specific theorems in `RHTower.D4BMNativeCuspJets`:

- `nativeCuspJet_integral`: every ordered native derivative equals its actual integrand derivative averaged with the original measure.
- `nativeCuspJet_rapid_bound`: for every derivative word, order `N`, and fixed `D>=0`, one constant gives `|jet(d,X,k)| <= B exp(N(D-k))` whenever `0<=d<=D<=k`, uniformly in `X`.
- `nativeCuspJet_weighted_tendsto_zero`: `exp(Nk) jet(d(k),X(k),k)` tends to zero for arbitrary paths `d(k)` in `[0,D]` and arbitrary `X(k)`.

The existing [source-jet module](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSquareCuspJets.lean) adds `squareRemainder_jet_smooth`; its previously audited declaration prefix is unchanged.

Scratch `lake env lean` checks passed. Final exact-module builds passed without warnings: the source-jet extension in 135 seconds (three jobs), and the native module in 90 seconds (four jobs). The isolated audit froze 3,944 cached own-module imports and their available artifacts. No dependency or umbrella build ran. Only the four new public theorems were axiom-audited; each reported exactly `propext`, `Classical.choice`, and `Quot.sound`. Both verified sources and ten artifacts were installed byte-identically, and the new native module was wired into `RHTower.lean`. Corpus indexing completed, formal lint passed, and edited local links, whitespace and target umbrella imports passed. All owned search and Lean processes reached terminal status; owned scratch and search files were removed.

Full principal angular flux, complete physical-current cancellation, fixed Hawking-clock extinction and RH remain unproved.
