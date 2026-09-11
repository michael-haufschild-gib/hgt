# HB: full native spin-two primitive

Stage: 3-formalized for the full native spin-two primitive and its characteristic data. Full physical-current cancellation and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Direct hard target

The source transpose needs the original spin-two kernel and its characteristic derivative. The [original Darboux integral and source derivative](hb-native-darboux-primitive.md) admit the scalar native derivative. The new proof applies the actual angular Laplacian repeatedly to that same circle mean, derives the resulting Darboux equations and original contacts, then integrates the complete spin-two kernel twice. No separated angular eigenvalue or regularity premise is supplied.

## Conjecture and analytical proof mechanism

Let `F_n(d,X,k)=Delta^n mean(d,X,k)`, with the full base Laplacian in logarithmic height, and `A_n(Z)=F_n(arcosh Z)`. Joint smoothness of the original mean and the corpus radial/angular commutator give

```
sinh(d)^2 partial_d^2 F_n+sinh(d)cosh(d) partial_d F_n
  = sinh(d)^2 F_(n+1).
```

Continuity at zero forces `partial_d F_n(0)=0`. Dividing the regular equation away from zero and taking the original smooth derivative limit gives `partial_d^2 F_n(0)=F_(n+1)(0)/2`. Thus `A_n'(Z)` has the original right limit `F_(n+1)(0)/2`, for every finite angular iterate.

Put `w=Z^2-1`, `B_n=A_n'`, and define the original full-source primitive

```
J=w*(A_1-2Z B_0),
J_1=w*(B_1-2B_0).
```

The actual Darboux equations give `J'=J_1` and `J_1'=A_2-2A_1`. Both primitive jets tend to zero at the original characteristic because the admitted `A_n` and `B_n` have finite limits. The fundamental theorem therefore gives

```
J(Z)=integral(r=1..Z) (Z-r)*(A_2(r)-2A_1(r)) dr.
```

The retained spin-two kernel is `-A_2+2A_1`. The proof identifies it with `nativeSpinTwoTrace` of the original physical direct/image kernel, with source radius frozen before angular differentiation. The equality holds on the characteristic as well as in the interior. It retains every principal power and the entire cusp remainder.

The same all-iterate contact gives the actual spin-two right derivative and the limit of its ordinary interior derivative:

```
partial_Z spinTwo(1)=(-F_3(0)+2F_2(0))/2.
```

Continuity of the original spin-two trace on every compact invariant interval and the two integral formulas give a positive constant `C`, depending on the original source, angular base point and upper invariant bound, such that

```
|J(Z)| <= C (Z-1)^2,  |J_1(Z)| <= C (Z-1).
```

These are proved bounds, not assigned endpoint values. The [original diagonal delay transfer](hb-spin-two-delay-characteristic.md) now factors both primitives into continuous native moments, proves the exact degenerate characteristic current and bulk contact, and establishes the finite transfer with the original clock. Every geometric coefficient loses its inverse-radius poles. Uniformity over angular compact sets, off-diagonal/image delay transfer and the full physical-current comparison still need their own proofs.

## Corpus ingredients

`ThetaCuspHawkingBMCommonSourceGreen` contains actual coordinate-derivative commutation, joint smoothness and the radial/base Laplacian commutator. `ThetaCuspHawkingBMNativeCharacteristicContact` contains the original smooth radial contact argument. `ThetaCuspHawkingBMSpinTwoKernelPrimitive` supplies the two-zero-jet FTC method for a separated Legendre kernel; the present target proves the corresponding original full-source identity.

## Formal status

The scratch proof and exact-module build passed. The isolated exact target built in 18 seconds, three jobs, reusing 4,134 cached own modules, 20,526 available artifact links and 12 dependency path packages. No old module or umbrella build ran.

Exactly the thirteen new public theorems were audited in a separate scratch file; each reported only `propext`, `Classical.choice`, and `Quot.sound`. The verified source and five artifacts were installed byte-identically. The new module is wired once into `RHTower.lean`; no umbrella build ran. Corpus indexing completed (two changed files), formal lint passed with existing large-file warnings, and twelve local document links passed. All owned search, Lean, Lake, indexing and lint handles reached terminal status. The final owned-process check was clear; scratch, isolated audit and search files were removed. The frontier map and universal ledger were not edited. No mathematical computation ran.

[ThetaCuspHawkingBMNativeSpinTwoPrimitive](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeSpinTwoPrimitive.lean), namespace `RHTower.D4BMNativeSpinTwoPrimitive`, proves:

- `laplaceMean_darboux`: the actual radial Darboux equation for every angular-Laplacian iterate.
- `first_tendsto_characteristic`, `argument_right_derivative`: the actual first invariant contacts of all those original iterates.
- `spinTwo_right_derivative`, `spinTwo_derivative_tendsto_characteristic`: the original retained spin-two contact and interior derivative limit.
- `primitive_derivatives`, `primitive_eq_weighted_second`: the two actual primitive derivatives and its identification with `(Z^2-1)^2 partial_Z^2 M`.
- `primitive_characteristic`, `primitive_tendsto_characteristic`: the two zero endpoint values and their independently derived interior limits.
- `primitiveFirst_integral`, `primitive_volterra`: both full-source integral identities.
- `primitive_characteristic_bounds`: linear and quadratic characteristic orders on each compact invariant interval.
- `nativeSpinTwoTrace_eq`: equality with the original radius-frozen direct/image physical trace.

The derivative equation is obtained by commuting the literal coordinate derivatives of the smooth circle mean. The endpoint argument differentiates the original smooth radial functions and takes punctured limits. The final FTC uses those limits rather than postulating boundary regularity. Angular principal currents, the full transposed physical kernel action and complete cancellation remain open.

## Search applicability

Own deep queries included `commuting derivatives`, `interchange Laplacian`, and `second primitive boundary estimate`; broad OR searches were used where terms need not co-occur. Candidate statements, source arguments, proof-method views and proposed ingredient sets were inspected. The latest search inventoried 56,454 files, with 371 pending/stale source files and predominantly source-only compiler metadata. Coverage was partial. The proposed abstract Fourier-multiplier and boundary-chain ingredient sets did not discharge the literal native-source obligations.

`ComplexCoordinateDerivativeRules` and the common-source Green proof supplied actual coordinate commutation. The Fokas–Lenells causal-orbit proof supplied the norm-of-integral bounding method; its different evolution was not substituted for this source. The existing endpoint FTC and separated primitive supplied proof mechanisms whose applicability was checked on the original native mean in Lean.

Broad arXiv searches used bispectral, commuting flows, transposition, transgression and intertwining, including recent date filters. They did not return a useful June–September 2026 ingredient. Inspected primary sources included [Bakalov–Horozov–Yakimov, General methods for constructing bispectral operators](https://arxiv.org/abs/q-alg/9605011) (May 1996) and [Beceanu–Schlag, Structure formulas for wave operators](https://arxiv.org/abs/1612.07304) (December 2016; revised January 2017). Neither supplies the original source-current cancellation; neither is a proof premise.
