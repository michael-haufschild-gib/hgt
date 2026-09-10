# HB: radial energy of the literal time primitive

Stage: 3-formalized. Three new public theorems passed the isolated final module build and axiom audit. Global angular energy, joint energy-domain admission, full physical inverse identification, physical-current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains the complete physical current with independent SS/SV/VV amplitudes. The immediate domain problem is to apply the original positive spatial operator to the literal native time primitive. The prior [elliptic equation](hb-native-time-primitive-elliptic-equation.md) supplies its pointwise action. This result discharges the radial Green boundary terms needed in the [cusp energy construction](../1-in-progress/hb-native-cusp-inverse-identification.md#native-elliptic-energy-construction).

## Exact statements

For arbitrary native `q : XiZeroCopy`, complex `s, amplitude` and real `t,X,k`, write

```
V(p,r)=fullNullResidual(q,s,amplitude,p,r,X,k),
W(x)=integral_0^t (t-u) V(u+x,u-x) du,
L=-max(t,0)-1.
```

All three theorems live in `RHTower.D4BMNativeResponse`, in [ThetaCuspHawkingBMFullNativeWave.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullNativeWave.lean).

| Theorem | Statement |
| --- | --- |
| `nativeResidualTimePrimitive_finite_propagation` | `max(t,0)<=abs(x)` implies `W(x)=0`, including characteristic edges and nonpositive time. |
| `nativeResidualTimePrimitive_radial_green` | `integral_L^0 conj(W) W_xx + integral_L^0 conj(W_x) W_x = 0`. |
| `nativeResidualTimePrimitive_radial_energy` | `integral_L^0 abs(W_x)^2 = -Re integral_L^0 conj(W) W_xx`. |

The derivatives are the actual Lean `deriv` of the literal integral. No field equation, regularity, trace or vanishing-current hypothesis is supplied to the Green or energy theorem.

## Proof

On the time integration interval, `u<=max(t,0)`. Outside the stated radial support, either `u+x<=0` or `u-x<=0`, so the previously proved exact source-cone vanishing applies pointwise. This also treats an oriented negative-time interval.

The actual first radial derivative follows by integrating the two continuous first null derivatives. The existing second-spatial-derivative theorem supplies differentiability of that derivative. Its right side is continuous, by continuity of the residual and compact parameter integration of the effective forcing. Thus both derivatives used in integration by parts exist and the relevant interval integrals are integrable.

Apply complex integration by parts to `conj(W)` and `W_x` over `[L,0]`. The original Dirichlet theorem gives `W(0)=0`; finite propagation gives `W(L)=0`. Both endpoint products vanish without a bound on the endpoint derivative. Taking real parts and using `Re(conj(z)*z)=norm(z)^2` gives the positive radial energy identity.

The angular action has not been dropped. Combining this identity with the known elliptic equation still leaves the angular term, whose compact modular Green identity and cusp limit are the next construction obligations. This result alone does not imply global energy finiteness or physical-current extinction.

## Validation

- Scratch: `lake env lean /tmp/hb-native-energy.jl2371mW/FullNativeWave.lean`, passed.
- Final: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullNativeWave` in an isolated audit root, passed in 35 seconds, two jobs. It used 4091 cached own-module dependencies and 11 cached dependency packages; no old dependency or umbrella was rebuilt.
- Only the three new public declarations were checked with `#print axioms` in a scratch file. Each depends only on `propext`, `Classical.choice`, `Quot.sound`.
- Source and the five emitted artifacts were installed byte for byte from the audited target, guarded against a concurrent source change.
- `scripts/formal_tools.py lint` passed; its size warnings include this 1807-line module.
- The existing import in `GaloisForLFunctions/RHTower.lean` already includes this module. The root umbrella and frontier map were not changed.

No mathematical computation or external numerical result enters these proofs.
