# HB: original-source characteristic radial flux

Status: nine source-current theorems formalized. Complete physical-current cancellation and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and all physical boundary components. The [original-source Green identity](hb-common-source-green-transfer.md) identifies the actual local transfer. This work proves its improper radial integral, signed characteristic face, and late-delay cancellation of that face at fixed source time.

## Exact Lean scope

The [source module](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCommonSourceGreen.lean), namespace `RHTower.D4BMCommonSourceGreen`, proves:

- `nativeSpinTwoTrace_eq_interior`: the frozen-radius angular trace equals the full spin-two kernel on the smooth cone interior.
- `nativeSpinTwoTrace_characteristic`: both characteristic traces equal the full original spin-two source.
- `sourceCharacteristic_causal_interval`: the actual causal source intervals have the stated finite lower endpoints.
- `sourceRadialTraceCurrent_signed_faces`: exact direct-minus-image radial face, including both upper and both lower endpoints.
- `sourceRadialCurrent_characteristic_limit`: the original interior current has the derived characteristic limit.
- `sourceRadialTransfer_integral`: the original source/transpose integrand, retaining both angular divergences, has the stated integral on every truncated physical interval.
- `sourceRadialTransfer_characteristic_integral`: its improper limit at either characteristic is the negative characteristic current.
- `sourceRadialTransfer_signed_characteristic_integral`: the two actual improper integrals have the exact signed face as their common-cutoff limit.
- `sourceRadialTraceCurrent_signed_faces_tendsto_zero`: this signed face tends to zero at fixed source time as ingoing delay tends to infinity.

Source regularity and characteristic admission are derived internally. Geometric parameters specify the actual positive-delay, negative-radius domains. No boundary cancellation, endpoint integrability, altered onset or angular eigenvalue equation is supplied as a hypothesis.

## Conjecture and proof mechanism

At fixed ingoing delay `H`, target `x`, and source `y`, the direct kernel uses `invariant(H-x+y,x,y)` and the image uses `invariant(H-x+y,x,-y)`. Their lower source faces are respectively `x-H/2` and `-H/2`. Both invariants equal one there, so their angular traces are the literal source `Q`.

Take the full spin-two operator `R=-Delta(Delta-2)` on angular slices with source radius fixed. This defines the trace even when transverse differentiability across the characteristic has not been admitted. On the smooth cone interior it agrees with the spin-two field in the proved Green identity. At either characteristic its value is exactly `R Q`.

With `u(y)=-tanh y`, `b(u)=u^4(1+u)`, `K=(7lambda-2-2Delta)/8`, and original seed `F_s=a² chi(v)exp(2sv)(1+u)^(2s)Q`, the radial current is `b(u)exp(-k)(K F_s)(R M Q)`. Its upper source face vanishes at `y=0`. The signed direct-minus-image face is therefore

```
exp(-k) a² chi(v)exp(2sv) (KQ)(RQ)
  * [b(u_image)(1+u_image)^(2s)
     -b(u_direct)(1+u_direct)^(2s)].
```

## Radial integral and characteristic admission

Let `G` be either full spin-two native kernel, and retain the original Green currents `I_x,I_X,I_k`. Define the combined integrand

```
D(y)=mu(y,k)[(P F)(y)G(y)-F(y)(Pdagger G)(y)]
     -partial_X I_X(y)-partial_k I_k(y).
```

For every cutoff strictly between the corresponding characteristic `e` and zero, the local identity gives `D=partial_y I_x`; the kernel and source are smooth throughout that truncated interval. The fundamental theorem of calculus yields

```
integral_cut^0 D(y)dy = -I_x(cut).
```

Joint smoothness of the circle mean implies continuity of its full angular spin-two transform in circle radius. Composing with `arcosh Z` near `Z=1` gives the actual characteristic limit of `I_x`. Therefore the truncated integrals have an improper limit as `cut` decreases to `e`, equal to the negative characteristic current. This argument requires no assumed integrability at the characteristic. Taking the direct-minus-image difference with cutoffs `e_direct+d,e_image+d`, then `d→0+`, gives exactly the displayed signed face above.

The two angular divergences remain in this combined integrand. This does not yet integrate them over the original angular domain, establish one-sided transverse derivatives of every current component, transport the full Einstein current, or justify physical horizon/cusp/time limits.

## Late-delay cancellation of this radial face

For any fixed complex rate, `W_s(y)=b(u(y))(1+u(y))^(2s)` has the same finite limit `2*2^(2s)` as `y→-infinity`. Both source characteristics tend to minus infinity when `H→infinity` at fixed target. Consequently their difference tends to zero, and the complete signed radial face vanishes at fixed source time, amplitude and angular point. This is a cancellation between the two actual characteristic contributions. The [source-time integral](hb-source-time-radial-flux.md) has a formal `C exp(-T)` bound, uniform in exterior target radius, retaining the full angular coefficient and actual onset. The [source-time/radial interchange](hb-source-time-radial-interchange.md) now transfers that bound to the admitted original radial source integrals. Angular integration and the other physical boundary currents remain open.

## Search and applicability

Broad corpus queries `bispectral` and `concomitant`, a deep source/kernel-intertwining query, and a deep kernel-moment integration query were used. Available results are partial; source-only statements and generated ingredient groups require verification. The exact native characteristic theorem and the existing compact-circle smoothness proof supply the relevant ingredients here. Shared source rates alone have not supplied the required cancellation identity.

An independent literature search found [Intertwining diffusions and wave equations](https://arxiv.org/abs/1306.0857), revised June 2025. It connects intertwining to a kernel PDE with additional compatibility conditions; it supplies no cancellation theorem for this source. No external paper is a premise of these formal results.

## Validation

Scratch checks passed for the new calculus, source traces, integrals and delay limits. The final audit built only `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonSourceGreen`; Lean compiled the complete 1,184-line module in 15 seconds, and Lake reported three jobs. The 4,133 existing own-corpus dependencies and installed package artifacts were frozen. No dependency or umbrella build ran.

Only the nine new public theorems were axiom-audited. Each reports exactly `propext`, `Classical.choice` and `Quot.sound`. The installed source and five olean/ilean/hash/trace artifacts are byte-identical to the audited files. The original source prefix is unchanged, and the existing RHTower import is verified. No mathematical computation was used.

The corpus index was refreshed. Whole-corpus static lint passed with existing large-file warnings only; all eleven local report links and scoped whitespace checks passed. All owned Lean/Lake processes exited, and the owned scratch tree, search outputs and lint output were removed. The frontier map and universal status ledger were unchanged.
