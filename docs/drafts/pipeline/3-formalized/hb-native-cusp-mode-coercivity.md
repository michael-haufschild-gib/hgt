# HB: source-derived forced coercivity of native cusp modes

- **ID:** HB-QNCM
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Predecessor:** [physical-clock tested-current balance](hb-physical-clock-tested-current-cusp-balance.md)
- **Active attack:** [source-contact/current balance](../1-in-progress/hb-source-contact-spin-two-balance.md)
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMQuarticNativeCuspModes.lean`

Proof chain: literal theta cusp → Xi occurrence → retained spin two → physical
causal radial/left-QNM action → fixed common Hawking-clock extinction → RH.
The hard boundary obstacle is the mean of products of the native responses
and their derivatives in the actual scalar-tested vertical current. Knowing
each response's mean does not determine those products.

## Constructed fields and exact equations

For each original Xi occurrence q and either physical branch b, take the
constructed native response R=globalResponse q b and its complete
cusp-subtracted forcing F=globalForcing q b. Put alpha=parameter q b and

```
c_n(y) = integral_0^1 exp(-2*pi*i*n*x) R(x+i*y) dx,
f_n(y) = integral_0^1 exp(-2*pi*i*n*x) F(x+i*y) dx,
k_n = 2*pi*n,
u_n = |c_n|^2,
W_n = Re(f_n conjugate(c_n))/y^2.
```

The native response solves y^2 Delta_planar R=alpha R+F. Smoothness justifies
both height derivatives of its literal coefficients. Two horizontal
integrations by parts cancel only the periodic side terms, giving

```
c_n'' = k_n^2 c_n + (alpha c_n+f_n)/y^2,
u_n'  = 2 Re(c_n' conjugate(c_n)),
u_n'' = 2|c_n'|^2 + 2(k_n^2+Re(alpha)/y^2)u_n + 2W_n.
```

This is the forced response equation, including n=0. It is not the
homogeneous Maass eigenfunction equation. Both actual response branches and
the complete forcing remain; no source work is set to zero.

## Coercive estimate

The nonnegative square |c_n+f_n/y^2|^2 gives

```
u_n'' >= 2|c_n'|^2
          +(2k_n^2+2Re(alpha)/y^2-1)u_n-|f_n|^2/y^4.
```

Set Y_b=1+2|Re(alpha)|. For y>=Y_b, Re(alpha)/y^2>=-1/2.
For n!=0, the integer frequency gap gives k_n^2>=2. Consequently

```
u_n'' >= 2|c_n'|^2 + k_n^2 u_n - |f_n|^2/y^4.
```

Y_b is a cusp-height cutoff only. The original physical spectral parameters,
common Hawking clock and horizon rate are unchanged.

## Inputs proved from the literal source

For every complex weight w there is C>=0 such that

```
|y^w f_n(y)| <= C                 (all integers n, all y>3),
sum_n |c_n(y)|^2 = mean_x |R(x+i*y)|^2,
integral_2^infinity |c_n(y)|^2/y^2 dy < infinity.
```

The first follows from the literal weighted square-remainder bound. Above
the original transition region F=(alpha/2)*squareRemainder; modular
translation moves the right half of [0,1] into the closed fundamental cell
without changing height or forcing. The Fourier kernel has norm one, so the
same bound holds for every integer coefficient.

Parseval is applied to the actual smooth response, not a proposed modal
ansatz. Its periodicity moves the period integral to the original
[-1/2,1/2] cusp rectangle. Each modal mass is bounded by the full nonnegative
slice mass. The latter's y^-2 integral is already admitted by the constructed
modular energy; domination proves the modal integral. Thus neither decay
nor a zero boundary value is an input.

## Comparison successor and remaining boundary work

[HB-QNCD](hb-native-nonconstant-cusp-decay.md) now proves the infinite-cusp
comparison and complete summed nonconstant-mass decay from these inputs.
For each nonzero mode it uses a source-derived barrier
u_n(Y)*exp(Y-y)+(C_N/k_n^2)*y^(-(2*N+4)). Native weighted integrability
supplies distant finite comparison endpoints; no upper boundary value is
assumed. Parseval and inverse-square summability retain every nonzero mode.
The full native mass splits exactly into its retained zero-mode mass plus
the rapidly decaying remainder.

The present module supplies the differential/coercive/admission inputs.
Polynomially weighted derivative control, the actual complete tested-current
finite part, physical-action identification and fixed-clock extinction remain
open. Neither module changes the original physical clock or assigns the
native homogeneous mean zero.

## Lean verification

All statements passed `lake env lean /tmp/hb-native-cusp-modes.lean` at
default limits. Finite regularity coercions, explicit chart/function
identifications, and a separate nonnegative-square identity resolved
elaboration failures. No heartbeat, recursion-depth or transparency override
was introduced. The module has five public definitions and nine public
theorems and is wired once into RHTower. The exact isolated leaf audit uses
cached dependencies; its final result and generated-index lint are recorded
below after completion.

Exact isolated leaf audit passed in 59 seconds at default limits. Source
SHA256: `033761794ebf44dea4d5ca66b7602d70c005b4971dcb10f77c667339f1dd35c6`.
The checked source's matching Lean artifacts were published to the local
cache. No dependency or umbrella build was run.

All 14 public API rows, the single umbrella import, unchanged source hash,
and removal of the temporary audit directory were verified. All owned Lean
and search processes completed. Global lint was run after the index refresh;
concurrent tree changes prevented a green repository-wide result. The initial
unreachable RealSL2Haar module was subsequently wired by other work. A final
combined refresh/check (2 newly changed files) reports an unreachable
`GaloisForLFunctions.HTGeometry.CoordinateEinsteinDiagonalCollapse` and stale
LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md. This is recorded as a failed global
lint, not a passed gate. No unrelated module was edited to suppress it.
The exact new leaf audit remains successful. Log:
`formal/.lake/hb-extinction-scratch/native-cusp-modes-final-lint.log`.
