# Xi/full-density source-exchange obstruction

- **ID:** `xi-full-density-source-exchange-obstruction`
- **Stage:** 3-formalized
- **Type:** `[THEOREM (LEAN)] [NEW CORPUS KNOWLEDGE] [UNCONDITIONAL] [NO RH CLAIM]`
- **Failed predecessor:**
  `../../5-failed/xi-taylor-full-density-transfer-wronskian.md`
- **Successor:**
  `../../1-in-progress/xi-completed-density-antipodal-crossing-barrier.md`

## Result

For the canonical zero-free full-density channel `F` and final odd Xi Taylor sections `P_d`, define

```text
W_d=P_d'F-P_dF',
Omega_F=XiC'F-XiC F',
R_d=XiC-P_d.
```

Then unconditionally:

```text
W_d=Omega_F-(R_d'F-R_dF'),
W_d(z) -> Omega_F(z) for every fixed z,
Omega_F(0)!=0.                                        (1)
```

The exact two-phase kernel is `i(x-t)exp(i(x+t)z)` and vanishes exactly at `x=t`, proving that
full-phase cancellation requires a source-matched antisymmetric integration and is unavailable for
the Xi/full-density pair.

The completed reflection and its derivative further give

```text
C_F=2z(F+F(-z))F-(z^2+1/4)(F'(-z)F+F(-z)F')+(1/2)F'
   =8z XiC F+4z^2 Omega_F.                             (2)
```

At every simple Xi zero in the open upper theta strip, `C_F=4z^2 XiC'F!=0`.

Finally, if `T_d=P_d/F` and `Q=XiC/F`, then

```text
T_d -> Q,
T_d' -> Q',
J(T_d) -> J(Q),
Q(z)=0 <-> XiC(z)=0  for Im z>0.                      (3)
```

This corrects the frontier interpretation: transfer current is an exact RH-equivalent gauge
bridge, but not a finite-truncation defect.  Its limit retains the full Xi divisor.

## Paper proof

Kernel identity is exponential multiplication and ring algebra.  Equation `(1)` follows by adding
and subtracting `XiC'F-XiC F'`; convergence follows from locally uniform convergence of canonical
Taylor sections and their derivatives.  At zero, Xi parity gives `XiC'(0)=0`, while positivity of
`rho` gives

```text
F'(0)=i integral t rho(t)dt !=0.
```

Since `XiC(0)!=0`, `Omega_F(0)=-XiC(0)F'(0)!=0`.

For `(2)`, multiply differentiated completed reflection by `F` and subtract the value reflection
multiplied by `F'`; common `F'F` terms cancel.  At a simple upper zero, monotone completion gives
`F!=0`, so the remaining product is nonzero.  Equation `(3)` follows from Taylor convergence,
continuity of field operations, and zero-freeness of `F`.

## Scientific significance

The generic algebra is classical.  New corpus knowledge is source-specific closure of the failed
mechanism: exact theta sources force a nonzero reflected background, and the canonical transfer
converges to `XiC/F` rather than to a truncation defect.  Publication novelty is not claimed.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailFullDensityWronskianNoGo.lean`.

Principal declarations:

- `fullPhaseWronskianKernel_eq_zero_iff`;
- `xiCTaylorFullDensityWronskian_eq_full_sub_remainder`;
- `xiFullDensityReflectedConnection_eq_background`;
- `xiFullDensityReflectedConnection_ne_zero_at_simple_upper_zero`;
- `xiFullDensityWronskian_zero_ne`;
- `tendsto_xiCTaylorFullDensityWronskian`;
- `xiFullDensityQuotientValue_eq_zero_iff`;
- `tendsto_xiCTaylorFullDensityTransferCurrent`.

## Status

Formalized.  Direct Lean check and targeted module build pass.  Axiom audit of kernel
classification, remainder decomposition, reflected connection, central noncancellation, quotient
zero set, and transfer-current limit reports only `propext`, `Classical.choice`, and `Quot.sound`.
`scripts/formal_tools.py lint` passes.

## Log

- 2026-07-21 — Derived by first hostile symbolic experiment on proposed transfer Wronskian.
- 2026-07-21 — Paper proof formalized; direct check, targeted build, axiom audit, and lint passed.
