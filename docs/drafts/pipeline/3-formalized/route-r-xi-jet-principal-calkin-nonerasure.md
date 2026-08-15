# Route R Xi-jet principal Calkin non-erasure

- **Stage:** 2 — fully proved on paper
- **Route:** R
- **Status:** `[NEW INTERNAL CLASSIFICATION] [LEAN-CERTIFIED] [NOT RH PROOF]`

Let `T_rho` be Route R's fixed `(2,3)` Stokes--Sonin receiver at centered
grade `a_rho`, and let

```text
c_rho = XiC^(m_rho)(z_rho) != 0
```

be the first nonzero multiplicity-exact Xi jet.  Define the forced singular
principal coefficient

```text
P_rho = c_rho^(-1) T_rho.
```

Then `c_rho P_rho = T_rho`.  Since multiplication by a nonzero complex
scalar preserves and reflects compactness,

```text
P_rho compact <-> T_rho compact <-> a_rho = 0
              <-> Re(rho) = 1/2.
```

More generally, if an operator `S` matches the same first Xi jet modulo the
compact ideal,

```text
c_rho S - T_rho compact,
```

then

```text
c_rho (S - P_rho) = c_rho S - T_rho
```

is compact, hence `S-P_rho` is compact.  Thus the leading Calkin class is
unique and nonzero at every off-line fibre.  A singular multiplier may
factor the punctured receiver, but its principal Calkin coefficient cannot
be removed by a source-exact compact counterterm unless the fibre is already
critical.

Strongest positive survivor: any viable singular Route-R producer must act
on this forced nonzero principal Calkin class and supply a genuinely
source-derived reason it is compact.  Choosing another Laurent lift,
regularizing lower coefficients, or changing compact representatives gives
no freedom.

No RH, critical-line placement, source-dagger identity, same-fibre norm
identity, or physical compactness is assumed.

The complete regular bounded class

```text
R_z = { XiC(z) S + K : S bounded, K compact }
```

has the exact fibre classification

```text
R_z = all bounded operators,  if XiC(z) != 0;
R_z = compact ideal,          if XiC(z) = 0.
```

It is operator-norm closed.  Hence finite regular expressions and their norm
completion cannot manufacture a missing divisor principal coefficient.
Allowing an arbitrary divisor-dependent compact leading coefficient `S_rho`
with `c_rho S_rho - T_rho` compact is still globally equivalent to RH.

## Lean certificate

Module: `GaloisForLFunctions.RHTower.RouteRXiJetPrincipalCalkinNonErasure`, wired into the
`GaloisForLFunctions.RHTower` umbrella.

| Card statement | Lean declaration |
|---|---|
| forced principal coefficient is compact exactly on the critical fibre | `routeRTwoThreeXiJetPrincipalCalkinCoefficient_isCompactOperator_iff` |
| principal Calkin class is unique modulo compacts | `routeRTwoThreeXiJetPrincipalCalkinCoefficient_unique_mod_compact` |
| fibre classification of the regular Xi/Calkin class | `routeRTwoThreeStokesReceiver_mem_regularXiCalkinClass_iff` |
| global regular membership is RH | `routeRTwoThreeStokesReceiver_global_mem_regularXiCalkinClass_iff_rh` |
| choice-free singular landing classification | `routeRCompactXiJetPrincipalLanding_iff_rh` |
| global removability of the principal coefficient is RH | `routeRTwoThreeXiJetPrincipalCalkinCoefficient_globalCompact_iff_rh` |

Every listed declaration reports exactly `propext`, `Classical.choice`, `Quot.sound`.
