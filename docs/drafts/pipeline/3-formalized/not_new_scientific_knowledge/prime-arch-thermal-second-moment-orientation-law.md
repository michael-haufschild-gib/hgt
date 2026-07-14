# Prime--archimedean thermal second-moment orientation law

- **ID:** `prime-arch-thermal-second-moment-orientation-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** the reciprocal-square Xi moment identity, the completed endpoint value bound, and
  finite atomic KMS realization
- **Statement:** The explicit finite Xi thermal systems are unconditionally KMS-realizable, and
  RH is equivalent to convergence of their single second-moment value to the first nontrivial
  normalized prime--Gamma source moment.
- **Novelty status:** not asserted; the value relation is retained for its RH proof leverage.

## Main law

For a multiplicity copy `q` of the Xi divisor, set

```text
z_q      = (xiSpectralPoint q)^(-1),
lambda_q = z_q^2,
a_q      = Re(lambda_q).
```

Every `a_q` is strictly positive without RH.  Indeed, if
`delta = Re(rho_q)-1/2` and `gamma = Im(rho_q)`, then

```text
a_q = (gamma^2-delta^2)/(gamma^2+delta^2)^2.
```

The completed endpoint law gives `gamma^2>1`, while the open critical strip gives
`delta^2<1/4`.  Hence the multiplicity-exact truncations

```text
m_N(n) = sum_(j<N) a_j^(n+1)
```

are positive finite atomic moment sequences and therefore canonical finite KMS/Wightman moment
sequences.  For every `n`, absolute summability proves the unconditional thermodynamic limit

```text
lim_(N->infinity) m_N(n) = M_positive(n)
                       := sum_q a_q^(n+1).                (0)
```

Thus existence of the complete positive thermal moment tower requires no RH input.  Its
identification `M_positive = normalizedPrimeArchMoment` is equivalent to RH, and the coordinate
`n=1` already decides that equality.

Define the thermodynamic second moment and transverse orientation energy by

```text
M_2 = sum_q (Re(lambda_q))^2,
E_T = sum_q (Im(lambda_q))^2.
```

Absolute reciprocal-square summability makes both series convergent.  The first nontrivial
normalized prime--Gamma source value `m_source(1)` satisfies the exact identity

```text
M_2 - E_T = m_source(1).                                  (1)
```

Consequently

```text
m_source(1) <= M_2                                        (2)
```

unconditionally, and the following statements are equivalent:

```text
RH
M_2 = m_source(1)
M_2 <= m_source(1)
E_T = 0
lim_(N->infinity) m_N(1) = m_source(1).                   (3)
```

Thus the entire thermal-limit proof obligation reduces to the reverse of the already proved
lower bound `(2)`, at one scalar value.

Equivalently, the Hermitian square mass

```text
H_2 = sum_q |lambda_q|^2
```

satisfies

```text
H_2-m_source(1) = 2 E_T,
M_2 = (H_2+m_source(1))/2.                                (3a)
```

This is the static operator-state form: `m_source(1) <= H_2` is the universal
Hermitian/holomorphic trace inequality, and RH is exactly its equality case or its reverse
inequality.

For the concrete reciprocal Xi kernel `K = xiReciprocalDiagonalKernel`, Lean also identifies both
sides as intrinsic operator values:

```text
H_2         = ||K^2||_HS^2,
m_source(1) = Re Tr(K^4).
```

Hence the exact gap and the resulting one-law RH criterion are

```text
||K^2||_HS^2 - Re Tr(K^4) = 2 E_T,
||K^2||_HS^2 - Re Tr(K^4) = (1/2)||K^2-(K^2)^*||_HS^2,
RH iff ||K^2||_HS^2 <= Re Tr(K^4),                       (3b)
```

while `Re Tr(K^4) <= ||K^2||_HS^2` is unconditional.  This removes the source-value placeholder
from the static formulation: the remaining estimate is an internal norm-versus-trace saturation
law for one explicit compact Hilbert--Schmidt kernel.

## Reflection-energy identification

Let

```text
D_Xi = sum_q |z_q-conj(z_q)|^2
```

be the existing global reflection-defect energy.  Pointwise,

```text
(Im(lambda_q))^2
  = (Re(z_q))^2 |z_q-conj(z_q)|^2.                        (4)
```

The completed endpoint bound proves

```text
0 < (Re(z_q))^2 < 1                                       (5)
```

at every Xi zero.  Therefore `E_T` is a faithful high-height-damped form of the existing global
defect:

```text
0 <= E_T <= D_Xi,
E_T < D_Xi iff not RH.                                    (6)
```

Combining `(1)` with the existing global source-gap identity gives

```text
M_2-m_source(1)
  <= 2 (xiReciprocalHermitianMass-primeArchCentralCurvature).  (7)
```

The thermal obstruction is therefore not an additional gap.  It is a strictly smoothed but
zero-faithful version of the established reflection defect.

## RH proof impact

The finite-system construction, KMS positivity, and convergence of the complete positive moment
tower are discharged unconditionally.  No single finite system needs to represent all source
moments: finite systems may grow, and their pointwise limit stays in the closed trace--Hankel cone.
It is enough to prove either of the equivalent one-value reverse inequalities

```text
M_2 <= m_source(1),
||K^2||_HS^2 <= Re Tr(K^4).
```

This theorem does not prove that inequality: `M_2` is still defined from the Xi divisor.  A
source-side estimate of this scalar, or a source-defined physical realization whose second moment
has this value, is the remaining open core.

## Lean certificate

Formalization:
`formal/GaloisForLFunctions/RHTower/PrimeArchThermalKrylovEquivalence.lean`.

Principal declarations:

- `xiThermalNode_pos`
- `finiteKMSWightmanMomentSequence_xiThermalTruncation`
- `xiThermalSecondMoment_sub_orientationEnergy_eq_source`
- `xiReciprocalSquareHermitianMass_sub_source_eq_two_orientationEnergy`
- `normalizedPrimeArchMoment_one_eq_re_trace_xiReciprocalKernel_four`
- `xiReciprocalKernel_hsNormSq_sub_reTrace_four_eq_two_orientationEnergy`
- `xiReciprocalKernel_reTrace_four_le_hsNormSq`
- `xiReciprocalKernel_hsNormSq_eq_reTrace_four_iff_rh`
- `xiReciprocalKernel_hsNormSq_le_reTrace_four_iff_rh`
- `xiReciprocalSquareKernel_adjointDefect_hsNormSq_eq_reflectionEnergy`
- `xiReciprocalKernel_normTraceGap_eq_half_adjointDefect`
- `xiReciprocalSquareHermitianMass_le_source_iff_rh`
- `tendsto_xiThermalTruncation_positiveMoment`
- `xiThermalPositiveMoment_eq_source_iff_rh`
- `xiThermalOrientationEnergy_eq_weightedGlobalDefect`
- `xiThermalOrientationEnergy_lt_globalReflectionDefectEnergy_iff_not_rh`
- `xiThermalSecondMoment_le_source_iff_rh`
- `tendsto_xiThermalTruncation_one_iff_rh`
- `tendsto_xiThermalTruncation_iff_rh`

The module builds successfully.  `#print axioms` for the principal declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`; no project axiom, proposition interface,
`sorryAx`, or unproved hypothesis occurs.

## Gates

- [x] 0 → 1: exact thermal values and RH consumer identified
- [x] 1 → 2: complete unconditional proof of `(1)`--`(7)`
- [x] 2 → 3: Lean module built and trust surface checked
- [ ] 3 → 4: publication treatment and independent novelty audit
- [ ] RH: prove the source-side reverse inequality `M_2 <= m_source(1)`
