# Cubic height-Bohr fibre and source-translation gate

- **ID:** `cubic-height-bohr-fiber-source-translation-gate`
- **Stage:** `3-formalized`
- **Type:** FINITE BOHR IDENTITY / MULTIPLICITY BOUND / SOURCE-INTERFACE NO-GO
- **Status:** `[LEAN-FORMALIZED] [BRIDGE] [NO ZERO-PROPORTION CLAIM]`
- **Parent:** `../../1-in-progress/zeta23-beyond-bandwidth-one-proportion.md`

## Statement

For a finite packet `z_j=a_j+i gamma_j`, define the genuine holomorphic cubic Laplace kernel

```text
K_(j,k)=2/(a_j+a_k+i(gamma_j-gamma_k))^3
```

and phase trace

```text
E(tau)=sum_(j,k) m_j m_k K_(j,k) exp(-i(gamma_j-gamma_k)tau).
```

Exact character orthogonality gives

```text
BohrMean E
 = sum_(j,k:gamma_j=gamma_k) 2m_jm_k/(a_j+a_k)^3.
```

If `0<a_j<=1/2`, every retained term is nonnegative and every diagonal is at least `2m_j^2`.
Therefore

```text
2 sum_j m_j <= BohrMean E.
```

Combined with `N=N_0+2R`, any arithmetic upper bound `BohrMean E<=N/4` implies
`N_0>=3N/4`.

Ordinary holomorphic translation cannot supply the pure phases source-faithfully.  Its character
at `a+i gamma` has modulus `exp(-tau a)`, whereas the ordinate phase has modulus one.  For
`tau>0`, no scalar independent of `a` normalizes the translation simultaneously at depths one
and two.

The reciprocal Krein repair is also classified exactly.  Common vertical translation leaves the
literal conjugate codiagonal invariant:

```text
(w+i tau)+conj(v+i tau)=w+conj(v).
```

Consequently every observable factoring through the actual von Mangoldt/Krein codiagonal is
constant in `tau`; invariant reciprocal translation cannot yield ordinate Bohr dephasing.
Opposite translation instead gives `w+conj(v)+2i tau`, so it moves the Xi resolvent parameter
rather than phasing a fixed zero fibre.  This is the surviving source-visible vertical-moment
channel, not a proof of the required `N/4` budget.

## Scope

The Bohr computation is finite Fourier orthogonality and the multiplicity bound is diagonal
positivity.  Neither is claimed new.  The result fixes an interface error in the active route:
post-divisor unitary phases cannot be advertised as scalar holomorphic source translation.
Reciprocal FE/Krein translation can cancel the real boost qualitatively, but the required dyadic
prime--Gamma trace and its `N/4` arithmetic bound are not proved.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/XiWardCubicHeightBohrFiber.lean
```

Declarations:

- `holomorphicCubicLaplaceKernel`;
- `norm_holomorphicHeightTranslate`;
- `norm_ordinateUnitaryPhase`;
- `not_exists_scalar_normalizer_holomorphicHeightTranslate`;
- `kreinCommonVerticalShift_codiagonal`;
- `kreinCodiagonalObservable_commonVerticalShift_invariant`;
- `xiGammaEulerPrimitiveJointDepthKreinPair_commonVerticalShift`;
- `kreinOppositeVerticalShift_codiagonal`;
- `xiGammaEulerPrimitiveJointDepthKreinPair_oppositeVerticalShift`;
- `bohrMean_finiteHolomorphicCubicPhaseTrace`;
- `two_mul_sum_multiplicity_le_finiteHolomorphicCubicOrdinateFiberEnergy`;
- `three_quarters_line_of_holomorphicCubicOrdinateFiberEnergy`.

Verification:

- direct module build passes;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for every capstone;
- repository formal lint passes with no forbidden declaration.
