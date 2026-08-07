# Burnol--Hedenmalm archimedean completion domain--radical exchange — formalized

- **ID:** `burnol-hedenmalm-archimedean-completion-domain-radical-exchange-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-hedenmalm-archimedean-completion-domain-radical-exchange.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/FractionalPartZeta.lean
formal/GaloisForLFunctions/RHTower/ZetaCriticalLineNotSquareIntegrable.lean
formal/GaloisForLFunctions/RHTower/BurnolHedenmalmUncompletedDomain.lean
formal/GaloisForLFunctions/RHTower/BurnolHedenmalmCompletionDomain.lean
formal/GaloisForLFunctions/RHTower/XiHedenmalmSymmetricMultiplicity.lean
```

## Formal theorem chain

### Section 1 --- the uncompleted coordinate domain

```text
1  criticalLinePoint, dividedZetaLine                 the line and the divided vector x_rho
2  memLp_riemannZeta_criticalLine_of_dividedZetaLine  the recurrence transport             (3),(5)
3  fractLogCarrier                                    phi y = frac(e^y) e^(-y/2)
4  integrable_fractLogCarrier                         phi is integrable
5  fourier_fractLogCarrier                            Fourier(phi)(xi) = - zeta(w)/w
6  memLp_inv_criticalAbscissa                         1/w is square integrable on the line
7  integrable_fourier_fractLogCarrier                 zeta in L^2 makes Fourier(phi) integrable
8  continuous_fourierInv_of_integrable                so the inverse transform is continuous
9  fractLogCarrier_eq_left, fractLogCarrier_eq_right  the two branches of phi at log 2
10 continuousAt_fractLogCarrier_left / _right         phi is continuous off the points log n
11 not_memLp_riemannZeta_criticalAbscissa             the jump at log 2 forbids zeta in L^2   (4)
12 not_memLp_riemannZeta_criticalLine                 the same in the natural parametrisation (4)
13 not_memLp_coordinate_dividedZetaLine_unconditional the exclusion, with no hypothesis left
```

### Sections 2 and 3 --- completion and radical

```text
14 completedXiFirstDividedFunction, completedXiFirstDividedL2   q_alpha                     (7)
15 memLp_completedXiFirstDividedFunction              q_alpha in L^2(R)                     (8)
16 maximalRealCoordinate, maximalRealCoordinateDomain the maximal domain of M_z
17 maximalRealCoordinate_formalSelfAdjoint            M_z is symmetric there
18 completedXiFirstDividedL2_mem_maximalRealCoordinateDomain    z q_alpha in L^2            (8)
19 maximalRealCoordinate_completedXiFirstDividedL2    M_z q_alpha = alpha q_alpha + XiC     (9)
20 xiThetaFourierSourceL2_ne_zero,
   completedXiFirstDividedL2_ne_zero                 both vectors are nonzero
21 burnolHedenmalm_archimedeanCompletion_domain_radicalExchange  the packaged statement
22 symmetric_xiSourceQuotient_implies_rh_and_simple   the radical endpoint            (10),(11)
```

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/ZetaCriticalLineNotSquareIntegrable.lean  -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolHedenmalmUncompletedDomain.lean     -- clean
lake build GaloisForLFunctions.RHTower.BurnolHedenmalmUncompletedDomain             -- success
#print axioms not_memLp_riemannZeta_criticalLine
  -> [propext, Classical.choice, Quot.sound]
#print axioms not_memLp_coordinate_dividedZetaLine_unconditional
  -> [propext, Classical.choice, Quot.sound]
#print axioms burnolHedenmalm_archimedeanCompletion_domain_radicalExchange
  -> [propext, Classical.choice, Quot.sound]
```

All modules are wired into `GaloisForLFunctions.RHTower`.

## Note on the classical input

The paper card cites the critical-line mean-square asymptotic
`integral_0^T |zeta(1/2+it)|^2 dt = T log T + O(T)` for the exclusion.  The formalization does not
use it.  The divergence needed is weaker and is obtained from the jump of the fractional part: the
logarithmic carrier of the fractional-part Mellin identity has Fourier transform exactly
`- zeta(w)/w`, so square integrability of `zeta` would make that transform integrable, hence the
carrier equal to a continuous function at all its continuity points --- contradicted by its jump at
`log 2`.  This needs no Sobolev theory, no Hardy space and no approximate functional equation.
