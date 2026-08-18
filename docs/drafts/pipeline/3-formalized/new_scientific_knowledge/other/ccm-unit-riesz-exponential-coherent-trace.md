# CCM unit-Riesz exponential coherent trace

- **ID:** `ccm-unit-riesz-exponential-coherent-trace`
- **Stage:** 3-formalized
- **Type:** THEOREM / cross-route source identification
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED, UNCONDITIONAL] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CCMUnitRieszExponentialCoherentTrace.lean`
- **Parent:** `ccm-unit-riesz-aperture-resolvent-weld`

## Statement

For `x,s in R`, put

```text
v_x(s)=1_(x<s) exp(-(s-x)/2).
```

These are unit vectors in `L2(R)` and

```text
<v_x,v_y> = exp(-|x-y|/2),
||v_x-v_y||_2^2 = 2(1-exp(-|x-y|/2)).                 (1)
```

For `0<n<=X`, the literal unit-aperture critical prime weight is therefore

```text
w_X(n)=||v_(log X)-v_(log n)||_2^2/sqrt X.           (2)
```

Consequently the finite von-Mangoldt renewal is the positive coherent energy

```text
E_X(K)=1/sqrt X sum_(2<=n<=K) Lambda(n)
          ||v_(log X)-v_(log n)||_2^2.               (3)
```

At an integer aperture `N>=1`, this is not a detached positive lift. Exact layer-cake summation
and linear change of variables give the literal completed-source identity

```text
E_polar(X)=1/sqrt X integral_0^X
  ||v_(log X)-v_(log y)||_2^2 dy=(2/3)sqrt X,         (4)

R_1(log N)=E_N(N)-E_polar(N),                         (5)

R_1(t)=exp(-t) integral_0^(exp t) (psi(y)-y)y^(-1/2)dy.
```

Thus the common CCM-UR / aperture-resolvent arithmetic source is exactly a trace discrepancy:
positive atomic energy minus continuous energy of the same coherent increment frame. No smoothing,
asymptotic, Stieltjes shorthand, zero-location hypothesis, or exponent loss occurs in `(4)`--`(5)`.

## Off-diagonal source geometry

The lift retains more than the scalar trace. For positive lags define

```text
K(u,v)=1-exp(-u/2)-exp(-v/2)+exp(-|u-v|/2).
```

This is the Gram kernel of the actual increments `v_0-v_(-u)`. For `0<u<v`, Lean proves the exact
two-lag determinant

```text
K(u,u)K(v,v)-K(u,v)^2
 =(1-exp(-u/2))(1-exp(-(v-u)/2))
   (3+exp(-(v-u)/2)+exp(-u/2)(1-exp(-(v-u)/2))) > 0. (6)
```

Hence every distinct two-atom source packet is automatically separating. Formula `(6)` also
prices crowding exactly: separation collapses through the factor `1-exp(-(v-u)/2)` as logarithmic
prime lags collide. Positivity is source-native; no generic-vector choice is used.

## Proof spine

1. Direct integration over the common tail `(max(x,y),infinity)` proves `(1)`.
2. Substitute `x=log X`, `y=log n`; monotonicity of `log` and the critical Riesz resonance prove
   `(2)`, then finite summation proves `(3)`.
3. On `0<=v<=1`, prove the exact finite staircase identity

   ```text
   psi(Nv)=sum_(0<=n<=N) 1_(n/N<=v) Lambda(n).
   ```

4. Integrate against `dv/(2sqrt v)`. Each atom has mass `1-sqrt(n/N)`, giving exactly the renewal.
5. Substitute `y=Nv` into the defining Chebyshev half-weight integral. The polar layer has exact
   mass `N/3`; normalization yields `(4)`--`(5)`.
6. Polarize the overlaps in `(1)` to obtain `K`; ordered-lag exponential algebra factors the
   determinant as `(6)`.

## Route consequences

- **CCM-UR / CCM-FU:** exact source weld is strengthened from scalar resolvent equality to a
  canonical positive prime frame plus explicit negative polar trace. Remaining theorem is a bound
  on their difference, not construction of positive prime atoms.
- **CCM-GS:** generic fixed-cutoff separating-vector existence is unnecessary for this source
  frame. Distinct source lags are already strictly separated, with explicit crowding price `(6)`.
  Missing step is an index-preserving comparison from this frame to the true CCM ground state.
- **CCM-HG:** `K` supplies a canonical completed-source positive covariance candidate. Existing
  fast-minus-slow scalar covariance remains indefinite; any HG transfer must use this full source
  frame and prove the boundary-density `<=4` comparison.
- **CCM-EP:** prime frame is positive but `(5)` is a signed prime-minus-polar trace. EP still needs
  operator-valued recombination preserving the polar subtraction through boundary convergence.
- **Route O / Route G:** source-side positivity cannot imply scalar ground positivity. The exact
  missing map is now a quantitative contraction/intertwiner carrying `K` into true restricted-Weil
  ground incidence without losing the crowding factor or the polar trace.

## Hostile novelty and theatre audit

- The exponential covariance kernel, partial summation, and Riesz-type criteria are classical.
- Corpus already contains other coherent prime carriers, Suzuki all-prime fusion, and generic CCM
  separating laws. No claim of inventing coherent states or source separation in general is made.
- Checked Riesz-criterion and Connes--Consani scaling-Hamiltonian literature did not expose the
  exact chain `(2)`--`(6)` for this literal CCM completed current. Absence is not proved; novelty
  remains unverified.
- `(3)` alone would be theatre: any nonnegative scalar sum can be diagonalized. Non-theatrical
  content is the atomic-versus-continuous trace identity for the same frame plus retained
  off-diagonal Gram law.
- This does **not** establish Loewner domination of prime frame by polar continuum, transport to
  actual CCM ground, the required all-epsilon arithmetic bound, or RH.

## Open core exposed

Construct a source-derived operator `T_N` from the coherent increment frame to one true CCM
ground/boundary carrier such that:

```text
T_N preserves the prime-minus-polar trace,
T_N^*T_N has a cofinal lower bound compatible with (6),
and the bound survives prime-log crowding and N -> infinity.
```

Failure of such a comparison must be classified by an exact leverage/crowding obstruction rather
than by another scalar source reformulation.

## Index of the formalization

Module: `RHTower/CCMUnitRieszExponentialCoherentTrace.lean`.  All declarations are unconditional;
`#print axioms` returns only `propext, Classical.choice, Quot.sound`.

| Card item | Lean declaration |
|---|---|
| `(1)` coherent overlaps and distances | `integrable_unitExponentialCoherentState_mul`, `integral_unitExponentialCoherentState_mul`, `unitExponentialCoherentDistanceSq_eq` |
| `(2)` literal prime weight | `unitApertureCriticalPrimeWeight_eq_coherentDistance` |
| `(3)` positive coherent energy | `unitRieszVonMangoldtRenewal_eq_coherentPrimeEnergy` |
| exact staircase identity | `chebyshevPsi_scaled_eq_vonMangoldt_indicator`, `integral_scaledChebyshevPsi_layerWeight` |
| layer-cake normalization | `unitRieszVonMangoldtRenewal_eq_scaledPsiLayerEnergy`, `integral_chebyshevPsi_halfWeight_eq_scaledLayerEnergy` |
| `(4)` continuous polar energy | `unitRieszCoherentPolarEnergy_eq` |
| `(5)` trace discrepancy | `criticalMellinChebyshevResolventSource_log_nat_eq_coherentDefect`, `criticalMellinChebyshevResolventSource_log_nat_eq_coherentPrime_sub_polar` |
| `(6)` two-lag determinant | `unitExponentialIncrementKernel_eq_gram`, `unitExponentialIncrementKernel_twoByTwoDet_eq`, `unitExponentialIncrementKernel_twoByTwoDet_pos` |
