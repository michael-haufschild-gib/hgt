# Burnol evaluator nonvanishing via the divided-shift geometric contradiction

- **ID:** `burnol-evaluator-nonvanishing-divided-shift`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[PROVED HERE] [FORMALIZED] [NOT AN RH PROOF]`
- **Serves:** the single load-bearing open gate of
  `burnol-bilateral-aperture-defect-energy-law.md`
  `(13)`/`(14)`→`(15)`,
  `burnol-copoisson-berezin-diagonal-reflection-law.md` `(12)`/`(13)`,
  `burnol-copoisson-quotient-bilateral-order-rh-law.md` `(8)`, the theorem,
  and the two open Lean gates of
  `burnol-sonin-off-axis-aperture-type-rigidity.md`.

## Statement

Let `L_a` be Burnol's extended cosine-Sonine space at aperture `a`, `k_{w,a}` the completed-Mellin
Riesz evaluation vector, and `0 < a <= 1`.  Then for every `w` with `1/2 < Re w < 1`,

```text
k_{w,a} /= 0.                                            (N)
```

The corpus already proved `(N)` when `zeta(w) /= 0` (the co-Poisson inhabitant is a witness).  The
content here is the remaining case `zeta(w) = 0`, where every co-Poisson source is annihilated and
the witness must come from the orthogonal complement.

## Proof

Write `sigma = Re w`, `M = 1/(sigma - 1/2)`, and `F(t) = f(t)` for the coefficient function of a
vector of `L_a`.  Define two operators on `L²(0,infinity)` by

```text
(A_w f)(t) = integral_1^infinity u^(-w) f(ut) du,
(C_w f)(t) = integral_0^1     u^(w-1) f(ut) du.         (1)
```

In terms of the normalized dilation group `D_u f = sqrt u f(u .)` these are the Bochner integrals

```text
A_w = integral_1^infinity u^(-w-1/2) D_u du,
C_w = integral_0^1       u^(w-3/2)  D_u du,             (2)
```

so both are bounded with

```text
||A_w|| <= 1/(sigma-1/2),   ||C_w|| <= 1/(sigma-1/2).   (3)
```

Because `F_+ D_u F_+ = D_{1/u}` and the substitution `u -> 1/u` carries `u^(-w-1/2) du` to
`v^(w-3/2) dv`, the cosine transform exchanges them:

```text
F_+ A_w = C_w F_+.                                       (4)
```

**Head laws.**  If `f` is constant `= c` on `(0,a)` then for `0 < t < a`

```text
(C_w f)(t) = c/w,                                        (5)
(A_w f)(t) = -c/(1-w) + t^(w-1) * integral_0^infinity f(s) s^(-w) ds.   (6)
```

`(5)` is unconditional; `(6)` is constant exactly when the *uncompleted* Mellin value of `f` at `w`
vanishes.  Since the completion factor `pi^(-w/2) Gamma(w/2)` is nonzero on `Re w > 0`, that is
exactly `<k_{w,a}, f> = 0`.

**Consequence.**  If `k_{w,a} = 0`, then every `f in L_a` has vanishing evaluation, so by `(4)`,
`(5)`, `(6)` the space `L_a` is *invariant* under `A_w`.

**Mellin multiplier.**  For `1/2 < Re v < sigma` and `f in L_a`,

```text
integral_0^infinity (A_w f)(t) t^(-v) dt
  = (1/(w-v)) integral_0^infinity f(t) t^(-v) dt,        (7)
```

by Fubini; the double integral converges absolutely exactly because `Re v < sigma`.

**Geometric contradiction.**  Assume `k_{w,a} = 0`.  Pick `epsilon in (0, sigma-1/2)` with
`zeta(w-epsilon) /= 0` (possible: the zeros of `zeta` are isolated) and set `v = w - epsilon`.  Let
`f_0 in L_a` be the explicit co-Poisson inhabitant, whose completed Mellin value at `v` is nonzero.
Put `h_k = A_w^k f_0`.  By the invariance above `h_k in L_a` for every `k`, and

```text
||h_k|| <= M^k ||f_0||,    M(h_k)(v) = M(f_0)(v)/epsilon^k.   (8)
```

The aperture bound makes `|M(h)(v)| <= C(v,a) ||h||` on `L_a`, so

```text
|M(f_0)(v)| <= C(v,a) ||f_0|| (M epsilon)^k  ->  0,      (9)
```

because `M epsilon < 1`.  Hence `M(f_0)(v) = 0`, contradicting the choice of `epsilon`.  Therefore
`k_{w,a} /= 0`.  `QED`

## Why this is new

Every co-Poisson Mellin transform carries the factor `zeta(w)`, so no co-Poisson vector can witness
`(N)` at a zero; the corpus recorded this as the honest boundary of its construction.  The divided
shift is exactly the missing operator: it divides the Mellin transform by `(w - .)` *inside* the
Sonine space, and the head laws `(5)`,`(6)` show that the only obstruction to staying in `L_a` is
the very evaluation being assumed to vanish.  The contradiction is then purely metric: the operator
norm is the reciprocal distance to the critical line, while the multiplier blows up at `w`.

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/SoninDilationContinuity.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninDividedShift.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationNonvanishing.lean
```

All three are wired into `GaloisForLFunctions.RHTower`.

## Gates

- [x] strong continuity of the normalized dilation group on `L²(R)`
- [x] the two divided-shift operators, their integrability and norm bounds `(2)`,`(3)`
- [x] the cosine exchange `(4)`
- [x] pointwise a.e. formula for `A_w`
- [x] head laws `(5)`,`(6)`
- [x] extended-Sonine invariance under the assumption `k_{w,a} = 0`
- [x] Mellin multiplier `(7)`
- [x] geometric contradiction `(8)`,`(9)` and `(N)`

## Formal theorem chain

```text
1  tendsto_norm_rayDilate_sub_self, continuousOn_rayDilate
     the normalized dilation group is strongly continuous on L²(R)
2  burnolShift, burnolCoShift, norm_burnolShift_le, norm_burnolCoShift_le
     the two divided shifts, each of norm at most 1/(Re w - 1/2)                    (2),(3)
3  soninCosineUnitary_burnolShift
     the cosine transform exchanges them                                            (4)
4  coe_burnolShift_ae, coe_burnolCoShift_ae
     both are the pointwise divided-shift integrals almost everywhere
5  burnolCoShiftFun_head_eq, burnolShiftFun_head_eq
     the two head laws                                                              (5),(6)
6  burnolShift_mem_soninExtendedSpace
     the extended Sonine space is invariant under A_w at an annihilated point
7  integral_burnolShiftFun_mellinKernel
     the Mellin multiplier 1/(w - v)                                                (7)
8  eventually_riemannZeta_ne_zero_nhdsNE
     the zeros of zeta are isolated in the critical strip
9  burnolExtendedSoninEvaluationVector_ne_zero
     k_{w,a} /= 0 for every 1/2 < Re w < 1 and every 0 < a < 1                       (N)
10 exists_soninExtendedSpace_mellin_ne_zero
     equivalently, the completed Mellin evaluation is a nonzero functional on L_a
```

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/SoninDilationContinuity.lean          -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolSoninDividedShift.lean          -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolSoninEvaluationNonvanishing.lean -- clean
lake build GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing        -- success
#print axioms burnolExtendedSoninEvaluationVector_ne_zero
  -> [propext, Classical.choice, Quot.sound]
#print axioms exists_soninExtendedSpace_mellin_ne_zero
  -> [propext, Classical.choice, Quot.sound]
```

## Consumers

The nonvanishing discharges the load-bearing premise of four Burnol cards; the resulting
unconditional RH interfaces are collected in
`formal/GaloisForLFunctions/RHTower/BurnolBilateralApertureRH.lean`.
