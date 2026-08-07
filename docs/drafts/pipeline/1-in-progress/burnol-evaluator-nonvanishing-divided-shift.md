# Burnol evaluator nonvanishing via the divided-shift geometric contradiction

- **ID:** `burnol-evaluator-nonvanishing-divided-shift`
- **Stage:** 1 — in progress
- **Type:** THEOREM (paper proof complete here), `[FORMALIZATION IN FLIGHT]`
- **Serves:** the single load-bearing open gate of
  `../2-fully-proven/new_scientific_knowledge/burnol/burnol-bilateral-aperture-defect-energy-law.md`
  `(13)`/`(14)`→`(15)`,
  `../2-fully-proven/new_scientific_knowledge/burnol/burnol-copoisson-berezin-diagonal-reflection-law.md` `(12)`/`(13)`,
  `../2-fully-proven/new_scientific_knowledge/burnol/burnol-copoisson-quotient-bilateral-order-rh-law.md` `(8)`, the theorem,
  and the two open Lean gates of
  `../2-fully-proven/new_scientific_knowledge/burnol/burnol-sonin-off-axis-aperture-type-rigidity.md`.

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
formal/GaloisForLFunctions/RHTower/SoninDilationContinuity.lean      -- built, green
formal/GaloisForLFunctions/RHTower/BurnolSoninDividedShift.lean      -- in flight
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationNonvanishing.lean  -- planned
```

## Gates

- [x] strong continuity of the normalized dilation group on `L²(R)` (Lean)
- [x] the two divided-shift operators, their integrability and norm bounds `(2)`,`(3)` (Lean)
- [x] the cosine exchange `(4)` (Lean)
- [x] pointwise a.e. formula for `A_w` (`coe_burnolShift_ae`; product integrability, indicator
      test vectors, Fubini)
- [x] head laws `(5)`,`(6)` (`burnolCoShiftFun_head_eq`, `burnolShiftFun_head_eq`)
- [x] extended-Sonine invariance under the assumption `k_{w,a} = 0`
      (`burnolShift_mem_soninExtendedSpace`)
- [x] Mellin multiplier `(7)` (`integral_burnolShiftFun_mellinKernel`)
- [ ] geometric contradiction `(8)`,`(9)` and `(N)`

## Lean state

`SoninDilationContinuity.lean` and `BurnolSoninDividedShift.lean` both compile clean under
`lake env lean`.  Named endpoints already available:

```text
tendsto_norm_rayDilate_sub_self, continuousOn_rayDilate   -- strong continuity
burnolShift, burnolCoShift, norm_burnolShift_le, norm_burnolCoShift_le
soninCosineUnitary_burnolShift                            -- the cosine exchange (4)
coe_burnolShift_ae, coe_burnolCoShift_ae                  -- pointwise a.e. forms
burnolShiftFun_head_eq, burnolCoShiftFun_head_eq          -- head laws (6), (5)
burnolShift_mem_soninExtendedSpace                        -- invariance
integral_burnolShiftFun_mellinKernel                      -- the multiplier (7)
```

Remaining Lean work, all in one new module `BurnolSoninEvaluationNonvanishing.lean`:

1. assume `k_{w,a} = 0`; `burnolExtendedSoninEvaluationVector_eq_zero_iff` plus
   `mellinCompletionFactor_ne_zero` turn it into `∫ f t^(-w) dt = 0` for every `f in L_a`;
2. iterate `h 0 = coPoissonIndicatorSoninCosine`, `h (k+1) = burnolShift w (h k)`; membership by
   induction from `burnolShift_mem_soninExtendedSpace`;
3. `‖h k‖ ≤ M^k ‖h 0‖` by induction from `norm_burnolShift_le`;
4. `∫ (h k) t^(-v) dt = (∫ (h 0) t^(-v) dt)/(w-v)^k` by induction from
   `integral_burnolShiftFun_mellinKernel` composed with `coe_burnolShift_ae`;
5. pick `v = w - eps` with `eps in (0, Re w - 1/2)` and `zeta v /= 0`; conclude from
   `norm_burnolExtendedSoninEvaluationLinearMap_le` that `|M(h 0)(v)| <= C (M eps)^k -> 0`,
   contradicting `soninMellinEvaluation_coPoissonIndicatorSoninCosine_ne_zero_iff`.

For step 5 the isolated-zero input is already a five-line corpus recipe, used verbatim in
`BoundedClockZeroTransfer.lean` around line 234:

```text
have hnotEventuallyZero : ¬ ∀ᶠ z in 𝓝 w, XiC z = 0 := fun hev =>
  XiC_zero_ne (XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ w) hev (Set.mem_univ 0))
have hpunct : ∀ᶠ z in 𝓝[≠] w, XiC z ≠ 0 :=
  (XiC_analytic w (Set.mem_univ w)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    hnotEventuallyZero
```

then transfer `XiC`/`xi` nonvanishing to `riemannZeta` on the strip with `xi_eq_zero_iff`.

Neither module is wired into `RHTower.lean` yet; wire both once the last two gates close.
