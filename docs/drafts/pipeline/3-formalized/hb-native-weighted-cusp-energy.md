# HB: source-derived weighted admission of native cusp derivative energy

- **ID:** HB-QNCE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticNativeCuspEnergy.lean`
- **Parent:** [HB-QNCD](hb-native-nonconstant-cusp-decay.md)
- **Route:** HB; literal theta cusp → Xi occurrence → retained spin two → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH
- **Active integration:** [source/contact/spin-two balance](../1-in-progress/hb-source-contact-spin-two-balance.md)

## Mathematical obstacle and scope

The previous leaf proves rapid decay of the complete nonconstant native cusp
mass U_b(y). Cusp currents also contain products involving native response
derivatives. Mass decay alone does not admit these derivative products or
supply their upper traces. This leaf attacks derivative admission directly
from the original forced modal equation. Both native branches are retained.
It does not assert complete nonlinear radiative extinction.

Write c_n for the original native response mode, u_n=|c_n|², f_n for the
complete original cusp-subtracted forcing mode, L_n=(2πn)² and
W_n=Re(f_n conj(c_n))/y². The source equations give the exact identity

```
u_n'' = 2|c_n'|² + 2(L_n + Re(α_b)/y²)u_n + 2W_n.
```

Above the already source-derived coercivity height, n≠0,

```
E_n - g_n ≤ u_n'',
E_n = 2|c_n'|² + L_n u_n,   g_n = |f_n|²/y⁴.
```

Neither the signed work nor the changing y^-2 metric term is removed from
the exact identity. The coercive estimate bounds their adverse contribution
by the complete original forcing loss.

## Conjecture, proof, and improvement

**First multiplier.** For any real polynomial P, w=P², the exact finite-height
source identity is

```
∫_a^b w u_n'' = [w u_n' - w' u_n]_a^b + ∫_a^b w'' u_n.
```

Both endpoint terms are retained. Estimating w'' is possible but introduces
unnecessary second-cutoff-derivative bookkeeping.

**Sharper multiplier.** The nonnegative square |P c_n' + 2P' c_n|² absorbs
the mixed term in (P² u_n')'. Together with L_n u_n≥0 it yields

```
∫_a^b P² E_n
≤ 2[P² u_n']_a^b + 8∫_a^b (P')²u_n + 2∫_a^b P²g_n.
```

This uses only the first derivative of P. It is an estimate for the original
response, not a definition of a new physical action or a modified clock.

**Auxiliary cutoff.** Take

```
P_B(y)=y^(N+1)(y-A)(1-y/B),   A≤y≤B.
```

P_B(A)=P_B(B)=0, so its auxiliary flux vanishes at both finite endpoints
without any assumption about c_n or c_n'. On [A,B],

```
0≤P_B(y)≤y^(N+2),
|P_B'(y)|≤(N+3)y^(N+1).
```

The upper height B does not appear in these bounds. For A+1≤y≤T and B=2T,

```
y^(2(N+1)) ≤ 4P_(2T)(y)².
```

Thus a uniform bound for cutoff energy yields a uniform bound on every
interior interval [A+1,T]. Applying the improper-integral criterion directly
avoids a separate cutoff limit and a separate Fatou argument in height.

## Complete forcing and finite-index passage

Parseval for the literal forcing, with period one shifted to its original
cusp cell [-1/2,1/2], gives

```
Σ_n g_n(y) = forcingMass_b(y)
          = y^-4 ∫_(-1/2)^(1/2) |globalForcing_b(x+iy)|² dx.
```

Literal theta square-remainder bounds give, for every N,

```
y^(2N+4) forcingMass_b(y) ≤ C_N,  y>3.
```

No uniform single-frequency constant is summed over infinitely many modes.
Together with the proved rapid U_b decay, choose A≥4 above coercivity height
so that

```
y^(2(N+1)+2) U_b(y) ≤ 1,
y^(2(N+2)+2) forcingMass_b(y) ≤ C,   y≥A.
```

For every finite nonzero frequency set E, positivity and complete Parseval
bound both finite source sums. The square multiplier therefore gives

```
∫_A^B P_B² Σ_(n∈E) E_n ≤ (8(N+3)²+2C)/A.
```

The constant is independent of E and B. Interior comparison and the
improper-integral criterion admit every finite weighted energy sum with a
single bound. Consequently the nonnegative modal energy integrals form a
summable series. Tonelli bounds the integral of the complete sum and admits

```
∫_(A+1)^∞ y^(2(N+1)) Σ_(n≠0) E_n(y) dy < ∞.
```

Independent Parseval for the original horizontal and vertical derivatives
identifies the modal sum with the literal gradient slice and restores its
native zero-mode derivative exactly. This avoids treating a totalized,
potentially nonsummable series as a physical energy.

## Remaining interface

This derivative admission supplies the positive source estimate needed for
weighted Cauchy–Schwarz on nonconstant response/derivative products. An upper
current trace still requires control of its derivative or another trace
estimate. Native zero-mode products and the signed tested source work remain.
The scalar/vector and vector/vector terms, retained spin-two terms and
physical horizon, characteristic and contact contributions must also enter
the complete left-QNM action before any extinction claim is possible.
The common Hawking clock has not been changed. RH remains unproved.

## Search and proof engineering

Cached deep corpus search for uniform finite weighted energy bounds returned
partial coverage (source retrieval interrupted; semantic coverage unmeasured).
Candidate, method/source and ingredient views were inspected. The different
native time-primitive cutoff theorem does not identify this original angular
response. Finite-measure uniform-integrability and exponential clock examples
also do not supply the required cusp estimate. The applicable direct tools
are the finite interval FTC, nonnegative finite sums, improper-integral
boundedness and Tonelli, verified against this installed mathlib.

Broad recent-paper searches included multiplier, exhaustion and observability.
[Si, July 2026](https://arxiv.org/html/2607.29323v1) bounds wave energy by
boundary observations plus forcing, under geometric and time conditions.
It does not establish vanishing of this literal forcing or those observations.
[Liu–Xiang, July 2026](https://arxiv.org/abs/2607.17177) concerns weak
observability and approximate null controllability for linear SPDE/control
systems; no applicable fixed-clock source cancellation follows from its abstract.

Lean uses typed finite identities and explicit normalization of function sums,
interval integrals and polynomial evaluations. No heartbeat, recursion or
transparency override is introduced. No numerical mathematical experiment is used.

## Checked Lean interface

The assembled scratch passed with no diagnostics at default limits. Its public
source interface consists of eight definitions and ten theorems:

- `multiplierBoundary_hasDerivAt`, `nativeMode_multiplier_identity`: exact signed finite identity.
- `nativeMode_firstWeight_coercivity`: square absorption with finite endpoint flux.
- `forcingLoss_hasSum`, `forcingMass_weighted_bound`: complete literal forcing control.
- `nativeFiniteEnergy_admission`: one bound uniform in all finite nonzero mode sets.
- `nativeNonconstantEnergy_admission`: complete weighted energy integrability and summable modal integrals.
- `modeEnergy_hasSum`, `nativeGradientSlice_decomposition`: independent literal gradient Parseval and retained zero mode.
- `nativeGradientRemainder_admission`: the admitted quantity is the actual native gradient remainder.

Assembled source SHA256: `bc4fbd314c92c817eeeb7d6cfee618e714fa90029e5903485bdd7da02df7e975`.

## Next source-current conjecture

Subtracting the exact native zero-mode current should leave a nonconstant
cusp-current remainder with polynomially weighted L1 control of both itself
and its derivative. The new derivative admission and the previous mass decay
supply Cauchy–Schwarz bounds for the native-native products. The exact source
divergence must supply the derivative bound, retaining signed forcing,
source/test derivatives and changing weights. L1 control of the function
and its derivative would then force its upper trace to zero.

The derivative/trace step is now formalized in the
[native cusp-current trace](hb-native-cusp-current-trace.md): both weighted
integrabilities are derived from the original source, and the upper native
remainder trace is zero. The retained zero-mode current and other physical
faces must still be evaluated.

## Exact leaf verification

The assembled scratch and exact isolated `lake build
GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticNativeCuspEnergy` passed.
The exact leaf build took 38 seconds with cached dependencies and unchanged
source SHA256. Its artifacts were published and its temporary audit directory
removed. One umbrella import was added; no umbrella or full build was run.
No owned Lean process remains from these checks. Global lint is recorded
separately; the leaf result does not assert a clean shared tree.

Final shared-tree verification: index refreshed six changed files; all eighteen
new API rows and the single umbrella import were verified. The source hash
remained unchanged. `scripts/formal_tools.py lint --check-generated` exited 1
with the sole error:

```
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries
```

This is a different shared-tree module; no unrelated unfinished source was
modified. Global lint success is not claimed. All owned Lean, search, index
and lint processes have completed.
