# The archimedean Weil weight is a Dirichlet energy, and its sign changes at one explicit point

- **ID:** `ARCH-WEIL-KERNEL-SIGN-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / ELEMENTARY ROUTE TO RESTRICTED WEIL POSITIVITY
- **Parent:** `functional-equation-is-blind-to-rh.md` §3 (the one lane the firewall still endorses)
- **RH used:** no · **Computation used:** no
- **Lean status:** unconditional and closed — no hypotheses, no added axioms

## 1. The recasting

Weil's archimedean distribution and the pole term, written in the autocorrelation variable for an
even correlation `g` supported in `[-S, S]`:

```
poleTerm(g)   = 2 ∫_{-S}^{S} g(u) cosh(u/2) du,
archTerm(g)   = (-γ - log π) g(0) + 2 ∫_0^∞ ( g(0) e^{-2u} - g(u) e^{-u/2} ) / (1 - e^{-2u}) du.
```

Both are classical (Weil, Barner); the second follows from
`ψ(z) = -γ + ∫_0^∞ (e^{-t} - e^{-zt})/(1 - e^{-t}) dt` at `z = 1/4 + ir/2` after the substitution
`t = 2u` and Parseval.  Substituting `g(u) = g(0) - D(u)`, `D(u) := g(0) - g(u)`, and splitting the
`u`-integral at `S` gives the exact identity

```
   poleTerm(g) + archTerm(g)  =  C(S)·g(0)  +  ∫_0^S D(u)·K(u) du,
   C(S) = -γ - log π - log(1 - e^{-2S}) - J(S) + 8 sinh(S/2),
   J(S) = 2 ∫_0^S (e^{-u/2} - e^{-2u})/(1 - e^{-2u}) du,
   K(u) = 2 e^{-u/2}/(1 - e^{-2u}) - 4 cosh(u/2).
```

For `g = f ⋆ f̃` one has `D(u) = ‖f - T_u f‖²/2 ≥ 0`, so **the archimedean part of the Weil form is a
multiple of `‖f‖²` plus a weighted Dirichlet energy.**  This is the recasting; everything below is
about the two elementary objects `C` and `K` it produces.

## 2. The kernel's sign, exactly

**Theorem (identity).**  For `u > 0`,

```
   K(u) · ( e^{-u/2} (1 - e^{-2u}) / 2 )  =  e^{-3u} + e^{-2u} - 1.
```

Multiplying by that positive factor clears both denominators; with `E = e^{-u/2}` the left side is
`E² - (1 + E²)(1 - E⁴)`, which is `E⁶ + E⁴ - 1`.

**Corollary (sign criterion).**  `K(u) > 0  ⟺  e^{-3u} + e^{-2u} > 1`.

**Theorem (threshold).**  `u ↦ e^{-3u} + e^{-2u}` is strictly decreasing on `[0,∞)`, equals `2` at
`0`, and is `< 1` at `u = 1` (since `e ≥ 2` gives `e^{-2} ≤ 1/4`, `e^{-3} ≤ 1/8`).  So there is a
**unique `u₀ > 0` with `e^{-3u₀} + e^{-2u₀} = 1`**, and

```
   K > 0 on (0, u₀),        K < 0 on (u₀, ∞).
```

The archimedean Weil weight therefore changes sign exactly once on the positive axis, at the root of
`e^{-3u} + e^{-2u} = 1`.  On every aperture `S ≤ u₀` the Dirichlet-energy term is unconditionally
nonnegative.

## 3. The constant

`J` is pinned: the integrand `(e^{-u/2} - e^{-2u})/(1 - e^{-2u})` lies in `[0, 3/4]`, the upper bound
being the algebraic inequality `y⁴ - 4y + 3 = (y-1)²(y² + 2y + 3) ≥ 0` at `y = e^{-u/2}` (attained in
the limit `u → 0`).  Hence `0 ≤ J(S) ≤ (3/2) S`.  With `1 - e^{-2S} ≤ 2S` and `sinh(S/2) ≥ 0`,

```
   C(S)  ≥  log(1/(2S)) - γ - log π - (3/2) S,
```

which is strictly positive below the explicit aperture

```
   S  <  1 / ( 2 π e^{γ + 3/4} ).
```

**Theorem.** `0 < S < 1/(2π e^{γ+3/4})  ⟹  C(S) > 0`.

## 4. What this gives

On any aperture below `min(u₀, 1/(2π e^{γ+3/4}))` both terms of §1 are nonnegative, so the
archimedean part of the Weil form is nonnegative there — by an argument using nothing beyond
`log v ≤ v - 1`, `e ≥ 2`, and a quartic factorisation.  Yoshida (1992) and Bombieri (2000) obtain
small-support positivity non-explicitly; Connes–Consani (2021) obtain the archimedean place through
prolate spheroidal analysis and Toeplitz operators.  The route here is elementary and gives the
aperture explicitly.

Honest scope.  The identification of `poleTerm + archTerm` with the archimedean part of the Weil
functional is classical and is **not** formalized — the Lean development defines `K`, `J`, `C` as
explicit elementary functions and proves theorems about them, unconditionally and with no
hypotheses.  The threshold obtained is well below `log 2`, so no prime power enters; pushing the
aperture across the first prime is not addressed here and remains the open problem of the lane.

## 5. Lean

| result | theorem | module |
|---|---|---|
| kernel sign identity | `weilKernel_mul_pos_eq` | `RHTower/ArchimedeanWeilKernelSign` |
| sign criterion | `weilKernel_pos_iff` | same |
| unique threshold `u₀` | `exists_unique_weilKernelThreshold` | same |
| two-sided sign law | `weilKernel_pos_of_lt_threshold`, `weilKernel_neg_of_threshold_lt` | same |
| deficit integrand in `[0, 3/4]` | `kernelDeficit_nonneg`, `kernelDeficit_le` | `RHTower/ArchimedeanWeilApertureConstant` |
| `0 ≤ J(S) ≤ (3/2)S` | `deficitIntegral_nonneg`, `deficitIntegral_le` | same |
| **aperture constant positive below the threshold** | `apertureConstant_pos` | same |

Both modules wired into `GaloisForLFunctions.RHTower`; `lake build` green; every theorem audits to
`[propext, Classical.choice, Quot.sound]`.

## 6. Novelty (bounded audit)

Checked: Weil's and Barner's forms of the archimedean term; Yoshida (1992); Bombieri, *Remarks on
Weil's quadratic functional* (Rend. Lincei 2000); Connes–Consani, *Weil positivity and trace formula,
the archimedean place* (Selecta 2021); Connes–Consani–Moscovici (2024–25); Suzuki, *Weil's quadratic
form via the screw function* (`arXiv:2606.09096`); Groskin (`arXiv:2607.02828`).  The `x`-space form
of the archimedean term is classical and is used as input, not claimed.  What the checked sources do
not contain is the recasting of §1 as *constant plus weighted Dirichlet energy*, the exact sign
criterion `e^{-3u} + e^{-2u} > 1`, or the identification of the weight's unique sign-change point;
these carry the elementary positivity route of §4.

---

# Continuation: uniform deficit bound, two-sided window, and the certificate

## 7. The deficit correction is bounded by `4`, at every aperture

The linear bound `J S ≤ (3/2) S` of §3 is wasteful.  In the variable `y = e^{-u/2} ∈ (0,1)` the
deficit integrand is the rational function

```
   (e^{-u/2} - e^{-2u}) / (1 - e^{-2u})  =  (y - y⁴)/(1 - y⁴)  =  y (1 + y + y²) / ((1+y)(1+y²)),
```

which equals `3/4` in the limit `y → 1` and is dominated by `y` itself, since
`y - y⁴ ≤ y(1 - y⁴)` reduces to `y⁵ ≤ y⁴`.  Integrating the dominating exponential,

```
   J S  ≤  2 ∫_0^S e^{-u/2} du  =  4 (1 - e^{-S/2})  ≤  4      for every S ≥ 0.
```

Lean: `kernelDeficit_le_exp`, `deficitIntegral_le_four`.  The rational-in-`y` form is worth
recording on its own: **in the variable `y = e^{-u/2}` both archimedean weights are rational**, the
kernel being `K = 2(y⁶ + y⁴ - 1) / (y(1 - y⁴))`, which re-derives the sign criterion of §2 at sight.

## 8. The aperture constant is positive at both ends

With `J S ≤ 4` uniformly, `-log(1 - e^{-2S}) ≥ 0`, and `8 sinh(S/2)` growing, the constant returns to
positivity at large aperture:

**Theorem.**  `4 ≤ S  ⟹  C(S) > 0`.

The proof uses only `γ < 2/3` (mathlib), `log π < 2` (from `π ≤ 4 < e²`), `J S ≤ 4`, and
`sinh(S/2) ≥ sinh 2 ≥ 15/8` (from `e² ≥ 4`).  Lean: `apertureConstant_pos_of_four_le`.

Combined with §3: `C(S) > 0` for `0 < S < 1/(2π e^{γ+3/4})` **and** for `S ≥ 4`.  Any failure of the
aperture constant is therefore confined to a bounded middle window — the constant is not the obstacle
at large aperture.

## 9. What actually decides the reach: the certificate

Past the sign change `u₀` the Dirichlet term must be *bounded*, not merely signed.  For `g = f ⋆ f̃`,

```
   D u = ‖f - T_u f‖² / 2  ≤  2 ‖f‖²,
```

since `‖T_u f‖ = ‖f‖` gives `‖f - T_u f‖ ≤ 2‖f‖`.  Hence pointwise, for every `u`,

```
   D u · K u  ≥  2 ‖f‖² · min (K u) 0,
```

and therefore

```
   poleTerm + archTerm  ≥  ‖f‖² · Cert(S),     Cert(S) := C(S) + 2 ∫_0^S min (K u) 0 du.
```

Lean: `deficit_mul_kernel_ge`, `half_norm_sub_sq_le`.

**This is the object that decides the reach of the elementary route.**  For `S ≤ u₀` the integral
vanishes and `Cert = C`.  For large `S` the negative mass grows like `-8 sinh(S/2)`, exactly
cancelling the `+8 sinh(S/2)` inside `C`, so `Cert(S) → -∞`: the certificate must fail eventually,
as it must, since a certificate valid at every aperture would prove RH.  The reach is the first zero
of `Cert`, an explicit number determined by `γ`, `π`, and the two elementary integrals.

**Open, and the next target.**  Decide whether that first zero exceeds `log 2`, i.e. whether the
elementary certificate survives the entry of the first prime power.  The crude step is
`D u ≤ 2‖f‖²`, which ignores that `f` is supported in an interval of length `S`: for `u` close to
`S` the translate `T_u f` overlaps `f` only on a set of length `S - u`, so `D u` is much smaller than
its worst case there — precisely where `K` is most negative.  Recovering that support factor is the
identified next step, and it is elementary.

---

# Continuation II: monotonicity of the weight and the support refinement

## 10. The weight is strictly decreasing

**Theorem.** `K` is strictly decreasing on `(0, ∞)`.

Its first term `2 e^{-u/2}/(1 - e^{-2u})` is a decreasing positive numerator over an increasing
positive denominator; its second term `-4 cosh(u/2)` is decreasing.  Lean:
`weilKernel_strictAntiOn`.

Two consequences.  First, this re-proves the uniqueness of the sign change of §2 without the
threshold function.  Second, and this is the useful direction, it gives

```
   u ≥ a > 0   ⟹   K u ≤ K a,
```

Lean: `weilKernel_le_of_le`.  Since `K a < 0` for `a > u₀`, this converts the negative mass of the
kernel into an explicit bound `∫_a^S K ≤ (S - a) K a` for any probe point `a ∈ (u₀, S)` — the
quantity that has to be beaten for the certificate to survive.

## 11. The support refinement

The step `D u ≤ 2 g 0` throws away the support of `f`.  Take `f` supported in `[-S/2, S/2]`.  The
correlation `g u = ∫ f(x) f(x-u) dx` is carried by the overlap of `supp f` and `supp f + u`, so `f`
must have mass in **both**

```
   A(u) = [u - S/2, S/2]        and        B(u) = [-(S/2), S/2 - u],
```

each of length `S - u`.  For `u > S/2` these two windows are **disjoint** (Lean:
`disjoint_overlap_windows`), so with `α² = ‖f‖²_{A}` and `β² = ‖f‖²_{B}`,

```
   α² + β² ≤ ‖f‖² = g 0,       |g u| ≤ α β ≤ (α² + β²)/2 ≤ g 0 / 2,
```

whence

```
   D u = g 0 - g u  ≤  (3/2) g 0        for u > S/2,
```

against the crude `2 g 0`.  Lean: `mul_le_half_of_sq_add_sq_le`, `deficit_le_three_halves`,
`deficit_le_of_disjoint_masses`, and the certificate form `deficit_mul_kernel_ge_refined`.

The gain of a quarter falls exactly on the upper half of the aperture, which is where `K` is most
negative — so it is applied where it is worth the most.  The refined certificate is

```
   Cert₂(S) = C(S) + 2 ∫_0^{S/2} min(K,0) + (3/2) ∫_{S/2}^{S} min(K,0).
```

## 12. Why this is the limit of pointwise bounds

The factor `3/2` cannot be improved by any bound on `D` that depends on `u` alone.  Equality in
`α β ≤ (α² + β²)/2` needs `α = β = ‖f‖/√2`, i.e. `f` splitting its mass evenly between the two
shrinking end-windows — and that configuration is admissible at each fixed `u`, for every `u < S`,
since concentration near an endpoint is not forbidden by membership in `L²`.  For a *fixed* `f` the
masses `α(u), β(u)` do tend to `0` as `u → S`, but not uniformly over `f`, so no uniform pointwise
bound sees it.

**This locates the obstruction precisely.**  Beating `3/2` requires an estimate that uses `f` at
several apertures at once — a genuinely non-pointwise argument.  That is exactly what the prolate
spheroidal analysis of Connes–Consani supplies, and it is why the elementary route has a finite
reach.  The remaining question of the lane is quantitative: whether the first zero of `Cert₂`
exceeds `log 2`, i.e. whether the elementary certificate survives the entry of the first prime power.
By §10 that question is now reduced to comparing two explicit elementary quantities, `C(S)` and
`(3/2)(S - a) K(a)`, with no analysis left in it.
