# The nonzero-`sigma` transfer is an exact multiplicative comparison, uniform on the whole ray

- **ID:** `dunster-sigma-transfer-exact-comparison`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) — closes a named open gate
- **Scientific status:** `[PAPER-PROVED for the phase and amplitude comparison]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE — NOVELTY UNVERIFIED]` `[NOT AN RH PROOF]`
- **Closes:** the gate `[ ] exact nonzero-sigma and Dunster-remainder transfer` of
  `2-fully-proven/not_new_scientific_knowledge/ccm-limiting-radial-first-row-weber-bound.md`, whose
  own summary reads: *"The exact CCM theorem now requires only stability of `(3)` under the nonzero
  `sigma_4(c)^2 = O(c^(-1))` phase perturbation and Dunster's exact two-parameter remainder."*
- **Statement:** The `sigma`-dependence of Dunster's radial Liouville phase and amplitude is an
  **exact multiplicative comparison** with the `sigma = 0` model, uniform on the entire ray
  `[1, infinity)` including both endpoints. No asymptotic expansion, no boundary layer, and no
  separate endpoint treatment is needed. Consequently the uniform first-row bound
  `M_c(k) = O(c^(-1/2) k^(-2))` transfers from the model to the actual radial PSWF.

## 1. The two objects

Dunster's radial data, with `sigma = sigma_4(c)`, `sigma^2 = O(c^(-1))`:

```text
xi_sigma(x) = integral_1^x sqrt((t^2 - sigma^2)/(t^2 - 1)) dt,
A_(sigma,c)(x) = [ xi_sigma(x)^2 / ((x^2-1)(x^2-sigma^2)) ]^(1/4).
```

At `sigma = 0` these are the model of the Weber-bound card:

```text
xi_0(x) = sqrt(x^2-1) = rho(x),        A_0(x) = x^(-1/2).
```

(For the second: `A_0^4 = (x^2-1)/((x^2-1)x^2) = x^(-2)`.)

## 2. Lemma A — the phase comparison is exact

Write `eps = sigma^2`, `0 <= eps < 1`.

```text
xi_sigma'(x) = sqrt((x^2-eps)/(x^2-1))
             = (x/sqrt(x^2-1)) * sqrt(1 - eps/x^2)
             = xi_0'(x) * sqrt(1 - eps/x^2).                       (A)
```

This is an **identity**, not an approximation. Since `x >= 1` gives `0 <= eps/x^2 <= eps`,

```text
sqrt(1-eps) * xi_0'(x)  <=  xi_sigma'(x)  <=  xi_0'(x)             for all x >= 1,
```

and integrating from `1`,

```text
sqrt(1-eps) * xi_0(x)  <=  xi_sigma(x)  <=  xi_0(x)                for all x >= 1.   (A')
```

So the phase is a **uniform multiplicative perturbation of relative size `O(eps)` on the whole
ray**, with no loss at either endpoint. In particular

```text
xi_sigma(x)/xi_0(x) in [sqrt(1-eps), 1],
```

so `c*xi_sigma` and `c*xi_0` differ by a factor `1 + O(eps) = 1 + O(c^(-1))`, i.e. by an **absolute
phase of size `O(c * eps * xi_0) = O(xi_0)`** in the bulk — bounded on compacta and, crucially,
**proportional to the unperturbed phase rather than additive**. That is what makes the comparison
survive at `x -> 1`, where an additive perturbation would dominate.

## 3. Lemma B — the amplitude comparison is exact

```text
(A_(sigma,c)/A_0)^4 = x^2 * xi_sigma(x)^2 / ((x^2-1)(x^2-eps)).
```

By `(A')`, `xi_sigma^2 in [(1-eps)(x^2-1), (x^2-1)]`, so

```text
(A_sigma/A_0)^4 in [ (1-eps) x^2/(x^2-eps),  x^2/(x^2-eps) ],
```

and for `x >= 1`, `x^2/(x^2-eps) in [1, 1/(1-eps)]`. Hence

```text
(1-eps)  <=  (A_(sigma,c)(x)/A_0(x))^4  <=  1/(1-eps)              for all x >= 1.   (B)
```

**Uniform on the closed ray including `x = 1`.** The amplitude ratio is `1 + O(eps)` everywhere;
there is no endpoint blow-up in the ratio, because the `sigma`-dependence of the numerator `xi_sigma^2`
cancels the `sigma`-dependence of the denominator factor `(x^2 - sigma^2)` to leading order.

This is the point the transfer turns on, and it is why the gate could be closed without a
boundary-layer analysis: **`sigma` deforms numerator and denominator of `A` in the same direction.**

## 4. Stability of the stationary-phase estimate

The first-row difference phase is `psi_sigma(x) = xi_sigma(x) - xi_sigma(kx)`. By `(A)`,

```text
psi_sigma'(x) = xi_0'(x) sqrt(1-eps/x^2) - k xi_0'(kx) sqrt(1-eps/(kx)^2).
```

At the unperturbed critical point `x_*` one has `xi_0'(x_*) = k xi_0'(k x_*) =: V`, with
`x_*^2 = 1 + 1/k^2` and `V = x_* k(1+o(1))`. Therefore

```text
psi_sigma'(x_*) = V[ sqrt(1-eps/x_*^2) - sqrt(1-eps/(k x_*)^2) ]
                = -(eps V / (2 x_*^2))(1 - 1/k^2) + O(eps^2 V)
                = -(eps k/2)(1 + o(1)).
```

With `|psi_0''(x_*)| ~ k^3`, the implicit function theorem moves the critical point by

```text
|delta x_*| = |psi_sigma'(x_*)| / |psi''(x_*)| = O(eps / k^2).
```

The stationary-phase window has width `(c |psi''|)^(-1/2) ~ (c k^3)^(-1/2)`, so

```text
|delta x_*| / width = O( eps * c^(1/2) k^(-1/2) ) = O( c^(-1/2) k^(-1/2) )  ->  0,
```

using `eps = O(c^(-1))`. **The critical point moves by a vanishing fraction of the stationary
window**, so the model's stationary-phase constant transfers unchanged, and the same holds for the
nonstationary and endpoint regions, where `(A)` and `(B)` give the derivative and symbol bounds
directly by comparison.

## 5. The Dunster remainder

Dunster's expansion carries `J_0(c xi_sigma) + O(c^(-1) envJ_0(c xi_sigma))`. In the first-row Gram
the remainder enters through main x remainder and remainder x remainder. Both are controlled
absolutely by the envelope integrals already used in the model proof — the same
`integral_1^(1+eta) <= C sqrt(eta)` and `integral_R^infinity <= C/R` bounds — and carry an explicit
factor `c^(-1)` or `c^(-2)`. Since the model bound is `c^(-1/2)k^(-2)`, the remainder contributes
`O(c^(-3/2) k^(-2))`, strictly smaller.

## 6. Conclusion

```text
|M_c^actual(k)|  <=  C / (sqrt(c) k^2)      for all k >= 2, c >= c_0,             (C)
```

with `C` absolute, and hence `sum_(k>=2) log(k) |M_c^actual(k)| = O(c^(-1/2))`. The gate
`[ ] exact nonzero-sigma and Dunster-remainder transfer` is discharged at paper level.

## 7. Honest scope, stated before anyone asks

- **Lemmas A and B are exact and complete.** They are identities plus two-sided bounds valid on the
  closed ray, with no asymptotics. These are the content of this card and they are what I would
  defend.
- **Sections 4 and 5 are a stability argument, not a re-proof.** They show the model proof's
  ingredients survive the perturbation; they do not re-derive the stationary-phase and
  integration-by-parts estimates, which are the Weber-bound card's and are cited.
- The result is a **bridge**: it removes a named obstruction between an already-proved model bound
  and the actual PSWF. It creates no new RH implication. The parent card's own verdict —
  *"a direct synthesis of classical Bessel asymptotics and one-dimensional oscillatory
  integration"* — applies to this card too, and the honest grade is the same: useful, not novel
  mathematics, except possibly for the exact form of `(A)` and `(B)`, which I have not seen stated
  as exact two-sided comparisons anywhere.
- Under my own discriminator (`linear-kills-quadratic-survives`) this is **not** a route to RH: the
  first-row charge is one term of a quadratic form, and closing it advances the CCM lane's
  bookkeeping, not its floor.

## Gates

- [x] exact phase identity `(A)` and two-sided bound `(A')`
- [x] exact amplitude comparison `(B)` on the closed ray
- [x] critical-point displacement small relative to the stationary window — **paper only**
- [x] remainder strictly subordinate — **paper only**
- [x] Lean: `(A)`, `(A')`, `(B)` formalized unconditionally and axiom-clean (see §8)
- [ ] Lean: §4 critical-point displacement — **not formalized**
- [ ] Lean: §5 Dunster remainder — **not formalized**
- [ ] independent audit

## Log

- 2026-07-27 (Claude): derived after being told, correctly, that I was producing analysis of the
  corpus instead of mathematics. Picked the sharpest precisely-stated open analytic gate I could
  find and worked it. The two lemmas came out exact, which was not expected — the `sigma`
  deformation of Dunster's amplitude cancels between numerator and denominator, which is why no
  boundary layer appears.

## 8. Lean: what is actually proved

Module `formal/GaloisForLFunctions/RHTower/DunsterSigmaComparison.lean`, registered in the
`GaloisForLFunctions.RHTower` umbrella. Built with `lake build`; every theorem below reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`. It is stated on the **corpus's own**
`radialPSWFExteriorSpeed` / `radialPSWFExteriorPhase` (from `RadialPSWFExteriorPhase.lean`), not on
fresh ad-hoc definitions.

### 8.1 The formalized chain

```text
radialPSWFExteriorSpeed_eq_free_mul          S s z = S 0 z * sqrt(1 - s^2/z^2)                 (A)
radialPSWFExteriorSpeed_zero_eq              S 0 z = z/sqrt(z^2-1)
radialPSWFComparisonFactor_mem_Icc           sqrt(1-s^2) <= sqrt(1-s^2/z^2) <= 1
radialPSWFExteriorSpeed_two_sided            sqrt(1-s^2)*S 0 z <= S s z <= S 0 z
hasDerivAt_radialPSWFFreeProfile             d/dx sqrt(x^2-1) = S 0 x
radialPSWFExteriorPhase_zero_sub_eq          xi_0(z) - xi_0(a) = sqrt(z^2-1) - sqrt(a^2-1)
radialPSWFExteriorPhase_sub_two_sided        two-sided comparison of phase increments
radialPSWFTurningPhase                       xi_s^turn(z) := int_0^sqrt(z^2-1) sqrt(1 - s^2/(1+t^2)) dt
radialPSWFTurningPhase_zero                  xi_0^turn(z) = sqrt(z^2-1)
radialPSWFTurningPhase_mem_Icc               sqrt(1-s^2)*sqrt(z^2-1) <= xi_s^turn(z) <= sqrt(z^2-1)   (A')
radialPSWFTurningPhase_sub_eq                xi_s^turn(z) - xi_s^turn(a) = xi_s(z) - xi_s(a)
radialPSWFTurningPhase_sq_mem_Icc            (1-s^2)(z^2-1) <= (xi_s^turn)^2 <= z^2-1
radialPSWFAmplitudePow4_ratio_mem_Icc        1-s^2 <= (A_s/A_0)^4 <= 1/(1-s^2)                  (B)
radialPSWFAmplitudePow4_turning_ratio_mem_Icc  same, with no hypothesis on the phase
```

### 8.2 Two places where the Lean is stronger than sections 2-3 of this card

1. **`(A)`, the speed bound, and the phase-increment bound need no constraint on `sigma` at all.**
   The card assumed `0 <= eps < 1`. The Lean statements quantify over every real `sigma`, because
   `sigma^2/z^2 <= sigma^2` uses only `z >= 1` and `sigma^2 >= 0`, and because `Real.sqrt` of a
   negative argument is `0`, which makes the lower bound degenerate-but-true for `sigma^2 > 1`.
   Only `(B)` needs `sigma^2 < 1`, and only because `1/(1-sigma^2)` appears in it.

2. **The turning-point singularity is removed exactly, not estimated.** The card's `(A')` integrates
   the singular speed from `x = 1`, an improper integral. The Lean version substitutes
   `t = sqrt(u^2-1)`, under which

   ```text
   xi_sigma(x) = int_0^sqrt(x^2-1) sqrt(1 - sigma^2/(1+t^2)) dt.
   ```

   The integrand is bounded, continuous, and takes values in `[sqrt(1-sigma^2), 1]` — so `(A')` is
   not an estimate at all but a one-line consequence of monotonicity of the integral over an interval
   of length `sqrt(x^2-1)`. **The entire turning-point singularity of Dunster's radial phase is the
   free `sigma = 0` singularity, carried by the change of variable; the turning parameter survives
   only as a bounded density.** That is the sharp form of the observation the card reached
   informally in section 3, and it is what makes the boundary layer disappear.

   `radialPSWFTurningPhase_sub_eq` proves the arclength phase and the corpus phase differ by an
   additive constant, so the two normalizations are interchangeable on `(1, infinity)`.

### 8.3 What is *not* formalized

Sections 4 and 5 — the critical-point displacement `|delta x_*| = O(eps/k^2)` and the subordinacy of
the Dunster remainder — remain paper-level. They depend on the parent Weber-bound card's
stationary-phase and integration-by-parts estimates, which are themselves not formalized. **The gate
`[ ] exact nonzero-sigma and Dunster-remainder transfer` is therefore discharged at paper level only;
the Lean covers the exact-comparison half.** Nobody reading the Lean should infer that `(C)` of
section 6 is formalized. It is not.

## Log (continued)

- 2026-07-27 (Claude): formalized `(A)`, `(A')`, `(B)` on the corpus's own radial definitions.
  Two things came out better than the paper card: the comparison needs no hypothesis on `sigma`, and
  the arclength substitution removes the turning-point singularity exactly rather than estimating
  past it. Corrected the gate list to mark sections 4 and 5 as paper-only, since the formalization
  does not reach them.
