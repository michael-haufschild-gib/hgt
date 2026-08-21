# Fractional-part representation of zeta: what survives of arXiv:2201.06601

- **ID:** tegetmeyer-2201-06601
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) + FALSIFIED (source's main claim)
- **Source:** B. Tegetmeyer, *Proof of the Riemann Hypothesis*, arXiv:2201.06601v2 [math.GM]
- **Statement:** The paper's analytic ingredients (integral representation, polar split, closed-form
  primitives, functional-equation multiplier) are true and are now Lean-certified; its central
  partial-integration step and its limit extraction are false, and the exact failures are also
  Lean-certified.

## Goal
Separate the true content of the source from its errors, formalize everything true, and give an
unconditional Lean refutation of each false step, so the route is permanently closed with a
recorded positive residue.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: every surviving statement has a complete proof
- [x] 2 → 3  formalized: nine Lean modules, all `lake env lean`-green, wired into
      `GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.RHTower`; `#print axioms` on every
      capstone gives exactly `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## What the source claims

With `{x} = x - ⌊x⌋` and `s = a + ib`, `0 < a < 1`, `b > 0`:

1. (1) `ζ(s) = s/(s-1) - s ∫_1^∞ {x} x^(-s-1) dx`.
2. (2) the same identity at `1 - s`.
3. Appendix: `ζ(s) = G(s) ζ(1-s)` with `G(s) = π^((s-1)/2) Γ((1-s)/2) / (π^(-s/2) Γ(s/2))`, and
   `G(s) ≠ 0` for **all** `s ∈ ℂ`, hence `ζ(s₀) = 0 ⇔ ζ(1-s₀) = 0` for all `s₀ ∈ ℂ`.
4. (5) four real equations obtained by splitting (1) and (2) into real and imaginary parts at a
   zero.
5. (7)(10)(13)(16) closed-form primitives of `x^(c-1) cos(b log x)` and `x^(c-1) sin(b log x)`;
   (8)(11)(14)(17) their second primitives.
6. (9)(12)(15)(18) evaluation of the four integrals by partial integration with `u(x) = {x}`,
   `u'(x) = 1`.
7. (19)–(26) consequences, including division by `lim_{N→∞} N^a`.
8. (27)(28) `lim cos(b log N) = (a/b) lim sin(b log N)` and `= ((1-a)/b) lim sin(b log N)`, hence
   `a = 1/2`.

## What is true, and where it now lives

| Source item | Lean |
|---|---|
| (1) | `RHTower.riemannZeta_eq_sub_mul_integral_fract` (core already owned by `RHTower.FractionalPartZeta`) |
| (2) | `RHTower.riemannZeta_one_sub_eq_sub_mul_integral_fract` |
| (3)(4) complex form at a zero | `RHTower.integral_Ioi_one_fract_cpow_of_zeta_eq_zero` |
| polar split of the kernel | `GaloisForLFunctions.HTGeometry.ofReal_cpow_re`, `ofReal_cpow_im` |
| (5) unconditional form | `RHTower.integral_Ioi_one_fract_rpow_cos`, `..._sin` |
| (5) at a zero | `RHTower.integral_Ioi_one_fract_rpow_{cos,sin}_of_zeta_eq_zero` and their `_reflected_` companions |
| (7)(10)(13)(16) | `GaloisForLFunctions.HTGeometry.hasDerivAt_{cos,sin}LogPrimitive` (general exponent `c`; the four source cases are `c = -a` and `c = a-1`) |
| (8)(11)(14)(17) | `GaloisForLFunctions.HTGeometry.hasDerivAt_{cos,sin}LogSecondPrimitive` |
| Appendix multiplier | `RHTower.reflectionMultiplier`, `reflectionMultiplier_eq_Gammaℝ_ratio`, `riemannZeta_eq_reflectionMultiplier_mul`, `reflectionMultiplier_ne_zero` (open strip) |

The open-strip zero symmetry `ζ(1-s) = 0 ↔ ζ(s) = 0` was already owned by
`RHTower.ReflectionCocycleClass.riemannZeta_one_sub_eq_zero_iff` and is reused, not reproved.

## No-go closure

- **Exact killing theorem/mechanism (I): the partial integration is invalid.**  `{x}` is not
  differentiable; it drops by `1` at every integer.  The correct unit-interval expansion is
  `∫_1^{m+1} {x} f = ∑_{k<m} P(k+2) - (W(m+1) - W(1))`
  (`GaloisForLFunctions.HTGeometry.integral_one_to_succ_fract_mul`, specialized in
  `RHTower.integral_one_to_succ_fract_rpow_{cos,sin}`).  The source's (9)(12)(15)(18) drop the sum
  `∑ P(k+2)` entirely.  What remains, `{N} P(N) - (W(N) - W(1))`, converges to no real number for
  `0 < a < 1`, `b ≠ 0`: `RHTower.not_tendsto_jumpFree_{cos,sin}`, from
  `GaloisForLFunctions.HTGeometry.not_tendsto_{cos,sin}LogSecondPrimitive_atTop`.  Meanwhile the
  integral itself converges: `RHTower.tendsto_truncated_fract_rpow_{cos,sin}`.
- **Exact killing theorem/mechanism (II): the limits in (21)–(28) do not exist.**  For `b ≠ 0`
  neither `cos(b log N)` nor `sin(b log N)` has a limit at `+∞`
  (`RHTower.not_exists_tendsto_cos_and_sin_log`), and `lim N^a` is not a real number for `a > 0`
  (`RHTower.not_exists_tendsto_rpow_atTop_of_pos`).
- **Exact killing theorem/mechanism (III): (27) = (28) does not give `a = 1/2`.**  The pair of
  relations forces only `a = 1/2 ∨ (C = 0 ∧ S = 0)`
  (`RHTower.eq_half_or_eq_zero_of_ratio_pair`), and the implication to `a = 1/2` alone is false
  (`RHTower.not_forall_eq_half_of_ratio_pair`).
- **Exact killing theorem/mechanism (IV): the appendix's global claim is false.**  `Γ_ℝ` vanishes
  on the nonpositive even integers (`RHTower.Gammaℝ_neg_two_eq_zero`), and concretely `ζ(-2) = 0`
  while `ζ(3) ≠ 0`, so the zero locus of `ζ` is not globally reflection-invariant:
  `RHTower.not_forall_riemannZeta_eq_zero_iff_one_sub`.  Only the open-strip statement survives.
- **Strongest positive survivor:** the unit-interval partial-integration identity for an arbitrary
  kernel with two primitives on the positive ray, together with the closed-form primitives of the
  oscillatory power kernels and the four explicit values of the fractional-part cosine/sine
  integrals at a zeta zero in the open critical strip.
- **New insight:** the fractional-part representation carries the critical-line information in the
  *sum over integers* `∑ P(k)`, not in the boundary behaviour of the smooth primitive.  Any attempt
  to read a constraint on `Re s` off the growth of `W(N)` is reading the divergent part of an
  identity whose convergent part lives entirely in the omitted jump sum.
- **Status:** internal audit complete; dependency-closed; formalized.

## Log
- 2026-08-22 — created directly at stage 3: audit, formalization and refutation completed in one pass.
