# Pay both Haar poles from the rooted arithmetic defect

- **ID:** acs-haar-prime-defect-pays-poles
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [signed Haar head payment](../1-in-progress/acs-low-haar-head-payment.md)
- **Target:** Prove a positive mass floor for
  `haarPrimeLogDefect d X + P(haarSectionProfile d X)` at every horizon,
  with every low-index coefficient and both original pole moments retained.

## Dependency-closed paper proof [PROVED HERE]

The [divisor-square argument](acs-haar-prime-ground-state.md) gives a
uniform arithmetic floor `haarPrimeLogDefect ≥ log(2)*mass/12`; both
modules passed their direct Lean checks.

For one pair of widths u,v, w=u+v and M=uv/w, let c be the common
boundary. Exact zero mean permits subtraction of f(c). On the left
interval, |h(x)|=v/w and |x−c|=c−x; on the right they are u/w and x−c.
Thus `integral |h(x)|*|x−c| = (v/w)*u²/2+(u/w)*v²/2 = M*w/2`.
A Lipschitz bound on f now gives
`|integral h*f|≤Lip(f)*M*w/2`. For f=exp(x/2) the derivative bound is
sqrt(2a+2)/2; for f=exp(−x/2) it is 1/(2sqrt(2a)). The exponential tangent
inequality `exp(t)≥1+t` and monotonicity give both estimates on the actual interval. Hence
the two half-exponential moments satisfy

`A_a^2/M_a ≤ M_a*w_a^2*(2a+2)/16`,
`B_a^2/M_a ≤ M_a*w_a^2/(16*(2a))`.

Use w_1<7/10, M_a≤w_a/4, w_a≤1/a. For a≥2, the normalized moment
squares are bounded by 3/(64a²) and 1/(512a²), respectively. At a=1,
the two bounds are at most 343/16000 and 343/128000. These imply the
pointwise bounds `A_a²/M_a≤1/(12a(a+1))` and
`B_a²/M_a≤1/(144a(a+1))` at every a≥1. The telescoping identity
`sum_(a=1..X) 1/(a(a+1))=1−1/(X+1)≤1` gives normalized moment sums
at most 1/12 and 1/144, respectively.
Weighted Cauchy–Schwarz gives the simultaneous operator bounds
`A(d)^2≤mass/12` and `B(d)^2≤mass/144` for arbitrary signed coefficients.
Weighted Young gives `P(d)=2A(d)B(d)≥−7mass/144`. Since log(2)>2/3,
the arithmetic defect plus the full pole retains mass/144. More precisely,
the pole bound is `P(d)≥−7mass/144`; together with `D_X≥mass/18` this
also gives `D_X+P(d)≥D_X/8`. Thus a positive share of the original
divisor-square form survives, not only its scalar mass floor. This
stronger consequence follows by multiplying `D_X≥mass/18` by 7/8
and adding the pole bound. Both conclusions are formalized.

The identity `(A/2+2B)^2≥0` gives the stated weighted Young bound without
introducing a separate pole or changing either moment. The elementary
lower logarithm bound log(2)>2/3 is available in mathlib. Thus every paper
input is discharged by the exact source identities and scalar estimates.

## Lean formalization

`ArithmeticCastelnuovoSeveri/TheHaarArithmeticReservePaysBothPoles.lean`
passed its final direct `lake --old env lean` check with no diagnostics.
It proves:

- `integral_haarProfile_distance`: exact shared-boundary distance moment.
- `abs_haarProfile_moment_le_slope`: mean cancellation retains that moment.
- `haarSectionProfile_exp_pos_sq_le_twelfth` and
  `haarSectionProfile_exp_neg_sq_le_oneHundredFortyFourth`: both signed
  exponential functionals have summable mass bounds.
- `haarSectionProfile_pole_ge_distance_budget`: `P≥−7mass/144`.
- `haarPrimeLogDefect_add_pole_ge_eighth_defect`: `D_X+P≥D_X/8`.
- `haarPrimeLogDefect_add_pole_ge_mass`: `D_X+P≥mass/144`.

The module is wired into the owning umbrella; the umbrella was not compiled.
Only missing prerequisite oleans were built, one at a time. This module
remains a leaf without an olean build.

## Scope

The actual Gamma/central-mass comparison, first-prime coarse/detail mixing
and coarse signed source remain open; this theorem does not assert full
Weil positivity or close ACS.

For the next joint comparison, retain the complete divisor-square defect
and the sharp pole estimate `P≥−7mass/144`. Replacing the defect everywhere
by its scalar floor would discard arithmetic payment needed against the
exact logarithmic/outgoing diagonal. No signed Gamma comparison is assumed.

No web search, novelty checks, numerical experiments, or axiom checks.

## Log

- 2026-10-29 — Closed paper proof, formalized both original poles with all
  signed coefficients and every low index retained; final direct Lean check passed.
