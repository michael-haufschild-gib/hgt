# Guarded Finite-Passport Compact-Open Closure

- **ID:** `guarded-finite-passport-compact-open-closure`
- **Stage:** 2-fully-proven (needs-audit)
- **Type:** THEOREM (paper) / INFINITE-JET IMAGE BOUNDARY
- **Scientific status:** `[NOVELTY UNVERIFIED]`. The construction is elementary, but the exact
  guarded closure statement and its source-selector consequence require parent-literature audit.
- **Statement:** A periodic real-even order-one entire function with an off-axis zero quartet and
  exact all-order equality of two period-partner completed-flux germs is a compact-open limit of
  aperiodic real-even order-one entire functions with the same quartet and zero-free imaginary
  axis whose partner germs agree to arbitrarily high finite order but are never equal.

## Goal

Classify the boundary between finite completed-flux passports and the infinite source image. The
theorem shows that coefficientwise or compact-open control supplies no positive separation margin:
the missing selector must read global source data at infinity, not merely the analytic germ on
larger and larger compact sets.

## Exact construction

Fix `a>0` and put

`A(z)=cosh(z-a) cosh(z+a)`,

`alpha=a+pi*i/2`,

`Q(z)=(z^2-alpha^2)(z^2-conj(alpha)^2)`.

For `N>=0`, let

`epsilon_N=exp(-(N+1)^2)`,

`P_N(z)=1+epsilon_N Q(z)^(N+1)`,

`F_N(z)=A(z)P_N(z)`.

Then `A` and every `F_N` are entire, real-even, and Schwarz-real. The four points
`{+/-alpha,+/-conj(alpha)}` are simple zeros of all of them. On the imaginary axis,

`A(iy)=|cosh(iy-a)|^2>0`,

`Q(iy)=|y^2+alpha^2|^2>0`,

so `F_N(iy)>0` for every real `y`.

The function `A` has period `pi*i`. Multiplication by the nonconstant polynomial `P_N` destroys
every nonzero period, while preserving exact entire order one.

## Finite contact and full separation

Let

`c=-alpha`, `d=-conj(alpha)=c+pi*i`.

The residue-filled logarithmic-flux germs of `A` at `c` and `d` agree identically because `A` is
`pi*i`-periodic. At both centers, `Q^(N+1)` has order `N+1`. Consequently the two correction germs

`-x P_N'(c+x)/P_N(c+x)` and `-x P_N'(d+x)/P_N(d+x)`

vanish through degree `N`. The completed-flux germs of `F_N` at `c` and `d` therefore have equal
Taylor coefficients in every degree `0<=n<=N`.

They cannot be equal as analytic germs. Equality would cancel the periodic `A` contribution and
give equality of the logarithmic derivatives of `P_N(z)` and `P_N(z+pi*i)`. Hence

`P_N(z+pi*i)=C P_N(z)`

for some nonzero constant `C`. Equality of leading coefficients gives `C=1`, making the
nonconstant polynomial `P_N` periodic, a contradiction.

## Compact-open convergence

For a compact set `K`, put `M_K=max_(z in K)|Q(z)|`. Then

`sup_(z in K)|F_N(z)-A(z)|
 <= sup_(z in K)|A(z)| exp(-(N+1)^2) M_K^(N+1)`.

The logarithm of the final factor is

`-(N+1)^2+(N+1)log M_K -> -infinity`,

with the case `M_K=0` immediate. Thus `F_N -> A` uniformly on every compact subset of `C`.

## Positive source-image consequence

Let `J_N` be the set of guarded aperiodic functions whose two selected partner flux germs agree
through degree `N`. Every `J_N` is nonempty, and the explicit sequence above approaches a guarded
periodic function in the exact all-order locus. Therefore the all-order locus lies on the
compact-open boundary of arbitrarily deep finite-passport realizers.

The source selector must consequently use a nonlocal arithmetic condition that remains meaningful
under the loss of compact-open separation: for example fixed Dirichlet/Bohr coefficients, an exact
prime-power representing distribution, or another condition at infinity. Merely strengthening
finite local convergence or imposing the elementary global guards cannot supply a positive gap.

## Gates

- [x] 0 -> 1: explicit source-pure statement, construction, and boundary interpretation.
- [x] Paper proof written; independent audit still required before stage 2.
- [ ] Parent-theory and literature audit of compact-open density/closure results for symmetric
  exponential-type entire functions.
- [x] Lean formalization of the explicit family, full elementary guard stack, exact finite
  partner-flux contact, exact escape order, and pointwise convergence in
  `GuardedFinitePassportClosure.lean`.
- [x] Lean upgrade from pointwise to compact-open convergence and formal germ separation.

## 2026-07-12 Lean upgrade: compact-open convergence and formal germ separation

Both remaining Lean gates are closed in `GuardedFinitePassportClosure.lean`, axiom-clean
(`propext, Classical.choice, Quot.sound` only), lint green:

- `guardedClosureApproximant_tendstoLocallyUniformly` — `F_N -> A` uniformly on every compact
  subset of the plane (`TendstoLocallyUniformly`), via compact bounds on the envelope and the
  quartet atom plus the Gaussian-beats-geometric scale lemma.
- `guardedClosure_partner_fluxCorrection_germ_ne` — the two period-partner completed
  flux-correction germs are never eventually equal near the origin. Proof chain, fully formal:
  eventual equality of the corrections equates the coordinate-weighted logarithmic derivatives of
  the two recentered multiplier factors (`hermiteFlatFluxCorrection_eq_neg_logDeriv`); agreement
  near the origin forces a polynomial Wronskian identity
  (`polynomial_eq_of_eval_eventuallyEq_nhds_zero` on an infinite agreement set); value-one
  normalization at both centers upgrades the Wronskian identity to equality of the two shifts
  (`polynomial_eq_of_derivative_mul_eq`, an exact-vanishing-order argument at the origin); shift
  equality gives the nonconstant multiplier the vertical period `pi*i`, impossible for positive
  degree (`polynomial_no_nontrivial_period`).
- `guardedClosure_partner_factor_germ_ne` — no scalar multiple identifies the two factor germs
  either; the scalar is forced to one by evaluation at the centers
  (`guardedClosurePolynomial_comp_partner_ne_C_mul`).

The reusable general lemmas (`polynomial_no_nontrivial_period`,
`polynomial_eq_of_derivative_mul_eq`, `polynomial_eq_of_eval_eventuallyEq_nhds_zero`,
`infinite_setOf_eq_of_eventuallyEq_nhds_zero`) are stated for arbitrary complex polynomials and
are independent of the guarded family.

Stage moves to 2-fully-proven/needs-audit: the mathematics and the formalization are complete;
the outstanding gate is the parent-literature audit of compact-open density/closure results for
symmetric exponential-type entire functions, which decides new/not-new placement at stage 3.
