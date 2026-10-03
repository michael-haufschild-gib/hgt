# TG C9.11r–s — native nuclear control from one ground column

- **ID:** tg-prime-polar-ground-nuclear-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1 `tg-principal-polar-operator-cancellation`; route TG
- **Statement:** Every native prime–polar Taylor-column tail has an exact positive energy decomposition through its ground column; every native symmetric physical time-band tail is controlled by that column in genuine Schatten-one norm.
- **Status:** all four affected leaf audits and all 32 public axiom queries pass; index refreshed; global lint has twelve unrelated unwired leaves and no finding in these modules.

## Hard question and new result

The previous signed-energy theorem retained all native cancellations, but left
an infinite family of Taylor degrees to control before nuclear admission.
That independent obstacle is removed. For every native finite tail K, write
`f_n=1_[−a,a] x^n`, `R_n=∫_0^∞ exp(-(n+1/2)t)D_exp(t)dt` and
`T_n=1−nR_n`. Then, for all degrees at once,

`‖K f_n‖² + a^(2n)n(n+1)‖R_n K f_0‖² = a^(2n)‖K f_0‖²`.

K may be a one-direction difference with arbitrary finite prime sets and
continuum endpoints, or the complete two-direction difference. The original
prime coefficients, polar density, full physical carrier and both parity
channels remain. No arithmetic cancellation premise is inserted.

For the actual physical time-band operator H and a>0, a fixed constant C gives

`‖K H‖_(S1) <= C ‖K f_0‖_(L2)`.

This is an estimate of an element of the genuine Schatten-one Banach space.
It is not a scalar trace estimate. It reduces physical nuclear admission to
the actual ground-tail problem, which remains unsolved.

## Dependency-closed paper proof

1. Construct the full physical resolvent `R_lambda f` by its strong Laplace
   integral for lambda>0, using corpus strong continuity and dilation unitarity.
   Every real translated tail is integrable. The group law gives
   `exp(-lambda h) U_h R_lambda f = R_lambda f − ∫_0^h exp(-lambda t)U_t f dt`.
   Differentiation at zero and unitarity yield
   `Re<R_lambda f,f>=lambda‖R_lambda f‖²`. Therefore
   `‖f−cR_lambda f‖²+c(2lambda−c)‖R_lambda f‖²=‖f‖²`.
   This holds for every physical f without a generator-domain assumption.

2. For `g_m=1_[−a,a]|x|^m`, exact overlap gives, for t>=0,
   `<U_t f_0,g_m>=2a^(m+1)exp(-(m+1/2)t)/(m+1)`.
   Scalar Laplace integration gives
   `<R_lambda f_0,g_m>=2a^(m+1)/((m+1)(lambda+m+1/2))`.
   At lambda=n+1/2, the resolvent energy and these moments give
   `‖T_n f_0‖²=2a/(2n+1)` and
   `<T_n f_0,g_n>=2a^(n+1)/(2n+1)`.
   Since `‖g_n‖²=2a^(2n+1)/(2n+1)`, the squared difference proves
   `a^n T_n f_0=g_n`, including degree zero.

3. The multiplier S_n is 1 on the positive half-line and `(-1)^n` on its
   complement. It is isometric, commutes with every positive dilation, and
   sends g_n to the actual signed f_n. R_n also commutes with every original
   dilation. Pass these commutations through the finite prime sum and the
   integrable literal polar continuum. Thus `K f_n=a^n S_n T_n K f_0`.
   The full energy law follows from step 1, with no lost source cross terms.

4. Exact cutoff mass implies `a^n‖f_0‖ <= (n+1)‖f_n‖`. The corpus identifies
   the actual Fourier Taylor output A_n as lying in span(f_n), so
   `‖K A_n‖ <= (‖K f_0‖/‖f_0‖)(n+1)‖A_n‖`.
   Its weighted Taylor norm series is already summable. Every K A_n has rank
   at most one, hence operator norm equals trace norm. Sum in the complete
   Schatten-one carrier; the continuous operator image and uniqueness of the
   known Fourier Taylor sum identify the result as K H. One fixed constant is
   `C=(Σ_n (n+1)‖A_n‖)/‖f_0‖`, independent of prime and continuum cutoffs.

## Lean evidence

- `SoninDilationResolventEnergy`: literal full resolvent, exact energy/loss and dilation commutation.
- `SoninPrimePolarGroundTransfer`: exact cutoff identification, parity isometry, all-degree native signed and symmetric tail energy.
- `SoninPrimePolarGroundNuclear`: native symmetric tail and physical time-band tail in Schatten-one, with its ground-column norm control.
- `SoninPrimePolarSignedEnergy`: additionally exposes the original finite source formula on every full physical vector.

All three new leaves are wired into `formal/GaloisForLFunctions/RHTower.lean`.
Each affected leaf passed foreground `lake --old env lean <leaf> -o <olean>`
with empty diagnostics. No full or umbrella build, heartbeat increase,
numerical experiment, proof hole or added axiom was used.

The public audit scratch is `/tmp/tg-c911r-axioms.lean`. It contains 32 queries
covering every public declaration in the four affected leaves. The audit exited
0; every declaration uses only `propext`, `Classical.choice`, `Quot.sound`.
The generated index completed successfully and all 32 declarations occur in
`formal/LEAN_API.md`. Global lint exited 1 solely for twelve unrelated
unwired modules; these four leaves have no lint finding. Detailed logs are
`/tmp/tg-c911r-axioms.log`, `/tmp/tg-c911r-index.log`, and
`/tmp/tg-c911r-lint.log`. All owned build/search processes terminated.

## Remaining hard proof and next conjecture

Actual arithmetic ground-tail decay is not proved. Its expected physical
coordinate formula includes both the weighted square integral of the native
prime-counting discrepancy and its endpoint square term. Neither may be
removed by an absolute coefficient estimate or a reversed positivity bound.
The retrieved chronological-work balance explicitly retains its upper signed
work term; it does not settle this cancellation.

The full Fourier-channel and complete-response transport still need to be
formalized from the native symmetric source and existing fixed correction
factors. Joint Gamma completion, the degree-three Hardy comparison and the
source-derived strict sub-unit law remain open. No RH proof or falsification
is claimed.

## Log

- 2026-10-02 — C9.11r conjecture proved through translated tails, exact cutoff moments and parity transport; native all-degree energy formalized.
- 2026-10-02 — C9.11s physical nuclear transfer proved through the corpus's weighted Fourier Taylor series; all affected leaf audits pass.

- 2026-10-02 — Successor P3 `tg-prime-polar-ground-recovery` proves fixed actual-column recovery and the reverse nuclear estimate. Ground and square time-band nuclear admission now have bounds in both directions; actual arithmetic cancellation remains open.
