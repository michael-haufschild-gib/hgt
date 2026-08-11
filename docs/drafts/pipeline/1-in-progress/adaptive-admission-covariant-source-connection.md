# Adaptive admission covariant source connection

- **ID:** adaptive-admission-covariant-source-connection
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** Moving Gram--Schmidt admission converts completed adaptive source positivity into a strictly dissipative covariant derivative; frozen-flag failure is precisely its connection/lower-contact memory.

## Goal

Close gap between positive source of current monic admission and negative source forced for frozen
boundary flag.  Producer must remain source-first: full null-gauge coefficient minus its intrinsic
lower-contact residual, then rational--Gamma/von Mangoldt formation, before reflection aggregation.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Conjecture / proof-or-fail loop

1. **Conjecture A — ordinary moving odd current is decreasing.**  Let `L_y` obey
   `d L_y(f)/dy = -L_y(X (X f' + f))`, let `P_n(y)` be moving monic orthogonal admission, and set
   `B_n(y)=L_y(P_n X P_n)`.  Differentiation gives

   `B_n' = -2 L_y((X P_n) X (X P_n' + P_n)) + 2 L_y((∂_y P_n) X P_n)`.

   First term is negative Jacobi energy.  Second term need not vanish because `X P_n` has a
   `P_(n-1)` component.  **FAIL:** positivity alone does not imply ordinary monotonicity.

2. **Conjecture B — monicity kills moving-frame term.**  Monicity gives
   `degree(∂_y P_n)<n`, but three-term recurrence gives exactly

   `L_y((∂_y P_n) X P_n)=h_n ∂_y(nextCoeff P_n)`.

   **FAIL:** degree drop kills pairing with `P_n`, not with `X P_n`.

3. **Conjecture C — corrected current has strict covariant dissipation.**  With
   `a_n=nextCoeff(P_n)`, `h_n=L_y(P_n²)`, and Jacobi energy `E_n>0`, define

   `D B_n := B_n' - 2 h_n a_n'`.

   Then exact source connection predicts `D B_n=-2 h_n E_n<0`.  This is the positive survivor.

4. **Conjecture D — connection is removable by local scalar correction `B_n-2h_na_n`.**
   Differentiation leaves `-2a_n h_n'`; therefore proposed primitive does not remove connection.
   **FAIL.**  One-form `2h_n da_n` is not generally exact in multi-parameter moment space; its
   curvature is `2 dh_n∧da_n`.  Along one ray it has a nonlocal primitive, which is exactly an
   effectivity/admission issue rather than a fixed finite reporter.

5. **Producer theorem under attack.**  Before calculus, combine existing null-gauge source law
   with Jacobi energy.  For current monic admission and finite positive block `H_(n+2)`, full
   corrected null-gauge coefficient must equal

   `(2n+1) · 2 h_n E_n > 0`.

   Any negative outgoing corrected coefficient therefore forces either failure of `H_(n+2)≻0`
   or frozen/moving admission mismatch.  This is exact arithmetic localization of connection
   defect, not an orientation map.

   **PROVED AND FORMALIZED.**  The full corrected producer, finite Jacobi-energy identity,
   genuine-crossing dichotomy, moving product rule, and covariant derivative law are in
   `RHTower.XiShiftedAdaptiveOrthogonalNullGaugeArithmeticProducer` and
   `RHTower.XiShiftedAdaptiveAdmissionCovariantSource`.

6. **Conjecture E — canonical inverse-Hankel evolution supplies actual tangent, not abstract path
   data.**  Write canonical lower coefficient vector `a=-H_n⁻¹t_n`.  Corpus matrix inverse jet and
   shifted-Xi terminal-flux theorem force

   `a' = -( -(H_n⁻¹ H_n' H_n⁻¹)t_n + H_n⁻¹t_n')`.

   **PROVED AND FORMALIZED.**  Every coefficient of actual canonical admission has this derivative;
   its terminal monic velocity is zero.  Thus covariant source law now applies to actual `P^sharp`,
   without postulating a differentiable admission curve.

7. **Conjecture F — norm evolution cancels moving tangent.**  Differentiating
   `h_n=L_y(P_n²)` kills `2L_y(P_n ∂_yP_n)` by orthogonality.  Exact top-jet projection of
   `X²P_n'` gives

   `h_n'=(2a_n-(2n+1)α_n)h_n`.

   **PROVED AND FORMALIZED.**  Only finite `H_(n+2)≻0` is used.

8. **Conjecture G — one gauge-invariant cumulative flux cancels connection.**  With
   `a_n=-Σ_(j<n) α_j`, set

   `C_n=-2a_n+α_n=2Σ_(j<n)α_j+α_n`.

   Quotient differentiation of `α_n=B_n/h_n`, using covariant source and norm laws, cancels
   `a_n'` exactly and yields

   `C_n'=-(2Σ_(j<n)α_j²+α_n²+4Σ_(j<n)β_j+2(n+1)(β_n+β_(n+1)))<0`.

   **PROVED AND FORMALIZED.**  This is a strict source-side Lyapunov law for actual inverse-Hankel
   admission, not a fixed reporter.  It replaces failed attempt to sign single connection
   coefficient.

9. **Next conjecture — first-face extension or singular holonomy.**  On any positive chamber
   connected to far right, strict decrease toward far-right zero suggests `C_n>0`.  This alone does
   not yet forbid first boundary: Jacobi coordinates may diverge when `det H_n→0`, or finite limit
   may survive.  Required theorem is exact boundary classification: show `C_n` extends with a sign
   incompatible with outgoing null-flag contact, or prove every nonextendable branch forces a
   prohibited smaller principal-minor failure.  No sign claim is made without that audit.

## Door passport

- **Input purity:** shifted-Xi moment source connection, moving monic orthogonal admission, full
  inverse null-gauge germ, explicit lower-contact residual, finite Hankel positivity.
- **No circularity:** no RH, zero-location, Laguerre--Pólya, Herglotz realization, fixed linear
  reporter, post-aggregation orientation, or numerical evidence.
- **Output sought:** corrected arithmetic producer identity, covariant dissipation, then a theorem
  eliminating both higher-block failure and admission holonomy along any genuine crossing ray.
- **Current boundary:** positivity does not control connection one-form or rule out infinite degree
  escape; that is next hard theorem, not hidden in notation.

## Log

- 2026-08-11 — created in `1-in-progress`; ordinary monotonicity and naive local primitive
  falsified; covariant Jacobi dissipation and corrected null-gauge producer survive.
- 2026-08-11 — surviving producer and covariant law proved and formalized; exact remaining scalar
  is subleading admission connection.  Separate Stage-3 certificate:
  `adaptive-null-gauge-covariant-jacobi-source.md`.
- 2026-08-11 — actual inverse-Hankel admission differentiated from corpus terminal-flux and matrix
  inverse jets.  Exact completed canonical aggregate `2h_nE_n`, norm ODE, cumulative trace identity,
  and strictly negative cumulative Jacobi-flux derivative proved in Lean.  Open core moved to
  boundary extension versus singular holonomy, not connection sign.
