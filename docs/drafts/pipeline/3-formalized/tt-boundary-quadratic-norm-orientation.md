# Exact quadratic norm orientation at the nonlinear boundary

- **ID:** TT-C78-NORM-ORIENTATION
- **Stage:** 3-formalized (2026-10-17)
- **Type:** THEOREM (paper)
- **Source:** Route TT; C75 complete boundary remainder, C76 exact regularization, C77 row-zero certificate; working card `../1-in-progress/tt-third-slope-nonlinear-cone.md`.
- **Statement:** The compact quadratic norm of the complete boundary reduced slope has an exact factor h^6, with strictly negative remaining factor at zero clock throughout the admissible parameter box. The physical value is positive and its conjugate negative on a uniform clock strip.

## Goal

Determine the actual norm orientation before proposing a global norm certificate for C78. This does not prove the full interior slope sign or RH. No positivity assumption on the unknown source polynomial is introduced.

## Gates

- [x] 0 → 1: full source and exact quadratic branch retained.
- [x] 1 → 2: dependency-closed paper proof below, [PROVED HERE].
- [x] 2 → 3: exact factorization, uniform sign, and source-norm identification audited with `lake --old env lean`; standard foundational axioms only; umbrella wiring complete (2026-10-17).
- [ ] 3 → 4: standalone publication audit.

Lean formalization is pending. Cell227 currently owns the sole Lean pipeline for C77; do not start a second build. Formalize this exact survivor after C77's global/source sign priority. The no-go is NOT closed in Lean and must not be retired as if it were.

## Definitions and verified inputs

All displayed functions below are real polynomials, using the real forms of the rational-coefficient C75/C76 expressions. Let

    H = 4/5, S = (6/5)*(361/25), b(h) = 1/12 - 7h/72,
    R(h,s) = s*(1-h^2*b(h)*s),
    Z(h,s) = (1-h*b(h)*s)/3,
    y(h,s) = h*Z(h,s), beta(h) = (2h-1)/3,
    alpha(h,s) = y(h,s)^2-beta(h)*y(h,s),
    A(h,s) = boundaryCompactA75(h,R(h,s)),
    B(h,s) = boundaryCompactB75(h,R(h,s)),
    G(h,s) = boundaryRegularCore77(h,s).

Here A and B mean the real values, not real parts used to discard imaginary terms. Their original finite expressions have rational coefficients; evaluation on real arguments is real. This real-cast bridge must be explicit in Lean.

Verified inputs:

1. `TTC76BoundaryRegularCore.boundaryCompact_regularization76` and `TTC77BoundaryRealCore.boundaryRegularCore77_ofReal` give

       A + y*B = h^6*G.

2. `TTC75BoundaryCompactZero` gives

       A(0,s)=0, B(0,s)=B0=268435456/2187 > 0.

   Audit evidence: `/tmp/tt_c75_boundary_compact_zero_pass1.log`, standard3.

3. Full C77 power reconstruction and `TTC77BoundaryPowerDegree0Norm` give

       G(0,s)=g(s)=155520-(567/64)*s^2.

   The complete row-zero Bernstein certificate in `TTC77BoundaryPowerDegree0Sign`, together with full reconstruction, gives g(s)>0 for every s in [0,S]. Equivalently its already-proved endpoint sign at (0,36) gives g(S)>0, and s^2<=S^2 gives g(s)>=g(S). No coefficient arithmetic outside Lean is required.

4. `TTC75BoundaryCompactAssembly.boundaryCompactA75_eq` and `boundaryCompactB75_eq` identify A=h^22*W.re and B=h^21*W.im, where

       W = boundaryReducedSlope75(9-h^2*R(h,s),h^(-1)).

   For h!=0, the exact boundary-root identity gives alpha=h^2*boundaryA(V,h^(-1)) and beta=h*boundaryB(h^(-1)). Therefore the norm defined below is h^44*QuadraticAlgebra.norm(W). Mathlib's actual `QuadraticAlgebra.norm_def` is re^2+b*re*im-a*im^2.

These are identities of the complete source slope after removing its proven V factor. Source differentiation occurs before boundary substitution.

## Paper proof [PROVED HERE]

Define

    Delta = beta-2*y = (2*h^2*b(h)*s-1)/3,
    J = h^6*G + Delta*B,
    N = A^2 + beta*A*B - alpha*B^2,
    Nhat = G*J,
    Ahat = h^5*G-Z*B,
    T = 2*A + beta*B.

Since alpha=y^2-beta*y, ordinary ring algebra gives

    N = (A+y*B)*(A+(beta-y)*B)
      = h^6*G*(h^6*G+Delta*B)
      = h^6*Nhat,

    A+(beta-y)*B = J,
    A = h*Ahat,
    T = 2*h^6*G+Delta*B.

Thus the second factor is the actual conjugate value, not an independently chosen comparison polynomial. At h=0:

    J(0,s) = -B0/3,
    Ahat(0,s) = -B0/3,
    T(0,s) = -B0/3,
    Nhat(0,s) = -B0*g(s)/3 < 0.

All functions are continuous polynomials. The compact interval [0,S] and strict face signs give one epsilon>0 such that, simultaneously for all s in [0,S] and 0<=h<epsilon,

    G(h,s)>0, B(h,s)>0, J(h,s)<0, Ahat(h,s)<0,
    Nhat(h,s)<0, T(h,s)<0.

This follows by taking an open neighborhood of the compact face {0} x [0,S] inside the intersection of the six strict sign sets and extracting a uniform product neighborhood. Consequently, for every 0<h<epsilon,

    A = h*Ahat < 0,
    A+y*B = h^6*G > 0,
    A+(beta-y)*B = J < 0,
    N = h^6*Nhat < 0.

For each s in [0,S], both Nhat(0,s) and Ahat(0,s) are nonzero. Hence N has exact vanishing order six and A has exact vanishing order one at zero clock. In particular N is divisible by h^6 and not by h^7, while A is divisible by h and not by h^2, as polynomials in h. These are algebraic order statements, not numerical sampling or asymptotic truncations. The negative first-order coefficient A is canceled by y*B through order five in the physical value.

For h>0, h^44 and h^22 are positive. The source-norm and source-trace identifications therefore transfer these signs to W.norm and 2*W.re+boundaryB(h^(-1))*W.im.

The exact-order conclusion can be strengthened from polynomial divisibility to continuous factorization, even on a punctured right neighborhood of zero. If N=h^7*D eventually as h tends to zero from the right, with D continuous at zero, cancellation gives Nhat=h*D on that neighborhood. Taking the right limit at zero forces Nhat(0,s)=0, contradicting its strict sign. The same argument excludes A=h^2*D with D continuous at zero. No differentiability or polynomial representation of D is required.

The source scaling also identifies the actual poles, rather than only the vanishing orders of the compactified expressions. For h!=0, cancellation in N=h^44*W.norm=h^6*Nhat and A=h^22*W.re=h*Ahat gives

    h^38*W.norm=Nhat,
    h^21*W.re=Ahat.

Consequently h^38*W.norm tends to -B0*g(s)/3 and h^21*W.re tends to -B0/3 as h tends to zero from the right. Both limits are nonzero on the stated parameter box. Thus the norm has exact pole order 38 and the first source coefficient exact pole order 21. These conclusions retain the complete source and follow from the same dependency-closed identities. Their Lean proofs are prepared but unaudited.

## Strict-interior consequence [PROVED HERE, Lean pending]

Here a physical interior point means a state satisfying all C78 inequalities. No membership in the actual modular orbit is asserted.

The obstruction is not removed by excluding the boundary. Fix any s with 0<s<361/25. At h=0 the boundary parameters have r=s, V=9, t0=s/12, h*t0=0, and compactSpeed=s/2>0. Continuity and a sufficiently small positive h put the exact boundary point inside every strict non-error constraint, and the norm and trace above are negative.

Keep this h,r,V fixed and let e approach 1 from below. In the full source polynomial use J=e*omega in the same quadratic algebra; its physical evaluation is at z=e*Z. At e=1 this equals W, by the full source identity and the proven V factor. Equality may also be established from evaluation at the two distinct real roots; no quotient derivative is used.

The corresponding t is

    t_e = t0 + 3*(1-e)*Z/h > t0.

For 0<e<1 close enough to 1, all strict speed/kinetic constraints persist. The exact error identity

    E(t_e) = (t_e-t0)*(1-h^2*(t_e+t0))

is positive: the second factor is positive at t0 for sufficiently small h and remains positive nearby. The full source norm and trace are polynomial functions of e and remain negative near e=1. Thus physical interior points with E>0 also have negative quadratic source norm and trace. This refutes a certificate demanding positive norm and trace throughout the full C78 cone, without refuting source-slope positivity there.

## No-go closure

- **Exact killing mechanism:** positive norm (and positive trace) has the wrong orientation in a whole boundary clock strip, and negativity persists at strict interior points. Earlier B0>0 alone did not establish this; C76's exact h^6 cancellation and C77's row-zero positivity complete the argument.
- **Strongest positive survivor:** exact factorizations N=h^6*Nhat and A=h*Ahat, with Nhat(0,s)=-B0*g(s)/3<0 and Ahat(0,s)=-B0/3<0; exact orders six and one; uniform A<0, B>0, positive physical value and negative conjugate value. The already-audited opposite-norm sign criterion `affine_boundary_pos_of_negative_norm75` has the correct orientation on this strip. This also settles the previously undetermined first-order sign of A on paper.
- **New insight:** a global certificate requiring positivity on both quadratic embeddings is incompatible with the full source. A negative norm is compatible with, and here accompanies, the desired physical positivity. Continue C78 with its physical branch or a correctly oriented piecewise norm criterion.
- **Status:** paper proof complete; exact Lean formalization pending, including the real-cast bridge and uniform compactness step. Do not mark the no-go closed until the positive survivor is audited and integrated.

## Log

- 2026-10-05 — Derived during C77 row40 audit from existing C75/C76 identities and C77 row-zero signs. No new Lean process launched. Corpus query `/tmp/tt_c78_quadratic_norm_trace_20261005.json` completed partial=false, query generation1240199, coverage generation1240207/inventory65772; compiler metadata mostly pending/stale, background refresh incomplete. All result categories inspected. General operator trace-norm hits do not apply to this quadratic source norm.

- 2026-10-05 — Formalization sources prepared, all UNVERIFIED, no Lean process launched: `/tmp/TTC78BoundaryNormAlgebra.lean` (exact factorizations and source norm/trace), `/tmp/TTC78BoundaryClockZeroSign.lean` (zero face from audited row0), `/tmp/TTC78BoundaryNormReal.lean` (complete real B bridge and column continuity), `/tmp/TTC78BoundaryNormSign.lean` (real identities and uniform orientation). Audit serially in that order after cell227 releases Lean and C77 source priority. The uniform sign proof uses only the row-zero certificate, not an assumed global C77 sign. Static forbidden-token scan is empty; it is not a compiler audit. No new caches exist. Exact source sign corollaries, strict-interior obstruction, and typed exact-order conclusions still require completion/audit before this no-go closes.

- 2026-10-05 — During C77 row43 audit, prepared three further UNVERIFIED modules: `/tmp/TTC78NormSource.lean` identifies the full normalized reduced source, its two-root norm/trace, continuity in e, source sign transfer, and exact pole regularizations; `/tmp/TTC78NormInterior.lean` retains all strict C78 state-space inequalities and proves the proposed e<1 obstruction by continuity and exact error factorization; `/tmp/TTC78NormOrder.lean` excludes an extra continuous clock factor and states the two exact source-pole limits. Audit the existing `/tmp/TTC78InteriorAlgebra.lean` before these three, then Source, Interior, Order. No numerical sampling, added sign premise in the existential capstone, second build, or compiler verification. All three have an empty static forbidden-token scan only. The stronger continuous-factor and pole-order statements above passed this paper dependency review; Lean audit and production integration remain mandatory before no-go closure.

## Lean status (2026-10-17) — survivor fully formalized; no-go closed

Three modules, all clean under `lake env lean`, `#print axioms` = `propext, Classical.choice,
Quot.sound` on every main theorem, appended to `GaloisForLFunctions/RHTower.lean`:

`RHTower/ThetaCuspRatioBoundaryNormOrientation.lean`
- real-cast bridge: real polynomials `boundaryCompactA77`, `boundaryCompactB77` with
  `boundaryCompactA77_ofReal`, `boundaryCompactB77_ofReal` (`(A : ℂ) = boundaryCompactA75`, no real
  parts taken);
- `boundaryNormA78_add_y_mul` (`A + yB = h⁶G`), `boundaryNorm78_factor` (`N = h⁶ Ĝ J`),
  `boundaryNormJ78_eq_conjugate`, `boundaryNormA78_eq_mul_hat` (`A = h Â`), `boundaryNormTrace78_eq`;
- clock zero: `boundaryNormA78_zero`, `boundaryNormB78_zero` (`B₀ = 268435456/2187`),
  `boundaryRegularCore77_zero` (`G(0,s) = 155520 - (567/64) s²`, by direct evaluation of the C77 core),
  `boundaryNormJ78_zero`, `boundaryNormAHat78_zero`, `boundaryNormTrace78_zero`, `boundaryNormHat78_zero_neg`;
- `boundaryNorm78_uniform_strip` (one `ε`, six simultaneous strict signs on `[0,ε)×[0,S]`, via a
  compact-face thickening lemma `exists_strip_neg_of_continuous`), `boundaryNorm78_orientation`
  (`A<0`, physical value `>0`, conjugate value `<0`, `N<0`, trace `<0`);
- exact orders: `boundaryNorm78_not_seventh_order`, `boundaryNormA78_not_second_order` (no continuous
  factor `h⁷D`, resp. `h²D`);
- `boundaryNormSlope78_source` (`h²²W.re = A`, `h²¹W.im = B`, `h²a = α`, `hb = β`, `h⁴⁴ norm W = N`,
  `h²²(2W.re + bW.im) = 2A+βB`), `boundaryNormSlope78_norm_trace_neg`;
- `boundaryNormSlope78_pole_identities`, `boundaryNormSlope78_pole_limits` (`h³⁸ norm W → -B₀g(s)/3`,
  `h²¹ W.re → -B₀/3`).
The global C77 Bernstein certificate is not needed: `g(s) > 0` on `[0,S]` follows from the exact
formula, and `G > 0` on the strip from continuity.

`RHTower/ThetaCuspRatioSourceSlopeReal.lean`
- `sourcePolyConj_slope`: the full source slope polynomial has real coefficients;
- `interiorHom` (`J ↦ eω` in the boundary quadratic algebra), `interiorHom_one`,
  `boundaryEval_interiorHom` (physical evaluation at `(v,k,ez)`), `interiorHom_slope_conj` (real
  components), `continuous_interiorHom` (continuity in `e`).

`RHTower/ThetaCuspRatioBoundaryNormInterior.lean`
- `interior_error_factor` (`E(t) = (t-t₀)(1-h²(t+t₀))`), `interiorT78_source` (`J = eZ`),
  `interiorNorm78_one` (`e = 1` recovers `N/h⁴⁴`, `T/h²²`), `interiorSlope78_physical`;
- **`boundaryNorm78_interior_negative`**: for every `0 < s < 361/25` there are `h > 0`, `e₀ < 1` such
  that for `e ∈ (e₀,1)` the state `(h, r, t_e)` satisfies `StrictCoarseCone`, has `E > 0`, and has
  negative real quadratic source norm and trace.

The no-go "positive norm and trace throughout the C78 cone" is therefore closed in Lean, together
with its positive survivor.  Card moved to `3-formalized`.
