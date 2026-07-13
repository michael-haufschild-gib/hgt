# Finite-transverse leaf-reflection rigidity

- **ID:** `finite-transverse-leaf-reflection-rigidity`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/rhtower_status_constraint_1107.md` · §3
- **Statement:** An even entire two-base flank carrier with irrational generator ratio is constant whenever its coefficient support occupies only finitely many slices in either generator direction.

## Goal

Close the first genuinely leaf-intrinsic subcell beyond finite torus models.  No growth bound and no
holomorphic extension in the two torus variables is assumed; each occupied slice may contain an
infinite one-variable series whose continuation is available only through the original entire
leaf carrier.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, narrow build green, axioms checked, lint green
- [ ] scientific-new-knowledge: parent-theory and literature audit passed
- [ ] 3 → 4 publication-ready: standalone exposition + Lean certificate

## Theorem

`[PROVED HERE]` Let `α, β, w > 0` with `β/α ∉ ℚ`.  Let `G : ℂ → ℂ` be entire and even.  Suppose
that on `Im z ≤ -w`,

\[
G(z)=\sum_{m,n\ge0}b_{m,n}e^{-iz(m\alpha+n\beta)},
\qquad
\sum_{m,n\ge0}|b_{m,n}|e^{-w(m\alpha+n\beta)}<\infty.
\]

If the transverse support

\[
S_\beta=\{n\ge0:\exists m,\ b_{m,n}\ne0\}
\]

is finite, then `G` is constant.  By symmetry of the argument, the same conclusion holds if the
set of occupied `α`-slices is finite.

## Proof

Put `T=2π/α`, let `R` be the shift `(RG)(z)=G(z+T)`, and set
`ω=e^{-2πiβ/α}`.  Irrationality says that `ω` is not a root of unity.

For each occupied transverse slice define

\[
G_n(z)=\sum_{m\ge0}b_{m,n}e^{-iz(m\alpha+n\beta)}
\]

on the lower flank.  There `RG_n=ω^nG_n`, so the finite characteristic polynomial

\[
p(X)=\prod_{n\in S_\beta}(X-\omega^n)
\]

annihilates `G`.  Both sides are entire, hence the identity theorem promotes
`p(R)G=0` to all of `ℂ`.

Let `J` be reflection, `(JH)(z)=H(-z)`.  Then `JG=G` and `JRJ=R^{-1}`.  Conjugating the
annihilator by `J`, and multiplying by a harmless power of the invertible shift `R`, gives a second
polynomial annihilator

\[
p^\vee(R)G=0,
\qquad
\operatorname{roots}(p^\vee)=\{\omega^{-n}:n\in S_\beta\}.
\]

The two root sets intersect only at `1`: if `ω^n=ω^{-m}` with `m,n ≥ 0`, then
`ω^{m+n}=1`; irrationality forces `m=n=0`.  Therefore

\[
\gcd(p,p^\vee)\mid X-1.
\]

If `0∉S_β`, the gcd is `1`, so Bézout applied to the two annihilators gives `G=0`.  If
`0∈S_β`, the gcd is exactly `X-1`, and Bézout gives `(R-1)G=0`.  Thus in every case `G` is
`T`-periodic (with the zero function included).

The lower-flank series is absolutely bounded there.  Evenness gives the same bound on the upper
flank.  Periodicity folds the intervening strip into a compact fundamental rectangle, so `G` is
bounded on `ℂ`.  Liouville makes `G` constant.  Equivalently, the final step is the already
formalized `periodic_spectrum_rigidity` mechanism.  ∎

## Strong corollary

`[PROVED HERE]` Every nonconstant counterexample to two-base leaf-intrinsic reflection rigidity must
occupy infinitely many `α`-slices and infinitely many `β`-slices.  In particular it must have
infinite-dimensional orbit under each exact generator-period shift.  Finite transverse bandwidth,
finite tensor-polynomial width, and every finite union of parallel arithmetic-progression spectra
are closed.

## Why this is not the finite torus theorem

The earlier finite-dimensional torus argument assumes a single entire function of both torus
variables.  Here the slice functions may be infinite power series and may fail every transverse
continuation test.  The proof uses only a finite *set of transverse characters* to manufacture two
incompatible shift constraints.  It therefore closes an infinite-dimensional leaf-only class.

## Scientific-novelty audit

`[NOVELTY UNVERIFIED]` The proof mechanism combines standard constant-coefficient difference
equations with reflection and one-sided semigroup support.  Initial searches found parent work on:

- characteristic-polynomial solution theory for constant-coefficient difference equations;
- holomorphic almost-periodic functions with spectrum in a cone;
- global reflection symmetries of almost-periodic functions;
- analytic continuation and universal approximation for general Dirichlet series.

No located source states the finite-transverse dense-leaf theorem or its reciprocal-annihilator
proof.  This absence is not enough for scientific novelty.  The result remains in `needs-audit`
until authoritative bibliographies in analytic almost-periodic functions, exponential-series
continuation, and difference equations have been checked for an equivalent spectral-synthesis
statement.  The parent-theory gate is the main risk: despite closing a new infinite-dimensional
cell, the Bézout mechanism may be judged a routine application of standard difference algebra.

## RH verdict

The theorem materially sharpens the HGT reflection-rigidity problem but does not localize zeta zeros
and does not imply RH.  It must not be presented as an RH route.

## Lean target

1. Formalize polynomial action of a shift on functions and the Bézout annihilator lemma.
2. Formalize reciprocal conjugation under `J R J = R⁻¹`.
3. Prove coprimality after removing `X-1` from the two finite phase polynomials.
4. Connect the resulting period to `periodic_spectrum_rigidity`.

## Log

- 2026-07-11 — theorem discovered and complete paper proof written; scientific novelty left
  explicitly unverified; isolated Lean core started.

## 2026-07-11 Lean core status

`FiniteTransverseReflectionRigidity.lean` now machine-checks the reusable algebraic mechanism:

- `eq_zero_of_coprime_polyShiftOp` — coprime shift polynomials have no common nonzero carrier;
- `fixed_of_coprime_reflected_shift_annihilators` — after removing the common fixed root, forward
  and reflected annihilators force exact shift invariance;
- `phase_ne_inverse_phase_of_infinite_order` — positive forward and reciprocal phases cannot meet;
- `forward_reflected_phase_residual_isCoprime` — the two finite residual phase polynomials are
  coprime.

Standalone compilation and the named Lake build pass.  All four theorems have only
`[propext, Classical.choice, Quot.sound]`.  The analytic wrapper from a finite transverse flank
series to the two polynomial annihilators remains to be formalized before the 2 → 3 gate is checked.

## 2026-07-13 Lean finish added

The Liouville finish (Lean target step 4, "connect the resulting period to rigidity") is now a
standalone reusable theorem in
`formal/GaloisForLFunctions/RHTower/EvenPeriodicFlankRigidity.lean`, axiom-clean:

- `even_periodic_flankBounded_const` — an even entire `G` that is invariant under a nonzero real
  period `pR` and bounded on the lower flank `Im z ≤ -w` is constant (compact fundamental-cell bound
  + evenness-reflected flank bound + Liouville).

This decouples the finish from `periodic_spectrum_rigidity` (which was welded to the
arithmetic-progression series).

## 2026-07-13 Full analytic wrapper formalized

The complete analytic mechanism is now formalized axiom-clean in
`formal/GaloisForLFunctions/RHTower/FiniteTransverseReflectionRigidityAnalytic.lean`, capstone

- `finiteTransverse_reflection_rigidity` — an even entire `G` whose lower-flank trace is a finite sum
  of shift eigenfunctions `G = ∑_{n∈S} G_n` with `G_n(z+T) = ω^n G_n(z)` (`ω` of infinite
  multiplicative order) and which is bounded on the lower flank, is constant.

Supporting reusable pieces, all axiom-clean:

- `shiftEnd` / `shiftEnd_pow_apply` / `polyShiftOp_shiftEnd_apply` — the shift endomorphism of
  `ℂ → ℂ` and the pointwise value `polyShiftOp(shiftEnd c) p G z = ∑_e p.coeff e · G(z + e·c)`;
- `polyShiftOp_eq_zero_on_of_eigenslice` — a shift polynomial vanishing at every slice eigenvalue
  annihilates a finite eigenslice sum on any set closed under `+c`;
- `polyShiftOp_eq_zero_of_eventually` — the identity-theorem promotion from a neighbourhood to `ℂ`;
- `fullPhase_eq_mul` / `fullPhase_eq` (and the reflected versions) — the `(X−1)`-factorisation feeding
  the coprime-residual Bézout core.

The forward annihilator `∏_{n∈S}(R − ω^n)` is killed on the lower flank by the eigenslice; evenness
gives the reflected eigenslice `G = ∑_{n∈S} G_n(−·)` with eigenvalues `ω^{−n}` on the upper flank, so
`∏_{n∈S}(R − ω^{−n})` is killed there; the identity theorem globalises both; the coprime residuals
force `R G = G` (or `G = 0` when `0 ∉ S`); and `even_periodic_flankBounded_const` finishes.

The only remaining step for a top-level theorem stated from the explicit two-generator flank
exponential series is the elementary restatement supplying the eigenslice hypotheses `hslice`/`heig`
from `e^{-iT(mα+nβ)} = ω^n` (with `T = 2π/α`), which the wrapper takes as inputs.
