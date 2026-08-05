# Mass-Xi line-conjugate hyperbolic pair no-go

- **ID:** mass-xi-line-conjugate-hyperbolic-pair-no-go
- **Stage:** 5-failed
- **Type:** CONJECTURE DISPROOF + FORMALIZED SURVIVOR
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · 9.3
- **Statement:** Critical-line conjugation cannot supply the cancellation missing at the exact entropy wall; at vertical complex time a conjugate pair retains the larger exponential arm up to an exact relative factor.

## Goal

Test the first symmetry-sensitive escape from the absolute corona wall: pair every mass-shifted
spectral point with its critical-line conjugate before taking norms. If this cancellation conjecture
fails, extract and formalize the sharp positive law governing the pair.

## Gates

- [x] 0 → 1 in-progress: exact conjecture, candidate identity, no-go target
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: unconditional Lean theorem, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: route failed; positive survivor retained here

## Conjecture C29 [FAILED]

For an admissible spectral family, put `p=M+iK` and `tau=sigma+iu`. Conjecture: pairing `p` with
`conj p` reduces the exponential type of

\[
  e^{-\tau p}+e^{-\tau\bar p}.
\]

Exact expansion gives the opposite:

\[
  e^{-\tau p}+e^{-\tau\bar p}
   =2e^{-\tau M}\cos(\tau K).
\]

The two arm norms are `exp(-sigma M+uK)` and `exp(-sigma M-uK)`. Reverse triangle therefore gives

\[
 e^{-\sigma M}\left|e^{uK}-e^{-uK}\right|
 \le \left|e^{-\tau p}+e^{-\tau\bar p}\right|.
\]

If `uK>=0`, this is equivalently

\[
 e^{-\sigma M+uK}(1-e^{-2uK})
 \le \left|e^{-\tau p}+e^{-\tau\bar p}\right|.
\]

The stronger relative-error law is

\[
 \left|\frac{|e^{-\tau p}+e^{-\tau\bar p}|}{e^{-\sigma M+uK}}-1\right|
 \le e^{-2uK}.
\]

Thus, for `K>0`, normalized pair norm tends to one as `u→+infinity`. Line conjugation preserves,
rather than lowers, the exponential type responsible for the entropy wall.

## Lean artifacts

Sources:

- `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralVerticalHyperbolicPair.lean`
- `formal/GaloisForLFunctions/RHTower/XiMassLineConjugateHyperbolicPairNoGo.lean`

Key declarations:

- `HTGeometry.AbstractSpectralFamily.term_add_inv_eq_two_exp_mul_cos`
- `HTGeometry.AbstractSpectralFamily.exp_mul_abs_exp_sub_exp_le_norm_term_add_inv`
- `HTGeometry.AbstractSpectralFamily.dominant_arm_mul_one_sub_exp_le_norm_term_add_inv`
- `HTGeometry.AbstractSpectralFamily.abs_norm_term_add_inv_div_dominant_sub_one_le`
- `HTGeometry.AbstractSpectralFamily.tendsto_norm_term_add_inv_div_dominant_atTop_one`
- `RHTower.abs_norm_xiMassTerm_add_lineConj_div_dominant_sub_one_le`
- `RHTower.tendsto_norm_xiMassTerm_add_lineConj_div_dominant_atTop_one`

Umbrellas:

- `formal/GaloisForLFunctions/HTGeometry.lean`
- `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- Direct `lake env lean` on both modules: pass.
- Targeted builds: pass, `[2719/2719]` and `[9358/9358]`.
- Axiom audit of factorization, lower bounds, relative error, limit, and Xi specializations: only
  `propext`, `Classical.choice`, and `Quot.sound`.
- No RH hypothesis, project-local axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation proof.

## No-go closure

- **Exact killing theorem/mechanism:** reverse triangle plus exact two-arm norm law; normalized pair
  tends to the dominant arm with error at most `exp(-2uK)`.
- **Strongest positive survivor:** pointwise dominant-arm lower bound, exact relative-error bound,
  and asymptotic ratio one.
- **New insight:** vertical complex time hyperbolizes conjugation symmetry. Pairwise symmetry is an
  amplification law, not a cancellation resource. Any surviving cancellation must be nonlocal in
  spectral height or must retain literal prime phases.
- **Status:** failed route retired; positive survivor has dependency-closed paper proof and
  unconditional Lean formalization.

## Log

- 2026-08-05 — C29 opened; naive line-conjugate cancellation falsified algebraically.
- 2026-08-05 — sharp ratio-one survivor proved abstractly and specialized to mass-Xi; card retired.
