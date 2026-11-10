# Closure tasks in the consolidated review

- **ID:** fable-route-closures
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/fable.md`, §12.3.
- **Goal:** Resolve all ten tasks in the explicitly named §12.3 with unconditional, dependency-audited Lean proofs. §12.1 instead lists nine unfinished assemblies; the positivity ceiling belongs to both.

## Obligations

| Item | Required scope | Status |
|---|---|---|
| Calibrations of B13, Landing, DH | Exact scope of the three model theorems and joint rigidity | Audit pending |
| Arithmetic constituents | Wiener obstruction and the remaining bounded class | Bounded case `0 ≤ x < 1/2` remains open |
| First rung by sizes | Exact barrier and positive boundary theorem | Audit pending |
| Section rings of the square | Tower product formula and planar ideal equality | Audit pending |
| Covers and averaged families | Fixed-part and character-index laws, with rightmost-zero exception | Audit pending |
| S3 transfer | Exact implication and status of the transfer itself | Source proves transfer ⇒ (`Θ < 1` ⇒ RH); transfer remains unproved |
| Window and theta stages | Verification law and obstruction to unconditional induction | Audit pending |
| Scheduled sums and source completions | Exact criteria for all named routes | Audit pending |
| Positivity census | Decide 70% at every bandwidth | Open; existing spike only excludes 75% at `4/3` |
| Short mean values as detectors | Relocation invariance and positive density/census scope | Audit pending |

## Positivity question

The known model has excess mass `1/5` near frequency one. Its lower bound
`1/18 + 47/750` does not exceed the 70% target `7/45`.
A stronger candidate adds several nonnegative Fourier spikes. Set

`P(x) = 1 − sin²(x)/3 − sin⁴(x)/18 − sin⁶(x)/36 − 5sin⁸(x)/288`.

Then `sinc²(x) ≤ b²P(bx)` for `b ≥ 1`. The Fourier coefficients of `P` are
`3273/4096`, `991/4608`, `−49/3072`, `1/512`, `−5/36864` at cosine
frequencies `0, 2, 4, 6, 8`. Source: `TransThresholdPairCorrelation/PeriodicSincMajorant.lean`.
`sinc_sq_le_scaled_periodicMajorant` and `periodicSincMajorant_fourier` pass
direct `lake --old env lean` checking; their transitive axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`. Umbrella import added.

**Paper argument.** For `g(x)=x(2+cos x)−3sin x`, successive derivatives reduce
to `x sin x ≥ 0` on `[0,π]`, giving Cusa–Huygens. For `0≤c≤1`, the difference
between `1−(1−c²)/2−(1−c²)²/8−(1−c²)³/16−5(1−c²)⁴/128` and `c` is
`(1−c)⁵(5c³+25c²+47c+35)/128`. Hence `(2+|cos x|)²/9≤P(x)`.
For `|bx|≤π/2`, sine monotonicity and Cusa–Huygens give the scaled sinc bound;
outside, `|sin x|≤1` and `π>3` suffice. Double-angle identities give the coefficients.

**Remaining construction.** Add `(1−b²·3273/4096)K_N(2bx)` to `b²P(bx)`,
where `K_N=1+2Σ_{k=1}^N(1−k/(N+1))cos(kt)`. With `b=10001/10000`,
large `N` gives positive nonconstant coefficients and first coefficient above
`3/10`. Replace each Fourier atom by a narrow triangle. Prove pair-density
positivity, exact Fourier duality, and weighted mass above `7/45` at `4/3`.
The corpus already supplies the required difference-count identity
`RHTower.Sieve.sum_dist_double` and triangle Fourier transform.

The all-bandwidth obstruction remains open. A single counterexample at `4/3`
does not settle it; any fixed integrable perturbation of the constant form factor
has Frobenius value tending to one as bandwidth tends to infinity.

A stronger candidate is a positive off-diagonal pair measure with an atom of
mass greater than `3/10` at zero and the prescribed sub-threshold Fourier data.
The identity `frobenius(F,λ)=1+∫sinc²(πλx) dp(x)` would then exclude 70% at
every bandwidth. Positivity of its dual form factor is an additional obligation;
positive quadrature alone does not discharge it. No such measure is proved here.

## Completion gates

Exact statements, paper proofs, direct `lake --old env lean` checks, transitive
`#print axioms`, umbrella imports, and positive survivors for every retired route.
No numerical optimization or assumed analytic inputs.
