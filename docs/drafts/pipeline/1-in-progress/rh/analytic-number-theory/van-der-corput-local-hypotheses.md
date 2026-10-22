# The corpus's van der Corput could not be pointed at any Liouville phase; now it can

- **ID:** `van-der-corput-local-hypotheses`
- **Stage:** 1-in-progress
- **Type:** INFRASTRUCTURE (formalized)
- **Scientific status:** `[LEAN-PROVED, AXIOM-CLEAN]` `[NOT NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT AN RH PROOF]`
- **Module:** `formal/GaloisForLFunctions/RHTower/VanDerCorputLocal.lean`,
  `formal/GaloisForLFunctions/RHTower/LogChirpNonstationary.lean`

## 1. The defect

`RHTower/VanDerCorput.lean` proves the weighted first- and second-derivative tests, but states them
with **global** smoothness:

```text
firstDerivTest  : ContDiff ℝ 2 φ, ContDiff ℝ 1 A  on all of ℝ
secondDerivTest : ContDiff ℝ 2 φ, ContDiff ℝ 1 A  on all of ℝ
```

Almost no phase of interest to this project is globally `C²`:

- the exterior radial Liouville phase `ξ_σ` is singular at the turning point `z = 1`;
- the Riemann–von Mangoldt chirp `t log t` is not `C²` at `t = 0`;
- every Liouville–Green phase is smooth only on the classically allowed region.

So the tests could not be applied to any of them without first constructing a global extension —
which is real work, and which nobody did. **The obstruction was formal, not mathematical**, and it
had silently blocked the whole van der Corput lane.

## 2. What is now proved

Same statements, same constants, all hypotheses on `[a,b]` only, derivatives supplied as data:

```text
norm_le_budget_of_hasDerivAt : ‖A t‖ ≤ ‖A a‖ + ∫_a^b ‖A'‖              (local amplitude budget)
firstDerivTestOn  : |φ'| ≥ lam > 0, φ'' ≥ 0 on [a,b]
                    ==> ‖∫_a^b A e^{iφ}‖ ≤ 4 (‖A b‖+‖A a‖+∫‖A'‖)/lam
secondDerivTestOn : φ'' ≥ mu > 0 on [a,b]
                    ==> ‖∫_a^b A e^{iφ}‖ ≤ 32 (‖A b‖+‖A a‖+∫‖A'‖)/sqrt(mu)
```

Both axiom-clean `[propext, Classical.choice, Quot.sound]`.

## 3. First application: the log-chirp

`LogChirpNonstationary.lean`, for `φ(t) = c·t log t`, so `φ'(t) = c(log t + 1)`, `φ''(t) = c/t`:

```text
norm_integral_logChirp_le              with amplitude, second-derivative form
norm_integral_logChirp_const_le        ‖∫_T^R exp(i c t log t)‖ ≤ 64 sqrt(R)/sqrt(c)   (0 < T ≤ R)
norm_integral_logChirp_const_le_of_one_le
                                       ‖∫_T^R exp(i c t log t)‖ ≤ 8/(c (log T + 1))    (1 ≤ T ≤ R)
```

The two bounds are incomparable, and each is the better one in its own regime. The first-derivative
form does not grow with the length of the interval and is the one to use whenever `T ≥ 1`; the
second-derivative form is the only one available on an interval containing the stationary point
`t = e^{-1}` (the unique zero of `φ'`), where the first-derivative test has no lower bound to use.
Neither is claimed to be sharp.

**This is not an improvement to the Selberg lane and I am not claiming it is.** For `T` large the
*first*-derivative test is far stronger, since `φ' = c(log t + 1)` grows while `φ'' = c/t` decays:
it gives `O(1/(c log T))` on `[T,2T]`, i.e. the corpus's already-recorded
`Ψ_T(k) = O_F(1/(k d_F T))` (working log §178.1, Theorem 104), and Theorem 104 proves that rate is
the method's total unconditional content. Nothing here moves that ceiling.

What the second-derivative form does give that the first cannot: a bound that is **uniform across the
stationary point** `t = e^{-1}`, where `φ' = 0` and the first-derivative test is unavailable. Any
argument whose interval straddles `e^{-1}` needs this form.

## 4. Second application

`OscillatoryMassRetention.lean` and `RadialPSWFMassRetention.lean` — see
`oscillatory-envelope-to-relative-mass.md`. Those are the reason this file exists: the mass-retention
estimate is an application of `firstDerivTestOn` to the doubled radial phase, and it could not have
been stated with the global test.

## 5. Honest grade

Van der Corput's tests are 1920s mathematics and the local restatement changes no constant. This is
infrastructure. Its only claim on attention is that it removes a *silent* blocker: a tool the corpus
believed it had, but could not actually use on its own objects. That kind of defect is invisible
until someone tries to apply the tool, which is an argument for applying tools rather than cataloguing
them.

## Gates

- [x] `firstDerivTestOn` — Lean, axiom-clean
- [x] `secondDerivTestOn` — Lean, axiom-clean
- [x] log-chirp bound, uniform across the stationary point — Lean, axiom-clean
- [x] first-derivative log-chirp bound `8/(c(log T + 1))` for `T ≥ 1` (sharp form) — Lean,
  axiom-clean (`norm_integral_logChirp_const_le_of_one_le`)
- [ ] independent audit

## Log

- 2026-07-27 (Claude): found while trying to apply the corpus's van der Corput to the radial
  Liouville phase and discovering it could not be applied at all. Checked afterwards whether the
  log-chirp rate improved anything in the Selberg lane: it does not — the corpus's Theorem 104
  already proves `O(1/(k d_F T))` is the ceiling, and my second-derivative bound is weaker there.
  Recorded that rather than presenting the bound as progress.
