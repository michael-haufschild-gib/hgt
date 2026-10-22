# Suzuki holomorphic-gauge characteristic limit no-go

- **ID:** `suzuki-holomorphic-gauge-characteristic-limit-no-go`
- **Stage:** 3-formalized
- **Type:** CLASS-COMPLETE ONE-ANGLE NO-GO / ROUTE-G FAILED SUBCLASS
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL]`
  `[NEW QUANTIFIER CLOSURE] [NOT AN RH PROOF] [NO COMPUTATION]`
- **Paper parent:** `../../5-failed/suzuki-holomorphic-gauge-characteristic-limit.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCharacteristicEntireLimitNoGo.lean`

## Formal theorem surface

```lean
def SuzukiHolomorphicGaugeCharacteristicLimitWall : Prop :=
  ∃ W Phi : ℕ → ℂ → ℂ,
    TendstoLocallyUniformly
        (fun n z => Complex.exp (Phi n z) * W n z)
        suzukiXiCharacteristicTarget atTop ∧
      (∀ᶠ n in atTop, Differentiable ℂ (W n)) ∧
      (∀ᶠ n in atTop, Differentiable ℂ (Phi n)) ∧
      (∀ᶠ n in atTop, ∀ z : ℂ, W n z = 0 → z.im = 0) ∧
      ∃ a : ℂ, suzukiXiCharacteristicTarget a ≠ 0

theorem not_suzukiHolomorphicGaugeCharacteristicLimitWall :
    ¬ SuzukiHolomorphicGaugeCharacteristicLimitWall
```

The declaration quantifies over all eventually entire real-zero characteristic families and all
eventually entire exponential gauges.  Hence it contains every analytic normalization of Suzuki's
Corollary 1.6, independently of aperture, shift, extension angle, or source realization.

## Proof architecture

1. `Phi n` entire implies `exp(Phi n)` entire and nowhere zero.
2. Gauged approximants remain entire and have the same real zero set as `W n`.
3. Mathlib's Weierstrass theorem
   `TendstoLocallyUniformlyOn.differentiableOn` derives global differentiability, hence
   `AnalyticOnNhd ... univ`, of the locally uniform target.
4. The gauged family therefore constructs the already formalized
   `SuzukiXiCharacteristicLimitWall`.
5. `not_suzukiXiCharacteristicLimitWall` refutes that wall by the consecutive-Xi-zero/Rolle pole
   theorem.

No conditional proposition, project axiom, numerical zero, simplicity premise, or computation is
used.

## Positive survivor

The theorem does not refute Suzuki's fixed-aperture real-zero theorem.  It forces any successor to
leave the one-entire-function category.  The exact survivor is the already formalized two-angle
meromorphic quotient/Livšic carrier in `SuzukiFiniteApertureHermiteBiehler.lean`, where common
entire gauges cancel and limiting poles are retained.

That survivor is Route G's corrected live core. It is not an unproved sublemma that can repair the
retired one-angle compact-limit statement.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCharacteristicEntireLimitNoGo.lean` — passed.
- `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiCharacteristicEntireLimitNoGo` — passed.
- `#print axioms RHTower.not_suzukiHolomorphicGaugeCharacteristicLimitWall` —
  `[propext, Classical.choice, Quot.sound]` only.
- Module was already imported by `formal/GaloisForLFunctions/RHTower.lean`; no new umbrella import
  was required.
- Repository static `scripts/formal_tools.py lint` was run without `--build`. It reported no Route G
  error; global exit was nonzero only because concurrently added unrelated modules
  `RHTower.DeningerPrimeBlockGreenSummability`, `HTGeometry.DigammaFieldJetPresentation`, and
  `HTGeometry.SyndeticDenseOrbitLaw` were not umbrella-reachable.
- No full build was run.
