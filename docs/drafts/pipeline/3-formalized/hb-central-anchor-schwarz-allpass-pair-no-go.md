# HB central-anchor Schwarz all-pass pair no-go

- **ID:** hb-central-anchor-schwarz-allpass-pair-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB survivor: source-derived phase/clock calibration; `ThetaCuspHawkingPartnerCorrelationEndpoint.lean` open source-locked homodyne reference
- **Statement:** Every hypothetical upper theta-Hawking/Xi resonance forces a second upper resonance whose paired causal all-pass dressing preserves full physical-frequency intensity, exact zero-frequency complex calibration, and real-time Schwarz symmetry, but carries strictly positive pointwise Wigner--Smith clock and winding charge two.

## Goal

Kill central homodyne calibration, even when strengthened by real-signal/Schwarz symmetry, as a producer for HB's missing source-dynamical minimum-phase/clock law.  Exact RH chain:

`off-critical Xi zero`
→ `upper theta-Hawking resonance r`
→ `source-forced upper partner -conj(r)`
→ `paired causal all-pass ambiguity invisible to intensity + central complex anchor + reality symmetry`
→ `central calibration cannot prove minimum phase`
→ surviving HB burden is a source-derived nonlocal phase-transport, frequency-derivative/clock, or global winding law.

No RH premise occurs.  The theorem quantifies over every resonance and proves the obstruction conditionally inside a closed proposition.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem `d4ThetaCuspHawkingCentralAnchorSchwarzAllPassPairRouteKilled`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus audit

Required searches used `scripts/formal_tools.py research`.

- `XiC_conj` and `XiC_even` provide the source-forced zero quartet.
- `xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance` identifies Xi zeros with literal two-ended theta-Hawking resonances.
- `thetaCuspHawkingCausalAllPassBoundary_eq_poleFactor`, `norm_thetaCuspHawkingCausalAllPassBoundary`, and `thetaCuspHawkingCausalAllPassClock_pos` provide one-resonance boundary factor, intensity blindness, and positive clock.
- `thetaCuspHawkingAllPassWindingCharge_eq_one` gives one winding unit per upper resonance.
- `ThetaCuspHawkingPartnerCorrelationEndpoint.lean` explicitly leaves canonical source-locked phase convention open.
- No corpus theorem constructs the upper partner `-conj(r)`, proves its paired factor is centrally anchored and Schwarz-real, or applies that pair to kill central phase calibration.

## Literature audit (through 2026-08-31)

- Generic boundary interpolation by finite Blaschke products is classical; Bolotnikov classifies products matching finitely many unimodular boundary values.  Therefore no generic claim that finite phase anchors fail is novel here.
- Real-time scattering symmetry and conjugate-paired all-pass/Blaschke factors are standard in filter and passive-scattering literature.  Therefore the pair algebra itself is not claimed as novel.
- Searches combining Riemann Xi, theta/Hawking scattering, Blaschke/all-pass phase, Wigner--Smith clock, and homodyne anchoring found no source-native theorem below.

Novelty classification: **new route-specific obstruction/bridge, not a new general Blaschke theorem**.  New content is that Xi's own FE--Schwarz quartet supplies the real-symmetric, centrally anchored ambiguity automatically, so one cannot appeal to source reality or a zero-frequency phase convention to remove the already-formalized theta-Hawking all-pass sector.

## Exact theorem and proof

Let `r` be a theta-Hawking backreaction resonant mode with value

`r = a + i b`, `b > 0`.

Define its upper FE--Schwarz partner

`r# := -conj(r) = -a + i b`.

### Lemma 1: source-forced upper partner

`XiC(r) = 0`.  Schwarz reality gives

`XiC(conj(r)) = conj(XiC(r)) = 0`,

and evenness gives

`XiC(-conj(r)) = XiC(conj(r)) = 0`.

The exact resonance determinant converts this zero back into a theta-Hawking resonant mode.  Direct coordinate calculation gives

`Re(r#) = -Re(r)`, `Im(r#) = Im(r) = b > 0`.

### Lemma 2: paired all-pass boundary

For real physical frequency `x`, write the existing causal boundary factor as

`B_r(x) = (x-r)/(x-conj(r))`.

Define

`A_r(x) := B_r(x) B_{r#}(x)`.

Both denominators are nonzero because their imaginary parts have absolute value `b > 0`.  Existing one-factor norm rigidity yields

`|A_r(x)| = |B_r(x)| |B_{r#}(x)| = 1`.

### Lemma 3: exact central complex anchor

Since `r != 0`,

`B_r(0) = r/conj(r)`

and

`B_{r#}(0) = conj(r)/r`.

Therefore

`A_r(0) = 1`.

This is intrinsic to the source-forced pair; no arbitrary external phase rotation is inserted.

### Lemma 4: real-time Schwarz symmetry

For real `x`, direct conjugation of the pole factors gives

`B_r(-x) = conj(B_{r#}(x))`,

`B_{r#}(-x) = conj(B_r(x))`.

Commutativity then gives

`A_r(-x) = conj(A_r(x))`.

Thus the ambiguity respects the standard Fourier reality condition.

### Lemma 5: dressed literal source remains calibrated and intensity-equivalent

Define the paired dressed theta-Born boundary response

`D_r(x) := A_r(x) thetaCuspFourierLaplace(x)`.

Then `D_r(0) = thetaCuspFourierLaplace(0)` by Lemma 3, and

`|D_r(x)| = |thetaCuspFourierLaplace(x)|`

for every real `x` by Lemma 2.  On the real axis, `thetaCuspFourierLaplace = XiC`; `XiC` is even and Schwarz-real, hence its real-axis values are real and even.  Lemma 4 therefore also gives

`D_r(-x) = conj(D_r(x))`.

### Lemma 6: surviving clock and winding

Define paired clock

`tau_r(x) := tau_single(r,x) + tau_single(r#,x)`.

Each summand is strictly positive because both resonances have imaginary part `b > 0`; hence `tau_r(x) > 0` for every real `x`, in particular at the central anchor.  Each factor has winding charge one, so the paired charge is exactly two.

### Theorem [PROVED HERE]

For every upper theta-Hawking resonance, the paired dressing simultaneously satisfies:

1. exact complex calibration at zero frequency;
2. unchanged magnitude at every physical frequency;
3. real-time Schwarz symmetry;
4. strictly positive pointwise additional Wigner--Smith clock;
5. winding charge two.

Lemmas 1--6 prove all clauses with no open dependency.  Therefore intensity plus one central complex phase anchor plus reality symmetry cannot imply the minimum-phase/clock rigidity equivalent to RH.

## No-go closure

- **Exact killing theorem/mechanism:** Xi FE--Schwarz symmetry forces the second upper resonance needed to make the hidden causal all-pass sector both centrally normalized and real-symmetric.
- **Strongest positive survivor:** The paired phase derivative is not merely nonzero: it is the sum of two strictly positive Lorentzians and its global winding is exactly two.  A source-derived clock/phase-transport law can detect precisely what central value and all intensities erase.
- **New insight:** Source reality strengthens, rather than removes, the obstruction: it organizes any hypothetical off-axis resonance into the exact degree-two all-pass packet that survives central homodyne calibration.
- **Status:** Formalized in `ThetaCuspHawkingCentralAnchorSchwarzAllPassPairNoGo.lean`; direct Lean, targeted module build, axiom audit, corpus-index lookup, and global formal lint all PASS.  Axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Failure pivots

- **C0 — arbitrary finite anchors determine phase:** rejected as classical false/generic boundary interpolation, not new.
- **C1 — one factor can be centrally anchored while preserving reality:** failed for a generic non-imaginary resonance; a single normalized factor does not obey the required negative-frequency conjugation law.
- **C2 — source-forced FE--Schwarz pair:** survives and proves theorem above.

## Log

- 2026-08-31 — created in 1-in-progress; corpus and literature audits complete; C0 and C1 rejected; C2 paper proof closed; Lean formalization and targeted audit passed.
