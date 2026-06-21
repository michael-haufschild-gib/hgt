# R45 - beta-conditioned layer correlation

Status: non-reducing bounded experimental finding / conjecture.

Random source chain:
- seed RandomNode: temperature is not always a sharply defined state variable for a small nonequilibrium system
- broad topic RNG: 10, superstatistics and fluctuating inverse temperature
- NODE RNG: 18, correlations between beta and dynamical variables can invalidate simple mixture models
- target-file RNG: 2, `docs/consolidated/01-landscape-and-geometry.md`
- target-topic RNG: 10, the layers of the landscape
- scientific-method RNG: 20, missing lemma
- perturbation-method RNG: 17, change representation

## Finding

The scalar layer cannot be used as an independent superstatistical beta
mixture for the landscape layers.

Let

```text
P = zeta'/zeta
A = d/ds log(0.5*s*(s-1)*pi^{-s/2} Gamma(s/2))
beta = log(1+|P|)
Delta = max(log|A|, log|P|) - log|A+P|.
```

The missing lemma for a scalar-mixture model would be:

```text
conditioning on beta decouples the phase-weld and sigma-lane layers.
```

The experiment falsifies that lemma on the tested windows. After binning by
the scalar beta layer, the true `Delta` field retains sigma-lane structure far
above phase-random controls that preserve the same `|P|` and hence the same
beta bins.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r45-beta-layer-correlation.py
```

Beta-conditioned mean `Delta` by lane:

```text
beta_bin=0: sigma=0.7:  0.2511, sigma=1.2:-0.0058
beta_bin=1: sigma=0.3:  0.9035, sigma=0.5: 0.8477, sigma=0.7: 0.3634, sigma=1.2:-0.0307
beta_bin=2: sigma=0.3:  0.7141, sigma=0.5: 0.8343, sigma=0.7:-0.3214
beta_bin=3: sigma=0.3:  0.4203, sigma=0.5: 0.0916, sigma=0.7:-0.3600
```

Residual lane score after beta conditioning:

```text
true weighted_spread = 0.780317
random weighted_spread: mean=0.206035, min=0.124195, max=0.357344

true max_spread = 1.155679
random max_spread: mean=0.406306, min=0.194739, max=1.086144
```

Step 11 changed representation to a beta-bin by sigma-lane interaction matrix,
with row and column effects removed:

```text
true interaction_rms = 0.192100
random interaction_rms: mean=0.092640, min=0.058127, max=0.157454
```

The controls preserve the scalar beta layer by construction; the excess is in
the conditional phase-weld/lane interaction.

## Interpretation

The landscape-layer warning becomes a quantitative non-product statement:
`beta` is not an independent mixing coordinate. A scalar-layer superstatistical
mixture cannot reproduce the phase-weld/cross-lane structure unless it also
models the beta-dynamics correlation.

Reduction risk: this is adjacent to prior amplitude-neutralized phase-carrier
findings. The increment is the explicit beta-conditioned layer-product test
and the interaction residual representation, not a new zero theorem.
