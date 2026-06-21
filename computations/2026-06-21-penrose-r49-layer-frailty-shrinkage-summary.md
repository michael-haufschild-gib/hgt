# R49 - layer frailty shrinkage

Status: dead end / instrumentation warning.

Random source chain:
- seed RandomNode: aggregating heterogeneous individuals can create apparent power laws even when no individual follows one
- broad topic RNG: 9, frailty models in survival analysis
- NODE RNG: 10, frailty estimates can shrink strongly toward the population mean, especially in small clusters
- target-file RNG: 3, `docs/consolidated/01-landscape-and-weld-geometry.md`
- target-topic RNG: 12, layers of the landscape
- scientific-method RNG: 5, make visual
- perturbation-method RNG: 10, test extreme cases

## Transfer

The frailty NODE maps to a layer-estimation warning:

```text
small lane-cluster phase estimates shrink toward a global landscape mean.
```

The tested phase-weld layer was

```text
Delta = max(log|A|, log|P|) - log|A+P|.
```

Lane/window cells were treated as small clusters and passed through a simple
empirical-Bayes normal shrinkage estimator.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r49-layer-frailty-shrinkage.py
```

NODE validation on synthetic frailty data:

```text
n=1:  shrink_factor=0.200, mean|raw|=1.805, mean|posterior|=0.361
n=4:  shrink_factor=0.500, mean|raw|=1.084, mean|posterior|=0.542
n=32: shrink_factor=0.889, mean|raw|=0.811, mean|posterior|=0.721
```

Target transfer with five samples per lane-cluster:

```text
empirical shrink_factor=0.596193
raw lane means:    sigma .3=0.546515, .5=0.581647, .7=0.074084, 1.2=-0.025542
shrunk lane means: sigma .3=0.444619, .5=0.465564, .7=0.162959, 1.2= 0.103562
raw spread=0.607189
shrunk spread=0.362002
```

Extreme-case sweep:

```text
points_per_cell=1:  shrink_factor=1.000000, ratio=1.000000
points_per_cell=2:  shrink_factor=0.528255, ratio=0.528255
points_per_cell=5:  shrink_factor=0.596193, ratio=0.596193
points_per_cell=10: shrink_factor=0.620264, ratio=0.620264
```

The one-point case is a boundary artifact: the estimator has no within-cell
variance information and falsely reports no shrinkage.

## Verdict

Dead end for non-reducing count. The phase-weld layer contrast is visibly
attenuated by hierarchical pooling, but that is exactly the frailty shrinkage
constraint. The result is a useful experimental warning: do not over-pool
small lane/window cells when testing landscape layers. It does not add a new
native layer invariant.
