# R50 - Fisher array exchangeability warning

Status: dead end / product-sum substrate warning.

Random source chain:
- seed RandomNode: frailty estimates can shrink strongly toward the population mean, especially in small clusters
- broad topic RNG: 18, exchangeability in de Finetti-style probability models
- NODE RNG: 12, arrays and networks need Aldous-Hoover-style analogues, not ordinary sequence de Finetti alone
- target-file RNG: 2, `docs/consolidated/01-landscape-and-geometry.md`
- target-topic RNG: 17, Fisher signature wall
- scientific-method RNG: 11, experiments
- perturbation-method RNG: 21, build a dependency chain

## Transfer

The NODE asks whether a sequence-level Fisher norm misses an array-level
prime interaction. The tested finite-prime quantities were:

```text
S_X(sigma) = sum_p p^{-2 sigma}
E_X(sigma) = sum_{p<q} (p q)^{-2 sigma}
R_X(sigma) = sum_p p^{-2 sigma} (sum_{q != p} q^{-sigma})^2.
```

`E_X` is the independent-edge square norm. `R_X` is a toy shared-prime
row-interaction mass, meant to represent the kind of node-latent dependence
ordinary sequence exchangeability misses.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r50-fisher-array-exchangeability.py
```

At `X=100000`:

```text
sigma=0.45: S=4.147804, E=8.317985, R=50048.893158, R/E=6016.949
sigma=0.55: S=1.937728, E=1.694115, R= 3908.300252, R/E=2306.987
sigma=0.70: S=0.997192, E=0.393106, R=  179.001002, R/E= 455.350
sigma=1.20: S=0.300938, E=0.024497, R=    0.392174, R/E=  16.009
```

The array row interaction grows very differently from the sequence norm. But
the dependency chain is purely algebraic:

```text
R_X is controlled by sum_p p^{-sigma} and sum_p p^{-2 sigma}.
```

Thus the growth is inherited from prime-density/product sums.

## Verdict

Dead end for non-reducing count. The experiment is a useful modeling warning:
array/network prime observables are not interchangeable with sequence Fisher
norms. But the discovered growth reduces to PNT/product algebra, and the
independent-edge norm `E_X` adds no new wall beyond the original sequence
Fisher wall.
