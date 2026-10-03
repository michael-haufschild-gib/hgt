# Window-local dimension of W₃ (2026-10-03)

## Computed
- For each window `[T1, T2]` (40 units): FE-defect null space up to `T2 + 60`, with `N = 4(T_c/2π)^{3/2}`; Z-evaluation of that null space on the window.
- Count the singular values above 0.3, 0.1, 0.03, 0.01 and 0.001 of the window's top value, and compare with ζ's zero count `ϑ(T2)/π − ϑ(T1)/π`.

## Results (threshold 0.01)

| window | dim | zeros |
|---|---|---|
| 60–100 | 8 | 16.1 |
| 100–140 | 14 | 18.8 |
| 140–180 | 19 | 20.6 |
| 180–220 | 22 | 22.0 |
| 220–260 | 23 | 23.2 |
| 260–300 | 24 | 24.2 |

- The spectrum is a flat plateau (≈ 0.28), then a cliff.

## Interpretation
- `dim W₃|window → ζ's zero count`: L399's surplus `ϑ/π` is exact.
- Below the onset (~45 to 140), freedom lags.
- Perturbative twins need one condition per ζ zero, so the degree-3 twin problem is exactly critical. Counting cannot decide C329.
- **S19, evaluation at ζ zeros.** Smallest singular value on the plateau subspace:

  | point set | window 180–220 | window 260–300 |
  |---|---|---|
  | ζ zeros | 3.0e-4 | 4.8e-4 |
  | Gram points | 1.3e-3 | 1.1e-3 |
  | midpoints | 2.1e-3 | 1.8e-3 |
  | zeros shifted by 0.25 spacing | 6.5e-4 | 4.1e-4 |
  | zeros shifted by 0.5 spacing | 1.2e-3 | 3.5e-4 |
  | random points (median) | 4.6e-6 | 3.7e-7 |

  ζ's zeros are an ordinary well-spread node set for W₃: no near-kernel (no twin seeds) and no special repulsion.
