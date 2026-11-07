# BHR — the gravitational wave of a pulse is regular across the horizon

- **ID:** bhr-metric-regularity (review-0711 A26, "regularity at r = 1")
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** In ingoing coordinates `v = t + r_*`, the exact vacuum perturbation of every compact profile (`imageMetric`, in particular the gravitational wave of every pulse) has components `h_{vi} = σᵢ(F m(S) + m′(S))`, `h_{ri} = σᵢ(m′(S)/(r+1) − m(S))`, `S = v − log(2r/(r+1)) + log s`, and every component is `C^∞` at every point with `r > 0`, `y > 0`, the future horizon `r = 1` included. The background becomes `−F dv² + 2dv dr + r²(dx²+dy²)/y²`.

## Proof
The Jacobian is `dt = dv − dr/F`, `F = r²−1`. So `h_{vi} = h_{ti}` and `h_{ri}^{in} = h_{ri} − h_{ti}/F`. For one row `h_{ti} = σᵢ(F m + m′)`, `h_{ri} = σᵢ(r/F)m′`, hence `h_{ri} − h_{ti}/F = σᵢ((r−1)/F · m′ − m) = σᵢ(m′/(r+1) − m)`. In ingoing coordinates `t + γ(r) = v − log(2r/(r+1))`, smooth for `r > 0`. Rows are locally finite (compact support of `m` in `S`), uniformly on a neighborhood in `(v,r,x,y)`, so the sums are locally finite sums of smooth functions.

## Lean
`formal/GaloisForLFunctions/BlackHoleRingdown/TheMetricOfAPulseIsRegularAcrossTheHorizon.lean`: `hyperTime_exteriorOfIngoing`, `ingoing_background`, `rowR_sub_rowT_exteriorOfIngoing`, `ingoing_imageMetric` (`Jᵀ h J` is the ingoing perturbation on the exterior), `exists_finset_ingoing`, `contDiffAt_ingoingMetric`. Checked with `lake --old env lean`.
