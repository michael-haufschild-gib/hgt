# Growing overlap has an effective complete defect reserve

- **ID:** growing-overlap-effective-complete-defect-reserve
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** There are fixed positive constants `a,C,H` such that `W_(N,c)(x)≥a c^-7 D_N(x)-C c^9‖x‖²` for `c≥1` and `N≥H c^8`.

## Paper proof

The exact prime identity and the existing upper row bound give, at every horizon,
`P_N(x)+D_N(x)≤(log N+log 4+4)‖x‖²`.
This retains the entire defect at a fixed mass cost.

Put `d=min(growingMassConstant,1/2)>0`, `δ=d/c^7`, and choose
`L=ceil(max(3,4c,128 exp(2)c/δ))+1`. Then `L=O(c^8)`.
For `N≥L`, split coefficients at `M=floor(N/L)`.
The separated prefix pays its logarithmic self-energy with defect cost at most `δ/4`.
The proved growing Gamma bound pays the tail with coefficient at least `δ log N` and mass cost `O(c)`.
Ordered prefix-tail cross energy costs `O(c)` because physical width is at most one.
The existing prime-defect tail bound gives
`log N‖x_tail‖²≤(1+δ/4)D_N(x)+T‖x‖²`, where
`T=(1+4/δ)(log(2L)+log 4+log 8+8)+log(2L)`.
Thus Gamma pays `log N‖x‖²-(1-δ/2)D_N(x)` with mass cost `O(c^7 log(c+1))`.

Combine Gamma with the exact ratio-prime estimate. Assign defect allowance `δ/8` to each of the actual non-ratio prime form and the pole product. Their proved Young costs are `O(c²/δ+δ)=O(c^9)`. The complete form retains `δ/4` of the defect, proving the stated bound. All orientations, prime powers, and poles remain included.

In particular every negative unit vector has `D_N(x)≤(C/a)c^16`. This is a quantitative defect bound; passing from it to useful conductor confinement remains open.

## Lean proof

`CriticalArithmeticCorrelationTheory/TheCompleteWeilReserveHasPolynomialOverlapCost.lean`.

- `atomicWeilForm_add_full_poleDefect_le`: exact uniform prime counterterm.
- `tiltedUnitSpline_complete_defect_reserve_explicit`: explicit cutoff and cost.
- `exists_growingDefectCutoff_polynomial_bound`: cutoff `O(c^8)`.
- `exists_growingCompleteReserveCost_polynomial_bound`: mass cost `O(c^9)`.
- `exists_tiltedUnitSpline_complete_defect_reserve_polynomial`: complete reserve.
- `exists_negative_completeWeil_poleDefect_polynomial_bound`: negative-vector defect `O(c^16)`.

Focused Lean check passes; all six transitive audits use only `propext`, `Classical.choice`, and `Quot.sound`.
