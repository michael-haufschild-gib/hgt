# Cesàro all-cofinal-schedules no-go

- **ID:** cesaro-all-cofinal-schedules-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `squarefree-convolution-half-cesaro-source-criterion.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH]`

## Statement

The canonical triangular Cesàro half-source does not converge to zero at `s=6/11`. Therefore no
cofinal Cayley pole-degree schedule makes its pole-cleared family locally bounded on `rightHalf`.

## Proof

Assume `C_N(6/11)→0` and put `D_N` for raw half partial sums and `B_N=N C_N`. Then eventually
`‖B_N‖≤N`. For `k=floor(sqrt(floor(sqrt N)))`, average `D_j` over backward block
`N-k^3≤j<N`. Exact telescoping expresses block sum as `B_N-B_{N-k^3}`.

Every block index is at least `(k(k-1))^2`. Coefficient bound `‖a_n‖≤1` and
`n^{-6/11}≤n^{-1/2}` therefore give `‖D_N-D_j‖≤2k`. The block average and variation yield

`‖D_N‖ ≤ 34k ≤ 34N^(1/3)`.

Since `1/3<5/11=1-6/11`, polynomial Abel continuation would analytically cross zeta's pole at one,
contradiction. Every cofinal scheduled local bound already forces `C_N(6/11)→0`, so all such
schedules fail.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroAllCofinalNoGo.lean`.

Main theorems:

- `not_tendsto_squarefreeHalfCesaroSum_boundaryExteriorPoint_zero`
- `no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_cofinal`

Verification on 2026-09-04: direct check pass; targeted build `13053/13053`; both theorem axiom
audits contain only `propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

## Positive survivor

Order-one Cesàro/Riesz smoothing is terminal, independent of schedule. Any live arithmetic
successor must use stronger smoothing whose primitive geometry evades this interpolation, or a
singular nonlinear correction that changes the raw discrete derivative. Schedule slowing alone is
not a search class.
