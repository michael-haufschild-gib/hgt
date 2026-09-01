# Monotone Schrödinger potential does not force TCD D1

- **ID:** TCD-MS-D1-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The positive even entire profile `g(z)=exp(-z²-z⁴/6)` has `V=g''/g` with `V(0)<0` and `V` strictly increasing on `[0,∞)`, but central signed reflected rank-three D1 equals `-87040`.

## Goal
Kill the generic Riccati/Sturm bridge from the proved theta facts `V(0)<0` and monotonicity of `V` to the finite TCD D1 gate toward RH.

## Gates
- [x] 0 → 1: corpus-derived exact countermodel
- [x] 1 → 2: closed differentiation/ODE proof
- [x] 2 → 3: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4: publication-ready

## Proof
`g''=Vg` with
`V(x)=-2+2x²+(8/3)x⁴+(4/9)x⁶`; its derivative is positive for `x>0`.
Evenness kills odd central jets. Differentiating `g''=Vg` gives
`(g₀,g₂,g₄,g₆,g₈)=(1,-2,8,0,-1120)`, hence reflected jets
`(p₀,p₂,p₄,p₆,p₈)=(1,-4,40,-480,2240)` and D1 `=-87040`.

## No-go closure
- **Exact killing theorem/mechanism:** monotone Schrödinger potential controls a third-order Riccati margin but not eighth-order reflected Hankel orientation.
- **Strongest positive survivor:** the missing TCD D1 interval requires theta-specific quantitative modular/source geometry beyond potential monotonicity and its central sign.
- **New insight:** generic Sturm comparison cannot discharge the finite TCD gate.
- **Status:** `RHTower.TCDMonotoneSchrodingerNoGo.monotoneSchrodinger_rankThreeD1_noGo` in `RHTower/TCDMonotoneSchrodingerD1NoGo.lean`; targeted build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`; no exact arXiv collision found through 2026-08.
