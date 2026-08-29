# S6F refined-cone exact geometry

Date: 2026-08-29  
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Question

On the sharper cone already proved without computation, does native D1 acquire global
wall-coordinate monotonicity or a simpler upper-face certificate? Either outcome changes the
shortest conceptual proof route. The run also rechecks scale first variation, clock-square second
variation, mixed derivatives, and exact seam/outer faces in refined coordinates

```text
X = 191/10 + (37/5)w + S,
y = 13/32 + w/32 + eta(1/160+w/32),
S>=0, 0<=w<=9/100, 0<=eta<=1.
```

## Outcome

- Direct D1 remains strictly positive: all 13,975 exact half-prism Bernstein coefficients are
  positive.
- Scale geometry remains strong: all 12,750 coefficients of `dD1/dS` and all 11,550 of
  `d²D1/dS²` are positive.
- Clock-square concavity remains strict: all 13,325 coefficients of `d²D1/dw²` are negative;
  all 13,000 coefficients of the third derivative are positive.
- **Global wall monotonicity is still false as a coefficient certificate.** `dD1/deta` has 1,772
  negative, 11,332 positive, and 312 zero Bernstein coefficients. Both the second wall derivative
  and all tested mixed first derivatives are also mixed. Refining the cone does not resurrect this
  shortcut.
- The upper-wall clock derivative is mixed (551 negative, 73 positive coefficients), so direct
  upper-wall monotonicity in `w` is also unavailable.
- **Positive survivor:** after scale reduction and clock concavity, the outer face has a compact
  exact certificate. All 24 Bernstein coefficients of `-dD1/deta` on that face are strictly
  positive, and all 25 coefficients of its value are positive. Seam face is independent of
  `eta` and positive.

## Consequence

Sharpened direct-D1 proof architecture is now rigid:

1. prove scale increase conceptually and set `S=0`;
2. prove clock-square concavity conceptually and reduce to `w=0` or `w=9/100`;
3. use existing seam positivity;
4. prove one univariate outer-face decrease and its upper-corner positivity.

Neither wall interpolation nor upper-wall clock monotonicity can replace step 2. Computation should
now mine determinant first/second-variation identities and a compact outer-face algebraic
decomposition, not search more coordinate monotonicities.

## Reproduction

RunPod used 12 exact SymPy workers. Scripts reconstruct native D1 from the source-positive Lie
recursion; no stored polynomial is taken as input. Exact run and structural verifier passed.
`results.json`, logs, environment metadata, scripts, and `SHA256SUMS` are included.

No coefficient, digest, or sign count in this folder may be imported into Lean.
