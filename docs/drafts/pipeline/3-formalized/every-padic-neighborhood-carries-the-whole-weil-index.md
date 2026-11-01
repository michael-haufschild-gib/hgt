# Every p-adic neighborhood carries the whole Weil index

- **ID:** AKG-PADIC-LOCAL-INDEX
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3110/argon.md`, §2.4.
- **Lean:** `AdelicKreinGeometry/EveryPadicNeighborhoodCarriesTheWholeIndex.lean`.

## Exact statements

For a prime `p` and `n≥0`, let

```
H(p,n) = {u∈ℚ>0 : |u|p=1, |u−1|p<1/(n+1)}.
```

1. `log H(p,n)` is dense in `ℝ`.
2. `negIndex(ratCorr restricted to H(p,n)) = negIndex(ratCorr)`.
3. Every global value of `ratCorr` lies in the closure of its values on `H(p,n)`.
4. For each `p`, some fixed `ε>0` satisfies: every `H(p,n)` contains `u` with
   `‖ratCorr(u)−ratCorr(1)‖≥ε`. Hence `ratCorr` is not p-adically continuous at `1`.

## Dependency-closed paper proof

The ultrametric inequality and `|uv−1|p≤max(|u−1|p,|v−1|p)` on p-adic units show
that `H(p,n)` is a subgroup. Inversion preserves `|u−1|p` there.

The real and p-adic absolute values on `ℚ` are nontrivial and inequivalent.
Weak approximation supplies, for every `x>0` and every `δ>0`, a rational `q`
with `|q−x|<min(δ,x)` and
`|q−1|p<min(1,1/(n+1))`. Thus `q>0`, `|q|p=1`, and `q∈H(p,n)`.
Continuity of logarithm gives statement 1.

Apply the existing dense-shift orbit-kernel index theorem to the subgroup
homomorphism from `H(p,n)` to the rational Hecke lattice. The cubic-spline
transform sees every right-hand zeta zero, exactly as for the full rational
slope group. This proves statement 2, including infinite index.

Write `ratCorr(u)=splineCorr(−log u)`. The established real continuity of
`splineCorr` and statement 1 prove statement 3.

The existing nonzero coprime mixed difference of `ratCorr` implies that it is
nonconstant. Choose `v` with `d=‖ratCorr(v)−ratCorr(1)‖>0`. Statement 3 gives,
in every `H(p,n)`, a value within `d/2` of `ratCorr(v)`. The triangle inequality
then gives statement 4 with `ε=d/2`. Since `1/(n+1)→0`, continuity at `1`
would contradict this fixed oscillation.

## Exact obstruction and positive survivor

- **Obstruction:** the globally defined Weil dilation correlation cannot be extended
  continuously to `ℚp×`. Compact Fourier support of local indicator functions does
  not transfer to this correlation.
- **Positive survivor:** every principal-unit resolution retains the entire Weil
  negative index and approximates every global correlation value.
- **Scope:** no RH assumption, no finite-index assumption. This does not rule out a
  comparison retaining genuinely global data. Other prime valuations are unrestricted;
  finite-idèle unit neighborhoods impose additional conditions and are not covered.
- **Scientific status:** corpus-new application of weak approximation and the existing
  dense-shift index law; no external novelty claim.

## Validation

- [x] Direct checks of both modules with `lake --old env lean`; no umbrella build.
- [x] Transitive axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
- [x] Umbrella imports; umbrella not compiled.

## Lean declarations

- `negIndex_ratCorr_padicPrincipalUnits` — exact index preservation.
- `exists_padicPrincipalUnit_ratCorr_near` — every global value remains approximable.
- `exists_uniform_padic_ratCorr_oscillation` — one positive oscillation at every resolution.
- `not_padic_continuous_ratCorr` — no p-adic modulus at the identity.
