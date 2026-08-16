# SP-E Stokes-wall Hilbert--Schmidt energy floor

- **ID:** SP-E-WALL-HS-FLOOR
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM
- **Source:** corpus audit beyond P-G105O/P-G105P
- **Statement:** P-G105K child Hilbert--Schmidt energy stays uniformly positive as physical aperture `d → 0+`, despite every fixed prime coordinate vanishing.

## Goal

Prove nontrivial SP-E divisor retention at wall at level of determinant second jet, without target fitting, PNT recomputation, or assumed limit operator. This attacks aperture-wall collapse gate left after ordinary determinant and cofinal local-uniformity.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and attack identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: closed Lean theorem, target-only Olean and kernel audit
- [ ] 3 → 4 publication-ready: standalone theorem/proof/certificate

## Corpus audit

Queries run before conjecturing:

- `SP-E prime Gamma signed-permutation Eulerian limit`
- `Stokes cofinal child kernel d tends zero Hilbert Schmidt norm`
- `aperture wall child kernel mass escape determinant`
- `routePPrimitiveGammaJuliaStokesCofinalChildKernel normSq tsum`
- `second determinant jet Stokes wall child`
- `X power six one minus X cube prime aperture moment`

Corpus already proves P-G105K exact cubic Schur law, P-G105M trace class, P-G105N ordinary determinant, P-G105O cofinal local-uniformity, P-G105P balanced square law, and right-wall first-trace quantization `W(d) → 4`. Search found no Hilbert--Schmidt wall floor or determinant second-jet retention theorem.

## Conjecturing loop

### C1 — limit operator in fixed prime coordinates

**Failed.** Every fixed transported prime weight tends to zero while total trace tends to four. Coordinatewise/trace-norm limit is mass escape, not a nonzero fixed operator.

### C2 — diagonal energy retains wall mass

**Failed.** Fixed-coordinate diagonal squares can vanish under diffuse prime mass. Off-diagonal cubic coherence is load-bearing.

### C3 — scaled-moment coherence floor

Set

```text
w_d(p) = 8 d log(p) p^(-1-2d),
X_d(p) = p^(-2d),
M(d) = sum_p w_d(p) X_d(p)^6 (1-X_d(p))^3.
```

Exact dilation identity gives

```text
M(d) = W(7d)/7 - 3W(8d)/8 + W(9d)/3 - W(10d)/10,
```

so existing `W(cd) → 4` implies `M(d) → 1/210`.

For `a=2d log p`, `b=2d log q`, exact cubic coherence is

```text
C(a,b)=64 a^3 b^3/(a+b)^6.
```

Using `1-exp(-a) ≤ a` and `1+a ≤ exp(a)` gives

```text
C(a,b) ≥ 64 [exp(-6a)(1-exp(-a))^3]
                 [exp(-6b)(1-exp(-b))^3].
```

Hence full child energy satisfies `E(d) ≥ 64 M(d)^2`; eventually `E(d) ≥ 4/11025`. This proves noncollapse of SP-E square-coordinate quadratic energy without constructing a wall operator. Passing this invariant to a determinant second jet is the next gate.

## Formal theorem

Module:

`GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyFloor`

Main declarations:

- `wallCoherenceMoment_eq_current_combination`
- `tendsto_wallCoherenceMoment_nhdsGT_zero`
- `wallCoherenceMoment_product_le_kernel_normSq`
- `wallHilbertSchmidtEnergy_ge_moment_sq`
- `eventually_wallHilbertSchmidtEnergy_ge`

Direct source elaboration and target Olean emission passed. Kernel audit for limit,
energy comparison, and eventual floor reports only Lean's standard logical
dependencies: `propext`, `Classical.choice`, and `Quot.sound`.

## Falsification conditions

C3 fails if any of these exact identities is false: transported weight dilation, rpow/exponential conversion, cubic coherence rescaling, summable double-series comparison, or the `W(cd) → 4` composition. If C3 fails, retain strongest exact moment or finite-section lower bound and pivot to a logarithmic band argument.

## Log

- 2026-08-16 — created after corpus-first audit; C1 and C2 rejected; C3 selected.
- 2026-08-16 — C3 proved on paper and in Lean; exact wall moment `1/210` and energy floor `4/11025` closed. Umbrella wired; route map left unchanged.
