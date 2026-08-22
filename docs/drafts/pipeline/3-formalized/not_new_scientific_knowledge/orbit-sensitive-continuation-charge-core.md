# Orbit-sensitive continuation forces inverse-horizontal charge

- **ID:** `orbit-sensitive-continuation-charge-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean file:**
  `formal/GaloisForLFunctions/RHTower/OrbitSensitiveContinuationCharge.lean`
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/13-constraint-carrier-calculus/orbit-sensitive-continuation-horizontal-charge-norm-law.md`
- **Statement:** A simple pole at horizontal depth `a` has bounded energy on any fixed line above
  it, but its crossed-residue energy is proportional to `1/a`. Hence no finite uniform fixed-line
  energy bound controls every crossing depth, and any bounded residue graph must pay an explicit
  inverse-horizontal domain charge.

## Formalized result

For `0<a<Y`, residue `c`, and ordinate `gamma`, Lean defines the pole sampled on `Im z=Y` and its
causal contour-jump mode. It proves the actual integral identities

```text
integral_R |c/(x+iY-(-gamma+ia))|^2 dx
  = pi |c|^2/(Y-a),

integral_0^infinity |c exp(-at+i gamma t)|^2 dt
  = |c|^2/(2a).
```

Their exact energy amplification is

```text
(Y-a)/(2 pi a).
```

For every fixed `Y>0` and every proposed finite squared bound `M^2`, Lean constructs an
`a in (0,Y)` whose amplification is strictly greater than `M^2`. It then proves the quantified
nonexistence theorem: there is no single fixed-line energy constant controlling all crossed pole
depths. Conversely, if a domain budget `D` and residue-map bound `M` do control one pole, Lean
forces

```text
(|c|^2/(2a))/M^2 <= D.
```

This is the positive carrier law: inverse-horizontal residue charge must appear in the graph norm.

The same file reuses `FiniteOfflineCauchyEnergy.lean`, `FiniteOfflineCauchyL2.lean`, and
`XiRationalQuartetGauge.lean` to identify the two right-half modes of a centered FE--Schwarz
quartet with actual zeros of the formalized gauge. For multiplicity `m`, it proves the exact
residue-profile integral

```text
4m^2/a + 4m^2 a/(a^2+gamma^2),
```

and therefore the forced lower charge `4m^2/a`.

## Main declarations

- `norm_fixedLinePoleProfile_sq`
- `integral_norm_sq_fixedLinePoleProfile`
- `norm_crossedPoleResidueProfile_sq`
- `integral_norm_sq_crossedPoleResidueProfile`
- `crossedPole_energy_ratio`
- `exists_crossedPole_energy_ratio_gt`
- `no_uniform_crossedPole_energy_bound`
- `domainBudget_ge_inverseHorizontalCharge`
- `centeredQuartetGauge_symmetricQuartetPoint_zero`
- `symmetricQuartet_cauchyEnergy`
- `integral_norm_sq_symmetricQuartetProfile`
- `symmetricQuartet_cauchyEnergy_ge_inverseHorizontal`

## Reuse and placement

The fixed-line integral reuses the exact Cauchy integral
`integral_inv_sq_add_sq_univ` from `XiThetaSquareRateBoundary.lean`. The crossed mode and quartet
integrals reuse the exponential and finite Cauchy-Gram infrastructure already present in the
RHTower. The module is imported by `formal/GaloisForLFunctions/RHTower.lean` beside the finite
off-line energy modules.

## Boundary of the certificate

Lean now certifies the exact one-pole obstruction, the forced graph charge, and the actual
right-half quartet residue energy. It does not yet formalize the paper's four-pole fixed-line
triangle estimate for the full symmetric logarithmic correction. More importantly, it does not
construct the pointed Xi continuation graph or prove the source-specific upper bound
`C_E(0,0)<=4`. The theorem excludes a universal ordinary-Hardy continuation; it leaves the exact
Xi-pointed charged graph as the live direct Hilbert--Pólya carrier.

## Gates

- [x] exact fixed-line pole energy formalized
- [x] exact crossed-residue energy formalized
- [x] exact amplification and unbounded-depth theorem formalized
- [x] positive inverse-horizontal domain-budget law formalized
- [x] actual FE--Schwarz right-half gauge pair identified
- [x] exact symmetric-pair residue integral and lower charge formalized
- [x] RHTower aggregate import added
- [ ] full four-pole fixed-line norm bound formalized
- [ ] pointed Xi charged continuation graph constructed
- [ ] source-specific four-unit upper bound proved
