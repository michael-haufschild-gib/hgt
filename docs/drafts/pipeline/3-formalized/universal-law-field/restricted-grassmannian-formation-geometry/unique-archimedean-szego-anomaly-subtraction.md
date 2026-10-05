# Unique archimedean Szegő anomaly subtraction

- **ID:** ULF-UASA-001
- **Stage:** 3-formalized
- **Claim status:** `[PAPER-PROVED]`; `[NOVELTY UNVERIFIED]`
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-CCRHD-001`, `ULF-CTRFM-001`; corpus modules
  `HedenmalmThetaKernelEnergy`, `ThetaCarrierPolarizationFisher`, `SzegoOuterBoundary`,
  `SzegoOuterCyclic`, `DiskMultiplierInnerOuterFactor`
- **Surviving RH edge:** metric anomaly coefficient and scalar completion are now forced; an
  oriented doubled theta/Poisson boundary identification remains open.

## 1. Higher-law interpretation

The prime-collision and theta gauges have the same contrast colligation but inequivalent marked
spectral measures.  Their relative Radon--Nikodym half-density is the natural completion field.
`ULF-CTRFM-001` proved that this field is too singular at unit contrast for every fixed critical-
strip tilt.

The singularity is not arbitrary.  Literal theta formation has a two-sided first-atom envelope

```text
k(x) asymp exp(9|x|/2-pi exp(2|x|)).                 (UASA.1)
```

The term `pi exp(2|x|)` is therefore a universal archimedean metric anomaly.  This card proves
that, throughout the punctured critical strip, subtracting exactly that term is the unique scalar
subtraction which turns the prime--theta relative density into a Szegő weight.  The residual
completion is outer and has no finite-dimensional inner defect.

The scalar construction nevertheless cannot carry the reflection-odd unsquared source amplitude.
Thus the result fixes the metric leg and simultaneously proves that orientation needs a separate
conjugate/indefinite leg.

## 2. Two contrast laws and their modular density

Let

```text
h(v)=(105/16)v^2(1-v^2)^2,             -1<v<1,       (UASA.2)
```

the source Hodge contrast density of `ULF-CCRHD-001`.  Let `k=thetaCuspFullSource`.  The literal
theta envelope theorem supplies constants `0<C_-<=C_+<infinity` such that, for all real `x`,

```text
C_- exp(9|x|/2-pi exp(2|x|))
 <=k(x)<=
C_+ exp(9|x|/2-pi exp(2|x|)).                         (UASA.3)
```

The positive-half inequalities are
`thetaCuspFullSource_ge_envelope` and `thetaCuspFullSource_le_envelope`; evenness supplies the
negative half.

For `b>0`, define the balanced theta law

```text
Z_b=integral_R cosh(bx)k(x)dx,
d nu_b(x)=Z_b^(-1)cosh(bx)k(x)dx,
sigma_b=(tanh(b .))_*nu_b.                            (UASA.4)
```

Superexponential decay gives `0<Z_b<infinity`.  Write

```text
x_b(v)=artanh(v)/b,
Q(v)=(1+|v|)/(1-|v|).
```

**Lemma UASA-A (exact theta contrast density).**  On `(-1,1)`,

```text
d sigma_b(v)=s_b(v)dv,
s_b(v)=k(x_b(v))/(b Z_b(1-v^2)^(3/2)).                (UASA.5)
```

Consequently the relative modular density is

```text
r_b(v)=h(v)/s_b(v)
 =(105/16)bZ_b v^2(1-v^2)^(7/2)/k(x_b(v)).            (UASA.6)
```

**Proof.**  The derivative of `v=tanh(bx)` is `b sech(bx)^2=b(1-v^2)`, while
`cosh(bx)=(1-v^2)^(-1/2)`.  Substitution in `(UASA.4)` gives `(UASA.5)` and division gives
`(UASA.6)`. QED.

## 3. Exact anomaly expansion

For a real counterterm coefficient `c`, put

```text
A_b(v)=Q(v)^(1/b)=exp(2|x_b(v)|),
r_(b,c)(v)=r_b(v)exp(-c A_b(v)).                      (UASA.7)
```

**Lemma UASA-B (bounded-remainder expansion).**  There is a bounded function `epsilon_b` on
`(-1,1)` such that, away from `v=0`,

```text
log r_(b,c)(v)
 =(pi-c)A_b(v)
  -(9/(4b))log Q(v)
  +2log|v|+(7/2)log(1-v^2)
  +epsilon_b(v).                                     (UASA.8)
```

**Proof.**  From `(UASA.3)`,

```text
log k(x)=9|x|/2-pi exp(2|x|)+epsilon(x)
```

with bounded `epsilon`.  Also `|x_b(v)|=(2b)^(-1)log Q(v)`.  Insert this identity and `(UASA.6)`
into `(UASA.7)`; absorb the fixed positive factor `(105/16)bZ_b` into `epsilon_b`. QED.

The logarithmic terms in `(UASA.8)` are integrable on `(-1,1)`.  At either endpoint,

```text
A_b(v) asymp 2^(1/b)(1-|v|)^(-1/b).                  (UASA.9)
```

Hence `A_b` is integrable exactly when `b>1`.

## 4. Unique critical-strip subtraction

**Theorem UASA-C (unique Szegő counterterm).**  For `0<b<=1`,

```text
log r_(b,c) in L1(-1,1)  iff  c=pi.                  (UASA.10)
```

For `b>1`, `log r_(b,c)` is integrable for every real `c`.

**Proof.**  When `c=pi`, the nonintegrable term in `(UASA.8)` vanishes and every remaining term is
integrable.  When `0<b<=1` and `c!=pi`, divide `(UASA.8)` by `A_b(v)`.  The logarithmic remainder
is `o(A_b(v))`, so the quotient tends to `pi-c` at both endpoints.  Thus
`|log r_(b,c)|` dominates a positive multiple of the nonintegrable `A_b` near each endpoint.
For `b>1`, `(UASA.8)` and integrability of `A_b` give the last assertion. QED.

This is stronger than merely identifying a convenient renormalization.  Inside the horizontal
grade band `0<|a|<=1`, the coefficient `pi` is forced by finite logarithmic completion action.
No zero, divisor, ordinate, or fitted normalizer occurs.

## 5. Residual outer completion

At the forced coefficient, `(UASA.3)` gives two constants `0<d_b<=D_b<infinity` with

```text
d_b P_b(v)<=r_(b,pi)(v)<=D_b P_b(v),                 (UASA.11)
P_b(v)=v^2(1-v^2)^(7/2)Q(v)^(-9/(4b)).
```

Therefore `r_(b,pi)` is integrable, essentially bounded, positive almost everywhere, and has
integrable logarithm.  Compactify the contrast interval by

```text
W_b(theta)=r_(b,pi)(theta/pi),   -pi<theta<pi,        (UASA.12)
```

and extend periodically.  Values at `theta in {0,+-pi}` are irrelevant.

**Theorem UASA-D (canonical residual Szegő factor).**  There is a unique normalized outer function
`D_b` on the disk with `D_b(0)>0` and

```text
|D_b(e^(i theta))|^2=W_b(theta)  a.e.                (UASA.13)
```

It belongs to `H2 intersect H-infinity`, is zero-free in the disk, and multiplication by `D_b` on
`H2` is injective with dense nonclosed range.

**Proof.**  Equations `(UASA.10)`--`(UASA.12)` are precisely the scalar Szegő hypotheses, so the
Herglotz--Riesz exponential of `(1/2)log W_b` gives the normalized outer factor and `(UASA.13)`.
The essential upper bound gives `D_b in H-infinity`; outer functions are cyclic, hence the
multiplication range is dense.  The factor is an exponential and therefore zero-free.  Finally,
`W_b` tends to zero on positive-measure neighbourhoods of the seam and compactified endpoint, so
it has no positive essential lower bound.  An injective closed-range multiplier would be bounded
below, forcing its boundary modulus to have such a lower bound.  Thus the range is not closed.
QED.

The residual completion has no inner factor and no finite-rank Hardy defect.  Its obstruction is
purely nonclosed range.  This is the exact positive survivor of the fixed-scale mismatch.

For comparison, if `0<b<=1` and `c<pi`, then `r_(b,c)` is not integrable; if `c>pi`, it is
integrable but its logarithmic integral is `-infinity`, so every lower-truncated Szegő determinant
collapses to zero.  Only `c=pi` produces a nonzero outer completion.

## 6. Unsquared orientation cannot be scalar Hardy data

The source half-density after metric subtraction is the real odd boundary amplitude

```text
Psi_b(theta)=sign(theta)sqrt(W_b(theta)).             (UASA.14)
```

It is nonzero in `L2`, and its square is the metric boundary value `(UASA.13)`.

**Theorem UASA-E (scalar orientation no-go).**  No function in scalar `H2` has radial boundary
value `Psi_b` almost everywhere.

**Proof.**  If an `H2` function has real boundary values almost everywhere, its imaginary harmonic
part has zero boundary values and hence vanishes in the disk.  The analytic function is therefore
real-valued and constant.  But `Psi_b` is odd and nonzero, hence nonconstant. QED.

Thus the outer factor closes only the reflection-even metric leg.  The unsquared Euler orientation
cannot be reconstructed from it and cannot be included by a scalar phase choice.  Its minimal
causal carrier must contain both Hardy frequency halves; functional-equation doubling then gives
the corpus's four-leg/Krein architecture.

## 7. RH leverage and exact open core

The theorem supplies the subtraction demanded by the relative-completion programme:

```text
literal theta first atom  -> unique pi exp(2|x|) metric counterterm
prime Hodge spectral law  -> residual Szegő weight
residual Szegő weight     -> outer dense-range completion with no inner index.
```

If literal integer/Poisson completion is proved to carry the marked source colligation through the
oriented double of `D_b`, then any strict-right Xi copy would require an additional rank-one inner
Hardy defect.  Outer uniqueness would forbid that defect, forcing neutral horizontal grade and
closing RH by the existing formation-boundary fusion.

`[OPEN CORE]` Derive, from the exact Poisson coface and pole--Gamma countercurrent, a functorial
oriented-double boundary identification whose metric factor is `D_b` and which preserves
outer/inner type.  This must not assume absence of a target inner factor; that is the conclusion.

## 8. Hostile novelty and correctness audit

- `[CORPUS]` The two-sided coefficient-exact theta envelope is already formalized in
  `HedenmalmThetaKernelEnergy`; scalar Szegő construction and cyclicity are formalized in
  `SzegoOuterBoundary` and `SzegoOuterCyclic`.
- `[LITERATURE]` Outer-factor/logarithmic-integral equivalence and spectral Szegő theory are
  classical; see Bessonov--Denisov, *A spectral Szegő theorem on the real line*,
  arXiv:1711.05671, and Simon--Zlatoš, *Higher-Order Szegő Theorems With Two Singular Points*,
  arXiv:math-ph/0409065.
- `[REDISCOVERED]` Radon--Nikodym unitary equivalence and scalar outer factorization are not new.
- `[PAPER-PROVED]` New local delta is the exact prime-Hodge/theta relative density, the sharp
  `b=1` admissibility threshold, and uniqueness of the coefficient `pi` throughout
  `0<b<=1`.
- `[FALSIFIED]` A scalar outer factor cannot preserve the real reflection-odd unsquared current.
- `[NOVELTY UNVERIFIED]` Searches found no external statement of this exact arithmetic fusion;
  no scientific-priority claim is made before Lean proof and independent audit.
- The theorem is not RH and imports no Xi factorization.  It narrows completion to one forced
  metric counterterm and an oriented doubled lift; identifying that lift with actual theta/Poisson
  completion is still the missing selection theorem.

## 9. Lean status

Stage 2 paper proof only.  No Lean code or build was performed during the corpus-audit research
phase.  The exact relative-density, threshold, unique-subtraction, outer-range, and scalar-
orientation statements still require Stage 3 formalization.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.ArchimedeanSzegoCounterterm`, `GaloisForLFunctions.HTGeometry.SzegoWeightOuterMultiplier`, `GaloisForLFunctions.HTGeometry.HardyRealBoundaryConstant`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.HTGeometry.ArchimedeanSzegoCounterterm` (93 constants), with new generic infrastructure `GaloisForLFunctions.HTGeometry.SzegoWeightOuterMultiplier` (40 constants: Szegő outer multipliers of bounded measurable periodic weights) and `GaloisForLFunctions.HTGeometry.HardyRealBoundaryConstant` (5 constants: `H²` functions with real boundary are constant); all axiom-audit clean. `k = thetaCuspFullSource`, `ν_b = thetaBalanceLaw b`, `σ_b = thetaContrastLaw b` (ULF-CTRFM-001), `h = hodgeSpectralDensity`, `A_b = archimedeanAnomaly b`, `r_{b,c} = subtractedModularDensity b c`, `W_b = residualSzegoWeight b`, `D_b = (residualSzego hb).outer`, `Ψ_b = orientationAmplitude b`.

| Claim | Lean declaration |
|-|-|
| (UASA.1)/(UASA.3) two-sided first-atom envelope for all real `x`; bounded remainder `ε` | `thetaCuspFullSource_two_sided_envelope`, `envelopeRemainder`, `exists_abs_envelopeRemainder_le`, `envelopeRemainder_le`, `le_envelopeRemainder` (corpus `thetaCuspFullSource_le_envelope`, `thetaCuspFullSource_ge_envelope`) |
| (UASA.2), (UASA.4) `h`, `ν_b`, `σ_b = tanh(b·)_*ν_b`, `0 < Z_b < ∞` | corpus `hodgeSpectralDensity`, `thetaBalanceLaw`, `thetaContrastLaw`, `thetaBalanceMass_pos` |
| Lemma A, (UASA.5)–(UASA.6): density `s_b(v) = k(artanh v/b)/(bZ_b(1-v²)^{3/2})`, `r_b = h/s_b` | `thetaContrastDensity`, `integral_thetaContrastLaw`, `thetaContrastDensity_tanh`, `image_tanh_mul_univ`, `hasDerivAt_tanh_mul`, `thetaContrastDensity_pos` |
| (UASA.7) `A_b = e^{2∣x_b∣} = Q^{1/b}`, `r_{b,c} = r_b e^{-cA_b}` | `archimedeanAnomaly`, `archimedeanAnomaly_eq_rpow`, `subtractedModularDensity`, `subtractedModularDensity_eq_mul` |
| Lemma B, (UASA.8) `log r_{b,c} = (π-c)A_b + G_b`, `G_b` = logarithmic terms + bounded remainder | `log_subtractedModularDensity`, `anomalyRegularPart`, `integrableOn_anomalyRegularPart`, `integrableOn_log_Ioo`, `integrableOn_log_one_add_Ioo`, `integrableOn_log_one_sub_Ioo`, `integrableOn_artanh_Ioo` |
| (UASA.9) `A_b(v)(1-∣v∣)^{1/b} = (1+∣v∣)^{1/b}`; `A_b ∈ L¹` iff `b > 1` | `archimedeanAnomaly_mul_rpow`, `integrableOn_archimedeanAnomaly_iff_one_lt`, `integrableOn_archimedeanAnomaly_iff` |
| Theorem C, (UASA.10): `log r_{b,c} ∈ L¹(-1,1)` iff `c = π` or `b > 1` | `integrableOn_log_subtractedModularDensity_iff`, `ae_log_subtractedModularDensity` |
| (UASA.11) `d P_b ≤ r_{b,π} ≤ D P_b`, `P_b = v²(1-v²)^{7/2}Q^{-9/(4b)}`; `r_{b,π}` bounded, positive | `residualProfile`, `residualProfile_eq_rpow`, `contrastRatio_rpow`, `subtractedModularDensity_pi_eq`, `subtractedModularDensity_pi_bounds`, `thetaEnvelopeLower_le_upper`, `subtractedModularDensity_pi_le_sq` |
| (UASA.12) compactified periodic weight `W_b`, positive, bounded, measurable, `log W_b` locally integrable; `W_b → 0` at the seam, `1/W_b ∉ L¹` | `angularContrast`, `residualSzegoWeight`, `residualSzegoWeight_pos`, `residualSzegoWeight_le`, `measurable_residualSzegoWeight`, `intervalIntegrable_log_residualSzegoWeight`, `locallyIntegrable_log_residualSzegoWeight`, `not_intervalIntegrable_inv_residualSzegoWeight`, `residualSzego` |
| Theorem D, (UASA.13): unique normalized outer `D_b`, `D_b(0) > 0`, `∣D_b(e^{iθ})∣² = W_b` a.e. (radial and `L²` boundary), `H² ∩ H^∞`, zero-free, outer, multiplication injective with dense non-closed range | `residual_szego_factor`; generic `SzegoWeight.outer`, `SzegoWeight.tendsto_normSq_outer`, `SzegoWeight.ae_norm_sq_boundary_outer`, `ae_norm_sq_diskMultiplierBoundaryFun_eq_of_radial`, `SzegoWeight.outer_zero`, `SzegoWeight.outer_ne_zero`, `SzegoWeight.isOuter`, `SzegoWeight.hardyMul_outer_injective`, `SzegoWeight.denseRange_hardyMul_outer`, `SzegoWeight.not_isClosed_range_hardyMul_outer`, `SzegoWeight.eq_outer_of_isOuter` |
| comparison: `c < π` ⇒ `r_{b,c} ∉ L¹`; `c > π`, `b ≤ 1` ⇒ `r_{b,c} ∈ L¹`, `(log r)⁺ ∈ L¹`, `log r ∉ L¹`, truncated `∫ max(log r, -n) → -∞` | `not_integrableOn_subtractedModularDensity`, `pullback_subtractedModularDensity_ge`, `integrableOn_Ioo_iff_tanh`, `subtractedModularDensity_of_pi_lt`, `tendsto_integral_max_neg_natCast_atBot` |
| (UASA.14) `Ψ_b = sign(θ)√W_b`, `Ψ_b² = W_b` off the seam | `orientationAmplitude`, `orientationAmplitude_sq`, `orientationAmplitude_pos`, `orientationAmplitude_neg` |
| Theorem E: no scalar `H²` function has boundary value `Ψ_b` | `not_exists_hardyDisk_boundary_orientationAmplitude`; generic `hardyDisk_coeff_eq_zero_of_boundary_real`, `hardyDiskBoundary_ae_eq_const_of_real`, `fourierCoeff_neg_of_ae_real` |
| Summary | `unique_archimedean_szego_anomaly_subtraction` |

Theorem C's non-integrability for `c < π` is proved for every `b > 0`. §1, §7 (explicitly marked `[OPEN CORE]`, not a theorem) and §8 are interpretation and audit.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
