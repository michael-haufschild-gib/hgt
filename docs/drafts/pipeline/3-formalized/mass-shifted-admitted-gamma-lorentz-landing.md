# Mass-shifted admitted Gamma--Lorentz landing

- **ID:** MSST-AGLL-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4) / NO-GO CLASSIFICATION
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, after conjecture 40
- **Statement:** On each strict-right upper representative of an off-line Xi quartet, the actual
  cooriented `(2,3)` Gamma exterior and the odd shifted-Hankel mixed feature admit a canonical
  positive normalization whose bilinear landing is exactly the even Lorentz shear; consequently
  Gamma orientation supplies no additional sign beyond that shear.

## Goal

Construct the requested source-first, admission-sensitive typed landing before reflection
aggregation. Determine hostilely whether it produces the missing strict sign or only transports
the already-open adaptive null-feature sign.

## Gates

- [x] 0 → 1  in-progress: exact right-upper admission, source and target types, hostile attack
- [x] 1 → 2  fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [x] 2 → 3  formalized: exact Lean theorem, direct and targeted builds, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper not claimed

## Internal frontier

- `[CORPUS]` `xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge` factors the
  actual Gamma exterior as centered Xi rate times a strictly positive gauge.
- `[CORPUS]` `xiShiftedApertureLorentzShearTerm_eq_phaseWeight_mul_mixed` factors the even marked
  Lorentz shear as shifted-atom imaginary phase times the odd mixed feature.
- `[CORPUS]` `XiRightUpperZeroCopy` is one strict-right upper representative per off-line quartet;
  `xiWardQuadrupleEmbed` restores all four functional-equation/Schwarz images.
- `[LOCAL-RESEARCH]` fixed-corona linear reporters with product-continuous lifts vanish, while
  odd-by-odd polarization survives reflection. No declaration identifies centered Xi rate with
  shifted reciprocal phase.

## External frontier

- `[LITERATURE]` Suzuki, arXiv:1204.1827, constructs the Xi canonical system unconditionally only
  for parameter `omega>1`; extension to every positive parameter is itself an RH criterion.
- `[LITERATURE]` Suzuki, arXiv:2301.00421v3, obtains the Weil Hilbert/de Branges space under RH and
  records unconditional auxiliary spaces, but positivity remains equivalent to RH.
- `[LITERATURE]` Salazar, arXiv:2606.31647v2, obtains strict total positivity from positive
  exponential/Mellin moment representations. It does not orient an adaptive signed discrepancy.
- `[LITERATURE]` Berg--Szwarc, arXiv:1405.7267, shows finite-mass Hankel determinant conditions
  require the full positivity pattern; determinant nonnegativity alone does not supply PSD.

No external source supplies a Gamma-to-adaptive-null incidence or a sign theorem for the first
omitted shifted-Xi coupling.

## Conjecture loop

### Conjecture 41 — right-upper admission makes every nonzero bilinear atom positive

`[CONJECTURE]` Multiplying the positive right-upper Gamma exterior by the marked null feature
should give a positive atom whenever the feature is nonzero.

**Hostile verdict: `FALSE`.** Right-upper admission fixes the signs of centered Xi rate and shifted
atom imaginary phase, but the remaining mixed amplitude is a product of a sheared real evaluation
and an imaginary polynomial evaluation. Neither null incidence nor upper-half admission fixes its
sign. Existing tied-power/full-support carrier countermodels already show that generic adaptive
null data can carry either total crossing sign.

**Positive survivor:** identify the exact positive gauge relating Gamma orientation to shifted
phase, then classify what sign information the landing can and cannot add.

### Conjecture 42 — centered Gamma orientation is the shifted phase in another gauge

Let `rho` be a strict-right upper Xi support point, `z=(rho-1/2)(-i)`,
`a=2 Re(rho)-1`, and `lambda_y=1/(z^2+y)`. Then

```text
Im(lambda_y) * |z^2+y|^2 = Im(rho) * a.
```

Thus `a = A_y(rho) Im(lambda_y)` with
`A_y(rho)=|z^2+y|^2/Im(rho)>0`. Combining this with Gamma factorization and
the Lorentz shear factorization yields one positive normalization of

```text
GammaExterior(a) * MixedFeature_y(P,rho)
```

equal to the Lorentz shear atom.

**Hostile verdict: `SURVIVES PRELIMINARY ATTACK`.** The exact phase identity is not an RH
criterion and does not use target positivity. Its positive normalization exists precisely on the
right-upper admission domain, before functional-equation/Schwarz aggregation.

### Conjecture 43 — positive normalization creates a new strict sign

`[CONJECTURE]` The Gamma-normalized landing should have a stronger sign than the Lorentz shear it
targets.

**Hostile verdict: `FALSE`.** The landing equals the shear, and its normalization relative to the
raw Gamma/mixed product is strictly positive. Hence

```text
RawGammaMixedLanding > 0  <->  LorentzShear > 0,
RawGammaMixedLanding = 0  <->  LorentzShear = 0.
```

The source Gamma factor changes gauge and prevents orientation loss, but supplies no new sign.
Any claimed strictness from this factorization alone is circular.

### Conjecture 44 — admission loses the completed reflection aggregate

`[CONJECTURE]` Selecting one strict-right upper representative may discard the completed quartet
observable.

**Hostile verdict: `FALSE`.** Shifted reciprocal square is invariant under functional-equation
reflection and conjugates under Schwarz conjugation. The Lorentz shear is invariant under all four
Klein images. Therefore the complete quartet sum is exactly four times the admitted landing.
Admission removes cancellation without losing the completed observable.

## Paper proof `[PAPER-PROVED]`

Let `q` be a strict-right upper Xi zero copy, `rho` its support point,
`mu=xiZeroCopyReciprocalSquare(q)`, and

```text
lambda = mu/(1+y*mu),       a = 2*Re(rho)-1.
```

For `y>0`, both `rho-1/2` and `1+y*mu` are nonzero. Existing exact coordinate formulas give

```text
Im(mu) = 2*(Re(rho)-1/2)*Im(rho) / normSq(rho-1/2)^2,
Im(lambda) = Im(mu) / normSq(1+y*mu).
```

Define

```text
A_y(q) = normSq(rho-1/2)^2 * normSq(1+y*mu) / Im(rho).
```

Right-upper admission gives `Im(rho)>0`; both norm-square factors are strictly positive. Thus
`A_y(q)>0`, and substitution proves the division-free phase identity

```text
a = A_y(q) * Im(lambda).                                      (1)
```

Let `G_a(q)>0` be the actual fixed `(2,3)` Gamma gauge and `E_a(q)` the corresponding cooriented
Gamma exterior. Corpus factorization gives

```text
E_a(q) = a*G_a(q).                                            (2)
```

For a real polynomial `P`, let `M_y(P,q)` be its odd mixed longitudinal/transverse feature and
`S_y(P,q)` its even Lorentz shear. Corpus factorization gives

```text
S_y(P,q) = (2*Im(lambda)*norm(lambda)/Re(lambda))*M_y(P,q).    (3)
```

The shifted response has positive real part and nonzero norm. Define the strictly positive
admission normalization

```text
N_y(q) = 2*norm(lambda) /
  (Re(lambda)*A_y(q)*G_a(q)).
```

Define raw and normalized source-first landings

```text
R_y(P,q) = E_a(q)*M_y(P,q),
L_y(P,q) = N_y(q)*R_y(P,q).
```

Equations (1)--(3) give, without division by centered rate,

```text
L_y(P,q) = S_y(P,q).                                         (4)
```

Since `N_y(q)>0`, (4) proves the exact sign and zero equivalences between the raw Gamma/mixed
landing and Lorentz shear.

For the four divisor images of `q`, functional-equation reflection sends the centered spectral
point to its negative and hence fixes its reciprocal square; Schwarz conjugation conjugates the
shifted reciprocal square; critical-line reflection does the same. Direct substitution in the
real-polynomial shear shows invariance under every image. Consequently

```text
sum_(epsilon in Bool x Bool)
  S_y(P, xiWardQuadrupleEmbed(epsilon,q)) = 4*L_y(P,q).        (5)
```

Taking `P=Polynomial.ofFn N c` makes (4)--(5) coefficient-faithful to the same adaptive null vector
`c` whose factorial-diagonal source representation is `P^sharp`. No null-incidence premise is
needed for the landing identity; at actual null incidence it specializes without changing gauge.

Hostile check: no step assumes positivity of `S_y`, a first-crossing exclusion, RH, or a global
linear corona reporter. The construction is pointwise bilinear and performed on the admitted
quartet representative before aggregation.

## No-go closure

- **Exact killing theorem/mechanism:** positive normalization makes the raw Gamma/mixed landing
  sign-equivalent to Lorentz shear. Upper admission aligns odd coordinates but leaves adaptive
  mixed amplitude signed.
- **Strongest positive survivor:** exact positive-gauge landing, preservation of zero/sign, and
  exact recovery of the complete four-image shear aggregate.
- **New insight:** Gamma and Lorentz orientations are one divisor coordinate in different positive
  gauges. Missing producer is not another orientation map; it is a source law on the remaining
  mixed amplitude or its adaptive aggregate.
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]` in
  `RHTower/XiShiftedHankelAdmittedGammaLorentzLanding.lean`. Direct `lake env lean` and targeted
  module build pass. Six capstone declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`. Repository lint reaches the new module through the `RHTower` umbrella; its only
  failures are unrelated concurrent reachability gaps for `HTGeometry.AbelianZetaGas.Core`,
  `HTGeometry.AbelianZetaGas.GibbsLaw`, `HTGeometry.AbelianZetaGas.Normalization`,
  `HTGeometry.ConstitutiveNaturalPowerNormalization`, `HTGeometry.ContinuousMapLocallyConvex`,
  `HTGeometry.FiniteDimensionalOperatorAlbertiLaw`, and
  `HTGeometry.SeparableBuresPositiveReporterLaw`.

## Log

- 2026-08-09 — opened after internal and external frontier audit; conjecture 41 killed, conjecture
  42 active.
- 2026-08-09 — conjecture 42 paper proof closed; conjecture 43 killed by positive-gauge
  sign-equivalence; conjecture 44 killed by exact quartet recovery. Promoted to Stage 2 before Lean.
- 2026-08-09 — exact paper theorem formalized. Targeted build passed (11,693 jobs); capstone axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Promoted to Stage 3.
- 2026-08-09 — global formal lint audited: new module is reachable; only seven unrelated
  concurrent `HTGeometry` umbrella omissions remain.
