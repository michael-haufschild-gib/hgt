# Mass-shifted Hankel boundary Hilbert--charge flow

- **ID:** mass-shifted-hankel-boundary-hilbert-charge-flow
- **Stage:** 3-formalized
- **Type:** CANDIDATE
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** At every positive mass shift, the complete shifted Xi Hankel form is the exact
  difference of a nonnegative sheared-evaluation Hilbert energy and a nonnegative transverse
  charge.  Conjugation makes every longitudinal feature orthogonal to every transverse feature.
  On a singular Hankel face its null polynomial induces an isometric lightlike flag; the
  derivative of its saturated gap is exactly the Krein crossing and completed-source flux.

## Goal

Reinterpret the §9.3 boundary orientation as first variation of an exact longitudinal/transverse
energy saturation.  This must identify a new, source-addressable strict inequality without assuming
RH, positivity of the target Hankel tower, or the desired sign.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure target, exact divisor-side attack, Door passport
  sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem/module, direct compile, target `lake build`, axiom audit;
  module reachable from `RHTower` umbrella.  Repository-wide lint currently fails only on unrelated
  refactor modules missing their umbrella imports; no diagnostic names this module.
- [ ] 3 → 4 publication-ready: standalone paper + Door-2 audit

## Approach

For an atom `λ` with `a = Re λ > 0` and complex polynomial value `w`, use the exact oriented
square law

```text
Re(λ w²)
  = a (Re w - (Im λ / a) Im w)²
    - (|λ|² / a) (Im w)².
```

Sum this identity over multiplicity-exact shifted Xi atoms.  Shifted sector control gives
`(Im λ)² < a²`, hence `|λ|²/a < 2a`; polynomial evaluation is uniformly bounded because positive
Möbius translation does not enlarge an atom.  Both channels are therefore absolutely summable.

For `P_c = Polynomial.ofFn (n+1) c`, the exact shifted trace expansion identifies the channel gap
with `cᵀ H_y c`.  If `H_y c = 0`, then the two nonnegative channels are equal.  The existing
mass-derivative theorem then transports verbatim to this equality gap:

```text
d/dy (HilbertEnergy_y(P_c) - TransverseEnergy_y(P_c))
  = -(2n+1) c_n FirstOmittedCoupling_y(c).
```

The right side is also `-(2n+1)c_n²` times the canonical Krein crossing class.  Thus a right-hand
first crossing is a nonnegative first variation of a saturated longitudinal/transverse balance;
the missing source theorem must force strict decay of this balance, equivalently strict positive
Krein crossing.

### Polarized strengthening `[PROVED HERE]`

Put

```text
L_y(P;q) = sqrt(a_q) (Re P(λ_q) - Im(λ_q)/a_q Im P(λ_q)),
V_y(P;q) = |λ_q|/sqrt(a_q) Im P(λ_q).
```

For real polynomials, line conjugation fixes `L_y(P;q)` and negates `V_y(P;q)`.  Moreover

```text
|L_y(P;q) V_y(Q;q)| ≤ (L_y(P;q)^2 + V_y(Q;q)^2)/2,
```

so the mixed product is absolutely summable and exact conjugation reindexing proves
`sum_q L_y(P;q)V_y(Q;q)=0` for every `P,Q`.  Polarization gives

```text
[P,Q]_y = <L_y(P),L_y(Q)> - <V_y(P),V_y(Q)>.
```

If `P` is the canonical monic polynomial of a size-`n+1` kernel, then the complete kernel row gives
`<L_y(P),L_y(Q)>=<V_y(P),V_y(Q)>` for every `deg Q≤n`; mixed correlations still vanish.  Hence the
null face is an isometric lightlike flag and `XP` is its first out-of-flag defect.

In `0<y<41/2`, momentwise negative-binomial source transport proves

```text
[P,Q]_y = momentInner (Re primeArchShiftedReciprocalMoment y) P Q.
```

Thus the crossing is exactly the zero-free prime--Gamma pairing of `P` with `XP`.  On the whole
Euler ray `y=w²`, the saturated-gap derivative equals
`-(2n+1)c_n*xiShiftedHankelBoundarySourceJet w (n+1) c`; strict decay is exactly projective
archimedean dominance over the oriented Chebyshev discrepancy jet.

## Conjecture loop

1. **Confluent-resolvent producer.** Conjectured that coalescing resolvent kernels supply the
   missing sign. **FAIL:** corpus already contains the complete resolvent ladder and low-rung
   vacuity; this is not new and does not orient the first omitted rung.
2. **All-degree charge domination.** Conjectured that the new squared-Euler charge criterion closes
   the face. **FAIL:** all-degree domination is already equivalent to RH.  At a singular face the
   relevant polynomial lies on equality, so ordinary domination has no remaining sign information.
3. **Ward/Pick positivity.** Conjectured that unconditional strict-right Ward positivity descends to
   the face. **FAIL:** the cofinal boundary-lift corpus proves that off-line zeros survive as a
   transverse negative defect; unconditional interior Pick positivity does not fix boundary
   orientation.
4. **Saturated-channel first variation.** **SURVIVES:** combine shifted all-degree Hilbert/charge
   splitting with null-face incidence and exact boundary flux.  Novel object is not another
   positivity criterion but derivative of an equality case.
5. **Generic Bures/prolate import.** **FAIL:** new Bures rigidity and prolate/integral primitives
   have no theorem mapping their state/channel variables to the completed-source null polynomial.
   Importing them would only rename the missing connector.
6. **Conjugation-isotropy conjecture.** **SURVIVES:** longitudinal feature is even and transverse
   feature odd under the actual Xi line-conjugation equivalence.  Absolute AM--GM domination
   upgrades this to all-degree Hilbert orthogonality, null isotropy, and null-flag channel isometry.
7. **Zero-free source-pair conjecture.** **SURVIVES:** negative-binomial moment transport commutes
   with polarization, making the channel pair gap the prime--Gamma moment pairing and the crossing
   its `P,XP` specialization.
8. **Gamma-sewn contraction / source Rayleigh gap.** **FAIL:** the strict contraction acts on the
   prime--valuation stream and preserves normalized Szegő angles; Rayleigh law assumes coercivity.
   Corpus contains no intertwiner to the null-flag source pairing.  This is the missing theorem,
   not a consequence of those diagonal results.

## Novelty and hostile audit

- Central all-degree Hilbert/charge splitting exists, but not its positive-shift version nor its
  null-face derivative bridge.
- Shifted first-minor dispersion/charge cancellation exists only at degree one and does not encode
  arbitrary singular faces.
- Null self-pairing, Krein crossing, and mass derivative exist separately; corpus search found no
  theorem identifying them as first variation of a globally summable shifted Hilbert/charge
  saturation.
- Corpus search found no shifted all-degree mixed-channel orthogonality, no null-flag channel
  isometry, and no theorem identifying arbitrary polarized channel gaps with the zero-free shifted
  prime--Gamma pairing.
- The result does **not** prove the missing sign.  It strictly reduces the open core to a
  source-conditioned strict cross-channel monotonicity theorem.  Existing sector first-crossing
  countermodel already shows conjugation, safe sector, positive atomic weights, exact mass
  transport, and null isotropy do not orient the first omitted coupling.  Claiming RH from the
  decomposition alone would be circular.

## Door passport

- **Input:** shifted Xi divisor, positive mass shift, finite coefficient vector.
- **Output:** two orthogonal summable Hilbert feature maps, their Krein difference, null-flag
  isometry, zero-free source pairing, and equality-gap derivative.
- **Non-circularity:** all identities use unconditional shifted atom sector, summability, trace
  expansion, kernel incidence, and mass differentiation.
- **Orientation retained:** derivative/crossing keeps terminal coefficient times first omitted
  coupling; no squaring of this product.
- **Remaining source obligation:** prove strict positivity of completed-source pairing
  `momentInner primeArch P (X*P)` at actual null incidence, equivalently strict decrease of channel
  gap or projective archimedean dominance over oriented Chebyshev discrepancy.

## Log

- 2026-08-09 — created in 1-in-progress after corpus/literature novelty audit and three failed
  conjecture routes; dependency closure being checked before Lean.
- 2026-08-09 — paper proof closed for shifted summability, polarized Krein split, conjugation-even/
  odd orthogonality, null-flag isometry, source pairing, and completed-source saturation flow.
  Formalized unconditionally in
  `RHTower/XiShiftedHankelBoundaryHilbertChargeFlow.lean`.
- 2026-08-09 — `lake env lean` and targeted `lake build
  GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryHilbertChargeFlow` passed.  Axiom audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`.  Global lint exception recorded above.

## Marked Lorentz-transfer packet `[PROVED HERE]`

For one shifted atom `lam=a+ib`, put `N=|lam|^2`, `w=P(lam)`,
`s=Re(w)-(b/a)Im(w)`, and `v=Im(w)`.  Multiplication by `X` obeys

```text
s(lam*w)  = ((a^2-b^2)/a)*s - (b*N/a^2)*v,
Im(lam*w) = b*s + (N/a)*v.
```

With `H=a*s^2`, `T=(N/a)*v^2`, `M=sqrt(N)*s*v`,
`tau=(a^2-b^2)/a`, `kappa=N/a`, and `beta=b*sqrt(N)/a`, exact expansion gives

```text
Re (lam*w*(lam*w)) = tau*H - 2*beta*M - kappa*T.
```

The longitudinal and transverse transports are nonnegative.  Ordinary mixed covariance `M` is odd
under line conjugation, but `beta` is odd as well; hence the phase-weighted shear `beta*M` is even
and survives orbit summation.  This is the exact information lost by phase-blind covariance and
distance constructions.

Globally, marked Lorentz transport equals the polarized channel gap at `(P,X*P)`.  In
`0<y<41/2` it is exactly the prime--Gamma moment pairing.  At completed null incidence it is the
intrinsic Krein crossing, and on `y=w^2` its product with the terminal coefficient equals the
completed source jet.  Formal theorem chain:

- `xiShiftedApertureHankelPairTerm_X_mul_eq_lorentzTransport`;
- `xiShiftedApertureLorentzShearTerm_lineConj`;
- `xiShiftedAperturePairGap_X_mul_eq_lorentzCrossingEnergy`;
- `xiShiftedApertureLorentzCrossingEnergy_eq_primeArchMomentInner`;
- `xiShiftedHankelBoundaryNullCrossingForm_eq_lorentzCrossingEnergy`;
- `xiShiftedHankel_terminal_mul_lorentzCrossingEnergy_eq_sourceJet`.

### Conjecture loops 9--16

9. **Volterra-tail positivity. FAIL:** the resolvent ladder only relocates crossing sign to an
   iterated cumulative tail of the signed completed heat weight.  No unconditional sign is gained.
10. **Suzuki backward-tail transfer. FAIL:** its terminal-charge and decay hypotheses do not hold
    for this completed signed source.
11. **Positive null-root orientation. FAIL:** corpus proves real simple roots, not positive roots;
    positive-carrier tied-power countermodels already realize both crossing signs.
12. **Finite KMS/local atomic closure. FAIL:** corpus theorem identifies this closure with RH, so
    invoking it here is circular.
13. **Reverse-Bessel positivity plus PNT remainder. FAIL:** factorial normalization produces
    `t^k/(k!)^2`, whose Hankel obstruction is already formalized; absolute PNT error supplies no
    adaptive degree-uniform coercive floor.
14. **Relative-Connes/Bures orientation. FAIL:** unsquared source phase exists before taking energy,
    but no typed map reaches the shifted null polynomial; Bures squaring removes the marked sign.
15. **Marked Lorentz transfer. SURVIVES:** exact multiplication law exposes a conjugation-even,
    phase-weighted shear and intertwines it with the prime--Gamma source and completed source jet.
16. **Source-conditioned marked dominance. OPEN:** prove that completed Euler--Gamma incidence
    strictly dominates surviving shear plus transverse transport on every adaptive null flag.

### Sharpened no-theatre boundary

`docs/notes.md` is useful only at loop 16: its joint source-conditioning idea must instantiate the
marked Lorentz law above.  Abstract CLG, cotangent, covariance, or Bures realizability without this
typed source-to-null-flag connector does not reduce proof burden.  This packet does not prove the
strict sign or RH.

## Lorentz packet audit

- 2026-08-09 — direct `lake env lean` passed after marked-transfer additions.
- 2026-08-09 — axiom audit of six Lorentz/source bridge theorems reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-08-09 — forbidden-declaration scan is clean; umbrella import is present; targeted
  `lake build GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryHilbertChargeFlow` passed.

## Source-conditioned joint-incidence refinement

### Conjecture loop 17

**Conjecture.** `docs/notes.md`'s source-conditioned joint-realizability pivot should force an
anti-isometry between archimedean and Chebyshev-discrepancy source forms on a singular shifted-Xi
face.

**Hostile audit.** A global anti-isometry is false and overstates available incidence: singular
Hankel data annihilates only null polynomial against finite flag. Correct source-specific survivor
is exact cancellation on this null line, followed by first noncancelling `X`-extension.

For normalized source sequences `A_k(w)` and `Delta_k(w)`, define

```text
A_w(P,Q) = momentInner(A(w), P, Q)
D_w(P,Q) = momentInner(Delta(w), P, Q).
```

Coefficientwise completed-source split gives, for `w > 1/2`,

```text
[P,Q]_(w^2) = A_w(P,Q) + D_w(P,Q).
```

If `P_c` is monic null polynomial of singular `(n+1)` shifted face, then

```text
degree Q < n+1  ->  A_w(P_c,Q) = -D_w(P_c,Q).
```

At first transverse probe,

```text
LorentzCrossing_(w^2)(P_c) = A_w(P_c, X P_c) + D_w(P_c, X P_c),
c_last * (A_w(P_c, X P_c) + D_w(P_c, X P_c)) = CompletedSourceJet_w(c).
```

**Status:** `[LEAN-PROVED][CORPUS-SYNTHESIS]`. This removes every lower-rung source estimate from
open core and identifies strict sign as one relative source-extension coordinate. It does not prove
that coordinate positive.

Formal declarations:

- `xiShiftedApertureArchimedeanSourcePair`;
- `xiShiftedApertureDiscrepancySourcePair`;
- `xiShiftedAperturePairGap_eq_archimedeanSourcePair_add_discrepancySourcePair`;
- `xiShiftedHankelNull_archimedeanSourcePair_eq_neg_discrepancySourcePair_of_natDegree_lt`;
- `xiShiftedApertureLorentzCrossingEnergy_eq_archimedeanSourcePair_add_discrepancySourcePair`;
- `xiShiftedHankel_terminal_mul_sourcePairExtension_eq_sourceJet`.

### Source-pair refinement audit

- 2026-08-09 — direct `lake env lean` passed for full module.
- 2026-08-09 — targeted `lake build
  GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryHilbertChargeFlow` passed.
- 2026-08-09 — all four source-pair theorems depend only on `propext`, `Classical.choice`, and
  `Quot.sound`; target forbidden-declaration scan is clean.
- 2026-08-09 — full corpus lint is temporarily red on unrelated unreachable modules created by
  concurrent RHTower/HTGeometry refactor. Target module is present in RHTower umbrella and is not
  named by any lint error.

## Adaptive reverse-Bessel carrier refinement

### Conjecture loops 18--24

18. **First-singular monotonicity. FAIL:** first-crossing geometry forces the canonical Krein
    crossing nonpositive; geometry cannot also supply the required strict opposite sign.
19. **Global source anti-isometry. FAIL / POSITIVE SURVIVOR:** archimedean and discrepancy forms
    cancel only on the adaptive null line against the completed lower flag. The first `X`-extension
    is the sole surviving source coordinate; this survivor is formalized above.
20. **Lower-polynomial gauge removal of Lorentz shear. FAIL:** changing the extension by a lower
    null-flag probe leaves total crossing invariant.
21. **Flat-quadrature Christoffel coercivity. FAIL:** generic positive carriers and exact lower
    moments permit either sign at first extension.
22. **Reverse-Bessel kernel positivity. FAIL / POSITIVE SURVIVOR:** each radial kernel is positive,
    but the adaptive coefficient combination is controlled by a signed factorial transform. The
    exact combined-carrier law below survives.
23. **Source-normal/divisor orientation shortcut. FAIL:** newer divisor-support orientation laws
    classify off-critical horizontal displacement but provide no typed map to the adaptive shifted
    Hankel null line.
24. **Componentwise PNT domination. FAIL AS STATED:** absolute errors for individual source moments
    do not control a coefficient-cancelled null packet. A possible survivor would have to be a
    relative operator estimate uniform on actual null flags.

For base order `r`, coefficients `c_j`, and

```text
P^sharp_(r,c)(T) = sum_j c_j T^j / ((r+j)!)^2,
A(u,x,w) = u * (w * log x + u/2),
T(u,x,w) = A(u,x,w) / (2*w^2),
```

the exact normalized boundary radial packet is

```text
sum_j c_j * radialBesselKernel(r+j, 1/2+w, x)
        / completedSourceMomentScale(r+j,w)
= x^(-(1/2+w)) / (2^r*w^(2*r+1))
    * integral_(0,inf) exp(-u) * A(u,x,w)^r * P^sharp_(r,c)(T(u,x,w)) du.
```

For `w>0`, `x>=1`, and `u>0`, carrier argument is nonnegative and Gamma density is strictly
positive. Hence crossing sign is distribution of positive carrier across sign intervals of
`P^sharp`; raw kernel positivity, absolute PNT bounds, and marginal source estimates cannot orient
it.

**Status:** `[LEAN-PROVED][CORPUS-SYNTHESIS][ROUTE-KILL]`. This is a strict reduction of proof
burden, not RH: missing theorem is source-specific oriented discrepancy/interlacing relative to
`P^sharp`, or equivalent adaptive relative operator control.

Formal declarations:

- `integrableOn_reverseBesselPositiveIntegrand`;
- `xiShiftedBoundaryFactorialCarrierPolynomial`;
- `xiShiftedHankelBoundaryRadialKernel`;
- `xiShiftedBoundaryFactorialCarrierArgument_nonneg`;
- `xiShiftedBoundaryFactorialCarrierDensity_pos`;
- `radialBesselKernel_half_add_eq_reverseBesselPoly`;
- `xiShiftedHankelBoundaryRadialKernel_eq_factorialCarrierIntegral`.

### Adaptive carrier audit

- 2026-08-09 — targeted `lake build
  GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryReverseBesselCarrier` passed.
- 2026-08-09 — axiom audit of all five public carrier theorems reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-08-09 — target forbidden-declaration scan is clean; new module is imported by RHTower
  umbrella.

## Combined arithmetic-discrepancy carrier

Conjecture 25 survives: finite linearity pushes the adaptive reverse-Bessel packet through both
the Lebesgue and Chebyshev--Stieltjes integrals before subtraction.  With

```text
K_(n,c,w)(x) = sum_j c_j * radialBesselKernel(n+j, 1/2+w, x)
                       / completedSourceMomentScale(n+j,w),
```

one has unconditionally for `w>1/2`

```text
xiShiftedHankelBoundaryDiscrepancyJet w n c
  = integral_(1,inf) K_(n,c,w)(x) dx
      - integral K_(n,c,w)(x) d chebyshevPsiStieltjes,

xiShiftedHankelFirstOmittedCoupling (w^2) n c
  = xiShiftedHankelBoundaryArchimedeanJet w n c
      + xiShiftedHankelBoundaryRadialDiscrepancy w n c.
```

The pointwise carrier theorem expands the same `K` in both integrals through `P^sharp`.  Hence the
actual arithmetic discrepancy retains adaptive null-polynomial cancellation exactly.  This closes
the previous type gap between the positive Gamma carrier and the first omitted shifted-Xi
coupling; it does not orient that coupling.

New declarations:

- `integrableOn_radialBesselKernel`;
- `xiShiftedHankelBoundaryRadialDiscrepancy`;
- `integrableOn_xiShiftedHankelBoundaryRadialKernel`;
- `integrable_xiShiftedHankelBoundaryRadialKernel_chebyshev`;
- `xiShiftedHankelBoundaryDiscrepancyJet_eq_radialDiscrepancy`;
- `xiShiftedHankelBoundaryDiscrepancyJet_eq_factorialCarrierDiscrepancy`;
- `xiShiftedHankelFirstOmittedCoupling_eq_archimedean_add_radialDiscrepancy`.

### `docs/notes.md` applicability loops

- **Conjecture 27 — fused negative Poisson shuttle orients crossing: FAIL.**
  `XiAperturePoissonValuationClockShuttle` proves strict negative orientation after fusing all
  valuation depths at a fixed prime, but its observable is a degree-zero aperture density.  It has
  neither the adaptive coefficient vector nor `P^sharp`; all-prime/Gamma completion is explicitly
  open.  `factorialPositiveCarrierOrientationNoGo` is not a type identification with this shuttle;
  it is a hostile model blocking transport of any such marginal sign through factorial
  normalization from positivity alone.
- **Conjecture 28 — marked half-character or calibrated prime-two seam supplies missing sign:
  FAIL as a producer.** `MarkedHalfCharacterCofinalDiagonalInverseLaw` keeps a chosen-zero
  orientation but its energy squares that orientation; its Stokes law is an equality without an
  adaptive discrepancy inequality.  `XiPrimeTwoEulerHurwitzMonodromyCalibration` gives a common
  zero fibre whose global vanishing is already equivalent to RH.  Neither module maps to the
  finite shifted-Hankel null polynomial or proves a sign for its first extension.
- **Positive survivor.** Notes' “source-conditioned joint realizability” is useful only after
  typing it as (i) channel anti-cancellation on the complete null flag and (ii) a source-native
  orientation law on the combined discrepancy above.  Fixed-prime signs, scalar energies, and
  zero-fibre equivalences are insufficient interfaces.

### Combined-discrepancy audit

- 2026-08-09 — direct Lean passed for `SquaredXiChebyshevWindow.lean` and
  `XiShiftedHankelBoundaryReverseBesselCarrier.lean`.
- 2026-08-09 — targeted builds of both modules passed; final carrier build completed successfully
  after the dependency refactor.
- 2026-08-09 — axiom audit of all new integrability, discrepancy, carrier, and recombination
  theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-09 — no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in the target
  files.

## Squared-factorial root-threshold refinement

### Conjecture loops 29--30

29. **Real/simple/positive adaptive roots orient crossing. FAIL.** Two strictly positive atomic
    carriers have identical squared-factorial moments through order two, hence the same positive
    head, singular face, and null vector. Their common exact transform is
    `P^sharp_(2,c)(t)=(t-9)/36`, but their crossings are `37/144` and `-19/72`.
30. **Strictly positive full-support density repairs orientation. FAIL.** Every factorial carrier is
    realized by an exponential-mixture density. Two such densities are positive at every real
    point, share the same adaptive root, and give exact root-threshold integrals `7/24` and
    `-1/12`.

### Positive survivor

For every finite squared-factorial carrier,

```text
sum_j c_j s_(r+j)
  = sum_i weight_i node_i^r P^sharp_(r,c)(node_i).
```

For every finite exponential mixture, the same observable is an actual Lebesgue integral:

```text
integral_(0,∞) t^r P^sharp_(r,c)(t) rho(t) dt
  = sum_j c_j (sum_i weight_i scale_i^(r+j))/(r+j)!.
```

The missing source theorem is therefore a strict incidence/mass-balance law across roots of the
*actual* adaptive null polynomial. Root geometry, carrier positivity, smoothness, full support,
total positivity, and variation diminution do not provide that incidence law by themselves.

**Status:** `[LEAN-PROVED][CORPUS-SYNTHESIS][ROUTE-KILL]`. Formal declarations are recorded in
`mass-shifted-squared-factorial-root-threshold-orientation-no-go.md` and module
`XiShiftedHankelBoundaryFactorialRootThresholdNoGo`.

### Root-threshold audit

- 2026-08-09 — direct Lean and targeted module build passed.
- 2026-08-09 — capstone explicitly includes positive-semidefinite common face and nonzero kernel.
- 2026-08-09 — axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-09 — target forbidden-declaration scan is clean and RHTower umbrella import is present.
- 2026-08-09 — corpus lint remains red only on seven unrelated unreachable HTGeometry modules
  introduced by concurrent refactor; target module is absent from lint errors.
