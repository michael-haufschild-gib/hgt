# Suzuki fixed-affine signed-compensation classification

- **ID:** SWA-FIXED-AFFINE-COMPENSATION-CLASSIFICATION
- **Stage:** 3-formalized
- **Type:** ROUTE-CLASS NO-GO / POSITIVE CLASSIFICATION `[LEAN-PROVED]`
- **Source:** `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`

## Exact RH chain under attack

Write

- `C_N = suzukiNaturalApertureTransitionCoreCauchyEnergy N`,
- `E_N = suzukiTransitionCoreAlignedGammaCompletedEnergy N`.

For fixed real coefficients `a,b`, define

`K_N(a,b) = a C_N + b E_N`,

and corrected residual

`R_N(a,b) = C_N - K_N(a,b)`.

The proposed chain is

`fixed affine signed compensation K(a,b)` → `positive nontrivial bounded residual` →
`bounded aligned completed energy` → `RH` → shared HB/FZZ-P/PW-B/RBH Ward endpoint.

This card asks whether coefficient choice itself can discharge the last source-order theorem.

## Internal frontier

`[CORPUS]` The prior linear-compensation theorem proves that every lower-semibounding correction
must carry positive linear mass along apertures `8n`; no sublinear correction survives.

`[CORPUS]` The coefficient-faithful canonical correction `C_N-E_N` satisfies

- `E_N / C_N -> 0`,
- `(C_N-E_N)/C_N -> 1`,
- `C_N-(C_N-E_N)=E_N`,
- eventual boundedness of `E_N` is equivalent to RH.

`[CORPUS]` `E_N >= 0` for every `N`.

Internal corpus search found no classification of all fixed affine corrections.

## External frontier and priority audit

Primary-source audit through 2026-08-31 covered Suzuki's screw-function papers
`arXiv:2206.03682`, `arXiv:2209.04658`, Matsumoto--Suzuki's M-function/screw-function paper
`arXiv:2409.00888`, and Suzuki's Weil/screw synthesis `arXiv:2606.09096`.  They prove or organize
RH-equivalent screw/Weil boundedness and positivity statements.  They do not define the transition
core `C_N`, aligned energy `E_N`, fixed-affine correction family, saturation quotient, or the
classification below.  The novelty claim is limited to this corpus-native compensation
classification and its four-route consequence.

## Conjecture loop

### C0 — universal fixed-affine bounded compensation

`[CONJECTURE]` Some fixed `a,b` make `K(a,b)` asymptotically cancel the transition core while
leaving a nonzero nonnegative residual bounded by a source theorem strictly weaker than RH.

Hostile verdict: **CIRCULAR**.

Exact why: since `E_N/C_N -> 0`,

`K_N(a,b)/C_N = a + b E_N/C_N -> a`.

Saturation therefore forces `a=1`, after which

`R_N(1,b) = -b E_N`.

For the positive nontrivial chamber `b<0`, boundedness is exactly boundedness of `E_N`, hence
exactly RH.  No coefficient choice creates an intermediate estimate.

### C1 — fixed-affine compensation trichotomy

`[CONJECTURE]` Every fixed affine correction is classified as follows:

1. its relative correction limit is `a`, so transition-core saturation holds exactly when `a=1`;
2. if `a=1` and `b<0`, the residual is a positive scalar multiple of `E_N`, and eventual upper
   boundedness is equivalent to RH;
3. if `a=1` and `b=0`, the residual is identically zero (complete source erasure);
4. if `a=1` and `b>0`, the residual is nonpositive and its upper boundedness is unconditional
   (sign-reversed vacuity).

Verdict after internal and external hostile audit: **SURVIVES PRELIMINARY ATTACK**.

This is stronger and more explanatory than C0: it classifies the full coefficient plane and turns
the circularity mechanism into a route-class theorem.

## Paper proof

### Relative-limit rigidity

Eventually `C_N != 0`.  Hence

`K_N(a,b)/C_N = a + b(E_N/C_N)`.

The already proved limit `E_N/C_N -> 0` gives

`K_N(a,b)/C_N -> a`.

Limits in `R` are unique, so this quotient tends to one exactly when `a=1`.

### Residual normal form

For `a=1`, direct algebra gives

`R_N(1,b) = C_N-(C_N+bE_N) = -bE_N`.

### Positive chamber

If `b<0`, then `-b>0`.  Since `E_N>=0`, the residual is nonnegative.  Multiplication by the fixed
positive scalar `-b` preserves and reflects eventual upper boundedness:

`R_N(1,b)` eventually bounded above iff `E_N` eventually bounded above.

The corpus equivalence for `E_N` then gives

`R_N(1,b)` eventually bounded above iff RH.

### Erasing and sign-reversed chambers

If `b=0`, the residual normal form is identically zero.  If `b>0`, nonnegativity of `E_N` gives
`R_N(1,b)=-bE_N<=0`; therefore it is unconditionally eventually bounded above by zero.  This
boundedness has the wrong sign and contains no RH information.

These cases exhaust `b<0`, `b=0`, and `b>0`, while relative-limit rigidity exhausts `a`.  The
classification is dependency-closed. `[PAPER-PROVED]`

## Hostile audit of complete proof

- Division is used only eventually, after the existing theorem `C_N != 0`.
- No inference that `E_N/C_N -> 0` implies `E_N=O(1)` occurs.
- Positive scaling preserves boundedness in both directions only in the explicitly assumed chamber
  `b<0`.
- The `b>0` chamber is not misreported as an RH criterion: it is upper bounded because it reverses
  the nonnegative energy sign.
- `b=0` is excluded as a producer because it deletes the entire corrected source.
- Coefficients are fixed.  Scale-dependent, nonlinear, singular, or nonlocal corrections are not
  classified and remain separate architectures.

## Mathematical delta

Fixed affine signed compensation is terminal.  Every core-saturating coefficient choice is either

- a positive scalar copy of the exact RH-equivalent aligned residual,
- total erasure, or
- a sign-reversed vacuous upper-bound criterion.

Thus the shared Suzuki/Ward route cannot gain new arithmetic order from any constant affine mixing
of transition-core and aligned-energy channels.  A successor must be scale-dependent, nonlinear,
singular, or nonlocal before positive-energy projection.

## Gates

- [x] Internal corpus audit
- [x] Current primary-literature audit
- [x] C0 frozen and killed as circular
- [x] Stronger C1 frozen and hostile-audited
- [x] Complete dependency-closed paper proof
- [x] Exact unconditional Lean theorem
- [x] Targeted module build, axiom audit, umbrella wiring, formal lint

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.Suzuki.SuzukiFixedAffineSignedCompensationClassification`.

Capstone:
`suzukiFixedAffineSignedCompensation_routeClassification`.

Supporting declarations include the exact relative-limit theorem, saturation iff `a=1`, residual
normal form, positive-chamber RH equivalence, erasure theorem, and sign-reversed vacuity theorem.

Audit:

- direct check passed with
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiFixedAffineSignedCompensationClassification.lean`;
- targeted module build passed, `13733/13733` jobs;
- five audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`;
- module is wired into `GaloisForLFunctions.RHTower` and formal lint reports no issue in it;
- global lint remains red only from shared-tree unwired modules
  `HedenmalmCriticalFeatureFirstOrderWindingReduction`,
  `HedenmalmCriticalFeaturePoleGammaVerticalFTC`, and
  `HTGeometry.FormationClockTransmutation`, none owned by this result.
