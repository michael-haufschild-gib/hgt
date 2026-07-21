# RH ultra research handover

**Handover date:** 2026-07-21

**Repository:** `/Volumes/Intenso/code/hgt`

**Research areas:** `RHTower`, `HTGeometry`, and `HilbertMetric`

**Current verdict:** **RH is not proved.** The source-derived infinite aperture, several exact
cancellation laws, and a new source exterior cube are available. The RH-bearing source-to-response
exterior intertwiner and the all-degree signed response inequality are still open.

This is a restart document for an AI agent with no conversation history. Read the live files named
here before acting because this is a shared, active worktree and later source always outranks this
snapshot.

## 1. Mission

Create genuinely new, significant, unconditional mathematics toward a proof of the Riemann
hypothesis, using the whole HGT corpus as a research instrument rather than treating Lean as a
bookkeeping step. Every successful paper theorem must be formalized in permanent Lean source.

The immediate lane at the stopping point is:

```text
actual normalized Xi-shift valuation innovations
  -> strict source exterior cube at three distinct primes
  -> coefficientwise source-to-completed-response exterior intertwiner       [OPEN]
  -> rooted second compound + pure tangent third compound + signed Jordan join
  -> three-node response controls transverse charge                          [OPEN]
  -> integer-polynomial squared-Euler charge domination                       [OPEN; RIGHTMOST]
  -> all-degree prime--Gamma Hankel / Weil positivity                         [LEAN-CLOSED]
  -> RH.
```

The source **already produces the missing third exterior order**. Do not spend another session
trying to manufacture a third compound using a generic Gram completion. Backward traversal must
nevertheless attack the rightmost open node first: discharge
`XiSquaredEulerApertureIntChargeDominated`.  The exact infinite-summability, multiplicity grouping,
and implication from that condition through complete Weil positivity to RH are now formalized in
`XiSquaredEulerAllDegreeChargeCriterion`; no separate all-degree connector remains.  Return to the
upstream exterior intertwiner only if the charge condition has first been reduced or obstructed.

The direct source edge is now also closed, without passing through RH:

```text
coupled-Sonin finite moment/Gram producer                              [OPEN CONSTRUCTION]
  -> PrimeArchSourceTraceHankelIntNonnegative                         [LEAN-CLOSED]
  <-> XiSquaredEulerApertureIntChargeDominated                        [LEAN-CLOSED]
  -> complete square-summable Xi Weil positivity                      [LEAN-CLOSED]
  -> RH.                                                               [LEAN-CLOSED]
```

The new equivalence is
`xiSquaredEulerApertureIntChargeDominated_iff_primeArchSourceTraceHankelIntNonnegative`.
Moment-measure, finite-KMS, Sonin-barycenter, and coupled-Sonin hypotheses already construct the
source Hankel condition conditionally.  Do not add wrappers for them.  Work on an actual producer,
preferably the source-specific coupled-Sonin variational/finite-Gram condition, or prove `(AH9)`
directly.

## 2. Mandatory initialization and working rules

Before research or edits, read completely:

1. `AGENTS.md` without modifying it;
2. `docs/meta/scientific-method.md`;
3. `/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md`;
4. `formal/README.md`;
5. this handover;
6. `docs/reports/rh-current-state.md`;
7. `docs/drafts/pipeline/1-in-progress/xi-shift-tangent-exterior-cube.md`;
8. `docs/drafts/pipeline/1-in-progress/rh-sota-literature-lean-wall-2026.md`;
9. `docs/reports/rh-lean-corpus-review-2026-07-19/06-corpus-synthesis.md`;
10. the relevant failed cards under `docs/drafts/pipeline/5-failed` before retrying any route.

The user's non-negotiable rules are:

- Check the current corpus before conjecturing or adding a declaration.
- Use the full interaction among `HTGeometry`, `RHTower`, and `HilbertMetric`; do not narrow the
  work to an isolated RHTower abstraction.
- Apply the anti-theatre test: if literature search can simply supply the proposed result, it is
  not the sought new knowledge. Conjecture from the exact source first, prove or refute it, and
  then search for collision and parent theory.
- Do not count infrastructure, wrappers, renamed classical facts, equivalent RH criteria, generic
  Gram factorizations, or formalized assumptions as scientific progress.
- Lean proofs must be unconditional. No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, numerical
  evidence, or computation-driven theorem selection.
- Use exactly one foreground Lean process owned by this task.
- Ordinary verification is always `lake env lean <file>` from `formal/`.
- Use `lake build <Exact.Module.Name>` only for the final targeted module audit.
- Batch meaningful edits before checking; do not alternate tiny edits and builds.
- Before and after a Lean run, identify only this task's process. Never kill or interfere with
  another agent's Lean or lake process.
- Preserve the dirty shared worktree and all unrelated edits. Do not stage or commit unless the
  user explicitly asks.
- Do not modify `AGENTS.md`.
- Keep `docs/reports/rh-current-state.md` as the tight live statement of what is known now. Put
  derivations and history on pipeline cards or here, not in that state document.

For any claimed reusable result, use the labels accurately:

- `[CORPUS]`: already present in the project;
- `[PAPER-PROVED]`: dependency-closed mathematical proof exists;
- `[LEAN-PROVED]`: the exact theorem has passed direct checking, exact module build, lint, and
  axiom audit;
- `[EXTERNAL NOVELTY UNVERIFIED]`: search found no collision but no priority claim is justified;
- `[OPEN CORE]`: the scientific implication still missing.

## 3. Exact stopping state

### 3.1 Permanent new research card

The central new card exists, is tracked, and was clean at handover:

`docs/drafts/pipeline/1-in-progress/xi-shift-tangent-exterior-cube.md`

Status recorded there:

```text
[PROVED HERE ON PAPER]
[INTERNAL NOVELTY AUDITED]
[EXTERNAL NOVELTY UNVERIFIED]
[NOT RH]
Lean target: RHTower/XiShiftTangentExteriorCube.lean
```

### 3.2 No permanent Lean module yet

`formal/GaloisForLFunctions/RHTower/XiShiftTangentExteriorCube.lean` did not exist at the stopping
point. A temporary `/tmp/xi_shift_cube.lean` had been started, but the user's interruption removed
the temporary file before it was preserved. Do not look for it.

What was known from that scratch run:

- an abstract `3 x 3` determinant factorization using `Matrix.det_fin_three` compiled;
- wrappers for the actual first three normalized Xi-shift coordinates were drafted;
- the first coordinate simplification initially left only inverse-cancellation goals such as
  `P * P⁻¹`; adding `ring_nf` and `simp [hp]` after `field_simp` was the intended repair;
- the second check was interrupted before a verdict, so **none of the actual-source coordinate
  lemmas may be called Lean-proved**.

At handover there was no process matching the discarded scratch checker. No owned Lean/lake
process was left running.

### 3.3 Live report is one result behind

`docs/reports/rh-current-state.md` is current through the signed projective curvature work, the
Gaussian aperture work, the HT sign-blindness no-go, and the one-cut response law. It does **not**
yet include the Xi-shift exterior-cube theorem. Update it only after the new Lean module passes.

Its Open Core C should then be sharpened from “construct a third compound” to “prove the
coefficientwise source/response exterior intertwiner and charge-control inequality.”

## 4. What this research run did

### 4.1 Corpus audit instead of literature substitution

The run read and compared the actual declarations and proof surfaces in:

- `formal/GaloisForLFunctions/RHTower/XiSquaredEulerApertureHilbertCorrelation.lean`;
- `GammaSewnFourRateSynchronizedEulerFisher.lean`;
- `CentralReciprocalMoments.lean`;
- `XiRelativeResolventTrace.lean`;
- `GammaJordanXiFourRateFatherDetailTransfer.lean`;
- `GammaSewnFourRateSchurFisherCurvature.lean`;
- `GammaSewnFourRateHeightLocalizedDomination.lean`;
- `GammaSewnSynchronizedEulerFisherBarycenter.lean`;
- `GammaSewnXiShiftTangentInnovation.lean`;
- `GammaSewnXiShiftTangentHilbertKernel.lean`;
- `XiShiftPrimeHypertranscendence.lean`;
- `formal/GaloisForLFunctions/HilbertMetric/ThreePointCorrelationLocal.lean`.

It also audited the live/failed cards for the two-node response barrier, pointed exterior transfer,
cubic aperture exterior fusion, tangent response gap, aperture signature parity, completed
reflection sectors, one-cut Krein spectrum, and the failed physical-cutoff Jordan route.

This review established that the source's all-depth normalized tangent feature was already present,
but had only been used through pairwise sums and Gram kernels. The correct new question was
therefore whether literal valuation coordinates already carry a nonzero third exterior compound.

### 4.2 New paper theorem: exact Xi-shift source exterior cube

`[PAPER-PROVED] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`

The normalized source feature already in Lean is

```text
u_p(e) = gammaSewnXiShiftEndpointUnitTangentFeature p e
       = p^2 * gammaSewnXiShiftEndpointTangentFeature p e.
```

For `a=1/p`, its first three valuation coordinates are

```text
u_p(0) = -a sqrt(1-a^2),
u_p(1) = (1-2a^2)sqrt(1-a^2),
u_p(2) = a(2-3a^2)sqrt(1-a^2).                         (XC1)
```

For three primes `p,q,r`, write `a=1/p`, `b=1/q`, `c=1/r`. Let `U(p,q,r)` be the matrix whose
columns are the three vectors in `(XC1)`. Then

```text
det U(p,q,r)
 = -3 sqrt(1-a^2)sqrt(1-b^2)sqrt(1-c^2)
     (b-a)(c-a)(c-b)(a+b+c+2abc).                      (XC2)

(det U(p,q,r))^2
 = 9(1-a^2)(1-b^2)(1-c^2)
     (b-a)^2(c-a)^2(c-b)^2(a+b+c+2abc)^2.              (XC3)
```

Therefore, for pairwise distinct primes,

```text
(det U(p,q,r))^2 > 0.                                  (XC4)
```

This is not a generic existence or realization theorem. It uses the actual first three
forward-difference innovations of the completed `+2` Xi-shift carrier, before Gram compression,
zero selection, inverse resolution, or graph completion.

### 4.3 Dependency-closed paper proof

Remove the three positive square-root factors. The remaining columns evaluate

```text
g_0(x)=-x,
g_1(x)=1-2x^2,
g_2(x)=2x-3x^3.
```

Flip the sign of the first row, giving `h_0=x`, `h_1=1-2x^2`, `h_2=2x-3x^3`. In the monomial
basis `(1,x,x^2,x^3)`, the Cauchy--Binet expansion has only two nonzero degree sets:

```text
{0,1,3}, with coefficient minor 3,
{1,2,3}, with coefficient minor 6.
```

The two alternants are

```text
det[1;x;x^3]   = (b-a)(c-a)(c-b)(a+b+c),
det[x;x^2;x^3] = abc(b-a)(c-a)(c-b).
```

Their sum, the restored first-row sign, and the square-root factors give `(XC2)`. Squaring gives
`(XC3)`. A prime satisfies `0<a<=1/2`, so all `1-a^2` terms and
`a+b+c+2abc` are positive. Distinct positive primes have distinct reciprocals, giving `(XC4)`.

### 4.4 All-depth HTGeometry interpretation

The existing generating-function theorem says, after the forced `p^2` normalization, that the
source feature has rational profile

```text
sqrt(1-a^2) (z-a)/(1-az)^2,       a=1/p.
```

It has a source-labelled double pole at `z=p` with nonzero principal part. The confluent Cauchy-jet
uniqueness mechanisms in `HTGeometry/CauchyJetControllability.lean` and its prime-log descendants
therefore explain finite linear independence of the complete features at distinct primes. The
explicit formula `(XC2)` is the first RH-relevant exterior degree where that all-depth pole
separation becomes visible in literal low valuation coordinates.

Do not overstate this: HT pole separation supplies independence and coordinates, not the analytic
sign of the completed response. The completed common field/ring can also erase orientation, as the
sign-blindness theorem below proves.

### 4.5 Why this changes the RH target

Permanent Lean already proves in
`RHTower/GammaSewnXiShiftTangentHilbertKernel.lean`:

```text
xiPhysicalEndpointCompletedThreePrimeDet
 = local stiffness * rootedTangentSecondCompound
   + 2 * tangentEdge(p,q) * tangentEdge(p,r) * tangentEdge(q,r).
```

The exact theorem name is

```text
xiPhysicalEndpointCompletedThreePrimeDet_eq_rootedSecond_add_tangentThird.
```

The source had previously been consumed only as a pairwise tangent Gram, which could at most
explain the rooted second-compound part. `(XC2)` proves that the actual source itself already has a
strict third exterior coordinate. Hence the remaining theorem is not “find a third compound.” It
is the source-derived, coefficientwise intertwining law that sends the exterior source coordinate
to the pure tangent third term of the completed response, while the known stiffness/tangent split
supplies the rooted second term and the signed Jordan join retains cancellation.

Positivity of `(XC3)` alone does not identify that image, control transverse charge, prove the
all-degree Hankel cone, or prove RH.

### 4.6 Novelty audit

The exact statement and source object were searched in the internal Lean tree, pipeline, reports,
and failed routes before and after proof. No duplicate was found.

External search after the proof located classical parent theories:

- generalized and confluent Vandermonde determinants: Goodstein (1970), Flowe--Harris (1993), and
  Lomidze (1994);
- Hardy-space rational factors related to `(z-a)/(1-az)` and `(1-az)^{-2}`: Dyakonov (2022).

Links are recorded on the pipeline card. None of those sources was found to state `(XC2)` for the
completed Xi-shift valuation innovation or its RH response role. This is a search noncollision,
not a priority claim. Keep `[EXTERNAL NOVELTY UNVERIFIED]` until expert audit.

## 5. Essential compiled corpus facts

These facts constrain every viable route. Recheck the live files, but do not rederive them.

### 5.1 Signed boundary Jordan law

`[CORPUS] [LEAN-PROVED]`

In `GammaSewnFourRateSynchronizedEulerFisher.lean`:

```text
F_H=-F/2,       F_S=3F/2,
-F_H=F_S/3,    F_H+F_S=F.
```

The negative mass is exactly one third of the positive mass. Separate estimates destroy the
source cancellation.

### 5.2 First Xi response correlation law

`[CORPUS] [LEAN-PROVED]`

In `XiSquaredEulerApertureHilbertCorrelation.lean`, for a finite zero packet:

```text
G_S = (1/2) sum_(q,r) a_q a_r (tau_q-tau_r)^2,
J_S = (sum_q a_q)(sum_q chi_q),
first central minor = G_S-J_S.
```

The concrete RH-facing degree-one target is

```text
J_S <= G_S.                                               (RH-R1)
```

This is not established for all source-realizable packets.

### 5.3 Scalar Gamma/Xi response gap: useful metric, terminal sign producer

`[CORPUS] [LEAN-PROVED]`

`GammaJordanXiTangentResponseGap.lean` proves a genuine off-diagonal metric comparable to the
all-depth tangent distance. `GammaJordanXiFourRateFatherDetailTransfer.lean` proves the decisive
no-go: every same-prime four-depth cell is pure father, with zero response detail and zero gap
transfer but positive Fisher father. No scalar multiple of the unpointed gap controls the signed
mass on all source cells.

`GammaXiResponseGapOneCutSpectrum.lean` further proves strict likelihood-ratio order and a one-cut
signed spectrum. The unchanged scalar gap is not of negative type globally, and the paper tangent
rigidity argument also rules it out on inverse primes. A true aperture Hilbert object must therefore
be multichannel and source-coupled; it cannot be the old scalar gap under a new name.

### 5.4 Endpoint stiffness and the exact compound split

`[CORPUS] [LEAN-PROVED]`

`XiPhysicalEndpointLocalStiffness.lean` proves unavoidable positive zero-mode stiffness and the
required tangent subtraction. `GammaSewnXiShiftTangentHilbertKernel.lean` proves that a full
three-node completed determinant has both rooted second and pure tangent third compounds. A rank-one
root times a second compound cannot remove the third term.

### 5.5 Source-derived Gaussian aperture

`[CORPUS] [LEAN-PROVED up to the stated open balance]`

On the completed theta-cusp source space:

```text
(C_L u)(x)=exp(-Lx^2/2)u(x),
C_L C_M=C_(L+M),
||C_Lu||<=||u||.
```

This is the desired infinite, height-localized, source-derived contraction. It avoids both HT
source-span saturation and the exact resolution deficit. Its first nonconstant Hankel gate is the
unsplit composite balance

```text
3 B_3/B_2 + 15 B_1/B_0 - 10 B_2/B_1 >= 0.               (GABTC)
```

The one-crossing aperture window, cooperative curvature flow, height-localized higher-atom
contraction, response-centered saddle, signed two-channel transport, and projective curvature laws
are permanently formalized in the modules named in `rh-current-state.md`.

The leading positive `C_4` channel has cold-negative curvature. The signed `p=2` correction is the
positive producer. The live first-atom target is the exact flux law

```text
q_j^(4)d_(j+2)T_j >= q_(j+2)^(4)d_jT_(j+1),             (OPEN-B-FLUX)
```

equivalently the weighted multiplier-concavity law `(OPEN-B-WC)`. It is not globally proved.

### 5.6 HT completion is sign-blind; pointed residues survive

`[CORPUS] [LEAN-PROVED]`

`HTGeometry/PrimeOrientationCompletedRingSignNoGo.lean` proves that all Boolean prime orientations
have the same compact-open completed common-atom ring, although the meromorphic carrier is Herglotz
only in the all-positive orientation. An unpointed completed field or ring cannot classify the
analytic sign needed for RH.

The positive survivor is residue pointing: distinct orientations differ at an exact prime pole
residue. The aperture response must preserve this pointed source information. HTGeometry may
provide independence, minimality, and coordinate control, but not sign after quotienting away the
residues.

### 5.7 Xi-shift source is genuinely hypertranscendental

`[CORPUS] [LEAN-PROVED]`

`RHTower/XiShiftPrimeHypertranscendence.lean` identifies the actual filtered von Mangoldt carrier
as hypertranscendental over `C(z)`. This matters because the exterior source coordinate is not an
arbitrary rational surrogate; it comes from the genuine Xi-shift carrier. Use the HTGeometry proof
architecture—coordinate field, pole jets, and differential-field generation—to understand what
maps are source-canonical, but do not infer an RH sign from hypertranscendence itself.

## 6. Exact live open cores

### Open Core A: literal sixth-seam source bridge

Formalize the actual theta-path autonomous system and prove

```text
thetaCuspGaussianApertureSixthSeamNumerator
 = thetaCuspGaussianApertureSixthSeamModularClosureValue > 0.
```

The modular polynomial chamber is compiled, but the bridge from literal theta derivatives to that
value is paper-only. Missing analytic inputs are the theta-three logarithmic derivative and the
Ramanujan `E_2` differential identity in the current formal substrate.

### Open Core B: signed aperture projective flux and GABTC

Prove `(OPEN-B-FLUX)` over the complete physical aperture continuum, then absorb the higher-atom
response and propagate through the cooperative flow to `lambda=0`. Mass contraction alone does not
preserve second degree differences. The independent direct route is the fixed-curvature pairing
against the already-proved unique one-crossing window.

### Open Core C: RH-bearing exterior response join — current lane

The source third exterior order is now paper-proved by `(XC2)`. The immediate scientific theorem is
to identify a **source-derived coefficientwise response map**, independent of selected zeros and
target signs, whose second and third compounds land in the existing completed three-node response
split. It must:

1. preserve the residue-pointed orientation lost by the completed HT ring;
2. operate on the infinite Xi-shift height source, not a selected finite jet or post-hoc Gram;
3. respect the forced stiffness/tangent subtraction;
4. map the strict source exterior cube to the pure tangent third response with a controlled sign;
5. combine with the rooted second compound and exact `-1/2,+3/2` Jordan law without splitting the
   signed pieces;
6. imply charge control at three nodes and then lift to the all-degree cone containing `(RH-R1)`.

No theorem in Lean or the audited literature supplies this map. Merely defining an operator whose
positivity is equivalent to RH is theatre. The coefficients must be derived from the completed
theta/prime--Gamma source and the causal response already present in the corpus.

## 7. Precise next actions

### Step 1: formalize the paper-proved source exterior cube

Create:

`formal/GaloisForLFunctions/RHTower/XiShiftTangentExteriorCube.lean`

Import only:

```lean
import GaloisForLFunctions.RHTower.GammaSewnXiShiftTangentHilbertKernel
```

Recommended declaration sequence:

1. an abstract first-three frame in inverse-prime coordinates;
2. its exact determinant factorization `(XC2)` using `Matrix.det_fin_three` and `ring` after the
   square-root factors are treated as scalars;
3. lemmas for `gammaSewnXiShiftEndpointUnitTangentFeature p 0`, `... p 1`, and `... p 2` proving
   `(XC1)`;
4. equality between the actual source frame and the abstract frame;
5. the exact determinant theorem for three `Nat.Primes`;
6. determinant nonvanishing for pairwise distinct primes;
7. the squared exterior cube formula and strict positivity theorem `(XC3)`--`(XC4)`;
8. optionally, only if short and useful, the truncated Gram determinant identity `det(UᵀU)=det(U)^2`.

For the coordinate lemmas, set

```lean
have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
```

and expect the actual feature expansion to need a batched combination of `norm_num`, `ring_nf`,
`field_simp [hp]`, and `simp [hp]`. Verify every recalled mathlib name in a `/tmp` file with
`have := @Name` before using it permanently.

For reciprocal separation and positivity, derive from prime positivity and `p.2.two_le`; do not
hide these facts in assumptions. If using `inv_ne_inv₀`, first verify its exact signature in this
toolchain. The permanent theorem should quantify over three primes with explicit pairwise
inequalities and prove strict positivity unconditionally.

Verification sequence, serialized:

```text
cd /Volumes/Intenso/code/hgt/formal
lake env lean GaloisForLFunctions/RHTower/XiShiftTangentExteriorCube.lean
```

After the complete batched file passes, and only for the final audit:

```text
lake build GaloisForLFunctions.RHTower.XiShiftTangentExteriorCube
```

Then run the project lint and a `/tmp` `#print axioms` audit for the capstone theorems. Do not add
the module to umbrella imports until the leaf is independently clean and the shared worktree is
stable.

### Step 2: promote the research state accurately

After the exact Lean audit passes:

- update the pipeline card's Lean gate and stage according to the pipeline rules;
- add the source exterior-cube result to `docs/reports/rh-current-state.md`;
- rewrite Open Core C there so the missing object is the coefficientwise exterior intertwiner;
- retain `[EXTERNAL NOVELTY UNVERIFIED]` and `[NOT RH]`;
- record exact direct-check, exact-module-build, lint, and axiom evidence.

### Step 3: conjecture the actual exterior intertwiner before coding it

Read together, line by line:

- `GammaSewnXiShiftTangentHilbertKernel.lean`, especially
  `gammaSewnXiShiftEndpointUnitTangentFeature`, its generating function, and
  `xiPhysicalEndpointCompletedThreePrimeDet_eq_rootedSecond_add_tangentThird`;
- `XiPhysicalEndpointLocalStiffness.lean`, especially
  `xiPhysicalEndpointTangentPrimeRatioRealKernel`;
- `GammaJordanXiTangentResponseGap.lean` and
  `GammaJordanXiFourRateFatherDetailTransfer.lean`;
- `XiSquaredEulerApertureHilbertCorrelation.lean`;
- `XiShiftPrimeHypertranscendence.lean`;
- HTGeometry's Cauchy-jet controllability and coordinate-field generation results;
- the cubic exterior matching and failed response cards listed below.

Then state a paper conjecture with literal coefficients. The map must be fixed by the source
response or a uniqueness principle, not chosen to make the target determinant positive. Subject
it immediately to:

- same-prime four-depth father cells;
- functional-equation quartets with equal response slope;
- the reflection-even odd-detector annihilation law;
- the exact rooted-second-plus-tangent-third split;
- coefficientwise finite-prefix versus infinite-fusion compatibility;
- the source residue orientation no-go.

If the conjecture fails, extract the strongest exact positive survivor—classification, unique
allowed channel, sharp obstruction, or replacement hypothesis—and formalize that. Do not merely
retire it.

### Step 4: connect the exterior join to charge, not just determinant positivity

The first response minor is `G_S-J_S`, not a free Gram determinant. A successful three-node
exterior map must produce an inequality that actually controls `J_S`, and then explain why the
control is stable under arbitrary finite packets/all degrees. Without this implication, a positive
three-prime determinant is another local criterion and not RH progress.

## 8. No-go list and positive survivors

Do not retry these routes unchanged:

| Dead route | Exact obstruction | Positive survivor to use |
|---|---|---|
| HT graph/source-span saturation | HT freedom can realize jets but supplies no analytic sign | residue-pointed pole coordinates and source-canonical maps |
| Unpointed completed HT ring | all orientations have the same completion | exact pointed residues distinguish orientations |
| Fourier/prolate superresolution | violates the exact resolution deficit | literal infinite Gaussian height contraction |
| Matched source/zero packet | ill-typed and target-selected | source-only coefficientwise response |
| Separate `-1/2` and `+3/2` estimates | erases exact Jordan cancellation | joined signed four-rate law |
| Scalar Gamma/Xi gap domination | same-prime father cells have positive mass and zero gap transfer | multichannel father/detail join |
| Scalar stationary/nonstationary Hilbertization | one-cut spectrum and inverse-prime tangent rigidity | source-coupled residue-pointed Hilbert object |
| Diagonal `det_2` response | zero-free and cannot carry divisor | off-diagonal joined response |
| Raw endpoint cancellation | positive zero-mode stiffness | unique stiffness subtraction plus tangent kernel |
| Rooted second compound alone | pure tangent third term survives exactly | source exterior cube `(XC2)` and an intertwiner |
| Functional-equation quartet cancellation | conjugate partners have equal slope and positive charge | cross-orbit/source response dispersion |
| One- or two-node response | unconditionally positive and cannot see charge | first possible sign at three nodes |
| Reflection-even completion | annihilates odd detectors | transverse aperture-odd real symmetric sector |
| Generic/post-hoc Gram or Pontryagin factorization | sign inserted rather than derived | literal Xi-shift feature and completed response coefficients |
| Arbitrary Gaussian/heat damping | not tied to the completed source | completed theta-cusp semigroup |
| Global positive `C_4` curvature | rigorously cold-negative | signed `p=2` correction and projective flux |
| Absolute leakage bound as cold closure | loses a full factor of aperture scale | signed projective cancellation |
| Finite jet theorem presented as RH | cannot control all packets/degrees | all-depth exterior join and all-degree lift |

Additional exact barriers:

- a functional-equation quartet does not cancel transverse charge because conjugate zeros share
  the same response slope; within-orbit dispersion is zero while charge is positive;
- one- and two-node Xi response is unconditionally positive; an isolated off-line orbit first
  becomes negative at three nodes;
- a four-depth same-prime source cell is pure father, so unpointed gap/detail mechanisms vanish;
- the full three-node determinant contains both a rooted second compound and a pure third compound;
- cross-orbit masking of an off-line cubic is only a finite-amplitude effect unless a source-pure
  unbounded or all-degree mechanism is proved.

## 9. Current assumed RH proof shape

```text
completed theta / prime--Gamma source
  -> residue-pointed source cone
  -> infinite height-localized source aperture preserving orientation and inertia
  -> exact father/detail decomposition and stiffness/tangent subtraction
  -> source exterior cube and coefficientwise completed-response intertwiner
  -> off-diagonal response dispersion cancels transverse Jordan charge
  -> integer-polynomial squared-Euler charge domination
  -> complete signed prime--Gamma Hankel / Weil positivity                   [Lean connector closed]
  -> every Xi zero is critical.
```

This is a working architecture, not a theorem. Pivot if exact source mathematics refutes it. A
valid pivot must still produce an unconditional global source theorem, not merely another
RH-equivalent consumer.

## 10. Files and declarations to open first

Primary current lane:

- `docs/drafts/pipeline/1-in-progress/xi-shift-tangent-exterior-cube.md`;
- `formal/GaloisForLFunctions/RHTower/GammaSewnXiShiftTangentHilbertKernel.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaSewnXiShiftTangentInnovation.lean`;
- `formal/GaloisForLFunctions/RHTower/XiShiftPrimeHypertranscendence.lean`;
- `formal/GaloisForLFunctions/RHTower/XiPhysicalEndpointLocalStiffness.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaJordanXiTangentResponseGap.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaJordanXiFourRateFatherDetailTransfer.lean`;
- `formal/GaloisForLFunctions/RHTower/XiSquaredEulerApertureHilbertCorrelation.lean`;
- `formal/GaloisForLFunctions/HTGeometry/CauchyJetControllability.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeLogCauchyJetControllability.lean`;
- `formal/GaloisForLFunctions/HilbertMetric/ThreePointCorrelationLocal.lean`.

Relevant cards to prevent rediscovery:

- `docs/drafts/pipeline/2-fully-proven/needs-audit/xi-euler-ray-two-node-response-barrier.md`;
- `docs/drafts/pipeline/1-in-progress/gamma-sewn-pointed-exterior-height-transfer.md`;
- `docs/drafts/pipeline/1-in-progress/xi-cubic-aperture-response-exterior-fusion.md`;
- `docs/drafts/pipeline/3-formalized/needs-audit/gamma-jordan-xi-tangent-response-gap-laplacian.md`;
- `docs/drafts/pipeline/3-formalized/needs-audit/xi-aperture-poisson-response-signature-parity.md`;
- `docs/drafts/pipeline/3-formalized/needs-audit/xi-completed-aperture-reflection-sector-odd-detector-law.md`;
- `docs/drafts/pipeline/1-in-progress/gamma-xi-response-gap-one-cut-krein-spectrum.md`;
- the corresponding failed physical-cutoff/Jordan cards under `5-failed`.

The formal research index currently locates these exact declarations:

```text
gammaSewnXiShiftEndpointTangentFeature
gammaSewnXiShiftEndpointUnitTangentFeature
gammaSewnXiShiftEndpointTangentGeneratingFunction_eq
constantDiagonalThreePointDet_root_add_tangent
xiPhysicalEndpointCompletedThreePrimeDet_eq_rootedSecond_add_tangentThird
xiPhysicalEndpointCompletedThreePrimeDet_eq_rootedSecond_iff
xiPhysicalEndpointTangentPrimeRatioRealKernel
gammaSewnXiShiftEndpointUnitTangentKernel_eq_responseFromBase
gammaJordanXiPrimeResponseGap_eq_joined_sub_tangent
```

Use `scripts/formal_tools.py research "<query>"` before adding any reusable declaration.

## 11. Shared-worktree snapshot and process hygiene

At the handover snapshot, many files belonged to other active work. Do not overwrite, stage, move,
or “clean up” them. The visible dirty/untracked set included:

```text
docs/drafts/pipeline/1-in-progress/hedenmalm-center-mixed-double-positivity-law.md
docs/drafts/pipeline/1-in-progress/rh-sota-literature-lean-wall-2026.md
docs/drafts/pipeline/1-in-progress/simple-pole-jet-lattice-holographic-selection-law.md
formal/GaloisForLFunctions/HTGeometry.lean
formal/GaloisForLFunctions/HTGeometry/GammaPoleCovariantJetRealization.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicSimplePoleDifferentialOperator.lean
formal/GaloisForLFunctions/RHTower.lean
formal/GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean
formal/LEAN_API.md
formal/LEAN_OVERVIEW.md
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-negative-shift-defect-escape.md
docs/drafts/pipeline/3-formalized/needs-audit/suzuki-ground-edge-cayley-universality.md
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-finite-aperture-hermite-biehler-normal-family.md
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-projective-defect-free-boundary.md
formal/GaloisForLFunctions/HTGeometry/GammaPoleBinomialSubprincipalDescent.lean
formal/GaloisForLFunctions/HTGeometry/GammaPolePrincipalRemainderFreeness.lean
formal/GaloisForLFunctions/HTGeometry/SimplePoleWeightedFirstSubprincipal.lean
formal/GaloisForLFunctions/RHTower/SuzukiFiniteApertureHermiteBiehler.lean
formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeCayleyUniversality.lean
formal/GaloisForLFunctions/RHTower/SuzukiProjectiveDefectBoundary.lean
docs/handover/htzeta.md
```

This list is only a snapshot. Re-run `git status --short` and inspect overlapping diffs before every
edit. The exterior-cube card was tracked and clean. This handover file was the only intended new
artifact of the stopping request.

No Lean build was run to produce this handover. The vanished scratch left no running checker. At
the start of a new Lean session, inspect processes narrowly, start one foreground command, wait for
it to finish, and confirm that exact PID is gone.

## 12. Definition of real progress from here

The next session has made real progress only if it does at least one of the following:

1. permanently and unconditionally formalizes `(XC1)`--`(XC4)` with targeted verification;
2. states and paper-proves a literal source-derived coefficientwise exterior intertwiner;
3. refutes a concrete intertwiner and extracts a sharp positive classification or unique surviving
   response channel, then formalizes it;
4. proves that the exterior response controls the actual transverse charge rather than a surrogate;
5. discharges or strictly reduces `XiSquaredEulerApertureIntChargeDominated`, whose all-degree
   lift to Weil positivity and RH is already formalized;
6. closes Open Core A or B with a source theorem strong enough to feed Open Core C.

It is not progress to add a name for the desired map, assume its positivity, restate RH, prove a
generic determinant identity detached from the Xi source, or rediscover a declaration already
listed here.

## 13. First command packet for the new session

After completing the mandatory reading and confirming the shared worktree:

```text
scripts/formal_tools.py research "Xi shift tangent exterior cube determinant"
scripts/formal_tools.py research "completed three prime determinant tangent third compound"
```

Reconstruct the whole paper-proved module in one meaningful batch. Then run only:

```text
cd formal
lake env lean GaloisForLFunctions/RHTower/XiShiftTangentExteriorCube.lean
```

Do not run an umbrella or full build. When the leaf is complete and directly clean, run the exact
module build once, audit axioms, update the card and current-state report, and move immediately to
the coefficientwise exterior-intertwiner conjecture.
