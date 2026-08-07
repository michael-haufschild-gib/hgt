# Route G2 relative-Volterra source-germ weld

- **ID:** `route-g2-relative-volterra-source-germ-weld`
- **Stage:** 2-fully-proven
- **Type:** NO-GO / EXACT RH-EQUIVALENT SOURCE CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `../3-formalized/new_scientific_knowledge/suzuki/suzuki-volterra-cartesian-phase-defect-formalized.md`,
  `suzuki-carleman-jump-euler-defect-weld.md`
- **Original statement:** Literal Suzuki screw/Volterra source constructs, without Xi-zero data,
  positivity assumptions, or RH, produce analytic boundary responses and an analytic
  upper-half-plane Euler-defect source whose pointed germ equals the Euler defect of the actual
  two-shift affine-sewn exterior Weyl quotient.
- **Verdict:** Route G2 does not provide an independent bypass. Under its already-required entire
  boundary and real-zero hypotheses, existence of even one such analytic pointed germ is
  equivalent to RH. Finite/local Volterra data enter only through an analytic correction and are
  transparent to the global Xi pole divisor.

## Goal and closure standard

Decide the source-level claim without replacing the actual exterior quotient, weakening the germ
identity, importing RH through a zero-free continuation, or relabelling a conditional connector as
source construction. A failed route is closed only after extracting and proving its strongest
positive survivor.

## Exact inherited objects

Fix distinct `alpha,beta : ℂ`, entire `WAlpha,WBeta,rightAlpha,rightBeta`, and assume every zero of
`WAlpha` and `WBeta` is real. Write

```text
P(z) = (beta-alpha) WAlpha(z) WBeta(z),
R(z) = (beta WBeta(z) rightAlpha(z)
        - alpha WAlpha(z) rightBeta(z)),
R_odd(z) = (R(z)-R(-z))/2,
M(z) = XiC'(z)/(z^2 XiC(z)),
m(z) = -[M(z)P(z)-R_odd(z)]/P(z),
E[f](z) = z f'(z)-f(z).
```

These are respectively `suzukiAffineSewnCharacteristic`, the target-zero
`suzukiAffineSewnIntervalPart`, its reflection-odd part, the zero-shift Xi multiplier,
`suzukiAffineSewnExteriorWeylQuotient`, and `suzukiEulerDefect`.

For every `z` with `P(z) != 0`, direct division gives the **source-transparency normal form**

```text
m(z) = R_odd(z)/P(z) - M(z).                                      (G2.1)
```

Because `alpha != beta` and all zeros of both characteristic factors are real, `P` has no zeros
off the real axis. Hence `R_odd/P` is analytic throughout both open half-planes. All off-real
singularities of `m` come from `-M`; no choice of analytic Volterra response changes that divisor.

## Hostile conjecture loop

### C1 — symmetric positivity transfers to phase sector

`[FALSE]` The Cartesian identity `2V=C+iH` makes `C=V+V*` and `H=-i(V-V*)` self-adjoint but does
not transfer positivity. The rank-one Neumann correction lives in the phase coordinate, while the
symmetric quadratic form is blind to it. This is the previously retired mechanism, not a source
weld.

### C2 — the phase rank-one law cancels the Xi pole

`[FALSE]` Homogeneous two-resolvent/marked-secant identities cancel a common projective gauge.
After division, (G2.1) shows the source normalization cancels but the universal term `-M` remains.
At every nonzero Xi zero not on the source divisor, `m` has exact order `-1`, with coefficient
`-multiplicity/z^2`; `E[m]` has exact order `-2`.

### C3 — a finite Donoghue or deficiency-family limit automatically yields the source germ

`[FALSE AS AN UNCONDITIONAL CLOSURE]` Normal-family compactness can produce an analytic
subsequential limit only where locally boundedness is proved. Identifying that limit with `E[m]`
on a punctured seed neighbourhood is the whole divisor-bearing step. Once that identity holds,
meromorphic identity propagation extends it across the connected upper half-plane and excludes
every upper Xi pole. Compactness does not prove the required identification.

### C4 — boundary-triple Green identity supplies analyticity for free

`[FALSE]` Abstract Green identities produce Nevanlinna Weyl functions only after a symmetric
operator, self-adjoint boundary data, and the required resolvent domain have been established.
They do not identify that Weyl function with the global Xi logarithmic derivative. The latter
identification is again the RH-equivalent germ weld.

### C5 — Suzuki's literal prime--Gamma screw source already supplies the full UHP identity

`[FALSE]` Suzuki's exact transform is initially proved only for `Im z > 1/2`:

```text
integral_0^infinity Psi(t) exp(i z t) dt
  = -(1/z^2) (xi'/xi)(1/2-i z).
```

Its proof uses the Euler product in the corresponding right half-plane. Continuing the right side
as an analytic function through the whole upper half-plane is possible exactly when it has no
upper-half-plane Xi poles. Calling that continuation `DSource` assumes the missing conclusion.

### C6 — weaken equality to one pointed germ

`[FALSE AS AN ESCAPE]` A pointed germ is not weak on a connected domain. Both sides are
meromorphic; the identity theorem propagates equality from one punctured seed neighbourhood.
Analyticity of the source then forces nonnegative meromorphic order everywhere, contradicting the
exact order `-2` at any upper Xi zero.

### Surviving conjecture — exact source-germ rigidity

`[PAPER-PROVED]` For every admissible boundary package above,

```text
RH
  <-> exists DSource seed,
        AnalyticOnNhd DSource upperHalfPlane
        and seed in upperHalfPlane
        and E[m] = DSource as a pointed germ at seed.               (G2.2)
```

The same equivalence holds after substituting the actual relative-Volterra phase boundary
responses. Thus any future literal prime--Gamma/Green/CD proof of the weld would be a genuine RH
proof, not missing routine operator infrastructure.

## Dependency-closed paper proof

### Lemma 1 — source-transparency normal form

At a point where `P(z) != 0`, expand the carrier and quotient definitions:

```text
m(z) = -(M(z)P(z)-R_odd(z))/P(z)
     = R_odd(z)/P(z)-M(z).
```

No parity, positivity, limit, or RH premise is used.

### Lemma 2 — local correction is analytic off the real axis

Entirety of the four boundary functions makes `P`, `R`, and `R_odd` entire. If `Im z != 0`, a
zero of `P` would force a zero of `WAlpha` or `WBeta` there, contradicting the real-zero premises;
the constant `beta-alpha` is nonzero. Therefore `R_odd/P` is analytic at every nonreal point.

### Lemma 3 — exact divisor transparency

Let `rho` be an off-real Xi zero. Centered Xi has no zero at `0`, so `rho != 0`. Lemma 2 gives
`P(rho) != 0` and analytic local correction. The zero-shift multiplier `M` has a simple pole at
`rho`; the exterior quotient consequently has exact meromorphic order `-1`. The general local
normal-form calculation for `E[f]=z f'-f` at a nonzero pole of order `n<0` gives order `n-1`.
Thus

```text
ord_rho(m) = -1,             ord_rho(E[m]) = -2.                   (G2.3)
```

This proves more than non-removability: the phase source cannot reduce pole degree, and the Euler
observable amplifies it by one.

### Theorem — (G2.2), forward direction

Assume RH. Every Xi zero is real, so `XiC(z) != 0` on the upper half-plane; also `z != 0` there.
The quotient formula for `M=XiC'/(z^2 XiC)` makes `M` analytic there. Lemma 2 and (G2.1) make `m`
analytic there, hence `E[m]=z m'-m` is analytic there. Choose

```text
DSource = E[m],              seed = i.
```

The pointed germ equality is reflexive. This establishes the existential source package.

### Theorem — (G2.2), reverse direction

Assume an analytic `DSource` on the upper half-plane and pointed equality with `E[m]` at one upper
seed. The quotient is meromorphic globally, hence its Euler defect is meromorphic on the upper
half-plane. The upper half-plane is connected. Apply meromorphic identity propagation to
`E[m]-DSource`: equality at the seed makes its meromorphic order top there, the top-order locus is
clopen, and connectedness makes it the entire domain. Therefore `E[m]` has nonnegative
meromorphic order at every upper point.

If `rho` were an upper Xi zero, (G2.3) would instead give order `-2`, contradiction. Thus no upper
Xi zero exists. If a lower Xi zero existed, centered Xi evenness would reflect it to an upper zero.
Every Xi zero is therefore real, which is the repository's centered-Xi formulation of RH.

### Relative-Volterra specialization

Substitute

```text
rightAlpha(z) = suzukiXiRealRightVolterraBoundaryResponse
                  rightEuler rightNeumann alpha uAlpha z,
rightBeta(z)  = suzukiXiRealRightVolterraBoundaryResponse
                  rightEuler rightNeumann beta uBeta z.
```

The proof above uses these functions only through their analyticity. Therefore it yields the exact
Route G2 boundary-family equivalence without discarding the Euler/Neumann channel or replacing the
actual affine-sewn quotient.

## Source and novelty audit

### Internal corpus

- `SuzukiVolterraCartesianPhaseDefect.lean`: unconditional Cartesian/phase algebra and one-way
  source-germ connector; no source construction.
- `SuzukiCarlemanJumpEulerDefectWeld.lean`: exact pole amplification and meromorphic germ
  propagation; no reverse construction under RH and no iff Route G2 classification.
- `SuzukiAdmissibleTwoShiftAffineSewing.lean` and `SuzukiCarlemanEvenPoleCarrier.lean`: affine
  sewing, universal pole carrier, and off-real analytic criteria.
- `suzuki-negative-projector-triangle-producer.md`: projective rank-one cancellation already
  kills the positivity-transfer route.
- `suzuki-jump-kernel-loewner-growth.md`: global/local source Gram remains distinct and open.

No internal artifact previously states the exact source-transparency formula together with the
existential pointed-germ iff and its actual relative-Volterra specialization.

### External primary sources checked

1. Masatoshi Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*,
   arXiv:2206.03682v4. Theorem 1.1 gives the literal prime--Gamma transform only for
   `Im z > 1/2`; screw positivity is RH-equivalent.
2. Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1.
   Finite Friedrichs/self-adjoint models and entire real-zero characteristic functions are
   unconditional; the limiting global Weyl identification is conjectural/conditional, and the
   paper explicitly notes that unconditional full kernel factorization would imply RH.
3. Masatoshi Suzuki, *An inverse problem for a class of canonical systems and its applications to
   the Riemann hypothesis*, arXiv:1204.1827. Unconditional canonical construction is confined to
   the established parameter range; extension across the critical range is RH-bearing.
4. Derkach--Hassi--Malamud, boundary relations and generalized resolvents, arXiv:1706.07948.
   Abstract Green identities explain Nevanlinna Weyl structure but do not provide the Xi source
   identification.

Exact searches for Suzuki plus `Euler defect`, `source germ`, `Christoffel--Darboux`, and
`Volterra` found no primary statement of (G2.1)--(G2.2). This is not a priority claim: external
novelty remains unverified pending expert review.

## No-go closure and mathematical delta

- **Exact killing mechanism:** analytic local source corrections are divisor-transparent;
  pointed analytic weld is globally rigid and is equivalent to removing all upper Xi poles.
- **Strongest positive survivor:** (G2.1)--(G2.3), especially exact RH equivalence (G2.2) for the
  actual relative-Volterra boundary family.
- **New knowledge:** Euler defect does not merely preserve the obstruction: it changes every
  nonzero off-real Xi pole from exact order `-1` to `-2`; any single analytic pointed source germ
  is therefore a complete RH certificate. Finite Volterra geometry can only determine the
  analytic correction, never weaken this certificate.
- **Route disposition:** original independent-bypass interpretation retired. A literal source
  proof remains permissible, but must be classified as the hard RH proof itself.
- **No theatre check:** no new operator was postulated; no source was defined from the target in
  the reverse implication; no known conditional continuation was relabelled unconditional. The
  only forward witness uses RH explicitly and serves solely to prove exact equivalence.

## Formalization contract

Formalize unconditionally:

1. pointwise source-transparency normal form at `P(z) != 0`;
2. RH implies upper-half-plane analyticity of the actual quotient's Euler defect;
3. generic existential pointed-source-germ iff RH;
4. exact relative-Volterra boundary-response specialization;
5. `#print axioms` audit, umbrella wiring, formal lint, and final targeted module build.

Explicit user rule forbids computations. Numerical pre-certification is therefore inapplicable and
waived for this purely symbolic divisor/analyticity theorem; no numerical evidence is used.

## Gates

- [x] 0 -> 1: exact inherited claim, source-purity conditions, and falsifiers recorded
- [x] 1 -> 2: internal/external audit, hostile conjecture loop, dependency-closed proof
- [x] 2 -> 3: unconditional Lean theorem, umbrella, lint, axiom audit, final module build
- [ ] 3 -> 4: independent priority and expert review

## Log

- 2026-08-01 — opened from `rh-current-frontier-map.md` Route G2.
- 2026-08-01 — literal Suzuki source domain audited against primary papers.
- 2026-08-01 — original source-construction claim retired as independent infrastructure;
  source-transparency and exact RH-equivalent pointed-germ survivor paper-proved.
- 2026-08-01 — exact survivor formalized in
  `SuzukiVolterraSourceGermWeldRigidity.lean`; source check, formal lint, axiom audit, and targeted
  module build passed.
