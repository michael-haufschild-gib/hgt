# Analytic operational-horizon dichotomy

- **ID:** `analytic-operational-horizon-dichotomy`
- **Stage:** 2-fully-proven
- **Type:** HORIZON DISCRIMINATOR / EXACT ANALYTIC SCALING LAW
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [FINITE POLYNOMIAL CERTIFICATE] [NOT NOVEL ALONE]`
- **Parent conjecture:**
  `../1-in-progress/temporal-atlas-relativity-conjecture.md`

## Exact theorem

Let \(f:\mathbb C\to\mathbb C\) have convergent Taylor series \(F\) at
\(g=0\), and suppose \(f(0)=0\). Exactly one of the following physical
alternatives occurs.

### Permanent analytic horizon

The response vanishes identically on a neighborhood of zero:
\[
 f=0\quad\text{locally}.                             \tag{1}
\]
This holds exactly when
\[
 F=0,                                                \tag{2}
\]
equivalently when every Taylor response coefficient vanishes.

### Finite analytic unlocking

There are a finite integer \(b>0\) and an analytic function \(u\), with
\(u(0)\ne0\), such that
\[
 f(g)=g^b u(g).                                      \tag{3}
\]
The inverse-response observation scale then satisfies
\[
 \frac{|g|^b}{|f(g)|}
 \longrightarrow
 \frac1{|u(0)|}\in(0,\infty).                        \tag{4}
\]

Thus no nonzero analytic weak link can remain hidden to every finite
response order. It has one finite first unlocking order and one exact
power-law observation scale. Permanent analytic invisibility is equivalent
to vanishing of the complete response jet.

## Dependency-closed proof

The convergent Taylor series of \(f\) is unique. It is zero exactly when
\(f\) is locally the zero function, proving `(1)`--`(2)`.

If the series is nonzero, its support is a nonempty subset of
\(\mathbb N\), so it has a least element \(b\). Because \(f(0)=0\), its
constant coefficient vanishes and \(b>0\). Analytic divided-difference
factorization removes \(g^b\) and yields `(3)`, where the remaining analytic
unit has nonzero value at zero. Taking norms in `(3)`, cancelling
\(|g|^b\) off the puncture and using continuity of \(u\) gives `(4)`.

## Operational meaning

Choose \(f(g)\) to be a calibrated source-to-reporter response across a
tunable coupling \(g\).

- If all response orders vanish, analyticity makes the invisibility exact
  throughout a neighborhood.
- If any response survives, a finite experiment order \(b\) exists in
  principle and the required horizon scales as \(|g|^{-b}\).
- A large but finite \(b\) is a weak link, not a permanent analytic horizon.

The theorem therefore provides an exact discriminator inside analytic
finite models. It is stronger than checking any preselected finite set of
derivatives, because the zero branch concerns the complete Taylor jet.

## Hostile boundary

1. The analytic identity/factorization mechanism is classical and is not
   novelty by itself.
2. Smooth nonanalytic flat responses, such as exponentially small
   responses, need not have a finite power-law unlocking order.
3. A mathematical response must be identified with a physically available
   source/reporter protocol before “horizon” is justified.
4. The theorem distinguishes a locally zero analytic channel from an
   analytic weak link. It does not prove that an astrophysical event horizon
   realizes that zero channel.
5. Measuring all Taylor orders is not a finite device protocol. A
   model-derived upper bound on \(b\) is needed for finite certification.
6. No gravity, black-hole information or spacetime claim follows without a
   concrete operational model.

## Bounded-degree finite certificate

If the calibrated response is a polynomial \(p\) of known degree at most
\(D\), the all-jet criterion becomes finite. For any \(D+1\) distinct
coupling settings \(g_0,\ldots,g_D\),
\[
 p=0
 \quad\Longleftrightarrow\quad
 p(g_0)=\cdots=p(g_D)=0.                             \tag{5}
\]
If \(p\ne0\) and \(p(0)=0\), its unlocking order is its root multiplicity
at zero and lies in
\[
 1\le \operatorname{ord}_0 p\le D.                  \tag{6}
\]

Thus a bounded-degree response model admits an exact finite horizon
certificate without reconstructing a Hamiltonian. This is a noiseless
identifiability theorem; finite-error certification still requires a
stability margin.

### Finite-depth path specialization

Consider an arbitrary finite interferometric path family. Let every path
contain \(m\) affine coupling factors
\[
 a_j+g b_j,\qquad j=1,\ldots,m,
\]
and permit arbitrary complex path weights and interference among paths.
Every path amplitude is a polynomial of degree at most \(m\), and a finite
weighted sum remains degree at most \(m\). Therefore:

- \(m+1\) distinct coupling settings decide exact zero response;
- any nonzero response vanishing at \(g=0\) unlocks at some
  \(1\le b\le m\); and
- destructive interference can delay unlocking but cannot hide the link
  beyond protocol depth.

This supplies a physical derivation of the degree bound for finite-depth
affine path experiments. It does not yet cover generic exponential
Hamiltonian evolution.

## Formal proof status

Files:

- `formal/GaloisForLFunctions/HTGeometry/AnalyticOperationalHorizonDichotomyLaw.lean`;
- `formal/GaloisForLFunctions/HTGeometry/BoundedDegreeOperationalHorizonCertificate.lean`;
- `formal/GaloisForLFunctions/HTGeometry/FiniteDepthOperationalHorizonLaw.lean`.

Unconditional theorems:

- `hasPermanentAnalyticHorizon_iff_series_eq_zero`;
- `hasPermanentAnalyticHorizon_or_finiteUnlocking`; and
- `analyticOperationalHorizon_dichotomy_core`;
- `polynomialResponse_eq_zero_iff_finiteSamples`;
- `polynomialResponse_unlockingOrder_pos_le`; and
- `boundedDegreeOperationalHorizon_finiteCertificate`;
- `natDegree_affinePathResponse_le`;
- `natDegree_finiteDepthAffineResponse_le`; and
- `finiteDepthAffineResponse_horizonCertificate`.

Foreground verification passed with
`lake env lean
GaloisForLFunctions/HTGeometry/AnalyticOperationalHorizonDichotomyLaw.lean`.

The scratch axiom audit reports only `propext`, `Classical.choice` and
`Quot.sound`.

## Promotion gates

- [x] exact analytic dichotomy
- [x] finite unlocking order for every active analytic response
- [x] inverse-response scaling law
- [x] unconditional Lean proof
- [x] finite upper bound and exact sample certificate for polynomial responses
- [x] finite-depth affine source/path/reporter specialization
- [ ] generic unitary/channel protocol specialization
- [ ] finite-sample noise and estimation theorem
- [ ] channel-level observer comparison map
- [ ] external joined-law novelty audit
- [ ] physical horizon model
