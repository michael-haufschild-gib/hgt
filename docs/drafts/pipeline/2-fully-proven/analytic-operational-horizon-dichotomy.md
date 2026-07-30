# Analytic operational-horizon dichotomy

- **ID:** `analytic-operational-horizon-dichotomy`
- **Stage:** 2-fully-proven
- **Type:** HORIZON DISCRIMINATOR / EXACT ANALYTIC SCALING LAW
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NOVEL ALONE]`
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

## Formal proof status

File:
`formal/GaloisForLFunctions/HTGeometry/AnalyticOperationalHorizonDichotomyLaw.lean`.

Unconditional theorems:

- `hasPermanentAnalyticHorizon_iff_series_eq_zero`;
- `hasPermanentAnalyticHorizon_or_finiteUnlocking`; and
- `analyticOperationalHorizon_dichotomy_core`.

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
- [ ] finite model-derived upper bound on unlocking order
- [ ] source/reporter operational specialization
- [ ] finite-sample noise and estimation theorem
- [ ] channel-level observer comparison map
- [ ] external joined-law novelty audit
- [ ] physical horizon model

