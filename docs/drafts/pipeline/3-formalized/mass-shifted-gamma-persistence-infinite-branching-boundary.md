# Mass-shifted Gamma persistence and infinite-branching face boundary

- **ID:** MSST-GPIB-1
- **Stage:** 3-formalized
- **Formalized companion:** `./mass-shifted-gamma-persistence-infinite-branching-boundary-formalized.md`
- **Type:** FALSIFIED / THEOREM (paper and Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 plus imported constitutive
  Kőnig, Gamma-corona, and finite-jet realization-boundary theorems
- **Statement:** Gamma death profiles cannot orient a signed Hankel normal, finite Hankel faces are
  infinitely branching in their first unseen moment, and the existing cooriented Gamma cone has no
  source-first landing into the adaptive shifted-Xi normal.

## Goal

Test whether new constitutive realization theorems reduce §9.3 proof burden. Locate the exact
failure of locally finite compactness in the shifted-Hankel extension tower, and determine whether
fixed-corona Gamma persistence supplies the missing adaptive source orientation.

## Gates

- [x] 0 → 1  in-progress: route-local objects and falsifiers fixed
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems, targeted builds green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (not currently claimed)

## Approach

1. Compare the finite Hankel face tower with the hypotheses of the imported Kőnig theorem.
2. Test whether the exact Gamma Bockstein death profile determines the sign of a linear normal
   observation.
3. Add the existing Gamma source coorientation and test whether its positive-cone theorem lands in
   the adaptive `P^sharp` source coordinate.
4. Search for a pre-divisor, Gamma-equivariant Bockstein-to-Hankel-normal map rather than assuming
   one at a selected Xi zero.

## Paper proof `[PROVED HERE]`

### 1. Persistence profile cannot orient a linear normal

For a family of linear responses `T_s`, define `kappa_T(x)(s)` by `T_s x = 0`. Linearity gives
`T_s(-x)=-T_sx`, hence `kappa_T(-x)=kappa_T(x)`. For every linear normal reporter `L`, however,
`L(-x)=-L(x)`. If `L(x) != 0`, a predicate of the kernel profile classifying `0 < L(x)` on every
input would assign the same truth value to `x` and `-x`, although exactly one of their reporter
values is positive. Contradiction.

Thus Gamma Bockstein death time is an exact magnitude/threshold invariant but cannot by itself
supply source coorientation.

### 2. Exact failure of Kőnig local finiteness

Fix a moment sequence `s` and a size-`n+1` face. For each real `delta`, change only moment
`2n+1`. Every visible matrix entry has index at most `2n`, so the face is unchanged. Evaluation at
coordinate `2n+1` proves the map from `delta` to the perturbed complete sequence is injective.
Hence every face fibre is infinite.

If the terminal null coefficient is nonzero, the monic remainder translates by exactly `delta`.
Choosing `delta = r - R(s,c)` realizes every prescribed `r : R`. Therefore the remainder map from
the fixed-face fibre onto `R` is surjective. Kőnig's locally finite hypothesis fails on the exact
first-unseen coordinate rather than at an unspecified limit.

### 3. Gamma coorientation does not yet land

The existing Gamma positive-cone theorem orients nonnegative finite and summable packets of
cooriented distinct-cell exteriors. To consume it here one needs a pre-divisor identity expressing
the adaptive completed source jet as such a packet with nonnegative weights. Corpus search finds
only Bockstein/Xi landing identities already specialized at a chosen divisor and its leading Xi
jet. No declaration maps fixed-corona dynamics to the `P^sharp` normal of a singular shifted-Xi
face. Existing exact hostile carriers additionally show positive marginal source weights can yield
both signs after the adaptive polynomial is applied. Therefore the positive-cone theorem cannot be
substituted for the missing landing.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Kernel/death profiles are invariant under source negation;
  fixed Hankel faces have injectively real-parameterized extension fibres; their monic remainder is
  onto `R`; existing Gamma coorientation has no source-first adaptive-normal landing.
- **Strongest positive survivor:** A possible contradiction route is now exact. Construct an
  infinite-carrier, source-first, cooriented Gamma-equivariant landing into the one-dimensional
  adaptive normal and prove critical Bockstein nonvanishing there. Surjective evolution on that
  finite normal cannot erase a nonzero image, so an off-line death event would be impossible.
- **New insight:** The repeated finite-face failures are shadows of one observer-boundary law.
  Route-local Kőnig escape is infinite branching at the first unseen moment; selection of the
  literal Xi extension is an effectivity/admission problem; lifetime forgets the `mu_2`
  coorientation needed to sign that extension.
- **Status:** Paper proof dependency-closed. Generic infinite-face and sign-profile theorems and
  shifted-Xi specialization are Lean-proved and axiom-audited; repository lint reaches only four
  unrelated concurrently created unwired modules.

## Log

- 2026-08-09 — created after importing Kőnig compactness, Gamma-corona infinite-dimensionality,
  and finite-jet nonseparation as external corpus findings rather than duplicate formalization.
- 2026-08-09 — conjectures 34--36 attacked; lifetime orientation and Kőnig routes falsified;
  infinite-branching fibre and source-first equivariant landing target proved on paper.
- 2026-08-09 — `FiniteHankelBoundaryExtensionClass` and
  `XiShiftedHankelBoundaryInfiniteObservationNoGo` direct checks and targeted builds passed;
  audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; promoted to
  Stage 3.
