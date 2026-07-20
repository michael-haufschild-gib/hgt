# Generalized spin-tower channel differential boundary

- **ID:** `generalized-spin-tower-differential-boundary`
- **Stage:** 3-formalized / not_new_scientific_knowledge
- **Type:** THEOREM (Lean) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** Berman--Caron-Huot--Chandra--Elvang--Herderschee--Lin--Morales,
  *Gravitational Effective Theories with Maximal Supersymmetry and a Peculiar Parity*,
  arXiv:2607.14230, equations (5.16)--(5.18)
- **Statement:** For
  `F_N(z)=Gamma(1-z)Gamma(1+z+N)/(Gamma(1+z)Gamma(1-z+N))`, `F_N` is
  differentially algebraic over `C(z)` exactly when `N` is an integer and is
  hypertranscendental otherwise.

## Scientific status

This theorem is an exact application of the existing meromorphic Gamma-orbit superselection law
to a formula harvested from 2026 string/SUSY amplitude research.  It is useful because the source
paper discusses finite-spin truncation, analytic continuation, positivity, and amplitude
uniqueness, but does not classify the continued multiplier in differential algebra.  It is not
claimed as new scientific knowledge: the mathematical proof is a direct specialization of the
project's stronger parent theorem.

The source paper's analytic continuation writes its finite generalized tower as the
Virasoro--Shapiro amplitude times, in each channel `x`,

`Gamma(1+x/m^2+N) / Gamma(1-x/m^2+N)`.

Combining that factor with the corresponding Virasoro--Shapiro channel factor and setting
`z=x/m^2` gives precisely `F_N`.  The theorem below classifies this single variable-channel
multiplier.  It does not assert the paper's stronger all-channel amplitude uniqueness claim.

## Gates

- [x] Source formula checked in the 2026 paper, not inferred from its abstract.
- [x] Existing formal Gamma, Veneziano, reflection, and orbit-charge APIs searched first.
- [x] Exact claim is source-pure and uses no numerical evidence.
- [x] Complete unconditional paper proof.
- [x] Hostile internal and external novelty audit; classification fixed to `BRIDGE`.
- [x] Exact Lean proof passes `lake env lean` on the source file.
- [x] Capstone axiom audit, generated indexes, final module build, and stage-3 promotion.
- [x] Repository lint localized: this module is umbrella-reachable and clean; the remaining lint
  failures are unrelated pre-existing/concurrent unreachable modules in `RHTower`, `HTGeometry`,
  and `HilbertMetric`.

## Complete paper proof

Work in the differential field of meromorphic functions on `C`, with base field `C(z)`.  Euler
reflection gives

`Gamma(1-z)=g_1(z)/Gamma(z)`

and

`Gamma(1-z+N)=g_(1+N)(z)/Gamma(z-N)`,

where every `g_b(z)=pi/sin(pi(b-z))` is nonzero and differentially algebraic.  Therefore

`F_N(z) = (g_1/g_(1+N))(z)
          Gamma(z-N)Gamma(z+1+N)/(Gamma(z)Gamma(z+1)).`

The sine quotient is a nonzero DA gauge and hence does not change differential algebraicity or
hypertranscendence.

If `N` is an integer, both Gamma ratios

`Gamma(z-N)/Gamma(z)` and `Gamma(z+1+N)/Gamma(z+1)`

are rational Pochhammer factors (or their reciprocals).  Hence `F_N` is DA.

Suppose `N` is not an integer.  Reduce the four positive-orientation Gamma factors modulo integer
translation.  The denominator factors `Gamma(z)` and `Gamma(z+1)` occupy the same orbit `[0]` and
give total charge `-2`.  The numerator factors occupy `[-N]` and `[N]`; both are distinct from
`[0]` because `N` is nonintegral.  They may coincide with each other, for example at some
half-integral parameters, but that collision is irrelevant: the existing one-distinguished-orbit
superselection theorem only requires the nonzero charged orbit `[0]` to be separated from all
other chosen representatives.  Its charge `-2` therefore forces the four-Gamma carrier to be HT.
Multiplication by the nonzero DA sine quotient preserves HT.  Thus `F_N` is HT for every
noninteger `N`.

The two cases are complementary, proving both exact equivalences.  No physical assumption,
positivity ansatz, amplitude bootstrap, or computation enters this classification.  QED.

## Exact Lean surface

- Module: `GaloisForLFunctions.HTGeometry.GeneralizedSpinTowerDifferentialBoundary`
- Source object: `generalizedSpinTowerChannelMero`
- Reflection normal form: `generalizedSpinTowerChannelMero_eq_gauge_mul_carrier`
- Integral branch: `differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_of_integer`
- Nonintegral branch:
  `hypertranscendentalOver_generalizedSpinTowerChannelMero_of_noninteger`
- Exact DA boundary:
  `differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer`
- Exact HT boundary:
  `hypertranscendentalOver_generalizedSpinTowerChannelMero_iff_noninteger`

The Lean proof encodes the central orbit as two offsets with charges `-1,-1` and the numerator
orbits as charges `+1,+1`.  It deliberately invokes the distinguished-orbit theorem rather than a
pairwise-separation theorem, so the possible collision between `[-N]` and `[N]` is covered.

## Hostile audit and open stronger statement

Searches for the exact formula combined with `differential algebraic`, `differential
transcendence`, and `hypertranscendental`, plus searches for the paper's “generalized spin tower”
with those terms, found amplitude-bootstrap and positivity results but no differential-algebra
classification.  This does not establish priority.  More importantly, the project already proves
the stronger parent Gamma-orbit theorem, so the present result is a specialization and is labelled
`BRIDGE` regardless of the external search outcome.

The source paper's claimed analytic uniqueness of the Virasoro--Shapiro amplitude uses an
all-orders exponentiated nonlinear-constraint ansatz; the displayed checks in the paper reach only
finite expansion order.  That physical uniqueness result is therefore not imported into Lean.

A stronger project statement would classify a fixed-channel quotient such as
`F_N(z)/F_N(z+b)` simultaneously in `(N,b)`, including every collision among the six translated
Gamma orbits.  The expected boundary is `N in Z` or `b in Z`, but this remains a conjecture until a
complete collision proof is written.  No conditional Prop interface has been introduced for it.

## No-go closure

- **Exact killing mechanism for a novelty claim:** the theorem is a direct source specialization
  of `hypertranscendentalOver_gammaCommonScaleProductMero_of_charge_ne_zero` and the integral
  Veneziano-ratio classification.
- **Strongest positive survivor:** an exact, unconditional, physically sourced DA/HT boundary
  covering all complex continuation parameters `N`, including outer-orbit collisions.
- **New insight for the programme:** finite physical tower length is exactly the DA lattice;
  analytic continuation away from integer length creates an unavoidable charge-`-2` Gamma clock.
- **Status:** paper proof and exact Lean theorem complete; direct check, axiom audit, generated
  index, and final module build pass.

## Log

- 2026-07-20 -- 2026 source formula harvested and matched against the whole formal corpus.
- 2026-07-20 -- paper proof completed; hostile audit demoted the claim from possible novelty to an
  exact bridge; direct Lean source check passed.
- 2026-07-20 -- capstone axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`;
  generated indexes include the public surface; the exact final module build passed.  Promoted to
  stage 3 as `not_new_scientific_knowledge`.
