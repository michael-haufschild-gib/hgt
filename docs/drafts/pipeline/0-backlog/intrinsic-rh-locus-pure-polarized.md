# The intrinsic RH locus = pure + polarized (G9)

- **ID:** intrinsic-rh-locus-pure-polarized
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#68 SEED-I §22) · 00-status row #98
- **Statement:** Every multi-`q` module `M` has a native L-function
  `ζ_M(s) = ∏_p det(1 − A_p p^{−s})^{−1}` (poles = trivial-`G_M`-rep multiplicity; FE ⟺
  polarization/self-duality). **RH is meaningful-and-clean ⟺ `M` is pure + polarized.** **Conjecture:**
  RH is a property *only* of the **pure-polarized sub-locus** (= the arithmetic motives); most of the
  field has no RH.

## Goal
**Defines what RH is about** — the positivity framing never makes this explicit. It says RH is not a
property of generic difference modules but of a thin, structured sub-locus (pure + polarized), explaining
why RH is rare in the moduli of prime systems (`bucket-realization-and-fake-family`'s off-line Beurling
examples: off-line zeros are generic, RH is the special arithmetic-forced stratum).

## Door passport
- **Door-1/3:** `ζ_M`, purity (weight), and polarization (the FE) are native module invariants
  (`G_M`-rep data); the sub-locus is cut by these.
- **Door-2:** purity + polarization are native conditions; the test is whether "RH lives only there"
  needs the joint structure or restates Deligne purity transported — the *transport* to the infinite base
  is the native content.

## Gates
- [ ] 0 → 1  in-progress: `ζ_M`, purity, polarization defined for multi-`q` modules; the pure-polarized
  sub-locus pinned; "RH meaningful only there" stated
- [ ] 1 → 2  fully-proven: RH degeneracy off the sub-locus proved; the sub-locus = arithmetic motives identified
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Define purity (weight-½ after the Arakelov `w`-coordinate) and polarization (FE self-duality) for the
native `ζ_M`; show RH is ill-posed or false off the pure-polarized locus and characterize that locus as
the arithmetic motives. Cross-check with the realization cuts (E)/(A)/(P): the sub-locus ⊆ the (A) Euler
stratum.

## Cross-references
- `realization-problem.md` — RH is rare in the moduli; the pure-polarized locus ⊆ the (A) Euler stratum.
- `fe-fourier-quasicrystal.md` — polarization = the FE, characterized crystallinely.
- `../../door/bucket-new-sibling-conjectures.md` — the SEED-I source.

## Log
- 2026-06-19 — created in 0-backlog. The intrinsic RH locus (G9, SEED-I): RH lives only on the
  pure-polarized sub-locus — what RH is *about*.
