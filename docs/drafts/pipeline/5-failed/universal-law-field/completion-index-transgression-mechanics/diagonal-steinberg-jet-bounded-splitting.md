# Diagonal Steinberg-jet bounded splitting

- **ID:** `ULF-SKSB-FAIL-1`
- **Stage:** 5-failed
- **Type:** falsified completion mechanism

## Mechanism tested

Resolve each actual complementary Steinberg cell by its first two Kummer jets and assemble the
cellwise right inverses into a bounded cofinal source splitting.

## Killing theorem

`ULF-SKSB-1` proves every such right inverse has cost at least

`1/(2 |log(x_m) log(y_m)|)`,

which diverges along the actual depth family.

## No-go closure

- **Exact killing mechanism:** collapsing augmentation Hessian.
- **Strongest positive survivor:** only a cross-cell interaction can supply a uniform frame bound;
  diagonal/local normal jets cannot.
- **New insight:** the source anomaly is already present in the conditioning of an algebraically
  exact resolution.  Adding local jets does not approach the solution.
- **Status:** dependency-closed proof in
  `pipeline/2-fully-proven/universal-law-field/completion-index-transgression-mechanics/steinberg-kummer-cofinal-splitting-blowup-law.md`.

## Log

- 2026-09-02 -- opened and killed by augmentation.
